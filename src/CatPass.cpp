#include "llvm/IR/Module.h"
#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/Support/Casting.h"
#include "llvm/ADT/BitVector.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Transforms/Utils/Cloning.h"

#include <set>
#include <unordered_set>
#include <vector>
#include <map>
#include <unordered_map>
#include <queue>
#include <chrono>
// #define CHECK_CONST_AGGRESSIVE
// #define ENABLE_TIMER
#define DEBUG_CORRECTNESS
using namespace llvm;
 
#define IN_MAP(map, key) (map.find(key) != map.end())
#define IN_SET(set, key) (set.find(key) != set.end())

namespace {

struct CAT : public ModulePass {
// struct CAT : public FunctionPass {
    static char ID; 
    Module *currentModule;

#define IS_USER_FUNC(fptr) (!fptr->empty())
    std::set<std::string> func_set = {
        "CAT_new",
        "CAT_add",
        "CAT_sub",
        "CAT_get",
        "CAT_set"
    };
    
    std::unordered_map<Function *, std::string> fptr2name;
    std::unordered_map<Function *, int> fptr2cnt;
    Function * CAT_new_ptr;
    Function * CAT_add_ptr;
    Function * CAT_sub_ptr;
    Function * CAT_get_ptr;
    Function * CAT_set_ptr;
    Function * main_fptr;
#define IS_CAT_new(fptr) (fptr == CAT_new_ptr)
#define IS_CAT_add(fptr) (fptr == CAT_add_ptr)
#define IS_CAT_sub(fptr) (fptr == CAT_sub_ptr)
#define IS_CAT_get(fptr) (fptr == CAT_get_ptr)
#define IS_CAT_set(fptr) (fptr == CAT_set_ptr)

#define IS_CAT_OP(fptr) ( fptr2name.find(fptr) != fptr2name.end() )

#define IS_CONST_CAT_OP(fptr) (IS_CAT_set(fptr) || IS_CAT_new(fptr))
    //HW1
    llvm::BitVector GEN;
    std::vector<llvm::Instruction *> instr_vec;
    std::vector<llvm::BitVector> KILL;
    std::unordered_map<void *, llvm::BitVector> instr2bitmap;

    //HW2
    std::unordered_map<llvm::Instruction *, llvm::BitVector> INSTR_IN, INSTR_OUT;
    std::unordered_map<llvm::BasicBlock *,llvm::BitVector> BB_GEN,BB_KILL,BB_IN,BB_OUT;
    
    
    std::unordered_set<CallInst *> escaped;
#define IS_ESCAPED(callptr) ( escaped.find(callptr) != escaped.end() )

    std::set<Value *> cat_arg;
#define IN_CAT_ARG(ptr) (cat_arg.find(ptr)!=cat_arg.end())

    std::set<Value*> cat_var;
#define IS_CAT_VAR(ptr) (cat_var.find(ptr)!=cat_var.end())
    std::set<Value *> arg_set;
    //Generic IN / OUT set
    // std::vector<Value*> sGEN;
    std::set<Value*> sGEN;
    std::unordered_map<Value*, std::set<Value*>> sKILL;
    std::unordered_map<Value*, std::set<Value*>> sVar2Def;
    std::unordered_map<Value*, std::set<Value*>> sBB_GEN;
    std::unordered_map<Value*, std::set<Value*>> sBB_KILL;
    std::unordered_map<Value *, std::set<Value*>> sBB_IN, sBB_OUT;
    std::unordered_map<Value *, std::set<Value*>> sIN, sOUT;

    std::unordered_map<Value*, std::set<Value*>> sVar2mightDef;
    // maps gen instruction to variable it defines
    std::unordered_map<Value* ,std::vector<Value*>> BB2CAT;
    
    std::unordered_map<Value *, Value*> ptrToVal;

    // May-Point-to Analysis
    std::unordered_map<Value *, std::set<std::pair<Value*, Value*>>> mptGEN; // instruction -> {(p,x)}
    std::unordered_map<Value *, std::set<std::pair<Value*, Value*>>> mptKILL; // instruction -> {(p,v)| v escaped}
    std::unordered_map<Value *, std::set<Value *>> ptr2Val; // p->{x | for all x that (p,x) };
    // std::unordered_map<Value *, std::set<Value *>> val2Ptr; // x->{p | for all p that (p,x) }
    std::unordered_map<Value *, std::set<std::pair<Value*, Value*>>> mptIN;
    std::unordered_map<Value *, std::set<std::pair<Value*, Value*>>> mptOUT;

    std::unordered_map<Value *,std::vector<Value*>> mptBB2CAT;

    /**
     * maps from user call to a map from its argument to replacement
     * Keep it map as we might need to iterate pretty often
     * userCall2replace : {userfunction Call -> {arg -> replaced dummy instruction}}
     * repalce2userCall: {replaced dummy instruction -> [userfunction Call, arg]}
     * */
    std::map<Instruction *, std::map<Value *, Instruction *>> userCall2replace;
    std::map<Instruction *, std::pair<Instruction *, Value * >> replace2userCall;

    enum CycleResult {noCycle, mustCycle, mightCycle};
    std::unordered_map<Value *, CycleResult> func2cycle;

    std::map<Value * , Value *> auto2def;

    /**
     *  live_{GEN|KILL|IN|OUT} are for the liveness of values of variables
     *  ref_{GEN|KILL|IN|OUT} are for the liveness of References of variables
     * */

    std::map<Value *, std::set<Value *>> live_GEN, live_KILL, live_might_KILL;
    std::map<Value *, std::set<Value *>> live_IN, live_OUT;
    
    std::unordered_map<Value *,std::vector<Instruction*>> liveBB2CAT;
    // std::map<Value *, std::set<Value *>> ref_GEN, ref_KILL;
    // std::map<Value *, std::set<Value *>> ref_IN, ref_OUT;

#define IS_PTR_TYPE(val) (isa<PointerType>(val->getType()) )
#define IS_INT_TYPE(val) (isa<IntegerType>(val->getType()) )
#define HAS_MOD(info) (\
        info == ModRefInfo::MustMod \
    || info == ModRefInfo::MustModRef \
    || info == ModRefInfo::Mod \
    || info == ModRefInfo::ModRef \
)

#define HAS_REF(info) (\
        info == ModRefInfo::MustRef \
    || info == ModRefInfo::MustModRef \
    || info == ModRefInfo::Ref \
    || info == ModRefInfo::ModRef \
)

#define NO_MOD(info) (!HAS_MOD(info))

    std::string ModRefInfo_toString(ModRefInfo info){
        std::string str;
        switch (info)
        {
        case ModRefInfo::Must :
            str = "ModRefInfo::Must";
            break;

        case ModRefInfo::MustRef :
            str = "ModRefInfo::MustRef";
            break;
        
        case ModRefInfo::MustMod :
            str = "ModRefInfo::MustMod";
            break;

        case ModRefInfo::MustModRef :
            str = "ModRefInfo::MustModRef";
            break;

        case ModRefInfo::NoModRef :
            str = "ModRefInfo::NoModRef";
            break;

        case ModRefInfo::Ref :
            str = "ModRefInfo::Ref";
            break;

        case ModRefInfo::Mod :
            str = "ModRefInfo::Mod";
            break;

        case ModRefInfo::ModRef :
            str = "ModRefInfo::ModRef";
            break;

        default:
            str = "";
            break;
        }

        return str;
    }

    std::string AliasResult_toString(AliasResult res){
        std::string str;
        switch (res)
        {
        case AliasResult::MustAlias :
            str = "AliasResult::MustAlias";
            break;

        case AliasResult::MayAlias :
            str = "AliasResult::MayAlias";
            break;
        
        case AliasResult::PartialAlias :
            str = "AliasResult::PartialAlias";
            break;

        case AliasResult::NoAlias :
            str = "AliasResult::NoAlias";
            break;


        default:
            str = "";
            break;
        }

        return str;
    }

    std::string CycleResult_toString(CycleResult res){
        std::string str;
        switch (res)
        {
        case CycleResult::noCycle :
            str = "CycleResult::noCycle";
            break;

        case CycleResult::mustCycle :
            str = "CycleResult::mustCycle";
            break;
        
        case CycleResult::mightCycle :
            str = "CycleResult::mightCycle";
            break;

        default:
            str = "";
            break;
        }

        return str;
    }

    template<class T>
    void set_union(std::set<T> & srcA, std::set<T> & srcB, std::set<T> & target){
        std::vector<T> output_vec = std::vector<T>(srcA.size() + srcB.size());
        typename std::vector<T>::iterator it;

        it = std::set_union(
            srcA.begin(), srcA.end(),
            srcB.begin(), srcB.end(),
            output_vec.begin()
        );

        output_vec.resize(it - output_vec.begin());

        target = std::set<T>(output_vec.begin(), output_vec.end());
    }


    template<class T>
    void set_intersect(std::set<T> & srcA, std::set<T> & srcB, std::set<T> & target){
        std::vector<T> output_vec = std::vector<T>(srcA.size() + srcB.size());
        typename std::vector<T>::iterator it;

        it = std::set_intersection(
            srcA.begin(), srcA.end(),
            srcB.begin(), srcB.end(),
            output_vec.begin()
        );

        output_vec.resize(it - output_vec.begin());
        
        target = std::set<T>(output_vec.begin(), output_vec.end());
    }

    template<class T>
    void set_diff(std::set<T> & srcA, std::set<T> & srcB, std::set<T> & target){
        std::vector<T> output_vec = std::vector<T>(srcA.size() + srcB.size());
        typename std::vector<T>::iterator it;

        it = std::set_difference(
            srcA.begin(), srcA.end(),
            srcB.begin(), srcB.end(),
            output_vec.begin()
        );

        output_vec.resize(it - output_vec.begin());
        
        target = std::set<T>(output_vec.begin(), output_vec.end());
    }


        // class to represent a disjoint set
        CAT() : ModulePass(ID) {}
        // CAT() : FunctionPass(ID) {}
    // This function is invoked once at the initialization phase of the compiler
    // The LLVM IR of functions isn't ready at this point
    bool doInitialization (Module &M) override {
        // errs() << "Hello LLVM World at \"doInitialization\"\n" ;
        currentModule = &M;

        for (const std::string & str : func_set) {
            Function * fptr = M.getFunction(StringRef(str));
            fptr2name[fptr] = str;
            if (str == "CAT_new") {CAT_new_ptr = fptr;}
            if (str == "CAT_add") {CAT_add_ptr = fptr;}
            if (str == "CAT_sub") {CAT_sub_ptr = fptr;}
            if (str == "CAT_get") {CAT_get_ptr = fptr;}
            if (str == "CAT_set") {CAT_set_ptr = fptr;}
        }
        main_fptr = M.getFunction(StringRef("main"));
        return false;
        
    }

    // This function is invoked once per function compiled
    // The LLVM IR of the input functions is ready and it can be analyzed and/or transformed
    class Timer{
    public:

        Timer(){
#ifdef ENABLE_TIMER
            t_begin = std::chrono::high_resolution_clock().now();
#endif
        }
#ifdef ENABLE_TIMER
        std::chrono::time_point<std::chrono::system_clock> t_start;
        std::chrono::time_point<std::chrono::system_clock> t_stop;
        std::chrono::time_point<std::chrono::system_clock> t_begin;
#endif
        void start(){
#ifdef ENABLE_TIMER
            t_start = std::chrono::high_resolution_clock().now();
#endif
        }
        void stop(){
#ifdef ENABLE_TIMER
            t_stop = std::chrono::high_resolution_clock().now();
#endif
        }
        void printDuration(std::string const & str){
#ifdef ENABLE_TIMER
            errs()<<str<<":"<<std::chrono::duration_cast<std::chrono::milliseconds>(t_stop - t_start).count()<<" ms\n";
#endif
        }
        void printEnd(){
#ifdef ENABLE_TIMER
            stop();
            errs()<<"TOTAL:"<<std::chrono::duration_cast<std::chrono::milliseconds>(t_stop - t_begin).count()<<" ms\n";
#endif
        }
    };
    Timer timer;

#ifdef DEBUG_CORRECTNESS
    bool runOnModule (Module &M) override {
        
        errs() << "DEBUG runOnModule\n";
        CallGraph &CG = getAnalysis<CallGraphWrapperPass>().getCallGraph();
        timer.start();
        bool inlined = function_inline(M, CG);
        timer.stop();
        timer.printDuration("INLINE ");
        if (!inlined){
            std::set<Function *> usedFunction;
            getUsedFunction(CG,M,usedFunction);
            for (auto & F: usedFunction){
                if (!F->empty()){

                    bool folded = false, propogated = false;
                    errs()<<"IN Function:"<<F->getName()<<"\n";
                    AliasAnalysis & AA = getAnalysis<AAResultsWrapperPass>(*F).getAAResults();
//                        timer.start();
                    CATNewElimination(*F);
//                        timer.stop();
//                        timer.printDuration("\tCAT NEW ELIMINATION ");
//                        timer.start();
                    mpt_wrap(*F, AA);
//                        timer.stop();
//                        timer.printDuration("\tMPT1");

//                        timer.start();
                    reachingDef_wrap(*F, AA);
//                        timer.stop();
//                        timer.printDuration("\tREACHING DEF1 ");
//
                        timer.start();
                    folded = constant_folding(*F, AA);
                        timer.stop();
                        timer.printDuration("\tCONST FOLDING");

                    if (!folded){
//                            timer.start();
                        mpt_wrap(*F, AA);
//                            timer.stop();
//                            timer.printDuration("\tMPT2 ");
//                            timer.start();
                        reachingDef_wrap(*F, AA);
//                            timer.stop();
//                            timer.printDuration("\tREACHING DEF2 ");
                            timer.start();
                        propogated = constant_propagation(*F, AA);
                            timer.stop();
                            timer.printDuration("\tPROPAGATION:");
                    }

                    if (!folded && !propogated) {
                        mpt_wrap(*F, AA);
                        live_analysis_wrapper(*F, AA);
                        eliminating(*F, AA);
                    }
                }
            }
        }
        timer.printEnd();
        return false;
    }

#else

    bool runOnModule (Module &M) override {

        CallGraph &CG = getAnalysis<CallGraphWrapperPass>().getCallGraph();
        timer.start();
        bool inlined = function_inline(M, CG);
        timer.stop();
        timer.printDuration("INLINE ");
        if (!inlined){
            std::set<Function *> usedFunction;
            getUsedFunction(CG,M,usedFunction);
            for (auto & F: usedFunction){
                if (!F->empty()){

                    bool folded = false, propogated = false;
                    errs()<<"IN Function:"<<F->getName()<<"\n";
                    AliasAnalysis & AA = getAnalysis<AAResultsWrapperPass>(*F).getAAResults();
                       timer.start();
                    CATNewElimination(*F);
                       timer.stop();
                       timer.printDuration("\tCAT NEW ELIMINATION ");
                       
                       timer.start();
                    mpt_wrap(*F, AA);
                       timer.stop();
                       timer.printDuration("\tMPT1");

                       timer.start();
                    reachingDef_wrap(*F, AA);
                       timer.stop();
                       timer.printDuration("\tREACHING DEF1 ");
//
                        timer.start();
                    folded = constant_folding(*F, AA);
                        timer.stop();
                        timer.printDuration("\tCONST FOLDING");

                        timer.start();
                    mpt_wrap(*F, AA);
                        timer.stop();
                        timer.printDuration("\tMPT2 ");
                        
                        timer.start();
                    reachingDef_wrap(*F, AA);
//                            timer.stop();
//                            timer.printDuration("\tREACHING DEF2 ");
                        timer.start();
                    propogated = constant_propagation(*F, AA);
                        timer.stop();
                        timer.printDuration("\tPROPAGATION:");

                        timer.start();
                    mpt_wrap(*F, AA);
                        timer.stop();
                        timer.printDuration("\tMPT3 :");

                        timer.start();
                    live_analysis_wrapper(*F, AA);
                        timer.stop();
                        timer.printDuration("\tlive Analysis");

                        timer.start();
                    eliminating(*F, AA);
                        timer.stop();
                        timer.printDuration("\tEliminating");
                }
            }
        }
        timer.printEnd();
        return false;
    }
#endif


    void getUsedFunction(CallGraph &CG,Module &M,std::set<Function *> &usedFunction){
        Function *mainF = M.getFunction("main");
        CallGraphNode *mainNode = CG[mainF];
        //errs()<<"FUNCTION NAME:\n";
        usedFunction.insert(mainF);
        for(auto callee: *mainNode){
            //errs()<<"NAME:"<<*callee.first<<"\n";
            if(!callee.second->getFunction()->empty()){
               getUsedFunctionHelper(callee.second,usedFunction);
            }
        }
    }

    void getUsedFunctionHelper(CallGraphNode *calleeNode, std::set<Function *> &usedFunction){
        if(IN_SET(usedFunction,calleeNode->getFunction()))
            return;
        usedFunction.insert(calleeNode->getFunction());
        for(auto callee: *calleeNode){
            if(!callee.second->getFunction()->empty()){
                getUsedFunctionHelper(callee.second,usedFunction);
            }
        }
    }



    class CC{
    public:
        std::vector<std::vector<Value*>> cc;


    };
    class Graph{
#define is_cat_new(fptr) (fptr->getName()=="CAT_new")
    public:
        std::map<Value *, std::set<Value *>> g;
        std::map<PHINode *, std::set<Value *>> visitedPHI;
        std::set<Value*> visited;
        CC cc;

        void clear(){
            g.clear();
            visited.clear();
            visitedPHI.clear();
            cc.cc.clear();
        }

        void initCATNewGraph(Function &F,std::set<Value*> &arg_set){
            this->clear();
            for(auto& BB: F){
                for(auto& I: BB){
                    if(isa<PHINode>(&I)){

                        PHINode *phi = cast<PHINode>(&I);

                        if(!IN_SET(visitedPHI,phi)){
                            auto count = countCATNewUnderPHI(phi,arg_set);
                            if(count>=2)
                                addEdgeGroup(visitedPHI[phi]);
                        }

                    }
                }
            }
            findCC();
            //print_CC();
        }

        void DFS(Value* valNode, std::vector<Value *> &cc_sub){

            for(auto& nbr : g[valNode]){
                if(!IN_SET(visited,nbr)){
                    visited.insert(nbr);
                    cc_sub.push_back(nbr);
                    DFS(nbr,cc_sub);
                }
            }
        }

        void findCC(){
            visited.clear();
            for(auto &kv:g){
                if(!IN_SET(visited,kv.first)){
                    visited.insert(kv.first);
                    std::vector<Value*> cc_sub;
                    cc_sub.push_back(kv.first);
                    DFS(kv.first,cc_sub);
                    cc.cc.push_back(cc_sub);
                }
            }

        }

        void addEdge(Value *a, Value *b){
            this->g[a].insert(b);
            this->g[b].insert(a);
        }

        void addEdgeGroup(std::set<Value*> &catNews){
            std::vector<Value *> catNewVec(catNews.begin(), catNews.end());
            for(auto i=1; i < catNewVec.size(); i++){
                this->addEdge(catNewVec[i],catNewVec[i-1]);
            }
        }

        int countCATNewUnderPHI(PHINode *phi,std::set<Value*> &arg_set){
            if(IN_SET(visitedPHI,phi)){
                return visitedPHI[phi].size();
            }
            auto numIn = phi->getNumIncomingValues();
            auto catNewNum = 0;
            visitedPHI[phi] = std::set<Value *>();
            for(auto i = 0; i < numIn; i++){
                Value *inValue = phi->getIncomingValue(i);
                if(isa<CallInst>(inValue)){
                    CallInst *callInst = cast<CallInst>(inValue);
                    Function *callee = callInst->getCalledFunction();
                    if(is_cat_new(callee)){
                        visitedPHI[phi].insert(callInst);
                        catNewNum++;
                    }
                }else if(isa<PHINode>(inValue)){
                    PHINode * childPHI = cast<PHINode>(inValue);
                    countCATNewUnderPHI(childPHI,arg_set);
                    catNewNum += visitedPHI[childPHI].size();
                    visitedPHI[phi].insert(visitedPHI[childPHI].begin(), visitedPHI[childPHI].end());
                }else if(isa<Argument>(inValue)&&!isa<ConstantInt>(inValue)){
                    Argument *arg = cast<Argument>(inValue);
                    visitedPHI[phi].insert(arg);
                    arg_set.insert(arg);
                    catNewNum++;
                }
            }
            return catNewNum;
        }

            void print_CC(){
                errs() <<"printing CC\n";
                for(uint32_t i = 0; i < cc.cc.size(); i++){
                    errs() <<"#" << i << " CC\n";
                    for(uint32_t j = 0; j < cc.cc[i].size(); j++){
                        errs() << *cc.cc[i][j] <<'\n';
                    }
                    errs() <<'\n';

                }
            }
    };
        void replace_instr_val(Instruction * instr, Value * val){
            BasicBlock::iterator ii(instr);
            BasicBlock * bb = instr->getParent();
            ReplaceInstWithValue(bb->getInstList(), ii, val);
        }
        void CAT_new_to_CAT_set(
                llvm::Value * CAT_new_old,
                llvm::Value * CAT_new_replace
        ) {
            CallInst *old = cast<CallInst>(CAT_new_old);
            IRBuilder<> builder(old);

            Value * val = old->getArgOperand(0);

            ArrayRef<Value *> arg_arr_ref = ArrayRef<Value *>{CAT_new_replace, val};

            Value * added_set_instr = builder.CreateCall(CAT_set_ptr, arg_arr_ref);

            // replacement
            replace_instr_val(old, CAT_new_replace);
        }
    void mergePHICATNew(Graph &G, Function &F){
            for(auto i = 0; i <G.cc.cc.size(); i++){
                // nodes = G.cc.cc[i]
                std::set<Value*> nodeSet(G.cc.cc[i].begin(),G.cc.cc[i].end());
                Value *CAT_new_replace = NULL;
                for(auto arg=F.arg_begin();arg!=F.arg_end();++arg){
                    if(IN_SET(nodeSet,arg)){
                        CAT_new_replace = cast<Value>(arg);
                        break;
                    }
                }
                for(Instruction & inst: F.getBasicBlockList().front()){
                    if(IN_SET(nodeSet,&inst)){
                        CAT_new_replace = cast<Value>(&inst);
                        break;
                    }
                }

                if(CAT_new_replace==NULL) CAT_new_replace = build_CAT_new_Head(F);

                for(auto j = 0; j <G.cc.cc[i].size();j++){
                    Value * CAT_new_old = cast<Value>(G.cc.cc[i][j]);
                    if(CAT_new_old != CAT_new_replace){
                        CAT_new_to_CAT_set(
                                CAT_new_old,
                                CAT_new_replace
                        );
                    }
                }

            }
        }


        void CATNewElimination(Function &F){
        Graph graph;
        graph.initCATNewGraph(F,arg_set);
        mergePHICATNew(graph,F);
        //graph.initCATNewGraph(F);
//        errs()<<"?????????????????????????????????????????????????????\n";
//        for(auto& BB: F){
//            for(auto& I:BB){
//                errs()<<I<<"\n";
//            }
//        }
        graph.initCATNewGraph(F,arg_set);
//        for(auto& t:graph.visitedPHI){
//            for(auto& t2: t.second){
//                errs()<<*t2<<"\n";
//            }
//        }

        merge_Phi(graph.visitedPHI);

    }
        CallInst * build_CAT_new_Head(Function & F){
            Instruction * first_instr = &(*instructions(F).begin());
            IRBuilder<> builder(first_instr);

            Constant * zeroConst = ConstantInt::get(IntegerType::get(currentModule->getContext(), 64), 0, true);
            // std::vector<Value *> arg_vec{zeroConst};
            ArrayRef<Value *> arg_arr_ref = ArrayRef<Value *>{zeroConst};

            Value * added_new_instr = builder.CreateCall(CAT_new_ptr, arg_arr_ref);
            return cast<CallInst>(added_new_instr);

        }
        void merge_Phi(
                std::map<PHINode *, std::set<Value *>> &visited_phi
        ){
            std::set<PHINode *> worklist;
            bool merged_in_round = true;

            for (auto & kv : visited_phi){
                worklist.insert(kv.first);
            }
            std::set<PHINode *> worklist_temp;

            while (merged_in_round && !worklist.empty())
            {
                // create temp as it's hard to erase while iterating
                worklist_temp = worklist;
                merged_in_round = false;

                for (auto & phi : worklist){
                    bool merged = merge_single_phi(phi);

                    if (merged){

                        worklist_temp.erase(phi);
                    }
                    merged_in_round = merged_in_round || merged;
                }

                worklist = worklist_temp;
            }

        }
        bool merge_single_phi(PHINode *phi) {
            // errs() << "replacing" << *phi  << "at " << phi << '\n';
            uint32_t numIncoming = phi->getNumIncomingValues();

            std::vector<Value *> inValue_collect(numIncoming);
            for (uint32_t i = 0; i < numIncoming; i++) {
                inValue_collect[i] = phi->getIncomingValue(i);
            }

            if (vec_all_equal(inValue_collect)){
                replace_instr_val(phi, inValue_collect[0]);
                // errs() <<"after replacement\n";
                // errs() << phi << '\n';
                return true;
            }

            return false;
        }

    // // This function is invoked once per function compiled
    // // The LLVM IR of the input functions is ready and it can be analyzed and/or transformed
    // bool runOnFunction (Function &F) override {
    //     //findCatVariables(F);
    //     //phi_node_new2set(F);
    //     AliasAnalysis & AA = getAnalysis<AAResultsWrapperPass>().getAAResults();
    //     mpt_wrap(F, AA);
    //     reachingDef_wrap(F, AA);
    //     bool folded = constant_folding(F, AA);

    //     mpt_wrap(F, AA);
    //     reachingDef_wrap(F, AA);
    //     bool propogated = constant_propagation(F, AA);
        
    //     if (! (folded || propogated)) {
    //         mpt_wrap(F, AA);
    //         live_analysis_wrapper(F, AA);
    //         eliminating(F, AA);
    //     }
        
    //     return false;
    // }

    // We don't modify the program, so we preserve all analyses.
    // The LLVM IR of functions isn't ready at this point
    void getAnalysisUsage(AnalysisUsage &AU) const override {
        // errs() << "Hello LLVM World at \"getAnalysisUsage\"\n" ;

        // AU.setPreservesAll();
        AU.addRequired<AAResultsWrapperPass>();
        AU.addRequired<CallGraphWrapperPass>();
    }

    
    CycleResult is_cycle_call(Function * F, CallGraph &CG) {
        CallGraphNode *n = CG[F];
        std::set<Function*> visited {F};
        for (auto callee : *n){
            CallGraphNode * calleeNode = callee.second;
            auto callInst = callee.first;

            auto calleeF = calleeNode->getFunction();
            if (calleeF == nullptr) {
                return mightCycle;
            }

            if (!IS_USER_FUNC(calleeF)) continue;
            
            CycleResult sub_result = is_cycle_call_helper(F, calleeF, CG, visited);
            if (sub_result != noCycle) {
                return sub_result;
            }
        }
        return noCycle;
    }

    CycleResult is_cycle_call_helper(
        Function * targetF, 
        Function * currF, 
        CallGraph &CG,
        std::set<Function*> visited
    ) {
        // errs() << "targetF = " << targetF->getName();
        // errs() << "currF = "   << currF->getName()  << '\n';
        if (IN_SET(visited, currF)) {
            if (currF == targetF){
                return mustCycle;
            } else {
                return noCycle;
            }
        }

        CallGraphNode *curr_node = CG[currF];
        visited.insert(currF);

        for (auto callee : *curr_node) {
            CallGraphNode * calleeNode = callee.second;
            auto callInst = callee.first;

            Function * calleeF = calleeNode->getFunction();
            if (calleeF == nullptr) {
                return mightCycle;
            }
            
            if (!IS_USER_FUNC(calleeF)) continue;
            CycleResult sub_result = is_cycle_call_helper(targetF, calleeF, CG, visited);

            /**
             *  Return cycle information once found suspicious
             * */
            if (sub_result != noCycle) {
                return sub_result;
            }
        }

        return noCycle;
    }


    /**
     *  Find out if Function F is in a cycle that points back to itself
     *      info store in func2cycle
     * */
    void Fill_func2cycle(Module &M, CallGraph &CG) {
        for (Function & F : M) {
            if (F.empty()) continue;
            
            CycleResult f_cycle = is_cycle_call(&F, CG);
            func2cycle[&F] = f_cycle;
        }

//        for (auto & F_cycle : func2cycle) {
//            errs() << F_cycle.first->getName() << " is ";
//            errs() << CycleResult_toString(F_cycle.second) << '\n';
//        }
    }

    bool function_inline(Module &M, CallGraph &CG) {
        
        Fill_func2cycle(M, CG);
        std::vector<CallInst *> inline_calls;
        bool inlined = false;

        for (Function & F: M) {
            for (Instruction & inst : instructions(F)) {
                if (isa<CallInst>(inst)) {
                    CallInst * call_inst = cast<CallInst>(&inst);
                    Function * fptr = call_inst->getCalledFunction();

                    /**
                     *  Try to inline user-defined function
                     * */
                    if (fptr && IS_USER_FUNC(fptr)) {
                        if (func2cycle[fptr] == noCycle) {
                            inline_calls.push_back(call_inst);
                        } else {
                            // if (F.getName().str() == "main" 
                            //     && F.getInstructionCount() < 64
                            // ) {
                            //     inline_calls.push_back(call_inst);
                            // }
                        }

                    }
                }
                
            }
        }

        for (CallInst * call: inline_calls) {
            //errs() << "Inlining " << call->getCalledFunction()->getName();
            //errs() << " to " << call->getParent()->getParent()->getName() << "\n";
            InlineFunctionInfo  IFI;
            inlined |= InlineFunction(call, IFI);
        }
        
        //errs() << "Finish inlining\n";
        return inlined;
    }

    void get_used_function(
        Module & M, 
        CallGraph & CG, 
        std::set<Function *> & used_functions
    ) {
        

    }

        //naive GEN KILL IN OUT
    void sGEN_sKILL_init() {
        // std::vector<Value*> sGEN;
        // std::unordered_map<Value*, std::set<Value*>> sKILL;
        // std::unordered_map<Value*, std::set<Value*>> sVar2Def;
        // std::unordered_map<Value*, std::set<Value*>> sBB_GEN;
        // std::unordered_map<Value*, std::set<Value*>> sBB_KILL;
        // std::unordered_map<Value *, std::set<Value*>> sBB_IN, sBB_OUT;
        // std::unordered_map<Value *, std::set<Value*>> sIN, sOUT;

        sGEN.clear();
        sKILL.clear();
        sBB_GEN.clear();
        sBB_KILL.clear();
        sBB_IN.clear();
        sBB_OUT.clear();
        sIN.clear();    
        sOUT.clear();

        arg_set.clear();
        BB2CAT.clear();
    }

    void mpt_init() {
        // std::unordered_map<Value *, std::set<std::pair<Value*, Value*>>> mptGEN; // instruction -> {(p,x)}
        // std::unordered_map<Value *, std::set<std::pair<Value*, Value*>>> mptKILL; // instruction -> {(p,v)| v escaped}
        // std::unordered_map<Value *, std::set<Value *>> ptr2Val; // p->{x | for all x that (p,x) };
        // // std::unordered_map<Value *, std::set<Value *>> val2Ptr; // x->{p | for all p that (p,x) }
        // std::unordered_map<Value *, std::set<std::pair<Value*, Value*>>> mptIN;
        // std::unordered_map<Value *, std::set<std::pair<Value*, Value*>>> mptOUT;
        mptGEN.clear();
        mptKILL.clear();
        mptIN.clear();
        mptOUT.clear();
        ptr2Val.clear();
    }
    
    bool CAT_auto_trace_back(Value * val, Value ** real) {
        if (IN_MAP(auto2def, val)){
            *real = auto2def[val];
            return true;
        }

        if (!isa<IntToPtrInst>(val)) {
            return false;
        }
        
        IntToPtrInst * int2ptr = cast<IntToPtrInst>(val);
        Value * int2ptr_op0 = int2ptr->getOperand(0);    
        
        if(!isa<AShrOperator>(int2ptr_op0)){
            return false;
        }
        
        AShrOperator * ashr = cast<AShrOperator>(int2ptr_op0);
        Value * ashr_op0 = ashr->getOperand(0);
        
        if(!isa<ShlOperator>(ashr_op0)){
            return false;
        }

        ShlOperator * shl = cast<ShlOperator>(ashr_op0);
        Value * shl_op0 = shl->getOperand(0);
        
        if(!isa<PtrToIntInst>(shl_op0)){
            return false;
        }

        PtrToIntInst * ptr2int = cast<PtrToIntInst>(shl_op0);
        Value * ptr2int_op0 = ptr2int->getOperand(0);

        errs() << *val << " can be traced back as auto of " << *ptr2int_op0 << '\n';
        auto2def[val] = ptr2int_op0;
        *real = ptr2int_op0;
        return true;
    }

    void select_phi_trace_back(Value * val, std::vector<Value *> & res) {
        res.push_back(val);
        if (!isa<SelectInst>(val) && !isa<PHINode>(val)) return;

        if (isa<SelectInst>(val)){
            SelectInst * select = cast<SelectInst>(val);

            Value * op1 = select->getOperand(1);
            Value * op2 = select->getOperand(2);

            res.push_back(op1);
            res.push_back(op2);

            select_phi_trace_back(op1, res);
            select_phi_trace_back(op2, res);
        }
        
        if (isa<PHINode>(val)){
            PHINode * phi = cast<PHINode>(val);

            uint32_t numIncome = phi->getNumIncomingValues();
            for (uint32_t i = 0; i < numIncome; i++) {
                Value * arg = phi->getIncomingValue(i);
                res.push_back(arg);
            
                select_phi_trace_back(arg, res);
                select_phi_trace_back(arg, res);
            }
        }
    }


    void mptGEN_KILL(Function &F, AliasAnalysis & AA){

        // errs() << "Start: MPT GenKILL for " << F.getName() << '\n'; 
        findCATVar(F);

        std::unordered_map<Value *,std::set< Value *>> mpt_gen2ptr;
        // May-Point-To GEN
        for(auto &bb : F){
            for(auto &inst: bb){
                if(isa<StoreInst>(&inst)){
                    StoreInst *storeInst = cast<StoreInst>(&inst);
                    Value *valueStored = storeInst->getValueOperand();
                    Value *ptrOperand = storeInst->getPointerOperand();
                    // If p -> v
                    /**
                     *  %10 = select i1 %9, i8** %3, i8** %4
                     *  store i8* %11, i8** %10, align 8, !tbaa !2
                     *      only %10 is the real pointer being strongly defined here
                     *      we need to gen pairs including %3 or %4, but only pairs involving %10 should be killed later 
                     * */
                    mpt_gen2ptr[&inst].insert(ptrOperand);


                    std::vector<Value *> ptr_collect;
                    std::vector<Value *> value_collect;

                    select_phi_trace_back(ptrOperand, ptr_collect);
                    select_phi_trace_back(valueStored, value_collect);
                    
                    for (Value * ptr : ptr_collect) {
                        for (Value * val : value_collect) {
                            
                            mptGEN[&inst].insert(std::make_pair(ptr, val));
                            
                            ptr2Val[ptr].insert(val);
                        }
                    }

                    
                } else if (isa<CallInst>(&inst)) {
                    CallInst * call_instr = cast<CallInst>(&inst);
                    Function * callee_ptr = call_instr->getCalledFunction();

                    if (IS_CAT_OP(callee_ptr)) {
                        mptBB2CAT[&bb].push_back(&inst);
                        /**
                         *  Do nothing. CAT operation never changes point-to analysis
                         * */
                    } else if (IS_USER_FUNC(callee_ptr)) {
                        uint32_t num_arg = call_instr->getNumArgOperands();
                        for (uint32_t i = 0; i < num_arg; i++) {
                            Value * arg = call_instr->getArgOperand(i);

                            if (IS_PTR_TYPE(arg) && !IS_CAT_VAR(arg) ) {
                                /**
                                 *  This is a pointer but not a CAT variable
                                 *      This has the suspicion of being a pointer to CAT variable
                                 * */
                                ModRefInfo ModRefResult = AA.getArgModRefInfo(call_instr, i);
                                // errs() << " MPT user function: " << inst << " , arg = " << *arg << " ModRefResult = " << ModRefInfo_toString(ModRefResult) << '\n';
                                if (HAS_MOD(ModRefResult)) {
                                    /**
                                     *  If the pointer is modified
                                     *      we don't have info about where it points to 
                                     *      To be conservative, we say it points to everything and 
                                     * */
                                    Value * dummy = build_constint(0);

                                    mptBB2CAT[&bb].push_back(&inst);
                                    mptGEN[&inst].insert(
                                        std::make_pair(arg, dummy)
                                    );
                                    mpt_gen2ptr[&inst].insert(arg);
                                    
                                    /**
                                     *  As we don't know which it points to, create dummy const
                                     * */
                                    ptr2Val[arg].insert(dummy);
                                }
                            }
                        }
                    } else {
                        /**
                         *  Do nothing. standard lib function
                         * */
                    }
                }else if(isa<LoadInst>(&inst)||isa<PHINode>(&inst)||isa<SelectInst>(&inst)){
                    mptBB2CAT[&bb].push_back(&inst);
                }
            }
        }


        /**
         * Calculating Kill per instruction
         * */
        for (auto & kv : mptGEN) {
            // kv : [store inst, set<(p, v) pairs>]
            // StoreInst * storeInst = cast<StoreInst>(kv.first);
            for (Value * ptr : mpt_gen2ptr[kv.first]){
                for (Value * val : ptr2Val[ptr]) {
                    mptKILL[kv.first].insert(
                        std::make_pair(ptr, val)
                    );
                }
            }
            
        }
        
        // errs() << "Done: MPT GenKILL for " << F.getName() << '\n';
    }

    /**
     * return true if out is changed
     * */

    bool calc_mpt_IN2OUT(
        Instruction * inst
    ){
        std::set<std::pair<Value*,Value*>> tempOut;
        if (isa<StoreInst>(inst) ) {
            /**
             *  p = &x;
             *  OUT[i] = GEN[i] U (IN[i] – KILL[i])
             * */
            StoreInst * storeInst = cast<StoreInst>(inst);
            std::set<std::pair<Value*,Value*>> inMinusKill;
            set_diff(
                mptIN[inst],
                mptKILL[inst], 
                inMinusKill
            );

            set_union(
                inMinusKill,
                mptGEN[inst], 
                tempOut
            );

        } else if (isa<LoadInst>(inst)) {
            /**
             *  p = *q;
             *  OUT[i] = {(p,t) | (q,r)∈IN[i] & (r,t)∈ IN[i]} U (IN[i] – {(p,x) for all x})
             * */
            LoadInst * loadInst = cast<LoadInst>(inst);
            Value * q = loadInst->getPointerOperand();
            Value * p = loadInst;

            std::set<Value *> r_set;
            for (auto & qr : mptIN[loadInst]) {
                if (qr.first == q) {
                    r_set.insert(qr.second);
                }
            }

            for (auto & rt : mptIN[loadInst]) {
                if (IN_SET(r_set, rt.first)) {
                    tempOut.insert(std::make_pair(p, rt.second));
                }
            }

            std::set<std::pair<Value*,Value*>> inMinusKill = mptIN[loadInst];

            for (auto & px : mptIN[loadInst]) {
                if (px.first == p) {
                    inMinusKill.erase(px);
                }
            }

            tempOut.insert(inMinusKill.begin(), inMinusKill.end());

        } else if (isa<SelectInst>(inst) || isa<PHINode>(inst)){
            
            /** 
             *  p = q1 or q2 or ...
             *  %10 = select xxx, %8, %9
             *  OUT[i] = {(p,z) | (t,z) ∈ IN[i]} U {(p,z) | (q,z) ∈ IN[i]} U (IN[i] – {(p,x) for all x})
             * */
            Value * p;
            std::vector<Value *> q_ptrs;

            if (isa<SelectInst>(inst)) {
                SelectInst * select_inst = cast<SelectInst>(inst);
                p = cast<Value>(select_inst);
                q_ptrs.push_back(select_inst->getOperand(1));
                q_ptrs.push_back(select_inst->getOperand(2));

            } else if (isa<PHINode>(inst)) {
                PHINode * phi = cast<PHINode>(inst);
                p = cast<Value>(phi);
                uint32_t num_incoming = phi->getNumIncomingValues();

                for (uint32_t i = 0; i < num_incoming; i++) {
                    q_ptrs.push_back(phi->getIncomingValue(i));
                }
                
            }
            
            for (Value * q : q_ptrs) {
                /**
                 *  OUT[i] U= {(p,z) | (q,z) ∈ IN[i]}
                 * */
                for (auto & qz: mptIN[inst]){
                    if (qz.first == q) {
                        tempOut.insert(
                            std::make_pair(p, qz.second)
                        );
                    }
                }
            }
                
            // print_set_pairs(tempOut);
            // errs() << '\n';
            /**
             *  OUT[i] U= (IN[i] – {(p,x) for all x})
             * */
            std::set<std::pair<Value*,Value*>> inMinusAllp = mptIN[inst];
            for (auto & px : mptIN[inst]) {
                if (px.first == p) {
                    inMinusAllp.erase(px);
                }
            }
            tempOut.insert(inMinusAllp.begin(), inMinusAllp.end());
            // print_set_pairs(tempOut);
            // errs() << '\n';
        } else if (isa<CallInst>(inst)) {
            Function * fptr = get_callee_ptr(inst);
            if (IS_USER_FUNC(fptr)) {
                /**
                 *  OUT[i] = GEN[i] U (IN[i] – KILL[i])
                 * */
                std::set<std::pair<Value*,Value*>> inMinusKill;
                set_diff(
                    mptIN[inst],
                    mptKILL[inst], 
                    inMinusKill
                );

                set_union(
                    inMinusKill,
                    mptGEN[inst], 
                    tempOut
                );
            } else {
                /**
                 *  CAT op and other funcionts, do nothign
                 * */
                tempOut = mptIN[inst];
            }
        } else {
            /**
             *  Other type of instructions??
             * */
            tempOut = mptIN[inst];
        }   

        if (tempOut != mptOUT[inst]) {
//            errs()<<"BASIC BLOCK:\n";
//            errs()<<*inst->getParent()<<"\n";
//            errs()<<"INST:"<<*inst<<"\n";
//            errs()<<"BEFORE:\n";
//            for(auto& t:mptOUT[inst]){
//                errs()<<*t.first<<","<<*t.second<<"\n";
//            }
//            errs()<<"AFTER:\n";
//            for(auto& t:tempOut){
//                errs()<<*t.first<<","<<*t.second<<"\n";
//            }
            mptOUT[inst] = tempOut;
            return true;
        }

        return false;
    }

    void mptIN_OUT(Function &F){
        std::set<BasicBlock *> bb_calced;

        std::set<BasicBlock *> workList;
        std::unordered_map<Value *, std::set<std::pair<Value*,Value*>>> mptBB_GEN;
        std::unordered_map<Value *, std::set<std::pair<Value*,Value*>>> mptBB_KILL;
        std::unordered_map<Value *, std::set<std::pair<Value*,Value*>>> mptBB_IN;
        std::unordered_map<Value *, std::set<std::pair<Value*,Value*>>> mptBB_OUT;
        for(auto &B: F){
            mptBB_IN[&B].clear();
            mptBB_OUT[&B].clear();
            for(auto &I:mptBB2CAT[&B]){
                mptBB_GEN[&B].insert(mptGEN[I].begin(),mptGEN[I].end());
                mptBB_KILL[&B].insert(mptKILL[I].begin(),mptKILL[I].end());
            }
        }
        //errs()<<"BREAK POINT 1\n";
//        bool changed;
//        do{
//            changed = false;
//            for(BasicBlock &bb : F){
//                for(BasicBlock *Pred : predecessors(&bb)){
//                    std::set<std::pair<Value*, Value*>> temp3;
//                    set_union(mptBB_IN[&bb],mptBB_OUT[Pred],temp3);
//                    mptBB_IN[&bb]=temp3;
//                }
//                std::set<std::pair<Value*, Value*>>  out;
//                std::set<std::pair<Value*, Value*>>  temp;
//                //  TEMP = (IN[i]-KILL[i])
//                set_diff(mptBB_IN[&bb],mptBB_KILL[&bb],temp);
//                //  OUT = GEN[i] U TEMP
//                set_union(mptBB_GEN[&bb],temp,out);
//
//                if(!changed){
//                    changed = (out!=mptBB_OUT[&bb]);
//                }
//                mptBB_OUT[&bb] = out;
//            }
//
//        }while(changed);



        bool changed;
        do {
            changed = false;
            for (BasicBlock & bb : F) {
                Instruction *first_inst;
                //errs()<<"BREAK POINT 1\n";
                if(mptBB2CAT[&bb].empty()){
                    first_inst = &(*bb.begin());
                }else{
                    first_inst =cast<Instruction>(mptBB2CAT[&bb].front());
                }
                //errs()<<"BREAK POINT 2\n";

                //errs()<<"NOT EMPTY\n";
                //Instruction * first_inst = &(*bb.begin());

                //errs()<<"BREAK POINT 2\n";
                /**
                 *  Calculate IN of first instruction from OUT of predessors
                 * */
                //mptIN[first_inst].clear();
                for (BasicBlock * predBB : predecessors(&bb)) {
                    //Instruction * predBB_terminator = predBB->getTerminator();
                    Value *predBBTerminator;
                    if(mptBB2CAT[predBB].empty()){
                        predBBTerminator = predBB->getTerminator();
                    }else{
                        predBBTerminator = mptBB2CAT[predBB].back();
                    }
                    // IN[B] = U<p is predecessors of B>OUT[p]?

                    mptIN[first_inst].insert(
                        mptOUT[predBBTerminator].begin(),
                        mptOUT[predBBTerminator].end()
                    );
                    //errs()<<"BREAK POINT 3\n";
                }

                bool first_out_changed = calc_mpt_IN2OUT(first_inst);
                //errs()<<"CHANGING:"<<first_out_changed<<"\n";
//                for(auto& p:mptOUT[first_inst]){
//                    errs()<<*p.first<<", "<<*p.second<<"\n";
//                }
//                for(auto& p:mptOUT[first_inst]){
//                    errs()<<p.first<<", "<<p.second<<"\n";
//                }

                if (!changed) changed = first_out_changed;

                if (first_out_changed  || !IN_SET(bb_calced, &bb)) {
                    std::set<std::pair<Value*,Value*>> prevOut = mptOUT[first_inst];
                    //errs()<<"BREAK POINT 4\n";
                    if(mptBB2CAT[&bb].empty()){
                        //errs()<<"EMPTY\n";
                        Instruction *terminator = bb.getTerminator();
                        mptIN[terminator] = prevOut;
                        //mptOUT[terminator] = prevOut;
                        //errs()<<"BREAK POINT 7\n";
                        calc_mpt_IN2OUT(terminator);
                        //errs()<<"BREAK POINT 8\n";
                    }else{
                        for(auto &I:mptBB2CAT[&bb]){
                            Instruction * cur_ptr = cast<Instruction>(I);
                            mptIN[cur_ptr] = prevOut;

                            calc_mpt_IN2OUT(cur_ptr);

                            prevOut = mptOUT[cur_ptr];
                            //errs()<<"BREAK POINT 5\n";
                        }
                    }


//                    for (auto iter = (++bb.begin()); iter != bb.end(); iter++) {
//                        Instruction * cur_ptr = &*iter;
//                        mptIN[cur_ptr] = prevOut;
//
//                        calc_mpt_IN2OUT(cur_ptr);
//
//                        prevOut = mptOUT[cur_ptr];
//                    }

                    bb_calced.insert(&bb);
                }

            }

        } while(changed);


    }
        void mptIN_OUT_backup(Function &F){
            std::set<BasicBlock *> bb_calced;

            bool changed;
            do {
                changed = false;
                for (BasicBlock & bb : F) {
                    Instruction * first_inst = &(*bb.begin());

                    /**
                     *  Calculate IN of first instruction from OUT of predessors
                     * */
                    for (BasicBlock * predBB : predecessors(&bb)) {
                        Instruction * predBB_terminator = predBB->getTerminator();

                        mptIN[first_inst].insert(
                                mptOUT[predBB_terminator].begin(),
                                mptOUT[predBB_terminator].end()
                        );
                    }

                    bool first_out_changed = calc_mpt_IN2OUT(first_inst);

                    if (!changed) changed = first_out_changed;

                    if (first_out_changed  || !IN_SET(bb_calced, &bb)) {
                        std::set<std::pair<Value*,Value*>> prevOut = mptOUT[first_inst];

                        for (auto iter = (++bb.begin()); iter != bb.end(); iter++) {
                            Instruction * cur_ptr = &*iter;
                            mptIN[cur_ptr] = prevOut;

                            calc_mpt_IN2OUT(cur_ptr);

                            prevOut = mptOUT[cur_ptr];
                        }

                        bb_calced.insert(&bb);
                    }

                }

            } while(changed);


        }
    

    void findCATVar(Function &F){
        cat_var.clear();
        for(auto& inst:instructions(F)){
            if(isa<CallInst>(&inst)){
                CallInst *callInst = cast<CallInst>(&inst);
                Function *callee = callInst->getCalledFunction();
                if(IS_CAT_new(callee)){
                    cat_var.insert(&inst);
                } else if(IS_CAT_add(callee)||IS_CAT_sub(callee)){

                    int num = callInst->getNumArgOperands();
                    for(auto i = 0; i<num;i++){
                        Value *arg = callInst->getArgOperand(i);
                        cat_var.insert(arg);
                    }

                }else if(IS_CAT_set(callee)||IS_CAT_get(callee)){
                    Value *arg = callInst->getArgOperand(0);
                    cat_var.insert(arg);
                }

            }
        }
    }

    void mpt_wrap(Function &F, AliasAnalysis & AA) {
        //errs() << "MPT Analysis on " << F.getName() << '\n';
            //Timer timer;
            timer.start();
        mpt_init();
        mptGEN_KILL(F, AA);
            timer.stop();
            timer.printDuration("\t\tMPT GEN-KILL ");

            timer.start();
        // mptIN_OUT(F);
        mptIN_OUT_backup(F);
            timer.stop();
            timer.printDuration("\t\tMPT IN-OUT ");
        //errs() << "Done: MPT Analysis on " << F.getName() << '\n';
    }
        
    /**
     *  Expect arg to be a pointer 
     * */
    Instruction * dummy_instr_create() {
        Constant *zeroConst = ConstantInt::get(
                                    IntegerType::get(currentModule->getContext(), 32), 
                                    0, 
                                    true);

        Instruction *newInst = BinaryOperator::Create(Instruction::Add, zeroConst, zeroConst, "replacing");
        // errs() << *newInst << " at " << newInst << '\n';
        return newInst;
    }

    void GEN_record_info (
        Value * gen, 
        Value * var,
        std::unordered_map<Value *, Value*> & sGEN2var
    ) {
        sGEN.insert(gen);
        sVar2Def[var].insert(gen);
        sGEN2var[gen] = var;
    }

    Instruction * dummy_def_val(Value * val, CallInst * call_instr){
        Instruction * dummy = dummy_instr_create();

        userCall2replace[call_instr][val] = dummy;
        replace2userCall[dummy] = std::make_pair(call_instr, val);

        return dummy;
    }

    /**
     *  Given call instruction on CAT_set, CAT_add, CAT_sub
     *      find target of operation
     * */
    Value * get_define_target(
        CallInst * call_instr, 
        AliasAnalysis & AA,
        std::vector<Value *> & might_defines
    ) {

        Value * key = NULL;
        Value * arg0 = call_instr->getArgOperand(0);
        if (IS_CAT_new(get_callee_ptr(arg0)) ) {
            /**
             *  First argument is a CAT_new call
             * */
            key = arg0;
        
        } else if (isa<PHINode>(arg0)) {
            key = arg0;

        } else if (isa<Argument>(arg0)) {
            key = arg0;

        } else if (isa<LoadInst>(arg0)) {
            LoadInst * loadInst = cast<LoadInst>(arg0);
            Value * ptr = loadInst->getPointerOperand();
            Value * val = must_point2(call_instr, ptr);
            
            if (val){
                /**
                 *  Must point to val, so call_instr must define key
                 * */
                key = val;
            } else {
                /**
                 *  Otherwise, it points to many variables
                 * */
                key = arg0;
                for (auto & vardef : sVar2Def) {
                    Value * var = vardef.first;
                    if (CAT_Alias(AA, var, arg0) == AliasResult::MustAlias) {
                        key = var;   
                    }
                }
                
                /**
                 *  call_instr might also define the variables that pointed by ptr
                 *      where arg is a load from ptr
                 * */
                may_point2(call_instr, ptr, might_defines);

            }
        }

        return key;
    }

    void polulate_sVar2mightDef(std::vector<Value *> & might_defines, Instruction * inst) {
        for (Value * mightdef: might_defines){
            // errs() << *inst << " might define " << *mightdef << '\n';
            sVar2mightDef[mightdef].insert(inst);
        }
    }

    
    void sGEN_sKILL(Function &F, AliasAnalysis & AA){
        /**
         *  Map from gen (instruction) to variable that such gen defines
         *  Used to make life easier for KILL calculation
         * */
        std::unordered_map<Value *, Value*> sGEN2var;
        /**
         *  Handling GEN KILL for Function argument
         * */
        BasicBlock *entry = &F.getEntryBlock();
        for (Argument &arg:  F.args()){
            if (isa<PointerType>(arg.getType())) {
                //BB2CAT[entry].push_back(&arg);
       
                arg_set.insert(&arg);

                GEN_record_info(
                            &arg,    /* gen value */
                            &arg,    /* Variable that gen defines*/
                            sGEN2var /* local info recorder*/
                );
            } 
        }

        for(auto& BB:F){

            for(auto &inst:BB){
                if (isa<CallInst>(&inst)){
                    CallInst * call_instr = cast<CallInst>(&inst);
                    Function * callee_ptr = call_instr->getCalledFunction();

                    if (IS_CAT_OP(callee_ptr)) {
                        BB2CAT[&BB].push_back(&inst);

                        if (!IS_CAT_get(callee_ptr)) {

                            Value * key;
                            if (IS_CAT_new(callee_ptr)) {
                                key = call_instr;

                            } else {
                                // get first operand if CAT_set, CAT_add, CAT_sub
                                std::vector<Value *>  might_defines;
                                key =  get_define_target(call_instr, AA, might_defines);

                                polulate_sVar2mightDef(might_defines, &inst);
                            }

                            GEN_record_info(
                                    call_instr,    /* gen value */
                                    key,    /* Variable that gen defines*/
                                    sGEN2var /* local info recorder*/
                            );
                        }

                    } else if (IS_USER_FUNC(callee_ptr)){
                        // TODO: user function defines all arg
                        // we technically only cares about CAT obj, so we only care ptr argument
                        uint32_t num_arg = call_instr->getNumArgOperands();
                        for (uint32_t i = 0; i < num_arg; i++) {
                            Value * arg = call_instr->getArgOperand(i);

                            /**
                             * Possible solution:
                             *  for each ptr argument of user function f we generate a dummy instruction
                             *          we assume that instruction defines arg and alias of arg
                             *  The relation is recorded in the map callInst -> set of dummy instructions
                             *
                             * */
                            if (isa<PointerType>(arg->getType())) {
                                std::vector<Value *> possible_vals;

                                if (IS_CAT_VAR(arg)) {
                                    possible_vals.push_back(arg);
                                } else {
                                    /**
                                     *  Has the possibility of being a pointer to CAT_VAR
                                     * */
                                    may_point2(&inst, arg, possible_vals);
                                }

                                for (uint32_t j = 0; j < possible_vals.size(); j++) {

                                    MemoryLocation memLoc(possible_vals[j]);
                                    ModRefInfo info = AA.getModRefInfo(call_instr, memLoc);


                                    // errs() << *call_instr << " has arg " << *arg << " at " << arg;
                                    // errs() << "arg points to " << *possible_vals[j] <<  " with ModRefInfo = " << ModRefInfo_toString(info) <<'\n';
                                    if (HAS_MOD(info)){

                                        Value * dummy = dummy_def_val(possible_vals[j], call_instr);

                                        BB2CAT[&BB].push_back(dummy);
                                        GEN_record_info(
                                                dummy,               /* gen value, used dummy instruction as the gen*/
                                                possible_vals[j],    /* Variable that gen defines*/
                                                sGEN2var             /* local info recorder*/
                                        );
                                    }
                                }
                            }
                        }

                        /**
                         * If call instruction itself returns a pointer
                         * */
                        if (isa<PointerType>(call_instr->getType())) {
                            BB2CAT[&BB].push_back(call_instr);
                            GEN_record_info(
                                    call_instr,          /* pointer returns by funciont */
                                    call_instr,         /* defines itself*/
                                    sGEN2var             /* local info recorder*/
                            );
                        }
                    }

                } else if (isa<PHINode>(&inst)) {
                    PHINode * phi = cast<PHINode> (&inst);

                    /**
                     * only phi node with Pointer type we should care, right?
                     * */
                    if (isa<PointerType> (phi->getType())){
                        BB2CAT[&BB].push_back(phi);
                        GEN_record_info(
                                phi,          /* phi pointer */
                                phi,         /* defines itself*/
                                sGEN2var     /* local info recorder*/
                        );

                    }

                }
                // INST Loop
            }
            //BB Loop
        }


//        for (auto& inst: llvm::instructions(F)) {
//
//
//        }

        /**
         *  Generating KILL per instruction
         * */ 
        for (Value * gen: sGEN) {
            Value * var = sGEN2var[gen];
            sKILL[gen] = sVar2Def[var];
            sKILL[gen].erase(gen);
        }
    }

    void calc_BB_GEN_KILL(Instruction * inst, BasicBlock  * bb){
        if(IN_SET(sGEN, inst)){
            sBB_GEN[bb].insert(inst);
        }
        //TODO:Optimize
        std::set<Value*> temp;
        set_union(sBB_KILL[bb],sKILL[inst],temp);
        sBB_KILL[bb]=temp;

        std::set<Value*> temp2;
        set_diff(sBB_GEN[bb],sKILL[inst],temp2);
        sBB_GEN[bb]=temp2;

        // if(std::find(sGEN.begin(),sGEN.end(),&inst)!=sGEN.end()){
        if(IN_SET(sGEN, inst)){
            sBB_KILL[bb].erase(inst);
        }
    }
    void sIN_sOUT(Function &F){

        std::set<BasicBlock *> workList;

        /**
         * calculate GEN/KILL for each basic block
         * */
        for(auto &bb :F){
            sBB_IN[&bb] = std::set<Value*>();
            sBB_OUT[&bb] = std::set<Value*>();
            sBB_GEN[&bb] = std::set<Value*>();
            sBB_KILL[&bb] = std::set<Value*>();

            workList.insert(&bb);

            for(auto& I: BB2CAT[&bb]){
                if(!isa<Instruction>(I))
                    continue;
                Instruction *inst = cast<Instruction>(I);
                if (IN_MAP(userCall2replace, inst)){
                    calc_BB_GEN_KILL(inst, &bb);
                    for (auto & kv : userCall2replace[inst]) {
                        Instruction * dummy_instr = kv.second;
                        calc_BB_GEN_KILL(dummy_instr, &bb);
                    }
                } else {
                    calc_BB_GEN_KILL(inst, &bb);
                }
            }
        }

        /**
         * add arguments defs to IN of first BB
         * */
        BasicBlock * first_bb = &F.getBasicBlockList().front();
        sBB_IN[first_bb].insert(arg_set.begin(), arg_set.end());
        


        /**
         * calculate IN/OUT for each basic block
         * TODO: optimize with worklist!!
         * */
        std::set<Value*> oldOUT;
        while(!workList.empty()){
            BasicBlock *B = *workList.begin();
            workList.erase(B);

            oldOUT = sBB_OUT[B];
            /**
             * IN[B] = U <p pred of B> OUT[p]
             */
            for(BasicBlock *Pred : predecessors(B)){
                std::set<Value*> temp3;
                set_union(sBB_IN[B],sBB_OUT[Pred],temp3);
                sBB_IN[B]=temp3;
            }
            std::set<Value*> out;
            std::set<Value*> temp;
            //  TEMP = (IN[i]-KILL[i])
            set_diff(sBB_IN[B],sBB_KILL[B],temp);
            //  OUT = GEN[i] U TEMP
            set_union(sBB_GEN[B],temp,out);
            sBB_OUT[B] = out;
            if(oldOUT!=sBB_OUT[B]){
                std::set<BasicBlock*> sucSet;
                for(BasicBlock *Suc : successors(B)){
                    sucSet.insert(Suc);
                }
                set_union(workList,sucSet,workList);
            }

        }
//        bool changed;
//        do{
//            changed = false;
//            for(BasicBlock &bb : F){
//                for(BasicBlock *Pred : predecessors(&bb)){
//                    std::set<Value*> temp3;
//                    set_union(sBB_IN[&bb],sBB_OUT[Pred],temp3);
//                    sBB_IN[&bb]=temp3;
//                }
//                std::set<Value*> out;
//                std::set<Value*> temp;
//                //  TEMP = (IN[i]-KILL[i])
//                set_diff(sBB_IN[&bb],sBB_KILL[&bb],temp);
//                //  OUT = GEN[i] U TEMP
//                set_union(sBB_GEN[&bb],temp,out);
//
//                if(!changed){
//                    changed = (out!=sBB_OUT[&bb]);
//                }
//                sBB_OUT[&bb] = out;
//            }
//        }while(changed);

    }

    void sIN_sOUT_backup(Function &F){

            /**
             * calculate GEN/KILL for each basic block
             * */
            for(auto &bb :F){
                sBB_IN[&bb] = std::set<Value*>();
                sBB_OUT[&bb] = std::set<Value*>();
                sBB_GEN[&bb] = std::set<Value*>();
                sBB_KILL[&bb] = std::set<Value*>();

                for(llvm::Instruction &inst :bb){

                    if (IN_MAP(userCall2replace, &inst)){
                        calc_BB_GEN_KILL(&inst, &bb);
                        for (auto & kv : userCall2replace[&inst]) {
                            Instruction * dummy_instr = kv.second;
                            calc_BB_GEN_KILL(dummy_instr, &bb);
                        }
                    } else {
                        calc_BB_GEN_KILL(&inst, &bb);
                    }
                }

                // errs() << "Basic block GEN : " << bb << '\n';
                // print_set_with_addr(sBB_GEN[&bb]);
                // errs() << "Basic block KILL : " << bb << '\n';
                // print_set_with_addr(sBB_KILL[&bb]);
            }

            /**
             * add arguments defs to IN of first BB
             * */
            BasicBlock * first_bb = &F.getBasicBlockList().front();
            sBB_IN[first_bb].insert(arg_set.begin(), arg_set.end());



            /**
             * calculate IN/OUT for each basic block
             * TODO: optimize with worklist!!
             * */
            bool changed;
            do{
                changed = false;
                for(BasicBlock &bb : F){
                    for(BasicBlock *Pred : predecessors(&bb)){
                        std::set<Value*> temp3;
                        set_union(sBB_IN[&bb],sBB_OUT[Pred],temp3);
                        sBB_IN[&bb]=temp3;
                    }
                    std::set<Value*> out;
                    std::set<Value*> temp;
                    //  TEMP = (IN[i]-KILL[i])
                    set_diff(sBB_IN[&bb],sBB_KILL[&bb],temp);
                    //  OUT = GEN[i] U TEMP
                    set_union(sBB_GEN[&bb],temp,out);

                    if(!changed){
                        changed = (out!=sBB_OUT[&bb]);
                    }
                    sBB_OUT[&bb] = out;
                }
            }while(changed);

        }

    void __INSTR_INOUT(std::set<Value*> & prev_out, Instruction * inst) {

        std::set<Value*> local_INSTR_IN = prev_out;

        //TODO: need to be replaced by bitwise_diff function later
        std::set<Value*> local_INSTR_OUT = local_INSTR_IN;
        if(!IN_SET(sGEN,inst)&&sKILL[inst].empty()){
            sIN[inst] = local_INSTR_IN;
            sOUT[inst] = local_INSTR_OUT;
            prev_out = local_INSTR_OUT;
            return;
        }

        /**
         * IN[i] - KILL[i]
         * */
        std::set<Value*> temp;
        set_diff(local_INSTR_IN, sKILL[inst], temp);
        local_INSTR_OUT = temp;
        /**
         * OUT[i] = GEN[i] U (IN[i] - KILL[i])
         * */
        if(IN_SET(sGEN, inst)){
            local_INSTR_OUT.insert(inst);
        }

        sIN[inst] = local_INSTR_IN;
        sOUT[inst] = local_INSTR_OUT;

        prev_out = local_INSTR_OUT;
    }

    void sIN_OUT_inst(Function &F){
        for (BasicBlock &bb : F){
            std::set<Value*> prev_out = sBB_IN[&bb];
            // errs() << "Basic block IN : " << bb << '\n';
            // print_set_with_addr(prev_out);
//            if(sBB_GEN[&bb].empty()&&sBB_KILL[&bb].empty())
//                continue;
            for(auto &I : BB2CAT[&bb]){
                if(isa<Instruction>(I)){
                    Instruction *inst = cast<Instruction>(I);
                    if (IN_MAP(userCall2replace, inst)){
                        /**
                         * This is a instruction that calls others
                         * IN[i] should just be the previous IN
                         * OUT[i] should be the last OUT produced by arguments replacement
                         */
                        __INSTR_INOUT(prev_out, inst);
                        sIN[inst] = prev_out;
                        for (auto & kv : userCall2replace[inst]) {
                            Instruction * dummy_instr = kv.second;
                            __INSTR_INOUT(prev_out, dummy_instr);
                            sOUT[inst] = prev_out;
                        }

                    } else {
                        /**
                         * This is a normal instruction should be good with what we have done before
                         */
                        __INSTR_INOUT(prev_out, inst);
                    }
                }

                
            }
        }
    }
    
    void reachingDef_cleanup() {
        for (auto & dummy_userCall : replace2userCall) {
            // dummy_userCall.first->eraseFromParent(); 
        }   
    }
    void reachingDef_wrap(Function &F, AliasAnalysis & AA) {
        //errs() << "Reaching definition on " << F.getName() << '\n';
        //Timer timer;
            timer.start();
        sGEN_sKILL_init();
        sGEN_sKILL(F, AA);
            timer.stop();
            timer.printDuration("\t\tREACHING DEF GEN-KILL ");
        //print_gen_kill(caller_name,F);
            timer.start();
        sIN_sOUT(F);
            timer.stop();
            timer.printDuration("\t\tREACHING DEF IN-OUT BB ");

            timer.start();
        sIN_OUT_inst(F);
            timer.stop();
            timer.printDuration("\t\tREACHING DEF IN-OUT INST ");
        // print_in_out(F);
        //errs() << "Done: Reaching definition on " << F.getName() << '\n';
    }
    

    void print_in_out(Function &F){
        errs() << "Function \"" << F.getName() << "\" " << '\n';
        unsigned inst_counter = 0;
        for (BasicBlock &bb : F){
            for(Instruction &inst : bb){
                errs() << "INSTRUCTION: " << inst << '\n';
                errs() << "***************** IN\n{\n";
                // print_set(sIN[&inst]);
                print_set_with_addr(sIN[&inst]);
                errs() << "}\n";
                errs() << "**************************************\n";
                errs() << "***************** OUT\n{\n";


                // print_set(sOUT[&inst]);
                print_set_with_addr(sOUT[&inst]);
                errs() << "}\n";
                errs() << "**************************************\n";
                errs() << "\n\n\n";
                inst_counter++;
            }
        }

    }
    void print_gen_kill(std::string &func_name, Function &F){
        errs() << "Function \"" << func_name << "\" " << '\n';
        for (auto& inst:instructions(F)){
            errs() << "INSTRUCTION: " << inst << '\n';
            errs() << "***************** GEN\n{\n";
            // if(std::find(sGEN.begin(),sGEN.end(),&inst)!=sGEN.end()){
            if(IN_SET(sGEN, &inst)){
                errs() << " " << inst << '\n';
            }
            errs() << "}\n";


            errs() << "**************************************\n";
            errs() << "***************** KILL\n{\n";
            for(auto& kill: sKILL[&inst]){
                errs() << " " << *kill << '\n';
            }
            errs() << "}\n";
            errs() << "**************************************\n";
            errs() << "\n\n\n";
        }
    }


    void print_mpt_GENKILL(Function &F){
        errs() << "Function \"" << F.getName() << "\" " << '\n';
        unsigned inst_counter = 0;
        for (BasicBlock &bb : F){
            for(Instruction &inst : bb){
                errs() << "INSTRUCTION: " << inst << '\n';
                errs() << "***************** MPT GEN\n{\n";
                // print_set(sIN[&inst]);
                print_set_pairs(mptGEN[&inst]);
                errs() << "}\n";
                errs() << "**************************************\n";
                errs() << "***************** MPT KILL\n{\n";


                // print_set(sOUT[&inst]);
                print_set_pairs(mptKILL[&inst]);
                errs() << "}\n";
                errs() << "**************************************\n";
                errs() << "\n\n\n";
                inst_counter++;
            }
        }

    }

    void print_mpt_INOUT(Function &F){
        errs() << "Function \"" << F.getName() << "\" " << '\n';
        unsigned inst_counter = 0;
        for (BasicBlock &bb : F){
            for(Instruction &inst : bb){
                errs() << "INSTRUCTION: " << inst << '\n';
                errs() << "***************** MPT IN\n{\n";
                // print_set(sIN[&inst]);
                print_set_pairs(mptIN[&inst]);
                errs() << "}\n";
                errs() << "**************************************\n";
                errs() << "***************** MPT OUT\n{\n";


                // print_set(sOUT[&inst]);
                print_set_pairs(mptOUT[&inst]);
                errs() << "}\n";
                errs() << "**************************************\n";
                errs() << "\n\n\n";
                inst_counter++;
            }
        }

    }
    void print_set_with_addr(std::set<Value*> const& p_set){
        for(auto& i:p_set){
            errs() << " " << *i << " at " << i << '\n';
        }
    }

    void print_set_pairs(std::set<std::pair<Value*, Value*>> const& p_set){
        for(auto& kv:p_set){
            errs() << " (" << *kv.first << " , " << *kv.second << ")\n";
        }
    }

    void print_set(std::set<Value*> const& p_set){
        for(auto& i:p_set){
            errs() << " " << *i << '\n';
        }
    }


    void H0_init(){
        fptr2cnt = std::unordered_map<Function *, int>();
    }
    /**
     * populate fptr2cnt map
     * */
    void H0_function_count(Function &F) {

        for (auto& inst: llvm::instructions(F)) {
        
            if (isa<CallInst>(&inst)){
                // errs() << inst;
                CallInst *callInst = cast<CallInst>(&inst);
                Function * callee_ptr = callInst->getCalledFunction();
            
                if (fptr2name.find(callee_ptr) != fptr2name.end()) {
                    if (fptr2cnt.find(callee_ptr) == fptr2cnt.end()) {
                        fptr2cnt[callee_ptr] = 0;
                    }
                    fptr2cnt[callee_ptr] = fptr2cnt[callee_ptr] + 1;
                }
            }
        }
    }

    void H0_output(std::string & func_name) {
        for (const auto& kv : fptr2cnt) {
            errs() << "H0: \"" << func_name << "\": " << fptr2name[kv.first]  << ": " << kv.second << "\n";
        }
    }

    void H1_init(Function &F) {
        unsigned NumInstrs = F.getInstructionCount();

        GEN = llvm::BitVector(NumInstrs, 0);
        KILL = std::vector<llvm::BitVector>(NumInstrs, llvm::BitVector(NumInstrs, 0));
        instr_vec = std::vector<llvm::Instruction *>(NumInstrs, NULL);
        instr2bitmap = std::unordered_map<void *, llvm::BitVector>();
    }

    void H1_GEN_KILL(Function &F) {
        unsigned NumInstrs = F.getInstructionCount();
        // std::unordered_map<void *, llvm::BitVector> instr2bitmap;
        unsigned i = 0;
        
        for (auto& inst: llvm::instructions(F)) {
            instr_vec[i] = &inst;
            // errs()<<"INSTR: "<<inst<<" at "<<&inst<<"\n";
           if (isa<CallInst>(&inst)){
                CallInst * call_instr = cast<CallInst>(&inst);
                Function * callee_ptr = call_instr->getCalledFunction();

                if (fptr2name.find(callee_ptr) != fptr2name.end()) {
                    // find one call_instr that calls one of CAT functions  
                    std::string callee_name = fptr2name[callee_ptr];
                    if (callee_name != "CAT_get") {
                        
                        GEN.set(i);

                        // if (callee_name == "CAT_new") {
                        //     instr2bitmap[call_instr] = llvm::BitVector(NumInstrs, 0);
                        //     instr2bitmap[call_instr].set(i);
                        // } else {
                        //     // get first operand if CAT_set, CAT_add, CAT_sub
                        //     void * arg0 = call_instr->getArgOperand(0);
                        //     errs()<< arg0 << "\n";
                        //     instr2bitmap[arg0].set(i);
                        // }
                        void * key;
                        if (callee_name == "CAT_new") {
                            key = call_instr;
                        } else {
                            // get first operand if CAT_set, CAT_add, CAT_sub
                            void * arg0 = call_instr->getArgOperand(0);
                            key = arg0;
                        }
                        
                        if (instr2bitmap.find(key) == instr2bitmap.end()) {
                            instr2bitmap[key] = llvm::BitVector(NumInstrs, 0);
                        }

                        instr2bitmap[key].set(i);

                    }   
                }
            }
            i++;
        }


        for (i = 0; i < instr_vec.size(); i++) {
            if (GEN.test(i)) {
                // This is a GEN, either, CAT_new, CAT_set, CAT_add, CAT_sub
                CallInst * call_instr = cast<CallInst>(instr_vec[i]);
                void * arg0 = call_instr->getArgOperand(0);
                if (instr2bitmap.find(arg0) != instr2bitmap.end()) {
                    // This must be a CAT_set, CAT_add, CAT_sub
                    KILL[i] = instr2bitmap[arg0];
                } else {
                    // must be a CAT_new
                    KILL[i] = instr2bitmap[call_instr];
                }

                // it should not kill itself
                KILL[i].flip(i);
            }
        }
    }

    void H1_output(std::string & func_name ) {
        errs() << "Function \"" << func_name << "\" " << '\n';
        for (int i = 0; i < instr_vec.size(); i++){
            errs() << "INSTRUCTION: " << *instr_vec[i] << '\n';
            errs() << "***************** GEN\n{\n";
            if (GEN.test(i)) {
                errs() << " " << *instr_vec[i] << '\n';
            }
            errs() << "}\n";


            errs() << "**************************************\n";
            errs() << "***************** KILL\n{\n";
            if (KILL[i].any()) {
                for (int j = 0; j < instr_vec.size(); j++ ) {
                    if (KILL[i].test(j)) {
                        errs() << " " << *instr_vec[j] << '\n';
                    }
                }
            }
            errs() << "}\n";
            errs() << "**************************************\n";
            errs() << "\n\n\n";
        }
    }

    void H2_init(Function &F){
        BB_IN = std::unordered_map<llvm::BasicBlock *, llvm::BitVector>();
        BB_OUT = std::unordered_map<llvm::BasicBlock *, llvm::BitVector>();
        BB_GEN = std::unordered_map<llvm::BasicBlock *, llvm::BitVector>();
        BB_KILL = std::unordered_map<llvm::BasicBlock *, llvm::BitVector>();

        INSTR_IN = std::unordered_map<llvm::Instruction *, llvm::BitVector>();
        INSTR_OUT = std::unordered_map<llvm::Instruction *, llvm::BitVector>();
    }

    // return A - B
    llvm::BitVector bitwise_diff(llvm::BitVector & A, llvm::BitVector & B) {
        llvm::BitVector res = A;
        llvm::BitVector neg_B = B;
        neg_B.flip();
        res &= neg_B;
        return res;
    }

    void H2_IN_OUT(Function &F){
        unsigned NumInstr = F.getInstructionCount();
        unsigned inst_counter = 0;
        //Generating GEN/KILL FOR BB
        BasicBlock &entry = F.getEntryBlock();
        errs()<<"ENTRY: "<<F.getName()<<"\n";
        for(auto& i: entry){
            errs()<<i<<"\n";
        }
        for (llvm::BasicBlock &bb : F){
            //probably number of instr in a b
            BB_IN[&bb] = BitVector(NumInstr, 0);
            BB_OUT[&bb] = BitVector(NumInstr, 0);
            BB_GEN[&bb] = llvm::BitVector(NumInstr,0);
            BB_KILL[&bb] = llvm::BitVector(NumInstr, 0);


            // Mapping <BasicBlock *, BitVector>
            for(llvm::Instruction &inst :bb){
                //only extract bits that belongs to this BB
                if(GEN.test(inst_counter)){
                    BB_GEN[&bb].set(inst_counter);
                }
                //TODO: Verify if this operation is correct.
                BB_KILL[&bb] |= KILL[inst_counter];

                BB_GEN[&bb] = bitwise_diff(BB_GEN[&bb], KILL[inst_counter]);
                if (GEN[inst_counter]) BB_KILL[&bb][inst_counter] = 0;
                inst_counter++;
            }
             
        }
        // IN/OUT
        bool changed;
        do{
            changed = false;
            for(BasicBlock &bb : F){
                for(BasicBlock *Pred : predecessors(&bb)){
                    //TODO: UNION?????
                    BB_IN[&bb] |= BB_OUT[Pred];
                }
                //TODO:Verify Old OUT is changed
                BitVector OUT_TEMP = BB_IN[&bb];
                BitVector INTERSECTION = BB_KILL[&bb];
                INTERSECTION &= BB_IN[&bb];
                OUT_TEMP ^= INTERSECTION;
                OUT_TEMP |= BB_GEN[&bb];
                
                if (!changed) changed = (OUT_TEMP!=BB_OUT[&bb]);
                BB_OUT[&bb] = OUT_TEMP;
            }
        }while(changed);

    }

    void H2_output(std::string &func_name, Function &F){
        errs() << "Function \"" << func_name << "\" " << '\n';
        unsigned inst_counter = 0;
        for (BasicBlock &bb : F){
            for(Instruction &inst : bb){
                errs() << "INSTRUCTION: " << inst << '\n';
                errs() << "***************** IN\n{\n";
                print_bitvector(INSTR_IN[&inst]);
                errs() << "}\n";
                errs() << "**************************************\n";
                errs() << "***************** OUT\n{\n";


                print_bitvector(INSTR_OUT[&inst]);
                errs() << "}\n";
                errs() << "**************************************\n";
                errs() << "\n\n\n";
                inst_counter++;
            }
        }

    }

    void instruction_IN_OUT( Function &F){
        unsigned inst_counter = 0;
        for (BasicBlock &bb : F){
            BitVector local_INSTR_IN = BB_IN[&bb];
            BitVector local_INSTR_OUT = BB_IN[&bb];
            for(Instruction &inst : bb){
                local_INSTR_IN = local_INSTR_OUT;

                
                //TODO: need to be replaced by bitwise_diff function later
                BitVector OUT_TEMP = local_INSTR_IN;
                BitVector INTERSECTION = KILL[inst_counter];
                INTERSECTION &= local_INSTR_IN;
                OUT_TEMP ^= INTERSECTION;
                if(GEN.test(inst_counter)){
                    OUT_TEMP.set(inst_counter);
                }

                local_INSTR_OUT = OUT_TEMP;


                INSTR_IN[&inst] = local_INSTR_IN;
                INSTR_OUT[&inst] = local_INSTR_OUT;
                inst_counter++;
            }
        }
    }


    // return the callee fptr if inst_ptr is call function
    Function * get_callee_ptr(Value * inst_ptr) {
        if (isa<CallInst>(inst_ptr)){
            return cast<CallInst>(inst_ptr)->getCalledFunction();
        }
        return NULL;
    }

    template<class T>
    bool vec_all_equal(std::vector<T> &v) {
        if (v.size() == 0) return true;
        T head = v[0];
        for (unsigned i = 1; i < v.size(); i++) {
            if (head != v[i]) return false; 
        }
        return true;
    }

    bool VAL_vec_all_equal(std::vector<Value *> &v) {
        /**
         * Needs to be fixed
         * 
         * */
        if (v.size() <= 1) return true;
        
        for (unsigned i = 0; i < v.size(); i++) {
            if (!isa<ConstantInt>(v[i])) return false;
        }

        int64_t head = cast<ConstantInt>(v[0])->getSExtValue();
        for (unsigned i = 0; i < v.size(); i++) {
            int64_t curr = cast<ConstantInt>(v[i])->getSExtValue();

            if (head != curr) return false; 
        }
        return true;
    }

    template<typename T>
    bool vec_is_equal(std::vector<T> const &v1, std::vector<T> const &v2)
    {
        return (v1.size() == v2.size() &&
                std::equal(v1.begin(), v1.end(), v2.begin()));
    }


    // create set instruction before cat_add or cat_sub
    Value * build_cat_set(CallInst * call_instr, Value * set_val) {
        IRBuilder<> builder(call_instr);
        std::vector<Value *> arg_vec;
        arg_vec.push_back(call_instr->getArgOperand(0));

        // Type * llvm_int64 =  IntegerType::get(currentModule->getContext(), 64);
        // Value * val = ConstantInt::get(llvm_int64, set_val, true);
        arg_vec.push_back(set_val);
        ArrayRef<Value *> arg_arr_ref = ArrayRef<Value *>(arg_vec);
        // arg_arr.
        Value * added_inst = builder.CreateCall(CAT_set_ptr, arg_arr_ref);
        return added_inst;
    }


    Value *build_constint(int64_t num) {
        Type * llvm_int64 =  IntegerType::get(currentModule->getContext(), 64);
        Value * val = ConstantInt::get(llvm_int64, num, true);
        return val;
    }

    Value * build_const_phi (Instruction * inst, PHINode * phi, std::vector<Value *> & temp_vals) {
        IRBuilder<> builder(phi);
        Type * llvm_int64 =  IntegerType::get(currentModule->getContext(), 64);

        PHINode * const_phi = builder.CreatePHI(
            llvm_int64,
            phi->getNumIncomingValues(),
            "const_phi"
        );

        for (uint32_t i = 0; i < phi->getNumIncomingValues(); i++) {
            const_phi->addIncoming(
                temp_vals[i],
                phi->getIncomingBlock(i)
            );
        }

        return const_phi;
    }
    
    PHINode * create_const_phi (PHINode * phi, std::vector<Value *> & temp_vals) {
        Type * llvm_int64 =  IntegerType::get(currentModule->getContext(), 64);

        PHINode * const_phi = PHINode::Create(
            llvm_int64,
            phi->getNumIncomingValues(),
            "const_phi"
        );

        for (uint32_t i = 0; i < phi->getNumIncomingValues(); i++) {
            const_phi->addIncoming(
                temp_vals[i],
                phi->getIncomingBlock(i)
            );
        }
        //errs() << "Creating const phi " << *const_phi << " before " << *phi << '\n';
        return const_phi;
    }

    PHINode * create_artificial_phi (std::vector<Value *> & temp_vals, std::vector<BasicBlock *> & BBs) {
        

        Type * llvm_int64 =  IntegerType::get(currentModule->getContext(), 64);

        PHINode * artificial_phi = PHINode::Create(
            llvm_int64,
            temp_vals.size(),
            "artificial_phi"
        );

        for (uint32_t i = 0; i < temp_vals.size(); i++) {
            artificial_phi->addIncoming(
                temp_vals[i],
                BBs[i]
            );
        }
        //errs() << "Creating artificial_phi " << *artificial_phi  << " at " << artificial_phi << '\n';
        return artificial_phi;
    }

    CallInst * create_CAT_get (Value * var) {
        Type * llvm_int64 =  IntegerType::get(currentModule->getContext(), 64);
        
        ArrayRef<Value *> arg_arr_ref{
            var
        };
        
        CallInst * cat_get = CallInst::Create(
            CAT_get_ptr, 
            var
        );
        return cat_get;
    }

    Value * build_add_sub(CallInst * call, Value * arg1_val, Value * arg2_val) {
        Function * fptr = call->getCalledFunction();
        IRBuilder<> builder(call);
        Value * result = NULL;

        if (IS_CAT_sub(fptr)) {
            result = builder.CreateSub(
                arg1_val,
                arg2_val,
                "folding val"
            );
        } else if(IS_CAT_add(fptr)) {
            result = builder.CreateAdd(
                arg1_val,
                arg2_val,
                "folding val"
            );
        } else {
            /**
             *  Not supposed to be other functions
             * */
        }

        return result;
    }

    /**
     *  return all (p, v) pairs that has p == ptr in 
     * */
    void mpt_ptr_selection(
        Instruction * instr, 
        Value * ptr, 
        std::vector<std::pair<Value *, Value *>> & res
    ) {
        for (auto &pv: mptIN[instr]) {
            if (pv.first == ptr) {
                res.push_back(pv);
            }
        }
    }

    /**
     *  append every thing that @ptr might point to right before @instr to vals
     * */
    void may_point2(Instruction * instr, Value * ptr, std::vector<Value *> & vals) {
        
        for (auto &pv: mptIN[instr]) {
            if (pv.first == ptr) {
                vals.push_back(pv.second);
            }
        }
    }

    /**
     *  return NULL if it's not must point to 
     * */
    Value * must_point2(Instruction * instr, Value * ptr) {
        std::vector<Value *> vals;
        for (auto &pv: mptIN[instr]) {
            if (pv.first == ptr) {
                vals.push_back(pv.second);
            }
        }

        if(vals.size() != 1) return NULL;
        
        return vals[0];
    }

    AliasResult CAT_Alias(AliasAnalysis & AA, Value * valA, Value * valB) {
        AliasResult AAResult = AA.alias(valA, valB);  
        
        // Strong enough
        if (AAResult == AliasResult::MustAlias){
            return AAResult;
        }

        if (isa<LoadInst>(valA) && isa<LoadInst>(valB)) {
            LoadInst * loadA = cast<LoadInst>(valA);
            LoadInst * loadB = cast<LoadInst>(valB);
            Value * ptrA = loadA->getPointerOperand();
            Value * ptrB = loadB->getPointerOperand();
            
            if (ptrA == ptrB || AA.alias(ptrA, ptrB) == AliasResult::MustAlias) {
                /**
                 *  if ptrA == ptrB or ptrA mustAlias ptrB
                 *      if mptIN[loadA][ptrA] == mptIN[loadB][ptrB] -> two load are the same
                 *          return mustAlias
                 * 

                 * */
                
                std::vector<std::pair<Value *, Value *>> pv_pairA, pv_pairB;
                mpt_ptr_selection(loadA, ptrA, pv_pairA);
                mpt_ptr_selection(loadB, ptrB, pv_pairB);

                if (vec_is_equal(pv_pairA, pv_pairB)){
                    return AliasResult::MustAlias;
                }
                
            }
        }
        return AAResult;
    }

    /**
     *  Wrapper with AliasAnalysis.
     *  If we arg MUST Alias with some CAT_var, we are same to claim it's constant
     *          as long as one of them is constant in terms of reaching definition of instr
     * */

    bool check_constant_AA_wrap(AliasAnalysis & AA, Instruction * instr, Value * arg, int64_t * res) {
        std::vector<Value *> aliases;
        aliases.push_back(arg);
        
        for (auto & var : cat_var) {
            if (var != arg){
                AliasResult AAResult = CAT_Alias(AA, var, arg);

                // errs() << "At instruction : " << *instr; 
                // errs() << *arg << " at " << arg << " alias with " << *var << " at " << var;
                // errs() << " with result = " << AliasResult_toString(AAResult) << '\n';
                if (AAResult == AliasResult::MustAlias) {
                    aliases.push_back(var);
                }
            }
            
        }

        /**
         * If one alias is sure to be constant we should be good to propogate
         * */
        int64_t temp_val;
        for (uint32_t i = 0; i < aliases.size(); i++) {
            if(check_constant_s(instr, aliases[i], &temp_val)) {
                *res = temp_val;
                return true;
            }
        }
        
        if (isa<LoadInst>(arg)) {
            LoadInst * loadInst = cast<LoadInst>(arg);
            Value * ptr = loadInst->getPointerOperand();

            if (Value * val  = must_point2(instr, ptr)) {
                //errs() << "At instruction : " << *instr;
                //errs() << " the load result must be " << *val << '\n';
                if(check_constant_s(instr, val, &temp_val)) {
                    *res = temp_val;
                    return true;
                }
            }
        }
        return false;
    }

    bool check_constant_s(Instruction * instr, Value * arg, int64_t * res) {
        
        /**
         * Find the intersection between reaching definition of instr and definitions that define arg
        */
        std::set<Value *> arg_defs;
        // set_intersect(sIN[instr], sVar2Def[arg], arg_defs);
        set_union(sVar2Def[arg], sVar2mightDef[arg], arg_defs);
        set_intersect(sIN[instr], arg_defs, arg_defs);
        // errs() << "arg_defs of " << *arg  <<  " at " << *instr << " = \n";
        // print_set_with_addr(arg_defs);
        
        // errs() << "sVar2mightDef[arg] = \n";
        // print_set_with_addr(sVar2mightDef[arg]);
        
        /**
         * No available reaching definition
         * */
        if (arg_defs.size() == 0) return false; 
        /**
         * Expected vector of constants
         * */
        std::vector<int64_t> const_vec (arg_defs.size());
        uint32_t idx = 0;

        for (auto & def : arg_defs) {
            bool is_const = check_constant_val(def, &const_vec[idx]);
            
            /**
             * false immediately if one any of the definition is not a constant
             * */
            if (!is_const) return false;
            
            idx++;
        }

        if (vec_all_equal(const_vec)){
            *res = const_vec[0];
            return true;
        }

        return false;

    }

    /**
     *  check if given @val defines a constant
     *  if so result is stored in res, and return true
     *  otherwise return false, res is not touched
     * */ 
    bool check_constant_val(Value * def, int64_t * res) {
        /**
         * If the imcoming node is a Argument definition, it's not a constant, so far
         * */
        if (isa<Argument>(def)) {
            return false;
        }


        /**
         * If the imcoming node is Phi Node definition, we recursively check if each of its incoming value is constant
         * */
        if (isa<PHINode>(def)){
            PHINode * phi = cast<PHINode>(def);
            uint32_t numIncoming = phi->getNumIncomingValues();
            std::vector<int64_t> temp_val_arr(numIncoming);

            for (uint32_t i = 0; i < numIncoming; i++) {
                Value * inValue = phi->getIncomingValue(i);
                if (!check_constant_val(inValue, &temp_val_arr[i]) ){
                    return false;
                }
            }

            if (vec_all_equal(temp_val_arr) && temp_val_arr.size() > 0){
                *res = temp_val_arr[0];
                return true;
            }

            return false;
        }  

        /**
         * If the imcoming node is a replaced dummy definition, it's not a constant, so far
         * */
        if(!isa<Instruction>(def)){
            return false;
        }
        
        if (IN_MAP(replace2userCall, cast<Instruction>(def))) {
            return false;
        }
        
        if (!isa<CallInst>(def)) return false;

        CallInst * call_instr = cast<CallInst>(def);
        // must be a cat_set or cat_new for constant propagation or folding
        Function * callee = call_instr->getCalledFunction();
        
        if (!IS_CONST_CAT_OP(callee)) return false;

        // bool is_const = get_const_CATnew_CATset(call_instr, res);
        Value * arg;
        
        if (IS_CAT_set(callee)){
            // cat_set(d, xx)
            arg = call_instr->getArgOperand(1);
        } else {
            // cat_new(xx)
            arg = call_instr->getArgOperand(0);
        }

        if (isa<ConstantInt>(arg)){
            
            *res = cast<ConstantInt>(arg)->getSExtValue();
            return true;
        }
        return false; 
    }

    /**
     *  (instruction to be replaced -> (old phi -> set of new phi))
     * */
    std::map<Instruction *, std::map<PHINode *, std::set<PHINode *>>> phi_toInsert;
    /**
     *  (instruction that needs artificial Phi -> set of Phi)
     * */
    std::map<Instruction *, std::set<PHINode *>> arti_phi_toInsert;
    void insert_phi_constant() {
        for (auto & instr_phiPair : phi_toInsert) {
            Instruction * inst = instr_phiPair.first;
            for (auto & old_new : phi_toInsert[inst]) {
                PHINode * oldPhi = old_new.first;

                for (PHINode * newPhi : old_new.second){
                
                    /**
                     *  Insert a copy of newPhi into the IR
                     * */
                    IRBuilder<> builder(oldPhi);

                    builder.Insert(newPhi);
                }
            }
        }
    }

    void delete_phi_constant(Instruction * inst) {
        for (auto & old_news : phi_toInsert[inst]) {
            for (PHINode * newPhi : old_news.second) {
                //errs() << "deleting constant phi" << *newPhi << " at " << newPhi << '\n';
                delete newPhi;
            }
        }
        phi_toInsert.erase(inst);
    }

    /**
     *  Should be at the top of the BB
     * */
    void insert_phi_artificial() {
        for (auto & inst_phi : arti_phi_toInsert) {
            Instruction * inst = inst_phi.first;
            BasicBlock * parent = inst->getParent();
            Instruction * head = &parent->front();
            for (PHINode * phi : inst_phi.second) {
                
                IRBuilder<> builder(head);
                builder.Insert(phi);
            }
        }
    }

    void delete_phi_artificial(Instruction * inst) {
        for (auto & art_phi : arti_phi_toInsert[inst]) {
            //errs() << "deleting artificial phi " << *art_phi << " at " << art_phi << '\n';
            delete art_phi;
        }
        arti_phi_toInsert.erase(inst);
    }

    bool VAL_check_constant_AA_wrap(
        AliasAnalysis & AA, 
        Instruction * instr, 
        Value * arg, 
        Value ** res
    ) {
        std::vector<Value *> aliases;
        aliases.push_back(arg);
        
        for (auto & var : cat_var) {
            if (var != arg){
                AliasResult AAResult = CAT_Alias(AA, var, arg);

                // errs() << "At instruction : " << *instr; 
                // errs() << *arg << " at " << arg << " alias with " << *var << " at " << var;
                // errs() << " with result = " << AliasResult_toString(AAResult) << '\n';
                if (AAResult == AliasResult::MustAlias) {
                    aliases.push_back(var);
                }
            }
            
        }

        /**
         * If one alias is sure to be constant we should be good to propogate
         * */
        Value * temp_val;
        for (uint32_t i = 0; i < aliases.size(); i++) {
            if(VAL_check_constant_s(instr, aliases[i], NULL, &temp_val)) {
                *res = temp_val;
                return true;
            }
        }
        
        if (isa<LoadInst>(arg)) {
            LoadInst * loadInst = cast<LoadInst>(arg);
            Value * ptr = loadInst->getPointerOperand();

            if (Value * val  = must_point2(instr, ptr)) {
                //errs() << "At instruction : " << *instr;
                //errs() << " the load result must be " << *val << '\n';
                if(VAL_check_constant_s(instr, val, NULL, &temp_val)) {
                    *res = temp_val;
                    return true;
                }
            }
        }
        return false;
    }

    bool VAL_check_constant_s_phi_helper(Instruction * instr, PHINode * phi, Value ** res) {
        uint32_t numIncoming = phi->getNumIncomingValues();
        std::vector<Value *> temp_val_arr(numIncoming);

        for (uint32_t i = 0; i < numIncoming; i++) {
            Value * inValue = phi->getIncomingValue(i);
            BasicBlock * inBB = phi->getIncomingBlock(i);
            if (!VAL_check_constant_s(instr, inValue, inBB, &temp_val_arr[i]) ){
                return false;
            }
        }
    
        if (temp_val_arr.size() == 0) return false;

        if (VAL_vec_all_equal(temp_val_arr)){
            *res = temp_val_arr[0];
            return true;

        } else if (numIncoming == temp_val_arr.size()) {
            /**
             *  All constant but not same value, why not substitute with a phi node
             * */
            
            PHINode * new_phi = create_const_phi(phi, temp_val_arr);

            phi_toInsert[instr][phi].insert(new_phi);
            *res = cast<Value>(new_phi); 
            return true;
        }

        return false;
    }

    bool VAL_check_constant_s(Instruction * instr, Value * arg, BasicBlock * incomingBB, Value ** res) {
        if (isa<IntegerType>(arg->getType())) {
            *res = arg;
            return true;
        }

        /**
         * Find the intersection between reaching definition of instr and definitions that define arg
        */
        std::set<Value *> arg_defs;
        // set_intersect(sIN[instr], sVar2Def[arg], arg_defs);
        set_union(sVar2Def[arg], sVar2mightDef[arg], arg_defs);
        set_intersect(sIN[instr], arg_defs, arg_defs);

        // errs() << "arg_defs of " << *arg  <<  " at " << *instr << " = \n";
        // print_set_with_addr(arg_defs);

        if (incomingBB) {
            set_intersect(sBB_OUT[incomingBB], arg_defs, arg_defs);
        }

        // errs() << "arg_defs of " << *arg  <<  " at " << *instr << " = \n";
        // print_set_with_addr(arg_defs);
        
        // errs() << "sVar2mightDef[arg] = \n";
        // print_set_with_addr(sVar2mightDef[arg]);
        
        /**
         * No available reaching definition
         * */
        if (arg_defs.size() == 0) return false; 
        /**
         * Expected vector of constants
         * */
        std::vector<Value *> const_vec (arg_defs.size());
        std::vector<BasicBlock *> def_bb;
        uint32_t idx = 0;

        BasicBlock * inst_parent = instr->getParent();
        
        std::set<BasicBlock *> preds_set;
        for (BasicBlock * pred : predecessors(inst_parent)) {
            preds_set.insert(pred);
        }

        for (auto & def : arg_defs) {
            bool is_const = false;
            if (isa<PHINode>(def)){
                PHINode * phi = cast<PHINode>(def);
                is_const = VAL_check_constant_s_phi_helper(instr, phi, &const_vec[idx]);
            } else {
                is_const = VAL_check_constant_val(instr, def, &const_vec[idx]);
            }   
            
            /**
             *   false immediately if one any of the definition is not a constant
             * */
            if (!is_const) return false;
            
#ifdef CHECK_CONST_AGGRESSIVE
            if (isa<Instruction>(def) && const_vec[idx] != instr) {
                BasicBlock * def_parent = cast<Instruction>(def)->getParent();
                if (IN_SET(preds_set, def_parent)) {
                    def_bb.push_back(def_parent);
                }
            }
#endif

            idx++;
        }   
        

        if (VAL_vec_all_equal(const_vec)){
            
            *res = const_vec[0];
            
            return true;
        } 
        
#ifdef CHECK_CONST_AGGRESSIVE
        std::set<BasicBlock *> def_bb_set(def_bb.begin(), def_bb.end());
        // errs() << "def_bb_set.size() = " << def_bb_set.size() << " def_bb.size() = " << def_bb.size() << '\n';
        if (
                def_bb.size() == const_vec.size()
            &&  def_bb.size() == def_bb_set.size()
        ) {
            /**
             *  Continue if every def comes from a different branches
             * */
            PHINode * artificial_phi = create_artificial_phi(const_vec, def_bb);
            arti_phi_toInsert[instr].insert(artificial_phi);
            *res = artificial_phi;
            return true;
        }
#endif

        return false;
    }
    /**
     *  check if given @val defines a constant
     *  if so result is stored in res, and return true
     *  otherwise return false, res is not touched
     * */ 
    bool VAL_check_constant_val(Instruction * instr, Value * def, Value ** res) {
        /**
         * If the imcoming node is a Argument definition, it's not a constant, so far
         * */
        if (isa<Argument>(def)) {
            return false;
        }


        /**
         * If the imcoming node is Phi Node definition, we recursively check if each of its incoming value is constant
         * */
        // if (isa<PHINode>(def)){
        //     PHINode * phi = cast<PHINode>(def);
        //     uint32_t numIncoming = phi->getNumIncomingValues();
        //     std::vector<Value *> temp_val_arr(numIncoming);

        //     for (uint32_t i = 0; i < numIncoming; i++) {
        //         Value * inValue = phi->getIncomingValue(i);
        //         if (!VAL_check_constant_val(instr, inValue, &temp_val_arr[i]) ){
        //             return false;
        //         }
        //     }
        
        //     if (temp_val_arr.size() == 0) return false;

        //     if (VAL_vec_all_equal(temp_val_arr)){
        //         *res = temp_val_arr[0];
        //         return true;

        //     } else if (numIncoming == temp_val_arr.size()) {
        //         /**
        //          *  All constant but not same value, why not substitute with a phi node
        //          * */
        //         *res = build_const_phi(instr, phi, temp_val_arr);
        //         return true;
        //     }

        //     return false;
        // }  

        /**
         * If the imcoming node is a replaced dummy definition, it's not a constant, so far
         * */
        if(!isa<Instruction>(def)){
            return false;
        }
        
        if (IN_MAP(replace2userCall, cast<Instruction>(def))) {
            return false;
        }
        
        if (!isa<CallInst>(def)) return false;

        CallInst * call_instr = cast<CallInst>(def);
        // must be a cat_set or cat_new for constant propagation or folding
        Function * callee = call_instr->getCalledFunction();
        
        if (!IS_CONST_CAT_OP(callee)) return false;

        // bool is_const = get_const_CATnew_CATset(call_instr, res);
        Value * arg;
        
        if (IS_CAT_set(callee)){
            // cat_set(d, xx)
            arg = call_instr->getArgOperand(1);
        } else {
            // cat_new(xx)
            arg = call_instr->getArgOperand(0);
        }
        
        // if (isa<ConstantInt>(arg)){
            
        //     // *res = cast<ConstantInt>(arg)->getSExtValue();
        //     *res = cast<ConstantInt>(arg);
        //     return true;
        // }
        if (isa<IntegerType>(arg->getType())){
            
            // *res = cast<ConstantInt>(arg)->getSExtValue();
            *res = arg;
            return true;
        }
        return false; 
    }

    /**
     *  Location to be inserted -> instruction to be inserted
     * */
    void build_from_map(std::map<Instruction *, Instruction *> & loc2newInst) {
        for (auto & loc_newInst : loc2newInst) {
            Instruction * location = loc_newInst.first;
            Instruction * newInst = loc_newInst.second;

            IRBuilder<> builder(location);
            builder.Insert(newInst);
        }
    }

    void replace_from_map(std::unordered_map<llvm::CallInst *, llvm::Value *> & replace_map) {
        for (auto & kv: replace_map) {
            // errs() << "Replacing " << *kv.first << " with " << *kv.second << '\n';
            BasicBlock::iterator ii(kv.first);
            BasicBlock * bb = kv.first->getParent();

            // kv.first->eraseFromParent();
            ReplaceInstWithValue(bb->getInstList(), ii, kv.second);

        }
        // errs() << "done!\n";
    }



    bool constant_folding(Function & F, AliasAnalysis & AA) {
        //errs() << "Folding on " << F.getName().str() << '\n';
        std::unordered_map<llvm::CallInst *, Value *> toFold;

        /**
         *  folding helper: callinst -> (val1, val2)
         * */
        std::unordered_map<llvm::CallInst *, std::pair<Value *, Value *>> toFold_helper;

        /**
         *  add instruction -> get instruction before it
         * */
        std::map<Instruction *, Instruction *> catGet_beforeAdd;
        
        /**
         *  Keep track of constant Ints that built by ourselves
         * */
        std::set<Value *> artificial_const;
        
        
        phi_toInsert.clear();
        arti_phi_toInsert.clear();
        
        for (BasicBlock &bb : F){
            for(Instruction &inst : bb){
                if (isa<CallInst>(&inst)) {
                    
                    CallInst * call_instr = cast<CallInst>(&inst);
                    Function * callee_ptr = call_instr->getCalledFunction();

                    /**
                     *  CAT_sub trick
                     * */
                    if (IS_CAT_sub(callee_ptr)) {
                        Value * arg1 = call_instr->getArgOperand(1);
                        Value * arg2 = call_instr->getArgOperand(2);
                        if (arg1 == arg2) {
                            Value * dummy_arg1 = build_constint(0);
                            Value * dummy_arg2 = build_constint(0);
                            artificial_const.insert(dummy_arg1);
                            artificial_const.insert(dummy_arg2);

                            toFold_helper[call_instr] = std::make_pair(
                                dummy_arg1,
                                dummy_arg2
                            ) ;
                            continue;
                        }
                    }

                    if (IS_CAT_add(callee_ptr) || IS_CAT_sub(callee_ptr)) {
                        
                        // errs() << "Constant Folding on " << *call_instr  << '\n';

                        Value * arg0 = call_instr->getArgOperand(0);
                        Value * arg1 = call_instr->getArgOperand(1);
                        Value * arg2 = call_instr->getArgOperand(2);

                        Value * arg1_LLVM_val, * arg2_LLVM_val;
                        bool arg1_const = VAL_check_constant_AA_wrap(AA, call_instr, arg1, &arg1_LLVM_val);
                        bool arg2_const = VAL_check_constant_AA_wrap(AA, call_instr, arg2, &arg2_LLVM_val);

                        
                        if (arg1_const && arg2_const) {
                            // toFold[call_instr] = build_cat_set(call_instr, substitution);
                            
                            
                            // Value * substitution = build_add_sub(call_instr, arg1_LLVM_val, arg2_LLVM_val);
                            // errs() << "Folding " << *call_instr << " with set " << *arg1_LLVM_val << " and " << *arg2_LLVM_val <<'\n';
                            toFold_helper[call_instr] = std::make_pair(arg1_LLVM_val, arg2_LLVM_val);
                            continue;
                        } else {
                            delete_phi_constant(call_instr);
                            delete_phi_artificial(call_instr);
                        }
                        
                    }
#ifdef CHECK_CONST_AGGRESSIVE
                    if (IS_CAT_add(callee_ptr)) {
                        Value * arg1 = call_instr->getArgOperand(1);
                        Value * arg2 = call_instr->getArgOperand(2);
                        if (arg1 == arg2) {
                            CallInst * cat_get = create_CAT_get(arg1);
                            
                            catGet_beforeAdd[call_instr] = cat_get;
                            toFold_helper[call_instr] = std::make_pair(
                                cat_get,
                                cat_get
                            );
                            continue;
                        }
                    }
#endif
                }
            }
        }

        build_from_map(catGet_beforeAdd);
        insert_phi_constant();
        insert_phi_artificial();

        

        for (auto &kv: toFold_helper) {
            CallInst * callinst = kv.first;
            Function * fptr = callinst->getCalledFunction();
            Value * arg1_val = kv.second.first;
            Value * arg2_val = kv.second.second;

            Value * substitution;
            if (isa<ConstantInt>(arg1_val) && isa<ConstantInt>(arg2_val)) {
                ConstantInt * arg1_val_int = cast<ConstantInt>(arg1_val);
                ConstantInt * arg2_val_int = cast<ConstantInt>(arg2_val);
                int64_t arg1_int = arg1_val_int->getSExtValue();
                int64_t arg2_int = arg2_val_int->getSExtValue();
                
                int64_t calc_res = 0;
                if(IS_CAT_add(fptr)) calc_res = arg1_int + arg2_int;
                if(IS_CAT_sub(fptr)) calc_res = arg1_int - arg2_int;

                substitution = build_constint(calc_res);
                
            } else {
                substitution = build_add_sub(kv.first, arg1_val, arg2_val);
            }

            //errs() << "Folding " << *kv.first << " by CATset " << *substitution << " at " << substitution << '\n';
            toFold[callinst] = build_cat_set(callinst, substitution);
        }

        replace_from_map(toFold);

        // for (auto & BB: F) {errs() << BB;}

        return toFold.size() != 0;
    }

    bool constant_propagation(Function & F, AliasAnalysis & AA) {
        //errs() << "Propogate on " << F.getName().str() << '\n';
        phi_toInsert.clear();
        arti_phi_toInsert.clear();

        unsigned inst_counter = 0;
        std::unordered_map<llvm::CallInst *, Value *> toPropogate;

        for (BasicBlock &bb : F){
            for(Instruction &inst : bb){
                if (isa<CallInst>(&inst)) {
                    CallInst * call_instr = cast<CallInst>(&inst);
                    Function * callee_ptr = call_instr->getCalledFunction();
                    if(IS_CAT_get(callee_ptr)) {
                        Value * arg = call_instr->getArgOperand(0);
                        int64_t arg_val; 
                        Value * arg_LLVM_val;
                        // bool arg_const = check_constant_s(call_instr, arg, &arg_val);

                        // bool arg_const = check_constant_AA_wrap(AA, call_instr, arg, &arg_val);
                        bool arg_const = VAL_check_constant_AA_wrap(AA, call_instr, arg, &arg_LLVM_val);
                        if (arg_const) {
                            // errs() << *call_instr << " replaced with " << arg_val <<'\n';
                            // toPropogate[call_instr] = build_constint(arg_val);
                            toPropogate[call_instr] = arg_LLVM_val;

                            //errs() << "Propogate " << *call_instr << " with " << *arg_LLVM_val << '\n';
                        } else {
                            // phi_toInsert.erase(call_instr);
                            delete_phi_constant(call_instr);
                            delete_phi_artificial(call_instr);
                        }
                    }
                }
            }
        }

        insert_phi_constant();
        insert_phi_artificial();

        replace_from_map(toPropogate);

        // for (auto & BB: F) {errs() << BB;}
        // errs() << "Done: constant prop !\n";
        return toPropogate.size() != 0;
    }

    void print_bitvector(BitVector &bv){
        if(bv.any()){
            for (int j = 0; j < instr_vec.size(); j++ ) {
                if (bv.test(j)) {
                    errs() << " " << *instr_vec[j] << '\n';
                }
            }
        }
    }

    void live_analysis_init() {
        // std::map<Value *, std::set<Value *>> live_GEN, live_KILL;
        // std::map<Value *, std::set<Value *>> live_IN, live_OUT;
        
        live_GEN.clear();
        live_KILL.clear();
        live_IN.clear();
        live_OUT.clear();
    }


    void might_alias(Instruction * inst, Value * target, std::vector<Value *> & aliases) {
        if (isa<PHINode>(target) || isa<SelectInst>(target)) {
            select_phi_trace_back(target, aliases);
            return;
        }

        if (isa<LoadInst>(target)) {
            LoadInst * load_inst = cast<LoadInst>(target);
            Value * ptr = load_inst->getPointerOperand();
            
            may_point2(inst, ptr, aliases);
            aliases.push_back(load_inst);

            return;
        }

        /**
         *  Other cases: CAT_new, Argument 
         * */
        aliases.push_back(target);
    }

    void live_GEN_populate(Instruction * inst, Value * used_var) {
        std::vector<Value *> aliases;
        might_alias(inst, used_var, aliases);
        live_GEN[inst].insert(aliases.begin(), aliases.end());

        // errs() << "At " << *inst  << *used_var << " might alias "  << '\n';
        // for (Value * might_a: aliases) {
        //     errs() << *might_a << '\n';
        // }

        Value * auto_res;
        bool is_auto = CAT_auto_trace_back(used_var, &auto_res);
        if (is_auto) {
            /**
             *  If auto, apply the same thing on the traced back variable.
             * */
            live_GEN_populate(inst, auto_res);
        }

    }

    void live_KILL_populate(Instruction * inst, Value * def_var) {
        live_KILL[inst].insert(def_var);
        
        if (isa<LoadInst>(def_var)) {
            LoadInst * load_inst = cast<LoadInst>(def_var);
            Value * ptr = load_inst->getPointerOperand();

            Value * must_val = must_point2(inst, ptr);
            if (must_val) {
                live_KILL[inst].insert(must_val);
            }
        }

        std::vector<Value *> aliases;
        might_alias(inst, def_var, aliases);
        live_might_KILL[inst].insert(aliases.begin(), aliases.end());

        Value * auto_res;
        bool is_auto = CAT_auto_trace_back(def_var, &auto_res);
        if (is_auto) {
            /**
             *  If auto, apply the same thing on the traced back variable.
             * */
            live_KILL_populate(inst, auto_res);
        }
    }

    void live_analysis_GENKILL(Function & F, AliasAnalysis & AA ){
        unsigned NumInstrs = F.getInstructionCount();

        for (BasicBlock &bb : F){
            for(Instruction &inst : bb){
                Function * fptr = get_callee_ptr(&inst);
                if(fptr){
                    CallInst * call_instr = cast<CallInst>(&inst);
                    if (IS_CAT_OP(fptr)){
                        liveBB2CAT[&bb].push_back(call_instr);

                        // errs() << "analyzing " << *call_instr << '\n';
                        if (IS_CAT_new(fptr)){
                            // only define but not killed
                            live_KILL[&inst].insert(&inst);
                            
                            // ref_KILL[&inst].insert(&inst);
                            
                        } else if (IS_CAT_get(fptr)) {
                            /**
                             *  Only use variable, both value and reference
                             * */
                            Value * arg0 = call_instr->getArgOperand(0);
                            
                            live_GEN_populate(call_instr, arg0);

                            // ref_GEN[&inst].insert(arg0);
                            
                        } else if (IS_CAT_set(fptr)) {
                            // CAT_set, define and usearg0
                            
                            // Instruction * arg0 = cast<Instruction>(call_instr->getArgOperand(0));
                            Value * arg0 = call_instr->getArgOperand(0);

                            live_KILL_populate(call_instr, arg0);

                            // ref_GEN[&inst].insert(arg0);
                        } else {
                            // CAT_add, CAT_sub
                            // define arg0
                            // use arg1, arg2

                            Value * arg0 = call_instr->getArgOperand(0);
                            Value * arg1 = call_instr->getArgOperand(1);
                            Value * arg2 = call_instr->getArgOperand(2);

                            live_KILL_populate(call_instr, arg0);

                            live_GEN_populate(call_instr, arg1);

                            live_GEN_populate(call_instr, arg2);

                            // ref_GEN[&inst].insert(arg0);
                            // ref_GEN[&inst].insert(arg1);
                            // ref_GEN[&inst].insert(arg2);
                        }   

                    } else if (IS_USER_FUNC(fptr)){
                        liveBB2CAT[&bb].push_back(call_instr);
                        uint32_t arg_cnt = call_instr->getNumArgOperands();
                        for(uint32_t i = 0; i < arg_cnt; i++){
                            Value * arg = call_instr->getArgOperand(i);
                            
                            
                            /**
                             * TODO: augmented with alias analysis and MPT analysis
                             * */

                            if (IS_PTR_TYPE(arg)) {
                                
                                // std::vector<Value *> possible_vals;
                                // may_point2(&inst, arg, possible_vals);
                                // if (possible_vals.empty()) possible_vals.push_back(arg);
                                
                                // for (Value * val : possible_vals){
                                //     MemoryLocation memLoc(val);
                                //     ModRefInfo info = AA.getModRefInfo(call_instr, memLoc); 


                                // // errs() << *call_instr << " has arg " << *arg << " at " << arg;
                                // // errs() << "arg points to " << *possible_vals[j] <<  " with ModRefInfo = " << ModRefInfo_toString(info) <<'\n';
                                //     if (HAS_MOD(info)){
                                        
                                //     }

                                //     if (HAS_REF(info)){
                                        
                                //     }                                   
                                
                                //     live_KILL[&inst].insert(arg);
                                //     live_GEN[&inst].insert(arg);
                                //     ref_GEN[&inst].insert(arg);
                                // }
                                live_KILL[&inst].insert(arg);
                                live_GEN[&inst].insert(arg);
                                // ref_GEN[&inst].insert(arg);
                            }
                        
                        }
                    } else {
                        /**
                         *  Non user function, should not matter at current stage
                         * */
                        
                    }

                } else if (isa<PHINode>(&inst)){

                    PHINode * phi = cast<PHINode>(&inst);
                    
                    if (IS_PTR_TYPE(phi)) {
                        live_KILL[phi].insert(phi);
                        // ref_KILL[phi].insert(phi);

                        uint32_t numIncome =  phi->getNumIncomingValues();

                        for (uint32_t i = 0; i < numIncome; i++) {
                            Value * in_value = phi->getIncomingValue(i);
                            live_GEN[phi].insert(in_value);
                            // ref_GEN[phi].insert(in_value);
                        }
                        
                        liveBB2CAT[&bb].push_back(phi);
                    }

                } else if (isa<SelectInst>(&inst)){
                    SelectInst * select_inst = cast<SelectInst>(&inst);
                    if (IS_PTR_TYPE(select_inst)) {
                        live_KILL[select_inst].insert(select_inst);
                        // ref_KILL[select_inst].insert(select_inst);

                        Value * op1 = select_inst->getOperand(1);
                        Value * op2 = select_inst->getOperand(2);
                        
                        live_GEN[select_inst].insert(op1);
                        // ref_GEN[select_inst].insert(op1);

                        live_GEN[select_inst].insert(op2);
                        // ref_GEN[select_inst].insert(op2);

                        liveBB2CAT[&bb].push_back(select_inst);
                    }   

                } 
                
                // else if (isa<StoreInst>(&inst)) {
                    
                //     StoreInst * store_inst = cast<StoreInst>(&inst);
                //     Value * ptr = store_inst->getPointerOperand();
                //     Value * val = store_inst->getValueOperand();
                    
                //     live_KILL[store_inst].insert(ptr);
                //     ref_GEN[store_inst].insert(val);
                //     live_GEN[store_inst].insert(val);

                // } else if (isa<LoadInst>(&inst)) {
                //     LoadInst * load_inst = cast<LoadInst>(&inst);
                //     Value * ptr = load_inst->getPointerOperand();
                    
                //     live_GEN[load_inst].insert(ptr);
                //     ref_KILL[load_inst].insert(load_inst);
                //     live_KILL[load_inst].insert(load_inst);
                
                // } else if (isa<AllocaInst>(&inst)) {
                //     AllocaInst * alloc_inst = cast<AllocaInst>(&inst);
                    
                //     ref_KILL[alloc_inst].insert(alloc_inst);

                // } else if (isa<ReturnInst>(&inst)) {

                    
                //     ReturnInst * return_inst = cast<ReturnInst>(&inst);
                //     Value * ret_val = return_inst->getReturnValue();

                //     if (ret_val && IS_PTR_TYPE(ret_val)){
                //         ref_GEN[return_inst].insert(ret_val);
                //         live_GEN[return_inst].insert(ret_val);
                //     }

                // } else if (isa<PtrToIntInst>(&inst)) {
                //     PtrToIntInst * ptr2int = cast<PtrToIntInst>(&inst);
                //     Value * ptr2int_op0 = ptr2int->getOperand(0);

                //     ref_GEN[ptr2int].insert(ptr2int_op0);
                //     ref_KILL[ptr2int].insert(ptr2int);
                //     live_KILL[ptr2int].insert(ptr2int);

                // } else if (isa<ShlOperator>(&inst)) {
                //     ShlOperator * shl = cast<ShlOperator>(&inst);
                //     Value * shl_op0 = shl->getOperand(0);

                //     ref_GEN[shl].insert(shl_op0);
                //     ref_KILL[shl].insert(shl);
                //     live_KILL[shl].insert(shl);

                // } else if (isa<AShrOperator>(&inst)) {
                //     AShrOperator * ashr = cast<AShrOperator>(&inst);
                //     Value * ashr_op0 = ashr->getOperand(0);

                //     ref_GEN[ashr].insert(ashr_op0);
                //     ref_KILL[ashr].insert(ashr);
                //     live_KILL[ashr].insert(ashr);

                // } else if (isa<IntToPtrInst>(&inst)) {
                //     IntToPtrInst * int2ptr = cast<IntToPtrInst>(&inst);
                //     Value * int2ptr_op0 = int2ptr->getOperand(0);

                //     ref_GEN[int2ptr].insert(int2ptr_op0);
                //     ref_KILL[int2ptr].insert(int2ptr);
                //     live_KILL[int2ptr].insert(int2ptr);

                // } else if(isa<CmpInst>(&inst)) {
                //     CmpInst * cmp_inst = cast<CmpInst>(&inst);
                //     Value * LHS = cmp_inst->getOperand(0);
                //     Value * RHS = cmp_inst->getOperand(1);

                //     if (IS_PTR_TYPE(RHS) && !isa<ConstantPointerNull>(RHS) ){
                //         errs() << "comp inst" << inst << "operand = " << *LHS;

                //     } 

                //     if (IS_PTR_TYPE(RHS) && !isa<ConstantPointerNull>(RHS) ){
                //         errs() << "comp inst" << inst << "operand = " << *RHS;
                        
                //     } 
                // }
            }
        }

        // errs() << "live_analysis_GENKILL_INST done \n";
        // errs() << "printing reference variables\n";
        // print_set_reference(referenced_var);
    }

    bool calc_live_OUT2IN(
        Instruction * inst,
        std::map<Value *, std::set<Value *>> & GEN,
        std::map<Value *, std::set<Value *>> & KILL,
        std::map<Value *, std::set<Value *>> & IN,
        std::map<Value *, std::set<Value *>> & OUT
    ) {
        std::set<Value *> tempIN;
         /**
             *  p = &x;
             *  IN[i] = GEN[i] U (OUT[i] – KILL[i])
             * */
        std::set<Value *> outMinusKill;
        set_diff(
            OUT[inst],   /* srcA */
            KILL[inst],  /* srcB */
            outMinusKill      /* target */
        );

        set_union(
            outMinusKill,   /* srcA */
            GEN[inst], /* srcB */
            tempIN          /* target */
        );

        bool diff = tempIN != IN[inst];
        IN[inst] = tempIN;
        return diff;
    }

    void backward_INOUT(
        Function & F,
        std::map<Value *, std::set<Value *>> & GEN,
        std::map<Value *, std::set<Value *>> & KILL,
        std::map<Value *, std::set<Value *>> & IN,
        std::map<Value *, std::set<Value *>> & OUT
    ) {
        std::set<BasicBlock *> bb_calced;

        bool changed;
        do {
            changed = false;
            for (BasicBlock & bb : F) {
                // Instruction * last_inst = bb.getTerminator(); 
                if (liveBB2CAT[&bb].empty()) continue;
                Instruction * last_inst = liveBB2CAT[&bb].back();
                /**
                 *  Calculate OUT of last instruction from IN of successors
                 * */
                for (BasicBlock * succBB : successors(&bb)) {
                    Instruction * predBB_terminator = liveBB2CAT[&bb].front();

                    OUT[last_inst].insert(
                        IN[predBB_terminator].begin(),
                        IN[predBB_terminator].end()
                    );
                }

                bool last_in_changed = calc_live_OUT2IN(last_inst, GEN, KILL, IN, OUT);
                
                if (!changed) changed = last_in_changed;

                if (last_in_changed  || !IN_SET(bb_calced, &bb)) {
                    bool in_changed;
                    std::set<Value *> nextIN = IN[last_inst];

                    for (auto iter = (++liveBB2CAT[&bb].rbegin()); iter != liveBB2CAT[&bb].rend(); iter++) {
                        Instruction * cur_ptr = *iter;
                        OUT[cur_ptr] = nextIN;

                        in_changed = calc_live_OUT2IN(cur_ptr, GEN, KILL, IN, OUT);

                        nextIN = IN[cur_ptr];
                    }

                    if (!changed) changed = in_changed;
                    bb_calced.insert(&bb);
                } 

            }

        } while(changed);
    }

    void backward_INOUT_backup(
        Function & F,
        std::map<Value *, std::set<Value *>> & GEN,
        std::map<Value *, std::set<Value *>> & KILL,
        std::map<Value *, std::set<Value *>> & IN,
        std::map<Value *, std::set<Value *>> & OUT
    ) {
        std::set<BasicBlock *> bb_calced;

        bool changed;
        do {
            changed = false;
            for (BasicBlock & bb : F) {
                Instruction * last_inst = bb.getTerminator(); 
                
                /**
                 *  Calculate OUT of last instruction from IN of successors
                 * */
                for (BasicBlock * succBB : successors(&bb)) {
                    Instruction * predBB_terminator = &succBB->front();

                    OUT[last_inst].insert(
                        IN[predBB_terminator].begin(),
                        IN[predBB_terminator].end()
                    );
                }

                bool last_in_changed = calc_live_OUT2IN(last_inst, GEN, KILL, IN, OUT);
                
                if (!changed) changed = last_in_changed;

                if (last_in_changed  || !IN_SET(bb_calced, &bb)) {
                    bool in_changed;
                    std::set<Value *> nextIN = IN[last_inst];

                    for (auto iter = (++bb.rbegin()); iter != bb.rend(); iter++) {
                        Instruction * cur_ptr = &*iter;
                        OUT[cur_ptr] = nextIN;

                        in_changed = calc_live_OUT2IN(cur_ptr, GEN, KILL, IN, OUT);

                        nextIN = IN[cur_ptr];
                    }

                    if (!changed) changed = in_changed;
                    bb_calced.insert(&bb);
                } 

            }

        } while(changed);
    }

    /**
     *  Return if def which is defined by inst has contruction outside the function
     **/
    bool var_escaped(CallInst * inst, Value * def) {
        
        
        if (isa<Argument>(def)) {
            return true;
        }

        if (isa<GlobalVariable>(def)) {
            return true;
        }
        
        Function * parent_func = inst->getParent()->getParent();

        if (isa<LoadInst>(def)) {
            LoadInst * load_inst = cast<LoadInst>(def);
            Value * ptr = load_inst->getPointerOperand();
            
            return var_escaped(inst, ptr);
        }
        return false;
    }

    bool can_be_eliminated(CallInst * inst) {
        
        Function * fptr = inst->getCalledFunction();
        if (fptr == nullptr) return false;
        if (!IS_CAT_OP(fptr)) return false;

        if (IS_CAT_new(fptr)) {
            return inst->user_empty();
            // return !IN_SET(ref_OUT[inst], inst);           
        }

        bool escaped = var_escaped(inst, inst->getArgOperand(0));
        if (escaped) return false;


        /**
         *  An instruction can be eliminated if what it defines will not be used by later instructions
         *  live_OUT[inst] & live_KILL[inst] = empty
         * */

        std::set<Value *> laterUsed;
        set_intersect(
            live_OUT[inst],     /* srcA */
            // live_KILL[inst],    /* srcB */
            live_might_KILL[inst],    /* srcB */
            laterUsed           /* target */
        );

        return laterUsed.empty();
    }

    void elimiating_erase(std::vector<Instruction *> & to_eliminate) {
        for (Instruction * inst : to_eliminate) {
            inst->eraseFromParent();
        }
    }

    bool eliminating(Function &F, AliasAnalysis & AA) {
        
        std::vector<Instruction *> to_eliminate;

        for (BasicBlock &bb : F){
        for(Instruction &inst : bb){
            if (isa<CallInst>(&inst)) {
                CallInst * call_inst = cast<CallInst>(&inst);
                Function * fptr = call_inst->getCalledFunction();
                if (IS_CAT_OP(fptr)) {
                    if (!IS_CAT_get(fptr)) {

                        bool canElim = can_be_eliminated(call_inst);
                        if (canElim){
                            to_eliminate.push_back(call_inst);
                            errs() << "Eliminating " << *call_inst << '\n';
                        }
                    }
                }
            }
            
        }
        }

        elimiating_erase(to_eliminate);

        return !to_eliminate.empty();
    }

    void print_live_GENKILL(Function &F){
        errs() << "Function \"" << F.getName() << "\" " << '\n';
        for (BasicBlock &bb : F){
            for(Instruction &inst : bb){
                errs() << "INSTRUCTION: " << inst << '\n';
                errs() << "***************** live GEN\n{\n";
                // print_set(sIN[&inst]);
                print_set_with_addr(live_GEN[&inst]);
                errs() << "}\n";
                errs() << "**************************************\n";
                errs() << "***************** live KILL\n{\n";


                // print_set(sOUT[&inst]);
                print_set_with_addr(live_KILL[&inst]);
                errs() << "}\n";
                errs() << "**************************************\n";
                errs() << "\n\n\n";
            }
        }

    }

    void print_live_INOUT(
        Function &F    
    ){
        errs() << "Function \"" << F.getName() << "\" " << '\n';
        for (BasicBlock &bb : F){
            for(Instruction &inst : bb){
                errs() << "INSTRUCTION: " << inst << '\n';
                errs() << "***************** live IN\n{\n";
                // print_set(sIN[&inst]);
                print_set_with_addr(live_IN[&inst]);
                errs() << "}\n";
                errs() << "**************************************\n";
                errs() << "***************** live OUT\n{\n";


                // print_set(sOUT[&inst]);
                print_set_with_addr(live_OUT[&inst]);
                errs() << "}\n";
                errs() << "**************************************\n";
                errs() << "\n\n\n";
            }
        }

    }

    // void print_ref_INOUT(Function &F){
    //     errs() << "Function \"" << F.getName() << "\" " << '\n';
    //     for (BasicBlock &bb : F){
    //         for(Instruction &inst : bb){
    //             errs() << "INSTRUCTION: " << inst << '\n';
    //             errs() << "***************** ref IN\n{\n";
    //             print_set_with_addr(ref_IN[&inst]);
                
    //             errs() << "}\n";
    //             errs() << "**************************************\n";
    //             errs() << "***************** ref OUT\n{\n";


    //             print_set_with_addr(ref_OUT[&inst]);
    //             errs() << "}\n";
    //             errs() << "**************************************\n";
    //             errs() << "\n\n\n";
    //         }
    //     }

    // }

    void live_analysis_wrapper(Function &F, AliasAnalysis & AA){
        // errs() << "liveness Analysis on " << F.getName() << '\n';
        live_analysis_init();
        
            timer.start();
        live_analysis_GENKILL(F, AA);
            timer.stop();
            timer.printDuration("\t\tLIVE GEN-KILL ");
        
            timer.start();  
        backward_INOUT_backup(
            F,
            live_GEN,
            live_KILL,
            live_IN,
            live_OUT
        );
            timer.stop();
            timer.printDuration("\t\tLIVE IN-OUT ");
        // backward_INOUT(
        //     F,
        //     ref_GEN,
        //     ref_KILL,
        //     ref_IN,
        //     ref_OUT
        // );
        // print_live_GENKILL(F);
        // print_live_INOUT(F);
        
        // print_ref_INOUT(F);

        // errs() << "Done: liveness Analysis on " << F.getName() << '\n';
    }
    
    // eliminating(F, AA);
};  
}

// Next there is code to register your pass to "opt"
char CAT::ID = 0;
static RegisterPass<CAT> X("CAT", "Homework for the CAT class");

// Next there is code to register your pass to "clang"
static CAT * _PassMaker = NULL;
static RegisterStandardPasses _RegPass1(PassManagerBuilder::EP_OptimizerLast,
    [](const PassManagerBuilder&, legacy::PassManagerBase& PM) {
        if(!_PassMaker){ PM.add(_PassMaker = new CAT());}}); // ** for -Ox
static RegisterStandardPasses _RegPass2(PassManagerBuilder::EP_EnabledOnOptLevel0,
    [](const PassManagerBuilder&, legacy::PassManagerBase& PM) {
        if(!_PassMaker){ PM.add(_PassMaker = new CAT()); }}); // ** for -O0