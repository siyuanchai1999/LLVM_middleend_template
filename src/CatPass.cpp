// #include "llvm/Pass.h"
// #include "llvm/IR/Function.h"
// #include "llvm/Support/raw_ostream.h"
// #include "llvm/IR/LegacyPassManager.h"
// #include "llvm/Transforms/IPO/PassManagerBuilder.h"

#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/Support/Casting.h"
#include "llvm/ADT/BitVector.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/IRBuilder.h"
#include <set>
#include <unordered_set>
#include <vector>
#include <map>
#include <unordered_map>
#include <queue>
using namespace llvm;
 
namespace {
    template<class T> class Set:public std::set<T>{
    public:

};

// Disjoint-Set Data Structure (Union Find Algorithm)


struct CAT : public FunctionPass {
    static char ID; 
    Module *currentModule;
    // map(caller_name, (callee_name, count))
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

#define IN_MAP(map, key) (map.find(key) != map.end())
#define IN_SET(set, key) (set.find(key) != set.end())

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

    std::unordered_map<llvm::Value *, std::unordered_set<llvm::Value *>> store_table;
#define IN_STORE_TABLE(ptr) ( store_table.find(ptr) != store_table.end() )

    std::set<Value *> cat_arg;
#define IN_CAT_ARG(ptr) (cat_arg.find(ptr)!=cat_arg.end())

    std::unordered_map<Function *, std::set<Value*>> cat_var;


    //Generic IN / OUT set
    std::vector<Value*> sGEN;
    std::unordered_map<Value*, std::set<Value*>> sKILL;
    std::unordered_map<Value*, std::set<Value*>> sTemp;
    std::unordered_map<Value*, std::set<Value*>> sBB_GEN;
    std::unordered_map<Value*, std::set<Value*>> sBB_KILL;
    std::unordered_map<Value *, std::set<Value*>> sBB_IN, sBB_OUT;
    std::unordered_map<Value *, std::set<Value*>> sIN, sOUT;

    void set_intersect(std::set<Value*> const &a,std::set<Value*> const &b, std::set<Value*> &ret){
        std::set_intersection(a.begin(),a.end(),b.begin(),b.end(),std::inserter(ret,ret.begin()));
    }
    void set_diff(std::set<Value*> const &a,std::set<Value*> const &b, std::set<Value*> &ret){
        std::set_difference(a.begin(),a.end(),b.begin(),b.end(),std::inserter(ret,ret.begin()));
    }
    void set_union(std::set<Value*> const &a,std::set<Value*> const &b, std::set<Value*> &ret){
        ret.insert(a.begin(),a.end());
        ret.insert(b.begin(),b.end());
    }
    void set_xor(std::set<Value*> const &a,std::set<Value*> const &b, std::set<Value*> &ret){
       std::set_symmetric_difference(a.begin(),a.end(),b.begin(),b.end(),std::inserter(ret,ret.begin()));
    }


    // deadcode elimination
    std::unordered_map<llvm::Instruction *, llvm::BitVector> live_GEN_INST, live_KILL_INST;
    std::unordered_map<llvm::Instruction *, llvm::BitVector> live_IN_INST, live_OUT_INST;
    std::unordered_map<llvm::BasicBlock *, llvm::BitVector> live_GEN_BB, live_KILL_BB;
    std::unordered_map<llvm::BasicBlock *, llvm::BitVector> live_IN_BB, live_OUT_BB;

        // class to represent a disjoint set

        class DisjointSet
        {

        public:
            std::unordered_map<Value *, Value *> parent;
            void makeSet(Function &F){
                for(auto &BB : F){
                    for(auto &instr: BB){
                        if(isa<PHINode>(instr))
                            this->parent[&instr]=&instr;
                        if(isa<CallInst>(instr)){
                            CallInst *call_inst = cast<CallInst>(&instr);
                            Function *callee_ptr = call_inst->getCalledFunction();
                            if(callee_ptr->getName().str()=="CAT_new")
                                this->parent[&instr]=&instr;
                        }

                    }

                }
                //printSet();
                //errs()<<"After Making set."<<"\n";
            }

            void makeSet2(Function &F){
                for(auto &BB : F){
                    for(auto &instr: BB){
                        if(isa<CallInst>(instr)){
                            CallInst *call_inst = cast<CallInst>(&instr);
                            Function *callee_ptr = call_inst->getCalledFunction();
                            if(callee_ptr->getName().str()=="CAT_new")
                                this->parent[&instr]=&instr;
                        }

                    }

                }
                printSet();
            }
            void printSet(){
                auto it = this->parent.begin();
                while(it != this->parent.end()){
                    errs()<<*(it->first)<<"<==>"<<*(it->second)<<"\n";
                    it++;
                }
            }


            // Find the root of the set in which element k belongs
            Value* Find(Value *k)
            {
                // if k is root
                if (this->parent[k] == k)
                    return k;

                // recur for parent until we find root
                return Find(this->parent[k]);
            }

            // Perform Union of two subsets
            void Union(Value* a, Value* b)
            {
                // find root of the sets in which elements
                // x and y belongs
                Value* x = Find(a);
                Value* y = Find(b);

                parent[x] = y;
            }

            int getConnectedSize(Value *instr){
                int count = 0;
                auto it = parent.begin();
                while(it!=parent.end()){
                    if(this->Find(it->first)==this->Find(instr))
                        count++;
                    it++;
                }
                return count;
            }
            int getConnectedComponent(Value* v, Set<Value *> &s){
                int count = 0;
                for(auto &p:parent){
                    if(this->Find(p.first)==this->Find(v)){
                        s.insert(p.first);
                        count++;
                    }
                }
                return count;
            }
        };

        CAT() : FunctionPass(ID) {}

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
        return false;
        
    }


    // This function is invoked once per function compiled
    // The LLVM IR of the input functions is ready and it can be analyzed and/or transformed
    bool runOnFunction (Function &F) override {
      // errs() << "Hello LLVM World at \"runOnFunction\"\n" ;
        //findCatVariables(F);
        //phi_node_new2set(F);
        std::string caller_name = F.getName().str();
        H0_init();
        H0_function_count(F);
        // H0_output(caller_name);
        sGEN_sKILL(F);
        //print_gen_kill(caller_name,F);
        sIN_sOUT(F);
        sIN_OUT_inst(F);
        print_in_out(caller_name, F);

//        H1_init(F);
//        H1_GEN_KILL(F);
//        // H1_output(caller_name);
//
//        H2_init(F);
//        H2_IN_OUT(F);
//        instruction_IN_OUT(F);
//        //H2_output(caller_name,F);
//
//        build_store_table(F);
//        find_escaped(F);
//
//        constant_folding(F);
//        constant_propagation(F);

        return false;
    }

    // We don't modify the program, so we preserve all analyses.
    // The LLVM IR of functions isn't ready at this point
    void getAnalysisUsage(AnalysisUsage &AU) const override {
        // errs() << "Hello LLVM World at \"getAnalysisUsage\"\n" ;
        AU.setPreservesAll();
    }

    void findCatVariables(Function &F){
            for(auto &inst: instructions(F)){
                if(isa<CallInst>(inst)){
                    CallInst* callInst = cast<CallInst>(&inst);
                    Function* callee_ptr = callInst->getCalledFunction();
                    if(fptr2name.find(callee_ptr) != fptr2name.end()){
                        std::string callee_name = fptr2name[callee_ptr];
                        //CAT_set, first operand is a CAT var
                        if(callee_name=="CAT_set"){
                            // tail call void @CAT_set(i8* %8, i64 42) #3
                            Value *arg = callInst->getArgOperand(0);
                            cat_var[&F].insert(arg);
                        }
                        //CAT_add, CAT_sub all of their operands are CAT var
                        if(callee_name=="CAT_add"||callee_name=="CAT_sub"){
                            //tail call void @CAT_add(i8* %8, i8* %8, i8* %8) #3
//                            Value* arg1 = callInst->getArgOperand(0);
//                            Value* arg2 = callInst->getArgOperand(1);
//                            Value* arg3 = callInst->getArgOperand(2);
                            cat_var[&F].insert(callInst->arg_begin(),callInst->arg_end());
                        }
                        //CAT_new, the instruction itself is CAT var
                        if(callee_name=="CAT_new"){
                            cat_var[&F].insert(&inst);
                        }
                    }
                }
            }
        }

        //naive GEN KILL IN OUT

    void sGEN_sKILL(Function &F){
            for (auto& inst: llvm::instructions(F)) {
                if (isa<CallInst>(&inst)){
                    CallInst * call_instr = cast<CallInst>(&inst);
                    Function * callee_ptr = call_instr->getCalledFunction();

                    if (fptr2name.find(callee_ptr) != fptr2name.end()) {
                        // find one call_instr that calls one of CAT functions
                        std::string callee_name = fptr2name[callee_ptr];
                        if (callee_name != "CAT_get") {
                            sGEN.push_back(call_instr);

                            Value * key;
                            if (callee_name == "CAT_new") {
                                key = call_instr;
                            } else {
                                // get first operand if CAT_set, CAT_add, CAT_sub
                                Value * arg0 = call_instr->getArgOperand(0);
                                key = arg0;
                            }
                            if(sTemp.find(key)==sTemp.end()){
                                sTemp[key] = std::set<Value*>();
                            }
                            sTemp[key].insert(call_instr);

                        }
                    }
                }
            }
            for(Value *gen:sGEN){
                CallInst *call_instr = cast<CallInst>(gen);
                Value* arg0 = call_instr->getArgOperand(0);
                if(sTemp.find(arg0)!=sTemp.end()){
                    sKILL[gen] = sTemp[arg0];
                }else{
                    sKILL[gen] = sTemp[gen];
                }
                sKILL[gen].erase(gen);
            }
    }
    void sIN_sOUT(Function &F){
            for(auto &bb :F){
                sBB_IN[&bb] = std::set<Value*>();
                sBB_OUT[&bb] = std::set<Value*>();
                sBB_GEN[&bb] = std::set<Value*>();
                sBB_KILL[&bb] = std::set<Value*>();
                for(llvm::Instruction &inst :bb){

                    if(std::find(sGEN.begin(),sGEN.end(),&inst)!=sGEN.end()){
                        sBB_GEN[&bb].insert(&inst);
                    }
                    //TODO:Optimize
                    std::set<Value*> temp;
                    set_union(sBB_KILL[&bb],sKILL[&inst],temp);
                    sBB_KILL[&bb]=temp;

                    std::set<Value*> temp2;
                    set_diff(sBB_GEN[&bb],sKILL[&inst],temp2);
                    sBB_GEN[&bb]=temp2;
                    if(std::find(sGEN.begin(),sGEN.end(),&inst)!=sGEN.end()){
                        sBB_KILL[&bb].erase(&inst);
                    }
                }
            }
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
                    //  OUT = GEN[i]^TEMP
                    set_union(sBB_GEN[&bb],temp,out);

                    if(!changed){
                        changed = (out!=sBB_OUT[&bb]);
                    }
                    sBB_OUT[&bb] = out;
                }
            }while(changed);
    }
    void sIN_OUT_inst(Function &F){
        for (BasicBlock &bb : F){
            std::set<Value*> local_INSTR_IN = sBB_IN[&bb];
            std::set<Value*> local_INSTR_OUT = sBB_IN[&bb];
            for(Instruction &inst : bb){
                local_INSTR_IN = local_INSTR_OUT;


                //TODO: need to be replaced by bitwise_diff function later
                std::set<Value*> OUT_TEMP = local_INSTR_IN;
                std::set<Value*> INTERSECTION;
                std::set<Value*> temp;
                set_intersect(sKILL[&inst],local_INSTR_IN,INTERSECTION);
                std::set<Value*> out;
                set_xor(OUT_TEMP,INTERSECTION,temp);
                OUT_TEMP = temp;

                if(std::find(sGEN.begin(),sGEN.end(),&inst)!=sGEN.end()){

                    OUT_TEMP.insert(&inst);
                }
                local_INSTR_OUT = OUT_TEMP;


                sIN[&inst] = local_INSTR_IN;
                sOUT[&inst] = local_INSTR_OUT;
            }
        }
        }
    void print_in_out(std::string &func_name, Function &F){
        errs() << "Function \"" << func_name << "\" " << '\n';
        unsigned inst_counter = 0;
        for (BasicBlock &bb : F){
            for(Instruction &inst : bb){
                errs() << "INSTRUCTION: " << inst << '\n';
                errs() << "***************** IN\n{\n";
                print_set(sIN[&inst]);
                errs() << "}\n";
                errs() << "**************************************\n";
                errs() << "***************** OUT\n{\n";


                print_set(sOUT[&inst]);
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
            if(std::find(sGEN.begin(),sGEN.end(),&inst)!=sGEN.end()){
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
    void print_set(std::set<Value*> const& p_set){
        for(auto& i:p_set){
            errs() << " " << *i << '\n';
        }
    }
    void eliminate_multiple_definition(){

    }
    void ok(){

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

    void build_store_table(Function & F) {
        for (BasicBlock &bb : F){
            for(Instruction &inst : bb){
                if (isa<StoreInst>(&inst)){
                    StoreInst * store_instr = cast<StoreInst>(&inst);
                    Value * val = store_instr->getValueOperand();
                    Value * ptr = store_instr->getPointerOperand();
                    store_table[ptr].insert(val);
                }
            }
        }
    }

    void find_escaped(Function & F) {
        for (BasicBlock &bb : F){
            for(Instruction &inst : bb){
                Function * callee_fptr = get_callee_ptr(&inst);
                if (callee_fptr != NULL && !IS_CAT_OP(callee_fptr)) {
                    CallInst * callinstr = cast<CallInst>(&inst);
                    uint32_t arg_num = callinstr->getNumArgOperands();

                    for (uint32_t i = 0; i < arg_num; i++){
                        Value * arg = callinstr->getArgOperand(i);
                        std::vector<CallInst *> sub_escape;
                        if (get_CATvar_fromArg(arg, sub_escape)) {
                            escaped.insert(sub_escape.begin(), sub_escape.end());
                        }
                    }
                }
            }
        }
        
        errs() << escaped.size() << "  escaped var in " << F.getName().str() <<'\n';
        for ( auto it = escaped.begin(); it != escaped.end(); ++it ){
            errs() << **it <<'\n';
        }
    }

    bool get_CATvar_fromArg(Value * arg, std::vector<CallInst *> & sub_escape){
        if (isa<PHINode>(arg)){
            PHINode * phi = cast<PHINode>(arg);
            uint32_t numIncoming = phi->getNumIncomingValues();
            bool found = false;

            for (uint32_t i = 0; i < numIncoming; i++) {
                Value * inValue = phi->getIncomingValue(i);
                if (get_CATvar_fromArg(inValue, sub_escape)) {
                    found = true;
                }
            }

            return found;            
        }

        if (IN_STORE_TABLE(arg)){
            bool found = false;
            for (auto it = store_table[arg].begin(); it != store_table[arg].end(); it++){
                if(get_CATvar_fromArg(*it,sub_escape)){
                    found = true;
                }
            }
            return found;    
        }

        if (isa<CallInst>(arg)){
            CallInst * call_instr = cast<CallInst>(arg);
            Function * fptr = call_instr->getCalledFunction();
            // what about others?
            sub_escape.push_back(call_instr);
            if (IS_CAT_new(fptr)) return true;
        }

        return false;
    }
    
    /**
     * visited_phi[phi] returns a set of CAT_new under such phi
     * */
    int count_CAT_new_under_Phi(
        PHINode * phi, 
        std::map<PHINode *, std::set<Value *>> & visited_phi
    ) {
        errs() << "counting for " << *phi << '\n';
        if (IN_SET(visited_phi, phi)){
            return visited_phi[phi].size();
        }

        uint32_t numIncoming = phi->getNumIncomingValues();
        int cat_new_num = 0;
        visited_phi[phi] = std::set<Value *>();

        for (uint32_t i = 0; i < numIncoming; i++) {
            Value * inValue = phi->getIncomingValue(i);
            
            if(Function * fptr = get_callee_ptr(inValue)){
                if (IS_CAT_new(fptr)){
                    CallInst * call_instr = cast<CallInst>(inValue);
                    visited_phi[phi].insert(call_instr);
                    cat_new_num++;
                }

            } else if(isa<PHINode>(inValue)){
                PHINode * child_phi = cast<PHINode>(inValue);
                
                count_CAT_new_under_Phi(
                    child_phi,
                    visited_phi
                );

                cat_new_num += visited_phi[child_phi].size();
                visited_phi[phi].insert(
                    visited_phi[child_phi].begin(),
                    visited_phi[child_phi].end()
                );

            } else if(isa<Argument>(inValue)&&!isa<ConstantInt>(inValue)){
                Argument *arg = cast<Argument>(inValue);
                cat_arg.insert(arg);
                visited_phi[phi].insert(arg);
                cat_new_num++;
            }
        }

        return cat_new_num;
    }

    void add_edge(
        std::map<llvm::Value *, std::set<llvm::Value *>> &graph,
        llvm::Value * val_a,
        llvm::Value * val_b
    ) {
        if (!IN_MAP(graph, val_a)){
            graph[val_a] = std::set<llvm::Value *>();
        }

        if (!IN_MAP(graph, val_b)){
            graph[val_b] = std::set<llvm::Value *>();
        }

        graph[val_a].insert(val_b);
        graph[val_b].insert(val_a);

    }

    void add_edge_group(
        std::map<llvm::Value *, std::set<llvm::Value *>> &graph,
        // PHINode * phi,
        std::set<Value *> & cat_news
    ){  
        std::vector<Value *> cat_new_vec(cat_news.begin(), cat_news.end());

        // for(uint32_t i = 0; i < cat_new_vec.size(); i++){
        //     for(uint32_t j = i + 1; j < cat_new_vec.size(); j++){
        //         add_edge(
        //             graph,
        //             cat_new_vec[i],
        //             cat_new_vec[j],
        //             phi
        //         );
        //     }
        // }
        for(uint32_t i = 1; i < cat_new_vec.size() ; i++){
            add_edge(
                graph,
                cat_new_vec[i],
                cat_new_vec[i - 1]
            );
        }
    }

    void DFS(
        std::map<llvm::Value *, std::set<llvm::Value *>> &graph,
        std::set<llvm::Value *> & visited,
        llvm::Value * val_node,
        std::vector<llvm::Value *> & CC_sub
        // std::set<llvm::Value *> & CC_edge_sub
    ) {
        for (auto & ngbr : graph[val_node]) {
            if(!IN_SET(visited, ngbr)){
                
                visited.insert(ngbr);
                CC_sub.push_back(ngbr);
                // CC_edge_sub.insert(kv.second);

                DFS(
                    graph,
                    visited,
                    ngbr,
                    CC_sub
                    // CC_edge_sub
                );
            }
        }
    }
    
    void connected_components(
        std::map<llvm::Value *, std::set<llvm::Value *>> &graph,
        std::vector<std::vector<llvm::Value *>> & CC
        // std::vector<std::set<llvm::Value *>> & CC_edge
    ) {
        std::set<llvm::Value *> visited;
        for (auto &kv : graph){
            if(!IN_SET(visited, kv.first)){

                visited.insert(kv.first);
                std::vector<llvm::Value *> CC_sub;
                CC_sub.push_back(kv.first);

                // std::set<llvm::Value *> CC_edge_sub;

                DFS(
                    graph,
                    visited,
                    kv.first,
                    CC_sub
                    // CC_edge_sub
                );

                CC.push_back(CC_sub);
                // CC_edge.push_back(CC_edge_sub);
            }
        }
    }

    void print_CC(
        std::vector<std::vector<llvm::Value *>> &CC
        // std::vector<std::set<llvm::Value *>> & CC_edge
    ){
        errs() <<"printing CC\n";
        for(uint32_t i = 0; i < CC.size(); i++){
            errs() <<"#" << i << " CC\n";
            for(uint32_t j = 0; j < CC[i].size(); j++){
                errs() << *CC[i][j] <<'\n';
            }

            // errs() <<"Connected over\n";
            // for (auto it = CC_edge[i].begin(); it != CC_edge[i].end(); it++){
            //     errs() << **it <<'\n';
            // }

             errs() <<'\n';

        }
    }


    void print_phi_info(std::map<PHINode *, std::set<Value *>> &visited_phi){
        errs() <<"printing kv info\n" ;
        for (auto & kv : visited_phi){
            errs() << "Phi node: " << *kv.first <<'\n';
            for (auto &v : kv.second){
                errs()  << *v <<'\n';
            }
        }
    }


    void replace_instr_val(Instruction * instr, Value * val){
        BasicBlock::iterator ii(instr);
        BasicBlock * bb = instr->getParent();
        ReplaceInstWithValue(bb->getInstList(), ii, val);
    }

    /**
     * replace body with head
     * */
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
    

    /**
     * Create dummy CAT_new at the beginning of the Function
     * */
    CallInst * build_CAT_new_Head(Function & F){
        Instruction * first_instr = &(*instructions(F).begin());
        IRBuilder<> builder(first_instr);

        Constant * zeroConst = ConstantInt::get(IntegerType::get(currentModule->getContext(), 64), 0, true);
        // std::vector<Value *> arg_vec{zeroConst};
        ArrayRef<Value *> arg_arr_ref = ArrayRef<Value *>{zeroConst};

        Value * added_new_instr = builder.CreateCall(CAT_new_ptr, arg_arr_ref);
        return cast<CallInst>(added_new_instr);

    }

    void merge_Phi_CAT_new(
        Function & F,
        std::vector<llvm::Value *> & nodes
        // std::set<llvm::Value *> & edges
    ){
        /**
         * expect nodes to be all CallInstr on CAT_new
         * expect edges to be all phi node phi that connects CAT_new 
         * */
        std::set<llvm::Value *> nodes_set(nodes.begin(), nodes.end());

        Value * CAT_new_replace = NULL;

        // Need fix if we add dummy block for argument???
        
        // find first instruction in the first basic block in the set of Cat_new to be merged
        errs()<<"BEFORE\n";
        for(auto arg=F.arg_begin();arg!=F.arg_end();++arg){
            if(IN_SET(nodes_set, arg)){
                errs()<<"FOUND"<<*arg<<"\n";
                CAT_new_replace = cast<Value>(arg);
                break;
            }
        }
        for(Instruction & inst: F.getBasicBlockList().front()){
            if(IN_SET(nodes_set, &inst)){
                CAT_new_replace = cast<Value> (&inst);
                break;
            }
        }

        // if there's no such CAT_new, create a dummy one
        if (CAT_new_replace == NULL) CAT_new_replace = build_CAT_new_Head(F);

        for (uint32_t i = 0; i < nodes.size(); i++) {
            Value * CAT_new_old = cast<Value>(nodes[i]);

            if (CAT_new_old != CAT_new_replace){
                CAT_new_to_CAT_set(
                    CAT_new_old,
                    CAT_new_replace
                );
            }
            
        }
        errs()<<"AFTER\n";
        // for (auto it = edges.begin(); it != edges.end(); it++){
        //     PHINode * phi = cast<PHINode>(*it);
        //     replace_instr_val(phi, CAT_new_replace);
        // }
        
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

    void merge_Phi(
        std::map<PHINode *, std::set<Value *>> &visited_phi
    ){  
        std::set<PHINode *> worklist;
        bool merged_in_round = true;

        for (auto & kv : visited_phi){
            worklist.insert(kv.first);
        }

        while (merged_in_round && !worklist.empty())
        {
            // create temp as it's hard to erase while iterating
            std::set<PHINode *> worklist_temp = worklist;
            merged_in_round = false;

            for (auto & phi : worklist_temp){
                bool merged = merge_single_phi(phi);

                if (merged){
                    
                    worklist_temp.erase(phi);
                }
                merged_in_round = merged_in_round || merged;
            }

            worklist = worklist_temp;
        }
        
    }
    /**
     * Go through the function, find all CAT_new linked by Phi node
     * */
    void phi_node_new2set(Function & F){
        // std::unordered_map<PHINode *, std::vector<Value *>> to_merge;

        // graph[cat_new1][cat_new2] -> phi node that connects them
        errs() << "new2set for Function :" << F.getName().str() << '\n';
        std::map<llvm::Value *, std::set<llvm::Value *>> graph;

        std::map<PHINode *, std::set<Value *>> visited_phi;

        for (BasicBlock &bb : F){
            for(Instruction &inst : bb){
                if (isa<PHINode>(&inst)){
                    PHINode * phi = cast<PHINode>(&inst);
                    
                    if(!IN_SET(visited_phi, phi)){
                        errs() << "analyzing " << *phi << '\n';
                        int cnt = count_CAT_new_under_Phi(phi, visited_phi);
                        errs() << "get cnt = " << cnt << '\n';
                        if (cnt >= 2) {
                            add_edge_group(
                                graph,
                                visited_phi[phi]
                            );
                        }
                    }
                }   
            }
        }

        errs() << "fine before CC\n";
        std::vector<std::vector<llvm::Value *>> CC;
        // std::vector<std::set<llvm::Value *>> CC_edge;
        connected_components(
            graph,
            CC
            // CC_edge
        );

        print_CC(CC);
        print_phi_info(visited_phi);

        errs() << "fine before merge\n";
        for (uint32_t i = 0; i < CC.size(); i++){
            merge_Phi_CAT_new(
                F,
                CC[i]
            );
        }
        
        // for(auto & kv: to_merge){
        //     merge_phi_and_new(kv.first, kv.second);
        // }
        merge_Phi(visited_phi);
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


    // create set instruction before cat_add or cat_sub
    Value * build_cat_set(CallInst * call_instr, int64_t set_val) {
        IRBuilder<> builder(call_instr);
        std::vector<Value *> arg_vec;
        arg_vec.push_back(call_instr->getArgOperand(0));

        Type * llvm_int64 =  IntegerType::get(currentModule->getContext(), 64);
        Value * val = ConstantInt::get(llvm_int64, set_val, true);
        arg_vec.push_back(val);
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

//    CallInst * build_CAT_new_Head(Function & F){
//        Instruction * first_instr = &(*instructions(F).begin());
//        IRBuilder<> builder(first_instr);
//
//        Constant * zeroConst = ConstantInt::get(IntegerType::get(currentModule->getContext(), 64), 0, true);
//        // std::vector<Value *> arg_vec{zeroConst};
//        ArrayRef<Value *> arg_arr_ref = ArrayRef<Value *>{zeroConst};
//
//        Value * added_new_instr = builder.CreateCall(CAT_new_ptr, arg_arr_ref);
//        return cast<CallInst>(added_new_instr);
//
//    }
//
//        /**
//     *  This function is in charge of PHINode
//     */
//
//    int UF_count_CAT_new(PHINode *phi){
//        uint32_t numIncoming = phi->getNumIncomingValues();
//        int32_t CAT_new_counter = 0;
//
//        // Check If all CAT_new_Instr
//
//        for (uint32_t i = 0; i < numIncoming; i++) {
//            Value * inValue = phi->getIncomingValue(i);
//            if(isa<CallInst>(inValue)){
//                CallInst *call_instr = cast<CallInst>(inValue);
//                Function *callee_ptr = call_instr->getCalledFunction();
//                if(IS_CAT_new(callee_ptr))
//                    CAT_new_counter++;
//            }else if(isa<PHINode>(inValue)){
//                PHINode *phi = cast<PHINode>(inValue);
//                CAT_new_counter += UF_count_CAT_new(phi);
//            }
//        }
//        return CAT_new_counter;
//    }
//
//    void UF_CAT_new(DisjointSet *ds, PHINode *phi){
//        uint32_t numIncoming = phi->getNumIncomingValues();
//        // ALL new instruction
//        for (uint32_t i = 0; i < numIncoming; i++) {
//            Value * inValue = phi->getIncomingValue(i);
//            if(isa<CallInst>(inValue)){
//                CallInst *call_instr = cast<CallInst>(inValue);
//                Function *callee_ptr = call_instr->getCalledFunction();
//                if(IS_CAT_new(callee_ptr)){
//                    Instruction *a = cast<Instruction>(call_instr);
//                    Instruction *b = cast<Instruction>(phi);
//                    ds->Union(a,b);
//                }
//            }else if(isa<PHINode>(inValue)){
//                PHINode *next_phi = cast<PHINode>(inValue);
//                UF_CAT_new(ds, next_phi);
//            }
//        }
//    }
//
//
//
//    void eliminate_unique_definition_assumption(Function &F){
//        DisjointSet ds;
//        ds.makeSet(F);
//
//        // Analyze stage 1 - Connected graph of PHINode+CAT_new
//        for(auto &BB: F){
//            for(auto &instr: BB){
//                // If this is PHI Node and both sides are CAT_new
//                if(isa<PHINode>(instr)){
//                    PHINode *phi = cast<PHINode>(&instr);
//                    if(UF_count_CAT_new(phi)>=2)
//                        UF_CAT_new(&ds,phi);
//                }
//            }
//        }
//        DisjointSet ds2;
//        ds2.makeSet2(F);
//
//        // Analyze stage 2 - Connected graph of only CAT_new, record
//        auto it = ds2.parent.begin();
//        while(it!=ds2.parent.end()){
//            auto it2 = ds2.parent.begin();
//            while(it2!=ds2.parent.end()){
//                if(ds.Find(it->first)==ds.Find(it2->first)&&it!=it2){
//                    errs()<<"UNION:"<<*it->first<<" "<<*it2->first<<"\n";
//                    errs()<<"UNION:"<<it->first<<" "<<it2->first<<"\n";
//                    ds2.Union(it->first,it2->first);
//                }
//
//                it2++;
//            }
//            it++;
//        }
//        errs()<<"AFTER\n";
//        ds2.printSet();
//        // stage 3, get connected graph
//        std::unordered_map<Instruction *, std::set<Instruction *>> toReplace;
//        std::vector<Instruction *> toDelete;
//        it = ds2.parent.begin();
//        while(it!=ds2.parent.end()){
//            if(ds2.getConnectedSize(it->first)>=2){
//                if(it->first!=it->second){
//                    CallInst *cat_new1 = cast<CallInst>(it->first);
//                    CallInst *cat_new2 = cast<CallInst>(it->second);
//                    Value *arg1 = cat_new1->getArgOperand(0);
//                    Value *arg2 = cat_new2->getArgOperand(0);
//                    if(cast<ConstantInt>(arg1)->getSExtValue()==cast<ConstantInt>(arg2)->getSExtValue()){
//                        if(toReplace.find(ds2.Find(it->first))==toReplace.end()){
//                            toReplace[ds2.Find(it->first)]=std::set<Instruction *>();
//                            toReplace[ds2.Find(it->first)].insert(it->first);
//                        }else{
//                            toReplace[ds2.Find(it->first)].insert(it->first);
//                        }
//                    }
//
//                }
//            }
//
//            it++;
//        }
//        // get the shared predecessor of all instruction
//        std::unordered_map<Instruction *, std::vector<BasicBlock *>> toReplacePred;
//        auto it_toReplace = toReplace.begin();
//        while(it_toReplace!=toReplace.end()){
//            std::set<BasicBlock *> bb_set;
//            bb_set.insert(it_toReplace->first->getParent());
//            for(auto item : it_toReplace->second){
//                bb_set.insert(item->getParent());
//            }
//            BasicBlock *shared_pred = get_shared_pred(&bb_set);
//        }
//
//        //ds.printSet();
//        printtoreplace(toReplace);
//
//
//
//        // Transform
////        auto iter = toReplace.begin();
////        while(iter!=toReplace.end()){
////            CallInst* head = build_CAT_new_Head(F);
////            errs()<<"HEADING:"<<(*head)<<"\n";
////            for(auto item:iter->second){
////                //errs()<<"ITEM:"<<(*item)<<"\n";
////                CallInst *call_instr = cast<CallInst>(item);
////                int64_t num = cast<ConstantInt>(call_instr->getArgOperand(0))->getSExtValue();
////                CallInst *sub = cast<CallInst>(build_cat_set(call_instr,num));
////                errs()<<"REPLACING:"<<(*item)<<" with "<<(*sub)<<"\n";
////            }
////            iter++;
////        }
////        errs()<<"END\n";
//    }
//
//    BasicBlock *get_shared_pred(std::set<BasicBlock *> *inst_set){
//        auto iter = inst_set->begin();
//        while(iter!=inst_set->end()){
//            auto bb_iter = pred_begin(*iter);
//            // go through BB
//            std::set<BasicBlock> inter;
//            while(bb_iter!=pred_end(*iter)){
//
//            }
//        }
//    }
//
//    void replace_instr_val(Instruction * instr, Value * val){
//        BasicBlock::iterator ii(instr);
//        BasicBlock * bb = instr->getParent();
//        ReplaceInstWithValue(bb->getInstList(), ii, val);
//    }
//        void CAT_new_to_CAT_set(
//                llvm::CallInst * CAT_new_old,
//                llvm::CallInst * CAT_new_replace
//        ) {
//            IRBuilder<> builder(CAT_new_old);
//
//            Value * val = CAT_new_old->getArgOperand(0);
//
//            ArrayRef<Value *> arg_arr_ref = ArrayRef<Value *>{CAT_new_replace, val};
//
//            Value * added_set_instr = builder.CreateCall(CAT_set_ptr, arg_arr_ref);
//
//            // replacement
//            replace_instr_val(CAT_new_old, CAT_new_replace);
//        }
//
//    void printtoreplace(std::unordered_map<Instruction *, std::set<Instruction *> > toReplace){
//        auto it = toReplace.begin();
//        while(it!=toReplace.end()){
//            for(auto it2 : it->second){
//                errs()<<"Replacing "<<it2<<" with "<<it->first<<"\n";
//            }
//
//            it++;
//        }
//
//    }



    /**
     *  check if given @instr defines a constant
     *  if so result is stored in res, and return true
     *  otherwise return false, res is not touched
     * */ 
    bool check_constant_instr(Instruction * instr, int64_t * res) {
        
        
        if (!isa<CallInst>(instr)) return false;

        CallInst * call_instr = cast<CallInst>(instr);
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
    // Check if arg of call_instr can be simpliefed with constant propogation
    
    // Check if arg under in IN/OUT secenario of instr is constant

    // if so, return true, and store constant value into res
    // if not, return false, nothing should be changed to res
    bool check_constant(Instruction * instr, Value * arg, int64_t * res){
        // if (isa<Argument>(arg)) {
        //     return false;
        // }


        // if (isa<PHINode>(arg)) {
            
        //     errs() << * call_instr <<'\n';
        //     errs() << "has argument phi: " <<'\n';
        //     errs() << *arg << "\n\n";
        //     PHINode * phi = cast<PHINode>(arg);
        //     uint32_t numIncoming = phi->getNumIncomingValues();
        //     std::vector<int64_t> temp_val_arr(numIncoming);

        //     for (uint32_t i = 0; i < numIncoming; i++) {
        //         Value * inValue = phi->getIncomingValue(i);
        //         if (!check_constant(call_instr, inValue, &temp_val_arr[i]) ){
        //             return false;
        //         }
        //     }
        //     if (!vec_all_equal(temp_val_arr)) return false;

        //     *res = temp_val_arr[0];
        //     return true;
        // }
//        {
//            Function * callee_fptr = get_callee_ptr(instr);
//            if (callee_fptr != NULL && !IS_CAT_OP(callee_fptr)) {
//                CallInst * callinstr = cast<CallInst>(instr);
//                uint32_t arg_num = callinstr->getNumArgOperands();
//
//                for (uint32_t i = 0; i < arg_num; i++){
//                    Value * arg = callinstr->getArgOperand(i);
//                    std::vector<CallInst *> sub_escape;
//                    if (get_CATvar_fromArg(arg, sub_escape)) {
//                        escaped.insert(sub_escape.begin(), sub_escape.end());
//                    }
//                }
//            }
//        }


        if(isa<Argument>(arg)){
            if(IN_CAT_ARG(arg)){

            }else{
                return false;
            }
        }
        if (isa<CallInst>(arg)){
            errs()<<"IS A CALL!\n";
            CallInst * init_call_instr = cast<CallInst>(arg);
            if (IS_ESCAPED(init_call_instr)) return false;


            // instr2bitmap[arg] is everything that defines arg
            // if arg is a phi node, instr2bitmap[arg] contains everything after the generation of phi node
            BitVector defs_arg = instr2bitmap[arg];
            defs_arg &= INSTR_IN[instr];
            /**
             * INSTR_IN[&inst] must contain one and only one definition of arg
             * In other word,
             * (instr2bitmap[arg] & INSTR_IN[&inst]).count() must be one to be a constant
             *
             * */

            // if (isa<PHINode>(arg)) {

            //     errs() << * instr <<'\n';
            //     errs() << "has argument phi: " <<'\n';
            //     errs() << *arg << "\n";
            //     errs() << "instr2bitmap[arg]" << "\n";
            //     print_bitvector(instr2bitmap[arg]);
            //     errs() << "INSTR_IN[instr]" << "\n";
            //     print_bitvector(INSTR_IN[instr]);
            //      errs() << "\n";
            // }
            if (defs_arg.count() == 0){
                return false;
                // if (isa<PHINode>(arg)) {

                //     errs() << * instr <<'\n';
                //     errs() << "has argument phi: " <<'\n';
                //     errs() << *arg << "\n\n";
                //     PHINode * phi = cast<PHINode>(arg);
                //     uint32_t numIncoming = phi->getNumIncomingValues();
                //     std::vector<int64_t> temp_val_arr(numIncoming);

                //     for (uint32_t i = 0; i < numIncoming; i++) {
                //         Value * inValue = phi->getIncomingValue(i);
                //         if (!check_constant(phi, inValue, &temp_val_arr[i]) ){
                //             return false;
                //         }
                //     }
                //     if (!vec_all_equal(temp_val_arr)) return false;

                //     *res = temp_val_arr[0];
                //     return true;
                // } else {
                //     return false;
                // }
            }

            // one arg could have multiple IN definition, but happen to have same value
            // Get the all definition available for current instruction
            unsigned idx = defs_arg.find_first();
            bool is_const;
            int64_t const_val;
            std::vector<int64_t> const_vec;
            while (idx != -1) {
                Instruction * def_instr = instr_vec[idx];
                is_const = check_constant_instr(def_instr, &const_val);

                // one definition is not constant, return false directly
                if (!is_const) return false;

                const_vec.push_back(const_val);

                idx = defs_arg.find_next(idx);
            }

            bool all_const_eq = vec_all_equal(const_vec);
            if (!all_const_eq) return false;

            *res = const_vec[0];





            return true;
        }else{
            return false;
        }
        //

        CallInst * init_call_instr = cast<CallInst>(arg);
        if (IS_ESCAPED(init_call_instr)) return false;


        // instr2bitmap[arg] is everything that defines arg
        // if arg is a phi node, instr2bitmap[arg] contains everything after the generation of phi node
        BitVector defs_arg = instr2bitmap[arg];
        defs_arg &= INSTR_IN[instr];
        /**
         * INSTR_IN[&inst] must contain one and only one definition of arg
         * In other word,
         * (instr2bitmap[arg] & INSTR_IN[&inst]).count() must be one to be a constant 
         * 
         * */
        
        // if (isa<PHINode>(arg)) {
            
        //     errs() << * instr <<'\n';
        //     errs() << "has argument phi: " <<'\n';
        //     errs() << *arg << "\n";
        //     errs() << "instr2bitmap[arg]" << "\n";
        //     print_bitvector(instr2bitmap[arg]);
        //     errs() << "INSTR_IN[instr]" << "\n";
        //     print_bitvector(INSTR_IN[instr]);
        //      errs() << "\n";
        // }
        if (defs_arg.count() == 0){
            return false;
            // if (isa<PHINode>(arg)) {
            
            //     errs() << * instr <<'\n';
            //     errs() << "has argument phi: " <<'\n';
            //     errs() << *arg << "\n\n";
            //     PHINode * phi = cast<PHINode>(arg);
            //     uint32_t numIncoming = phi->getNumIncomingValues();
            //     std::vector<int64_t> temp_val_arr(numIncoming);

            //     for (uint32_t i = 0; i < numIncoming; i++) {
            //         Value * inValue = phi->getIncomingValue(i);
            //         if (!check_constant(phi, inValue, &temp_val_arr[i]) ){
            //             return false;
            //         }
            //     }
            //     if (!vec_all_equal(temp_val_arr)) return false;

            //     *res = temp_val_arr[0];
            //     return true;
            // } else {
            //     return false;
            // }
        }

        // one arg could have multiple IN definition, but happen to have same value
        // Get the all definition available for current instruction
        unsigned idx = defs_arg.find_first();
        bool is_const;
        int64_t const_val;
        std::vector<int64_t> const_vec;
        while (idx != -1) {
            Instruction * def_instr = instr_vec[idx];
            is_const = check_constant_instr(def_instr, &const_val);

            // one definition is not constant, return false directly
            if (!is_const) return false;

            const_vec.push_back(const_val);

            idx = defs_arg.find_next(idx);
        }
        
        bool all_const_eq = vec_all_equal(const_vec);
        if (!all_const_eq) return false;

        *res = const_vec[0];
        return true;
        
    }

    void replace_from_map(std::unordered_map<llvm::CallInst *, Value *> & replace_map) {
        for (auto & kv: replace_map) {
            BasicBlock::iterator ii(kv.first);
            BasicBlock * bb = kv.first->getParent();
            ReplaceInstWithValue(bb->getInstList(), ii, kv.second);
        }
        errs() << "done!\n";
    }

    void constant_folding(Function & F) {
        // errs() << "Folding on " << F.getName().str() << '\n';
        unsigned inst_counter = 0;
        std::unordered_map<llvm::CallInst *, Value *> toFold;
        std::unordered_map<llvm::CallInst *, int64_t> toFold_helper;
        for (BasicBlock &bb : F){
            for(Instruction &inst : bb){

                if (isa<CallInst>(&inst)) {
                    CallInst * call_instr = cast<CallInst>(&inst);
                    Function * callee_ptr = call_instr->getCalledFunction();
                    if (IS_CAT_add(callee_ptr) || IS_CAT_sub(callee_ptr)) {
                        
                        // errs() << "Constant Folding on " << *call_instr  << '\n';

                        Value * arg0 = call_instr->getArgOperand(0);
                        Value * arg1 = call_instr->getArgOperand(1);
                        Value * arg2 = call_instr->getArgOperand(2);
                        
                        int64_t arg1_val = 0, arg2_val = 0;
                        bool arg1_const = check_constant(call_instr, arg1, &arg1_val);
                        bool arg2_const = check_constant(call_instr, arg2, &arg2_val);

                        int64_t substitution = (IS_CAT_add(callee_ptr) ? arg1_val + arg2_val : arg1_val - arg2_val);
                        
                        if (arg1_const && arg2_const) {
                            // toFold[call_instr] = build_cat_set(call_instr, substitution);
                            toFold_helper[call_instr] = substitution;
                        }
                    }
                }
                inst_counter++;
            }
        }

        for (auto &kv: toFold_helper) {
            toFold[kv.first] = build_cat_set(kv.first, kv.second);
        }
        replace_from_map(toFold);
        // for (BasicBlock &bb : F){
        //     for(Instruction &inst : bb){
        //         errs() << inst << '\n';   
        //     }
        //     errs() << '\n';
        // }
    }

    void constant_propagation(Function & F) {
        // errs() << "Propogate on " << F.getName().str() << '\n';
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
                        bool arg_const = check_constant(call_instr, arg, &arg_val);

                        if (arg_const) {
                            errs() << *call_instr << " replaced with " << arg_val <<'\n';
                            toPropogate[call_instr] = build_constint(arg_val);
                        }
                    }
                }
            }
        }
        replace_from_map(toPropogate);
    }

    void live_analysis_init(Function & F){
        // std::unordered_map<llvm::Instruction *, llvm::BitVector> live_GEN, live_KILL;
        // std::unordered_map<llvm::Instruction *, llvm::BitVector> live_IN, live_OUT;
        // std::unordered_map<llvm::BasicBlock *, llvm::BitVector> live_GEN_BB, live_KILL_BB;
        // std::unordered_map<llvm::BasicBlock *, llvm::BitVector> live_IN_BB, live_OUT_BB;
        unsigned NumInstrs = F.getInstructionCount();
        for (BasicBlock &bb : F){
            live_GEN_BB[&bb] = BitVector(NumInstrs, 0);
            live_KILL_BB[&bb] = BitVector(NumInstrs, 0);
            for(Instruction &inst : bb){
                live_GEN_INST[&inst] = BitVector(NumInstrs, 0);
                live_KILL_INST[&inst] = BitVector(NumInstrs, 0);
            }
        }
    }
    

    void live_analysis_GENKILL(Function & F){
        unsigned NumInstrs = F.getInstructionCount();

        unsigned i = 0;
        for (BasicBlock &bb : F){
            for(Instruction &inst : bb){
                Function * fptr = get_callee_ptr(&inst);
                if(fptr){
                    CallInst * call_instr = cast<CallInst>(&inst);
                    if (IS_CAT_OP(fptr)){
                        if (IS_CAT_new(fptr)){
                            // only define but not killed
                            live_KILL_INST[&inst].set(i);

                        } else if (IS_CAT_get(fptr)) {
                            // only use variable, CAT_get
                            live_GEN_INST[&inst].set(i);

                        } else if (IS_CAT_get(fptr)) {

                        }

                    } else {

                    }

                }
                i++;
            }
        }
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
