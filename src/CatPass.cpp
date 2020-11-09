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
#include "llvm/Analysis/AliasAnalysis.h"
#include <set>
#include <unordered_set>
#include <vector>
#include <map>
#include <unordered_map>
#include <queue>
using namespace llvm;
 
#define IN_MAP(map, key) (map.find(key) != map.end())
#define IN_SET(set, key) (set.find(key) != set.end())

namespace {
//     template<class T> class Set:public std::set<T>{
//     public:

// };
struct CAT : public FunctionPass {
    static char ID; 
    Module *currentModule;
    std::unordered_set<Function *> user_func;
#define IS_USER_FUNC(fptr) (IN_SET(user_func, fptr))
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

    std::set<Value*> cat_var;
#define IS_CAT_VAR(ptr) (cat_var.find(ptr)!=cat_var.end())
    std::set<Value *> arg_set;
    std::set<Value *> CAT_new_collect;
    //Generic IN / OUT set
    // std::vector<Value*> sGEN;
    std::set<Value*> sGEN;
    std::unordered_map<Value*, std::set<Value*>> sKILL;
    std::unordered_map<Value*, std::set<Value*>> sVar2Def;
    std::unordered_map<Value*, std::set<Value*>> sBB_GEN;
    std::unordered_map<Value*, std::set<Value*>> sBB_KILL;
    std::unordered_map<Value *, std::set<Value*>> sBB_IN, sBB_OUT;
    std::unordered_map<Value *, std::set<Value*>> sIN, sOUT;
    std::unordered_map<Value *, Value*> ptrToVal;

    // May-Point-to Analysis
    std::unordered_map<Value *, std::set<std::pair<Value*, Value*>>> mptGEN; // instruction -> {(p,x)}
    std::unordered_map<Value *, std::set<std::pair<Value*, Value*>>> mptKILL; // instruction -> {(p,v)| v escaped}
    std::unordered_map<Value *, std::set<Value *>> ptr2Val; // p->{x | for all x that (p,x) };
    std::unordered_map<Value *, std::set<Value *>> val2Ptr; // x->{p | for all p that (p,x) }
    std::unordered_map<Value *, std::set<std::pair<Value*, Value*>>> mptIN;
    std::unordered_map<Value *, std::set<std::pair<Value*, Value*>>> mptOUT;
    std::unordered_map<Value *, std::set<Value *>> ptr2AliasPtrs;
    std::unordered_map<Value *, std::set<Value *>> ptr2Ptr;
    std::unordered_map<Value *, Value*> mustAliasing;

    std::unordered_map<Value*, std::set<Value*>> mayPointTo;
    
    /**
     * maps from user call to a map from its argument to replacement
     * Keep it map as we might need to iterate pretty often
     * userCall2replace : {userfunction Call -> {arg -> replaced dummy instruction}}
     * repalce2userCall: {replaced dummy instruction -> [userfunction Call, arg]}
     * */
    std::map<Instruction *, std::map<Value *, Instruction *>> userCall2replace;
    std::map<Instruction *, std::pair<Instruction *, Value * >> replace2userCall;

    /**
     *  WARNING!!! 
     * 
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
    */

#define HAS_MOD(info) (\
        info == ModRefInfo::MustMod \
    || info == ModRefInfo::MustModRef \
    || info == ModRefInfo::Mod \
    || info == ModRefInfo::ModRef \
)

#define MUST_MOD(info)(info==ModRefInfo::MustMod||info==ModRefInfo::MustModRef)
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

    // May-point-to analysis
    template<class T>
    class PairSet{
        public:
            std::set<std::pair<T,T>> pairSet;

        };

    // deadcode elimination
    std::unordered_map<llvm::Instruction *, llvm::BitVector> live_GEN_INST, live_KILL_INST;
    std::unordered_map<llvm::Instruction *, llvm::BitVector> live_IN_INST, live_OUT_INST;
    std::unordered_map<llvm::BasicBlock *, llvm::BitVector> live_GEN_BB, live_KILL_BB;
    std::unordered_map<llvm::BasicBlock *, llvm::BitVector> live_IN_BB, live_OUT_BB;
        // class to represent a disjoint set
        CAT() : FunctionPass(ID) {}

    // This function is invoked once at the initialization phase of the compiler
    // The LLVM IR of functions isn't ready at this point
    bool doInitialization (Module &M) override {
        // errs() << "Hello LLVM World at \"doInitialization\"\n" ;
        currentModule = &M;

        for (Function & F: M) {
            /**
             * Function with basic blocks are user defined function
             * */
            if (!F.empty()){
                user_func.insert(&F);
            }
        }

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
        //findCatVariables(F);
        //phi_node_new2set(F);
        AliasAnalysis & AA = getAnalysis<AAResultsWrapperPass>().getAAResults();

        build_store_table(F);

        H0_init();
        H0_function_count(F);
        // H0_output(caller_name);

        sGEN_sKILL_init();
        mptGEN_KILL(F);
        mptIN_OUT(F);
        sGEN_sKILL(F, AA);
        sIN_sOUT(F);
        sIN_OUT_inst(F);
        constant_folding(F, AA);


        sGEN_sKILL_init();
        mptGEN_KILL(F);
        mptIN_OUT(F);
        sGEN_sKILL(F, AA);
        sIN_sOUT(F);
        sIN_OUT_inst(F);
        constant_propagation(F, AA);

//        sGEN_sKILL_init();
//        mptGEN_KILL(F);
//        mptIN_OUT(F);
//        sGEN_sKILL(F, AA);
//        sIN_sOUT(F);
//        sIN_OUT_inst(F);
//        constant_folding(F, AA);
//
//        sGEN_sKILL_init();
//        mptGEN_KILL(F);
//        mptIN_OUT(F);
//        sGEN_sKILL(F, AA);
//        sIN_sOUT(F);
//        sIN_OUT_inst(F);
//        constant_propagation(F, AA);
    //    constant_propagation(F);
        return false;
    }

    // We don't modify the program, so we preserve all analyses.
    // The LLVM IR of functions isn't ready at this point
    void getAnalysisUsage(AnalysisUsage &AU) const override {
        // errs() << "Hello LLVM World at \"getAnalysisUsage\"\n" ;

        // AU.setPreservesAll();
        AU.addRequired<AAResultsWrapperPass>();
    }


        //naive GEN KILL IN OUT
    void sGEN_sKILL_init() {
        sGEN.clear();
        sKILL.clear();
        sBB_GEN.clear();
        sBB_KILL.clear();
        sBB_IN.clear();
        sBB_OUT.clear();
        sIN.clear();    
        sOUT.clear();

        arg_set.clear();
        mayPointTo.clear();
        mptGEN.clear();
        mptKILL.clear();

        ptr2Val.clear();
        val2Ptr.clear();
        ptr2AliasPtrs.clear();

    }
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
/**
     *  Given call instruction on CAT_set, CAT_add, CAT_sub
     *      find target of operation
     * */
        Value * get_define_target(CallInst * call_instr) {

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

                key = val ? val : arg0;
            }

            return key;
        }


    void findCATVar(Function &F){
            cat_var.clear();
            for(auto& inst:instructions(F)){
                if(isa<CallInst>(&inst)){
                    CallInst *callInst = cast<CallInst>(&inst);
                    Function *callee = callInst->getCalledFunction();
                    if(IS_CAT_new(callee))
                        cat_var.insert(&inst);
                    if(IS_CAT_add(callee)||IS_CAT_sub(callee)){
                        int num = callInst->getNumArgOperands();
                        for(auto i = 0; i<num;i++){
                            Value *arg = callInst->getArgOperand(i);
                            cat_var.insert(arg);
                        }
                    }else
                    if(IS_CAT_set(callee)||IS_CAT_get(callee)){
                        Value *arg = callInst->getArgOperand(0);
                        cat_var.insert(arg);
                    }

                }
            }
        }

    void mptGEN_KILL(Function &F){
            findCATVar(F);
            std::set<Value *> allValue;

            // May-Point-To GEN
            for(auto &bb : F){
                for(auto &inst: bb){
                    if(isa<StoreInst>(&inst)){
                        StoreInst *storeInst = cast<StoreInst>(&inst);
                        Value *valueStored = storeInst->getValueOperand();
                        Value *ptrOperand = storeInst->getPointerOperand();
                        // If p -> v
                        mptGEN[&inst].insert(std::make_pair(ptrOperand,valueStored));
                        ptr2Val[ptrOperand].insert(valueStored);
                        // store this v, this can be anything not only cat var
                        allValue.insert(valueStored);
                    }

                    // Store this and waiting to be killed further
                    if(isa<SelectInst>(&inst)){
                        SelectInst *selectInst = cast<SelectInst>(&inst);
                        int num_arg = selectInst->getNumOperands();
                        for(auto i=1;i<num_arg;i++){
                            Value *aPtr = selectInst->getOperand(i);
                            ptr2AliasPtrs[aPtr].insert(&inst);
                            ptr2AliasPtrs[&inst].insert(aPtr);
                        }
                    }
                }
            }

            // MPT KILL
            // KILL only if this ptr escaped
            for(auto &&bb : F){
                for(auto &inst: bb){
                    if(isa<StoreInst>(&inst)){
                        StoreInst *storeInst = cast<StoreInst>(&inst);
                        Value *valueStored = storeInst->getValueOperand();
                        Value *ptrOperand = storeInst->getPointerOperand();
                        // If p -> v, just insert every escaped var here
                        // Kill all (p, cat_var), not matter what
                        // because here we just redefine p so it does not matter
                        // If SELECT INST, it is for sure they will be alias, e.g p = select 1 q r
                        // then KILL all (p,x) (q,x) (r,x)
                        for(auto& alias:ptr2AliasPtrs){
                            if(IN_SET(alias.second,ptrOperand)){
                                errs()<<"FIND:ALIAS "<< *alias.first<<"\n";
                                // first
                                for(auto& e:allValue){
                                    mptKILL[&inst].insert(std::make_pair(alias.first,e));
                                }
                                //second
                                for(auto& e:allValue){
                                    for(auto& p:alias.second){
                                        mptKILL[&inst].insert(std::make_pair(p,e));
                                    }
                                }
                            }
                        }

                        // {(p,v)| v escaped}
                        // Just simply kill all (p,v)
                        for(auto& e:allValue){
                            mptKILL[&inst].insert(std::make_pair(ptrOperand,e));
                        }

                    }
                }
            }
        }

        void mptIN_OUT(Function &F){
            // GEN KILL for each BB
            std::unordered_map<Value *, std::set<std::pair<Value*,Value*>>> mptBB_IN;
            std::unordered_map<Value *, std::set<std::pair<Value*,Value*>>> mptBB_OUT;
            for(auto &BB:F){
                mptBB_IN[&BB] = std::set<std::pair<Value*,Value*>>();
                mptBB_OUT[&BB] = std::set<std::pair<Value*,Value*>>();
            }


            bool changed;
            do{
                changed = false;
                for(auto& BB:F){
                    for(auto Pred:predecessors(&BB)){
                        std::set<std::pair<Value*,Value*>> temp;
                        set_union(mptBB_IN[&BB],mptBB_OUT[Pred],temp);
                        mptBB_IN[&BB] = temp;
                    }
                    std::set<std::pair<Value*,Value*>> local_IN = mptBB_IN[&BB];
                    std::set<std::pair<Value*,Value*>> local_OUT = mptBB_IN[&BB];
                    for(auto& inst:BB){
                        local_IN = local_OUT;
                        mptIN[&inst] = local_IN;


                        if(isa<StoreInst>(&inst)){

                            StoreInst *storeInst = cast<StoreInst>(&inst);
                            Value *valueStored = storeInst->getValueOperand();
                            Value *ptrOperand = storeInst->getPointerOperand();
                            // if p->v

                            std::set<std::pair<Value*,Value*>> temp;
                            // TEMP = IN[i] - KILL[i]
                            set_diff(local_IN,mptKILL[&inst],temp);
                            // OUT[i] = GEN[i] U TEMP
                            std::set<std::pair<Value*,Value*>> out;
                            set_union(temp,mptGEN[&inst],out);
                            if(!changed){
                                changed = (out!=mptOUT[&inst]);
                            }
                            local_OUT = out;

                        }

                        //FIXME:
                        // If store, remember the must alias table
                        if(isa<LoadInst>(&inst)){
                            errs()<<inst<<"\n";
                            LoadInst* loadInst = cast<LoadInst>(&inst);
                            Value* ptr = loadInst->getPointerOperand();
                            // find if (loadRoot,x) in mptIN
                            std::set<std::pair<Value*,Value*>> temp;
                            for(auto& pr:mptIN[&inst]){
                                //find
                                if(ptr==pr.first){
                                    temp.insert(pr);
                                    errs()<<*pr.first<<" ,"<<*pr.second<<"\n";
                                }
                            }

                            if(temp.size()==1){
                                //(0,1)
                                Value *t = temp.begin()->second;
                                //(0,3) -> (3,1)
                                mustAliasing[loadInst]=t;
                            }else if(temp.size()==0){
                                // If we can find the ptr in the mustAliasing
                                if(mustAliasing.find(ptr)!=mustAliasing.end()){
                                    //errs()<<"FIND";
                                    // The size of it must be 1
                                    Value* t = mustAliasing[ptr];
                                    //

                                    std::set<std::pair<Value*,Value*>> temp2;
                                    for(auto& pr:mptIN[&inst]){
                                        //find
                                        if(t==pr.first){
                                            temp2.insert(pr);
                                        }
                                    }
                                    if(temp2.size()==0){
                                        cat_var.insert(loadInst);
                                        local_OUT.insert(std::make_pair(ptr,loadInst));
                                    }else{
                                        Value *t1 = temp2.begin()->second;
                                        mustAliasing[loadInst]=t1;
                                    }

                                }else{
                                    cat_var.insert(loadInst);
                                    local_OUT.insert(std::make_pair(ptr,loadInst));
                                }


                            }

                            if(!changed){
                                changed = (local_OUT!=mptOUT[&inst]);
                            }
                        }


                        if(isa<SelectInst>(&inst)){

                           /*
                            std::set<std::pair<Value*,Value*>> temp;
                            for(int i=0;i<num_arg;i++){
                                Value* q = selectInst->getOperand(i);
                                for(auto& item:mptIN[&inst]){
                                    if(item.first==q){
                                        temp.insert(std::make_pair(&inst,item.second));
                                    }
                                }
                            }

                            std::set<std::pair<Value*,Value*>> all_x;
                            for(auto& x:cat_var){
                                all_x.insert(std::make_pair(&inst,x));
                            }

                            std::set<std::pair<Value*,Value*>> diff;

                            set_diff(mptIN[&inst],all_x,diff);

                            std::set<std::pair<Value*,Value*>> out;

                            set_union(temp,diff,out);

                            if(!changed){
                                changed = (out!=mptOUT[&inst]);
                            }
                            local_OUT = out;
                            errs()<<"SELECT INST\n";
                            for(auto& item:out){

                                errs()<<*item.first<<"  "<<*item.second<<"\n";
                            }
                            */
                        }


                        mptOUT[&inst] = local_OUT;
                    }
                    mptBB_OUT[&BB]=local_OUT;
                }

            }while(changed);

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
        errs() << *newInst << " at " << newInst << '\n';
        return newInst;
    }

    void dummy_def_val(Value * val, CallInst * call_instr){
        Instruction * dummy = dummy_instr_create();

        userCall2replace[call_instr][val] = dummy;
        replace2userCall[dummy] = std::make_pair(call_instr, val);

        sGEN.insert(dummy);
        sVar2Def[val].insert(dummy);

        
    }


    void sGEN_sKILL(Function &F, AliasAnalysis & AA){
        /**
         *  Handling GEN KILL for Function argument
         * */
        
        for (Argument &arg:  F.args()){
            if (isa<PointerType>(arg.getType())) {

                
                arg_set.insert(&arg);
                sGEN.insert(&arg);

                sVar2Def[&arg].insert(&arg);

                /**
                 * Assume all pointers are CAT variables??
                 * */
                CAT_new_collect.insert(&arg);
            } 
        }


        for (auto& inst: llvm::instructions(F)) {
            if (isa<CallInst>(&inst)){
                CallInst * call_instr = cast<CallInst>(&inst);
                Function * callee_ptr = call_instr->getCalledFunction();

                if (IS_CAT_OP(callee_ptr)) {
                
                    if (!IS_CAT_get(callee_ptr)) {
                        sGEN.insert(call_instr);

                        Value * key;
                        if (IS_CAT_new(callee_ptr)) {
                            key = call_instr;

                            CAT_new_collect.insert(call_instr);
                        } else {
                            // get first operand if CAT_set, CAT_add, CAT_sub

                            Value * arg0 = call_instr->getArgOperand(0);
                            key = arg0;
                            if(isa<LoadInst>(arg0)){
                                key = getLoadCatVar(arg0);
                            }
                        }
                        sVar2Def[key].insert(call_instr);
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
                            ptr_trace_back(arg, possible_vals);

                            for (uint32_t j = 0; j < possible_vals.size(); j++) {

                                    MemoryLocation memLoc(possible_vals[j]);
                                    ModRefInfo info = AA.getModRefInfo(call_instr, memLoc); 


                                    errs() << *call_instr << " has arg " << *arg << " at " << arg << " ModRefInfo = " << ModRefInfo_toString(info) <<'\n';
                                    if (HAS_MOD(info)){
                                        
                                        dummy_def_val(possible_vals[j], call_instr);
                                    }
                            }
                        }                
                    }
                    
                    /**
                     * If call instruction itself returns a pointer
                     * */
                    if (isa<PointerType>(call_instr->getType())) {
                        sGEN.insert(call_instr);
                        sVar2Def[call_instr].insert(call_instr);
                    }
                }

            } else if (isa<PHINode>(&inst)) {
                PHINode * phi = cast<PHINode> (&inst);

                /**
                 * only phi node with Pointer type we should care, right?
                 * */
                if (isa<PointerType> (phi->getType())){
                    // errs() << *phi <<  " with type " << *phi->getType() << '\n';
                    sGEN.insert(phi);

                    sVar2Def[phi].insert(phi);
                }
                
            } else if (isa<StoreInst>(&inst)){
                StoreInst *storeInst = cast<StoreInst>(&inst);
                Value* valueStored = storeInst->getValueOperand();
                Value* ptrOperand = storeInst->getPointerOperand();
                ptrToVal[ptrOperand] = valueStored;
            }
        }


        /**
         *  Generating KILL per instruction
         * */ 
        for(Value * gen : sGEN){

            if (isa<CallInst>(gen)){
                CallInst * call_instr = cast<CallInst>(gen);
                Function * callee_ptr = call_instr->getCalledFunction();

                if (IS_CAT_OP(callee_ptr)) {

                    if (!IS_CAT_get(callee_ptr)) {

                        Value * key;
                        if (IS_CAT_new(callee_ptr)) {
                            key = call_instr;
                        } else {
                            // get first operand if CAT_set, CAT_add, CAT_sub
                            Value * arg0 = call_instr->getArgOperand(0);
                            key = arg0;
                            if(isa<LoadInst>(arg0)){
                                Value *loadRoot = getLoadRoot(call_instr, arg0);
                                key = getLoadCatVar(arg0);
                            }
                        }

                        sKILL[gen] =  sVar2Def[key];
                    }

                } else if (IS_USER_FUNC(callee_ptr)) {
                    sKILL[gen] =  sVar2Def[call_instr];
                }

            } else if (isa<PHINode>(gen)) {
                PHINode * phi = cast<PHINode> (gen);
                sKILL[gen] =  sVar2Def[phi];

            } else if (IN_MAP(replace2userCall, (Instruction *)gen)) {
                /**
                 * This is a dummy instruction created by ourselves
                 * */
                Instruction * dummy = cast<Instruction> (gen);
                Instruction * call_inst = replace2userCall[dummy].first;
                Value * arg = replace2userCall[dummy].second;

                sKILL[gen] =  sVar2Def[arg];
            }

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
            for(Instruction &inst : bb){

                if (IN_MAP(userCall2replace, &inst)){
                    /**
                     * This is a instruction that calls others
                     * IN[i] should just be the previous IN
                     * OUT[i] should be the last OUT produced by arguments replacement 
                     */
                    __INSTR_INOUT(prev_out, &inst);
                    sIN[&inst] = prev_out;
                    for (auto & kv : userCall2replace[&inst]) {
                        Instruction * dummy_instr = kv.second;
                        __INSTR_INOUT(prev_out, dummy_instr);
                        sOUT[&inst] = prev_out;
                    }

                } else {
                    /**
                     * This is a normal instruction should be good with what we have done before
                     */
                   __INSTR_INOUT(prev_out, &inst);
                }
                
            }
        }
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

    void print_set_with_addr(std::set<Value*> const& p_set){
        for(auto& i:p_set){
            errs() << " " << *i << " at " << i << '\n';
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

    void ptr_trace_back(Value * ptr, std::vector<Value *> & possible_val){
        if (IN_STORE_TABLE(ptr)) {
            for (auto & val : store_table[ptr]) {
                ptr_trace_back(val, possible_val);
            }
        } else {
            possible_val.push_back(ptr);
        }
        
    }

    void build_store_table(Function & F) {
        store_table.clear();

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
     *  Wrapper with AliasAnalysis.
     *  If we arg MUST Alias with some CAT_var, we are same to claim it's constant
     *          as long as one of them is constant in terms of reaching definition of instr
     * */

    bool check_constant_AA_wrap(AliasAnalysis & AA, Instruction * instr, Value * arg, int64_t * res) {
        std::vector<Value *> aliases;
        aliases.push_back(arg);
        bool mustAlias = false;
        for (auto & cat_var : CAT_new_collect) {
            if (cat_var != arg){
                AliasResult AAResult = AA.alias(cat_var, arg);
                if (AAResult == AliasResult::MustAlias) {
                    errs() << *arg << " at " << arg << " alias with " << *cat_var << " at " << cat_var << '\n';
                    mustAlias = true;
                    aliases.push_back(cat_var);
                }
            }
            
        }
        int64_t temp_val;
        if(!mustAlias){
            // Check IN OUT of this inst

            if(isa<LoadInst>(arg)){
                if(check_constant_s(instr, getLoadCatVar(arg), &temp_val)) {
                    *res = temp_val;
                    return true;
                }
            }
        }

        /**
         * If one alias is sure to be constant we should be good to propogate
         * */

        for (uint32_t i = 0; i < aliases.size(); i++) {
            if(check_constant_s(instr, aliases[i], &temp_val)) {
                *res = temp_val;
                return true;
            }
        }
        return false;
    }
    // get @g, the root pointer
    Value* getLoadRoot(Instruction *instr, Value* arg){
        LoadInst *loadInst = cast<LoadInst>(arg);
        Value* ptr = loadInst->getPointerOperand();
        if(isa<LoadInst>(ptr)){
            return getLoadRoot(loadInst, ptr);
        }
        return ptr;
    }

    // get the root var this thing point to
    Value* getLoadCatVar(Value* arg){
        if(mustAliasing.find(arg)!=mustAliasing.end())
            return getLoadCatVar(mustAliasing[arg]);
            return arg;
    }
    std::set<Value*> getLoadLeaf(Instruction* instr, Value* loadRoot){

        std::set<Value*> leaf;
        leaf.clear();
        for(auto& item : mptIN[instr]){
            //errs()<<*item.first<<"\n";
            if(loadRoot==item.first){
                std::set<Value*> temp;
                temp = getLoadLeaf(instr, item.second);
                if(temp.size() == 0){
                    //errs()<<"LOOOOOL:"<<*item.second;
                    temp.insert(item.second);
                    return temp;
                }else{
                    std::set<Value*> temp2;
                    set_union(leaf,temp,temp2);
                    leaf = temp2;
                }
            }
        }
        //errs()<<"Returning:";
        return leaf;
    }

    bool check_constant_s(Instruction * instr, Value * arg, int64_t * res) {
        
        /**
         * Find the intersection between reaching definition of instr and definitions that define arg
        */
        std::set<Value *> arg_defs;
        set_intersect(sIN[instr], sVar2Def[arg], arg_defs);

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

    void constant_folding(Function & F, AliasAnalysis & AA) {
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
                        // bool arg1_const = check_constant_s(call_instr, arg1, &arg1_val);
                        // bool arg2_const = check_constant_s(call_instr, arg2, &arg2_val);
                        
                        bool arg1_const = check_constant_AA_wrap(AA, call_instr, arg1, &arg1_val);
                        bool arg2_const = check_constant_AA_wrap(AA, call_instr, arg2, &arg2_val);

                        int64_t substitution = (IS_CAT_add(callee_ptr) ? arg1_val + arg2_val : arg1_val - arg2_val);
                        
                        if (arg1_const && arg2_const) {
                            // toFold[call_instr] = build_cat_set(call_instr, substitution);
                            
                            // errs() << "Folding " << *call_instr << " with " << substitution << '\n';
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
    }

    void constant_propagation(Function & F, AliasAnalysis & AA) {
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
                        // bool arg_const = check_constant_s(call_instr, arg, &arg_val);

                        bool arg_const = check_constant_AA_wrap(AA, call_instr, arg, &arg_val);
                        if (arg_const) {
                            // errs() << *call_instr << " replaced with " << arg_val <<'\n';
                            toPropogate[call_instr] = build_constint(arg_val);
                        }
                    }
                }
            }
        }
        replace_from_map(toPropogate);

        // errs() << "Done: constant prop !\n";
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
