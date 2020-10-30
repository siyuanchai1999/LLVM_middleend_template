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

    std::unordered_set<Function *> user_functions;
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

    // deadcode elimination
    std::unordered_map<llvm::Instruction *, std::set<llvm::Value *>> live_GEN_INST, live_KILL_INST;
    std::unordered_map<llvm::Instruction *, std::set<llvm::Value *>> live_IN_INST, live_OUT_INST;
    std::unordered_map<llvm::BasicBlock *, std::set<llvm::Value *>> live_GEN_BB, live_KILL_BB;
    std::unordered_map<llvm::BasicBlock *, std::set<llvm::Value *>> live_IN_BB, live_OUT_BB;
    std::set<llvm::Value *> referenced_var;

    CAT() : FunctionPass(ID) {}

    // This function is invoked once at the initialization phase of the compiler
    // The LLVM IR of functions isn't ready at this point
    bool doInitialization (Module &M) override {
        // errs() << "Hello LLVM World at \"doInitialization\"\n" ;
        currentModule = &M;
        errs() << "available functions: \n";
        for (Function & F : M){
            if(!F.isDeclaration()){
                user_functions.insert(&F);
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
      // errs() << "Hello LLVM World at \"runOnFunction\"\n" ;
        phi_node_new2set(F);
        live_analysis_wrapper(F);
        std::string caller_name = F.getName().str();
        H0_init();
        H0_function_count(F);
        // H0_output(caller_name);
        
        H1_init(F);
        H1_GEN_KILL(F);
        // H1_output(caller_name);

        H2_init(F);
        H2_IN_OUT(F);
        instruction_IN_OUT(F);
        // H2_output(caller_name,F);

        build_store_table(F);
        find_escaped(F);

        
        constant_folding(F);
        constant_propagation(F);

        return false;
    }

    // We don't modify the program, so we preserve all analyses.
    // The LLVM IR of functions isn't ready at this point
    void getAnalysisUsage(AnalysisUsage &AU) const override {
        // errs() << "Hello LLVM World at \"getAnalysisUsage\"\n" ;
        AU.setPreservesAll();
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
        for (llvm::BasicBlock &bb : F){
            //probably number of instr in a b

            BB_GEN[&bb] = llvm::BitVector(NumInstr,0);
            BB_KILL[&bb] = llvm::BitVector(NumInstr, 0);
            BB_IN[&bb] = BitVector(NumInstr, 0);
            BB_OUT[&bb] = BitVector(NumInstr, 0);

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
        // errs() << "counting for " << *phi << '\n';
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
        llvm::CallInst * CAT_new_old,
        llvm::CallInst * CAT_new_replace
    ) {
        IRBuilder<> builder(CAT_new_old);

        Value * val = CAT_new_old->getArgOperand(0);
        
        ArrayRef<Value *> arg_arr_ref = ArrayRef<Value *>{CAT_new_replace, val};

        Value * added_set_instr = builder.CreateCall(CAT_set_ptr, arg_arr_ref);
        
        // replacement
        replace_instr_val(CAT_new_old, CAT_new_replace);
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

        CallInst * CAT_new_replace = NULL;

        // Need fix if we add dummy block for argument???
        
        // find first instruction in the first basic block in the set of Cat_new to be merged
        for(Instruction & inst: F.getBasicBlockList().front()){
            if(IN_SET(nodes_set, &inst)){
                CAT_new_replace = cast<CallInst> (&inst);
                break;
            }
        }
        
        // if there's no such CAT_new, create a dummy one
        if (CAT_new_replace == NULL) CAT_new_replace = build_CAT_new_Head(F);

        for (uint32_t i = 0; i < nodes.size(); i++) {
            CallInst * CAT_new_old = cast<CallInst>(nodes[i]);

            if (CAT_new_old != CAT_new_replace){
                CAT_new_to_CAT_set(
                    CAT_new_old,
                    CAT_new_replace
                );
            }
            
        }

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
                        // errs() << "analyzing " << *phi << '\n';
                        int cnt = count_CAT_new_under_Phi(phi, visited_phi);
                        // errs() << "get cnt = " << cnt << '\n';
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

        std::vector<std::vector<llvm::Value *>> CC;
        // std::vector<std::set<llvm::Value *>> CC_edge;
        connected_components(
            graph,
            CC
            // CC_edge
        );

        // print_CC(CC);
        // print_phi_info(visited_phi);

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


        if (!isa<CallInst>(arg)){
            return false;
            
        }

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
                            // errs() << *call_instr << " replaced with " << arg_val <<'\n';
                            toPropogate[call_instr] = build_constint(arg_val);
                        }
                    }
                }
            }
        }
        replace_from_map(toPropogate);
    }

    void live_analysis_init(Function & F){
        // std::unordered_map<llvm::Instruction *, std::set<llvm::Instruction *>> live_GEN_INST, live_KILL_INST;
        // std::unordered_map<llvm::Instruction *, std::set<llvm::Instruction *>> live_IN_INST, live_OUT_INST;
        // std::unordered_map<llvm::BasicBlock *, std::set<llvm::Instruction *>> live_GEN_BB, live_KILL_BB;
        // std::unordered_map<llvm::BasicBlock *, std::set<llvm::Instruction *>> live_IN_BB, live_OUT_BB;
        unsigned NumInstrs = F.getInstructionCount();
        for (BasicBlock &bb : F){
            live_GEN_BB[&bb] = std::set<llvm::Value *>();
            live_KILL_BB[&bb] = std::set<llvm::Value *>();

            live_IN_BB[&bb] = std::set<llvm::Value *>();
            live_OUT_BB[&bb] = std::set<llvm::Value *>();

            for(Instruction &inst : bb){
                live_GEN_INST[&inst] = std::set<llvm::Value *>();
                live_KILL_INST[&inst] = std::set<llvm::Value *>();

                live_IN_INST[&inst] = std::set<llvm::Value *>();
                live_OUT_INST[&inst] = std::set<llvm::Value *>();
            }
        }
    }
    
        template<class T>
    void set_union_wrap(std::set<T> & srcA, std::set<T> & srcB, std::set<T> & target){
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
    void set_intersection_wrap(std::set<T> & srcA, std::set<T> & srcB, std::set<T> & target){
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
    void set_diff_wrap(std::set<T> & srcA, std::set<T> & srcB, std::set<T> & target){
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

    void live_analysis_GENKILL_INST(Function & F){
        unsigned NumInstrs = F.getInstructionCount();

        unsigned i = 0;
        for (BasicBlock &bb : F){
            for(Instruction &inst : bb){
                Function * fptr = get_callee_ptr(&inst);
                if(fptr){
                    CallInst * call_instr = cast<CallInst>(&inst);
                    if (IS_CAT_OP(fptr)){
                        // errs() << "analyzing " << *call_instr << '\n';
                        if (IS_CAT_new(fptr)){
                            // only define but not killed
                            live_KILL_INST[&inst].insert(&inst);
                            
                        } else if (IS_CAT_get(fptr)) {
                            // only use variable, CAT_get
                            Value * arg0 = call_instr->getArgOperand(0);
                            live_GEN_INST[&inst].insert(arg0);

                            referenced_var.insert(arg0);

                            // also define itself for printf usage
                            // live_KILL_INST[&inst].insert(&inst);
                        } else if (IS_CAT_set(fptr)) {
                            // CAT_set, define and usearg0
                            
                            // Instruction * arg0 = cast<Instruction>(call_instr->getArgOperand(0));
                            Value * arg0 = call_instr->getArgOperand(0);

                            live_KILL_INST[&inst].insert(arg0);

                            referenced_var.insert(arg0);
                        } else {
                            // CAT_add, CAT_sub
                            // define arg0
                            // use arg1, arg2

                            Value * arg0 = call_instr->getArgOperand(0);
                            Value * arg1 = call_instr->getArgOperand(1);
                            Value * arg2 = call_instr->getArgOperand(2);

                            live_KILL_INST[&inst].insert(arg0);
                            live_GEN_INST[&inst].insert(arg1);
                            live_GEN_INST[&inst].insert(arg2);

                            referenced_var.insert(arg0);
                            referenced_var.insert(arg1);
                            referenced_var.insert(arg2);
                        }   

                    } else if (IN_SET(user_functions, fptr)){
                        // Other function? 
                        uint32_t arg_cnt = call_instr->getNumArgOperands();
                        for(uint32_t i = 0; i < arg_cnt; i++){
                            Value * arg = call_instr->getArgOperand(i);
                            // if (isa<Instruction>(arg)){
                            //     // Possibly use and define at the same time
                            //     Instruction * arg_inst = cast<Instruction>(arg);

                            //     live_KILL_INST[&inst].insert(arg_inst);
                            //     live_GEN_INST[&inst].insert(arg_inst);
                            // } else {
                            //     // argument? 
                            //     // constant??
                            // }
                        
                            live_KILL_INST[&inst].insert(arg);
                            live_GEN_INST[&inst].insert(arg);

                            referenced_var.insert(arg);
                        }
                    } else {
                        // non user function, eg. printf only use
                        // uint32_t arg_cnt = call_instr->getNumArgOperands();
                        // for(uint32_t i = 0; i < arg_cnt; i++){
                        //     Value * arg = call_instr->getArgOperand(i);
                        //     // if (isa<Instruction>(arg)){
                        //     //     // Possibly use and define at the same time
                        //     //     Instruction * arg_inst = cast<Instruction>(arg);

                        //     //     live_KILL_INST[&inst].insert(arg_inst);
                        //     //     live_GEN_INST[&inst].insert(arg_inst);
                        //     // } else {
                        //     //     // argument? 
                        //     //     // constant??
                        //     // }
                        
                        //     live_GEN_INST[&inst].insert(arg);
                        // }
                    
                    }
                }
                i++;
            }
        }

        // errs() << "live_analysis_GENKILL_INST done \n";
        // errs() << "printing reference variables\n";
        // print_set_reference(referenced_var);
    }

    void live_analysis_GENKILL_BB(Function & F){
        unsigned NumInstrs = F.getInstructionCount();

        unsigned i = 0;
        for (BasicBlock &bb : F){
            for(Instruction &inst : bb){
                set_union_wrap(
                    live_GEN_INST[&inst],  /* src A*/
                    live_GEN_BB[&bb],   /* src B*/
                    live_GEN_BB[&bb]    /* target*/
                );

                set_union_wrap(
                    live_KILL_INST[&inst],  /* src A*/
                    live_KILL_BB[&bb],   /* src B*/
                    live_KILL_BB[&bb]    /* target*/
                );
            }
        }
    }


    void live_analysis_INOUT_BB(Function & F){
        bool changed;
        do{
            changed = false;
            // for(BasicBlock &bb : F){
            for(auto it = F.getBasicBlockList().rbegin(); it != F.getBasicBlockList().rend(); it++ ){ 
                BasicBlock * bb_ptr = &(*it);
                for(BasicBlock * succ : successors(bb_ptr)){
                    set_union_wrap(
                        live_IN_BB[succ],  /* src A*/
                        live_OUT_BB[bb_ptr],   /* src B*/
                        live_OUT_BB[bb_ptr]    /* target*/
                    );
                }

                std::set<Value*> IN_TEMP;
                set_diff_wrap(
                    live_OUT_BB[bb_ptr],  /* src A*/
                    live_KILL_BB[bb_ptr],   /* src B*/
                    IN_TEMP    /* target*/
                );
                
                set_union_wrap(
                    live_GEN_BB[bb_ptr],  /* src A*/
                    IN_TEMP,   /* src B*/
                    IN_TEMP    /* target*/
                );
                

                if (!changed) changed = (IN_TEMP != live_IN_BB[bb_ptr]);
                live_IN_BB[bb_ptr] = IN_TEMP;
            }

        }while(changed);

    }

    void live_analysis_INOUT_INST(Function & F){
        unsigned NumInstrs = F.getInstructionCount();

        for (BasicBlock &bb : F){
            // errs() << "live GEN of BB: " << bb << '\n';
            // print_set_reference(live_GEN_BB[&bb]);

            // errs() << "live KILL of BB: " << bb << '\n';
            // print_set_reference(live_KILL_BB[&bb]);

            // errs() << "live IN of BB: " << bb << '\n';
            // print_set_reference(live_IN_BB[&bb]);
            
            // errs() << "live OUT of BB: " << bb << '\n';
            // print_set_reference(live_OUT_BB[&bb]);
            // errs() << '\n';

            std::set<Value* > local_INSTR_IN = live_OUT_BB[&bb];
            std::set<Value* > local_INSTR_OUT = live_OUT_BB[&bb];
            
            // travel reversely as we have backward analysis

            /*
             * OUT[i] = IN[i + 1]
             * IN[i] = GEN[i] U (OUT[i] - KILL[i])
            */
            for (auto it = bb.rbegin(); it != bb.rend(); it++){
                Instruction * inst_ptr = &(*it);
                local_INSTR_OUT = local_INSTR_IN;

                set_diff_wrap(
                    local_INSTR_OUT,  /* src A*/
                    live_KILL_INST[inst_ptr],   /* src B*/
                    local_INSTR_IN    /* target*/
                );

                set_union_wrap(
                    local_INSTR_IN,  /* src A*/
                    live_GEN_INST[inst_ptr],   /* src B*/
                    local_INSTR_IN    /* target*/
                );   

                live_IN_INST[inst_ptr] = local_INSTR_IN;
                live_OUT_INST[inst_ptr] = local_INSTR_OUT;

                // errs() << "live IN of instruction: " << *inst_ptr << '\n';
                // print_set_reference(live_IN_INST[inst_ptr]);

                // errs() << "live OUT of instruction: " << *inst_ptr << "\n";
                // print_set_reference(live_OUT_INST[inst_ptr]);
                // errs()   << "\n";
            }
            
        }
        
    }

    void eliminating(Function & F){
        std::vector<Instruction*> to_eliminate;

        for (BasicBlock &bb : F){
            for(Instruction &inst : bb){
                Function * fptr = get_callee_ptr(&inst);
                if(fptr && IS_CAT_OP(fptr)){
                    if(IS_CAT_get(fptr)){

                    } else if (IS_CAT_new(fptr)){
                        // if (!IN_SET(referenced_var, &inst)){
                        //     errs() << "eliminating " << inst << '\n';

                        //     to_eliminate.push_back(&inst);
                        // }

                    } else {
                        std::set<Value *> intersect;
                        set_intersection_wrap(
                            live_OUT_INST[&inst],         /* src A*/
                            live_KILL_INST[&inst],   /* src B*/
                            intersect               /* target*/
                        );

                        if(intersect.size() == 0) {
                            errs() << "eliminating " << inst << '\n';

                            to_eliminate.push_back(&inst);

                        }
                        // errs() << "live OUT of instruction: " << inst << '\n';
                        // print_set_reference(live_OUT_INST[&inst]);

                        // errs() << "live KILL of instruction: " << inst << "\n";
                        // print_set_reference(live_KILL_INST[&inst]);
                        // errs()   << "\n";
                        /**
                         * Can be eliminated if OUT[i] has no intersection with KILL[i]
                         * */
                    }
                }
            }
        }

        for (uint32_t i = 0; i < to_eliminate.size(); i++) {
            to_eliminate[i]->eraseFromParent();
        }

    }

    void live_analysis_wrapper(Function &F){
        live_analysis_init(F);
        live_analysis_GENKILL_INST(F);
        live_analysis_GENKILL_BB(F);
        live_analysis_INOUT_BB(F);
        live_analysis_INOUT_INST(F);
        eliminating(F);
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
    template<class T>
    void print_set_reference(std::set<T> & src) {
        for (auto & data_ptr : src ){
            errs() << *data_ptr << '\n';
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
