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

#include <set>
#include <unordered_set>
#include <vector>
#include <map>
#include <unordered_map>
using namespace llvm;
 

namespace {
struct CAT : public FunctionPass {
    static char ID; 
    // map(caller_name, (callee_name, count))
    // std::map<std::string, std::map<std::string, int>> func_count;
    std::map<std::string, int> func_count;

    std::set<std::string> func_set = {
        "CAT_new",
        "CAT_add",
        "CAT_sub",
        "CAT_get",
        "CAT_set"
    };
    
    std::unordered_map<Function *, std::string> fptr2name;
    
    CAT() : FunctionPass(ID) {}

    // This function is invoked once at the initialization phase of the compiler
    // The LLVM IR of functions isn't ready at this point
    bool doInitialization (Module &M) override {
        // errs() << "Hello LLVM World at \"doInitialization\"\n" ;
        for (const std::string & str : func_set) {
            Function * fptr = M.getFunction(StringRef(str));
            fptr2name[fptr] = str;
        }
        return false;
    }

    // This function is invoked once per function compiled
    // The LLVM IR of the input functions is ready and it can be analyzed and/or transformed
    bool runOnFunction (Function &F) override {
      // errs() << "Hello LLVM World at \"runOnFunction\"\n" ;
        std::string caller_name = F.getName().str();
        for (auto& inst: llvm::instructions(F)) {
        
            if (isa<CallInst>(&inst)){
                // errs() << inst;
                CallInst *callInst = cast<CallInst>(&inst);
                std::string callee_name = callInst->getCalledFunction()->getName().str();
                // errs() << callee_name << " called in " << caller_name << '\n';
                
                // if (func_set.find(callee_name) != func_set.end()) {
                //     // found callee function
                //     // std::map<std::string, int> * CAT_map_ptr;
                //     if (func_count.find(caller_name) == func_count.end()) {
                //         func_count[caller_name] = std::map<std::string, int>();
                //     } 

                //     if (func_count[caller_name].find(callee_name) == func_count[caller_name].end()){
                //         func_count[caller_name][callee_name] = 0;
                //     }

                //     func_count[caller_name][callee_name] += 1;
                // }
                if (func_set.find(callee_name) != func_set.end()) {
                    // found callee function
                    // std::map<std::string, int> * CAT_map_ptr;

                    if (func_count.find(callee_name) == func_count.end()) {
                        func_count[callee_name] = 0;
                    }

                    func_count[callee_name] = func_count[callee_name] + 1;
                }
            }
        }

        // for (const auto& kv : func_count) {
        //     errs() << "H0: \"" << caller_name << "\": " << kv.first << ": " << kv.second << "\n";
        // }

        func_count.clear();

        unsigned NumInstrs = F.getInstructionCount();

        llvm::BitVector GEN(NumInstrs, 0);
        std::vector<llvm::BitVector> KILL (NumInstrs, llvm::BitVector(NumInstrs, 0));
        std::unordered_map<void *, llvm::BitVector> instr2bitmap;
        
        std::vector<llvm::Instruction *> instr_vec (NumInstrs, NULL);

        unsigned i = 0;
        for (auto& inst: llvm::instructions(F)) {
            instr_vec[i] = &inst;
            if (isa<CallInst>(&inst)){
                CallInst * call_instr = cast<CallInst>(&inst);
                Function * callee_ptr = call_instr->getCalledFunction();

                if (fptr2name.find(callee_ptr) != fptr2name.end()) {
                    // find one call_instr that calls one of CAT functions  
                    std::string callee_name = fptr2name[callee_ptr];
                    if (callee_name != "CAT_get") {
                        
                        GEN.set(i);
                        
                        if (callee_name == "CAT_new") {
                            instr2bitmap[call_instr] = llvm::BitVector(NumInstrs, 0);
                            instr2bitmap[call_instr].set(i);
                        } else {
                            // get first operand if CAT_set, CAT_add, CAT_sub
                            void * arg0 = call_instr->getArgOperand(0);
                            instr2bitmap[arg0].set(i);
                        }
                    }
                }
            }
            i++;
        }

        for (i = 0; i < NumInstrs; i++) {
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

                KILL[i].flip(i);
            }
        }

        H1_output(
            caller_name,  /* function name*/
            GEN,
            KILL,
            instr_vec
        );

        return false;
    }

    // We don't modify the program, so we preserve all analyses.
    // The LLVM IR of functions isn't ready at this point
    void getAnalysisUsage(AnalysisUsage &AU) const override {
        // errs() << "Hello LLVM World at \"getAnalysisUsage\"\n" ;
        AU.setPreservesAll();
    }


    void H1_output(
        std::string & func_name, 
        llvm::BitVector & GEN,
        std::vector<llvm::BitVector> & KILL,
        std::vector<llvm::Instruction *> & instr_vec
    ) {
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
