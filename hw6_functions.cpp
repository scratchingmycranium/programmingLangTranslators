// Homework 6 

#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/ADT/StringMap.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/ADT/ilist_node.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/ADT/iterator_range.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/GlobalObject.h"
#include "llvm/IR/GlobalValue.h"
#include "llvm/IR/OperandTraits.h"
#include "llvm/IR/SymbolTableListTraits.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/Use.h"
#include "llvm/IR/Value.h"
#include "llvm/IR/ValueMap.h"
#include "llvm/IR/ValueSymbolTable.h"
#include <iostream>
#include <set>
#include <map>
#include <iterator>

using namespace llvm;
using namespace std;

namespace {

    std::string variable_to_string(Value * v);
    struct Functions : public ModulePass {
        static char ID; // Pass identification, replacement for typeid
        Functions() : ModulePass(ID) {}

        virtual bool runOnModule(Module &M) override {

            std::set<string> functionNames;
            Function *funcIt;
            bool done = false;

            while(!done){
                for (auto &F: M) {
                    functionNames.insert(F.getName());
                }

                errs() << "-------FUNCTION LIST BEFORE---------\n";
                std::set<string>::iterator itr;
                for (itr = functionNames.begin(); itr != functionNames.end(); ++itr){
                    errs() << *itr << "\n";
                }

                for (auto &F: M) {
                    errs() << "--------ENTERING FUNCTION " << F.getName() <<"----------\n";
                    for (Function::iterator BB = F.begin(); BB != F.end(); BB++) {
                        BasicBlock &bb = *BB;
                        errs() << "\nBasic Block: " << bb << "\n";
                        for (BasicBlock::iterator I = bb.begin(); I != bb.end(); I++) {
                            errs() << "Instruction: " << *I << "\n";
                            if (CallInst *CI = dyn_cast<CallInst>(I)) {
                                Function *func = CI->getCalledFunction();
                                errs()<< "\n";
                                errs() << "Instruction: " << func->getName() << " IS A CALL INSTRUCTION\n";
                                errs()<< "\n";
                                functionNames.erase(func->getName());
                            }
                        }
                    }                
                }
                functionNames.erase("main");
                if(functionNames.size()!=0){
                    errs() << "\n-------FUNCTION LIST AFTER---------\n";
                    std::set<string>::iterator itr2;
                    for (itr2 = functionNames.begin(); itr2 != functionNames.end(); ++itr2){
                        errs() << *itr2 << "\n";
                    }
                    errs()<< "\nBEFORE ERASING FROM PARENT\n";              
                    for (auto &F: M) {
                        const bool is_in = functionNames.find(F.getName()) != functionNames.end();
                        if(is_in){
                            funcIt=&F;
                            F.deleteBody();
                        }
                    }

                    funcIt->removeFromParent();
                    errs()<< "\n-------------------AFTER DELETING FUNCTION----------------\n";
                    for (auto &F: M) {
                        errs() << "--------ENTERING FUNCTION " << F.getName() <<"----------\n";
                        for (Function::iterator BB = F.begin(); BB != F.end(); BB++) {
                            BasicBlock &bb = *BB;
                            errs() << "\nBasic Block: " << bb << "\n";
                        }
                    }
                    functionNames.clear();
                    errs() << "--------------------END OF LOOP-----------------------\n\n\n";
                }else{
                    done = true;
                }
                
            }

        }  
    };
}

char Functions::ID = 0;
static RegisterPass<Functions> X("efunc", "My Function Set Pass");