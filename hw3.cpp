//Adapted from: Hello.cpp - Example code from "Writing an LLVM Pass"
#include "llvm/ADT/Statistic.h"
#include "llvm/IR/Function.h"
#include "llvm/Pass.h"
#include "llvm/IR/CallSite.h"
#include "llvm/Support/raw_ostream.h"
#include <iostream>
#include "llvm/IR/Module.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Argument.h"
#include "llvm/IR/IRBuilder.h"
using namespace llvm;

#define DEBUG_TYPE "hw3"

STATISTIC(Hw3Counter, "Counts number of functions greeted");

namespace {
  // Hw3 - The first implementation, without getAnalysisUsage.
  struct Hw3 : public FunctionPass {
    static char ID; // Pass identification, replacement for typeid
    Hw3() : FunctionPass(ID) {}

    bool runOnFunction(Function &F) override {
     
      ++Hw3Counter;
      errs().write_escaped(F.getName()) << " ";

      if(F.isVarArg()){
	      errs().write_escaped( "arguments= * ");
      }else if(!F.arg_empty()){
        errs().write_escaped( "arguments=");
        errs().write_escaped(std::to_string(F.arg_size())) << " ";
      }else{
	      errs().write_escaped( "arguments=0 ");
      }
 

      int callCounter = 0; 
      for (Function &Fun : F.getParent()->getFunctionList()){
        for(BasicBlock &block: Fun){
          for(Instruction &ins: block){
          if (CallInst* callInst = dyn_cast<CallInst>(&ins)) {
            if (callInst->getCalledFunction()->getName()  == Fun.getName()){
            }else{
            }
          }

          
          }

                for(Instruction &ins: block){
                CallSite cs(&ins);
                if(!cs.getInstruction()){
                    continue;
                }
                Value *called = cs.getCalledValue()->stripPointerCasts();
                if(Function* f = dyn_cast<Function>(called)){
                  if(f->getName() == F.getName() ){
                      ++callCounter;

                  }
                }
            }


        }
       }
      errs().write_escaped("callsites=");
      errs().write_escaped(std::to_string(callCounter)) << " ";
      errs().write_escaped("basicblocks=");
      errs().write_escaped(std::to_string((int) F.getBasicBlockList().size())) << " ";

      if(!(F.getInstructionCount() <= 0)){
        errs().write_escaped("instructions=");
        errs().write_escaped(std::to_string(F.getInstructionCount()));
      }
      errs().write_escaped("")<< "\n";
     

      return false;
    }
  };
}

char Hw3::ID = 0;
static RegisterPass<Hw3> X("hw3", "Hw3 Pass");

namespace {
  // Hw32 - The second implementation with getAnalysisUsage implemented.
  struct Hw32 : public FunctionPass {
    static char ID; // Pass identification, replacement for typeid
    Hw32() : FunctionPass(ID) {}

    bool runOnFunction(Function &F) override {
      ++Hw3Counter;
      errs() << "Hw3: ";
      errs().write_escaped(F.getName()) << '\n';
      return false;
    }

    // We don't modify the program, so we preserve all analyses.
    void getAnalysisUsage(AnalysisUsage &AU) const override {
      AU.setPreservesAll();
    }
  };
}

char Hw32::ID = 0;
static RegisterPass<Hw32>
Y("hw32", "Hw3 Pass (with getAnalysisUsage implemented)");