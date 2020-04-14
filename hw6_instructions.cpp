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

    std::string getShortValueName(Value * v);
    struct Instructions : public FunctionPass {
        static char ID; // Pass identification, replacement for typeid
        Instructions() : FunctionPass(ID) {}

        bool runOnFunction(Function &F) override {
            bool repeat = true;
            while(repeat){
                map<Value*, int> value2int;
                map<int, Value*> int2value;
                
                for(inst_iterator II = inst_begin(F); II!=inst_end(F); ++II) {
                    Instruction& insn(*II);
                    
                    // Look for insn-defined values and function args
                    for (User::op_iterator OI = insn.op_begin(), OE = insn.op_end(); OI != OE; ++OI)
                    {
                        Value *val = *OI;
                        if (isa<Instruction>(val) || isa<Argument>(val)) {
                            // Val is used by insn
                            if (value2int.find(val) == value2int.end()){
                                value2int.insert(pair<Value*, int>(val,value2int.size()));
                                int2value.insert(pair<int, Value*>(int2value.size(),val));
                            }
                        }
                    }
                }
                map<Instruction*, set<int>> USE;
                map<Instruction*, set<int>> DEF;
                map<Instruction*, set<int>> IN;
                map<Instruction*, set<int>> OUT;
                map<Instruction*, set<int>>::iterator it;
                map<Instruction*, set<int>>::iterator kit;
                map<PHINode*, map<BasicBlock*, set<int>>> PHI_USE;
                map<PHINode*, map<BasicBlock*, set<int>>> PHI_IN;

                for (BasicBlock &BB : F) {

                    for (Instruction &I : BB) {
                        Instruction *pI = &I;
                        Value* p = cast<Value> (pI);
                        //Value* p = cast<Value> &I;

                        set<int> s;
                        if (!isa<BranchInst>(pI) && !isa<ReturnInst>(pI)) s.insert(value2int[p]);
                        DEF.insert({&I, s});
                        IN.insert({&I, set<int>()});
                        OUT.insert({&I, set<int>()});

                        set<int> s2;
                        for (User::op_iterator opnd = I.op_begin(), opE = I.op_end(); opnd != opE; ++opnd) {
                            Value* val = *opnd;
                            if (isa<Instruction>(val) || isa<Argument>(val)) {
                                s2.insert(value2int[val]);
                            }
                        }
                        USE.insert({&I, s2});

                        //handle PHI NODE
                        if (PHINode* phi_insn = dyn_cast<PHINode>(&I)) {
                            map<BasicBlock*, set<int>> temp_use_map;
                            map<BasicBlock*, set<int>> temp_in_map;
                            for (int ind = 0; ind < phi_insn->getNumIncomingValues(); ind++) {
                                set<int> temp_set;
                                Value* val = phi_insn->getIncomingValue(ind);
                                if (isa<Instruction>(val) || isa<Argument>(val)) {
                                    BasicBlock* valBlock = phi_insn->getIncomingBlock(ind);
                                    if(temp_in_map.find(valBlock)==temp_in_map.end()){
                                        temp_in_map.insert({valBlock, set<int>()});
                                    }
                                    if(temp_use_map.find(valBlock)==temp_use_map.end()){
                                        temp_set.insert(value2int[val]);
                                        temp_use_map.insert({valBlock, temp_set});
                                    }
                                    else{
                                        temp_use_map[valBlock].insert(value2int[val]);
                                    }
                                }
                            }
                            PHI_USE.insert({phi_insn, temp_use_map});
                            PHI_IN.insert({phi_insn, temp_in_map});
                        }
                    }

                }
                

                map<Instruction*, vector<Instruction*>> SuccessorMap;
                Instruction *preI = nullptr;
                vector<Instruction*> all_instructions;
                for (BasicBlock &BB : F) {
                    const Instruction *TInst = BB.getTerminator();
                    for (Instruction &I : BB) {
                        Instruction *pI = &I;
                        all_instructions.push_back(pI);
                        if(preI != nullptr){
                            vector<Instruction*> successors;
                            
                            /*if(isa<PHINode>(&*preI)){
                                std::set<int> newUSE;
                                std::set_difference(USE[pI].begin(), USE[pI].end(), DEF[preI].begin(), DEF[preI].end(), std::inserter(newUSE, newUSE.begin()));
                                USE[pI] = newUSE;
                            }*/

                            if(pI == TInst){
                                for (int i = 0, NSucc = TInst->getNumSuccessors(); i < NSucc; i++) {
                                    BasicBlock* succ = TInst->getSuccessor(i);
                                    successors.push_back(&succ->front());
                                }
                                SuccessorMap.insert({pI,successors});
                            }
                            
                            successors.push_back(pI);
                            SuccessorMap.insert({preI,successors});
                        }
                        preI = pI;
                    }
                }

                std::reverse(all_instructions.begin(),all_instructions.end());
                bool exist_update = true;
                int iteration_count = 0;
                while(exist_update){
                    errs() << "backward iteration count: " << iteration_count << "\n";
                    exist_update = false;
                    //for (BasicBlock &BB : F) {
                        //for (Instruction &I : BB) {
                    for(auto &pI: all_instructions){
                            //in[n] = use[n] ∪ (out[n] – def[n])
                            //Instruction *pI = &I;
                            Instruction& I(*pI);
                            if(!isa<PHINode>(&I)){
                                std::set<int> diff;
                                std::set<int> newIN;
                                
                                std::set_difference(OUT[pI].begin(), OUT[pI].end(), DEF[pI].begin(), DEF[pI].end(), std::inserter(diff, diff.begin()));
                                std::set_union(USE[pI].begin(), USE[pI].end(), diff.begin(), diff.end(), std::inserter(newIN, newIN.begin()));
                                
                                if (IN[pI] != newIN){
                                    exist_update = true;
                                }
                                IN[pI] = newIN;
                            }
                            else{
                                PHINode* phi_insn = dyn_cast<PHINode>(&I);
                                for (pair<BasicBlock*, set<int>> temp : PHI_IN[phi_insn]) {
                                    set<int> temp_use = PHI_USE[phi_insn][temp.first];
                                    set<int> temp_in = temp.second;
                                    std::set<int> newIN;
                                    std::set<int> diff;
                                    std::set_difference(OUT[pI].begin(), OUT[pI].end(), DEF[pI].begin(), DEF[pI].end(), std::inserter(diff, diff.begin()));
                                    std::set_union(temp_use.begin(), temp_use.end(), diff.begin(), diff.end(), std::inserter(newIN, newIN.begin()));
                                    if (temp_in != newIN){
                                        exist_update = true;
                                    }
                                    PHI_IN[phi_insn][temp.first] = newIN;
                                }

                            }
                            //out[n] = ∪(s in succ) {in[s]}
                            std::set<int> newOUT;
                            errs() << "Instruction: " << I << " -->" << "\n";
                            for (auto &sI :SuccessorMap[pI]){

                                std::set<int> temp(IN[sI]);
                                if(isa<PHINode>(&*sI)){
                                    PHINode* phi_insn = dyn_cast<PHINode>(&*sI);
                                    temp = PHI_IN[phi_insn][pI->getParent()];
                                }
                                std::set<int> temp2(newOUT);
                                Instruction& I2(*sI);
                                errs() << "successor Instruction: " << I2 << " -->" << "\n";
                                std::set_union(temp.begin(), temp.end(), temp2.begin(), temp2.end(), std::inserter(newOUT, newOUT.begin()));
                            }
                            if (OUT[pI] != newOUT){
                                exist_update = true;
                            }
                            OUT[pI] = newOUT;

                            /*
                            if(DEF.find(&I) != DEF.end()){
                                auto d = DEF.find(&I);
                                errs() << " DEF: {"; 
                                for (set<int>::iterator sit = d->second.begin(); sit != d->second.end(); sit++) {
                                    errs() << getShortValueName(int2value[*sit]) << " ";
                                }
                                errs() << "}" << '\n';
                            }
                            if(USE.find(&I) != USE.end()){
                                auto d = USE.find(&I);
                                errs() << " USE: {"; 
                                for (set<int>::iterator sit = d->second.begin(); sit != d->second.end(); sit++) {
                                    errs() << getShortValueName(int2value[*sit]) << " ";
                                }
                                errs() << "}" << '\n';
                            }
                            if(IN.find(&I) != IN.end()){
                                auto d = IN.find(&I);
                                errs() << " liveness IN: {"; 
                                for (set<int>::iterator sit = d->second.begin(); sit != d->second.end(); sit++) {
                                    errs() << getShortValueName(int2value[*sit]) << " ";
                                }
                                errs() << "}" << '\n';
                            }
                            if(OUT.find(&I) != OUT.end()){
                                auto d = OUT.find(&I);
                                errs() << " liveness OUT: {"; 
                                for (set<int>::iterator sit = d->second.begin(); sit != d->second.end(); sit++) {
                                    errs() << getShortValueName(int2value[*sit]) << " ";
                                }
                                errs() << "}" << '\n';
                            }*/
                        //}
                    }
                    iteration_count++;

                }

                errs() <<"\n";
                errs() <<"\n";
                errs() <<"\n";
                errs() <<"\n";
                bool somethingRemoved = false;
                for (BasicBlock &BB : F) {

                    Instruction *instIt;
                    bool removalNeeded = false;
                    SmallVector<Instruction*, 128> removeInst;

                    errs() << "\nNEXT BASICBLOCK\n";

                    for (Instruction &I : BB) {
                        errs() << "Instruction: " << I << " -->" << "\n";

                        std::set<std::string> defSet;
                        std::set<std::string> outSet;
                        if(DEF.find(&I) != DEF.end()){
                            auto d = DEF.find(&I);
                            errs() << " DEF: {"; 
                            for (set<int>::iterator sit = d->second.begin(); sit != d->second.end(); sit++) {
                                errs() << getShortValueName(int2value[*sit]) << " ";
                                string valueName = getShortValueName(int2value[*sit]);
                                defSet.insert(valueName);
                            }
                            errs() << "}" << '\n';
                        }
                        if(USE.find(&I) != USE.end()){
                            if(isa<PHINode>(&I)){
                                PHINode* phi_insn = dyn_cast<PHINode>(&I);
                                for (pair<BasicBlock*, set<int>> temp : PHI_USE[phi_insn]) {
                                    set<int> temp_use = PHI_USE[phi_insn][temp.first];
                                    errs() << " USE: {"; 
                                    for (set<int>::iterator sit = temp_use.begin(); sit != temp_use.end(); sit++) {
                                        errs() << getShortValueName(int2value[*sit]) << " ";
                                    }
                                    errs() << "}" << '\n';
                                }

                            }
                            else{
                                auto d = USE.find(&I);
                                errs() << " USE: {"; 
                                for (set<int>::iterator sit = d->second.begin(); sit != d->second.end(); sit++) {
                                    errs() << getShortValueName(int2value[*sit]) << " ";
                                }
                                errs() << "}" << '\n';
                            }
                        }
                        if(IN.find(&I) != IN.end()){
                            if(isa<PHINode>(&I)){
                                PHINode* phi_insn = dyn_cast<PHINode>(&I);
                                for (pair<BasicBlock*, set<int>> temp : PHI_IN[phi_insn]) {
                                    set<int> temp_in = PHI_IN[phi_insn][temp.first];
                                    errs() << " IN: {"; 
                                    for (set<int>::iterator sit = temp_in.begin(); sit != temp_in.end(); sit++) {
                                        errs() << getShortValueName(int2value[*sit]) << " ";
                                    }
                                    errs() << "}" << '\n';
                                }

                            }
                            else{
                                auto d = IN.find(&I);
                                errs() << " liveness IN: {"; 
                                for (set<int>::iterator sit = d->second.begin(); sit != d->second.end(); sit++) {
                                    errs() << getShortValueName(int2value[*sit]) << " ";
                                }
                                errs() << "}" << '\n';
                            }
                            
                        }
                        if(OUT.find(&I) != OUT.end()){
                            auto d = OUT.find(&I);
                            errs() << " liveness OUT: {"; 
                            for (set<int>::iterator sit = d->second.begin(); sit != d->second.end(); sit++) {
                                errs() << getShortValueName(int2value[*sit]) << " ";
                                string valueName = getShortValueName(int2value[*sit]);
                                outSet.insert(valueName);
                            }
                            errs() << "}" << '\n';              
                        }

                        errs() << "----printing sets------\n";
                        errs() << "DEFset:\n";
                        errs() << "[ ";
                        for (auto it=defSet.begin(); it != defSet.end(); ++it){
                            errs() << *it;
                        }
                        errs() << " ]\n";
                        
                        errs() << "OUTset:\n";
                        errs() << "[ ";
                        for (auto it=outSet.begin(); it != outSet.end(); ++it){
                            errs() << *it;
                        }
                        errs() << " ]\n";
                        errs() << "end of my stuff----------------\n\n";
                        if(!defSet.empty()){
                            if(defSet != outSet){
                                removalNeeded = true;
                                removeInst.push_back(&I);
                            }
                        }
                    }
                    
                    if(removalNeeded){
                        for (Instruction *&I : removeInst){
                            errs() << "ALERT: Removing " << I << "\n";
                            I->dropAllReferences();
                            I->removeFromParent();
                        }
                        removalNeeded = false;
                        somethingRemoved = true;
                    }
                }
                repeat = somethingRemoved;
                
            }
            return false;
        }
    };
    std::string getShortValueName(Value * v) {
        if (v->getName().str().length() > 0) {
            return "%" + v->getName().str();
        }
        else if (isa<Instruction>(v)) {
            std::string s = "";
            raw_string_ostream * strm = new raw_string_ostream(s);
            v->print(*strm);
            std::string inst = strm->str();
            size_t idx1 = inst.find("%");
            size_t idx2 = inst.find(" ",idx1);
            if (idx1 != std::string::npos && idx2 != std::string::npos) {
                return inst.substr(idx1,idx2-idx1);
            }
            else {
                return "\"" + inst + "\"";
            }
        }
        else if (ConstantInt * cint = dyn_cast<ConstantInt>(v)) {
            std::string s = "";
            raw_string_ostream * strm = new raw_string_ostream(s);
            cint->getValue().print(*strm,true);
            return strm->str();
        }
        else {
            std::string s = "";
            raw_string_ostream * strm = new raw_string_ostream(s);
            v->print(*strm);
            std::string inst = strm->str();
            return "\"" + inst + "\"";
        }
    }
}

char Instructions::ID = 0;
static RegisterPass<Instructions> X("einst", "My Instruction Set Pass");