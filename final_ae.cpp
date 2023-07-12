#include<map>
#include<llvm/Pass.h>
#include "llvm/IR/BasicBlock.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/Function.h"
#include "llvm/Analysis/CallGraphSCCPass.h"
#include<set>
#include<iterator>
#include "llvm/IR/InstIterator.h"
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/ADT/BitVector.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/IRBuilder.h"
#include<bits/stdc++.h>
#define DEBUG_TYPE "opCounter"
using namespace llvm;
using namespace std;


class Exp
{
	public:
		 Value* op1;
		 Value* op2;
		 Value* dest;
		 unsigned opcode;
		 int fun_or_op;
		 
		 vector<Value*> arg;
		 int argc;
		 CallInst* inst;
		 Function *F;
		 
		 Exp(Value* v1,Value* v2,unsigned code,Value *v)
		 {
		   op1=v1;
		   op2=v2;
		   opcode=code;
		   dest = v;
		   fun_or_op = 0;
		 }
		 Exp(CallInst* call_inst)
		 {
		   
		   F = call_inst->getCalledFunction();
		   argc=F->arg_size();
		   arg.clear();
		   for(int i =0;i<argc;i++)
		   {
		     arg.push_back(F->getArg(i));
		   }
		   fun_or_op = 1;
		   inst = call_inst;
		  }
		 void print()
		 {
		 errs() << opcode <<"   "<<op1->getName()<<"  "<<op2->getName()<<"\n";
		 }
};


bool isSame(Exp *exp1,Exp *exp2);
int getIndex(Instruction *I);
void compute_USE(BasicBlock *bb);
void compute_DEF(BasicBlock *bb);
BitVector AND(BitVector A,BitVector B);
BitVector OR(BitVector A,BitVector B);
BitVector NEG(BitVector A);
bool isVectorsSame(BitVector A,BitVector B);
void dfs(BasicBlock* bb,int *change);
int isUnique(Exp *exp);
void initialize_IN_OUT(Function &F);
void compute_INOUT(Function &F);
void printt(BitVector A);

map<BasicBlock*,vector<Instruction*>> IN,OUT,V_USE,V_DEF;
map<BasicBlock*,BitVector> IN_BV,OUT_BV,V_USE_BV,V_DEF_BV;
map<Exp*,unsigned int> Ins_to_ind;
map<unsigned int,Exp*> Ind_to_ins;
map<unsigned int,unsigned int> Ins_to_freq;
map<BasicBlock*,int> visited;

int exp_count;
int lval;
int end_pass;
int fun_count;

int getIndex(Instruction *I)
{
	Exp *exp1;
	if(CallInst* call_inst = dyn_cast<CallInst>(&*I))
		exp1 = new Exp(call_inst);
	else
		exp1 = new Exp(I->getOperand(0),I->getOperand(1),I->getOpcode(),&*I);
	for(int i = 0;i<exp_count;i++)
	{
		Exp *exp2 = Ind_to_ins[i];
		if(isSame(exp1,exp2))
			return i;
	}
	return -1;
}
int compute_USE_call(BasicBlock *bb,CallInst *callInst1)
{
	int flag = 1;
	Function *calledFunction = callInst1->getCalledFunction();
	for (unsigned i = 0; i < calledFunction->arg_size(); i++) {
		    Value *v  = callInst1->getArgOperand(i);
		    Instruction *ins=dyn_cast<Instruction>(v);
		  if(ins == NULL)
		  	continue;
		  if(ins->getParent()==callInst1->getParent() && ins->getOpcode()!=Instruction::PHI)
		  {
		  	flag = 0;
		  	break;
		  }
	}
	return flag;
}
void compute_USE(BasicBlock *bb)
{
  BitVector bv(exp_count,false);
  errs() << "--USE of the BB == "<< bb->getName()<<"\n";
  for(BasicBlock::iterator I = bb->begin(), E = bb->end(); I != E; ++I)
  {
     Instruction *k=dyn_cast<Instruction>(I);
     if(!(!(k->getOpcode()==Instruction::PHI) && (k->isBinaryOp() || Instruction::isCast(k->getOpcode()) || isa<CallInst>(&*k))))
     	continue;
     	
     int flag = 1;
     if(CallInst* call_inst = dyn_cast<CallInst>(&*I))
     {
     	flag = compute_USE_call(bb,call_inst);
     }
     
     else
     {
	     for (Use &U : k->operands())
	     {
		  Value *v = U.get();
		  Instruction *ins=dyn_cast<Instruction>(v);
		  if(ins == NULL)
		  	continue;
		  if(ins->getParent()==k->getParent() && ins->getOpcode()!=Instruction::PHI)
		  {
		  	flag = 0;
		  	break;
		  }
	     }
     }
     if(flag==1)
     {
     	int ind = getIndex(k);
       errs()<<"\n	Instruction -- Ind -- "<<ind<<"---"<<*k<<"\n";
       bv.set(ind);
       V_USE[bb].push_back(k);
     }
     
   }
   V_USE_BV[bb] = bv;
}
     
void compute_DEF(BasicBlock *bb)
{
	BitVector bv(exp_count);
	bv.reset();
	errs() << "--DEF of the BB == "<< bb->getName()<<"\n";
	for(BasicBlock::iterator I = bb->begin(), E = bb->end(); I != E; ++I)
   	{
     		//if(I->getOpcode()==Instruction::PHI)
     		//	continue;
   		errs() << "\n	Def: " <<*I<<"\n";
   		for (User *U : I->users()) 
   		{
  			if (Instruction *Inst = dyn_cast<Instruction>(U)) 
  			{
  				if(Inst->getOpcode()==Instruction::PHI)
  				{
  					for (User *U1 : Inst->users()) 
  					{
  						Instruction *Inst1 = dyn_cast<Instruction>(U1);
  						if (Inst1!=NULL && (Inst1->isBinaryOp() || Instruction::isCast(Inst1->getOpcode() || isa<CallInst>(&*Inst1)))) 
  						{
  							int ind = getIndex(Inst1);
    							errs() << "		Use ----"<<ind<<"---"<<*Inst1 << "\n";
    							bv.set(ind);
    							V_DEF[bb].push_back(Inst1);
    						}
  					}
  				}
    				else if(Inst->isBinaryOp() || Instruction::isCast(Inst->getOpcode()) || isa<CallInst>(&*Inst))
    				{
    					int ind = getIndex(Inst);
    					errs() << "		Use:  ----"<<ind<<"---"<< *Inst << "\n";
    					bv.set(ind);
    					V_DEF[bb].push_back(Inst);
    				}
  			}
  		}
  	}
  	V_DEF_BV[bb] = bv;
}

BitVector AND(BitVector A,BitVector B)
{
	BitVector ret(exp_count,true);
	for(int i = 0; i < A.size(); i++)
     		if(A.test(i)==false || B.test(i)==false)
     			ret[i] = 0;
     	return ret;
}
BitVector OR(BitVector A,BitVector B)
{
	BitVector ret(exp_count,false);
	for(int i = 0; i < A.size(); i++)
     		if(A.test(i)==true || B.test(i)==true)
     			ret[i] = 1;
     	return ret;
}
BitVector NEG(BitVector A)
{
	BitVector ret(exp_count,false);
	for(int i = 0; i < A.size(); i++)
     		if(A.test(i)==false)
     			ret[i] = 1;
     	return ret;
}
bool isVectorsSame(BitVector A,BitVector B)
{
	for(int i = 0;i<A.size();i++)
	{
		if((A.test(i)==true && B.test(i)==false) || (A.test(i)==false && B.test(i)==true)) 
			return false;
	}
	return true;
}
void dfs(BasicBlock* bb,int *change)
{
	   visited[bb] = 1;
	   Instruction *non = bb->getFirstNonPHI();
      	   //errs() << "--First Instrn "<< *non <<"\n";
	   Instruction* linst=bb->getTerminator();
	   BitVector bv_out_new(exp_count,true);
	   if(linst->getNumSuccessors() ==0)
	   	bv_out_new.reset();
	   for(int i=0;i<linst->getNumSuccessors();i++)
	   {
	      BasicBlock *child = linst->getSuccessor(i);
	      
	      bv_out_new = AND(bv_out_new,IN_BV[child]); 
	      if(visited[linst->getSuccessor(i)]==0)
	      {
	      	dfs(linst->getSuccessor(i),change);
	      }
	   }
	   
	   BitVector bv_out_old = OUT_BV[bb];
	   BitVector bv_in_old = IN_BV[bb];
	  
	  
	   BitVector bv_in_new = OR(V_USE_BV[bb],AND(bv_out_new,NEG(V_DEF_BV[bb])));
	   
	   IN_BV[bb] = bv_in_new;
	   OUT_BV[bb] = bv_out_new;
	   
	   if(!(isVectorsSame(bv_in_new,bv_in_old) && isVectorsSame(bv_out_new,bv_out_old)))
	   	*change = 1;   
	   	
	   	
	   /*errs() << "\n\n--First Instrn "<< *non <<"\n";
	   errs()<<"\nIN\n";
	   for(int i = 0;i<bv_in_new.size();i++)
	   	errs()<<bv_in_new[i];
	   errs()<<"\nOUT\n";
	   for(int i = 0;i<bv_in_new.size();i++)
	   	errs()<<bv_out_new[i];
	   errs()<<"\nIN_OLD\n";
	   for(int i = 0;i<bv_in_new.size();i++)
	   	errs()<<bv_in_old[i];
	   errs()<<"\nOUT_OLD\n";
	   for(int i = 0;i<bv_in_new.size();i++)
	   	errs()<<bv_out_old[i];
	   errs()<<"\nUSE\n";
	   for(int i = 0;i<bv_in_new.size();i++)
	   	errs()<<V_USE_BV[bb][i];
	   errs()<<"\nDEF\n";
	   for(int i = 0;i<bv_in_new.size();i++)
	   	errs()<<V_DEF_BV[bb][i];
	   errs()<<"\n";*/
	   //}
	   
	   /*for(int i=0;i<linst->getNumSuccessors();i++)
	   {
	      
	      if(visited[linst->getSuccessor(i)]==0)
	      {
	      	dfs(linst->getSuccessor(i),change);
	      }
	   }*/
	   
}
	   
bool check_fun(Exp *exp1,Exp *exp2)
{
	CallInst* callInst1 = exp1->inst;
	CallInst* callInst2 = exp2->inst;
	Function *calledFunction1 = exp1->F;
	Function *calledFunction2 = exp2->F;
	
	bool allArgsEqual = false;
	if (calledFunction1 && calledFunction2 && calledFunction1 == calledFunction2) {
	    // The instructions have the same called function
	    //errs()<<"\n	One --- \n";
	    if (exp1->argc == exp2->argc) {
	    	//errs()<<"\n	Two --- \n";
		// The instructions have the same number of arguments
		allArgsEqual = true;
		for (unsigned i = 0; i < exp1->argc; i++) {
			//errs() <<"\n	"<<*(callInst1->getArgOperand(i)) << "  ---	"<<*(callInst2->getArgOperand(i))<<"\n";
		    if (exp1->arg[i] != exp2->arg[i]) {
		        //errs()<<"\n	Three --- \n";
		        allArgsEqual = false;
		        break;
		    }
		}
	    }
	}
	return allArgsEqual;
}
bool isSame(Exp *exp1,Exp *exp2)
{
	if(exp1->fun_or_op != exp2->fun_or_op)
		return false;
	if(exp1->fun_or_op == 1)
		return check_fun(exp1,exp2);
	if(exp1->op1==exp2->op1 and exp1->op2==exp2->op2 and exp1->opcode==exp2->opcode)
  		return true;
  	return false;	
}
int isUnique(Exp *exp)
{
	for(int i = 0;i<exp_count;i++)
	{
		Exp *temp = Ind_to_ins[i];
		if(isSame(temp,exp))
			return i;
	}
	return -1;
}
void initialize_IN_OUT(Function &F)
{
	for(Function::iterator bb = F.begin();bb!=F.end();bb++)
	{
		BitVector bv1(exp_count,true);
		
		BitVector bv2(exp_count,false);
		
		IN_BV[&*bb] = bv1;
		OUT_BV[&*bb] = bv2; 
		visited[&*bb] = 0;
	}
}

void compute_INOUT(Function &F)
{
	initialize_IN_OUT(F);
	
	errs() << "--DFS on CFG---\n\n";
	BasicBlock* bb=&F.getEntryBlock();
	int change = 1;
	int c = 0;
	while(change==1)
	{
		errs() << "	Iteration --"<<c++<<"\n";
		change = 0;
		visited.clear();
		dfs(bb,&change);
		errs() << "	Change == "<<change<<"\n\n";
	}
	
	errs() <<"	Final--\n\n";
	
	for(Function::iterator bb = F.begin();bb!=F.end();bb++)
	{
		Instruction *non = bb->getFirstNonPHI();
      	   	errs() << "\n\n--First Instrn "<< *non <<"\n";
      	   	errs()<<"\nIN\n";
		   for(int i = 0;i<exp_count;i++)
		   	errs()<<IN_BV[&*bb][i];
		   errs()<<"\nOUT\n";
		   for(int i = 0;i<exp_count;i++)
		   	errs()<<OUT_BV[&*bb][i];
	}
	
}
void printt(BitVector A)
{
	errs() << A.size()<<"\n";
	for(int i = 0;i<A.size();i++)
	{
		errs() << A[i];
	}
	errs()<<"\n";
}
int getFreq(Exp *exp1,BasicBlock *bb,map<BasicBlock*,int> &visit)
{
	visit[bb] = 1;
	int ret = 0;
	for(BasicBlock::iterator I = bb->begin(), E = bb->end(); I != E; ++I)
   	{
   		Instruction *k=dyn_cast<Instruction>(I);
   		if(!(!(k->getOpcode()==Instruction::PHI) && (k->isBinaryOp() || Instruction::isCast(k->getOpcode()) || isa<CallInst>(&*k))))
      			continue;
      		
      		Exp *exp2;
      		if(CallInst* call_inst = dyn_cast<CallInst>(&*I))
	      			exp2 = new Exp(call_inst);
      		else
      				exp2 = new Exp(k->getOperand(0),k->getOperand(1),k->getOpcode(),&*I);
      		
      		if(isSame(exp1,exp2))
      			ret++;
      		//errs()<<"	Print --- "<<*k<<"	-- "<<ret<<"\n";
      		
   	}
	Instruction* linst=bb->getTerminator();
	   for(int i=0;i<linst->getNumSuccessors();i++)
	   { 
	      if(visit[linst->getSuccessor(i)]==0)
	      {
	      	ret+=getFreq(exp1,linst->getSuccessor(i),visit);
	      }
	   }
	   return ret;
}
void hoist(BasicBlock *bb,Exp *exp1,Instruction *r,map<BasicBlock*,int> &visit)
{
	visit[bb] = 1;
	for(BasicBlock::iterator I = bb->begin(), E = bb->end(); I != E; ++I)
   	{
   		Instruction *k=dyn_cast<Instruction>(I);
   		
   		
   		if(!(!(k->getOpcode()==Instruction::PHI) && (k->isBinaryOp() || Instruction::isCast(k->getOpcode()) || isa<CallInst>(&*k))))
      			continue;
      		Exp *exp2;
      		if(CallInst* call_inst = dyn_cast<CallInst>(&*I))
	      			exp2 = new Exp(call_inst);
      		else
      				exp2 = new Exp(k->getOperand(0),k->getOperand(1),k->getOpcode(),&*I);
      		
      		//errs()<<"	Print --- "<<*k<<"\n";
      		if(isSame(exp1,exp2))
      		{
      			errs() << "			Hoist -- "<<*k<<"\n\n";
      			//process
      			k->replaceAllUsesWith(r);
      			
      			//errs()<<"		Hello	\n\n";
      			I--;
      			k->eraseFromParent();
      			
      		}
   	}
	 Instruction* linst=bb->getTerminator();
	   for(int i=0;i<linst->getNumSuccessors();i++)
	   {
	   	if(visit[linst->getSuccessor(i)]==0)
	      	{
	      	hoist(linst->getSuccessor(i),exp1,r,visit);
	      	}   
	   }
}
void decide_Anticipated(BasicBlock *bb,vector<int> &yet_to_visit)
{
	Instruction *lastBinary = NULL;
	for(BasicBlock::iterator I = bb->begin(), E = bb->end(); I != E; ++I)
	{
		Instruction *k=dyn_cast<Instruction>(I);
		if(k->isBinaryOp() || Instruction::isCast(k->getOpcode()) || isa<CallInst>(&*k))
			lastBinary = k;
	}
	BitVector in = IN_BV[bb];
	BitVector out = OUT_BV[bb];
	errs() << "\n\n	First_Instruction -- " <<*(bb->getFirstNonPHI())<<"\n";
	for(BasicBlock::iterator I = bb->begin(), E = bb->end(); I != E; ++I)
				{
					Instruction *k=dyn_cast<Instruction>(I);
					errs()<<"  Inst -- "<<*k<<"\n";
					}
					errs()<<"\n";
	for(int i = 0;i<exp_count;i++)
	{
		map<BasicBlock*,int> visit;
		Exp *exp1 = Ind_to_ins[i];
		int freq = getFreq(exp1,bb,visit);
		errs() << "	Ins == "<<i<<"  Freq == "<<freq<<"\n\n";
		if(in.test(i)==true && out.test(i)==true)
		{
			if(freq>1 && yet_to_visit[i]==0)
			{
				end_pass = 0;
				errs() << "		In(Yes), Out(yes) --"<<" --Inst_ind == "<<i<<"\n";
				// Place temp at top with Instruction Ind_to_ins[i]
				yet_to_visit[i] = 1;
				
				Instruction *ins;
				if(exp1->fun_or_op == 1)
				{
					vector<Value*> args;
					CallInst* callInst1 = exp1->inst;
					Function *calledFunction1 = callInst1->getCalledFunction();
						for (unsigned i = 0; i < calledFunction1->arg_size(); i++) {
							args.push_back(callInst1->getArgOperand(i));
						}
					ins = llvm::CallInst::Create(calledFunction1,args,to_string(lval));
				}
				//else if(exp1->opcode == llvm::Instruction::SIToFP)
				//{
				//	 
				//	Type* target = llvm::Type::getDoubleTy(bb->getContext());
				//	ins = llvm::CastInst::Create(static_cast<llvm::Instruction::CastOps>(exp1->opcode),exp1->op1,target,to_string(lval));
				//}
				else if(Instruction::isCast(exp1->opcode))
				{
					 
					//Type* target = llvm::Type::getInt32Ty(bb->getContext());
					ins = llvm::CastInst::Create(static_cast<llvm::Instruction::CastOps>(exp1->opcode),exp1->op1,(exp1->dest)->getType(),to_string(lval));
				}
				else
				{
					BinaryOperator* bp;
      					ins = bp->Create(static_cast<llvm::Instruction::BinaryOps>(exp1->opcode),exp1->op1,exp1->op2,to_string(lval));
				}
				//errs()<<"		New --- " <<*ins<<"\n\n";  
      				lval++;
      				
      				
      				
      				map<BasicBlock*,int> vis;
      				hoist(bb,exp1,ins,vis);
      				errs()<<"		Done--\n";
      				
      				ins->insertInto(bb,bb->getFirstInsertionPt());
			}
		}
		else if(in.test(i)==false && out.test(i)==true)
		{
			if(freq>1 && yet_to_visit[i]==0)
			{
				end_pass = 0;
				errs() << "		In(No), Out(yes) -- First_Instruction --"<<" --Inst_ind == "<<i<<"\n\n";
				// Place temp at bottom with Instruction Ind_to_ins[i]
				yet_to_visit[i] = 1;
				
				Instruction *ins;
				if(exp1->fun_or_op == 1)
				{
					vector<Value*> args;
					CallInst* callInst1 = exp1->inst;
					Function *calledFunction1 = callInst1->getCalledFunction();
						for (unsigned i = 0; i < calledFunction1->arg_size(); i++) {
							args.push_back(callInst1->getArgOperand(i));
						}
					ins = llvm::CallInst::Create(calledFunction1,args,to_string(lval));
					//errs()<<"\n	Created FUn	"<<*ins<<"\n";
				}
				//else if(exp1->opcode == llvm::Instruction::SIToFP)
				//{
				//	 
				//	Type* target = llvm::Type::getDoubleTy(bb->getContext());
				//	ins = llvm::CastInst::Create(static_cast<llvm::Instruction::CastOps>(exp1->opcode),exp1->op1,target,to_string(lval));
				//}
				else if(Instruction::isCast(exp1->opcode))
				{
					 
					//Type* target = llvm::Type::getInt32Ty(bb->getContext());
					ins = llvm::CastInst::Create(static_cast<llvm::Instruction::CastOps>(exp1->opcode),exp1->op1,(exp1->dest)->getType(),to_string(lval));
				}
				else
				{
					BinaryOperator* bp;
      					ins = bp->Create(static_cast<llvm::Instruction::BinaryOps>(exp1->opcode),exp1->op1,exp1->op2,to_string(lval));
				}
      				
      				//Instruction *ins=dyn_cast<Instruction>(dest);
      				
      				lval++;
      				//Instruction* linst=bb->getTerminator();
      				
      				// But it fails if ins is also computed in current basicblock
      				
      				
      				
      				int fl = 0;
      				Instruction *firstMatch_prev = NULL;
      				for(BasicBlock::iterator I = bb->begin(), E = bb->end(); I != E; ++I)
				{
					Instruction *k=dyn_cast<Instruction>(I);
      		
      					if(!(!(k->getOpcode()==Instruction::PHI) && (k->isBinaryOp() || Instruction::isCast(k->getOpcode()) || isa<CallInst>(&*k))))
      					{
      						// new_addition
      						firstMatch_prev = k;
			      			continue;
			      		}
			      		Exp *exp2;
			      		if(CallInst* call_inst = dyn_cast<CallInst>(&*I))
				      			exp2 = new Exp(call_inst);
			      		else
			      				exp2 = new Exp(k->getOperand(0),k->getOperand(1),k->getOpcode(),&*I);
      				
      					if(isSame(exp1,exp2))
      					{
      						fl = 1;
      						break;
      					}
      					firstMatch_prev = k;
				}
				
				map<BasicBlock*,int> vis;
      				hoist(bb,exp1,ins,vis);
      				
      				if(fl==0)
      					ins->insertAfter(lastBinary);
      				else if(firstMatch_prev == NULL)
      					ins->insertInto(bb,bb->getFirstInsertionPt());
      				else
      					ins->insertAfter(firstMatch_prev);
      					
      				
      				//ins->insertInto(bb,bb->end());
      				
      				//Instruction *k=dyn_cast<Instruction>(ins);
				     //int flag=1;
				     /*for (Use &U : ins->operands())
				     {
					  Value *v = U.get();
					  Instruction *use=dyn_cast<Instruction>(v);
					  if(use!=NULL)
					  {
					  	ins->insertAfter(use);
					  	break;
					  }
					 }*/
			
				
				
			}
		}
		else if(in.test(i) && !out.test(i))
		{
			
		}
	} 
}
void helper(BasicBlock *bb,vector<int> yet_to_visit)
{
	decide_Anticipated(bb,yet_to_visit);
	
	visited[bb] = 1;
	Instruction* linst=bb->getTerminator();
	   for(int i=0;i<linst->getNumSuccessors();i++)
	   { 
	      if(visited[linst->getSuccessor(i)]==0)
	      {
	      	helper(linst->getSuccessor(i),yet_to_visit);
	      }
	   }
}
void findAnticipated(Function &F)
{
	BasicBlock* bb=&F.getEntryBlock();
	visited.clear();
	vector<int> yet_to_visit(exp_count,0);
	helper(bb,yet_to_visit);
}
void CLEAR()
{
		IN.clear();
		OUT.clear();
		V_USE.clear();
		V_DEF.clear();
		IN_BV.clear();
		OUT_BV.clear();
		V_USE_BV.clear();
		V_DEF_BV.clear();
		Ins_to_ind.clear();
		Ind_to_ins.clear();
		Ins_to_freq.clear();
		visited.clear();
}
namespace {
  struct final_ae : public FunctionPass {
    static char ID;
    final_ae() : FunctionPass(ID) {}
    bool runOnFunction(Function &F) override {
    
      
      lval = 101;
      end_pass = 0;
      while(end_pass == 0)
      {
      		exp_count = 0;
      		end_pass = 1;
      		CLEAR();
		
		
	      errs() << "Function " << F.getName() << "\n";
	      errs() << "Unique_Instructions\n\n";
	      for(inst_iterator I = inst_begin(F), E = inst_end(F); I != E; ++I)
	      {
	      		if(!(!(I->getOpcode()==Instruction::PHI) && (I->isBinaryOp() || Instruction::isCast(I->getOpcode()) || isa<CallInst>(&*I))))
	      			continue;
	      			
			Exp *exp;
	      		if(CallInst* call_inst = dyn_cast<CallInst>(&*I))
	      			exp = new Exp(call_inst);
	      		else
	      			exp = new Exp(I->getOperand(0),I->getOperand(1),I->getOpcode(),&*I);
	      		
	      		int ind = isUnique(exp); 
	      		if(ind==-1)
	      		{
	      			errs()<<"	"<<*I<<"  ind == "<<exp_count<<"\n";
	      			Ins_to_ind[exp] = exp_count;
	      			Ind_to_ins[exp_count] = exp;
	      			Ins_to_freq[exp_count] = 1;
	      			
	      			exp_count++;
	      			
	      		}
	      		else
	      			Ins_to_freq[ind]++;
	      }
	      for(int i = 0;i<exp_count;i++)
	      {
	      	errs() << "\n	--- "<<i<<" -- Freq == "<<Ins_to_freq[i];
	      }
	      
	      
	      
	      /*for(inst_iterator I = inst_begin(F), E = inst_end(F); I != E; ++I)
	      {
	      		//Instruction *k=dyn_cast<Instruction>(I);
	      		Ind_to_ins[ind] = &*I;
	      		Ins_to_ind[&*I] = ind++;
	      }
	      errs()<<"---Number of Instructions == "<<ind<<"\n\n"; 
	      */
	      
	      for(Function::iterator bb = F.begin();bb!=F.end();bb++)
	      {
	      		// bb is BasicBlock*
	      		errs() <<  "Block_name " << bb->getName() << "\n";
	      		Instruction *non = bb->getFirstNonPHI();
	      		errs() << "--First Instrn "<< *non <<"\n";
	      		errs() << "--Terminator "<< *(bb->getTerminator())<<"\n";
	      		compute_USE(&*bb);
	      		compute_DEF(&*bb);
	      		errs()<<"\n\n";
	      }
	      initialize_IN_OUT(F);
	      
	      
	      compute_INOUT(F);
	      
	      findAnticipated(F);
	}
      
      return true;
    }
  };
}
char final_ae::ID=0;
static RegisterPass<final_ae> X("final_ae","USE and DEF of each block");
