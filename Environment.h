#include <stdio.h>

#include "clang/AST/ASTConsumer.h"
#include "clang/AST/Decl.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Frontend/FrontendAction.h"
#include "clang/Tooling/Tooling.h"
#include <iostream>
#include <string>

using namespace clang;
using namespace std;
#define INF 0x7fffffffffffffff

class Heap {
 
   std::map<long, long> mBufs;
 
   std::map<long, long> mContents;
public:
	Heap() : mBufs(), mContents(){
   }

  
   long Malloc(int size) {
    
      int * buf = (int *)malloc(size * sizeof(int) );
      mBufs.insert(std::make_pair((long)buf, size));

    
      for (int i=0; i<size; i ++) {
         mContents.insert(std::make_pair((long)(buf+i), 0));
      }
      return (long)buf;
   }

 
   void Free (long addr) {
      
   	  assert (mBufs.find(addr) != mBufs.end());
      int * buf = (int *)addr;
      long size = mBufs.find(addr)->second;
      mBufs.erase(mBufs.find(addr));

      for (int i = 0; i < size; i++) {
      	assert (mContents.find((long)(buf+i)) != mContents.end());
        mContents.erase((long)(buf+i));
      }
    
      free(buf);
   }

   
   void Update(long addr, long val) {
      assert (mContents.find(addr) != mContents.end());
      mContents[addr] = val;
   }

  
   long Get(long addr) {
      assert (mContents.find(addr) != mContents.end());
      return mContents.find(addr)->second;
    }
};

class StackFrame {

   std::map<Decl*, long> mVars;
   std::map<Stmt*, long> mExprs;

   Stmt * mPC;
public:
   StackFrame() : mVars(), mExprs(), /*mHeap(),*/ mPC() {
   }




	


  
   void bindDecl(Decl* decl, int val) {
      mVars[decl] = val;
   }

   
   long getDeclVal(Decl * decl) {
      assert (mVars.find(decl) != mVars.end());
      return mVars.find(decl)->second;
   }

 
   void bindStmt(Stmt * stmt, int val) {
	   mExprs[stmt] = val;
   }

  
   long getStmtVal(Stmt * stmt) {
	   assert (mExprs.find(stmt) != mExprs.end());
	   return mExprs[stmt];
   }


   void setPC(Stmt * stmt) {
	   mPC = stmt;
   }

   
   Stmt * getPC() {
	   return mPC;
   }
};

class Environment {
  
   std::vector<StackFrame> mStack;

   Heap mHeap;
   std::vector<StackFrame> mVarGlobal;


   FunctionDecl * mFree;
   FunctionDecl * mMalloc;
   FunctionDecl * mInput;
   FunctionDecl * mOutput;


   FunctionDecl * mEntry;
public:

   Environment() : mStack(), mVarGlobal(),mFree(NULL), mMalloc(NULL), mInput(NULL), mOutput(NULL), mEntry(NULL) {
   }



   void init(TranslationUnitDecl * unit) 
   {
	   for (TranslationUnitDecl::decl_iterator i =unit->decls_begin(), e = unit->decls_end(); i != e; ++ i) 
     {
		   if (FunctionDecl * fdecl = dyn_cast<FunctionDecl>(*i) ) 
       {
			   if (fdecl->getName().equals("FREE")) mFree = fdecl;
			   else if (fdecl->getName().equals("MALLOC")) mMalloc = fdecl;
			   else if (fdecl->getName().equals("GET")) mInput = fdecl;
			   else if (fdecl->getName().equals("PRINT")) mOutput = fdecl;
			   else if (fdecl->getName().equals("main")) mEntry = fdecl;
		   }

       if(VarDecl *vardecl=dyn_cast<VarDecl>(*i))
       {
          if(!( vardecl->hasInit()))
          {
              StackFrame stack;
              stack.bindDecl(vardecl, 0);
              mVarGlobal.push_back(stack);
          
          }
          else if( vardecl->hasInit() )
          {
           
              if(isa<IntegerLiteral>(vardecl->getInit()))
              {
                  StackFrame stack;
                  IntegerLiteral *integer=dyn_cast<IntegerLiteral>(vardecl->getInit());
                  int val=integer->getValue().getSExtValue();
                  stack.bindDecl(vardecl, val);
                  mVarGlobal.push_back(stack);
               
              }
          }
       }

	   }
	   mStack.push_back(StackFrame());
   }


   FunctionDecl * getEntry() {
	   return mEntry;
   }

  
   void binop(BinaryOperator *bop) {
   	 
	   auto * left = bop->getLHS();
	   auto * right = bop->getRHS();

	
	   int valLeft=mStack.back().getStmtVal(left);
	   int valRight=mStack.back().getStmtVal(right);

	
	   if (bop->isAssignmentOp()) {
	   
	   	if(isa<UnaryOperator>(left))
	   	{
	   		UnaryOperator *uop = dyn_cast<UnaryOperator>(left);
	   	
	   		if( (uop->getOpcode()) == UO_Deref)
	   		{
	   			Expr *expr = uop->getSubExpr();
                int addr = mStack.back().getStmtVal(expr);
             
                mHeap.Update(addr, valRight);
	   		}
	   	}
	   	
	   	if(isa<ArraySubscriptExpr>(left))
	   	{
	   		ArraySubscriptExpr *array=dyn_cast<ArraySubscriptExpr>(left);
	   		Expr *leftexpr=array->getLHS();
	   		
   	        long base=mStack.back().getStmtVal(leftexpr);
   	        Expr *rightexpr=array->getRHS();
   	     
   	        long offset=mStack.back().getStmtVal(rightexpr);
   	        mHeap.Update(base + offset*sizeof(int), valRight);
	   		
	   	}

		   
		   mStack.back().bindStmt(left, valRight);
		

		
		   if (DeclRefExpr * declexpr = dyn_cast<DeclRefExpr>(left)) {
			   Decl * decl = declexpr->getFoundDecl();
			   mStack.back().bindDecl(decl, valRight);
		   }
	   }
	   
	
	   if(bop->isComparisonOp())
	   {
	   	switch(bop->getOpcode())
	   	{
	   		
	   		case BO_LT:
	   		if( valLeft < valRight )
	   			mStack.back().bindStmt(bop,true);
	   		else
	   			mStack.back().bindStmt(bop,false);
	   		break;

	   	
	   		case BO_GT:
	   		if( valLeft > valRight )
	   			mStack.back().bindStmt(bop,true);
	   		else
	   			mStack.back().bindStmt(bop,false);
	   		break;

	   	
	   		case BO_GE:
	   		if( valLeft >= valRight )
	   			mStack.back().bindStmt(bop,true);
	   		else
	   			mStack.back().bindStmt(bop,false);
	   		break;

	   	
	   		case BO_LE:
	   		if( valLeft <= valRight )
	   			mStack.back().bindStmt(bop,true);
	   		else
	   			mStack.back().bindStmt(bop,false);
	   		break;

	   	
	   		case BO_EQ:
	   		if( valLeft == valRight )
	   			mStack.back().bindStmt(bop,true);
	   		else
	   			mStack.back().bindStmt(bop,false);
	   		break;

	   	
	   		case BO_NE:
	   		if( valLeft != valRight )
	   			mStack.back().bindStmt(bop,true);
	   		else
	   			mStack.back().bindStmt(bop,false);
	   		break;
	   		default:
	   		cout<<" invalid input comparisons! "<<endl;
	   		break;
	   	}
	   }

	
	   if(bop->isAdditiveOp())
	   {
	   	switch(bop->getOpcode())
	   	{
	   		
	   		case BO_Add:
	   		mStack.back().bindStmt(bop,valLeft+valRight);
	   		break;

	   		
	   		case BO_Sub:
	   		mStack.back().bindStmt(bop,valLeft-valRight);
	   		break;
	   	}
	   }

	
	   if(bop->isMultiplicativeOp())
	   {
	   	switch(bop->getOpcode())
	   	{
	   	
	   		case BO_Mul:
	   		mStack.back().bindStmt(bop,valLeft * valRight);
	   		break;
	   	}
	   }
   }

   void unaryop(UnaryOperator* uop)
   {
   	
   	Expr *expr=uop->getSubExpr();
   	
   	int val=mStack.back().getStmtVal(expr);
	switch(uop->getOpcode())
	{
	
		case UO_Plus:
		mStack.back().bindStmt(uop,val);
		break;

	
		case UO_Minus:
		mStack.back().bindStmt(uop,-val);
		break;

		
		case UO_Deref:
		
		mStack.back().bindStmt(uop, mHeap.Get(val));
		break;

	
		case UO_AddrOf: mStack.back().bindStmt(uop,(long)expr);
		cout<<long(expr)<<endl;
		
		break;

 
	}
   }

  
   void array(ArraySubscriptExpr *arrayexpr)
   {
   	
   	Expr *leftexpr=arrayexpr->getLHS();
   	
   	int base=mStack.back().getStmtVal(leftexpr);
   	Expr *rightexpr=arrayexpr->getRHS();
   	
   	int offset=mStack.back().getStmtVal(rightexpr);
   

   	
   	mStack.back().bindStmt(arrayexpr,mHeap.Get(base + offset*sizeof(int)));
   }


   void integerliteral(IntegerLiteral* integer)
   {
   	
   	int val=integer->getValue().getSExtValue();
   	mStack.back().bindStmt(integer,val);
   }


   bool getcond(/*BinaryOperator *bop*/Expr *expr)
   {
   	return mStack.back().getStmtVal(expr);
   }

   void decl(DeclStmt * declstmt) 
   {
   	
	   for (DeclStmt::decl_iterator it = declstmt->decl_begin(), ie = declstmt->decl_end(); it != ie; ++ it) 
	   {
		Decl * decl = *it;
		
		if (VarDecl * vardecl = dyn_cast<VarDecl>(decl)) 
		{
			
			if( !( vardecl->hasInit() ) /*&& (type.compare("int *")) && (type.compare("int **"))*/)
			 {
			 	
			 	if( !( vardecl->getType()->isArrayType() ) )
			 		mStack.back().bindDecl(vardecl, 0);
			 	else
			 	{
			 	
			 		string type=(vardecl->getType()).getAsString();
			 		
			 		int size=0;
			 		int indexLeft=type.find("[");
			 		int indexRight=type.find("]");
			 		if((indexLeft!=string::npos) && (indexRight!=string::npos))
			 		{
			 			string num=type.substr(indexLeft+1,indexRight-indexLeft-1);
    					size=atoi(num.c_str());
    					
			 		}
			 		
			 	
			 		long buf=mHeap.Malloc(size);
			 		
			 		mStack.back().bindDecl(vardecl, buf);
			 	}
			 }
			
			 else if( vardecl->hasInit() )
			 {
			 	int val=mStack.back().getStmtVal(vardecl->getInit());
		    	mStack.back().bindDecl(vardecl, val);
			 }
	    	}
	    }
   }

 
   void declref(DeclRefExpr * declref) 
   {
	   mStack.back().setPC(declref);
	
	   mStack.back().bindStmt(declref, 0);

	
	   if (declref->getType()->isIntegerType()) 
	   {
		   Decl* decl = declref->getFoundDecl();
		   int val = mStack.back().getDeclVal(decl);
		   mStack.back().bindStmt(declref, val);
	   }
	
	   else if(declref->getType()->isPointerType()) 
	   {
           Decl* decl = declref->getFoundDecl();
           int val = mStack.back().getDeclVal(decl);
           mStack.back().bindStmt(declref, val);
       }
      
       else if(declref->getType()->isArrayType())
       {
       	   Decl* decl = declref->getFoundDecl();
           int val = mStack.back().getDeclVal(decl);
           mStack.back().bindStmt(declref, val);
       }
   }

 
   void cast(CastExpr * castexpr) 
   {
	   mStack.back().setPC(castexpr);
	   Expr * expr = castexpr->getSubExpr();
	   if (castexpr->getType()->isIntegerType()) 
	   {
		   
		   int val = mStack.back().getStmtVal(expr);
		   //cout<<"------CastExpr expr val: "<<val<<" getSubExpr expr:"<<expr->getStmtClassName()<<endl;
		   mStack.back().bindStmt(castexpr, val );
	   }
	   else
	   {
         int val = mStack.back().getStmtVal(expr);
         mStack.back().bindStmt(castexpr, val );
       }
   }

  
   void unarysizeof(UnaryExprOrTypeTraitExpr *uop)
   {
   	
   	  int val;
   	
      if(uop->getKind() == UETT_SizeOf )
      {
      	
         if(uop->getArgumentType()->isIntegerType())
         {
            val = sizeof(long);
         }
      
         else if(uop->getArgumentType()->isPointerType())
         {
            val = sizeof(int *);
         }
      }    
   	  mStack.back().bindStmt(uop,val);
   }

 
   void ret(ReturnStmt *retstmt)
   {
   	
   	Expr *expr=retstmt->getRetValue();
   	//cout<<expr->getStmtClassName()<<endl;
   	int val=0;
   	val=mStack.back().getStmtVal(expr);
   	mStack.back().bindStmt(retstmt,val);

   	
   	mStack.pop_back();
   	Stmt *stmt=mStack.back().getPC();
   	
   	mStack.back().bindStmt(stmt,val);
   }

   
   void call(CallExpr * callexpr) 
   {
	   mStack.back().setPC(callexpr);
	   int val = 0;
	
	   FunctionDecl * callee = callexpr->getDirectCallee();

	
	   if (callee == mInput) 
	   {
		  llvm::errs() << "Please Input an Integer Value : ";
		  scanf("%d", &val);

		  mStack.back().bindStmt(callexpr, val);
	   }
	
	   else if (callee == mOutput) 
	   {
		   Expr * decl = callexpr->getArg(0);
		   val = mStack.back().getStmtVal(decl);
		   llvm::errs() << val;
	   }
	
	   else if ( callee == mMalloc )
	   {
	   	
	   	 Expr * unaryExprOrTypeTraitExpr = callexpr->getArg(0);
         val = mStack.back().getStmtVal(unaryExprOrTypeTraitExpr);
         long buf = mHeap.Malloc(val);
         mStack.back().bindStmt(callexpr, buf);
	   }
	
	   else if (callee == mFree )
	   {
	   	
	   	 Expr * unaryExprOrTypeTraitExpr = callexpr->getArg(0);
         val = mStack.back().getStmtVal(unaryExprOrTypeTraitExpr);
         mHeap.Free(val);
         mStack.back().bindStmt(callexpr, 0);
	   }
	
	   else 
	   {
		  
	   	

	   	
	   	StackFrame stack;
	   	auto pit=callee->param_begin();
	   	for(auto it=callexpr->arg_begin(), ie=callexpr->arg_end();it!=ie;++it,++pit)
	   	{
	   		int val=mStack.back().getStmtVal(*it);
	   		stack.bindDecl(*pit,val);
	   	}
	   	mStack.push_back(stack);
	   }
   }

};
