#ifndef IMP_VALUE_VISITOR
#define IMP_VALUE_VISITOR

#include "imp.hh"
#include "imp_value.hh"

class ImpValueVisitor {
public:
  virtual void visit(Program* p) = 0;
  virtual void visit(Body* b) = 0; 
  virtual void visit(VarDecList* e) = 0;
  virtual void visit(VarDec* e) = 0;
  virtual void visit(FunDecList* e) = 0;
  virtual void visit(FunDec* e) = 0;
  virtual void visit(StatementList* e) = 0;
  virtual void visit(AssignStatement* e) = 0;
  virtual void visit(PrintStatement* e) = 0;
  virtual void visit(IfStatement* e) = 0;
  virtual void visit(WhileStatement* e) = 0;
  virtual void visit(ReturnStatement* e) = 0;
  virtual void visit(FcallStatement * fcall) =0 ; // Fcallstm para interpreter
  virtual void visit(ForDoStatement * fordo) = 0 ; //Declaration of Fordo for interpreter
  
  virtual ImpValue visit(BinaryExp* e) = 0;
  virtual ImpValue visit(NumberExp* e) = 0;
  virtual ImpValue visit(TrueFalseExp* e) = 0;
  virtual ImpValue visit(IdExp* e) = 0;
  virtual ImpValue visit(ParenthExp* e) = 0;
  virtual ImpValue visit(CondExp* e) = 0;
  virtual ImpValue visit(FCallExp* e) = 0;
};


#endif
