#ifndef IMP_INTERPRETER
#define IMP_INTERPRETER

#include <unordered_map>

#include "imp.hh"
#include "imp_value_visitor.hh"
#include "environment.hh"

using namespace std;

class ImpInterpreter : public ImpValueVisitor {
private:
  Environment<ImpValue> env;
  Environment<FunDec*> fdecs;
  ImpValue retval;
  bool retcall;

public:
  void interpret(Program*);
  void visit(Program*);
  void visit(Body*);
  void visit(VarDecList*);
  void visit(VarDec*);  
  void visit(FunDecList*); // new
  void visit(FunDec*); // new 
  void visit(StatementList*);
  void visit(AssignStatement*);
  void visit(PrintStatement*);
  void visit(IfStatement*);
  void visit(WhileStatement*);
  void visit(ReturnStatement* e); // new
  void visit(FcallStatement * fcall); // Fcallstm para interpreter
  void visit(ForDoStatement* fordo); //Declaration of Fordo for interpreter
  
  ImpValue visit(BinaryExp* e);
  ImpValue visit(NumberExp* e);
  ImpValue visit(TrueFalseExp* e);
  ImpValue visit(IdExp* e);
  ImpValue visit(ParenthExp* e);
  ImpValue visit(CondExp* e);
  ImpValue visit(FCallExp* e); // new
};


#endif

