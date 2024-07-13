#include "imp_codegen.hh"

ImpCodeGen::ImpCodeGen(ImpTypeChecker* a):analysis(a) {

}

void ImpCodeGen::codegen(string label, string instr) {
  if (label !=  nolabel)
    code << label << ": ";
  code << instr << endl;  
}

void ImpCodeGen::codegen(string label, string instr, int arg) {
  if (label !=  nolabel)
    code << label << ": ";
  code << instr << " " << arg << endl;
}

void ImpCodeGen::codegen(string label, string instr, string jmplabel) {
  if (label !=  nolabel)
    code << label << ": ";
  code << instr << " " << jmplabel << endl;
}

string ImpCodeGen::next_label() {
  string l = "L";
  string n = to_string(current_label++);
  l.append(n);
  return l;
}

string ImpCodeGen::get_flabel(string fname) {
  string l = "L";
  l.append(fname);
  return l;
}

void ImpCodeGen::codegen(Program* p, string outfname) {
  nolabel = "";
  current_label = 0;

  p->accept(this);
  ofstream outfile;
  outfile.open(outfname);
  outfile << code.str();
  outfile.close();

  return;
}

// Este codigo esta completo
void ImpCodeGen::visit(Program* p) {
  current_dir = 0;  // usado para generar nuebvas firecciones
  direcciones.add_level();
  process_global = true;
  p->var_decs->accept(this);
  process_global = false;

  mem_globals = current_dir; 
  
  // codegen
  codegen("start","skip");
  codegen(nolabel,"enter",mem_globals);
  codegen(nolabel,"alloc",mem_globals);
  codegen(nolabel,"mark");
  codegen(nolabel,"pusha",get_flabel("main"));
  codegen(nolabel,"call");
  codegen(nolabel,"halt");

  p->fun_decs->accept(this);
  direcciones.remove_level();
  return;  
}

void ImpCodeGen::visit(Body * b) {

  // guardar direccion inicial current_dir
  int internal_dir = current_dir;
 current_dir =0;
  
  direcciones.add_level();
  
  b->var_decs->accept(this);
  b->slist->accept(this);
  
  direcciones.remove_level();

  // restaurar dir

    current_dir = internal_dir;
  return;
}

void ImpCodeGen::visit(VarDecList* s) {
  list<VarDec*>::iterator it;
  for (it = s->vdlist.begin(); it != s->vdlist.end(); ++it) {
    (*it)->accept(this);
  }  
  return;
}

// Se crea entrada para declaraciones de variables
void ImpCodeGen::visit(VarDec* vd) {
  list<string>::iterator it;
  for (it = vd->vars.begin(); it != vd->vars.end(); ++it){
    current_dir++;
    VarEntry ventry;
    ventry.dir = current_dir;
    ventry.is_global = process_global;
    direcciones.add_var(*it, ventry);
  }
  return;
}

void ImpCodeGen::visit(FunDecList* s) {
  list<FunDec*>::iterator it;
  for (it = s->fdlist.begin(); it != s->fdlist.end(); ++it) {
    (*it)->accept(this);
  }
  return;
}

void ImpCodeGen::visit(FunDec* fd) {
  FEntry fentry = analysis->ftable.lookup(fd->fname);
  current_dir = 0;
  int m = fd->types.size();


//  cout<<"fname          :" << fentry.fname <<endl;
//  cout<<"ImpType        :" << fentry.ftype <<endl;
//  cout<<" mem_locals    :" << fentry.mem_locals <<endl;
//  cout<<"max_stacks     :" << fentry.max_stack <<endl;
//  cout<<"m              :"<<m<<endl;

  VarEntry ventry;
  int location = m+3;
  // agregar direcciones de argumentos
  int enter_parameter = fentry.mem_locals + fentry.max_stack; // Se calcula el espacio en stack que usara la funcion
  int alloc_parameter =  fentry.mem_locals  ;

  for(auto function_parameter_id : fd->vars)
  {
      current_dir++;
      ventry.dir = current_dir - location;
      ventry.is_global = process_global;
      direcciones.add_var(function_parameter_id , ventry);
  }

  // agregar direccion de return
    ventry.dir = location;
   //Locacion donde esta la variable return en referencia a la funcion
   direcciones.add_var("return" , ventry ) ;//agregar al envirorment

  // generar codigo para fundec
    codegen("skip" , get_flabel(fd->fname));
    codegen(nolabel,"enter" ,enter_parameter);
    codegen(nolabel ,"alloc" , alloc_parameter);


  num_params = m;

  fd->body->accept(this);
  // -- sacar comentarios para generar codigo del cuerpo

  return;
}


void ImpCodeGen::visit(StatementList* s) {
  list<Stm*>::iterator it;
  for (it = s->slist.begin(); it != s->slist.end(); ++it) {
    (*it)->accept(this);
  }
  return;
}

void ImpCodeGen::visit(AssignStatement* s) {
  s->rhs->accept(this);
  VarEntry ventry = direcciones.lookup(s->id);

  int location = num_params+3; // Previamente guardado en declaracion de funcion
  if(ventry.is_global)
      codegen(nolabel,"store", ventry.dir - location);
  else codegen(nolabel,"storer", ventry.dir);



  return;
}

void ImpCodeGen::visit(PrintStatement* s) {
  s->e->accept(this);
  code << "print" << endl;;
  return;
}

void ImpCodeGen::visit(IfStatement* s) {
  string l1 = next_label();
  string l2 = next_label();
  
  s->cond->accept(this);
  codegen(nolabel,"jmpz",l1);
  s->tbody->accept(this);
  codegen(nolabel,"goto",l2);
  codegen(l1,"skip");
  if (s->fbody!=NULL) {
    s->fbody->accept(this);
  }
  codegen(l2,"skip");
 
  return;
}

void ImpCodeGen::visit(WhileStatement* s) {
  string l1 = next_label();
  string l2 = next_label();

  codegen(l1,"skip");
  s->cond->accept(this);
  codegen(nolabel,"jmpz",l2);
  s->body->accept(this);
  codegen(nolabel,"goto",l1);
  codegen(l2,"skip");

  return;
}

void ImpCodeGen::visit(ReturnStatement* s) {

    VarEntry return_addr = direcciones.lookup("return");

    if(s->e == nullptr) //Para void o main (no expresion de return esperada)
    {
        codegen(nolabel,"return" , return_addr.dir);//retornar location
        return;
    }


    // agregar codigo


  s->e->accept(this); //generar el codigo de la expresion de return
    codegen(nolabel , "storer" , -return_addr.dir);//guardar en direccion
  codegen(nolabel,"return", return_addr.dir);  //remover elementos de la pila
  return;
}


int ImpCodeGen::visit(BinaryExp* e) {
  e->left->accept(this);
  e->right->accept(this);
  string op = "";
  switch(e->op) {
  case PLUS: op =  "add"; break;
  case MINUS: op = "sub"; break;
  case MULT:  op = "mul"; break;
  case DIV:  op = "div"; break;
  case LT:  op = "lt"; break;
  case LTEQ: op = "le"; break;
  case EQ:  op = "eq"; break;
  default: cout << "binop " << Exp::binopToString(e->op) << " not implemented" << endl;
  }
  codegen(nolabel, op);
  return 0;
}

int ImpCodeGen::visit(NumberExp* e) {
  codegen(nolabel,"push ",e->value);
  return 0;
}

int ImpCodeGen::visit(TrueFalseExp* e) {
  codegen(nolabel,"push",e->value?1:0);
 
  return 0;
}

int ImpCodeGen::visit(IdExp* e) {
  VarEntry ventry = direcciones.lookup(e->id);
  if (ventry.is_global)
    codegen(nolabel,"load",ventry.dir);
  else
    codegen(nolabel,"loadr",ventry.dir);
  return 0;
}

int ImpCodeGen::visit(ParenthExp* ep) {
  ep->e->accept(this);
  return 0;
}

int ImpCodeGen::visit(CondExp* e) {
  string l1 = next_label();
  string l2 = next_label();
 
  e->cond->accept(this);
  codegen(nolabel, "jmpz", l1);
  e->etrue->accept(this);
  codegen(nolabel, "goto", l2);
  codegen(l1,"skip");
  e->efalse->accept(this);
  codegen(l2, "skip");
  return 0;
}

int ImpCodeGen::visit(FCallExp* e) {

  FEntry fentry = analysis->ftable.lookup(e->fname);
  ImpType ftype = fentry.ftype;

  // agregar codigo

  codegen(nolabel,"call");
  return 0;
}
