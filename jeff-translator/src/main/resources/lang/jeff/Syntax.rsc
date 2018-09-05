module lang::jeff::Syntax

extend lang::std::Layout;
extend lang::std::Id;

start syntax Prog
  = DeclOrTest* declsOrTests
  ;
  
syntax DeclOrTest
	= Decl decl
	| Test test
	;  
  
syntax Test 
	= typeChecking: "typetest" Id name "{" Expr expr "}" "hastype" "{" T expected "}" HasEffectOptional? WithEnvOptional?
	| checkClass: "classtypechecks" Id className YesNo yesno
	| checkInterface: "interfacetypechecks" Id className YesNo yesno
	| checkExecution: "evaltest" Id name "{" Expr expr "}" "produces" "{" Expr expr "}"
	; 
  
syntax WithEnvOptional
	= "withenv" "{"{FormalParam ","}* formals "}"
  	;
  	
syntax HasEffectOptional
	= "haseffect" "{" EffectsOptional effect "}"
  	;  	
  	
syntax Decl
  = interface: "interface" Id name TypeParsOptional ExtendsOptional extends  "{" MethodHeader* methods "}"
  | class: "class" Id name TypeParsOptional "("{FormalParam ","}* formals ")" ImplementsOptional "{" MethodDecl* methods "}"
  ;
  
syntax FormalParam 
  = T Id
  ;
  
syntax T 
	= Id\Reserved
	| Id\Reserved "\<"  {T ","}* typeArgs "\>";
	
syntax TypeParsOptional
	= TypePars?;
	
syntax TypePars
	= "\<" {TypePar ","}* typePars "\>"
	;    

	
syntax ExtendsOptional
	= Extends?;
		
syntax ImplementsOptional
	= Implements?;
  
	
syntax TypePar = Id "\<\<" T |
				 Id;

  
syntax Extends
  = "extends" {T ","}+ supers
  ;  
  
syntax Implements
  = "implements" {T ","}+ supers
  ; 

syntax MethodHeader
  = ModOptional mod TypeParsOptional tps T rType Id name "("{FormalParam ","}* formals ")" EffectsOptional
  ;
  
syntax ModOptional = Mod?;
  
lexical Mod = "eff" | "native";

lexical YesNo = "yes" | "no";
  
syntax MethodDecl
  = MethodHeader header "=" Expr body
  ;
  
syntax EffectsOptional = EffectsList? ;

syntax EffectsList
	= "(" { T "," }* types ")" 
	;


syntax MethodSelector = Id\Reserved;


// how to add `new` as valid argument
syntax Super
  = T;

syntax TypeArgsOptional
	= TypeArgs?;
	
syntax TypeArgs
	= "\<" {T ","}* typeArgs "\>"
	;    


keyword Reserved = "this" | "else" | "if" | "let" | "with" | "there" | "eff" | "native" | "pure" ;

lexical Str
  = [\"]![\"]*[\"];
  
lexical Num
  = [1-9][0-9]* !>> [0-9]
  | [0]
  ;

/*
C() create object of class C
this() create object of class I'm in
super() create object of super class of class I'm in
this.f() call method on self
super.f() call method on self via super
f!() call effect method on enclosing handler defining f!
*/

syntax Expr
  = this: "this"
  | there: "there"
  | with: "with" "(" Expr ")" "{" Expr "}"
  | field: Expr "." Id
  //| closure: "("  {FormalParam ","}* formals  ")" "=\>"  "{" Expr "}" 
  | sig: Id TypeArgsOptional "::" Id TypeArgsOptional "(" {Expr ","}* ")"
  | number: Num
  | var: Id \ Reserved
  //| val: Value
  | bracket brack: "(" Expr ")"
  //| ite: "if" "(" Expr ")" "{" Expr "}" "else" "{" Expr "}"
  | let: T Id "=" Expr "{" Expr "}" 
  //| right seq: Expr ";" Expr
  | new: "new" T "(" {Expr ","}* ")"
  | send: Expr "."  TypeArgsOptional Id "(" {Expr ","}* ")"
  ;   

