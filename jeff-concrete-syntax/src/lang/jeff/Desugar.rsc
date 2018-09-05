module lang::jeff::Desugar

import lang::jeff::Syntax;
import util::Maybe;
import ParseTree;
import IO;
import List;

start[Prog] desugar((start[Prog]) `<DeclOrTest* dts>`) =
	[start[Prog]]
	"<for (dt<-dts) {>
	'<desugar(dt)>
	'
	'<}>";

set[Id] getTypePars((TypeParsOptional) `\< <{TypePar ","}* typePars> \>`) 
	= {getId(tp) | tp <- typePars };
	
default set[Id] getTypePars(TypeParsOptional empty) 
	= { };	
	
Id getId((TypePar) `<Id id> \<\< <T t>`) = id;

Id getId((TypePar) `<Id id>`) = id;

Decl desugar ((DeclOrTest) `<Decl decl>`) = desugar(decl);
Test desugar ((DeclOrTest) `<Test tes>`) = desugar(tes);

Decl desugar ((Decl)
  `class <Id c> <TypeParsOptional pars> ( <{FormalParam ","}* fs> ) <ImplementsOptional ifaces> {<MethodDecl* mds>}`)
  =  [Decl] "class <c> <pars1> (<fs1>)
  	        '<ifaces1> { 
  			'<mds1>
  			'}"
  when
    bool withTypePars := (TypeParsOptional) `\< <{TypePar ","}* typePars> \>` := pars ,
    set[Id] tps := (withTypePars ? getTypePars(pars) : {}),
    pars1 := desugar(pars, {}),
  	tps := getTypePars(pars),
  	fs1 := visit(fs){ case FormalParam fp => desugar(fp, tps)}, 
  	ifaces1 := desugar(ifaces, tps),
  	mds1 := visit(mds){ case MethodDecl md => desugar(md, tps)}
    ;
Test desugar ((Test) `typetest <Id name> { <Expr expr> } hastype { <T t> }`)
	= desugar((Test) `typetest <Id name> { <Expr expr> } hastype { <T t> } withenv {}`)
	;
    
Test desugar ((Test) `typetest <Id name> { <Expr expr> } hastype { <T t> } withenv { <{FormalParam ","}* fs> }`)
  =  (Test) `typetest <Id name> { <Expr desugaredExpr> } hastype { <T desugaredType> } withenv { <{FormalParam ","}* fs1> }`
  when desugaredExpr := desugar(expr, {}),
  	   desugaredType := desugarType(t, {}),
  	   fs1 := visit(fs){ case FormalParam fp => desugar(fp, {})};

Test desugar ((Test) `typetest <Id name> { <Expr expr> } hastype { <T t> } haseffect { <EffectsOptional eo>}`)
  =  desugar((Test) `typetest <Id name> { <Expr expr> } hastype { <T t> }  haseffect { <EffectsOptional eo>} withenv {}`);  

  
Test desugar ((Test) `typetest <Id name> { <Expr expr> } hastype { <T t> } haseffect { <EffectsOptional eo>} withenv { <{FormalParam ","}* fs> }`)
  = (Test) `typetest <Id name> { <Expr desugaredExpr> } hastype { <T desugaredType> } haseffect { <EffectsOptional eo1> } withenv { <{FormalParam ","}* fs1> }`
  when desugaredExpr := desugar(expr, {}),
  	   desugaredType := desugarType(t, {}),
  	   fs1 := visit(fs){ case FormalParam fp => desugar(fp, {})},
  	   eo1 := desugar(eo, {});
  	   
Test desugar ((Test) `evaltest <Id name> { <Expr expr1> } produces { <Expr expr2> }`)
  =  (Test) `evaltest <Id name> { <Expr desugaredExpr1> } produces { <Expr desugaredExpr2>  }`
  when desugaredExpr1 := desugar(expr1, {}),
  	   desugaredExpr2 := desugar(expr2, {});  	   
  	   
Decl desugar ((Decl)
  `interface <Id c> <TypeParsOptional pars> <ExtendsOptional extends> { <MethodHeader* mhs> }`)
  =  [Decl] "interface <c> <pars1>
  	        '<extends1> { 
  			'<mhs1>
  			'}"
  when
    bool withTypePars := (TypeParsOptional) `\< <{TypePar ","}* typePars> \>` := pars ,
    set[Id] tps := (withTypePars ? getTypePars(pars) : {}),
    pars1 := desugar(pars, {}),
  	tps := getTypePars(pars),
  	extends1 := desugar(extends, tps),
  	mhs1 := visit(mhs){ case MethodHeader mh => desugar(mh, tps)}
    ;    
    
default Test desugar(Test t) = t;
    
 MethodDecl desugar ((MethodDecl) `<ModOptional mo> <TypeParsOptional typePars> <T rType> <Id name> ( <{FormalParam ","}* fs> ) <EffectsOptional eff> = <Expr body>`,
 	set[Id] tps)
 	=[MethodDecl] "<desugar((MethodHeader) `<ModOptional mo> <TypeParsOptional typePars> <T rType> <Id name> ( <{FormalParam ","}* fs> ) <EffectsOptional eff>`, tps)> = <desugar(body, tps + getTypePars(typePars))>";
 		
 MethodHeader desugar ((MethodHeader) `<ModOptional mo> <TypeParsOptional typePars> <T rType> <Id name> ( <{FormalParam ","}* fs> ) <EffectsOptional eff>`,
 	set[Id] tps)
 	= [MethodHeader] "<mo> <desugar(typePars, newtps)> <desugarType(rType, newtps)> <name> (<fs1>) <desugar(eff, newtps)>"
 	when newtps := tps + getTypePars(typePars),
 	     fs1 := visit(fs){ case FormalParam fp => desugar(fp, newtps)}
 		 
 	;

EffectsOptional desugar((EffectsOptional) `(<{T ","}* ts>)`, set[Id] typePars)
	= (EffectsOptional) `(<{T ","}+ newts>)`
	when newts := visit (ts) { case T t => desugarType(t, typePars)}
	;

default EffectsOptional desugar(EffectsOptional empty, set[Id] typePars) =
	desugar((EffectsOptional) `()`, typePars)
 ;
  

ImplementsOptional desugar((ImplementsOptional) `implements <{T ","}+ ifaces>`, set[Id] typePars)
	= [ImplementsOptional] "implements <visit (ifaces){ case T t => desugarType(t, typePars)}>"
	;

default ImplementsOptional desugar(ImplementsOptional empty, set[Id] typePars)
	= [ImplementsOptional] "implements Object \< \>"
 	;
 
    
TypeParsOptional desugar((TypeParsOptional) `\< <{TypePar ","}* typePars> \>`, set[Id] tps) =
	[TypeParsOptional] "\< <visit(typePars){
		case TypePar tp => desugar(tp, tps)
	}> \>"   
 ;

default TypeParsOptional desugar(TypeParsOptional empty, set[Id] typePars) =
	empty   
 ;

	
ExtendsOptional desugar((ExtendsOptional) `extends <{T ","}+ ts>`, set[Id] typePars)
	= [ExtendsOptional] "extends <visit (ts){ case T t => desugarType(t, typePars) } >";
	
default ExtendsOptional desugar(ExtendsOptional empty, set[Id] typePars)
	= [ExtendsOptional] "extends Object \< \>";
        
	
FormalParam desugar((FormalParam) `<T t> <Id id>`, set[Id] typePars)
	 = [FormalParam] "<desugarType(t, typePars)> <id>";
	
  
TypePar desugar((TypePar) `<Id id> \<\< <T t>`, set[Id] typePars)
	 = [TypePar] "<id> \<\< <desugarType(t, typePars)>";
  
	
TypePar desugar((TypePar) `<Id id>`, set[Id] typePars)
	 = [TypePar] "<id> \<\< Object \< \>";
	
T desugarType((T) `<Id id>`, set[Id] typePars) =
	(id in typePars) ? (T) `<Id id>` : [T] "<id>\< \>";
	
T desugarType((T) `<Id id> \< <{T ","}* typeArgs> \>`, set[Id] typePars)
	= [T] "<id> \< <visit (typeArgs){ case T ta => desugarType(ta, typePars) }> \>";

	
Expr desugar(Expr e, set[Id] typePars){ 
	Expr e1 = desugarExpr(e);
	return visit(e1){
		case T t => desugarType(t, typePars)
	};
}
 
Expr desugarExpr((Expr) `<Id receiver> <TypeArgsOptional targs> ::<Id id> <TypeArgsOptional methodtargs> (<{Expr ","}* args>)`) =
	(Expr) `<Id receiver> <TypeArgsOptional newtargs> ::<Id id> <TypeArgsOptional newmethodtargs> (<{Expr ","}* newargs>)`
	when newtargs := desugar(targs),
		 newmethodtargs := desugar(methodtargs),
		 newargs := visit(args) { case Expr arg => desugarExpr(arg) }
	;
		
Expr desugarExpr((Expr) `<Expr e>.<TypeArgsOptional targs> <Id id>(<{Expr ","}* args>)`) =
	[Expr] "<desugarExpr(e)>.<desugar(targs)> <id> (<visit(args) { case Expr arg => desugarExpr(arg) } >)"
	;	 
	
//Expr desugarExpr((Expr) `(<{FormalParam ","}* fs>) =\> { <Expr body> }`) =
//	[Expr] "(<visit(fs){ case FormalParam fp => desugar(fp, typePars)}>) =\> { <desugarExpr(body)> }"
//	;	 

default Expr desugarExpr(Expr e) = e;

TypeArgsOptional desugar((TypeArgsOptional) `\< <{T ","}* typeArgs> \>`) = (TypeArgsOptional) `\< <{T ","}* typeArgs> \>`;

default TypeArgsOptional desugar(TypeArgsOptional empty) = (TypeArgsOptional) `\< \>`;

//N desugar((N) `<Id t> \<  <{T ","}* typeArgs> \>`, set[Id] typePars) 
//	= [N] "<t> \< <for (ta <- typeArgs){><desugarType(ta, typePars)><}> \>"
//	;
	
//N desugar((N) `<Id id>`, set[Id] typePars) 
//	= (id in typePars ? [N] "<id>" : [N] "<t> \<  \>")
//	;
  
//{T ","}* desugar((N) `<Id t> \<  <{T ","}* typeArgs> \>`, set[Id] typePars) 
//	= [{T ","}*] "<for (ta <- typeArgs){><desugarType(ta, typePars)><}>";
	

 


