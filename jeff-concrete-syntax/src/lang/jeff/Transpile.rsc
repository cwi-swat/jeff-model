module lang::jeff::Transpile

import lang::jeff::Syntax;

str imports(str jeffLoc) =
	"#lang racket
	'(require redex)
	'(require (file \"<jeffLoc>/paper/jeff.rkt\"))
	'(require (file \"<jeffLoc>/paper/jeff-dyn.rkt\"))
	'
	'(caching-enabled? #f)
	'
	'";

str transpile(start[Prog] p, str jeffLoc)
	= "<imports(jeffLoc)> 
	  '(define p0 (term (add-built-in (program
	  '
	  '<(""| it + transpile(dt) + "\n" | DeclOrTest dt <- p.top.declsOrTests,
	  	(DeclOrTest) `interface <Id _> <TypeParsOptional _> <ExtendsOptional _> { <MethodHeader* _> }` := dt  )>
	  '
	  '<(""| it + transpile(dt) + "\n" | DeclOrTest dt <- p.top.declsOrTests, 
	  	(DeclOrTest) `class <Id _> <TypeParsOptional _> ( <{FormalParam ","}* _> ) <ImplementsOptional _> { <MethodDecl* _> }` := dt )>
	  '))))
	  '<(""| it + transpile(t) + "\n" | DeclOrTest dt <- p.top.declsOrTests, (DeclOrTest) `<Test t>` := dt)>
	  '
	  '(first (first (apply-reduction-relation* Red (term (((new (Main \< \>)) \< \> main) ,p0)))))";
	 
str transpile((DeclOrTest) `<Decl decl>`) = transpile(decl);

str transpile((DeclOrTest) `<Test tes>`) = transpile(tes);
	
str transpile((Decl) `class <Id c> <TypeParsOptional pars> ( <{FormalParam ","}* fs> )
					 '<ImplementsOptional ifaces> { <MethodDecl* mds> }`)
	= "(class <c> <transpile(pars)> class-args (<transpile(fs,"")>) implements <transpile(ifaces)>
	  '    <mds1>
	  ')"
	when mds1 := ("" | it + transpile(md) + "\n  "| md <- mds);
	
str transpile((Decl) `interface <Id c> <TypeParsOptional pars>
					 '<ExtendsOptional extends> { <MethodHeader* mhs> }`)
	= "(interface <c> <transpile(pars)> extends <transpile(extends)>
	  '    <mhs1>
	  ')"
	when mhs1 := ("" | it + transpile(mh) + "\n  "| mh <- mhs);
	
str transpile ((Test) `typetest <Id name> { <Expr expr> } hastype { <T t> } withenv { <{FormalParam ","}* fs> }`)
  = "(define <name> (term <transpile(expr)>))
  	'
  	'(module+ test
  	'	(test-equal
  	'		(judgment-holds (⊢ ,p0 () (<env>) ,<name> T F) T)
  	'			(list (term <transpile(t)>))))
  	'
  	'(define <name>Checking
  	'	(judgment-holds (⊢ ,p0 () (<env>) ,<name> T F) T))
  	'
  	'"
  	when env := (""| it + "(<id> <transpile(t)>)"| (FormalParam) `<T t> <Id id>` <- fs);
  	
str transpile ((Test) `typetest <Id name> { <Expr expr> } hastype { <T t> } haseffect { <EffectsOptional eo>}  	withenv { <{FormalParam ","}* fs> }`)
  = "(define <name> (term <transpile(expr)>))
  	'
  	'(module+ test
  	'	(test-equal
  	'		(judgment-holds (⊢ ,p0 () (<env>) ,<name> T F) (T F))
  	'			(list (list (term <transpile(t)>) (term <transpile(eo)>))))
  	'
  	'(define <name>Checking
  	'	(judgment-holds (⊢ ,p0 () (<env>) ,<name> T F) (T F)))
  	'
  	'"
  	when env := (""| it + "(<id> <transpile(t)>)"| (FormalParam) `<T t> <Id id>` <- fs);  	

str transpile ((Test) `evaltest <Id name> { <Expr expr> } produces { <Expr expr2> }`)
  = "(define <name> (term <transpile(expr)>))
  	'
  	'(module+ test
  	'	(test--\>\> Red
    '		(term (,<name> ,p0))
    '			(term (<transpile(expr2)> ,p0))))
	'
  	'"
  	;
  	//'(test-equal
  	//'   (apply-reduction-relation* Red (term (,<name> ,p0)))	
  	//'	(list (term <transpile(expr2)>)))
  	//'
  	

str transpile ((Test) `classtypechecks <Id name> <YesNo yesno>`)
  = "(define term-class-<name> (term (class-lookup ,p0 <name>)))
    '
  	'(module+ test
  	'	(test-equal
  	'		(judgment-holds (class-ok ,p0 ,term-class-<name>))
  	'			<boo>)) 
  	'"
  	when str boo := ((yesno := (YesNo) `yes`) ? "#t" : "#f");  
  	
str transpile ((Test) `interfacetypechecks <Id name> <YesNo yesno>`)
  = "(define term-class-<name> (term (class-lookup ,p0 <name>)))
    '
    '(module+ test
  	'	(test-equal
  	'		(judgment-holds (interface-ok ,p0 ,term-class-<name>))
  	'			<boo>)) 
  	'"
  	when str boo := ((yesno := (YesNo) `yes`) ? "#t" : "#f");  
    
	
str transpile((ImplementsOptional) `implements <{T ","}* ts>`)
	= "(<(""| it + transpile(t) + " "| T t <- ts)>)";
	
default str transpile(ImplementsOptional empty)
	= "( )";

str transpile((ExtendsOptional) `extends <{T ","}* ts>`)
	= "(<(""| it + transpile(t) + " "| T t <- ts)>)";
	
default str transpile(ExtendsOptional empty)
	= "( )";


str transpile({FormalParam ","}* fs, str initSymbol) =
	(initSymbol | it + "(" + transpile(fp) + ") " | FormalParam fp <- fs)
	;	

str transpile((TypeParsOptional) `\< <{TypePar ","}* tps> \>`)
	= "\< <(""| it + transpile(tp) + " "| TypePar tp <- tps)> \>";
	
default str transpile(TypeParsOptional empty)
	= "\< \>";

str transpile((TypePar) `<Id id>`)
	= "<id>";
	
str transpile((TypePar) `<Id id> \<\< <T t>`)
	= "(<id> \<\< <transpile(t)>)";
	
str transpile((FormalParam) `<T t> <Id id>`)
	= "<transpile(t)> <id>";
	
	
str transpile((T) `<Id id>`) = "<id>";

str transpile((T) `<Id id> \< <{T ","}* targs> \>`) = "(<id> \<<(""| it + " " + transpile(t) | t <- targs)> \>)";

str transpile((MethodDecl) `<MethodHeader mh> = <Expr e>`)
	= "(method <transpile(mh)> <transpile(e)>)";
	
str transpile((MethodHeader) `<ModOptional mo> <TypeParsOptional typePars> <T rType> <Id name> ( <{FormalParam ","}* fs> ) <EffectsOptional eff>`)
	= "(header <transpile(mo)> <transpile(typePars)> <transpile(rType)> <name> (<transpile(fs,"")>) <transpile(eff)>)";
	 
str transpile((ModOptional) `<Mod mo>`) = visit(mo){
	case (Mod) `eff`: return "effect";
	case (Mod) `native`: return "native";
};

default str transpile(ModOptional empty) = "simple";

str transpile((EffectsOptional) `(<{T ","}+ ts>)`) =
	 "(<("" | it + transpile(t) + " " | T t <- ts)>)";


default str transpile(EffectsOptional empty) = "( )";

str transpile((Expr) `with (<Expr handler>) { <Expr body> }`)
	= "(with <transpile(handler)> <transpile(body)>)";
	
str transpile((Expr) `<T t> <Id id> = <Expr e> { <Expr body> }`)
	= "(val <id> <transpile(t)> <transpile(e)> <transpile(body)>)";
	

str transpile((Expr) `new <T objectType> (<{Expr ","}* args>)`)
	= "(new <transpile(objectType)> <for (arg <- args){><transpile(arg)> <}>)";

str transpile((Expr) `<Expr receiver>.<Id field>`)
	= "(<transpile(receiver)> <field>)";

	
str transpile((Expr) `<Expr receiver>.<TypeArgsOptional targs> <Id method> (<{Expr ","}* args>)`)
	= "(<transpile(receiver)> <transpile(targs)> <method> <for (arg <- args){><transpile(arg)> <}>)";

str transpile((Expr) `<Id receiver> <TypeArgsOptional targs> ::<Id method> <TypeArgsOptional methodtargs> (<{Expr ","}* args>)`)
	= "(op <receiver> <transpile(targs)> <transpile(methodtargs)>  <method> <for (arg <- args){><transpile(arg)> <}>)";
	
str transpile((Expr) `(<Expr e>)`)
	= "<transpile(e)>";
	
str transpile((TypeArgsOptional) `\< <{T ","}* typeArgs> \>`)
	= "\< <for (t <- typeArgs){><transpile(t)> <}>\>";
	

	
str transpile(TypeArgsOptional empty)
	= "\< \>";	
 
default str transpile(Expr e) = "<e>";
