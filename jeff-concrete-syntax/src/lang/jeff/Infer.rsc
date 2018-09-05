module lang::jeff::Infer

import lang::jeff::Syntax;
import Set;
import List;
import Relation;
import IO;
import util::Maybe;

bool isEffectPolymorphic(Prog p, (T) `<Id typeName> \< <{T ","}* typeArgs> \>`, Id method){
	//println("iseffectpolymprphic <typeName>.<method>");
	visit(p){
		case (Decl) `class <Id c> <TypeParsOptional tpars> ( <{FormalParam ","}* fs> ) <InheritsOptional s> <ImplementsOptional ifaces> {<MethodDecl* mds>}`:{
			if ("<typeName>" == "<c>"){
				visit((Decl) `class <Id c> <TypeParsOptional tpars> ( <{FormalParam ","}* fs> ) <InheritsOptional s> <ImplementsOptional ifaces> {<MethodDecl* mds>}`){
					case (MethodHeader) `<TypeParsOptional typePars> <ModOptional mo> <T rType> <Id name> ( <{FormalParam ","}* fs> ) ()`:{
						if ("<method>" == "<name>"){
							return true;
						}
					}
				};
			};
		}	
		case (Decl) `interface <Id c> <TypeParsOptional tpars> <ExtendsOptional s> {<MethodHeader* mhs>}`:{
			if ("<typeName>" == "<c>"){
				visit((Decl) `interface <Id c> <TypeParsOptional tpars> <ExtendsOptional s> {<MethodHeader* mhs>}`){
					case (MethodHeader) `<TypeParsOptional typePars> <ModOptional mo> <T rType> <Id name> ( <{FormalParam ","}* fs> ) ()`:{
						if ("<method>" == "<name>"){
							return true;
						}
					}
				};
			};
		}	
	};
	println(false);
	return false;
}

start[Prog] infer(start[Prog] p) = visit(p){
	case (Decl) `class <Id c> ( <{FormalParam ","}* fs> ) <InheritsOptional s> <ImplementsOptional ifaces> {<MethodDecl* mds>}` 
		=> inferClass(p.top, typenv, (Decl) `class <Id c> \< \> ( <{FormalParam ","}* fs> ) <InheritsOptional s> <ImplementsOptional ifaces> {<MethodDecl* mds>}`) 
		when typenv := {<id, t>|(FormalParam) `<T t> <Id id>` <- fs} + <(Id)`this`, [T] "<c> \< \>" >
	case (Decl) `class <Id c> \< <{TypePar ","}* tps> \> ( <{FormalParam ","}* fs> ) <InheritsOptional s> <ImplementsOptional ifaces> {<MethodDecl* mds>}` 
		=> inferClass(p.top, typenv, (Decl) `class <Id c> \< <{TypePar ","}* tps> \> ( <{FormalParam ","}* fs> ) <InheritsOptional s> <ImplementsOptional ifaces> {<MethodDecl* mds>}`) 
		when ts := intercalate(", ", ["<id>" | (TypePar) `<Id id> \<\< <T t>` <- tps]), // assumes desugaring
		     typenv := {<id, t>|(FormalParam) `<T t> <Id id>` <- fs} + <(Id)`this`, [T] "<c> \< <ts> \>" >
};
	
Decl inferClass(Prog p, rel[Id, T] typenv, Decl decl) = visit(decl){
	case (MethodDecl) `<TypeParsOptional tpars> <ModOptional mo> <T rType> <Id name> ( <{FormalParam ","}* fs> ) <EffectsOptional eff> = <Expr body>` 
	 	=> (MethodDecl) `<TypeParsOptional tpars> <ModOptional mo> <T rType> <Id name> ( <{FormalParam ","}* fs> ) <EffectsOptional eff1> = <Expr body>`
		when typenv1 := {<id, t>|(FormalParam) `<T t> <Id id>` <- fs},
			 eff1 := infer(p, typenv1 + typenv, body, eff),
			 bprintln("inferred: <eff1>")
	
};

T getFieldType(Prog p, T classType, T fieldType){
	visit(p){
		case (Decl) `class <Id c> <TypeParsOptional tpars> ( <{FormalParam ","}* fs> ) <InheritsOptional s> <ImplementsOptional ifaces> {<MethodDecl* mds>}`:{
			if ("<classType>" == "<c>")
				return getOneFrom([t|(FormalParam) `<T t> <Id id>` <- fs, "<t>" == "<fieldType>"]);
		} 
	};
	throw "Wrong field";
}

Maybe[tuple[Id, list[Id]]] getReceiverDependencies(rel[Id, T] typenv, (Expr) `<Id receiver>.<Id method> <TypeArgsOptional targs> ( < {Expr ","}* args > )`) = 
	(receiver in domain(typenv)) ? just(<receiver, [method]>) : nothing();
	
Maybe[tuple[Id, list[Id]]] getReceiverDependencies(rel[Id, T] typenv, (Expr) `this.<Id method> <TypeArgsOptional targs> ( < {Expr ","}* args > )`) = 
	just(<(Id)`this`, [method]>);
	
Maybe[tuple[Id, list[Id]]] getReceiverDependencies(rel[Id, T] typenv, (Expr) `<Expr e>.<Id method> <TypeArgsOptional targs> ( < {Expr ","}* args > )`){ 
	if (just(<rcv, ids>) := getReceiverDependencies(typenv, e))
		return just(<rcv, ids + [method]>);
	else
		return nothing();
}		

default Maybe[tuple[Id, list[Id]]] getReceiverDependencies(rel[Id, T] typenv, Expr e) = nothing();
		
rel[Id, list[Id]] getDependencies(rel[Id, T] typenv, Expr e){ // assuming only concrete effects
	rel[Id, list[Id]] dependencies = {};
	visit(e){
		case (Expr) `<Expr e>.<Id method> <TypeArgsOptional targs> ( < {Expr ","}* args > )`:{
			if (just(<rcv, ids>) := getReceiverDependencies(typenv, (Expr) `<Expr e>.<Id method> <TypeArgsOptional targs> ( < {Expr ","}* args > )`))
				dependencies += <rcv, ids>;
		}
	};
	return dependencies;
}

list[str] depsToStr(rel[Id, list[Id]] deps) = ([] | it + ["<id>.<intercalate(".", ["<m>" | m <- ms])>"]| <id, ms> <- deps);

EffectsOptional infer(Prog p, rel[Id, T] typenv, Expr e, (EffectsOptional) `()`) =
 	(EffectsOptional) `()`;

EffectsOptional infer(Prog p, rel[Id, T] typenv, Expr e, (EffectsOptional) `(pure, <{ T "," }* ts>)`) =
 	infer(p, typenc, e, (EffectsOptional) `(pure(), <{ T "," }* ts>)`);
 
EffectsOptional infer(Prog p, rel[Id, T] typenv, Expr e, (EffectsOptional) `(pure(), <{ T "," }* ts>)`) =
 	[EffectsOptional] "(pure(<intercalate(", ", deps)>), <ts>)"
 	when deps := depsToStr(getDependencies(typenv, e));
 	
EffectsOptional infer(Prog p, rel[Id, T] typenv, Expr e, (EffectsOptional) `(pure)`) =
 	infer(p, typenc, e, (EffectsOptional) `(pure())`);
 	
EffectsOptional infer(Prog p, rel[Id, T] typenv, Expr e, (EffectsOptional) `(pure())`) =
 	[EffectsOptional] "(pure(<intercalate(", ", deps)>))"
 	when deps := depsToStr(getDependencies(typenv, e)),
 		 bprintln("(pure(<intercalate(", ", deps)>))")
 		 ;
 
  