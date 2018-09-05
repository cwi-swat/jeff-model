module Plugin

import util::IDE;
import ParseTree;
import lang::jeff::Syntax;
import lang::jeff::Desugar;
import lang::jeff::Transpile;
import IO;

private str JEFF_LANG = "jeff";
private str JEFF_EXT = "jeff";
private str JEFF_LOC = "/Users/pablo/git/jeff/jeff-semantics/src";

void main() {
  registerLanguage(JEFF_LANG, JEFF_EXT, start[Prog](str src, loc l) {
    return parse(#start[Prog], src, l);
  });
  
  contribs = {
  	builder(set[Message] (start[Prog] pt) {
    	//src = infer(desugar(pt));
    	//inferredLoc = (pt@\loc)[extension="inferred.jeff"].top;
    	//println(inferredLoc);
    	//writeFile(inferredLoc, inferredSrc);
    	racketSrc = transpile(desugar(pt), JEFF_LOC);
    	racketLoc = (pt@\loc)[extension="rkt"].top;
    	writeFile(racketLoc, racketSrc);
    	return {};
    })};
    
   registerContributions(JEFF_LANG, contribs);
}