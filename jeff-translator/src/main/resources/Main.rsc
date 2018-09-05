module Main

import List;
import IO;
import ParseTree;
import lang::jeff::Syntax;
import lang::jeff::Desugar;
import lang::jeff::Transpile;

public void transpile(loc racketDir, loc src) {
	start[Prog] pt = parse(#start[Prog], src);
	// TODO check that extension is .jeff
	racketSrc = lang::jeff::Transpile::transpile(desugar(pt), racketDir.path);
	loc tgt = src[extension="rkt"];
    writeFile(tgt, racketSrc);
}
