module lang::aliases::Test

import lang::aliases::Syntax;
extend  lang::aliases::Checker;
extend analysis::typepal::TestFramework;

import ParseTree;


// ---- Testing ---------------------------------------------------------------

TModel aliasesTModelForTree(Tree pt){
    return collectAndSolve(pt, config = aliasesConfig());
}

TModel aliasesTModelFromName(str mname){
    pt = parse(#start[Program], |project://typepal-examples/src/aliases/<mname>.alias|).top;
    return aliasesTModelForTree(pt);
}

bool aliasesTests(bool debug = false) {
    return runTests([|project://typepal-examples/src/lang/aliases/aliases.ttl|], 
                    #start[Program], 
                    TModel (Tree t) { return aliasesTModelForTree(t); },
                    runName = "Aliases");
}

bool main() = aliasesTests();