module lang::aliases::Test

extend  lang::aliases::Checker;
extend analysis::typepal::TestFramework;

import ParseTree;


// ---- Testing ---------------------------------------------------------------

TModel aliasesTModelForTree(Tree pt, bool debug = false){
    return collectAndSolve(pt, config = aliasesConfig(), debug=debug);
}

TModel aliasesTModelFromName(str mname, bool debug = false){
    pt = parse(#start[Program], |project://typepal-examples/src/aliases/<mname>.alias|).top;
    return aliasesTModelForTree(pt, debug=debug);
}

bool aliasesTests(bool debug = false) {
    return runTests([|project://typepal-examples/src/lang/aliases/aliases.ttl|], 
                    #start[Program], 
                    TModel (Tree t) { return aliasesTModelForTree(t, debug=debug); },
                    runName = "Aliases");
}

bool main() = aliasesTests();