module lang::extending::Test

import lang::extending::Syntax;
extend lang::extending::Checker;

extend analysis::typepal::TestFramework;

import ParseTree;


// ---- Testing ---------------------------------------------------------------

TModel extendingTModelForTree(Tree pt, bool debug = false){
    return collectAndSolve(pt, config = extendingConfig());
}

TModel extendingTModelFromName(str mname, bool debug = false){
    pt = parse(#start[Program], |project://typepal-examples/src/lang/extending/<mname>.xt|).top;
    return extendingTModelForTree(pt, debug=debug);
}

bool extendingTests(bool debug = false) {
    return runTests([|project://typepal-examples/src/lang/extending/extending.ttl|], 
                    #start[Program], 
                    TModel (Tree t) { return extendingTModelForTree(t, debug=debug); },
                    runName = "extending");
}

bool main() = extendingTests();