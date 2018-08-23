module lang::smallOO::Test

extend lang::smallOO::Checker;
extend analysis::typepal::TestFramework;

import ParseTree;

// ---- Testing ---------------------------------------------------------------
               
TModel smallOOTModelFromTree(Tree pt, bool debug){
    return collectAndSolve(pt, config=smallConfig(), debug=debug);
}

TModel smallOOTModelFromName(str mname, bool debug){
    pt = parse(#start[Module], |project://typepal-examples/src/lang/smallOO/<mname>.small|).top;
    return smallOOTModelFromTree(pt, debug);
}

list[Message] checkSmallOO(str mname, bool debug=false) {
    return smallOOTModelFromName(mname, debug).messages;
}

bool smallOOTests(bool debug = false) {
    return runTests([|project://typepal-examples/src/lang/smallOO/tests.ttl|], #start[Module], TModel (Tree t) {
        return smallOOTModelFromTree(t, debug);
    });
}

value main()
    = smallOOTests();