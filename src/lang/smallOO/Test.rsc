module lang::smallOO::Test

import lang::smallOO::Syntax;
extend lang::smallOO::Checker;
extend analysis::typepal::TestFramework;

import ParseTree;

// ---- Testing ---------------------------------------------------------------
               
TModel smallOOTModelForTree(Tree pt){
    return collectAndSolve(pt, config=smallConfig());
}

TModel smallOOTModelFromName(str mname){
    pt = parse(#start[Module], |project://typepal-examples/src/lang/smallOO/<mname>.small|).top;
    return smallOOTModelForTree(pt);
}

list[Message] checkSmallOO(str mname) {
    return smallOOTModelFromName(mname).messages;
}

bool smallOOTests() {
    return runTests([|project://typepal-examples/src/lang/smallOO/tests.ttl|], 
                    #start[Module], 
                    TModel (Tree t) { return smallOOTModelForTree(t); },
                    runName = "SmallOO");
}

value main()
    = smallOOTests();