module lang::untypedFun::Test

import lang::untypedFun::Syntax;

extend lang::untypedFun::Checker;
extend analysis::typepal::TestFramework;

// ----  Examples & Tests --------------------------------

private Expression sample(str name) = parse(#start[Expression], |project://typepal-examples/src/lang/untypedFun/<name>.ufun|).top;

list[Message] untypedFunCheck(str name){
    return untypedFunTModelForTree(sample(name)).messages;
}

TModel untypedFunTModelForTree(Tree pt)
    = collectAndSolve(pt);

bool untypedFunTests()
    = runTests([|project://typepal-examples/src/lang/untypedFun/tests.ttl|], #Expression, untypedFunTModelForTree, runName="UntypedFun");

value main() = untypedFunTests();
