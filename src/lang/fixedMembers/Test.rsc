module lang::fixedMembers::Test

import lang::fixedMembers::Syntax;
extend  lang::fixedMembers::Checker;
extend analysis::typepal::TestFramework;

import ParseTree;


// ---- Testing ---------------------------------------------------------------

TModel fixedMembersTModelForTree(Tree pt, bool debug = false){
    return collectAndSolve(pt, config = fixedMembersConfig());
}

TModel fixedMembersTModelFromName(str mname, bool debug = false){
    pt = parse(#start[Program], |project://typepal-examples/src/fixedMembers/<mname>.alias|).top;
    return fixedMembersTModelForTree(pt, debug=debug);
}

bool fixedMembersTests(bool debug = false) {
    return runTests([|project://typepal-examples/src/lang/fixedMembers/fixedMembers.ttl|], 
                    #start[Program], 
                    TModel (Tree t) { return fixedMembersTModelForTree(t, debug=debug); },
                    runName = "fixedMembers");
}

bool main() = fixedMembersTests();