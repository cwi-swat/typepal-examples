module lang::modules::Plugin

import ParseTree;
import util::IDE;
import IO;
import ValueIO;


import analysis::typepal::TypePal;

import lang::modules::Syntax;
import lang::modules::Checker;

import lang::modules::Test;

private loc project(loc file) {
   assert file.scheme == "project";
   return |project:///|[authority = file.authority];
}

Tree checkModules(Tree input) {
  println("Checking: <input@\loc>"); 
  model = modulesTModelFromTree(input); // your function that collects & solves
  types = getFacts(model);
  
  return input[@messages={*getMessages(model)}]
              [@hyperlinks=getUseDef(model)]
              [@docs=(l:"<prettyPrintAType(types[l])>" | l <- types)]
         ; 
} 



Contribution commonSyntaxProperties 
    = syntaxProperties(
        fences = {<"{","}">,<"(",")">}, 
        lineComment = "//", 
        blockComment = <"/*","*","*/">
    );

start[Program] parseModulesProgram(str s, loc l) = parse(#start[Program], s, l);


void registerModules() {
    registerLanguage("modules", "modules", parseModulesProgram);
    registerContributions("modules", {
        commonSyntaxProperties,
        treeProperties(hasQuickFixes = false),
        annotator(checkModules)
    });
    
}

void main() {
	registerModules();
}
