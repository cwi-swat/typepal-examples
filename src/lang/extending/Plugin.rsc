module examples::extending::Plugin

import ParseTree;
import util::IDE;
import IO;
import ValueIO;


import analysis::typepal::TypePal;

import examples::extending::Syntax;
import examples::extending::Checker;

import examples::extending::Test;

data MtlManifest 
 = mtlManifest(
      list[str] Source = ["src"],
      list[str] Libraries = ["lib"],
      str Target = "generated",
      str DockerImage = "xlinqreg.azurecr.io/openitems-maverick-develop:latest"
    );        
 

private loc project(loc file) {
   assert file.scheme == "project";
   return |project:///|[authority = file.authority];
}



data FMSummary(
    map[loc, AType] types = (),        // maps locations in the tree to control types
    rel[loc from, loc to] useDef = {}, // relation frome each use to its definition
    set[Message] messages = {}        // messages generated by checker
) = \module();

FMSummary makeSummary(loc root, TModel model)  {
    return \module(
        types=getFacts(model), 
        useDef=getUseDef(model), 
        messages={*getMessages(model)}
    );
}

FMSummary makeFMSummary(Tree t) 
    = makeSummary((t@\loc).top, extendingTModelForTree(t, debuig = true));

Tree checkExtending(Tree input)
    = check(makeFMSummary, input);    

 

Tree check(FMSummary (Tree) calcSummary, Tree input) {
  println("Checking: <input@\loc>"); 
  summary = calcSummary(input);
  types = summary.types;
  
  return input[@messages=summary.messages]
              [@hyperlinks=summary.useDef]
              [@docs=(l:"<prettyAType(types[l])>" | l <- types)]
         ;
} 



Contribution commonSyntaxProperties 
    = syntaxProperties(
        fences = {<"{","}">,<"(",")">}, 
        lineComment = "//", 
        blockComment = <"/*","*","*/">
    );

start[Program] parseXTProgram(str s, loc l) = parse(#start[Program], s, l);


void registerExtending() {
    registerLanguage("extending", "xt", parseXTProgram);
    registerContributions("extending", {
        commonSyntaxProperties,
        treeProperties(hasQuickFixes = false),
        annotator(checkExtending)
    });
    
}

void main() {
	registerExtending();
}