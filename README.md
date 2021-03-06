Problem Statement.

Implement a parser program in Java to automate counting cache misses. The input Java test cases allow for loop nests and up to 3D array references. You need to parse the .java file, collect the
necessary information, and report the cache misses for each array in each test.
You will use a popular top-down (LL) parser called ANTLR. The restricted grammar to parse the test cases is provided in a file called LoopNest.g4. You should not need to change the grammar. You can use the following instructions to generate the lexer, parser, and the syntax analysis template. Extend the necessary callbacks in Analysis.java to implement your analysis.
_______________________________________________________________
Run the program.

Use the shell script run.sh to automate using ANTLR.

-> bash run.sh TestCase1.java

To visualize the parse tree for a given test case to get a sense of what callbacks should be implemented use the following command.

->grun LoopNest tests −gui < TestCase1.java
______________________________________________________________________________________________
Implementation. 

When you compile the grammar LoopNest.g4, it will autogenerate the lexer and parser stub files. One such autogenerated file will be LoopNestBaseListener.java, which
includes empty callbacks for all rule entry and exits. For example, during parsing, whenever the parser will see a method declaration, it will call enterMethod, and after walking through all the
child nodes, it will call exitMethod. You need to extend the callback methods to record relevant information like cache dimensions and array accesses, and compute the number of cache misses.
Note that LoopNestBaseListener.java is autogenerated and will be overwritten every time the grammar is compiled. Do not directly edit LoopNestBaseListener.java. Instead, you should
extend LoopNestBaseListener.java and write your code there. In the attached files, Analysis.java is one such listener. The longest chain of rules is for the rule expression. You can simplify how you maintain information
across the rules related to different expression types. Note that the test cases will use a restricted syntax, and our simple cache model ignores the effect of local variables and arithmetic computations.
Note that you may have to substitute the values of constants during parsing. For example, if a declaration is int[][] A = new int[N][N], you will have to keep track and infer the proper value
of the array dimensions.
For every test case, you should create a HashMap<String, Long>. The keys of this map will be the
names of the arrays present in a test case. The values will be the number of cache misses.
You will create such maps for all test cases and collect them in a List<HashMap<String, Long>>.
After going through all the test cases, you will serialize this object into a file Results.obj. The
name of the file must be Results.obj. We have included a serialization wrapper in Analysis.java
(search for FIXME:).
____________________________________________________________________
Assumptions

• There are two special variables: cachePower will contain the size of the cache and blockPower
indicates the size of a cache block. The cache and block sizes are specified in powers of two,
i.e., a size of k indicates that the total cache size is 2k Bytes.

• There will be only one variable cacheType of type String in a test case. Its values can be any
of FullyAssociative, SetAssociative, and DirectMapped.

• You can assume that the input test methods will be syntactically valid Java snippets. You
need not do any error checking in your implementation.

• In all the for loops, the lower bound will always start from 0.

• There will be at most 3 dimensions for any array.

• Array dimensions will always be a power of 2.

Evaluation The output format should be strictly followed since we will use automated scripts to
evaluate the submissions. The scripts will call your program as follows.
java Driver Testcases.t
where Testcases.t is a file provided as a command line argument and will contain one or more
test cases.

ANTLR Resources Feel free to browse through additional ANTLR material on the Internet.

• https://github.com/antlr/antlr4/blob/master/doc/getting-started.md

• Tutorial 1: https://www.baeldung.com/java-antlr

• Tutorial 2: https://tomassetti.me/antlr-mega-tutorial/
