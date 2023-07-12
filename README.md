# Anticipated_Expression_Analysis
- An expression B op C is very busy or anticipated at a point p, if along every path from p, we come to a computation of
B op C before any computation of B or C.
- Useful in code hoisting and partial redundancy elimination.
- Hoisting refers to the process of moving instructions that are common to multiple basic blocks to a higher level in the program's control flow.
- Code hoisting does not reduce time but reduces space.
- final_ae.cpp corresponds to the optimisation pass written in the LLVM compiler that performs Anticipated Expression Analysis on Intermediate Representation(IR) of code and appropriately performs code hoisting.


## High level idea of how anticipated expressions are found :
- V_USE and V_DEF is calculated as mentioned above.
- Iteratively calculated IN and OUT of each block until there is no change in IN and OUT.
- IN and OUT at each block can be used to find the anticipated expressions and correspondingly created new instruction and hoisted the expressions appropriately.

## Notes
- When there are expressions that include more than 2 operands`(x*x+x)` and it was anticipated, then LLVM IR converts them into two binary operations. First we'll find `x*x` as anticipated expression and hoist that expression. Now say `x*x+x` becomes `a+x` in updated IR and this time we find `a+x` as anticipated and hoist appropriately.
