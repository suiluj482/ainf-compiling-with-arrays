# Bachelor thesis
This repository contains the source code for my bachelor thesis with the title: AiNF Automatic Differentiation, Optimizations and Codegeneration.

## Requirements
- Lean https://lean-lang.org/download/

For executing generated code:
- Python
- JAX https://docs.jax.dev/en/latest/installation.html#installation

## Structure
Throughout the folder All.lean files are used to import everything from a folder. They are auto generated with a small helper script https://github.com/suiluj482/leanHelpers.

There are 6 main folders:
- Utils contains general utilities not directly tied to the domain of this work
- Syntax defines the simple language Polara, the intermediate representation AiNF and utilities for them
- AD implements automatic differentiation techniques for Polara
- Optimizations defines conversions to and from AiNF, Optimizations and the optimization pipelines
- Codegeneration contains the code generation, execution of the generated code and parsing of the results
- Finally Tests contains examples, test cases the code for executing tests and main methods for it

## Abstract 
Linear algebra computations form the foundation of neural networks. For training
neural networks, gradient descent plays a central role. Automatic differentiation has
emerged as a source code transformation to compute these gradients. Often, automatic
differentiation is implemented for imperative programming languages.

This thesis implements automatic differentiation for the simple functional language
Polara, and provides a practical explanation for the used algorithm by Vákár and Smed-
ing [9]. Polara was introduced by Richter et al. [10]. It treats arrays as eagerly evaluated
functions. Together with Polara they proposed an optimization consisting of typed par-
tial evaluation and common subexpression elimination. The latter is performed on the
novel intermediate representation indexed administrative normal form (Ai NF), which
is maximally fissioned regarding loops, functions and if expressions. This thesis imple-
ments loop invariant code motion, loop unswitching, automatic differentiation and dead
code elimination for Ai NF and proposes a fusion algorithm to destruct it.

A case study of a simple multilayer perceptron shows that typed partial evaluation is
effective in simplifying code transformed by automatic differentiation and that fusion is
essential for performance when destructing Ai NF.