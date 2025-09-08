# Goal
- automatic differentiation 
    - remove overhead, optimierung code generierung jax

- performance test generated code

# Todo

## Write -- top priority
- tu darmstadt template inkompatibel, (koma script template?), begin article
- infos wie in tu darmstadt template

- (latex bestimmtes griechisch model in monospace font)
- (common errors, keine _ kein # im text)

## aD -- top priority
- can reverse be done by transpose? (explizitly model LFun?)


## Optimizations
- array operations
    - transform to array operations where possible (NbE)
- matrix multiplication
- fusion
    - operations on arrays functions
    - multiparameter functions
- CFG code motion?

## Tests
    - more testcases
        - testFall (func eher hintenanstellen)
        - forc tupel ?
        - func forc ifc forc
    - testing
        - args?
        - safe files on error (runners need full tree path)
        - get jaxpr
- bigger full example
    - multilayer perceptron (+use aD)

    (- https://arxiv.org/pdf/2505.08906 deren benchmarks laufen lassen (einfachste in Polara)
    - futhark vermutlich am ähnlichsten)


# Secondary ideas:
- make var type dependent of env, to allow implizit drop?
- macros for notations: https://leanprover-community.github.io/lean4-metaprogramming-book/main/08_dsls.html
