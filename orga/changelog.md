28.04 - 05.05:
- einlesen codebase, documentation und kleinere Änderungen
- basic python codegeneration
05.05 - 12.05:
- begin Jax einlesen und codegen
12.05 - 19.05:
- AINF.toTm
- AINF.valid
- basic AINF testcases
    - bug fix in polara and lean codegeneration for addition idx
19.05 - 27.05:
- fix AINF.toTm
- Tm.codegenPy, Tm.codegenJax
- start thinking about Optimal Code Motion
27.05 - 06.06:
- Verbesserung Test struktur
- Utils
- fix codegenLean (überall Except, Vector statt Array)
- Recherge und ein wenig Impl. OCM
06.06 - 16.06:
- vector operations
16.06 - 23.06:
- automatic Differentation
23.06 - 30.06:
- lin type for direvitive
- generalize over flt and lin vector operations
- test, parse and compare results of different target languages
30.6. - 06.07:
- refactoring to make transpose easier:
    - AINF and Env to be ListMaps (option HashMaps)
    - StateM to track given VPars
06.07 - 17.07:
- lt operator for aD maxf
- new Ty.ref
- transpose lin using refs
- linearity erasure
18.07 - 04.08:
- improve ref definition
05.08 - 11.08:
- fixed tests
11.08 - 18.08:
- Tm.df
18.08 - 25.08:
- Tm.dr