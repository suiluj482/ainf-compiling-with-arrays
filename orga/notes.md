# Optimizations

## SSA - Single Static Assignment
- each var assigned once
- primitive computations

## AINF - Indexed Administrative normal form
- SSA
- maximally fission

existierende AINF cse impl., removes full redundancys und bei ifs auch partial redundancies
z.B. 
    - durch env.upgrade wird etwa eine partiell redundante operation aus einem if rausgezogen
    - OCM würde stattdessen im anderen Fall des if's die Rechnung ergänzen
    => AINF CSE achtete auf lexikalisches Vorkommen in AINF, OCM auf Vorkommen in möglichen CFG Pfaden
    macht OCM CSE redundant???

OCM
- reinziehen auch in ifs nach unten, da nur ein pfad ausgeführt
- rausziehen aus for, da mehrfach ausgeführt
- rausziehen aus fun, wenn mehrfach ausgeführt

does OCM assumes no end of scopes z.B. when leaving if part? seems like it 
SSA book uses φ to merge after different if cases


## CSE - Common Subexpression Elimination
- remove full redundant computations

## OCM - Optimal Code Motion
- minimize number computations ~ PRE
- suppress unnecesary code motion ~ minimize lifetimes

## Partial Redundancy Elimination
- alos remove partial redundancies

## Redundancy Elimination
- full redundancy ~ CSE
- partial redundancy