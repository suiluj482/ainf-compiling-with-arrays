import Polara.Syntax.All

abbrev BndPrim := @Sigma (Sigma Var) (λ ⟨α,_⟩ => Prim α)
abbrev BndTree := LTree EnvPart BndPrim
def AINFTree (α: Ty) := BndTree × VPar α

partial def BndTree.toString: BndTree → String
| [] => ""
| node :: tree =>
    let nodeS := match node with
    | Tree.leaf ⟨⟨_,v⟩,prim⟩ => s!"let {v} := {prim}"
    | Tree.node envPart tree' =>
        let treeS := BndTree.toString tree' |>.indent.dropRight 2
        s!"{envPart}:\n{treeS}"
    s!"{nodeS}\n{BndTree.toString tree}"
def AINFTree.toString: AINFTree α → String
| (tree, v) => s!"{tree.toString}{v}"
instance: ToString (AINFTree α) := ⟨AINFTree.toString⟩


-- Operation deckt eine Env?
-- Analyse auf variablen, die nur innerhalb der env verwendet werden

-- todo optimize by allowing reorderings, diffrent order to prevent all the accesss to last element maybe also better for reordering
-- scope of binding isn't limited to subnodes, yet?
-- def BndTree.addBnd(tree: BndTree)(envBnd: EnvBnd): BndTree :=
--   (
--     match List.getLast? tree, envBnd with
--     | some (Tree.node envPart' tree'), (envPart :: envList, bnd) =>
--         if envPart == envPart' then
--           -- envBnd shares same first envPart with last child => can be added to it
--           some (tree.dropLast |>.concat (Tree.node envPart' (BndTree.addBnd tree' (envList, bnd))))
--         else none
--     | _, _ => none
--   ).getD (tree.concat (envBnd.fst.foldr (λ envPart acc => Tree.node envPart [acc]) (Tree.leaf envBnd.snd)))
-- termination_by envBnd.fst

-- def AINF.toTree (a: AINF α): AINFTree α :=
--   a.toList.map (λ l => l.foldl (λ acc envBnd => acc.addBnd envBnd) []) id


-- whats official semantic of envParts at the order at which they "need" to be destructed
--   probably none, that makes fusion harder

-- conservative Annahme nur terme die nur in env gebraucht werden fusen
-- eventuell mehrere exits als tuple rausschleusen, wirklich effizienter?

-- womit kommt das target klar?, ist unser Term eine einschränkung mit nur einem ergebnis eines fors?

open Ty
def x0: Var nat := .mk 0
def x1: Var flt := .mk 1
def x2: Var flt := .mk 2
def x3: Var flt := .mk 3
def x4: Var flt := .mk 4
def x10: Var (flt.array 10) := .mk 10
def x11: Var (flt.array 10) := .mk 11

def i0: Par (idx 10) := .mk 0
def i1: Par (idx 10) := .mk 0
#eval ((
  [
    let'' [] in x3 := .cst0 (.litf 0.1),
    let'' [.forc 10 i0, .forc 10 i1] in x0 := .cst1 .i2n (.p i0),
    let'' [.forc 10 i0, .forc 10 i1] in x1 := .cst1 .n2f (.v x0),
    -- array array ...
    let'' [.forc 10 i1] in x10 := for'' i0:10, (.v x1),
    let'' [.forc 10 i0] in x10 := for'' i1:10, (.v x1),

    let'' [] in x4 := .cst0 (.litf 0.2),

    let'' [.forc 10 i0] in x2 := .cst2 (.arithOp .add) (.v x1) (.v x3),

    -- here two exits
    let'' [] in x10 := for'' i0:10, (.v x1),
    let'' [] in x11 := for'' i0:10, (.v x2),
  ],
  (.v x1)
): AINF flt)

-- #eval (for' i: idx ⟨10, => i.i2n.n2f + 2)
