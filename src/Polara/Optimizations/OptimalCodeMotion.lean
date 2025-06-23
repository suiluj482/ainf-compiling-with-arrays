import Polara.Syntax.Index
import Polara.Optimizations.NbE
import Polara.Examples.Definitions

def Bnd := ((β: Ty) × Var β × Prim β)
def EnvBnd := (List EnvPart) × Bnd
-- keine Liste sondern Set da reihenfolge durch topologische sortierung wieder herstellen, aber sets als listen definiert
def AINF.toList: AINF α →  (List EnvBnd) × (VPar α)
  | .ret v => ([], v)
  | .bnd env v prim rest => rest.toList.map (⟨env.toList, _, v, prim⟩ :: ·) id

def BndTree := List (Tree EnvPart Bnd)
def AINFTree (α: Ty) := BndTree × VPar α

-- todo optimize by allowing reorderings, diffrent order to prevent all the accesss to last element maybe also better for reordering
-- scope of binding isn't limited to subnodes, yet?
def BndTree.addBnd(tree: BndTree)(envBnd: EnvBnd): BndTree :=
  (
    match List.getLast? tree, envBnd with
    | some (Tree.node envPart' tree'), (envPart :: envList, bnd) =>
        if envPart == envPart' then
          -- envBnd shares same first envPart with last child => can be added to it
          some (tree.dropLast |>.concat (Tree.node envPart' (BndTree.addBnd tree' (envList, bnd))))
        else none
    | _, _ => none
  ).getD (tree.concat (envBnd.fst.foldr (λ envPart acc => Tree.node envPart [acc]) (Tree.leaf envBnd.snd)))
termination_by envBnd.fst

def AINF.toTree (a: AINF α): AINFTree α :=
  a.toList.map (λ l => l.foldl (λ acc envBnd => acc.addBnd envBnd) []) id

partial def BndTree.toString(tree: BndTree): String :=
  match tree with
  | [] => ""
  | node :: tree' => (
      match node with
      | Tree.leaf ⟨β, v, prim⟩ => s!"let {v.pretty} := {prim.pretty}"
      | Tree.node envPart tree'' => s!"({EnvPart.toString envPart}{BndTree.toString tree'' |>.indent.dropRight 2})"
    ) ++ "\n" ++ BndTree.toString tree'
def AINFTree.toString: AINFTree α → String
  | (tree, v) => tree.toString ++ v.pretty
instance: ToString (AINFTree α) := ⟨AINFTree.toString⟩

#eval (fun' (x: VPar Ty.nat) => (tlitn 2 + tlitn 2 + tlitn 2)).toAINF.toTree
#eval cseTest1.toAINF.cse.toTree

open Notations Ty Const0 Const1 Const2 Prim AINF EnvPart

def test: AINF Ty.nat := (
  let'' [] in x0 := plitn 42;
  let'' [EnvPart.func Ty.nat i0] in x1 := cst2 addn (.v (x0: Var nat)) (.p (i0: Par nat));
  -- redundancy by performing x1(i0) twice ???
  let'' [EnvPart.func Ty.nat i0] in x2 := cst2 addn (.v (x1: Var nat)) (.v (x1: Var nat));
  let'' [] in x3 := fun'' (i0: Par Ty.nat), (.v (x2: Var nat));

  AINF.ret (VPar.v x0)
)

-- notes
-- Ergänzbare Vorbedingungen:
-- - funs ganz außen für jede einzeln
-- - ite vor alles for

-- arrays -> loops ~> mutations <-> parallel vector ops?
-- ite -> branches

-- mittelding ite zu kanten, arrays als ainf

-- Will OCM move computations into othervise empty ifs?

inductive Exit where -- return type?
  | basic: Exit -- one continuation
  | ite: VPar Ty.nat → VPar α → VPar α → Exit -- branching

  -- -- statdessen in env nur forc halten?
  -- | bld: Par (Ty.idx n) → VPar α → Exit -- array
  -- | app: VPar (α~>β) → VPar α → Exit -- function call

def Comp := Prim
-- inductive Comp : Ty → Type
--   | cst0 : Const0 α → Comp α
--   | cst1 : Const1 α₁ α → VPar α₁ → Comp α
--   | cst2 : Const2 α₁ α₂ α → VPar α₁ → VPar α₂ → Comp α -- includes app
--   | err : Comp α
--   | var : VPar α → Comp α
--   | abs : Par α → VPar β → Comp (α ~> β)
--   | bld : Par (idx n) → VPar α → Comp (array n α)

-- Motion Candidate
def T := (α: Ty) × Var α × Comp α -- v := t

structure Node (s: Nat) where
  predI: List (Fin s)
  succI: List (Fin s)

  bnds: List T -- forbid ite, for, fun??
  exit: Exit
structure Graph (α: Ty) where
  s: Nat -- number of nodes
  nonEmpty: s > 0
  nodes: Vector (Node s) s
  ret: VPar α -- return value of the graph
  -- s: Node
  -- e: Node

def Node.pred (g:  Graph α)(n: Node g.s): List (Node g.s) :=
  n.predI.map (λ i => g.nodes[i])
def Node.succ (g:  Graph α)(n: Node g.s): List (Node g.s) :=
  n.succI.map (λ i => g.nodes[i])

def Graph.startI (g:  Graph α): Fin g.s :=
  ⟨0, by simp [g.nonEmpty]⟩
def Graph.endI (g:  Graph α): Fin g.s :=
  ⟨g.s-1, by simp [g.nonEmpty, @Nat.sub_lt g.s 1 g.nonEmpty (by trivial)]⟩
def Graph.start (g:  Graph α): Node g.s :=
  g.nodes[g.startI]
def Graph.end (g:  Graph α): Node g.s :=
  g.nodes[g.endI]

def Fin.lift (ok: n<m)(i: Fin n): Fin m :=
  ⟨i.val, Nat.lt_trans i.isLt ok⟩
def Node.lift (ok:s<v)(n: Node s): Node v :=
  { predI := n.predI.map (Fin.lift ok),
    succI := n.succI.map (Fin.lift ok),
    bnds := n.bnds,
    exit := n.exit }
def Graph.addNode (g: Graph α)(m: Node (g.s+1)): Graph α :=
  have tmp: g.s < g.s + 1 := by simp
  let j. Fi := g.s + 1 -- new insetion point
  ⟨g.s + 1, by simp [g.nonEmpty],
    g.nodes.mapIdx (λ i n =>
      let i: Fin (g.s+1) := ⟨i, by sorry⟩
      let n := n.lift tmp
      let succ := if m.succI.contains i then j :: n.predI else n.predI
      n
    ) -- fix links
    |>.push m,
    g.ret⟩

-- def Prim.toComp: Prim α → (Comp α ⊕ Exit)
--   | .cst0 c       => Sum.inl <| Comp.cst0 c
--   | .cst1 c v     => Sum.inl <| Comp.cst1 c v
--   | .cst2 c v1 v2 => Sum.inl <| Comp.cst2 c v1 v2
--   | .err          => Sum.inl <| Comp.err
--   | .var v        => Sum.inl <| Comp.var v
--   | .abs p v      => Sum.inl <| Comp.abs p v
--   | .ite cond a b => Sum.inr <| Exit.ite cond a b
--   | .bld p v      => Sum.inl <| Comp.bld p v

def AINF.toCFG (a: AINF α):  Graph α :=
  match a with
  | .ret v => ⟨1 ,(by simp),
      Vector.mk [⟨[], [], [], Exit.basic⟩].toArray (by simp),
      v
    ⟩
  | .bnd env v prim rest =>
    let g := rest.toCFG
    -- let v :=
    have tmp: g.s < g.s + 1 := by simp
    ⟨g.s + 1, by simp [g.nonEmpty],
      g.nodes.map (Node.lift tmp) |>.push ⟨
        [], [], [], Exit.basic
      ⟩,
      g.ret,
    ⟩


-- beweis f immer was ändert in eine Richtung #ausdrücke ^ 2 (count false werte)
partial def fixPointSolution [BEq α](f: α → α)(s: α): α :=
  if f s == s then s
  else fixPointSolution f (f s)

partial def tillUnchanged (f: α → α × Bool)(s: α): α :=
  let (s', changed) := f s
  if !changed then s'
  else tillUnchanged f s'


def Node.transp (n: Node s) (t: T): Bool :=
  -- n is transparent for t
  true -- always true because no modifications? maybe in false for index for loops
  -- also when before definition??

def Node.nComp (n: Node s) (t: T): Bool :=
  -- n has an entry computation of t
  -- todo
  true

def Node.xComp (n: Node s) (t: T): Bool :=
  -- n has an exit computation of t
  false

---- Safety Analyses
-- Down-Safety Analysis

def T.ndSafe (g:  Graph α)(t: T)(xdSafe: Vector Bool g.s): Vector Bool g.s :=
  Vector.ofFn (λ i =>
    let n := g.nodes[i]
    Node.nComp n t || Node.transp n t && xdSafe[i]
  )
def T.xdSafe (g:  Graph α)(t: T)(ndSafe: Vector Bool g.s): Vector Bool g.s :=
  Vector.ofFn (λ i =>
    let n := g.nodes[i]
    Node.xComp n t || if i == g.endI
      then false
      else (n.succI.all (λ mI => ndSafe[mI]))
  )
def T.dSafe'(g:  Graph α)(t: T): Vector Bool g.s × Vector Bool g.s :=
  fixPointSolution
    (λ ⟨ndSafe, xdSafe⟩ => (T.ndSafe g t xdSafe, T.xdSafe g t ndSafe))
    (Vector.replicate g.s false, Vector.replicate g.s false)

-- Up-Safety
def T.nuSafe (g:  Graph α)(t: T)(xuSafe: Vector Bool g.s): Vector Bool g.s :=
  Vector.ofFn (λ i =>
    let n := g.nodes[i]
    if i == g.startI
      then false
      else n.predI.all (λ mI => Node.xComp g.nodes[mI] t || xuSafe[mI])
  )
def T.xuSafe (g:  Graph α)(t: T)(nuSafe: Vector Bool g.s): Vector Bool g.s :=
  Vector.ofFn (λ i =>
    let n := g.nodes[i]
    Node.transp n t && (Node.nComp n t || nuSafe[i])
  )
def T.uSafe'(g:  Graph α)(t: T): Vector Bool g.s × Vector Bool g.s :=
  fixPointSolution
    (λ ⟨nuSafe, xuSafe⟩ => (T.nuSafe g t xuSafe, T.xuSafe g t nuSafe))
    (Vector.replicate g.s false, Vector.replicate g.s false)

---- Earliestness
def T.earlist (g:  Graph α)(t: T): Vector Bool g.s × Vector Bool g.s :=
  let (ndSafe', xdSafe') := T.dSafe' g t
  let (nuSafe', xuSafe') := T.uSafe' g t
  (
    -- n
    Vector.ofFn (λ i =>
      let n := g.nodes[i]
      ndSafe'[i] && n.predI.all (λ mI =>
        xuSafe'[mI] || xdSafe'[mI]
      )
    ),
    -- x
    Vector.ofFn (λ i =>
      let n := g.nodes[i]
      xdSafe'[i] && !(Node.transp n t)
    )
  )

---- Delayability Analysis


---- Computation of Latestness


---- Isolation Analysis

-- Insertion and Replacement Points of the Lazy Code Motion Transforamtion
