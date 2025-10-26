import Std
import Polara.Utils.Utils

structure Graph (α: Type u) where
  s: Nat -- number of nodes
  nonEmpty: s > 0
  vals: Vector α s
  pred: Vector (List (Fin s)) s -- predecessors
  succ: Vector (List (Fin s)) s -- successors
  startI: Fin s -- start index
  endI: Fin s -- end index

structure Node (g: Graph α) where
  idx: Fin g.s
  val: α

def Graph.node (g: Graph α)(i: Fin g.s): Node g :=
  ⟨i, g.vals[i]⟩

def Node.pred (n: Node g): List (Node g) :=
  g.pred[n.idx].map g.node
def Node.succ (n: Node g): List (Node g) :=
  g.succ[n.idx].map g.node

def Graph.start (g: Graph α): Node g :=
  g.node g.startI
def Graph.end (g:  Graph α): Node g :=
  g.node g.endI

instance: BEq (Node g) := ⟨(·.idx == ·.idx)⟩

def Fin.lift (ok: n<m)(i: Fin n): Fin m :=
  ⟨i.val, Nat.lt_trans i.isLt ok⟩

def Graph.addNode (g: Graph α)(val: α)(pred succ: List (Node g)): Graph α :=
  have lt: g.s < g.s + 1 := by simp
  let j: Fin (g.s + 1) := ⟨g.s, lt⟩ -- new insetion point
  let succI := succ.map (·.idx)
  let predI := pred.map (·.idx)
  ⟨
    g.s + 1,
    by simp [g.nonEmpty],
    g.vals.push val,
    g.pred.mapFinIdx (λ i pred fin =>
      let pred := pred.map (Fin.lift lt)
      if succI.contains ⟨i, fin⟩ then j :: pred else pred
    ) |>.push (predI.map (Fin.lift lt)),
    g.succ.mapFinIdx (λ i succ fin =>
      let succ := succ.map (Fin.lift lt)
      if predI.contains ⟨i, fin⟩ then j :: succ else succ
    ) |>.push (succI.map (Fin.lift lt)),
    g.startI.lift lt,
    g.endI.lift lt,
  ⟩

def Node.lift {g g': Graph α}(ok: g.s<g'.s)(n: Node g): Node g' :=
  {n with idx := n.idx.lift ok}

private partial def Std.DHashMap.topologicalSort' [BEq α] [Hashable α]
(pred: (γ: α) → F γ → List α)(m: Std.DHashMap α F)(done: List (Sigma F)): List (Sigma F) :=
  let (startNodes, m') := m.partition
    (λ key val => pred key val |>.filter m.contains |>.isEmpty)
  match startNodes.isEmpty, m'.isEmpty with
  | true, true => done
  | true, false => panic! "topologicalSort error no dag"
  | _, _ => topologicalSort' pred m' (done ++ startNodes.toList)

def Std.DHashMap.topologicalSort [BEq α] [Hashable α]
(pred: (γ: α) → F γ → List α)(m: Std.DHashMap α F): List (Sigma F) :=
  Std.DHashMap.topologicalSort' pred m []
