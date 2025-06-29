
structure Graph (α: Type u) where
  s: Nat -- number of nodes
  nonEmpty: s > 0
  vals: Vector α s
  preds: Vector (List (Fin s)) s -- predecessors
  succs: Vector (List (Fin s)) s -- successors
  startI: Fin s -- start index
  endI: Fin s -- end index

structure Node (g: Graph α) where
  idx: Fin g.s
  val: α

def Graph.node (g: Graph α)(i: Fin g.s): Node g :=
  ⟨i, g.vals[i]⟩

def Node.pred (n: Node g): List (Node g) :=
  g.preds[n.idx].map g.node
def Node.succ (n: Node g): List (Node g) :=
  g.succs[n.idx].map g.node

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
    g.preds.mapFinIdx (λ i preds fin =>
      let preds := preds.map (Fin.lift lt)
      if succI.contains ⟨i, fin⟩ then j :: preds else preds
    ) |>.push (predI.map (Fin.lift lt)),
    g.succs.mapFinIdx (λ i succs fin =>
      let succs := succs.map (Fin.lift lt)
      if predI.contains ⟨i, fin⟩ then j :: succs else succs
    ) |>.push (succI.map (Fin.lift lt)),
    g.startI.lift lt,
    g.endI.lift lt,
  ⟩

def Node.lift {g g': Graph α}(ok: g.s<g'.s)(n: Node g): Node g' :=
  {n with idx := n.idx.lift ok}

def Graph.topologicalSort (g: Graph α): Graph α := sorry
