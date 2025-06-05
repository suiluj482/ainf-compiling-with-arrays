import Polara.Utils.Print

inductive Tree (α: Type u) (β: Type v)
  | leaf: β → Tree α β
  | node: α → List (Tree α β) → Tree α β
deriving Repr, BEq

def Tree.depth: Tree α β → Nat
  | leaf _ => 1
  | node _ ts => 1 + (ts.map Tree.depth |>.foldl max 0)

def Tree.map (f: α → α')(g: β → β') : Tree α β → Tree α' β'
  | leaf v => leaf (g v)
  | node k ts => node (f k) (ts.map (λ t => t.map f g))

def Tree.pretty [ToString α][ToString β]: Tree α β → String
  | leaf v => toString v
  | node k ts => toString k ++ ": (" ++ (ts.map Tree.pretty |>.foldr (s!"{·}\n{·}") "").indent.dropRight 2 ++ ")"

def Tree.mapM [Monad m] (f: α → m α') (g: β → m β') (t: Tree α β): m (Tree α' β') :=
  match t with
  | leaf v => do let v' ← g v; return (leaf v')
  | node k ts => do
    let k' ← f k
    let ts' ← ts.map (Tree.mapM f g) |>.mapM id
    return (node k' ts')

def Tree.leafM [Monad m] (t: Tree α (m β)): m (Tree α β) :=
  match t with
  | leaf v => do return (leaf (← v))
  | node k ts => do
    let ts' ← ts.map Tree.leafM |>.mapM id
    return (node k ts')

def Tree.flatten': List α → Tree α β → List (List α × β)
  | as, leaf b => [(as, b)]
  | as, node a ts => ts.map (Tree.flatten' (a::as)) |>.foldr List.append []
def Tree.flatten: Tree α β → List (List α × β) := Tree.flatten' []

def Tree.filter (f: α → Bool) (g: β → Bool): Tree α β → Option (Tree α β)
  | leaf v => if g v then some (leaf v) else none
  | node k ts =>
    if f k then
      let ts' := ts.filterMap (Tree.filter f g)
      if ts'.isEmpty then none else some (node k ts')
    else
      none

def LTree (α: Type u) (β: Type v) := List (Tree α β)
def LTree.map (ts: LTree α β)(f: Tree α β → γ) := List.map f ts
def LTree.filter (f: α → Bool) (g: β → Bool) (ts: LTree α β): LTree α β :=
  List.filterMap (Tree.filter f g) ts
