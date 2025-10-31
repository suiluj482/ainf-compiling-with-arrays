import Polara.Utils.Print
import Polara.Utils.Functions

inductive Tree (α: Type u) (β: Type v)
  | leaf: β → Tree α β
  | node: α → List (Tree α β) → Tree α β
deriving Repr, BEq

namespace Tree

-- def findSomeLeaf (f: β → Option γ): Tree α β → Option γ
--   | leaf v => f v
--   | node _ ts => ts.findSome? (findSomeLeaf f)

-- def findSomeNode (f: α → Option γ)(t: Tree α β): Option γ :=
--   match t with
--   | leaf _ => none
--   | node k ts => if (f k).isSome then f k else ts.findSome? (findSomeNode f)

def pretty [ToString α][ToString β]: Tree α β → String
  | leaf v => toString v
  | node k ts => toString k ++ ": {\n" ++ (ts.map pretty |>.foldr (s!"{·}\n{·}") "").indent.dropRight 2 ++ "}"

def json' [ToString α][ToString β]: Tree α β → String
  | leaf v => toString v
  | node k ts => "\"" ++ toString k ++ "\": {\n" ++ (ts.map json' |>.foldr (s!"{·},\n{·}") "").indent.dropRight 4 ++ "  \n}"

def json [ToString α][ToString β]: Tree α β → String
| t => "{\n" ++ (json' t).indent ++ "\n}"

def json2' [ToString α][ToString β]: Tree α β → String
  | leaf v => "{\n" ++ (toString v).indent ++ "\n}"
  | node k ts => "\"" ++ toString k ++ "\": [\n" ++ ((ts.map json2' |>.foldr (s!"{·},\n{·}") "").indent.dropRight 4) ++ "\n]"

def json2 [ToString α][ToString β]: Tree α β → String
  | leaf v => "{\n" ++ (toString v).indent ++ "\n}"
  | node k ts => "{\n  \"" ++ toString k ++ "\": [\n" ++ ((ts.map json2 |>.foldr (s!"{·},\n{·}") "").indent.dropRight 4).indent ++ "\n  ]\n}"

def jsonInlineObject [ToString α][ToString β]: Tree α β → String
| leaf v => toString v
| node k ts => "\"" ++ toString k ++ "\": {" ++
      (ts.map jsonInlineObject |>.foldr (s!"{·}, {·}") "").dropRight 2
    ++ "}"

def flatJsonInline: Tree String String → Tree String String
| t => Tree.leaf t.jsonInlineObject

def jsonArray' [ToString α][ToString β]: Tree α β → String
  | leaf v => toString v
  | node k ts => "\"" ++ toString k ++ "\": [\n" ++ (ts.map json |>.foldr (s!"{·},\n{·}") "").indent.dropRight 4 ++ "  \n]"

def jsonArray: Tree String String → Tree String String
| t => Tree.leaf t.jsonArray'

def jsonArrayInline' [ToString α][ToString β]: Tree α β → String
  | leaf v => toString v
  | node k ts => "\"" ++ toString k ++ "\": [\n" ++ (ts.map jsonInlineObject |>.foldr (s!"{"{"}{·}{"}"},\n{·}") "").indent.dropRight 4 ++ "  \n]"

def jsonArrayInline: Tree String String → Tree String String
| t => Tree.leaf t.jsonArrayInline'


-- #eval IO.print (Tree.node "root" [
--       Tree.node "a" [
--         Tree.leaf (1, "ok"),
--         Tree.leaf (2, "ok"),
--         Tree.node "aa" [
--           Tree.leaf (3, "ok"),
--           Tree.leaf (4, "ok"),
--         ]
--       ],
--       Tree.node "b" [
--         Tree.leaf (5, "ok"),
--         Tree.leaf (6, "ok"),
--       ],
--       Tree.leaf (7, "ok")
--     ] |>.json2)

-- #eval IO.print (Tree.node "test" [Tree.leaf "root", Tree.leaf "root"] |>.jsonArrayInline')

def depth: Tree α β → Nat
  | leaf _ => 1
  | node _ ts => 1 + (ts.map depth |>.foldl max 0)

def map (f: α → α')(g: β → β') : Tree α β → Tree α' β'
  | leaf v => leaf (g v)
  | node k ts => node (f k) (ts.map (λ t => t.map f g))

def postorder (t: Tree α β)(f: β → γ)(g: α → List γ → γ): γ :=
  match t with
  | leaf b => f b
  | node n cs => g n (cs.map (·.postorder f g))

def mutPostorder (t: Tree α β)(f: β → γ)(g: α → List γ → (α' × γ)): Tree α' β × γ :=
  match t with
  | leaf b => (leaf b, f b)
  | node a ns =>
      let (ns, cs) := ns.map (·.mutPostorder f g) |>.unzip
      let (a', c) := g a cs
      (node a' ns, c)

def mutPreorder (t: Tree α β)(f: α → γ → α' × γ)(g: β → γ → β')(s: γ): Tree α' β' :=
  match t with
  | leaf val => leaf (g val s)
  | node a ns =>
      let (a', s') := f a s
      node a' (ns.map (·.mutPreorder f g s'))

def mapM [Monad m] (f: α → m α') (g: β → m β') (t: Tree α β): m (Tree α' β') :=
  match t with
  | leaf v => do let v' ← g v; return (leaf v')
  | node k ts => do
    let k' ← f k
    let ts' ← ts.map (mapM f g) |>.mapM id
    return (node k' ts')

def leafM [Monad m] (t: Tree α (m β)): m (Tree α β) :=
  match t with
  | leaf v => do return (leaf (← v))
  | node k ts => do
    let ts' ← ts.map leafM |>.mapM id
    return (node k ts')

def flatten': List α → Tree α β → List (List α × β)
  | as, leaf b => [(as, b)]
  | as, node a ts => ts.map (flatten' (a::as)) |>.foldr List.append []
def flatten: Tree α β → List (List α × β) := flatten' []

def filter (f: α → Bool) (g: β → Bool): Tree α β → Option (Tree α β)
  | leaf v => if g v then some (leaf v) else none
  | node k ts =>
    if f k then
      let ts' := ts.filterMap (filter f g)
      if ts'.isEmpty then none else some (node k ts')
    else
      none

def FullTreeLists (α: Type u)(β: Type v): Nat → Type (max u v)
| 0 => α × List β
| n+1 => α × List (FullTreeLists α β n)

def ofLists (lists: FullTreeLists α β n): Tree α β :=
  match n with
  | 0 => Tree.node lists.fst (lists.snd.map Tree.leaf)
  | _+1 => Tree.node lists.fst (lists.snd.map ofLists)

def flattenAcc (f: γ → α → γ)(s: γ): Tree α β → List (γ × β)
  | leaf b => [(s, b)]
  | node a ts => ts.map (flattenAcc f (f s a)) |>.foldr List.append []

def prettyTable [ToString α][ToString β]: Tree α β → String
| tree => tree.flattenAcc (s!"{·}|{·}") "" |>.map (Func.tuple (s!"{·}|{·}|")) |> Print.foldLines

end Tree

def LTree (α: Type u) (β: Type v) := List (Tree α β)
def LTree.map (ts: LTree α β)(f: Tree α β → γ) := List.map f ts
def LTree.filter (f: α → Bool) (g: β → Bool) (ts: LTree α β): LTree α β :=
  List.filterMap (Tree.filter f g) ts


----Tests---
-- def tree := Tree.node "root" [
--       Tree.node "a" [
--         Tree.leaf (1, "ok"),
--         Tree.leaf (2, "ok"),
--         Tree.node "aa" [
--           Tree.leaf (3, "ok"),
--           Tree.leaf (4, "ok"),
--         ]
--       ],
--       Tree.node "b" [
--         Tree.leaf (5, "ok"),
--         Tree.leaf (6, "ok"),
--       ],
--       Tree.leaf (7, "ok")
--     ]
-- #eval tree.prettyTable
