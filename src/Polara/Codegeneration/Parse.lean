import Polara.Syntax.All

@[reducible]
def Ty.val: Ty → Type
| .nat => Nat
| .flt => Float
| .lin => Float
| .unit => Unit
| .idx n => Fin (n+1)
| α ×× β => α.val × β.val
| .array n α => Vector α.val n
| _ ~> _ => Unit
| ref _ => panic! "ref not supported"

def Ty.val? (α: Ty) := Option α.val

def String.unwrap (st: String)(s e: String): Option String :=
  if st.startsWith s && st.endsWith e then
    st.drop s.length |>.dropRight e.length
  else none
private def String.accept (s: String)(pre: String): Option String :=
  if s.startsWith pre then
    (s.drop pre.length).trim
  else none

private def String.firstVal(s: String)(f: String → Option α): Option (α × String) :=
  let p := s.find ([' ', ',', ']', ')'].contains ·)
  f (s.extract 0 p) |>.map (·, s.extract p ⟨s.length⟩ |>.trim)

private def Vector.ofStrm (seed: α)(f: α → Option (β × α))(n: Nat): Option ((Vector β n) × α) :=
  match n with
  | 0 => some (⟨#[], by simp⟩, seed)
  | 1 => do return (←f seed).map (⟨#[·], by simp⟩) id
  | n+1 => do
      let (v, seed) ← Vector.ofStrm seed f n
      let (a, seed) ← f seed
      return (v.push a, seed)

def toNat'? (s: String): Option Nat :=
  if s == "True" then some 1
  else if s == "False" then some 0
  else if s.endsWith ".0" then
    s.dropRight 2 |>.toNat?
  else
    s.toNat?

def Ty.parse' (α: Ty)(s: String): Option (α.val × String) :=
  let s := s.trim
  match α with
  | .nat => s.firstVal toNat'?
  | .flt => s.firstVal (·.toFloat?)
  | .lin => s.firstVal (·.toFloat?)
  | .unit => if s == "()" then some ((), s.drop 2) else none
  | .idx _ => s.firstVal (·.toFin?)
  | α ×× β => do
      let s ← s.accept "("
      let (a, s) ← α.parse' s
      let s ← s.accept ","
      let (b, s) ← β.parse' s
      let s ← s.accept ")"
      return ((a, b), s)
  | .array n α => do
      let s ← s.accept "["
      let (v, s) ← Vector.ofStrm s (λ s => do
        let (a, s) ← α.parse' s
        let s := s.accept "," |>.getD s.trim -- last element has no comma
        return (a, s)
      ) n
      let s ← s.accept "]"
      return (v, s)
  | _ ~> _ => ((), s)
  | .ref _ => panic! "ref not supported in parsing"

def Ty.parse (α: Ty)(s: String): Option α.val := do
  let s := if s.startsWith "ok: " then s.drop 4 else s
  let (a, s) ← α.parse' s
  if s == "" then a else none


----

def Parsed.toString {α: Ty}: α.val → String :=
  match α with
  | .nat => ToString.toString
  | .flt => ToString.toString
  | .lin => ToString.toString
  | .idx _ => ToString.toString
  | .unit => λ _ => "()"
  | _ ~> _ => λ _ => "<fun>"
  | α ×× β => λ (a, b) => s!"({@toString α a}, {@toString β b})"
  | .array _ α => λ v => s!"[{(v.toList.map (@toString α ·) |>.foldl (s!"{·}, {·}") "").drop 2}]"
  | .ref _ => panic! "ref not supported in ToString"

instance {α: Ty}: ToString α.val := ⟨Parsed.toString⟩

--------------------------------------------------
-- Similarity checks using knowledge of type
--------------------------------------------------

def Ty.similarVal (α: Ty)(a b: α.val): Bool :=
  match α with
  | .nat => a == b
  | .flt => a.similar b
  | .lin => a.similar b
  | .unit => true
  | .idx _ => a == b
  | α ×× β =>
      α.similarVal a.fst  b.fst &&
      β.similarVal a.snd b.snd
  | array _ α => a.zipWith (α.similarVal · ·) b |>.all id
  | _ ~> _ => true
  | .ref _ => panic! "ref not supported in similarity check"

def Ty.allSimilarVal (α: Ty)(l: List α.val): Bool :=
  match l with
  | a :: b :: l' => α.similarVal a b && α.allSimilarVal (b :: l')
  | _ => true

def Ty.allSimilarParseVal (α: Ty)(l: List String): Bool :=
  l.mapM α.parse |>.filter α.allSimilarVal |>.isSome

def Ty.allOkAndSimilar (α: Ty)(l: List String): Bool :=
  if l.all (·.startsWith "ok: ") then
    α.allSimilarParseVal (l.map (·.drop 4))
  else false
