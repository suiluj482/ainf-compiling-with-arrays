import Polara.Utils.Functions

def Vector.eq [BEq α](vec: Vector α n): Option α := do
  if h: n≠0 then
    have: NeZero n := ⟨h⟩
    let ref := vec.head
    if vec.all (ref==·) then ref else none
  else none

private def Vector.splitListPrefix' [BEq α](ref: List α)(ls: Vector (List α) n): List α × Vector (List α) n :=
  match ref with
    | [] => ([], ls)
    | h :: tail => if ls.all (λ l => l.head?.any (·==h))
      then splitListPrefix' tail (ls.map List.tail) |>.map (h::·) id
      else ([], ls)

def Vector.splitListPrefix [BEq α](ls: Vector (List α) n): List α × Vector (List α) n :=
  if h: n≠0 then
    have: NeZero n := ⟨h⟩
    Vector.splitListPrefix' ls.head ls
  else ([], ls)

namespace List

  def eq [BEq α]: List α → Bool
  | [] => true
  | _ :: [] => true
  | a :: b :: rest => a == b ∧ (b :: rest).eq

  def addToSet [BEq α](l: List α)(a: α): List α :=
    if l.contains a
      then l
      else a :: l

  def keepRight (l: List α)(n: Nat): List α :=
    l.drop (l.length-n)

  def combineSets [BEq α](l: List α): List α → List α
  | [] => l
  | a :: as => (l.addToSet a).combineSets as

  def slidingPair: List α → List (α × α)
  | [] => []
  | _ :: [] => []
  | a :: b :: rest => (a, b) :: slidingPair (b :: rest)

  def seperateBy (f: α → Bool): List α → List α × List α
  | [] => ([], [])
  | a :: as => match f a with
    | true  => as.seperateBy f |>.map (a::·) id
    | false => as.seperateBy f |>.map id (a::·)

  def seperateWith (f: α → β ⊕ γ): List α → List β × List γ
  | [] => ([], [])
  | a :: as => match f a with
    | .inl a => as.seperateWith f |>.map (a::·) id
    | .inr a => as.seperateWith f |>.map id (a::·)

  def getPrefix [BEq α]: List α → List α → List α
  | a :: as, b :: bs => if a==b then a :: List.getPrefix as bs else []
  | _, _ => []

  private def splitListPrefix' [BEq α](main: List α)(ls: List (List α)):  List α × List (List α) :=
    match main with
    | [] => ([], ls)
    | h :: tail => if ls.all (λ l => l.head?.any (·==h))
      then splitListPrefix' tail (ls.map List.tail) |>.map (h::·) id
      else ([], ls)

  def splitListPrefix [BEq α]: List (List α) → List α × List (List α)
  | [] => ([], [[]])
  | l :: ls => splitListPrefix' l (l::ls)

  def fold1 (f: α → α → α)(l: List α)(ok: l≠[]): α :=
  List.foldl f (l.head ok) l.tail

  private def splitAux : Nat → (List α) → (List α) → (List α) × (List α)
  | 0, a, b => (a, b)
  | _, a, [] => (a, [])
  | n+1, a, b :: bs => splitAux n (a.concat b) bs

  def split (a: List α) (n: Nat) : (List α) × (List α) :=
    splitAux n [] a

  -- #eval [1,2,3,4,5].split 4

  def fromNVal (x: α)(n: Nat): List α :=
    match n with
    | 0 => []
    | n'+1 => (fromNVal x n').cons x

  def fill (a: List α) (x: α) (n: Nat): List α :=
    if a.length < n then a.append (fromNVal x (n-a.length)) else a

  -- #eval [1,2,3].fill 0 5

  def fillD (a: List α) (n: Nat) (d: α): List α :=
    if a.length < n then a.append (fromNVal d (n-a.length)) else a

  def fillZ [Zero α]: List α → Nat → List α := Func.set3Param fillD Zero.zero


  def fillLeft (a: List α) (x: α) (n: Nat): List α :=
    if n<a.length then replicate (n-a.length) x |>.append a else a

  def zipWithAllFromRight (f: Option α → Option β → γ)(a: List α)(b: List β): List (γ) :=
    let (as, as') := a.split (a.length - b.length)
    let (bs, bs') := b.split (b.length - a.length)
    zipWithAll f as bs |>.append <| zipWithAll f as' bs'

  -- #eval zipWithAllFromRight (fun a? b? => a?.getD 0 |>.add (b?.getD 0)) [1,2,3] [1,2]

  def zipWithAllDFromRight [Inhabited α][Inhabited β] (f: α → β → γ)(a: List α)(b: List β): List (γ) :=
    zipWithAllFromRight (fun a? b? => f (a?.getD Inhabited.default) (b?.getD Inhabited.default)) a b

  def zipWithAllZFromRight [Zero α] [Zero β] (f: α → β → γ)(a: List α)(b: List β): List (γ) :=
    zipWithAllFromRight (fun a? b? => f (a?.getD Zero.zero) (b?.getD Zero.zero)) a b

  -- #eval zipWithAllDFromRight Nat.add [1,2,3] [1,2]



  partial def convolve [Add α] [Mul α] [Zero α] (as bs: List α): List α :=
    match as, bs with
    | [], _ => []
    | _ :: [], [] => []
    | a :: [], b :: [] => [a * b]
    | a :: [], b :: bs' => (a * b) :: convolve [a] bs'
    | _ :: _, [] => []
    | a :: as', b :: bs' =>
      have j1: Nat.succ (length as') = 1 + length as' := by
        rw [Nat.succ_eq_add_one]
        rw [Nat.add_comm]
      have j2: Nat.succ (length bs') = 1 + length bs' := by
        rw [Nat.succ_eq_add_one]
        rw [Nat.add_comm]
      (convolve [a] bs).zipWithAll (fun a b => (a.getD Zero.zero) + (b.getD Zero.zero)) (Zero.zero :: (convolve as' bs))

end List
