import Polara.Utils.Functions

namespace List

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
