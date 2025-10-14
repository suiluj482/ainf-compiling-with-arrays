structure Pos where
  val: Nat
  pos: val≠0
deriving DecidableEq, Hashable, Repr
def Nat.toPos (n: Nat)[pos: NeZero n]: Pos := ⟨n,pos.ne⟩
namespace Pos
  def toNat := Pos.val
  theorem zero_lt (p: Pos): 0<p.val := by
    rw[←@Nat.ne_zero_iff_zero_lt p.val]
    exact p.pos
  theorem one_le (p: Pos): 1≤p.val := by
    have a := zero_lt p
    have b := @Nat.lt_iff_add_one_le 0 p.val
    rw [Nat.zero_add] at b
    rw [b] at a
    exact a
  instance instInhabited: Inhabited Pos := ⟨⟨1,by simp⟩⟩
  instance instNeZero {n: Pos}: NeZero n.toNat := ⟨n.pos⟩
  instance instCoeNat: Coe Pos Nat := ⟨Pos.toNat⟩
  instance instOfNat [pos: NeZero n]: OfNat Pos n := ⟨n.toPos⟩
  instance instToString: ToString Pos := ⟨λ n => ToString.toString n.toNat⟩

  instance instAdd: Add Pos := ⟨λ ⟨a,ap⟩ ⟨b,bp⟩ => ⟨a+b, by simp[ap,bp]⟩⟩
  def addMinOne: Pos → Pos → Pos := λ ⟨a,ap⟩ ⟨b,bp⟩ => ⟨a-1+b, by simp[ap,bp]⟩
  theorem addMinOne_eq_add_min_one: (Pos.addMinOne n m).toNat = n.toNat+m.toNat-1 := by
    let a := (@Nat.sub_add_comm n m 1) (one_le n)
    simp[Pos.toNat, addMinOne]
    simp[Pos.toNat] at a
    rw[a]
  def finZero(n: Pos): Fin n := ⟨0,n.zero_lt⟩
  instance instFinOfNat {n: Pos}: OfNat (Fin n) i := ⟨Fin.ofNat' n i⟩
end Pos
