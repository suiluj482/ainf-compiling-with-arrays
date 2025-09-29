private def String.toFloat'? (s: String): Option Float :=
  let ss := s.splitOn "."
  match l: ss.length with
  | 2 =>
    if ss[1].isEmpty then
      match ss[0].toNat? with
      | some n => some (Float.ofNat n)
      | none => none
    else
      match ss[0].toNat?, ss[1].toNat? with
      | some n, some m => some (Float.ofNat n + Float.ofNat m / Float.ofNat (10 ^ ss[1].length))
      | _, _ => none
  | 1 =>
    match ss[0].toNat? with
    | some n => some (Float.ofNat n)
    | none => none
  | _ => none

def String.toFloat? (s: String): Option Float :=
  if s.startsWith "-" then
    s.drop 1 |>.toFloat'? |>.map (· * -1)
  else
    s.toFloat'?

def String.toFin? (s: String): Option (Fin n) :=
  match s.toNat? with
  | some v => if lt: v < n then some ⟨v, lt⟩ else none
  | none => none

def Float.similar (a b: Float): Bool :=
  let epsilon := 1e-3
  Float.abs (a - b) < epsilon
