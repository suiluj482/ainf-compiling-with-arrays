def Option.zip (a: Option α)(b: Option β): Option (α × β) :=
  a.bind (fun av => b.map (av, ·))

def Option.zipWith (f: α → β → γ)(a: Option α)(b: Option β): Option γ :=
  a.bind (fun av => b.map (f av))

def Option.comBinOp (bin: α → α → γ)(u: α → Option γ): Option α → Option α → Option γ
 | none, none => none
 | some a, none
 | none, some a => u a
 | some a, some b => bin a b

def Option.orElseOption (a: Option α)(b: Option α): Option α :=
  match a with
  | none => b
  | some _ => a
