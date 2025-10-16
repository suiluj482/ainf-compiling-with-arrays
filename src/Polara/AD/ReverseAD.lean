import Polara.Syntax.All

@[reducible]
def Ty.copower: Ty → Ty → Ty
| α, β => list (α ×× β) -- idealy parametric, because list size is static, but polara does not support that
-- derivation function as parameter, tracks calls

mutual
  @[reducible]
  def Ty.dr': Ty → Ty
  | .unit
  | .nat
  | .idx _
  | .lin => .unit
  | .flt => .lin
  | α ×× β     => α.dr' ×× β.dr'
  | .array n α => .array n α.dr'
  | .list α => .list α.dr'
  | α ~> β     => Ty.copower α.dr β.dr'

  @[reducible]
  def Ty.dr: Ty → Ty
  | .unit      => .unit
  | .nat       => .nat
  | .flt       => .flt
  | .idx n     => .idx n
  | α ~> β     => α.dr ~> (β.dr ×× (β.dr' ~> α.dr'))
  | α ×× β     => α.dr ×× β.dr
  | .array n α => .array n α.dr
  | .lin       => .lin
  | .list α => .list α.dr
end


@[reducible]
private def EnvDr := List (Sigma VPar)
@[reducible]
private def EnvDr.ty: EnvDr → Ty
| [] => .unit
| ⟨α,_⟩ :: env' => α ×× EnvDr.ty env'
@[reducible]
private def Ty.drEnv (env: EnvDr): Ty → Ty
| α => (α.dr ×× (α.dr' ~> (EnvDr.ty env).dr')) -- α ~> env

------------------------------------------------------------------------------------------
-- except Const2.app functions only changing type
----

private def Const0.dr: Const0 α → Tm Γ α.dr
| .litn n => tlitn n
| .litf f => tlitf f
| .liti i => tliti i
| .litlZ => tlitlZ
| .litu => tlitu
| .litlE => tlitlE

private def Const1.dr (x: Tm Γ α.dr): Const1 α β → Tm Γ β.dr
| .exp     => Tm.cst1 Const1.exp x
| .sqrt    => Tm.cst1 Const1.sqrt x
| .normCdf => Tm.cst1 Const1.normCdf x
| .log     => Tm.cst1 Const1.log x
| .fst     => Tm.cst1 Const1.fst x
| .snd     => Tm.cst1 Const1.snd x
| .sumf    => Tm.cst1 Const1.sumf x
| .suml    => Tm.cst1 Const1.suml x
| .i2n     => Tm.cst1 Const1.i2n x
| .n2f     => Tm.cst1 Const1.n2f x
| .arr2list => Tm.cst1 Const1.arr2list x

private def ArithOp.dr [t: BiArraysC BiArith α β γ](op: ArithOp)
  (a: Tm Γ α.dr)(b: Tm Γ β.dr): Tm Γ γ.dr :=
   match t.t with
  | .array n t' =>
      have: BiArraysC BiArith _ _ _ := ⟨t'⟩
      for' i => (ArithOp.dr op a[[i]] b[[i]])
  | .base t' => match t' with
    | .nats => Tm.cst2 (.arithOp op) a b
    | .flts => Tm.cst2 (.arithOp op) a b
private def linOpDr [t: BiArraysC BiLin α β γ](op: AddOp)
  (a: Tm Γ α.dr)(b: Tm Γ β.dr): Tm Γ γ.dr :=
  match t.t with
  | .array n t' =>
      have: BiArraysC BiLin _ _ _ := ⟨t'⟩
      for' i => (linOpDr op a[[i]] b[[i]])
  | .base t' => match t' with
    | .lins => Tm.cst2 (.linOp op) a b
private def linScaleDr [t: BiArrayC BiLF α β γ](op: MulOp)
  (a: Tm Γ α.dr)(b: Tm Γ β.dr): Tm Γ γ.dr :=
  let go {α' β' γ'}[t: BiLFC α' β' γ'](a: Tm Γ α'.dr)(b: Tm Γ β'.dr): Tm Γ γ'.dr :=
    match t.t with
    | .lf => (Tm.cst2 (.linScale op) a b)

  match t.t with
  | .array n t' =>
      have: BiLFC _ _ _ := ⟨t'⟩
      for' i => (go a[[i]] b[[i]])
  | .base t' =>
      have: BiLFC _ _ _ := ⟨t'⟩
      go a b

private def Const2.dr (a: Tm Γ α.dr)(b: Tm Γ β.dr): Const2 α β γ → Tm Γ γ.dr
| arithOp op => op.dr a b
| linOp op => linOpDr op a b
| linScale op => linScaleDr op a b
| .addi => Tm.cst2 (.addi) a b
| .eqi => a ==' b
| .lt => a <' b
| .maxf => Max.max a b
| .get  => a[[b]]
| .tup  => (a,, b)
| .app  => (a @@ b).fst -- derivation not needed for primal value
| .cons => a.cons b
| .append => a.append b
| .zipL => a.zipL b
| .mapL => a.mapL (fun' x => (b@@x).fst)
| .foldL => Tm.cst2 .foldL a ((fun' x => fun' y => ((b.fst@@x).fst@@y).fst),, b.snd)
| .foldA => Tm.cst2 .foldA a ((fun' x => fun' y => ((b.fst@@x).fst@@y).fst),, b.snd)

-----------------------------------------------------------------------------------------
-- derivation rules
----

private def Const1.dr' (x: Tm Γ α.dr)(y': Tm Γ β.dr'):
  Const1 α β → Tm Γ α.dr'
| .exp     => y' * x.exp               -- (e^x)' = e^x
| .sqrt    => y' / (tlitf 2 * x.sqrt)  -- (sqrt x)' = 1/(2*sqrt x)
| .normCdf =>                          -- (normCdr x)' = (1/sqrt(2*pi)) * e^(-x^2/2) * dx
    (y' / (tlitf 2 * Tm.π).sqrt) * (tlitf 0 - (x * x / (tlitf 2))).exp
| .log     => y' / x                   -- (log x)' = 1/x
| .fst     => (y',, Tm.zero _)
| .snd     => (Tm.zero _,, y')
| .sumf    => for'v _ => y'
| .suml    => for'v _ => y'
| .i2n     => ()'
| .n2f     => ()'
| refGet => panic! "ref not supported in automatic differentiation"

private def ArithOp.dr' [t: BiArraysC BiArith α β γ](op: ArithOp)
  (a: Tm Γ α.dr)(b: Tm Γ β.dr)(y': Tm Γ γ.dr'): (Tm Γ α.dr' × Tm Γ β.dr') :=
   match t.t with
  | .array n t' =>
      have: BiArraysC BiArith _ _ _ := ⟨t'⟩
      let go := λ i => (ArithOp.dr' op a[[i]] b[[i]] y'[[i]])
      (for' i => (go i).fst, for' i => (go i).snd)
  | .base t' => match t' with
    | .nats => (()', ()')
    | .flts =>
        match op with
        | .add => (y', y')                     -- (a + b)' = a' + b'
        | .sub => (y', tlitlZ - y')           -- (a - b)' = a' - b'
        | .mul => (y' * b, y' * a)             -- (a * b)' = a' * b + a * b'
        | .div => (y' / b, tlitlZ - y' * a / (b*b))     -- (a / b)' = (a' * b - a * b') / (b^2)
private def linOpDr' [t: BiArraysC BiLin α β γ]: (Tm Γ α.dr' × Tm Γ β.dr') :=
  match t.t with
  | .array n t' => (@linOpDr' _ _ _ _ ⟨t'⟩).map (for'v _ => ·) (for'v _ => ·)
  | .base (.lins) => (()', ()')
private def linScaleDr' [t: BiArrayC BiLF α β γ]: (Tm Γ α.dr' × Tm Γ β.dr') :=
  match t.t with
  | .array n (.lf) => (for'v _ => ()', for'v _ => Tm.zero _) -- todo check
  | .base (.lf) => (()', Tm.zero _)

private def Const2.dr' (env: EnvDr)(const2: Const2 α β γ)(a: Tm VPar (α.drEnv env))(b: Tm VPar (β.drEnv env))
  : Tm VPar (γ.drEnv env) := -- (Tm Γ α.dr' × Tm Γ β.dr') :=
  match const2 with
  | Const2.arithOp op  =>
      ((Const2.arithOp op).dr a.fst b.fst,,
       fun' y' =>
        let (a',b') := op.dr' a.fst b.fst y'
        Tm.sumLins (a.snd@@ a') (b.snd@@ b'))
  | Const2.linOp op    =>
      ((Const2.linOp op).dr a.fst b.fst,,
       fun' y' =>
        let (a',b') := @linOpDr' α β _ _ _
        Tm.sumLins (a.snd@@ a') (b.snd@@ b'))
  | Const2.linScale op =>
      ((Const2.linScale op).dr a.fst b.fst,,
       fun' y' =>
        let (a',b') := @linScaleDr' α β _ _ _
        Tm.sumLins (a.snd@@ a') (b.snd@@ b'))
  | .addi       =>
      (a.fst.addi b.fst,,
       fun' y' => Tm.sumLins (a.snd@@ ()') (b.snd@@ ()'))
  | .eqi        =>
      (a.fst.eqi b.fst,,
       fun' y' => Tm.sumLins (a.snd@@ ()') (b.snd@@ ()'))
  | .lt         =>
      (a.fst <' b.fst,,
       fun' y' => Tm.sumLins (a.snd@@ tlitlZ) (b.snd@@ tlitlZ))
  | .maxf       =>
      (a.fst.maxf b.fst,,
       fun' y' =>
        let' c := a.fst <' b.fst;
        let a' := if' c then Tm.zero _ else y'
        let b' := if' c then y' else Tm.zero _
        Tm.sumLins (a.snd@@ a') (b.snd@@ b')
      )
  | .get        =>
      (a.fst[[b.fst]],,
       fun' y' =>
        let a' := for' i => (if' i ==' b.fst then y' else Tm.zero _)
        Tm.sumLins (a.snd@@ a') (b.snd@@ ()'))
  | .tup        =>
      ((a.fst,, b.fst),,
       fun' y' => Tm.sumLins (a.snd@@ y'.fst) (b.snd@@ y'.snd))
  | .app => -- special case
      let' f := a;
      let' arg := b;
      let' y := f.fst @@ arg.fst;
      (
        y.fst,,
        fun' y' => Tm.sumLins (arg.snd @@ (y.snd @@ y')) (f.snd @@ (arg.fst,, y').listSingleton)
      )
  | .cons => panic! "df does not yet support cons" -- would require list.head and list.tail
      -- (a.fst.cons b.fst,,
      --   fun' y' => Tm.sumLins (a.snd@@ y'.head) (b.snd@@ y'.tail))
  | .append => panic! "df does not support append" -- the derivation list cant be split on the right point
      -- (a.fst.append b.fst,,
      --   fun' y' => Tm.sumLins (a.snd@@ y'.fst) (b.snd@@ y'.snd))
  | .zipL =>
      (a.fst.zipL b.fst,,
        fun' y' => Tm.sumLins (a.snd@@ (y'.mapL (fun' a => a.fst))) (b.snd@@ (y'.mapL (fun' a => a.snd)))
      )
  | .mapL => panic! "df does not yet support mapL"
  | .foldL => panic! "df does not yet support foldL"
  | .foldA => panic! "df does not yet support foldA"
----------------------------------------------------------------------------------------------

private def VPar.drEnv (env: EnvDr): VPar α → VPar (α.drEnv env) := VPar.changeType
private def VPar.idrEnv (env: EnvDr): VPar (α.drEnv env) → VPar α := VPar.changeType

private def VPar.dr: VPar α → VPar α.dr := VPar.changeType
private def VPar.idr: VPar α.dr → VPar α := VPar.changeType

-- Var -> Definitionstiefe in Bezug auf env
private def Ren := List (Sigma VPar × Nat)

private def Tm.dr'(env: EnvDr)(ren: Ren): Tm VPar α → Tm VPar (α.drEnv env)
| .err => (.err,, fun' y' => .err)
| .cst0 const0        => (
      const0.dr,,
      fun' y' => Tm.zero _
    )
| .cst1 const1 t      =>
    let' t := t.dr' env ren;
    (
      const1.dr t.fst,,
      fun' y' => t.snd @@ (const1.dr' t.fst y')
    )
| .cst2 const2 a b => const2.dr' env (a.dr' env ren) (b.dr' env ren)
| .bld a (n:=n)       =>
  let' arr := for'v idx =>
    let'v idx := (.var idx,, fun' y' => Tm.zero _);
    let origIdx: VPar (.idx n) := idx.idrEnv env
    (a origIdx).dr' env ((⟨_,origIdx⟩,env.length) :: ren);
  (
    for' idx => arr[[idx]].fst,,
    fun' y' => ( for' idx => (arr[[idx]].snd @@ y'[[idx]]) ).sumArrayOfLins
  )
| .ite cond a b       => .ite cond (a.dr' env ren) (b.dr' env ren)
| .var v (α:=α)       =>
    let rec go (env': EnvDr)(f: Tm VPar env'.ty.dr' → Tm VPar (env.ty.dr')):
      Tm VPar (α.drEnv env) :=
        match env' with
        | [] =>
          match ren.findSome? (λ (sv,n) => if sv == ⟨_,v⟩ then some n else none) with
          | some depth =>
            -- dbg_trace s!"{v} defined with depth {depth}"
            let rec go' (env): Term α.dr × (Term α.dr' → Term ((EnvDr.ty env).dr')) :=
              if env.length ≤ depth
                then let t := Tm.var (v.drEnv env); (t.fst, λ y' => t.snd @@ y')
                else match env with
                  | [] => panic! "Tm.dr' Tm.var depth in ren cant be right"
                  | _ :: env => go' env |>.map id (λ y' => (Tm.zero _,, · y'))
            let (v, d) := go' env; (v,, fun' y' => d y')
          | none =>
            -- dbg_trace s!"{v} defined outside"
            if α.contains (λ | _ ~> _ => true | _ => false)
              then panic! "Tm.df' outside vpar contains function"
              else (Tm.var v.dr,, fun' y' => Tm.zero _)
        | ⟨α',x⟩ :: env'' => if t: α=α' then if x=t▸v
            then (.var v.dr,, fun' y' => f (t▸y',, Tm.zero _)) -- in env, put dr in env
            else go env'' (f (Tm.zero _,, ·)) else go env'' (f (Tm.zero _,, ·))
    go env id
| .bnd t f            =>
    let'v v := t.dr' env ren;
    let origV := v.idrEnv env
    (f origV).dr' env ((⟨_,origV⟩,env.length) :: ren)
| .abs f (α:=α) (β:=β)            =>
    let' f := fun'v x => (f x.idr).dr' (⟨_,x.idr⟩ :: env) ren;
    (
      fun' x =>
        let' body := f @@ x;
        (
          body.fst,,
          fun' y' => (body.snd @@ y').fst
        ),,
      fun' copower => copower.foldL (fun' call => fun' acc =>
        let x  := call.fst;
        let y' := call.snd;
        let body := f @@ x;
        Tm.sumLins (body.snd @@ y').snd acc
      ) (Tm.zero _)
    )

def Tm.dr (t: Tm VPar α): Tm VPar α.dr :=
  t.dr' [] [] |>.fst -- remove derivation of empty env




-- open Ty

-- #eval (fun' f:(flt ~> flt) => fun' x:flt => (tlitf 1.0) + (f @@ x)).dr

-- #eval (unit).drEnv [⟨flt ~> unit, .v (.mk 0)⟩]

-- #eval (fun' f:(flt ~> unit) => ()').dr' []
-- #eval (()').dr' [⟨flt ~> unit, .v (.mk 0)⟩]

-- f(x)(y) = x+y
-- [1,2,3].map (·+1)
-- a := [1,2,3]
-- b := for' i => a[i] + 1
-- [1,2,3]


-- (lin, lin)
-- (
--  suml e,
--  suml e
-- )

-- f [n: Nat](a: array n α)
-- list

-- f

------------------------------------------------
-- open Ty

-- #eval! (fun' x:flt => x.exp).df |>.normVPar
-- #eval! (fun' x:flt => x.exp).dr |>.normVPar

-- #eval! (fun' x:flt××flt => x.fst+x.snd).df |>.normVPar
-- #eval! (fun' x:flt××flt => x.fst+x.snd).dr |>.normVPar

-- #eval! (fun' x:flt××flt => x.fst*x.snd).df |>.normVPar
-- #eval! (fun' x:flt××flt => x.fst*x.snd).dr |>.normVPar

-- #eval! (fun' x:flt => fun' y:flt => x+y).df |>.normVPar
-- #eval! (fun' x:flt => fun' y:flt => x+y).dr |>.normVPar

-- #eval! (fun' x:flt => fun' y:flt => x*y).df |>.normVPar
-- #eval! (fun' x:flt => fun' y:flt => x*y).dr |>.normVPar

-- #eval! (fun' x:flt => ((fun' a:flt => a)@@x)) |>.df |>.normVPar
-- #eval! (fun' x:flt => ((fun' a:flt => a)@@x)) |>.dr |>.normVPar

-- #eval! (fun' x:flt => (for' i:42 => i.i2n.n2f + x)) |>.df |>.normVPar
-- #eval! (fun' x:flt => (for' i:42 => i.i2n.n2f + x)) |>.dr |>.normVPar


-- #eval! (fun' x:flt××nat => x.fst) |>.df |>.normVPar

-- #eval flt |>drEnv [⟨flt, (.v (.mk 1))⟩]
-- #eval flt ~> flt |>.drEnv []
-- #eval flt ~> flt ~> flt |>.drEnv []
