import Polara.Syntax.All
import Polara.Optimizations.ForwardAD
import Polara.Optimizations.RmUnits

@[reducible]
def Ty.copower: Ty → Ty → Ty
| α, β => (α ×× β) -- todo [(a, b)]
-- erlaubt quasi mehrfachanwendung innerer funktion ohne mehrfaches auswerten
-- aber list hätte keine statische Größe, Probleme mit jax (vllt parametriesierte funktionen? in lean?)

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
  | .ref _     => panic! "ref not supported in automatic differentiation"
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
  | .ref _     => panic! "ref not supported in automatic differentiation"
end


@[reducible]
def EnvDr := List (Some VPar)
@[reducible]
def EnvDr.ty: EnvDr → Ty
| [] => .unit
| ⟨α,_⟩ :: env' => α ×× EnvDr.ty env'
@[reducible]
def Ty.drEnv (env: EnvDr): Ty → Ty
| α => (α.dr ×× (α.dr' ~> (EnvDr.ty env).dr')) -- α ~> env

-- open Ty in
-- #eval flt ~> flt |>.dr
-- open Ty in
-- #eval flt ~> flt ~> flt |>.dr


------------------------------------------------------------------------------------------
-- except Const2.app functions only changing type
----

def Const0.dr: Const0 α → Tm Γ α.dr
| .litn n => tlitn n
| .litf f => tlitf f
| .liti i => tliti i
| .litl l => tlitl l
| .litu => tlitu
| mkRef => panic! "ref not supported in automatic differentiation"

def Const1.dr (x: Tm Γ α.dr): Const1 α β → Tm Γ β.dr
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
| refGet => panic! "ref not supported in automatic differentiation"

def ArithOp.dr [t: BiArraysC BiArith α β γ](op: ArithOp)
  (a: Tm Γ α.dr)(b: Tm Γ β.dr): Tm Γ γ.dr :=
   match t.t with
  | .array n t' =>
      have: BiArraysC BiArith _ _ _ := ⟨t'⟩
      for' i => (ArithOp.dr op a[[i]] b[[i]])
  | .base t' => match t' with
    | .nats => Tm.cst2 (.arithOp op) a b
    | .flts => Tm.cst2 (.arithOp op) a b
def linOpDr [t: BiArraysC BiLin α β γ](op: AddOp)
  (a: Tm Γ α.dr)(b: Tm Γ β.dr): Tm Γ γ.dr :=
  match t.t with
  | .array n t' =>
      have: BiArraysC BiLin _ _ _ := ⟨t'⟩
      for' i => (linOpDr op a[[i]] b[[i]])
  | .base t' => match t' with
    | .lins => Tm.cst2 (.linOp op) a b
def linScaleDr [t: BiArrayC BiLF α β γ](op: MulOp)
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

def Const2.dr (a: Tm Γ α.dr)(b: Tm Γ β.dr): Const2 α β γ → Tm Γ γ.dr
| arithOp op => op.dr a b
| linOp op => linOpDr op a b
| linScale op => linScaleDr op a b
| .addi => Tm.cst2 (.addi) a b
| .eqi => a ==' b
| .lt => a <' b
| .maxf => Max.max a b
| .get  => a[[b]]
| .tup  => (a,, b)
| .refSet => panic! "refSet not supported in automatic differentiation"
| .app  => (a @@ b).fst -- derivation no longer needed


-----------------------------------------------------------------------------------------
-- derivation rules
----

def Const1.dr' (x: Tm Γ α.dr)(y': Tm Γ β.dr'):
  Const1 α β → Tm Γ α.dr'
| .exp     => y' * x.exp               -- (e^x)' = e^x
| .sqrt    => y' / (tlitf 2 * x.sqrt)  -- (sqrt x)' = 1/(2*sqrt x)
| .normCdf =>                          -- (normCdr x)' = (1/sqrt(2*pi)) * e^(-x^2/2) * dx
    (y' / (tlitf 2 * Tm.π).sqrt) * (tlitf 0 - (x * x / (tlitf 2))).exp
| .log     => y' / x                   -- (log x)' = 1/x
| .fst     => (y',, Tm.linZero _)
| .snd     => (Tm.linZero _,, y')
| .sumf    => for'v _ => y'
| .suml    => for'v _ => y'
| .i2n     => ()'
| .n2f     => ()'
| refGet => panic! "ref not supported in automatic differentiation"

def ArithOp.dr' [t: BiArraysC BiArith α β γ](op: ArithOp)
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
        | .sub => (y', tlitl 0 - y')           -- (a - b)' = a' - b'
        | .mul => (y' * b, y' * a)             -- (a * b)' = a' * b + a * b'
        | .div => (y' / b, y' * a / (b*b))     -- (a / b)' = (a' * b - a * b') / (b^2)
def linOpDr' [t: BiArraysC BiLin α β γ]: (Tm Γ α.dr' × Tm Γ β.dr') :=
  match t.t with
  | .array n t' => (@linOpDr' _ _ _ _ ⟨t'⟩).map (for'v _ => ·) (for'v _ => ·)
  | .base (.lins) => (()', ()')
def linScaleDr' [t: BiArrayC BiLF α β γ]: (Tm Γ α.dr' × Tm Γ β.dr') :=
  match t.t with
  | .array n (.lf) => (for'v _ => ()', for'v _ => Tm.linZero _) -- todo check
  | .base (.lf) => (()', Tm.linZero _)

def Const2.dr' (const2: Const2 α β γ)(a: Tm Γ α.dr)(b: Tm Γ β.dr)(y': Tm Γ γ.dr')
  (ok: (t: α=β~>γ) → const2 ≠ t▸Const2.app): (Tm Γ α.dr' × Tm Γ β.dr') :=
  match const2 with
  | Const2.arithOp op  => op.dr' a b y'
  | Const2.linOp op    => @linOpDr' α β _ _ _
  | Const2.linScale op => @linScaleDr' α β _ _ _
  | .addi       => (()', ()')
  | .eqi        => (()', ()')
  | .lt         => (tlitl 0, tlitl 0)
  | .maxf       => (
      if' a <' b then y' else Tm.linZero _,
      if' a <' b then Tm.linZero _ else y'
    )
  | .get        => (for' i => (if' i ==' b then y' else Tm.linZero _), ()')
  | .tup        => (y'.fst, y'.snd)
  | .refSet     => panic! "refSet not supported in automatic differentiation"
  | .app        => nomatch ((ok rfl) rfl) -- as special case handled in Tm.dr'

----------------------------------------------------------------------------------------------

def VPar.drEnv (env: EnvDr): VPar α → VPar (α.drEnv env) := VPar.changeType
def VPar.idrEnv (env: EnvDr): VPar (α.drEnv env) → VPar α := VPar.changeType

def VPar.dr: VPar α → VPar α.dr := VPar.changeType
def VPar.idr: VPar α.dr → VPar α := VPar.changeType

def Tm.dr'(env: EnvDr): Tm VPar α → Tm VPar (α.drEnv env)
| .err => (.err,, fun' y' => .err)
| .cst0 const0        => (
      const0.dr,,
      fun' y' => Tm.linZero _
    )
| .cst1 const1 t      =>
    let' t := t.dr' env;
    (
      const1.dr t.fst,,
      fun' y' => t.snd @@ (const1.dr' t.fst y')
    )
| .cst2 const2 a b (α₁:=α) (α₂:=β) (α:=γ) =>
    -- if h: α = β ~> γ then
    --   if const2 = h▸Const2.app then sorry
    -- else sorry else sorry

    match h: const2 with
    | Const2.app => -- special case
      let' f := a.dr' env;
      let' arg := b.dr' env;
      let' y := f.fst @@ arg.fst;
      (
        y.fst,,
        fun' y' => Tm.sumLins (arg.snd @@ (y.snd @@ y')) (f.snd @@ (arg.fst,, y'))
      )
    | const2 =>
      let' a := a.dr' env;
      let' b := b.dr' env;
      (
        const2.dr a.fst b.fst,,
        fun' y' =>
          let (a', b') := const2.dr' a.fst b.fst y' (by  sorry)
          Tm.sumLins (a.snd @@ a') (b.snd @@ b')
    )
| .bld a              =>
  let' arr := for'v idx =>
    let'v idx := (.var idx,, fun' y' => Tm.linZero _);
    (a (idx.idrEnv env)).dr' env;
  (
    for' idx => arr[[idx]].fst,,
    fun' y' => ( for' idx => (arr[[idx]].snd @@ y'[[idx]]) ).sumArrayOfLins
  )
| .ite cond a b       => .ite cond (a.dr' env) (b.dr' env)
| .var v (α:=α)       =>
    let rec go (env': EnvDr)(f: Tm VPar env'.ty.dr' → Tm VPar (env.ty.dr')):
      Tm VPar (α.drEnv env) :=
        match env' with
        | [] => .var (v.drEnv env) -- VPar not in env therefore allready changed by Tm.dr' rodo ??
        | ⟨α',x⟩ :: env'' => if t: α=α' then if x=t▸v
            then (.var v.dr,, fun' y' => f (t▸y',, Tm.linZero _)) -- in env, put dr in env
            else go env'' (f (Tm.linZero _,, ·)) else go env'' (f (Tm.linZero _,, ·))
    go env id
| .bnd t f            => let'v v := t.dr' env; (f (v.idrEnv env)).dr' env
| .abs f (α:=α) (β:=β)            =>
    let' f := fun'v x => (f x.idr).dr' (⟨_,x.idr⟩ :: env);
    (
      fun' x =>
        let' body := f @@ x;
        (
          body.fst,,
          fun' y' => (body.snd @@ y').fst
        ),,
      fun' copower => -- copower.fold λ copower => -- todo fold
        let x  := copower.fst;
        let y' := copower.snd;
        let body := f @@ x;
        (body.snd @@ y').snd
    )

def Tm.dr (t: Tm VPar α): Tm VPar α.dr :=
  t.dr' [] |>.fst -- remove derivation of empty env


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
open Ty

#eval! (fun' x:flt => x.exp).df |>.normVPar
#eval! (fun' x:flt => x.exp).dr |>.normVPar

#eval! (fun' x:flt××flt => x.fst+x.snd).df |>.normVPar
#eval! (fun' x:flt××flt => x.fst+x.snd).dr |>.normVPar

#eval! (fun' x:flt××flt => x.fst*x.snd).df |>.normVPar
#eval! (fun' x:flt××flt => x.fst*x.snd).dr |>.normVPar

#eval! (fun' x:flt => fun' y:flt => x+y).df |>.normVPar
#eval! (fun' x:flt => fun' y:flt => x+y).dr |>.normVPar

#eval! (fun' x:flt => fun' y:flt => x*y).df |>.normVPar
#eval! (fun' x:flt => fun' y:flt => x*y).dr |>.normVPar

#eval! (fun' x:flt => ((fun' a:flt => a)@@x)) |>.df |>.normVPar
#eval! (fun' x:flt => ((fun' a:flt => a)@@x)) |>.dr |>.normVPar

#eval! (fun' x:flt => (for' i:42 => i.i2n.n2f + x)) |>.df |>.normVPar
#eval! (fun' x:flt => (for' i:42 => i.i2n.n2f + x)) |>.dr |>.normVPar


#eval! (fun' x:flt××nat => x.fst) |>.df |>.normVPar |>.rmUnits

-- #eval flt |>drEnv [⟨flt, (.v (.mk 1))⟩]
-- #eval flt ~> flt |>.drEnv []
-- #eval flt ~> flt ~> flt |>.drEnv []
