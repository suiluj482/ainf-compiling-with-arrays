import Polara.Syntax.Definitions
import Polara.Syntax.PrettyPrint
import Polara.Syntax.Notations

def Tm.getTy: Tm Γ α → Ty := λ _ => α

@[reducible]
def Ty.transform (f: Ty → Ty) : Ty → Ty
| .nat => f .nat
| .idx n => f (.idx n)
| flt => f .flt
| lin => f .lin
| α ~> β => f (α.transform f ~> β.transform f)
| α ×× β => f (α.transform f ×× β.transform f)
| array n α => f (array n (α.transform f))
| list α => f (list (α.transform f))
| unit => f .unit

@[reducible]
def Ty.contains (t: Ty)(f: Ty → Bool): Bool :=
  match t with
  | .nat => f nat
  | .flt => f flt
  | .lin => f lin
  | .idx n => f (idx n)
  | .list α => f (list α) ∨ α.contains f
  | .unit => f unit
  | α ×× β => f t ∨ α.contains f ∨ β.contains f
  | .array _ α => f t ∨ α.contains f
  | α ~> β => f t ∨ α.contains f ∨ β.contains f

theorem Ty.contains_product_a (α: Ty)(β: Ty)(f: Ty → Bool):
  Ty.contains (α ×× β) f = false → Ty.contains α f = false := by simp[Ty.contains]; exact λ _ a _ => a
theorem Ty.contains_product_b (α: Ty)(β: Ty)(f: Ty → Bool):
  Ty.contains (α ×× β) f = false → Ty.contains β f = false := by simp[Ty.contains]
theorem Ty.contains_array (n: Pos)(α: Ty)(f: Ty → Bool):
  Ty.contains (array n α) f = false → Ty.contains α f = false := by simp[Ty.contains]
theorem Ty.contains_arrow_a (α: Ty)(β: Ty)(f: Ty → Bool):
  Ty.contains (α ~> β) f = false → Ty.contains α f = false := by simp[Ty.contains]; exact λ _ a _ => a
theorem Ty.contains_arrow_b (α: Ty)(β: Ty)(f: Ty → Bool):
  Ty.contains (α ~> β) f = false → Ty.contains β f = false := by simp[Ty.contains]
theorem Ty.contains_list (α: Ty)(f: Ty → Bool):
  Ty.contains (α.list) f = false → Ty.contains α f = false := by simp[Ty.contains]

def VPar.type(_: VPar α): Ty := α
def Par.type(_: Par α): Ty := α
def Var.type(_: Var α): Ty := α
def VPar.changeType: VPar α → VPar β
| .v (.mk n) => .v (.mk n)
| .p (.mk n) => .p (.mk n)
def Var.changeType: Var α → Var β
| (.mk n) => (.mk n)
def Par.changeType: Par α → Par β
| (.mk n) => (.mk n)

def VPar.changeTypeF (f: Ty → Ty): VPar α → VPar (f α)
| .v (.mk n) => .v (.mk n)
| .p (.mk n) => .p (.mk n)
def Var.changeTypeF (f: Ty → Ty): Var α → Var (f α)
| (.mk n) => (.mk n)
def Par.changeTypeF (f: Ty → Ty): Par α → Par (f α)
| (.mk n) => (.mk n)

def VPar.toSigma: VPar α → Sigma VPar := (⟨_,·⟩)
def Par.toSigma: Par α → Sigma Par := (⟨_,·⟩)
def Var.toSigma: Var α → Sigma Var := (⟨_,·⟩)
def VPar.eq: VPar α → VPar β → Bool := (·.toSigma == ·.toSigma)
def Par.eq: Par α → Par β → Bool := (·.toSigma == ·.toSigma)
def Var.eq: Var α → Var β → Bool := (·.toSigma == ·.toSigma)

abbrev VParM (α: Type n) := StateM (ULift (Nat × Nat)) α
def VParM.var : VParM ((β: Ty) → Var β) :=
  modifyGet fun i => (
    λ _ => (.mk i.down.fst),
    ⟨i.down.map (·+1) id⟩
  )
def VParM.par : VParM ((β: Ty) → Par β) :=
  modifyGet fun i => (
    λ _ => (.mk i.down.snd),
    ⟨i.down.map id (·+1)⟩
  )
def VParM.nextParNum : VParM Nat :=
  λ i => (i.down.snd, i)
def VParM.varVPar : VParM ((β: Ty) → VPar β) :=
  modifyGet fun i => (
    λ _ => (.v (.mk i.down.fst)),
    ⟨i.down.map (·+1) id⟩
  )
def VParM.parVPar : VParM ((β: Ty) → VPar β) :=
  modifyGet fun i => (
    λ _ => (.p (.mk i.down.snd)),
    ⟨i.down.map id (·+1)⟩
  )
def VParM.vpar : VParM ((β: Ty) → VPar β) :=
  modifyGet fun i => (
    λ _ => (.v (.mk i.down.fst)),
    ⟨i.down.map id (·+1)⟩
  )
def VParM.rPar: VParM Unit :=
  modify fun ⟨(i,_)⟩ => ⟨(i,0)⟩
def AINF.findFreshVPars: AINF α → Nat × Nat
| (bnds, _) => bnds.foldl (λ (x, i) ⟨⟨_,⟨n⟩⟩, _, prim⟩ =>
    (
      x.max n,
      match prim with
      | .abs ⟨n⟩ _
      | .bld ⟨n⟩ _ => i.max n
      | _ => i
    )
  ) (0, 0)
def VParM.freshAINFVPars (a: AINF α)(m: VParM β): β :=
  m ⟨a.findFreshVPars⟩ |>.fst
def VParM.startZero (m: VParM β): β :=
  m ⟨(0,0)⟩ |>.fst
--
abbrev VarM (α: Type n) := StateM (ULift Nat) α
def VarM.var : VarM ({β: Ty} → Var β) :=
  modifyGet fun i => (
    λ {_} => (.mk i.down),
    ⟨i.down + 1⟩
  )
def Bnds.findFreshVars: Bnds → Nat
| bnds => bnds.foldl (λ count ⟨⟨_,⟨n⟩⟩,_,_⟩ => count.max n) 0
def AINF.findFreshVars: AINF α → Nat
| (bnds, _) => bnds.findFreshVars
def Bnds.freshBndsVars (bnds: Bnds)(m: VarM β): β :=
  m ⟨bnds.findFreshVars⟩ |>.fst
def VParM.freshAINFVars (a: AINF α)(m: VarM β): β :=
  m ⟨a.findFreshVars⟩ |>.fst
def VarM.startZero (m: VarM β): β :=
  m ⟨0⟩ |>.fst


------
def Tm.toVPar: Tm VPar α → Tm VPar α := id

private def Tm.generalize' [DecidableEq Ty][∀ x:Ty, BEq (γ x)]
  : Tm γ α → ReaderM ((ListMap γ Γ) × Nat × (Nat → (β: Ty) → γ β)) (Tm Γ α)
  | .err => return Tm.err
  | .cst0 c => return Tm.cst0 c
  | .cst1 c v => return Tm.cst1 c (←v.generalize')
  | .cst2 c v1 v2 => return Tm.cst2 c (←v1.generalize') (←v2.generalize')
  | .abs f => do
      let (ren, n, vars) ← read
      let v := vars n _
      return Tm.abs (λ x => (f v).generalize' (⟨_, v, x⟩ :: ren, n+1, vars))
  | .bld f => do
      let (ren, n, vars) ← read
      let v := vars n _
      return Tm.bld (λ idx => (f v).generalize' (⟨_, v, idx⟩ :: ren, n+1, vars))
  | .ite cond a b => return Tm.ite (←cond.generalize') (←a.generalize') (←b.generalize')
  | .var v => do
      let (ren, _, _) ← read
      return match ren.lookup v with
      | some x => Tm.var x
      | none   => panic! "Tm.generalize' expr no ref. integrity"
  | .bnd t f => do
      let (ren, n, vars) ← read
      let v := vars n _
      return Tm.bnd
        (←t.generalize')
        (λ x => (f v).generalize' (⟨_, v, x⟩ :: ren, n+1, vars))

def Tm.generalize [DecidableEq Ty][∀ x:Ty, BEq (γ x)]
  (vars: Nat → (β: Ty) → γ β): Tm γ α → Tm Γ α :=
  (Tm.generalize' · ([], 0, vars))
def Tm.generalizeVPar : Tm VPar α → Tm Γ α :=
  Tm.generalize (λ n _ => VPar.v (.mk n))

------
def AINF.size : AINF α → Nat
| (bnds, _) => bnds.length

-------------
-- ReaderMonad for access to original AiNF
@[reducible] def Orig α := ∀ {β}, ReaderM (AINF β) α


-- lookup enviroment in binding of variable
def Var.defB (x: Var α): Bnds → Option (Env × Prim α)
  | bnds => DListMap.get? ⟨α,x⟩ bnds
def Var.def (x: Var α): AINF γ → Option (Env × Prim α) :=
 x.defB ∘ Prod.fst

-- lookup enviroment in binding of variable
def Var.lookupEnvB (x: Var α) : Bnds → Option Env
  | bs => x.defB bs |>.map (λ (env, _) => env)
def Var.lookupEnvRB (x: Var α) : ReaderM Bnds (Option Env) := x.lookupEnvB
def Var.lookupEnv (x: Var α) : AINF γ → Option Env :=
  x.lookupEnvB ∘ Prod.fst
def VPar.lookupEnv (a: AINF β) (v: VPar α): Option Env :=
  match v with
  | .v v => v.lookupEnv a
  | .p _ => some <| .nil

def AINF.mapBnds (f: Bnds → Bnds): AINF α → AINF α := Prod.map f id

def AINF.flatMapMBnd (g: Ty → Ty)(f: Bnd → VParM Bnds)(a: AINF α): AINF (g α) := match a with
| (bnds, v) => ((bnds.flatMapM f).freshAINFVPars a, v.changeType)

-- check if env defines parameter
def EnvPart.definesPar (i: Par α): EnvPart → Bool
| .func _ i' => Sigma.of i' == Sigma.of i
| .forc _ i' => Sigma.of i' == Sigma.of i
| .itec _ _ => false

def Env.definesPar (i: Par α): Env → Bool :=
  (·.any (·.definesPar i))

def Env.isPrefixOf (a b: Env): Bool :=
  List.isPrefixOf a b

def Env.getPrefix (a b: Env): Env :=
  List.getPrefix a b

-- check if variable of env can be used in env' (allows different orders in envs)
def Env.isCompatibleWith (env env': Env): Bool :=
  match env with
  | [] => true
  | .func _ i :: env => Env.isCompatibleWith env env' && env'.definesPar i
  | .forc _ i :: env => Env.isCompatibleWith env env' && env'.definesPar i
  | .itec cond val :: env => Env.isCompatibleWith env env' &&
    let rec containsItec: Env → Bool
    | [] => false -- todo auch andere param prüfen
    | .func _ _ :: env' | .forc _ _ :: env' => containsItec env'
    | .itec cond' val' :: env' => (cond == cond' && val==val') || containsItec env'
    containsItec env'

-- todo refs
def AINF.valid' (vars: ListMap Var (λ _ => Env)) (a: AINF α): Bool :=
  let lookup: {γ: Ty} → VPar γ → Option Env := λ
    | .v v => vars.lookup v
    | .p _ => some .nil
  let checkVPar (env: Env): {γ: Ty} → VPar γ → Bool := λ
      -- used Vars need to be defined in a compatible env
    | .v v => vars.lookup v |>.filter (·.isCompatibleWith env) |>.isSome
      -- used par need to be defined in the envenv.isCompatibleWith env' &&
    | .p p => env.definesPar p
  let rec checkEnv: Env → Bool -- todo check for multiple definitions of one par
    | [] => true
    | .func _ _ :: env' | .forc _ _ :: env' => checkEnv env'
    | .itec cond _ :: env' => checkVPar env' cond

  match a with
  | ([], ret) => match lookup (.v ret)  with
    | some .nil => true -- return var needs to have empty env
    | _ => false
  | (⟨⟨β,v⟩, env, prim⟩ :: rest, ret)  =>
    (vars.lookup v |>.isNone) && -- var isn't defined yet
    valid' (⟨β, v, env⟩ :: vars) (rest, ret) && -- recursive check
    checkEnv env && -- used conditions need to be valid
    match prim with -- used VPars need to be valid
    | .err           => true -- tothink
    | .var v         => checkVPar env v
    | .cst0 _        => true
    | .cst1 _ v      => checkVPar env v
    | .cst2 _ v1 v2  => checkVPar env v1 && checkVPar env v2
    | .ite cond a b  => checkVPar env cond
                        && checkVPar (.itec cond true :: env)  a
                        && checkVPar (.itec cond false :: env) b
    | .abs (α:=β) par v => checkVPar (.func β par :: env) v
    | .bld (n:=n) i v   => checkVPar (.forc n i :: env)   v

def AINF.valid (a: AINF α): Bool := a.valid' []


----- lins ------

@[reducible]
def Ty.linArg: Ty → Ty
| .unit
| .nat
| .idx _
| .lin       => .unit
| α ×× β     => α.linArg ×× β.linArg
| .array n α => .array n α.linArg
| .list α    => .list α.linArg
| .flt       => .lin
| α ~> β     => α ~> β.linArg

@[reducible]
def Ty.linRet := Ty.linArg

@[reducible]
def Ty.linFun: Ty → Ty → Ty
| α, β => α.linArg ~> β.linRet

def Tm.zero (α: Ty): Tm Γ α :=
  match α with
  | .lin => tlitlZ
  | _ ~> β => Tm.abs (λ _ => Tm.zero β)
  | α ×× β => Tm.cst2 Const2.tup (Tm.zero α) (Tm.zero β)
  | .array _ α => Tm.bld (λ _ => Tm.zero α)
  | .unit => ()'
  | .nat => tlitn 0
  | .idx _ => tlitiZ
  | .flt => tlitf 0
  | .list _ => tlitlE

def Tm.one (α: Ty): Tm Γ α :=
  match α with
  | .lin => panic! "Tm.one: no lin one"
  | _ ~> β => Tm.abs (λ _ => Tm.one β)
  | α ×× β => Tm.cst2 Const2.tup (Tm.one α) (Tm.one β)
  | .array _ α => Tm.bld (λ _ => Tm.one α)
  | .unit => ()'
  | .nat => tlitn 1
  | .idx _ => panic! "Tm.one doesn't support idx"
  | .flt => tlitf 1
  | .list _ => tlitlE

def Tm.sum (a b: Tm Γ α): Tm Γ α :=
  match α with
  | .lin => a + b
  | .unit => ()'
  | _ ×× _ => (
      Tm.sum a.fst b.fst,,
      Tm.sum a.snd b.snd
    )
  | .array _ _ => for' i => Tm.sum a[[i]] b[[i]]
  | _ ~> _ => fun' p => Tm.sum (a @@ p) (b @@ p)
  | .nat => a + b
  | .flt => a + b
  | .idx _ => panic! "Tm.sum doesn't support idx"
  | .list _ => a ++ b

def Tm.sumArray (arr: Tm Γ (.array n α)): Tm Γ α :=
  match α with
  | .lin => arr.suml
  | .unit => ()'
  | _ ×× _ => (
      (for' i => arr[[i]].fst).sumArray,,
      (for' i => arr[[i]].snd).sumArray
    )
  | _ ~> _ => fun' a => (for' i => arr[[i]] @@ a).sumArray
  | .array _ _ => for' j => (for' i => arr[[i]][[j]]).sumArray
  | .flt => arr.sumf
  | .nat => panic! "Tm.sumArray doesn't support nat"
  | .idx _ => panic! "Tm.sumArray doesn't support idx"
  | .list _ => arr.foldA (fun' x => fun' y => Tm.append x y) (Tm.zero _)

def Tm.linZero (α: Ty): Tm Γ α :=
  match α with
  | .lin => tlitlZ
  | _ ~> β => Tm.abs (λ _ => Tm.linZero β)
  | α ×× β => Tm.cst2 Const2.tup (Tm.linZero α) (Tm.linZero β)
  | .array _ α => Tm.bld (λ _ => Tm.linZero α)
  | .unit => ()'
  | .nat | .idx _ | .flt => panic! "Tm.linZero does not support this type"
  | .list _ => tlitlE -- because of copower dr

def Tm.sumLins (a b: Tm Γ α): Tm Γ α :=
  match α with
  | .lin => a + b
  | .unit => ()'
  | _ ×× _ => (
      Tm.sumLins a.fst b.fst,,
      Tm.sumLins a.snd b.snd
    )
  | _ ~> _ => fun' p => Tm.sumLins (a @@ p) (b @@ p)
  | .array _ _ => for' i => Tm.sumLins a[[i]] b[[i]]
  | .nat | .idx _ | .flt => panic! "sumArrayOfLins not supported for non linear types"
  | .list _ => a ++ b

def Tm.sumArrayOfLins (arr: Tm Γ (.array n α)): Tm Γ α :=
  match α with
  | .lin => arr.suml
  | .unit => ()'
  | _ ×× _ => (
      (for' i => arr[[i]].fst).sumArrayOfLins,,
      (for' i => arr[[i]].snd).sumArrayOfLins
    )
  | .array _ _ => for' j => (for' i => arr[[i]][[j]]).sumArrayOfLins
  | _ ~> _ => fun' a => (for' i => arr[[i]] @@ a).sumArrayOfLins
  | .nat | .idx _ | .flt => panic! "sumArrayOfLins not supported for non linear types"
  | .list _ => arr.foldA (fun' x => fun' y => Tm.append x y) (Tm.zero _)

def Tm.synBEq': {α: Ty} → Tm VPar α → Tm VPar α → VParM Bool
| _, .err, .err => return true
| _, .cst0 c, .cst0 c' => return c == c'
| _, .cst1 c a (α₁:=α₁), .cst1 c' a' (α₁:=α₁')=>
    if t:α₁=α₁'
      then return c==t▸c' ∧ (←a.synBEq' (t▸a'))
      else return false
| _, .cst2 c a b (α₁:=α₁) (α₂:=α₂), .cst2 c' a' b' (α₁:=α₁') (α₂:=α₂')=>
    if ta:α₁=α₁' then if tb:α₂=α₂'
      then return c==tb▸ta▸c' ∧ (←a.synBEq' (ta▸a')) ∧ (←b.synBEq' (tb▸b'))
      else return false else return  false
| _, .abs f (α:=α) (β:=β), .abs f' => do
    let v := (←VParM.parVPar) α
    (f v).synBEq' (f' v)
| _, .bld f (n:=n) (α:=α), .bld f' => do
    let v := (←VParM.parVPar) (Ty.idx n)
    (f v).synBEq' (f' v)
| _, .ite cond a b, .ite cond' a' b' =>
    return (← cond.synBEq' cond')
    ∧ (← a.synBEq' a')
    ∧ (← b.synBEq' b')
| _, .var v, .var v' => return v == v'
| _, .bnd t f (α:=α), .bnd t' f' (α:=α') => do
    if h: α=α' then
      if ←t.synBEq' (h▸t')
        then
          let v := (←VParM.varVPar) α
          (f v).synBEq' (f' (h▸v))
        else return false
    else return false
| _, _,  _ => return false

def Tm.synBEq: {α: Ty} → Tm VPar α → Tm VPar α → Bool
| _, a, b => (VParM.startZero (a.synBEq' b))
