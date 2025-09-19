import Polara.Syntax.Definitions
import Polara.Syntax.PrettyPrint
import Polara.Syntax.Notations

@[reducible]
def Ty.transform (f: Ty → Ty) : Ty → Ty
| .nat => f .nat
| .idx n => f (.idx n)
| flt => f .flt
| lin => f .lin
| α ~> β => f (α.transform f ~> β.transform f)
| α ×× β => f (α.transform f ×× β.transform f)
| array n α => f (array n (α.transform f))
| ref α => f (ref (α.transform f))
| unit => f .unit

@[reducible]
def Ty.contains (t: Ty)(f: Ty → Bool): Bool :=
  match t with
  | .nat => f nat
  | .flt => f flt
  | .lin => f lin
  | .idx n => f (idx n)
  | .ref α => f (ref α) ∨ α.contains f
  | .unit => f unit
  | α ×× β => f t ∨ α.contains f ∨ β.contains f
  | .array _ α => f t ∨ α.contains f
  | α ~> β => f t ∨ α.contains f ∨ β.contains f

theorem Ty.contains_product_a (α: Ty)(β: Ty)(f: Ty → Bool):
  Ty.contains (α ×× β) f = false → Ty.contains α f = false := by simp[Ty.contains]; exact λ _ a _ => a
theorem Ty.contains_product_b (α: Ty)(β: Ty)(f: Ty → Bool):
  Ty.contains (α ×× β) f = false → Ty.contains β f = false := by simp[Ty.contains]
theorem Ty.contains_array (n: Nat)(α: Ty)(f: Ty → Bool):
  Ty.contains (array n α) f = false → Ty.contains α f = false := by simp[Ty.contains]
theorem Ty.contains_arrow_a (α: Ty)(β: Ty)(f: Ty → Bool):
  Ty.contains (α ~> β) f = false → Ty.contains α f = false := by simp[Ty.contains]; exact λ _ a _ => a
theorem Ty.contains_arrow_b (α: Ty)(β: Ty)(f: Ty → Bool):
  Ty.contains (α ~> β) f = false → Ty.contains β f = false := by simp[Ty.contains]
theorem Ty.contains_ref (α: Ty)(f: Ty → Bool):
  Ty.contains (α.ref) f = false → Ty.contains α f = false := by simp[Ty.contains]

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
def VParM.vpar : VParM ((β: Ty) → VPar β) :=
  modifyGet fun i => (
    λ _ => (.v (.mk i.down.fst)),
    ⟨i.down.map id (·+1)⟩
  )
def VParM.rPar: VParM Unit :=
  modify fun ⟨(i,_)⟩ => ⟨(i,0)⟩
def AINF.findFreshVars: AINF α → Nat × Nat
| (bnds, _) => bnds.foldl (λ (x, i) ⟨⟨_,⟨n⟩⟩, _, prim⟩ =>
    (
      x.max n,
      match prim with
      | .abs ⟨n⟩ _
      | .bld ⟨n⟩ _ => i.max n
      | _ => i
    )
  ) (0, 0)
def VParM.freshAINFVars (a: AINF α)(m: VParM β): β :=
  m ⟨a.findFreshVars⟩ |>.fst

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
      | none   => Tm.err
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
| (bnds, v) => ((bnds.flatMapM f).freshAINFVars a, v.changeType)

-- check if env defines parameter
def EnvPart.definesPar (i: Par α): EnvPart → Bool
| .func _ i' => Some.of i' == Some.of i
| .forc _ i' => Some.of i' == Some.of i
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
  | ([], ret) => match lookup ret  with
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
| .ref _     => panic! "ref not supported in automatic differentiation"
| .flt       => .lin
| α ~> β     => α ~> β.linArg

@[reducible]
def Ty.linRet := Ty.linArg

@[reducible]
def Ty.linFun: Ty → Ty → Ty
| α, β => α.linArg ~> β.linRet

def Tm.linZero (α: Ty): Tm Γ α :=
  match α with
  | .lin => Tm.cst0 (Const0.litl 0)
  | _ ~> β => Tm.abs (λ _ => Tm.linZero β)
  | α ×× β => Tm.cst2 Const2.tup (Tm.linZero α) (Tm.linZero β)
  | .array _ α => Tm.bld (λ _ => Tm.linZero α)
  | .unit => ()'
  | .nat | .idx _ | .flt => panic! "Tm.linZero does not support this type"
  | .ref _ => panic! "Tm.linZero does not support references"

def Tm.sumLins (a b: Tm Γ α): Tm Γ α :=
  match α with
  | .lin => a + b
  | .unit => ()'
  | _ ×× _ => (
      Tm.sumLins a.fst b.fst,,
      Tm.sumLins a.snd b.snd
    )
  | .array _ _ => for' i => Tm.sumLins a[[i]] b[[i]]
  | _ ~> _ => fun' p => Tm.sumLins (a @@ p) (b @@ p)
  | .nat | .idx _ | .flt => panic! "sumArrayOfLins not supported for non linear types"
  | .ref _ => panic! "sumArrayOfLins not supported for references"

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
  | .ref _ => panic! "sumArrayOfLins not supported for references"
