import Polara.Syntax.Index
import Polara.Optimizations.CSE

-- variable type in target language needs to consider environment
@[reducible]
def EnvPart.tygenTm (t: Ty) (env: EnvPart): Ty := match env with
  | .func α _i  => (α ~> t)
  | .forc n _i  => (Ty.array n t)
  | .itec _i _m => t

def Env.tygenTm (env: Env): Ty → Ty :=
  env.foldl EnvPart.tygenTm

def RenParTm (Γ: Ty → Type) := ListMap Par Γ
def RenParTm.apply (ren: RenParTm Γ) (x: Par α): Tm Γ α :=
  match ren.lookup x with
  | some x' => Tm.var x'
  | none    => Tm.err

def EnvVar (Γ: Ty → Type)(α: Ty) := (env: Env) × Γ (env.tygenTm α)
def RenVarTm (Γ: Ty → Type) := ListMap Var (EnvVar Γ)

structure RenTm (Γ: Ty → Type) where
 par: RenParTm Γ
 var: RenVarTm Γ
def RenTm.addPar (ren: RenTm Γ) (x: Par α) (y: Γ α): RenTm Γ :=
  { ren with par := ⟨_, x, y⟩ :: ren.par }
def RenTm.addVar (ren: RenTm Γ) (x: Var α) (y: EnvVar Γ α): RenTm Γ :=
  { ren with var := ⟨_, x, y⟩ :: ren.var }

def Env.withargsTm (env: Env)(ren: RenParTm Γ)(x: Tm Γ (env.tygenTm α)): Tm Γ α :=
  match env with
  | []           => x
  | .func _α i :: env' =>
      Tm.cst2 Const2.app (Env.withargsTm env' ren x) (ren.apply i)
  | .forc _n i :: env' =>
      Tm.cst2 Const2.get (Env.withargsTm env' ren x) (ren.apply i)
  | .itec _i _b :: env' => Env.withargsTm env' ren x

def RenTm.apply (ren: RenTm Γ) (x: VPar α): Tm Γ α :=
  match x with
  | .v v => match ren.var.lookup v with
    | some ⟨env, x'⟩ => env.withargsTm ren.par (Tm.var x')
    | none           => Tm.err
  | .p p => ren.par.apply p

def Prim.toTm (_env: Env)(ren: RenTm Γ): Prim α → Tm Γ α
| err           => Tm.err
| var v         => ren.apply v
| cst0 c        => Tm.cst0 c
| cst1 c v      => Tm.cst1 c (ren.apply v)
| cst2 c v1 v2  => Tm.cst2 c (ren.apply v1) (ren.apply v2)
| ite cond a b  => Tm.ite (ren.apply cond) (ren.apply a) (ren.apply b)
| abs par v => fun'v x => (
    let ren := ren.addPar par x
    ren.apply v
  )
| bld idx v => for'v x => (
    let ren := ren.addPar idx x
    ren.apply v
  )

-- wrap environment around term depending on done renamings
def Env.wrapTm (ren: RenTm Γ)(k: RenTm Γ → Tm Γ α)(env: Env): (Tm Γ (env.tygenTm α)) :=
  match env with
  | [] => k ren
  | .func _ i :: env =>
      Env.wrapTm ren (λ ren => fun'v i' =>
        let ren' := ren.addPar i i'
        k ren'
      ) env
  | .forc _ i :: env =>
      Env.wrapTm ren (λ ren => for'v i' =>
        let ren' := ren.addPar i i'
        k ren'
      ) env
  | .itec cond true :: env =>
      Env.wrapTm ren (λ ren =>
        let cond' := ren.apply cond
        if' cond' then k ren else Tm.err -- undefined instead?
      ) env
  | .itec cond false :: env =>
      Env.wrapTm ren (λ ren =>
        let cond' := ren.apply cond
        if' cond' then Tm.err else k ren -- undefined instead?
      ) env

-- todo zeta reduction for env to prim
def AINF.toTm'(a: AINF α)(ren: RenTm Γ): Tm Γ α :=
  match a with
  | ([], v) => match v with
    | .v v => match ren.var.lookup v with
      | some ⟨.nil, x'⟩ => Tm.var x'
      | _               => Tm.err
    | .p p => ren.par.apply p
  | (⟨⟨_,v⟩, env, prim⟩ :: rest, ret) =>
    let'v v' := env.wrapTm ren (λ ren' => prim.toTm env ren');
    AINF.toTm' (rest, ret) (ren.addVar v ⟨env, v'⟩)

def AINF.toTm (a: AINF α): Tm Γ α := a.toTm' ⟨[], []⟩

-----------------------------------------------------------

def Tm.inst (α: Ty): Tm Γ α :=
  match α with
  | .nat => Tm.cst0 (Const0.litn 0)
  | .idx _ => Tm.cst0 (Const0.liti 0)
  | .flt => Tm.cst0 (Const0.litf 0)
  | .lin => Tm.cst0 (Const0.litl 0)
  | _ ~> β => Tm.abs (λ _ => Tm.inst β)
  | α ×× β => Tm.cst2 Const2.tup (Tm.inst α) (Tm.inst β)
  | .array _ α => Tm.bld (λ _ => Tm.inst α)
