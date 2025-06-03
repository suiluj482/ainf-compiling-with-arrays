import Polara.Syntax.Definitions

def AINF.size : AINF α → Nat
  | .ret _ => 0
  | .bnd _ _ _ p => p.size + 1

-- ReaderMonad for access to original AiNF
@[reducible] def Orig α := ∀ {β}, ReaderM (AINF β) α

-- lookup enviroment in binding of variable
def Var.lookupEnv (x: Var α) : AINF β → Option Env
  | .ret _y => none
  | .bnd (α:=β) env (y: Var β) _prim rest =>
    if h: β=α then if h▸ y==x then env
    else lookupEnv x rest else lookupEnv x rest
def VPar.lookupEnv (a: AINF β) (v: VPar α): Option Env :=
  match v with
  | .v v => v.lookupEnv a
  | .p _ => some <| .nil

-- check if env defines parameter
def Env.definesPar (env: Env) (i: Par α): Bool :=
  match env with
  | .nil => false
  | .func env' α' i' => (if h: α=α'        then h▸ i==i' else false) || env'.definesPar i
  | .forc env' n' i' => (if h: α=(Ty.idx n')  then h▸ i==i' else false) || env'.definesPar i
  | .itec env' _ _ => env'.definesPar i

def Env.isPrefixOf: Env → Env → Bool
| .nil, _ => true
| _, .nil => false
| .func env α i, .func env' α' i' => env.isPrefixOf env' && if h: α=α' then h▸ i==i' else false
| .forc env n i, .forc env' n' i' => env.isPrefixOf env' && if h: n=n' then h▸ i==i' else false
| .itec env i b, .itec env' i' b' => env.isPrefixOf env' && i==i' && b==b'
| _, _ => false

-- check if variable of env can be used in env' (allows different orders in envs)
def Env.isCompatibleWith (env env': Env): Bool :=
  match env with
  | .nil => true
  | .func env _ i => env.isCompatibleWith env' && env'.definesPar i
  | .forc env _ i => env.isCompatibleWith env' && env'.definesPar i
  | .itec env cond val => env.isCompatibleWith env' &&
    let rec containsItec: Env → Bool
    | .nil => false -- todo auch andere param prüfen
    | .func env' _ _ | .forc env' _ _ => containsItec env'
    | .itec env' cond' val' => (cond == cond' && val==val') || containsItec env'
    containsItec env'

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
    | .nil => true
    | .func env' _ _ | .forc env' _ _ => checkEnv env'
    | .itec env' cond _ => checkVPar env' cond

  match a with
  | .ret v => match lookup v  with
    | some .nil => true -- return var needs to have empty env
    | _ => false
  | .bnd (α:=β) env v prim rest =>
    (vars.lookup v |>.isNone) && -- var isn't defined yet
    valid' (⟨β, v, env⟩ :: vars) rest && -- recursive check
    checkEnv env && -- used conditions need to be valid
    match prim with -- used VPars need to be valid
    | .err           => true -- tothink
    | .var v         => checkVPar env v
    | .cst0 _        => true
    | .cst1 _ v      => checkVPar env v
    | .cst2 _ v1 v2  => checkVPar env v1 && checkVPar env v2
    | .ite cond a b  => checkVPar env cond
                        && checkVPar (Env.itec env cond true)  a
                        && checkVPar (Env.itec env cond false) b
    | .abs (α:=β) par v => checkVPar (Env.func env β par) v
    | .bld (n:=n) i v   => checkVPar (Env.forc env n i)   v

def AINF.valid (a: AINF α): Bool := a.valid' []
