import Polara.Syntax.All

-- renaming -----------------------------------
private abbrev Ren := ListMap Var Var

private def Var.rename (r: Ren)(v: Var α): Var α :=
  r.lookup v |>.getD v
private def VPar.rename (r: Ren): VPar α → VPar α
| .v x => .v (x.rename r)
| .p x => .p x

private def EnvPart.rename (r: Ren): EnvPart → EnvPart
| func α p     => func α p
| forc n p     => forc n p
| itec i true  => itec (i.rename r) true
| itec i false => itec (i.rename r) false
private def Env.rename (r: Ren)(env: Env): Env :=
  env.map (EnvPart.rename r)

private def Prim.rename (r: Ren): Prim α → Prim α
| .cst0 k => .cst0 k
| .cst1 k a => .cst1 k (a.rename r)
| .cst2 k a b => .cst2 k (a.rename r) (b.rename r)
| .err       => .err
| .var x     => .var x
| .abs i e   => .abs i (e.rename r)
| .ite a b c => .ite (a.rename r) (b.rename r) (c.rename r)
| .bld i f => .bld i (f.rename r)
private def Bnd.rename (r: Ren): Bnd → Bnd
| ⟨⟨_,i⟩, env, prim⟩ => ⟨⟨_, i.rename r⟩, env.rename r, prim.rename r⟩

private def AINF.rename (r: Ren): AINF α → AINF α
| (bnds, ret) => (bnds.map (Bnd.rename r), ret.rename r)
-----------------------------------------------

-- Trilean Left Right Middle
private inductive Tern where | L | R | M
-- intersection of two environments
private def Env.unify?' (t: Tern): Env → Env → Option Env
-- keep if identical
| [],         []        => return []
| .func α p :: env, .func β q :: env' =>
    if p.eq q then return .func α p :: (<- unify?' t env env') else none
| .forc n p :: env, .forc m q :: env' =>
  if p.eq q then return .forc n p :: (<- unify?' t env env') else none
| .itec i b :: env, .itec j d :: env' =>
  if i==j then
    if b==d
    then return .itec i b :: (<- unify?' t env env')  -- keep
    else return      (<- unify?' t env env')      -- (i=T||i=F) <-> T
  else none
-- keep itec if on Trilean side or Middle
| .itec _ _ :: env, env' => match t with
  | .L | .M => unify?' .L env env'
  | .R => none
| env, .itec _ _ :: env' => match t with
  | .L => none
  | .M | .R => unify?' .R env env'
-- else none
| _, _ => none
private def Env.unify?: Env → Env → Option Env := unify?' .M

private def Bnd.unify?: Bnd → Bnd → Option (Bnd × ((α: Ty) × Var α × Var α))
| ⟨⟨α,v⟩,env,prim⟩, ⟨⟨α',v'⟩,env',prim'⟩ => do
    if h: α=α' then do
      .guardCond (h▸prim == prim')
      let env ← env.unify? env'
      return (⟨⟨_,v⟩,env,prim⟩, ⟨α,h▸v',v⟩)
    else none

private def Bnds.unify?' (optBnds: Bnds)(bnd': Bnd): Bnds → Option (Bnds × ((α: Ty) × Var α × Var α))
| [] => none
| (bnd: Bnd) :: bnds =>
  match bnd.unify? bnd' with
  | none => unify?' (optBnds.concat bnd) bnd' bnds
  | some (bnd, rEle) => some (optBnds.append (bnd :: bnds), rEle)
private def Bnds.unify? := Bnds.unify?' []

private def AINF.cse' (r: Ren) (optBnds: Bnds)(ret: Var α): Bnds → AINF α
| [] => (optBnds, ret.rename r)
| (bnd: Bnd) :: bnds => let bnd := bnd.rename r
  match Bnds.unify? bnd optBnds with
  | none => cse' r (optBnds.concat bnd) ret bnds
  | some (optBnds,rEle) => cse' (rEle :: r) optBnds ret bnds

def AINF.cse: AINF α → AINF α
| (bnds, ret) => cse' [] [] ret bnds
