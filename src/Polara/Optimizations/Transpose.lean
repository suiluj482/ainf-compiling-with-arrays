import Polara.Syntax.Index
import Polara.Optimizations.CSE

def Const2.t (cst2: Const2 α β γ): RAINF :=
match cst2 with
| arithOp op =>
  match op with
  | .mul => -- check if linear umdrehen


-- lineare <-> nicht lineare Variable? argumente oder rückgabewert
def Prim.transpose (env: Env)(v: Var α)(p: Prim α): RAINF :=
  if α == Ty.lin then  -- panic bei mult weil lin linear
    match p with
    | .cst2 k a b =>
  else

def transpose (a: AINF α)
    b

def collection -- mehrfach deklarationen in summe packen
