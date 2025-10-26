import Polara.Optimizations.All
import Polara.AD.All

open Ty


--- cse ---

def cseFun := (
    let' f1 := (fun' a => (tlitf 2 * a) + tlitf 10);
    let' f2 := (fun' a => (tlitf 2 * a) + tlitf 11);
    (f1,, f2)
  ).toVPar

#eval cseFun
#eval cseFun.toAINF
#eval cseFun.toAINF.cse
#eval cseFun.toAINF.cse.fusion

def cseFor := (
    let' f1 := (for' i:5 => i.i2n + tlitn 10);
    let' f2 := (for' i:5 => i.i2n + tlitn 11);
    fun' i => (f1[[i]]) + (f2[[i]])
  ).toVPar

#eval cseFor
#eval cseFor.toAINF
#eval cseFor.toAINF.cse
#eval cseFor.toAINF.cse.toTm.normVPar

def cseBreakFun := (
    let' f1 := (fun' a => (tlitf 2 * a) + tlitf 10);
    let' f2 := (fun'v _ => fun' a => (tlitf 2 * a) + tlitf 11);
    fun' a => (f1 @@ a) + (f2 @@ ()' @@ a)
  ).toVPar

#eval cseBreakFun
#eval IO.print cseBreakFun.toAINF.toGraphviz
#eval cseBreakFun.toAINF.cse
#eval cseBreakFun.toAINF.cse.toTm.normVPar

def cseBreakFor := (
    let' f1 := (for' i:5 => i.i2n + tlitn 10);
    let' f2 := (for'v _:1 => for' i:5 => i.i2n + tlitn 11);
    fun' i => (f1[[i]]) + (f2[[tliti 0]][[i]])
  ).toVPar

#eval cseBreakFor
#eval cseBreakFor.toAINF
#eval cseBreakFor.toAINF.cse
#eval cseBreakFor.toAINF.cse.toTm.normVPar

def cseBreakFor2 := (
    let' f1 := (for' i:5 => i.i2n + tlitn 10);
    let' f2 := (for' i:5 => for'v _:1 => i.i2n + tlitn 11);
    fun' i => (f1[[i]]) + (f2[[i]][[tliti 0]])
  ).toVPar

#eval cseBreakFor2
#eval cseBreakFor2.toAINF
#eval cseBreakFor2.toAINF.cse -- envs not compatible????
#eval cseBreakFor2.toAINF.cse.toTm.normVPar


-- Conclusion: Cse capabilities of CSE have more to do with accidental fusion than fission

---- Test referential integrity
namespace RefIn

  def notDefined: Term flt :=
    (Tm.var (.v (.mk 0)))

  #eval notDefined.normVPar

  def wrongType: Term flt :=
    (let'v v := tlitn 0; Tm.var (v.changeType))
  -- type is "part of variable name"
  #eval wrongType.normVPar

  def dfInEnv :=
    (fun' x:flt => x).df

  #eval dfInEnv.normVPar

  def dfDiffEnvs :=
    (let' v := tlitf 0; fun'v _:nat => v).df

  #eval dfDiffEnvs.normVPar

  def dfOutside :=
    let' v := tlitf 0; (fun'v _:nat => v).df

  #eval dfOutside.normVPar

end RefIn

namespace AD

  def fp :=
    (fun' g:(flt ~> flt) => g@@ tlitf 0).toVPar
  #eval fp.getTy

  def fr :=
    (fun' x:flt => (fun' y:flt => x+y)).toVPar
  #eval fr.getTy

  def simple := (
      let' a := tlitf 1;
      fun' x => x + a
    ).toVPar

  namespace DN

    #eval fp.getTy.aD
    #eval fp.aD.normVPar
    #eval fr.getTy.aD
    #eval fr.df.normVPar

  end DN

  namespace DF

    #eval simple.df

    #eval fp.getTy.df
    #eval fp.df.normVPar
    #eval fr.getTy.df
    #eval fr.df.normVPar

    def f :=
      (fun' g:(flt ~> flt) => fun' x => (g @@ x) * (g @@ x) + tlitf 10).toVPar
    #eval f.getTy
    #eval f.getTy.df
    #eval f.df.normVPar

  end DF

  namespace DR

    #eval fp.getTy.dr
    #eval fp.dr.normVPar
    #eval fr.getTy.dr
    #eval fr.dr.normVPar
    def f :=
      (fun' g:(flt ~> flt) => fun' x => (g@@ (x+tlitf 1)) - (g@@x)).toVPar
    #eval f.getTy.dr
    #eval f.dr.normVPar

  end DR

end AD

namespace Fusion

  def ex := (
    let' a1 := (for' i:5 => i.i2n + tlitn 1);
    let' a2 := (for' i:5 => i.i2n + tlitn 2);
    (a1,, a2)
  ).toVPar

  #eval IO.print ex.toAINF.toGraphviz


  #eval (tlitf 1).exp.toAINF.fusion.normVPar
  #eval (tlitf 1 + tlitf 1 * tlitf 2).toAINF.fusion.normVPar
  #eval (let' a:= tlitf 1; fun' x:flt => x+a).toAINF.fusion.normVPar
  #eval (for' i:5 => fun' x => if' x <' tlitf 0 then i.i2n.n2f + x else x).toAINF.fusion.normVPar

  #eval (fun' x => fun' y => x+y) |>.toAINF.cleanEnv.fusion.normVPar


end Fusion

-- ((⟨(Float ~> Float), x3⟩, fun i1:Float), [⟨Float, (x0, i0)⟩, ⟨Float, (x1, i1)⟩, ⟨Float, (x2, x0 + x1)⟩])
-- ((⟨(Float ~> (Float ~> Float)), x4⟩, fun i0:Float), [⟨(Float ~> Float), (x3, fun i1:Float => x2)⟩])

-- ((⟨(Float ~> Float), x3⟩, fun i1:Float), [⟨Float, (x0, i0)⟩, ⟨Float, (x1, i1)⟩, ⟨Float, (x2, x0 + x1)⟩])
-- ((⟨(Float ~> (Float ~> Float)), x4⟩, fun i0:Float), [⟨(Float ~> Float), (x3, fun i1:Float => x2)⟩])

-- (let x0 := (fun i0 =>  (let x0 := (fun i1 =>  (let x0 := i0;
--     (let x1 := i1;
--     (let x2 := (x0 + x1);
--     x2))));
--   x0));
-- x0)
