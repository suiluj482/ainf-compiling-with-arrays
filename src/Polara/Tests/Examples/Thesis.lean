import Polara.Optimizations.All
import Polara.AD.All

open Ty


--- cse ---

def cseFun := (
    let' f1 := (fun' a => (tlitf 2 * a) + tlitf 10);
    let' f2 := (fun' a => (tlitf 2 * a) + tlitf 11);
    fun' a => (f1 @@ a) + (f2 @@ a)
  ).toVPar

#eval cseFun
#eval cseFun.toAINF
#eval cseFun.toAINF.cse
#eval cseFun.toAINF.cse.toTm.normVPar

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
#eval cseBreakFun.toAINF.cleanEnv
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

  def higherOrderDF :=
    (fun' g:(flt ~> flt) => fun' x => (g @@ x) * (g @@ x) + tlitf 10 ).df

  #eval higherOrderDF.normVPar

  def higherOrderDF' :=
    (fun' g:(flt ~> flt) => g @@ tlitf 0 ).df

end AD
