
-- unzip
-- (flt × lin) ~> (flt × lin)
-- => flt ~> (flt, lin ~> lin)

-- flt ~> (flt ~> flt)
-- flt ×× flt ~> flt
-- lin ~> lin ×× lin
-- flt ~> (flt ~> (flt ×× (lin ~> lin ~> lin))) forward mode
-- flt ~> (flt ~> (flt ×× (lin ~> lin (ptr as error hilfe) ×× lin))) backward mode

-- f: (flt ×× lin) ~> (flt ×× lin) ~> (flt ×× lin)
-- f (3.14, 0) (2.2, 1) = (f ..., f' ...)

-- g: (flt ×× ref lin) ~> (flt ×× ref lin) ~> (flt ×× ref lin)
-- g (3, ref (x')) (2, ref (y')) = (g ..., zref)
-- zref *:= 1
--

-- (flt × lin × (flt × lin)) ~> (flt × lin)

-- (flt × rlin × (flt × rlin)) ~> (flt × rlin)
-- rlin := lin ~> Empty -- spring nicht mal mehr zurück, False kein element
-- bei codegeneration schreiben in variable
-- in Polara sonderfall

-- funktion die output als argument angibt
-- binding construct

-- (3.14 (λ x => ??) 2.2 (λ x => ??)) ~> (1.0 f))
-- f 1.2
--

-- (flt × flt) ~> (flt, lin × lin ~> lin)

-- (flt × flt) ~> (flt, lin ~> lin × lin)
-- (flt × flt × lin) ~> (flt × lin × lin)

-- (flt × lin) ~> (flt × lin) ~> (flt × lin)
-- => flt ~> (flt, lin ~> lin ~> lin)
-- how to later know which argument is which?

-- transpose
-- (lin ×× lin ~> lin).transpose
-- => lin ~> lin ×× lin
-- (lin ~> lin ~> lin).transpose
-- => ???



@[reducible]
def Ty.liftTup: Ty → Ty
| array n (α ×× β) => (array n α) ×× (array n β)
| α ~> (β ×× γ) => (α ~> β) ×× (α ~> γ) -- to AINF funktionen zerlegen

| _ => nat

-- lieber ainf erweiteren als unzipping

@[reducible]
def Ty.combineFuncs: Ty → Ty
| α ~> (β ~> γ) => (α ×× β) ~> γ.combineFuncs
| α => α

#eval (Ty.flt ~> Ty.flt ~> Ty.flt).combineFuncs

@[reducible]
def Ty.unzip': Ty → (Option Ty × Option Ty)
| nat => (nat, none)
| idx n => (idx n, none)
| flt => (flt, none)
| lin => (none, lin)
| α ~> β =>
    let (α, αl) := α.unzip'
    let (β, βl) := β.unzip'
    (
      Option.comBinOp (· ~> ·) (some ·) α β,
      Option.comBinOp (· ~> ·) (some ·) αl βl,
    )
| α ×× β =>
    let (α, αl) := α.unzip'
    let (β, βl) := β.unzip'
    (
      Option.comBinOp (· ×× ·) (some ·) α β,
      Option.comBinOp (· ×× ·) (some ·) αl βl,
    )
| array n α =>
    let (α, αl) := α.unzip'
    (return array n (←α), return array n (←αl))

@[reducible]
def Ty.unzip (t: Ty): Ty × Ty :=
  t.unzip'.mapM.get!

#eval ((Ty.flt ×× Ty.lin)).unzip'
#eval ((Ty.flt ×× Ty.lin)~>(Ty.flt ×× Ty.lin)).unzip'
#eval ((Ty.flt ×× Ty.lin)~>(Ty.flt ×× Ty.lin)~>(Ty.flt ×× Ty.lin)).unzip'
-- (flt × lin) ~> (flt × lin) => flt ~> (flt, lin ~> lin)

@[reducible]
def Ty.transposable': Ty → Bool
| lin => true
| α ×× β => α.transposable' && β.transposable'
| array _ α => α.transposable'
| _ => false
@[reducible]
def Ty.transposable: Ty → Bool
| α ~> β => α.transposable' && β.transposable'
| _ => false
