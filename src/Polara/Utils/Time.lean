def Nat.toSec (n: Nat): Float := (n.toFloat / 1000.0)

def benchmark (a: α)(f: α → β): IO (β × Float) := do
  let start ← IO.monoMsNow
  let res := f a
  let stop ← IO.monoMsNow
  return (res, (stop - start).toSec)

def benchmarkIO (u: IO α): IO (α × Float) := do
  let start ← IO.monoMsNow
  let res ← u
  let stop ← IO.monoMsNow
  return (res, (stop - start).toSec)

def benchmarkIOF (a: α)(f: α → IO β): IO (β × Float) := do
  let start ← IO.monoMsNow
  let res ← f a
  let stop ← IO.monoMsNow
  return (res, (stop - start).toSec)

abbrev BenchRes := Nat × Float -- iterations, time
def BenchRes.mk: BenchRes := (0,0)
def BenchRes.bench: BenchRes := (100, 1*60)
def BenchRes.test: BenchRes := (1, 0)
def BenchRes.it: BenchRes → Nat := Prod.fst
def BenchRes.time: BenchRes → Float := Prod.snd
def BenchRes.avTime: BenchRes → Float | (i,t) => t / i.toFloat
def BenchRes.add: BenchRes → Float → BenchRes
| (it, time), t => (it+1, time+t)
def BenchRes.lt: BenchRes → BenchRes → Bool
| (i, t), (i', t') => i<i' ∧ t<t'

partial def benchmarkIOMult' (res: BenchRes)(limit: BenchRes)
(u: IO α): IO (α × BenchRes) := do
  let (b, t) ← benchmarkIO u;
  let res := res.add t
  if res.lt limit then
    benchmarkIOMult' res limit u
  else
    return (b, res)

def benchmarkIOM (u: IO α)(limit := BenchRes.test)
: IO (α × BenchRes) :=
  benchmarkIOMult' .mk limit u

-----Tests----
-- def fib (n: Nat): Nat :=
--   if n ≤ 1 then n else fib (n-1) + fib (n-2)

-- def fibFast (n: Nat): Nat :=
--   let rec go (a b: Nat): Nat → Nat
--     | 0 => a
--     | n+1 => go b (a+b) n
--   go 0 1 n

-- #eval benchmark 30 fib
-- #eval benchmark 30 fibFast

-- #eval benchmarkIO (do IO.sleep 20; IO.println "Hello, world!")
