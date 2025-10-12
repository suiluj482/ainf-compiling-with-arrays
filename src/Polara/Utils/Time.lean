def Nat.toMillis (n: Nat): Float := (n.toFloat / 1000.0)

def benchmark (a: α)(f: α → β): IO (β × Float) := do
  let start ← IO.monoNanosNow
  let res := f a
  let stop ← IO.monoNanosNow
  return (res, (stop - start).toMillis)

def benchmarkIO (u: IO α): IO (α × Float) := do
  let start ← IO.monoNanosNow
  let res ← u
  let stop ← IO.monoNanosNow
  return (res, (stop - start).toMillis)

def benchmarkIOF (a: α)(f: α → IO β): IO (β × Float) := do
  let start ← IO.monoNanosNow
  let res ← f a
  let stop ← IO.monoNanosNow
  return (res, (stop - start).toMillis)



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
