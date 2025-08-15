import Interval.Box.Basic

/-!
## Mandelbrot iteration

We iterate until either a cutoff is reached or we exceed a given radius, recording why we stopped.

See `Correct.Iterate` for correctness proofs.
-/

open Set

private local instance : Fact (2 ≤ 2) := ⟨by norm_num⟩

/-- Why we exited out of an iteration -/
inductive Exit : Type
  | count
  | large
  | nan
  deriving DecidableEq, Repr

/-- An iteration result -/
structure Iter where
  /-- The final value after iteration -/
  z : Box
  /-- Number of steps taken -/
  n : ℕ
  /-- Why we stopped iterating -/
  exit : Exit
  deriving Repr

/-- Helper for `iterate` -/
def iterate' (c z : Box) (rs : Floating) (k n : ℕ) : Iter := match n with
  | 0 => ⟨z, k, .count⟩
  | n + 1 =>
    -- Conveniently, `z.re.sqr` and `z.im.sqr` are needed by both iteration and squared magnitude
    let zr2 := z.re.sqr
    let zi2 := z.im.sqr
    let z2 := zr2.lo.add zi2.lo false
    if z2 = nan then ⟨z, k, .nan⟩ else  -- We hit nan, so stop computing
    if rs < z2 then ⟨z, k, .large⟩ else  -- Early exit if we know that `r ≤ |z|`
    let zri := z.re * z.im
    let w := ⟨zr2 - zi2, zri.scaleB 1⟩ + c
    iterate' c w rs (k+1) n

/-- Iterate until we reach a given count or definitely exceed a given squared radius.
    Returns the final iterate, and the number of steps taken. -/
def iterate (c z : Box) (rs : Floating) (n : ℕ) : Iter :=
  if rs = nan then ⟨z, 0, .nan⟩ else
  iterate' c z rs 0 n
