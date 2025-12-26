import Interval.Box.Basic

/-!
## Mandelbrot iteration

We iterate until either a cutoff is reached or we exceed a given radius, recording why we stopped.

See `Correct.Iterate` for correctness proofs.
-/

open Set

/-- Why we exited out of an iteration -/
inductive Exit : Type
  | count
  | large
  | nan
  deriving DecidableEq, Repr

/-- An iteration result -/
@[ext] structure Iter where
  /-- The final value after iteration -/
  z : Box
  /-- Number of steps taken -/
  n : ℕ
  /-- Why we stopped iterating -/
  exit : Exit
  deriving Repr

/-- An iteration result with derivative -/
structure DIter where
  /-- The final value after iteration -/
  z : Box
  /-- The derivative of the final value -/
  dz : Box
  /-- Number of steps taken -/
  n : ℕ
  /-- Why we stopped iterating -/
  exit : Exit
  deriving Repr

/-- Drop the derivative -/
def DIter.iter (i : DIter) : Iter := ⟨i.z, i.n, i.exit⟩

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

/-- Helper for `iterate_deriv` -/
def iterate_deriv' (c z dc dz : Box) (rs : Floating) (k n : ℕ) : DIter := match n with
  | 0 => ⟨z, dz, k, .count⟩
  | n + 1 =>
    -- Conveniently, `z.re.sqr` and `z.im.sqr` are needed by both iteration and squared magnitude
    let zr2 := z.re.sqr
    let zi2 := z.im.sqr
    let z2 := zr2.lo.add zi2.lo false
    if z2 = nan then ⟨z, dz, k, .nan⟩ else  -- We hit nan, so stop computing
    if rs < z2 then ⟨z, dz, k, .large⟩ else  -- Early exit if we know that `r ≤ |z|`
    let zri := z.re * z.im
    let w := ⟨zr2 - zi2, zri.scaleB 1⟩ + c
    let dw := z.scaleB 1 * dz + dc
    iterate_deriv' c w dc dw rs (k+1) n

/-- Iterate until we reach a given count or definitely exceed a given squared radius.
    Returns the final iterate, and the number of steps taken. -/
def iterate (c z : Box) (rs : Floating) (n : ℕ) : Iter :=
  if rs = nan then ⟨z, 0, .nan⟩ else
  iterate' c z rs 0 n

/-- Same as `iterate`, but also computes the derivative. -/
def iterate_deriv (c z dc dz : Box) (rs : Floating) (n : ℕ) : DIter :=
  if rs = nan then ⟨z, dz, 0, .nan⟩ else
  iterate_deriv' c z dc dz rs 0 n

/-!
### The natural commutative diagrams

Computing with derivatives and then dropping them is the same as computing without derivatives.
-/

variable {c z dc dz : Box} {rs : Floating} {c' z' dc' dz' : ℂ} {k n : ℕ}

@[simp] lemma iter_iterate_deriv' :
    (iterate_deriv' c z dc dz rs k n).iter = iterate' c z rs k n := by
  induction' n with n h generalizing k z dz
  · simp only [iterate_deriv', iterate', DIter.iter]
  · simp only [DIter.iter, Iter.ext_iff] at h
    simp only [DIter.iter, iterate_deriv', iterate']
    aesop

@[simp] lemma iter_iterate_deriv : (iterate_deriv c z dc dz rs n).iter = iterate c z rs n := by
  simp only [iterate_deriv, apply_ite (f := DIter.iter), iter_iterate_deriv', iterate]
  simp [DIter.iter]

@[simp] lemma z_iterate_deriv : (iterate_deriv c z dc dz rs n).z = (iterate c z rs n).z :=
  (Iter.ext_iff.mp iter_iterate_deriv).1
@[simp] lemma n_iterate_deriv : (iterate_deriv c z dc dz rs n).n = (iterate c z rs n).n :=
  (Iter.ext_iff.mp iter_iterate_deriv).2.1
@[simp] lemma exit_iterate_deriv : (iterate_deriv c z dc dz rs n).exit = (iterate c z rs n).exit :=
  (Iter.ext_iff.mp iter_iterate_deriv).2.2
