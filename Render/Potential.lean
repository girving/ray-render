import Interval.Interval.Division
import Interval.Interval.Exp
import Interval.Interval.Log
import Interval.Interval.Sqrt
import Render.Iterate

/-!
## Approximate computation of the Mandelbrot potential function

Fix `c`, and let `p z = potential 2 c z` be the potential function for the `c`-Julia set.  Say we
iterate `n` times to get `w = f^[n] z`.  There are two cases

#### Case 1: `‖w‖ ≤ 4`

By `le_potential`, we have

  `0.216 ≤ p w`
  `0.216 ^ (2^n)⁻¹ ≤ p z`.

Not very many iterations will give us a lower bound very close to `1`.

#### Case 2: `4 ≤ ‖w‖`

Increasing `n` by 1 if necessary, we have `6 ≤ ‖w‖`.  By `potential_approx` and
`potential_error_le_of_z6`, we have

  `|p w - 1/‖w‖| ≤ 0.8095 / ‖w‖ ^ 1.927`

Here is an `‖w‖ : 1/‖w‖, RHS` table for various `‖w‖` values:

  `w    6: 1/w 0.16667, error 2.563e-2, ratio 0.153`
  `w   32: 1/w 0.03125, error 1.018e-3, ratio 0.032`
  `w 1020: 1/w 0.00098, error 1.290e-6, ratio 0.001`

We then finish with

  `p z = p w ^ (2^n)⁻¹`

See `Correct.Potential` for correctness proofs.
-/

open Real (log)
open Set

/-!
### Potential approximation routines
-/

/-- Repeated square roots: `x ^ (2 ^ -n)` -/
@[irreducible] def Interval.iter_sqrt (x : Interval) (n : ℕ) : Interval :=
  exp ((log x).scaleB' (-.ofNat0 n))

/-- Repeated square roots and their derivatives -/
@[irreducible] def Interval.iter_sqrt_deriv (x dx : Interval) (n : ℕ) : Interval × Interval :=
  -- `s = x ^ (2 ^ -n) = exp (log x >>> n)`
  -- `df = 2 ^ -n * x ^ (2 ^ -n - 1) * dx = s / x * dx >>> n`
  let nn : Fixed 0 := -.ofNat0 n
  let s := exp ((log x).scaleB' nn)
  (s, s / x * dx.scaleB' nn)

/-- Approximate the potential of a large `z`.
    The estimate is independent of `c`, but is only valid if `max 10 ‖c‖ ≤ ‖z‖`. -/
@[irreducible] def Box.potential_large (z : Box) : Interval :=
  let z2 := z.normSq
  -- We have `|p' j.z + z2⁻¹| ≤ 2.45 / z2 ^ 1.5`
  let i := z2⁻¹
  let r := i.sqrt
  r.grow (0.849 * i).hi

/-- Approximate the potential of a large `z`, and the derivative.
    The estimate is only valid if `max 10 (√3 * ‖c‖) ≤ ‖z‖`. -/
@[irreducible] def Box.potential_deriv_large (c z dc dz : Box) : Interval × Interval :=
  let c2 := c.normSq
  let z2 := z.normSq
  let dcn := dc.normSq.sqrt
  let dzn := dz.normSq.sqrt
  -- We have `|p' j.z + z2⁻¹| ≤ 2.45 / z2 ^ 1.5`
  let i := z2⁻¹
  let r := i.sqrt
  (r.grow (0.849 * i).hi, (i * dzn).grow (r * (0.943 / (z2 - c2) * dcn + 2.45 * i * dzn)).hi)

/-- Approximate the potential of a small `z` (valid for `‖c‖, ‖z‖ ≤ 4`) -/
@[irreducible] def Box.potential_small : Interval :=
  0.216 ∪ 1

/-- Which potential estimate we used -/
inductive PotentialMode : Type
  | nan
  | large
  | small

@[ext] structure Potential where
  p : Interval
  m : PotentialMode

structure DPotential where
  p : Interval
  dp : Interval
  m : PotentialMode

instance : Nan Potential := ⟨nan, .nan⟩
instance : Nan DPotential := ⟨nan, nan, .nan⟩
def DPotential.potential (p : DPotential) : Potential := ⟨p.p, p.m⟩

@[simp] lemma Potential.p_nan : (nan : Potential).p = nan := rfl
@[simp] lemma Potential.m_nan : (nan : Potential).m = .nan := rfl
@[simp] lemma DPotential.p_nan : (nan : DPotential).p = nan := rfl
@[simp] lemma DPotential.dp_nan : (nan : DPotential).dp = nan := rfl
@[simp] lemma DPotential.m_nan : (nan : DPotential).m = .nan := rfl

/-- Below need `4 ≤ ‖c‖√3 ≤ ‖z‖`, but use `10` to get slightly tighter bounds -/
@[irreducible] def Box.potential_rc (r cs : Floating) : Floating :=
  (r.mul r true).max ((cs.mul 3 true).max 100)

/-- Approximate the Mandelbrot potential function at any point.
    We also return the exit mode from our iteration. -/
@[irreducible] def Box.potential (c z : Box) (n : ℕ) (r : Floating) : Potential :=
  let cs := c.normSq.hi
  let i := iterate c z (cs.max 9) n
  match i.exit with
  | .nan => nan
  | .large =>
    -- We're outside radius `3` after `i.n` iterations.  Iterate a bit more to make `z` very large,
    -- then use our large `z` potential bound.  This should always work, so we use a large count.
    let j := iterate c i.z (potential_rc r cs) 1000
    match j.exit with
    | .large => ⟨(potential_large j.z).iter_sqrt (i.n + j.n), .large⟩
    | _ => nan  -- If we fail to leave the large radius, give up
  | .count =>
    -- We don't know we're `≤ 3`. Use the small bound if we're `≤ 4`, otherwise bail.
    let zs := i.z.normSq.hi
    if zs = nan ∨ 16 < zs ∨ 16 < cs then nan else
    ⟨potential_small.iter_sqrt i.n, .small⟩

/-- Approximate the Mandelbrot potential function and its derivative at any point.
    We also return the exit mode from our iteration. -/
@[irreducible] def Box.potential_deriv (c z dc dz : Box) (n : ℕ) (r : Floating) : DPotential :=
  let cs := c.normSq.hi
  let i := iterate_deriv c z dc dz (cs.max 9) n
  match i.exit with
  | .nan => nan
  | .large =>
    -- We're outside radius `3` after `i.n` iterations.  Iterate a bit more to make `z` very large,
    -- then use our large `z` potential bound.  This should always work, so we use a large count.
    let j := iterate_deriv c i.z dc i.dz (potential_rc r cs) 1000
    match j.exit with
    | .large =>
      let (p, dp) := potential_deriv_large c j.z dc j.dz
      let (p, dp) := p.iter_sqrt_deriv dp (i.n + j.n)
      ⟨p, dp, .large⟩
    | _ => nan  -- If we fail to leave the large radius, give up
  | _ =>
    -- We don't know we're `≤ 3`. Use the small bound if we're `≤ 4`, otherwise bail.
    -- Unfortunately, we have no way to approximate derivatives.
    let zs := i.z.normSq.hi
    if zs = nan ∨ 16 < zs ∨ 16 < cs then nan else
    ⟨potential_small.iter_sqrt i.n, nan, .small⟩

/-!
### Commutative diagrams

Computing with derivatives and then dropping them is the same as computing without derivatives.
-/

variable {x dx : Interval} {c z dc dz : Box} {n : ℕ} {r : Floating}

@[simp] lemma Interval.fst_iter_sqrt_deriv :
    (x.iter_sqrt_deriv dx n).1 = x.iter_sqrt n := by simp only [iter_sqrt_deriv, iter_sqrt]

@[simp] lemma Box.fst_potential_deriv_large :
    (potential_deriv_large c z dc dz).1 = potential_large z := by
  simp only [potential_deriv_large, potential_large]

@[simp] lemma Box.potential_potential_deriv :
    (potential_deriv c z dc dz n r).potential = potential c z n r := by
  simp only [potential_deriv, exit_iterate_deriv, z_iterate_deriv, fst_potential_deriv_large,
    n_iterate_deriv, Interval.fst_iter_sqrt_deriv, Interval.hi_eq_nan, Floating.val_lt_val,
    potential]
  generalize iterate c z (c.normSq.hi.max 9) n = i
  generalize potential_rc r (c.normSq.hi) = rc
  generalize iterate c i.z rc 1000 = j
  cases i.exit <;> cases j.exit <;> simp [Potential.ext_iff, DPotential.potential,
    apply_ite (f := DPotential.p), apply_ite (f := Potential.p),
    apply_ite (f := DPotential.m), apply_ite (f := Potential.m)]

@[simp] lemma Box.p_potential_deriv : (potential_deriv c z dc dz n r).p = (potential c z n r).p :=
  (Potential.ext_iff.mp potential_potential_deriv).1

@[simp] lemma Box.m_potential_deriv : (potential_deriv c z dc dz n r).m = (potential c z n r).m :=
  (Potential.ext_iff.mp potential_potential_deriv).2
