import Interval.Approx.Approx
import Mathlib.Analysis.Complex.Basic
import Render.Int

/-!
## `ℕ`-based fixpoint complex arithmetic for Mandelbrot iteration purposes

These classes are very hard to use, but are designed to compile down to plain fixed-precision
integer arithmetic that tracks error bounds entirely implicitly.

We use a lot of dependent typing so that lemmas are clean. In particular, `Disc` includes the
radius bound, so we need to prove radius bounds for results as we define operations.

We perform fixpoint operations in two phases:

1. Lossless expansion operations, which are exact on `val` but increase required precision.
2. Lossy rounding operations (`lower`), we decrease precision and slightly increase error.
-/

open Metric (ball)

/-!
### Type definitions
-/

/-- An approximate complex number near `⟨re,im⟩ / 2 ^ s`, with magnitude `≤ r` and error `≤ e` -/
structure Disc (s : ℕ) (r e : ℝ) where
  re : ℤ
  im : ℤ
  r0 : 0 ≤ r
  e0 : 0 ≤ e
  normSq_le' : re ^ 2 + im ^ 2 ≤ r ^ 2 * 2 ^ (2 * s)
  deriving Repr

/-- Squared norm approximation from a disc -/
structure NormSq (s : ℕ) (r e : ℝ) where
  a : ℕ
  r0 : 0 ≤ r
  e0 : 0 ≤ e
  sq_le' : a ≤ r * 2 ^ s
  deriving Repr

variable {s : ℕ} {r e r0 e0 r1 e1 q' : ℝ} {z' w' z0' z1' : ℂ}

attribute [bound_forward] Disc.r0 Disc.e0

/-!
### Basic properties and operation definitions
-/

/-- The center of our approximating box -/
noncomputable def Disc.val (z : Disc s r e) : ℂ := ⟨z.re, z.im⟩ / 2 ^ s

/-- The central squared norm estimate -/
noncomputable def NormSq.val (q : NormSq s r e) : ℝ := q.a / 2 ^ s

/-- `normSq_le'` in terms of scaled, unsquared norm -/
lemma Disc.normSq_le'_iff_norm_le' {x y : ℤ} (r0 : 0 ≤ r := by bound) :
    x ^ 2 + y ^ 2 ≤ r ^ 2 * 2 ^ (2 * s) ↔ ‖(⟨x, y⟩ : ℂ)‖ ≤ r * 2 ^ s := by
  rw [mul_comm (2 : ℕ), pow_mul (2 : ℝ), ← mul_pow, ← Complex.normSq_add_mul_I, ← Complex.sq_norm,
      sq_le_sq₀ (by bound) (by bound), Complex.mk_eq_add_mul_I]

/-- Scaled norm bound in terms of unscaled norm bound -/
lemma Disc.norm_le'_iff_norm_le {x y : ℤ} :
    ‖(⟨x, y⟩ : ℂ)‖ ≤ r * 2 ^ s ↔ ‖(⟨x, y⟩ : ℂ) / 2 ^ s‖ ≤ r := by
  simp [div_le_iff₀]

/-- Scaled norm bound -/
@[bound] lemma Disc.norm_le' (z : Disc s r e  ): ‖(⟨z.re, z.im⟩ : ℂ)‖ ≤ r * 2 ^ s :=
  (normSq_le'_iff_norm_le' z.r0).mp z.normSq_le'

/-- Unscaled norm bound -/
@[bound] lemma Disc.norm_le (z : Disc s r e) : ‖z.val‖ ≤ r :=
  norm_le'_iff_norm_le.mp z.norm_le'

instance Disc.instApprox : Approx (Disc s r e) ℂ where
  approx z z' := ‖z.val - z'‖ ≤ e

instance NormSq.instApprox : Approx (NormSq s r e) ℝ where
  approx q q' := ‖q.val - q'‖ ≤ e

lemma Disc.approx_def {z : Disc s r e} : approx z z' ↔ ‖z.val - z'‖ ≤ e := by rfl
lemma NormSq.approx_def {q : NormSq s r e} : approx q q' ↔ ‖q.val - q'‖ ≤ e := by rfl

/-- Lossless squaring, with tight result bounds -/
def Disc.sqr (z : Disc s r e) : Disc (2 * s) (r ^ 2) (2 * r * e + e ^ 2) :=
  -- GPT-5.2 discussion: https://chatgpt.com/share/69534512-5f60-8009-a8e1-7bbb878df438
  let r2 := z.re * z.re
  let i2 := z.im * z.im
  let c := z.re * z.im
  { re := r2 - i2
    im := c <<< 1
    r0 := by bound
    e0 := by bound
    normSq_le' := by
      have e : (r2 * i2 : ℝ) = c ^ 2 := by simp [r2, i2, c]; ring
      refine le_trans (b := ((r2 + i2) ^ 2 : ℝ)) (le_of_eq ?_) ?_
      · simp [mul_pow, ← e]
        ring_nf
      · rw [mul_comm 2, pow_mul, ← mul_pow]
        simp only [r2, i2, ← pow_two, Int.cast_pow]
        bound [z.normSq_le'] }

/-- Lossless squaring, with tight result bounds -/
def Disc.normSq (z : Disc s r e) : NormSq (2 * s) (r ^ 2) (2 * r * e + e ^ 2) where
  a := (z.re * z.re + z.im * z.im).toNat
  r0 := by bound
  e0 := by bound
  sq_le' := by
    refine le_trans ?_ z.normSq_le'
    norm_cast
    rw [← pow_two, ← pow_two, ← Int.eq_natCast_toNat.mpr (by bound)]

/-- CSE'ed `sqr` and `normSq`, together -/
def Disc.sqr_and_normSq (z : Disc s r e) :
    Disc (2 * s) (r ^ 2) (2 * r * e + e ^ 2) × NormSq (2 * s) (r ^ 2) (2 * r * e + e ^ 2) :=
  let r2 := z.re * z.re
  let i2 := z.im * z.im
  let c := z.re * z.im
  (⟨r2 - i2, c <<< 1, z.sqr.r0, z.sqr.e0, z.sqr.normSq_le'⟩,
   ⟨(r2 + i2).toNat, z.normSq.r0, z.normSq.e0, z.normSq.sq_le'⟩)

/-- Lossless addition, with tight result bounds -/
def Disc.add (z0 : Disc s r0 e0) (z1 : Disc s r1 e1) : Disc s (r0 + r1) (e0 + e1) where
  re := z0.re + z1.re
  im := z0.im + z1.im
  r0 := by bound
  e0 := by bound
  normSq_le' := by
    rw [normSq_le'_iff_norm_le', add_mul]
    refine le_trans (le_trans (le_of_eq ?_) (norm_add_le _ _)) (add_le_add z0.norm_le' z1.norm_le')
    simp [Complex.mk_eq_add_mul_I]
    ring_nf

/-- `HAdd` instance to access `add` -/
instance Disc.instHAdd : HAdd (Disc s r0 e0) (Disc s r1 e1) (Disc s (r0 + r1) (e0 + e1)) where
  hAdd z0 z1 := add z0 z1

lemma Disc.add_def {z0 : Disc s r0 e0} {z1 : Disc s r1 e1} : z0 + z1 = add z0 z1 := rfl

/-- Lower precision to `t` bits, rounding to nearest -/
def Disc.lower (z : Disc s r e) (t : ℕ) (ts : t ≤ s) :
    Disc t (r + (√2)⁻¹ / 2 ^ t) (e + (√2)⁻¹ / 2 ^ t) :=
  let d := s - t
  { re := z.re.shiftRightNear d
    im := z.im.shiftRightNear d
    r0 := by bound
    e0 := by bound
    normSq_le' := by
      rw [normSq_le'_iff_norm_le', add_mul, div_mul_cancel₀ _ (by positivity)]
      trans ‖(⟨z.re, z.im⟩ : ℂ) / 2 ^ d +
        (⟨z.re.shiftRightNear d, z.im.shiftRightNear d⟩ - ⟨z.re, z.im⟩ / 2 ^ d)‖
      · simp [Complex.mk_eq_add_mul_I]
      · refine le_trans (norm_add_le _ _) ?_
        simp only [Complex.norm_div, norm_pow, Complex.norm_ofNat]
        grw [z.norm_le']
        have st : s - d = t := by omega
        rw [mul_div_assoc, div_eq_mul_inv (_ ^ _) (_ ^ _), ← pow_sub₀ _ (by norm_num) (by omega)]
        bound }

/-!
### Our arithmetic operations are conservative
-/

/-- Addition has exact center -/
@[simp] lemma Disc.val_add {z0 : Disc s r0 e0} {z1 : Disc s r1 e1} :
    (z0 + z1).val = z0.val + z1.val := by
  simp [val, add_def, Complex.mk_eq_add_mul_I, add]
  ring

/--- Addition is conservative -/
@[approx] lemma Disc.approx_add {z0 : Disc s r0 e0} {z1 : Disc s r1 e1} {z0' : ℂ} {z1' : ℂ}
    (a0 : approx z0 z0') (a1 : approx z1 z1') : approx (z0 + z1) (z0' + z1') := by
  simp only [approx_def, val_add] at a0 a1 ⊢
  refine le_trans (le_trans (le_of_eq ?_) (norm_add_le _ _)) (add_le_add a0 a1)
  ring_nf

/--- Squaring has exact center -/
@[simp] lemma Disc.val_sqr (z : Disc s r e) : z.sqr.val = z.val ^ 2 := by
  simp [val, Complex.mk_eq_add_mul_I, sqr, div_pow, ← pow_mul]
  ring_nf
  simp only [Complex.I_sq]
  ring

/-- The analytic reason `sqr` is conservative -/
lemma Disc.norm_sq_sub_sq (z w : ℂ) : ‖z ^ 2 - w ^ 2‖ ≤ ‖z - w‖ * (‖z‖ + ‖w‖) := by
  simp only [sq_sub_sq, Complex.norm_mul, mul_comm ‖z + w‖]
  bound

/--- Squaring is conservative -/
@[approx] lemma Disc.approx_sqr {z : Disc s r e} (a : approx z z') : approx z.sqr (z' ^ 2) := by
  simp only [approx_def, val_sqr] at a ⊢
  refine le_trans (norm_sq_sub_sq _ _) ?_
  have zn : ‖z'‖ ≤ r + e := by
    calc ‖z'‖
      _ = ‖z.val - (z.val - z')‖ := by ring_nf
      _ ≤ ‖z.val‖ + ‖z.val - z'‖ := by bound
      _ ≤ _ := by bound
  exact le_trans (b := e * (r + (r + e))) (by bound) (le_of_eq (by ring))

/-- Squared norm has exact center -/
@[simp] lemma Disc.val_normSq (z : Disc s r e) : z.normSq.val = ‖z.val‖ ^ 2 := by
  simp only [NormSq.val, normSq, ← pow_two, val, Complex.norm_div, norm_pow, Complex.norm_ofNat,
    div_pow, Complex.sq_norm, Complex.normSq_mk, ← pow_mul, mul_comm s, ne_eq, pow_eq_zero_iff',
    OfNat.ofNat_ne_zero, mul_eq_zero, false_or, false_and, not_false_eq_true, div_left_inj']
  norm_cast
  rw [← Int.eq_natCast_toNat.mpr (by bound)]

/-- Squared norm is conservative -/
@[approx] lemma Disc.approx_normSq {z : Disc s r e} (a : approx z z') :
    approx z.normSq (‖z'‖ ^ 2) := by
  simp only [approx_def, NormSq.approx_def, val_normSq, sq_sub_sq, norm_mul,
    Real.norm_eq_abs] at a ⊢
  calc |‖z.val‖ + ‖z'‖| * |‖z.val‖ - ‖z'‖|
    _ = (‖z.val‖ + ‖z.val - (z.val - z')‖) * |‖z.val‖ - ‖z'‖| := by
      rw [abs_of_nonneg (by bound)]; ring_nf
    _ ≤ (r + (‖z.val‖ + ‖z.val - z'‖)) * ‖z.val - z'‖ := by bound
    _ ≤ (r + (r + e)) * e := by bound
    _ = 2 * r * e + e ^ 2 := by ring

-- `sqr_and_normSq` inherits the properties of `sqr` and `normSq`
@[simp] lemma Disc.fst_sqr_and_normSq (z : Disc s r e) : z.sqr_and_normSq.1 = z.sqr := rfl
@[simp] lemma Disc.snd_sqr_and_normSq (z : Disc s r e) : z.sqr_and_normSq.2 = z.normSq := rfl
@[approx] lemma Disc.approx_fst_sqr_and_normSq {z : Disc s r e} (a : approx z z') :
    approx z.sqr_and_normSq.1 (z' ^ 2) := by
  rw [fst_sqr_and_normSq]
  approx
@[approx] lemma Disc.approx_snd_sqr_and_normSq {z : Disc s r e} (a : approx z z') :
    approx z.sqr_and_normSq.2 (‖z'‖ ^ 2) := by
  rw [snd_sqr_and_normSq]
  approx

/-- Precision loss is conservative -/
@[approx] lemma Disc.approx_lower {z : Disc s r e} (a : approx z z') {t : ℕ} (ts : t ≤ s) :
    approx (z.lower t ts) z' := by
  have de : ∀ z : ℂ, z / 2 ^ t - z' = (z - z' * 2 ^ t) / 2 ^ t := by simp [sub_div]
  simp only [approx_def, val, lower, de, Complex.norm_div, norm_pow, Complex.norm_ofNat,
    Nat.ofNat_pos, pow_pos, div_le_iff₀, add_mul, isUnit_iff_ne_zero, ne_eq, pow_eq_zero_iff',
    OfNat.ofNat_ne_zero, false_and, not_false_eq_true, IsUnit.div_mul_cancel] at a ⊢
  trans ‖(z.val - z') * 2 ^ t +
    ((⟨z.re.shiftRightNear (s - t), z.im.shiftRightNear (s - t)⟩ : ℂ) - z.val * 2 ^ t)‖
  · simp [Complex.mk_eq_add_mul_I]
    exact le_of_eq (by ring_nf)
  · refine le_trans (norm_add_le _ _) ?_
    simp only [val, Complex.norm_mul, norm_pow, Complex.norm_ofNat, div_mul,
      div_eq_mul_inv (_ ^ _) (_ ^ _), ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      ← pow_sub₀ _ _ ts]
    bound
