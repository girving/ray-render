import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Int.Bitwise
import Ray.Misc.Bound

/-!
## Integer machinery for fixpoint arithmetic
-/

@[simp] lemma Int.shiftLeft_one (n : ℤ) : n <<< 1 = 2 * n := by
  have e : (1 : ℤ) = (1 : ℕ) := rfl
  rw [e, Int.shiftLeft_eq_mul_pow]
  ring

/-- Shift right, rounding to nearest -/
def Int.shiftRightNear (n : ℤ) (k : ℕ) : ℤ :=
  (n + ((1 : ℤ) <<< k >>> (1 : ℕ))) >>> k

/-- Shifting right by zero is the identity -/
@[simp] lemma Int.shiftRightNear_zero (n : ℤ) : n.shiftRightNear 0 = n := by
  simp [shiftRightNear]
  rfl

/-- `shiftRightNear` is within a half -/
@[bound] lemma Int.shiftRightNear_error (n : ℤ) (k : ℕ) :
    |n.shiftRightNear k - (n : ℝ) / 2 ^ k| ≤ 2⁻¹ := by
  by_cases k0 : k = 0
  · simp [k0]
  generalize ha : (2 : ℤ) ^ (k - 1) = a
  have ha' : 2 ^ k = 2 * a := by rw [← ha, ← pow_succ']; lia
  have a0 : 0 < a := by rw [← ha]; positivity
  have a0' : 2 * a ≠ 0 := by simp [← ha]
  have k2 : (2 : ℝ) ^ k = 2 * a := by simp [← ha, ← pow_succ']; lia
  rw [← mul_le_mul_iff_of_pos_right (a := 2 ^ k) (by bound)]
  simp only [shiftRightNear, shiftLeft_eq, one_mul, shiftRight_eq_div_pow, pow_one, Nat.cast_ofNat,
    k2, ← mul_assoc (2 : ℝ)⁻¹]
  have xp : ∀ x : ℝ, |x| * (2 * a) = |x * (2 * a)| := by
    intro; simp [abs_of_pos (Int.cast_pos.mpr a0)]
  rw [inv_mul_cancel₀ (by norm_num), xp, sub_mul, mul_comm_div, div_self (by positivity), abs_le]
  norm_cast
  have e := Int.emod_add_mul_ediv (n + a) (2 * a)
  have m0 := Int.emod_nonneg (n + a) a0'
  have m1 := Int.emod_lt (n + a) a0'
  lia

/-- `shiftRightNear` is within a half -/
@[bound] lemma Int.shiftRightNear_sq_error (n : ℤ) (k : ℕ) :
    (n.shiftRightNear k - (n : ℝ) / 2 ^ k) ^ 2 ≤ 4⁻¹ := by
  rw [← sq_abs, (by norm_num : (4⁻¹ : ℝ) = 2⁻¹ ^ 2), sq_le_sq₀ (by bound) (by bound)]
  apply Int.shiftRightNear_error

/-- Error if we shift a complex number -/
@[bound] lemma Complex.shiftRightNear_error (x y : ℤ) (k : ℕ) :
    ‖(⟨x.shiftRightNear k, y.shiftRightNear k⟩ : ℂ) - ⟨x, y⟩ / 2 ^ k‖ ≤ (√2)⁻¹ := by
  have e : (⟨x, y⟩ : ℂ) / 2 ^ k = ⟨x / 2 ^ k, y / 2 ^ k⟩ := by simp [Complex.mk_eq_add_mul_I]; ring
  rw [Complex.norm_eq_sqrt_sq_add_sq, ← Real.sqrt_inv,
    Real.sqrt_le_sqrt_iff (by bound), e]
  simp only [sub_re, sub_im]
  exact le_trans (b := 4⁻¹ + 4⁻¹) (by bound) (by norm_num)
