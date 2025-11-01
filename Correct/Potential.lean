import Correct.Iterate
import Ray.Dynamics.Multibrot.PotentialLower
import Render.Potential

/-!
## Approximate computation of the Mandelbrot potential function

See `Render.Potential` for detailed comments and implementation.
-/

open Real (log)
open Set

private local instance : Fact (2 ≤ 2) := ⟨by norm_num⟩

/-- `Interval.iter_sqrt` is conservative -/
lemma Interval.approx_iter_sqrt {a : ℝ} {x : Interval} {n : ℕ} (ax : approx x a) :
    approx (x.iter_sqrt n) (a ^ (2 ^ (-n : ℝ) : ℝ)) := by
  rw [iter_sqrt]
  by_cases a0 : a ≤ 0
  · simp only [log_nonpos a0 ax, nan_scaleB', exp_nan, approx_nan]
  · rw [Real.rpow_def_of_pos (not_le.mp a0)]
    approx

/-- `Interval.iter_sqrt` is conservative, more inferable version -/
@[approx] lemma Interval.mem_approx_iter_sqrt' {a : ℝ} {x : Interval} {n : ℕ}
    (a0 : 0 ≤ a) (ax : approx x (a ^ (2^n))) : approx (x.iter_sqrt n) a := by
  generalize hb : a^(2^n) = b at ax
  have ab : a = b ^ (2 ^ (-n : ℝ) : ℝ) := by
    have e : (2:ℝ)^n = (2^n : ℕ) := by norm_num
    rw [← hb, Real.rpow_neg (by norm_num), Real.rpow_natCast, e,
      Real.pow_rpow_inv_natCast a0 (pow_ne_zero _ (by norm_num))]
  rw [ab]
  exact approx_iter_sqrt ax

/-- `potential_small` covers all small values -/
lemma Box.approx_potential_small {c' z' : ℂ} (c4 : ‖c'‖ ≤ 4) (z4 : ‖z'‖ ≤ 4) :
    approx potential_small ((superF 2).potential c' z') := by
  rw [potential_small]
  apply approx_of_mem_Icc (a := 0.216) (c := 1)
  · exact Interval.approx_union_left (Interval.approx_ofScientific _ _ _)
  · exact Interval.approx_union_right approx_one
  · constructor
    · exact le_potential c4 z4
    · apply Super.potential_le_one

/-- `potential_large` covers all large values -/
lemma Box.approx_potential_large {c' z' : ℂ} {z : Box} (cz : ‖c'‖ ≤ ‖z'‖) (z6 : 6 ≤ ‖z'‖)
    (zm : approx z z') : approx (potential_large z) ((superF 2).potential c' z') := by
  rw [potential_large]
  apply Interval.approx_grow (potential_approx 2 (le_trans (by norm_num) z6) cz)
  · intro n
    rw [Ne, Interval.hi_eq_nan] at n
    refine le_trans (potential_error_le_of_z6 _ z6 cz) ?_
    apply Interval.le_hi n
    rw [div_eq_mul_inv, ← Real.rpow_neg (by positivity), Real.rpow_def_of_pos (by linarith)]
    have e : Real.log (‖z'‖) * -1.927 = Real.log (‖z'‖ ^ 2) * -0.9635 := by
      rw [Real.log_pow, Nat.cast_two, mul_comm (2:ℝ), mul_assoc]; norm_num
    rw [e]
    approx
  · have e : 1 / ‖z'‖ = Real.exp (-(Real.log (‖z'‖ ^ 2) / 2)) := by
      simp only [one_div, Real.log_pow, Nat.cast_ofNat]
      rw [mul_div_cancel_left₀ _ two_ne_zero, Real.exp_neg, Real.exp_log (by linarith)]
    rw [e]
    approx

/-- `Box.potential` is conservative -/
@[approx] lemma Box.mem_approx_potential {c' z' : ℂ} {c z : Box}
    (cm : approx c c') (zm : approx z z') (n : ℕ) (r : Floating) :
    approx (Box.potential c z n r).1 ((superF 2).potential c' z') := by
  set s := superF 2
  unfold Box.potential
  generalize hcs : (normSq c).hi = cs
  generalize hi : iterate c z (cs.max 9) n = i
  by_cases csn : cs = nan
  · simp only [csn, Floating.nan_max, iterate_nan, approx_nan]
  simp only [hi, Interval.hi_eq_nan, Floating.val_lt_val]
  generalize hie : i.exit = ie
  induction ie
  · generalize hzs : (normSq i.z) = zs
    by_cases bad : zs = nan ∨ (16 : Floating).val < zs.hi.val ∨ (16 : Floating).val < cs.val
    · simp only [bad, ↓reduceIte, approx_nan]
    · simp only [bad, ↓reduceIte]
      simp only [not_or, not_lt, ← hzs] at bad
      rcases bad with ⟨zsn, z4, c4⟩
      rw [Floating.val_ofNat] at c4 z4
      simp only [← hcs, Nat.cast_ofNat, Interval.hi_eq_nan] at c4 z4 csn zsn
      apply Interval.mem_approx_iter_sqrt' s.potential_nonneg
      simp only [← s.potential_eqn_iter, f_f'_iter]
      generalize hw' : (f' 2 c')^[i.n] z' = w'
      have le4 : Real.sqrt 16 ≤ 4 := by rw [Real.sqrt_le_iff]; norm_num
      apply approx_potential_small
      · exact le_trans (Box.abs_le_sqrt_normSq cm csn) (le_trans (Real.sqrt_le_sqrt c4) le4)
      · refine le_trans (Box.abs_le_sqrt_normSq ?_ zsn) (le_trans (Real.sqrt_le_sqrt z4) le4)
        rw [← hw', ←hi]
        exact mem_approx_iterate cm zm _
  · generalize hj : iterate c i.z ((r.mul r true).max (cs.max 36)) 1000 = j
    simp only
    generalize hje : j.exit = je
    induction je
    · simp only [approx_nan]
    · simp only
      generalize hn : i.n + j.n = n
      apply Interval.mem_approx_iter_sqrt' s.potential_nonneg
      simp only [← s.potential_eqn_iter, f_f'_iter, ←hj] at hje ⊢
      generalize hw' : (f' 2 c')^[n] z' = w'
      have izm : approx i.z ((f' 2 c')^[i.n] z') := by rw [← hi]; exact mem_approx_iterate cm zm _
      have jl := iterate_large cm izm hje
      have jrn := ne_nan_of_iterate (hje.trans_ne (by decide))
      simp only [hj, ← Function.iterate_add_apply, add_comm _ i.n, hn, hw'] at jl
      simp only [ne_eq, Floating.max_eq_nan, not_or] at jrn
      rw [Floating.val_max jrn.1 (Floating.max_ne_nan.mpr jrn.2),
        Floating.val_max jrn.2.1 jrn.2.2, max_lt_iff, max_lt_iff, Floating.val_ofNat] at jl
      apply approx_potential_large
      · refine le_trans ?_ (le_trans (Real.sqrt_le_sqrt jl.2.1.le) ?_)
        · simp only [← hcs, Interval.hi_eq_nan] at csn ⊢; exact abs_le_sqrt_normSq cm csn
        · simp only [norm_nonneg, Real.sqrt_sq, le_refl]
      · refine le_trans ?_ (le_trans (Real.sqrt_le_sqrt jl.2.2.le) ?_)
        · have e : (36 : ℝ) = 6 ^ 2 := by norm_num
          simp only [Nat.cast_ofNat]
          rw [e, Real.sqrt_sq (by norm_num)]
        · simp only [norm_nonneg, Real.sqrt_sq, le_refl]
      · rw [← hw', ←hn, add_comm _ j.n, Function.iterate_add_apply, ←hj]
        exact mem_approx_iterate cm izm _
    · simp only [approx_nan]
  · simp only [approx_nan]

/-- `Box.potential` is conservative, diagonal version -/
@[approx] lemma Box.mem_approx_potential' {c' : ℂ} {c : Box} (cm : approx c c') (n : ℕ)
    (r : Floating) : approx (Box.potential c c n r).1 (_root_.potential 2 c') := by
  simp only [_root_.potential, RiemannSphere.fill_coe, mem_approx_potential cm cm]

/-!
### Unit tests

The first time I ran this, it failed to compute tight intervals for interior points.  Let's try
some examples.
-/

section debug
/-
def c : Box := .ofRat (-119/256, -763/1280)
def cs := c.normSq.hi
def n := 80
def r : Floating := 1000
def i := iterate c c (cs.max 9) n
def zs' := i.z.normSq
def zs := i.z.normSq.hi
#eval i
#eval zs'
--#eval i200
--#eval i200.z.re.lo.abs.log
--#eval i200.z.re.hi.abs.log
--#eval i200.z.re.size.abs.log
--#eval i200.z.im.lo.abs.log
--#eval i200.z.im.hi.abs.log
#eval zs = nan ∨ 16 < zs ∨ 16 < cs
#eval Box.potential_small
#eval Box.potential_small.iter_sqrt i.n
#eval Box.potential_small.log
#eval Box.potential_small.log.scaleB' (-.ofNat0 n)
#eval Box.potential_small.log.lo.scaleB' (-.ofNat0 n)
#eval Box.potential_small.log.hi
#eval Box.potential_small.log.hi.scaleB' (-.ofNat0 n)
#eval Box.potential c c n r
-/
end debug

private def good (x y : ℚ) (n : ℕ) : Bool :=
  let c : Box := .ofRat (x,y)
  (Box.potential c c n 1000).1 ≠ nan
example : good 0 0 100 := by native_decide
example : good 0.1 0.2 100 := by native_decide
example : good (-21/160) (-133/160) 100 := by native_decide
example : good (-119/256) (-763/1280) 80 := by native_decide
example : good (-1393/1280) (-329/1280) 50 := by native_decide
