import Correct.Iterate
import Ray.Manifold.RiemannSphere
import Ray.Multibrot.Basic
import Ray.Multibrot.Potential
import Ray.Multibrot.PotentialLower
import Render.Potential

/-!
## Approximate computation of the Mandelbrot potential function

See `Render.Potential` for detailed comments and implementation.
-/

open Function (uncurry)
open OneDimension
open Real (log)
open Set
open scoped RiemannSphere

variable {x dx : Interval} {x' dx' : ℝ} {c z dc dz : Box} {c' z' dc' dz' : ℂ} {n : ℕ}

/-- `Interval.iter_sqrt` is conservative -/
@[approx] lemma Interval.approx_iter_sqrt (ax : approx x x') :
    approx (x.iter_sqrt n) (x' ^ (2 ^ (-n : ℝ) : ℝ)) := by
  rw [iter_sqrt]
  by_cases x0 : x' ≤ 0
  · simp only [log_nonpos x0 ax, nan_scaleB', exp_nan, approx_nan]
  · rw [Real.rpow_def_of_pos (not_le.mp x0)]
    approx

/-- `Interval.iter_sqrt` is conservative, more inferable version -/
@[approx] lemma Interval.approx_iter_sqrt' {a : ℝ} {x : Interval} {n : ℕ}
    (a0 : 0 ≤ a) (ax : approx x (a ^ (2^n))) : approx (x.iter_sqrt n) a := by
  generalize hb : a^(2^n) = b at ax
  have ab : a = b ^ (2 ^ (-n : ℝ) : ℝ) := by
    have e : (2:ℝ)^n = (2^n : ℕ) := by norm_num
    rw [← hb, Real.rpow_neg (by norm_num), Real.rpow_natCast, e,
      Real.pow_rpow_inv_natCast a0 (pow_ne_zero _ (by norm_num))]
  rw [ab]
  exact approx_iter_sqrt ax

@[approx] lemma Interval.approx_iter_sqrt_deriv_1 (ax : approx x x') :
    approx (x.iter_sqrt_deriv dx n).1 (x' ^ (2 ^ (-n : ℝ) : ℝ)) := by
  simp only [fst_iter_sqrt_deriv]
  approx

/-- `Interval.iter_sqrt_deriv` is conservative -/
lemma Interval.approx_iter_sqrt_deriv (ax : approx x x') (adx : approx dx dx') :
    approx (x.iter_sqrt_deriv dx n).2 (bottcher_deriv_pow n x' * dx') := by
  rw [iter_sqrt_deriv]
  by_cases x0 : x' ≤ 0
  · simp [log_nonpos x0 ax, nan_scaleB', exp_nan, approx_nan]
  · simp only [not_le] at x0
    generalize hs : (x.log.scaleB' (-.ofNat0 n)).exp = s
    have e : (2 : ℝ) ^ (-n : ℤ) = 2 ^ (-n : ℝ) := by simp
    have as : approx s (x' ^ (2 ^ (-n : ℝ) : ℝ)) := by
      simpa only [← hs, iter_sqrt, e] using Interval.approx_iter_sqrt ax (n := n)
    simp only [bottcher_deriv_pow, mul_rotate _ _ dx', mul_assoc, mul_div_assoc, e]
    approx

/-- `potential_small` covers all small values -/
lemma Box.approx_potential_small (c4 : ‖c'‖ ≤ 4) (z4 : ‖z'‖ ≤ 4) :
    approx potential_small ((superF 2).potential c' z') := by
  rw [potential_small]
  apply approx_of_mem_Icc (a := 0.216) (c := 1)
  · exact Interval.approx_union_left (Interval.approx_ofScientific _ _ _)
  · exact Interval.approx_union_right approx_one
  · constructor
    · exact le_potential c4 z4
    · apply Super.potential_le_one

@[approx] lemma Box.approx_norm (ax : approx z z') : approx z.normSq.sqrt ‖z'‖ := by
  rw [(by simp : ‖z'‖ = Real.sqrt (‖z'‖ ^ 2))]; approx
@[approx] lemma Box.approx_inv_norm (ax : approx z z') : approx z.normSq⁻¹.sqrt ‖z'‖⁻¹ := by
  simp only [Complex.norm_def, ← Real.sqrt_inv]; approx

/-- `potential_large` covers all large values -/
lemma Box.approx_potential_large (le : max 10 ‖c'‖ ≤ ‖z'‖)
    (zm : approx z z') : approx (potential_large z) ((superF 2).potential c' z') := by
  rw [potential_large]
  simp only [sup_le_iff] at le
  apply Interval.approx_grow (potential_approx_strong_10 2 le.1 le.2)
  · intro n
    rw [Ne, Interval.hi_eq_nan] at n
    apply Interval.le_hi n
    rw [inv_pow]
    approx
  · approx

/-- `potential_deriv_large` covers all large values -/
lemma Box.approx_potential_deriv_large (le : max 10 (√3 * ‖c'‖) ≤ ‖z'‖)
    (cm : approx c c') (zm : approx z z') (dcm : approx dc dc') (dzm : approx dz dz') :
    approx (potential_deriv_large c z dc dz).2 (_root_.potential_deriv c' z' dc' dz') := by
  set s := superF 2
  simp only [potential_deriv_large]
  refine Interval.approx_grow (fderiv_bottcher_approx le) ?_ (by approx)
  intro n
  rw [Ne, Interval.hi_eq_nan] at n
  apply Interval.le_hi n
  simp only [Interval.div_def, div_eq_mul_inv]
  approx

/-- The defining property of `Box.potential_rc` -/
lemma Box.le_potential_rc {r cs : Floating} (hcs : c.normSq.hi = cs) (cm : approx c c')
    (rn : potential_rc r cs ≠ nan) :
    max (10 ^ 2) (3 * ‖c'‖ ^ 2) ≤ (potential_rc r cs).val := by
  simp only [ne_eq, potential_rc, Floating.max_eq_nan, not_or] at rn
  rw [potential_rc, Floating.val_max rn.1 (Floating.max_ne_nan.mpr rn.2),
    Floating.val_max rn.2.1 rn.2.2, Floating.val_ofNat, le_max_iff, max_comm (Floating.val _)]
  refine .inr (max_le_max (by bound) ?_)
  have csn := (Floating.ne_nan_of_mul rn.2.1).1
  have three : Floating.val 3 = 3 := by
    rw [← Floating.coe_valq, (by norm_num : (3 : ℝ) = (3 : ℚ)), Rat.cast_inj]
    decide +kernel
  simp only [← hcs, ne_eq, Interval.hi_eq_nan, mul_comm (3 : ℝ)] at csn rn ⊢
  refine le_trans ?_ (Floating.le_mul rn.2.1)
  rw [three, mul_le_mul_iff_of_pos_right (by norm_num)]
  exact Interval.le_hi csn (by approx)

/-- Drop a `√3` -/
private lemma drop_sqrt3 {c : ℂ} : max 10 ‖c‖ ≤ max 10 (√3 * ‖c‖) :=
  max_le_max (by bound) (by bound)

/-- `Box.potential_deriv` is conservative -/
lemma Box.approx_potential_deriv (cm : approx c c') (zm : approx z z') (dcm : approx dc dc')
    (dzm : approx dz dz') (n : ℕ) (r : Floating) :
    let s := superF 2
    approx (Box.potential_deriv c z dc dz n r).p (s.potential c' z') ∧
    approx (Box.potential_deriv c z dc dz n r).dp (_root_.potential_deriv c' z' dc' dz') := by
  set s := superF 2
  unfold Box.potential_deriv
  generalize hcs : (normSq c).hi = cs
  generalize hi : iterate_deriv c z dc dz (cs.max 9) n = i
  by_cases csn : cs = nan
  · simp only [csn, Floating.nan_max, iterate_deriv_nan, approx_nan, DPotential.p_nan,
      DPotential.dp_nan, true_and]
  simp only [hi, Interval.hi_eq_nan, Floating.val_lt_val]
  generalize hie : i.exit = ie
  induction ie
  · generalize hzs : (normSq i.z) = zs
    by_cases bad : zs = nan ∨ (16 : Floating).val < zs.hi.val ∨ (16 : Floating).val < cs.val
    · simp only [bad, ↓reduceIte, approx_nan, DPotential.p_nan, DPotential.dp_nan, true_and]
    · simp only [bad, ↓reduceIte, approx_nan, and_true]
      simp only [not_or, not_lt, ← hzs] at bad
      rcases bad with ⟨zsn, z4, c4⟩
      rw [Floating.val_ofNat] at c4 z4
      simp only [← hcs, Nat.cast_ofNat, Interval.hi_eq_nan] at c4 z4 csn zsn
      apply Interval.approx_iter_sqrt' s.potential_nonneg
      simp only [← s.potential_eqn_iter, f_f'_iter]
      generalize hw' : (f' 2 c')^[i.n] z' = w'
      have le4 : Real.sqrt 16 ≤ 4 := by rw [Real.sqrt_le_iff]; norm_num
      apply approx_potential_small
      · exact le_trans (Box.abs_le_sqrt_normSq cm csn) (le_trans (Real.sqrt_le_sqrt c4) le4)
      · refine le_trans (Box.abs_le_sqrt_normSq ?_ zsn) (le_trans (Real.sqrt_le_sqrt z4) le4)
        rw [← hw', ←hi]
        exact approx_iterate_deriv_z cm zm dcm dzm _
  · generalize hj : iterate_deriv c i.z dc i.dz (potential_rc r cs) 1000 = j
    simp only
    generalize hje : j.exit = je
    induction je
    · simp only [approx_nan, DPotential.p_nan, DPotential.dp_nan, true_and]
    · simp only
      generalize hn : i.n + j.n = n
      generalize hpj : j.z.potential_deriv_large j.dz = pj
      have izm : approx i.z ((f' 2 c')^[i.n] z') := hi ▸ approx_iterate_deriv_z cm zm dcm dzm _
      have idzm := hi ▸ approx_iterate_deriv_dz cm zm dcm dzm _
      have jzm : approx j.z ((f' 2 c')^[n] z') := by
        rw [← hn, add_comm i.n, Function.iterate_add_apply, ← hj]
        approx
      have jdzm : approx j.dz ((fderiv ℂ (fun p ↦ (f' 2 p.1)^[n] p.2) (c', z')) (dc', dz')) := by
        rw [← hn, add_comm i.n, fderiv_iterate_add, ← hj]
        approx
      simp only at idzm
      have le_z : max 10 (√3 * ‖c'‖) ≤ ‖(f' 2 c')^[n] z'‖ := by
        rw [max_le_iff, ← sq_le_sq₀ (a := (10 : ℝ)) (by bound) (by bound),
          ← sq_le_sq₀ (a := (√3 * ‖c'‖ : ℝ)) (by bound) (by bound), ← max_le_iff, mul_pow,
          Real.sq_sqrt (by bound)]
        have jl := hj ▸ iterate_deriv_large cm izm dcm idzm (hj ▸ hje)
        simp only [← Function.iterate_add_apply, add_comm, hn] at jl
        exact le_trans (le_potential_rc hcs cm (ne_nan_of_iterate_deriv
          ((hj ▸ hje).trans_ne (by decide)))) jl.le
      have le_z' := le_trans drop_sqrt3 le_z
      constructor
      · simp only [Interval.fst_iter_sqrt_deriv]
        apply Interval.approx_iter_sqrt' s.potential_nonneg
        simp only [fst_potential_deriv_large, ← s.potential_eqn_iter, f_f'_iter]
        exact approx_potential_large le_z' jzm
      · rw [potential_deriv_eqn (n := n)]
        · apply Interval.approx_iter_sqrt_deriv
          · simp only [fst_potential_deriv_large, ← s.potential_eqn_iter, f_f'_iter]
            exact approx_potential_large le_z' jzm
          · exact approx_potential_deriv_large le_z cm jzm dcm jdzm
        · rw [s.basin_iff_attracts, ← attracts_shift (k := n), ← s.basin_iff_attracts,
            f_f'_iter]
          simp only [max_le_iff] at le_z'
          exact julia_two_lt (by linarith) (by linarith)
    · simp only [approx_nan, DPotential.p_nan, DPotential.dp_nan, true_and]
  · simp only [approx_nan, DPotential.p_nan, DPotential.dp_nan, true_and]

/-- `Box.potential` is conservative -/
@[approx] lemma Box.approx_potential (cm : approx c c') (zm : approx z z') (n : ℕ)
    (r : Floating) : approx (Box.potential c z n r).p ((superF 2).potential c' z') := by
  simpa using (approx_potential_deriv cm zm approx_zero approx_zero n r).1

/-- `Box.potential_deriv` is conservative for potential -/
@[approx] lemma Box.approx_potential_deriv_p (cm : approx c c') (zm : approx z z') (n : ℕ)
    (r : Floating) : approx (Box.potential_deriv c z dc dz n r).p ((superF 2).potential c' z') := by
  simpa using (approx_potential_deriv cm zm approx_zero approx_zero n r).1

/-- `Box.potential_deriv` is conservative for potential derivatives -/
@[approx] lemma Box.approx_potential_deriv_dp (cm : approx c c') (zm : approx z z')
    (dcm : approx dc dc') (dzm : approx dz dz') (n : ℕ) (r : Floating) :
    approx (Box.potential_deriv c z dc dz n r).dp (_root_.potential_deriv c' z' dc' dz') := by
  simpa using (approx_potential_deriv cm zm dcm dzm n r).2

/-- `Box.potential` is conservative, diagonal version -/
@[approx] lemma Box.approx_potential' (cm : approx c c') (n : ℕ) (r : Floating) :
    approx (Box.potential c c n r).p (_root_.potential 2 c') := by
  simp only [_root_.potential, RiemannSphere.fill_coe]
  approx

/-- `Box.potential_deriv` is conservative, diagonal version -/
@[approx] lemma Box.approx_potential_deriv_p' (cm : approx c c') (n : ℕ) (r : Floating) :
    approx (Box.potential_deriv c c dc dc n r).p (_root_.potential 2 c') := by
  simp only [_root_.potential, RiemannSphere.fill_coe]
  approx

/-- `Box.potential_deriv` is conservative for derivatives, diagonal version -/
@[approx] lemma Box.approx_potential_deriv_dp' (cm : approx c c') (dcm : approx dc dc') (n : ℕ)
    (r : Floating) :
    approx (Box.potential_deriv c c dc dc n r).dp (_root_.potential_deriv c' c' dc' dc') := by
  approx
