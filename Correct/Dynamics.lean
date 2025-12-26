import Correct.Calculus
import Ray.Dynamics.BottcherNearM
import Ray.Dynamics.Postcritical
import Ray.Multibrot.Basic
import Ray.Multibrot.BottcherDeriv

/-!
## Extra holomorphic dynamics facts
-/

open Classical
open Filter (atTop)
open Function (uncurry)
open OneDimension
open Set
open scoped Real RiemannSphere Topology

variable {c z dc dz : ℂ} {n : ℕ}

lemma fderiv_iterate_add (a b : ℕ) :
    (fderiv ℂ (fun p ↦ (f' 2 p.1)^[a + b] p.2) (c, z) (dc, dz)) =
      fderiv ℂ (fun p ↦ (f' 2 p.1)^[a] p.2) (c, (f' 2 c)^[b] z) (dc,
        (fderiv ℂ (fun p ↦ (f' 2 p.1)^[b] p.2) (c, z) (dc, dz))) := by
  have e : (fun p : ℂ × ℂ ↦ (f' 2 p.1)^[a + b] p.2) =
      (fun p : ℂ × ℂ ↦ (f' 2 p.1)^[a] p.2) ∘ (fun p : ℂ × ℂ ↦ (p.1, (f' 2 p.1)^[b] p.2)) := by
    funext p
    induction' a with a h
    · simp
    · simp_all only [Function.iterate_add, Function.comp_apply]
  rw [e, fderiv_comp, DifferentiableAt.fderiv_prodMk]
  · simp [fderiv_fst]
  all_goals try unfold f'
  all_goals exact Differentiable.differentiableAt (by fun_prop)

lemma fderiv_iterate_succ (n : ℕ) :
    fderiv ℂ (fun p : ℂ × ℂ ↦ (f' 2 p.1)^[n + 1] p.2) (c, z) (dc, dz) =
    fderiv ℂ (fun p : ℂ × ℂ ↦ (f' 2 p.1)^[n] p.2) (c, f' 2 c z)
    (dc, fderiv ℂ (uncurry (f' 2)) (c, z) (dc, dz)) := by
  simpa only [Function.iterate_one] using fderiv_iterate_add n 1

@[simp] lemma fderiv_f' : fderiv ℂ (uncurry (f' 2)) (c, z) (dc, dz) = 2 * z * dz + dc := by
  simp only [Function.uncurry_def, f']
  rw [fderiv_fun_add, fderiv_fun_pow]
  · simp [fderiv_fst, fderiv_snd]
  all_goals fun_prop

lemma differentiableAt_bottcher (m : (c, ↑z) ∈ (superF 2).post):
    DifferentiableAt ℂ (fun p : ℂ × ℂ ↦ (superF 2).bottcher p.1 ↑p.2) (c, z) := by
  set s := superF 2
  refine (ContMDiffAt.analyticAt (I := II) (J := I) ?_).differentiableAt
  have e : (fun p : ℂ × ℂ ↦ s.bottcher p.1 ↑p.2) =
      uncurry s.bottcher ∘ (fun p : ℂ × ℂ ↦ (p.1, (p.2 : 𝕊))) := by
    rfl
  rw [e]
  refine (s.bottcher_mAnalyticOn _ (by exact m)).comp _ ?_
  exact contMDiffAt_fst.prodMk (RiemannSphere.mAnalytic_coe.contMDiffAt.comp _ contMDiffAt_snd)

/-- Tweaked inverse power for `bottcher` pullbacks -/
noncomputable def bottcher_pow (c z : ℂ) (n : ℕ) (w : ℂ) : ℂ :=
  let s := superF 2
  s.bottcher c z * (w / s.bottcher c z ^ 2 ^ n) ^ (2 ^ (-n : ℂ) : ℂ)

/-- Derivative norm for `bottcher_pow` -/
noncomputable def bottcher_deriv_pow (n : ℕ) (x : ℝ) : ℝ :=
  2 ^ (-n : ℤ) * x ^ (2 ^ (-n : ℤ) : ℝ) / x

@[bound] lemma bottcher_deriv_pow_nonneg {x : ℝ} (x0 : 0 ≤ x) : 0 ≤ bottcher_deriv_pow n x := by
  simp only [bottcher_deriv_pow]
  bound

/-- `bottcher_deriv_pow` is the derivative norm for `bottcher_pow` -/
lemma norm_deriv_bottcher_eq :
    let s := superF 2
    ‖deriv (bottcher_pow c z n) (s.bottcher c z ^ 2 ^ n)‖ =
      bottcher_deriv_pow n (s.potential c z ^ 2 ^ n) := by
  set s := superF 2
  unfold bottcher_pow
  simp only
  rw [deriv_const_mul, norm_mul, deriv_cpow_const, deriv_div_const, deriv_id'']
  · have e0 : (-n : ℂ) = (-n : ℝ) := by simp
    have e1 : (2 ^ n : ℝ) = (2 ^ n : ℕ) := by simp
    simp only [s.norm_bottcher, ne_eq, Nat.pow_eq_zero, OfNat.ofNat_ne_zero, false_and, e0,
      not_false_eq_true, pow_eq_zero_iff, sbottcher_coe_ne_zero, div_self, Complex.one_cpow,
      mul_one, one_div, norm_pow, bottcher_deriv_pow, zpow_neg, zpow_natCast,
      Complex.norm_cpow_real, Complex.norm_ofNat, Real.rpow_neg_natCast, zpow_neg, zpow_natCast,
      ← div_eq_mul_inv, e1, ← Real.rpow_natCast, norm_div, ← Real.rpow_mul s.potential_nonneg]
    simp only [Nat.cast_pow, Nat.cast_ofNat, ne_eq, pow_eq_zero_iff', OfNat.ofNat_ne_zero,
      false_and, not_false_eq_true, div_self, Real.rpow_one]
    ring
  · fun_prop
  · simp
  · apply DifferentiableAt.cpow_const <;> simp

/-- `bottcher_pow` is differentiable where we need it -/
lemma differentiableAt_bottcher_pow :
    DifferentiableAt ℂ (bottcher_pow c z n) ((superF 2).bottcher c z ^ 2 ^ n) := by
  have h := norm_deriv_bottcher_eq (c := c) (z := z) (n := n)
  contrapose h
  simp only [deriv_zero_of_not_differentiableAt h, norm_zero, bottcher_deriv_pow, zpow_neg,
    zpow_natCast, Eq.comm (a := (0 : ℝ)), div_eq_zero_iff, mul_eq_zero, inv_eq_zero,
    pow_eq_zero_iff', OfNat.ofNat_ne_zero, ne_eq, false_and, false_or, not_false_eq_true,
    spotential_coe_ne_zero, or_false]
  exact (Real.rpow_ne_zero (by bound) (by simp)).mpr (by simp)

/-- Express `bottcher` locally in terms of it's value at a future iterate -/
lemma bottcher_pullback (m : (c, ↑z) ∈ (superF 2).post) :
    let s := superF 2
    (fun p ↦ s.bottcher p.1 p.2) =ᶠ[𝓝 (c, z)]
      bottcher_pow c z n ∘
      (fun p : ℂ × ℂ ↦ s.bottcher p.1 p.2) ∘
      (fun p : ℂ × ℂ ↦ (p.1, (f' 2 p.1)^[n] p.2)) := by
  set s := superF 2
  set a : ℂ × ℂ → ℝ := fun p ↦ 2 ^ n * (s.bottcher p.1 p.2 / s.bottcher c z).arg
  have ac : ContinuousAt a (c, z) := by
    refine continuousAt_const.mul ((Complex.continuousAt_arg (by simp)).comp ?_)
    exact (differentiableAt_bottcher m).continuousAt.div_const _
  have a0 : -π < a (c, z) := by simp [a, Real.pi_pos]
  have a1 : a (c, z) < π := by simp [a, Real.pi_pos]
  filter_upwards [continuousAt_const.eventually_lt ac a0,
    ac.eventually_lt continuousAt_const a1] with ⟨d,w⟩ a0 a1
  simp only [Function.comp_apply, ← f_f'_iter, s.bottcher_eqn_iter, bottcher_pow, ← div_pow]
  rw [← Complex.cpow_nat_mul']
  · simp [Complex.cpow_neg, mul_div_cancel₀]
  · simp only [Nat.cast_pow, Nat.cast_ofNat, a, a0]
  · simp only [Nat.cast_pow, Nat.cast_ofNat, a, a1.le]

/-- The norm of the `bottcher` derivative if we iterate `n` times -/
noncomputable def bottcher_deriv_iter (c z dc dz : ℂ) (n : ℕ) : ℝ :=
  let s := superF 2
  bottcher_deriv_pow n (s.potential c z ^ 2 ^ n) *
    ‖fderiv ℂ (fun p ↦ s.bottcher p.1 p.2) (c, (f' 2 c)^[n] z)
    (dc, fderiv ℂ (fun p ↦ (f' 2 p.1)^[n] p.2) (c, z) (dc, dz))‖

@[bound] lemma bottcher_deriv_iter_nonneg : 0 ≤ bottcher_deriv_iter c z dc dz n := by
  simp only [bottcher_deriv_iter]
  bound

/-- If we're postcritical, the `bottcher` derivative norm iterates stably -/
lemma bottcher_deriv_eqn (m : (c, ↑z) ∈ (superF 2).post) :
    ‖fderiv ℂ (fun p ↦ (superF 2).bottcher p.1 p.2) (c, z) (dc, dz)‖ =
      bottcher_deriv_iter c z dc dz n := by
  set s := superF 2
  simp only [bottcher_deriv_iter]
  have di : DifferentiableAt ℂ (fun p ↦ (f' 2 p.1)^[n] p.2) (c, z) := by
    unfold f'
    apply Differentiable.differentiableAt
    fun_prop
  have dp := differentiableAt_bottcher m
  rw [(bottcher_pullback m).fderiv_eq, fderiv_comp, fderiv_comp,
    DifferentiableAt.fderiv_prodMk, fderiv_fst]
  all_goals try fun_prop
  · simp [Function.comp_def, ← f_f'_iter, s.bottcher_eqn_iter, ← Real.rpow_natCast,
      mul_comm _ (deriv _ _), norm_deriv_bottcher_eq]
  · exact differentiableAt_bottcher (by simp [← f_f'_iter, s.iter_stays_post m])
  · simp only [Function.comp_apply, ← f_f'_iter, s.bottcher_eqn_iter,
      differentiableAt_bottcher_pow]
  · simp only [Function.comp_def, ← f_f'_iter, s.bottcher_eqn_iter]
    exact (differentiableAt_bottcher m).pow _

/-- `bottcher_deriv_pow` composes nicely -/
lemma bottcher_deriv_pow_add {a n : ℕ} {p : ℝ} (p0 : 0 < p) :
    bottcher_deriv_pow a (p ^ 2 ^ a) * bottcher_deriv_pow n (p ^ 2 ^ (n + a)) =
      bottcher_deriv_pow (n + a) (p ^ 2 ^ (n + a)) := by
  have t0 : 0 < (2 : ℝ) := by norm_num
  have tp0 : ∀ {x : ℝ}, 0 < (2 : ℝ) ^ x := by bound
  simp only [bottcher_deriv_pow, zpow_neg, zpow_natCast, Nat.cast_add, neg_add, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, zpow_add₀, ← mul_inv, ← Real.rpow_natCast,
    ← Real.rpow_mul p0.le, Nat.cast_pow, Nat.cast_two, ← Real.rpow_add t0, mul_inv_cancel₀ tp0.ne',
    Real.rpow_one]
  simp only [Real.rpow_natCast, Nat.ofNat_pos, Real.rpow_add, mul_comm _ ((2 : ℝ) ^ n)⁻¹, ne_eq,
    pow_eq_zero_iff', OfNat.ofNat_ne_zero, false_and, not_false_eq_true, inv_mul_cancel_left₀,
    mul_inv_rev]
  ring_nf
  field_simp

/-- `bottcher_deriv_iter` is constant once we're in post -/
lemma bottcher_deriv_iter_const {a b : ℕ} (ma : (c, (f 2 c)^[a] z) ∈ (superF 2).post)
    (mb : (c, (f 2 c)^[b] z) ∈ (superF 2).post) :
    bottcher_deriv_iter c z dc dz a = bottcher_deriv_iter c z dc dz b := by
  set s := superF 2
  wlog ab : a ≤ b
  · exact (this mb ma (not_le.mp ab).le).symm
  · rw [← Nat.sub_add_cancel ab] at mb ⊢
    generalize b - a = n at mb
    clear b ab
    simp only [bottcher_deriv_iter, f_f'_iter] at ma mb ⊢
    simp only [bottcher_deriv_eqn ma (n := n), bottcher_deriv_iter, ← fderiv_iterate_add,
      ← mul_assoc, ← Function.iterate_add_apply]
    refine congr_arg₂ _ ?_ rfl
    simp only [← f_f'_iter, s.potential_eqn_iter, ← pow_mul, ← pow_add, add_comm a]
    exact bottcher_deriv_pow_add (by bound)

/-- A notion of `‖deriv bottcher‖` that is meaningful throughout the basin. This works because the
argument is ambiguous (due to the choice of branch cut), but the norm is not. -/
noncomputable def potential_deriv (c z dc dz : ℂ) : ℝ :=
  if h : (c, ↑z) ∈ (superF 2).basin ∧
    ∃ dp : ℝ, 0 ≤ dp ∧ ∀ᶠ n in atTop, dp = bottcher_deriv_iter c z dc dz n
  then choose h.2 else 0

/-- `potential_deriv` is meaningful throughout the basin -/
lemma potential_deriv_prop (m : (c, ↑z) ∈ (superF 2).basin) :
    ∃ dp : ℝ, 0 ≤ dp ∧ ∀ᶠ n in atTop, dp = bottcher_deriv_iter c z dc dz n := by
  set s := superF 2
  obtain ⟨n,p⟩ := s.basin_post m
  refine ⟨bottcher_deriv_iter c z dc dz n, by bound, ?_⟩
  refine Filter.eventually_atTop.mpr ⟨n, fun m nm ↦ bottcher_deriv_iter_const p ?_⟩
  rw [← Nat.sub_add_cancel nm, Function.iterate_add_apply]
  apply s.iter_stays_post p

/-- `potential_deriv` can be computed from any postcritical iterate -/
lemma potential_deriv_eq_iter (m : (c, (f 2 c)^[n] z) ∈ (superF 2).post) :
    potential_deriv c z dc dz = bottcher_deriv_iter c z dc dz n := by
  set s := superF 2
  have b := s.post_basin m
  rw [s.basin_iff_attracts, attracts_shift, ← s.basin_iff_attracts] at b
  simp only [potential_deriv, b, true_and, potential_deriv_prop b, dite_true]
  obtain ⟨k,p⟩ := s.basin_post b
  replace p : ∀ᶠ n in atTop, (c, (f 2 c)^[n] z) ∈ s.post := by
    refine Filter.eventually_atTop.mpr ⟨k, fun m nm ↦ ?_⟩
    rw [← Nat.sub_add_cancel nm, Function.iterate_add_apply]
    apply s.iter_stays_post p
  obtain ⟨a,pa,ea⟩ := (p.and (choose_spec (potential_deriv_prop b (dc := dc) (dz := dz))).2).exists
  rw [ea, bottcher_deriv_iter_const pa m]

/-- `potential_deriv` is the norm of the `bottcher` derivative in post -/
lemma potential_deriv_eq_fderiv (m : (c, ↑z) ∈ (superF 2).post) :
    potential_deriv c z dc dz =
      ‖fderiv ℂ (fun p ↦ (superF 2).bottcher p.1 p.2) (c, z) (dc, dz)‖ := by
  rw [potential_deriv_eq_iter (n := 0) (by simpa)]
  simp [bottcher_deriv_iter, fderiv_snd, bottcher_deriv_pow]

/-- `potential_deriv` satisfies a nice iteration equation -/
noncomputable def potential_deriv_eqn (m : (c, ↑z) ∈ (superF 2).basin) (n : ℕ) :
    potential_deriv c z dc dz =
      bottcher_deriv_pow n ((superF 2).potential c z ^ 2 ^ n) *
      potential_deriv c ((f' 2 c)^[n] z) dc
        (fderiv ℂ (fun p ↦ (f' 2 p.1)^[n] p.2) (c, z) (dc, dz)) := by
  set s := superF 2
  obtain ⟨k,p⟩ := s.basin_post m
  have pnk := s.iter_stays_post p n
  simp only [← Function.iterate_add_apply _ n k] at pnk
  have pkn := pnk
  simp only [add_comm n, Function.iterate_add_apply _ k n, f_f'_iter n] at pkn
  simp only [potential_deriv_eq_iter pkn, potential_deriv_eq_iter pnk, bottcher_deriv_iter,
    ← f_f'_iter, s.potential_eqn_iter, ← pow_mul, ← pow_add, ← mul_assoc, add_comm n]
  rw [bottcher_deriv_pow_add (by bound), ← fderiv_iterate_add, ← Function.iterate_add_apply]

lemma fderiv_bottcher_approx (le : max 10 (√3 * ‖c‖) ≤ ‖z‖) :
    |potential_deriv c z dc dz - (‖z‖ ^ 2)⁻¹ * ‖dz‖| ≤
      ‖z‖⁻¹ * (0.943 / (‖z‖ ^ 2 - ‖c‖ ^ 2) * ‖dc‖ + 2.45 / ‖z‖ ^ 2 * ‖dz‖) := by
  set s := superF 2
  have le1 : √3 * max 4 ‖c‖ ≤ ‖z‖ := by
    refine le_trans ?_ le
    rw [mul_max_of_nonneg _ _ (by bound)]
    refine max_le_max ?_ (by rfl)
    rw [← sq_le_sq₀ (by bound) (by norm_num), mul_pow, Real.sq_sqrt (by bound)]
    norm_num
  have lt2 : max 4 ‖c‖ < ‖z‖ := lt_of_lt_of_le (by bound) le1
  have m : (c, ↑z) ∈ s.post := by
    rw [sup_lt_iff] at lt2
    exact postcritical_large (by bound) (by bound)
  simp only [← norm_pow, ← norm_inv, ← norm_mul, ← norm_neg (_ * dz), potential_deriv_eq_fderiv m]
  refine le_trans (abs_norm_sub_norm_le _ _) ?_
  have e : ‖z‖⁻¹ * (0.943 / (‖z‖ ^ 2 - ‖c‖ ^ 2) * ‖dc‖ + 2.45 / ‖z‖ ^ 2 * ‖dz‖) =
      0.943 / (‖z‖ * (‖z‖ ^ 2 - ‖c‖ ^ 2)) * ‖dc‖ + 2.45 / ‖z‖ ^ 3 * ‖dz‖ := by
    simp only [mul_add, div_eq_mul_inv, mul_inv, pow_succ (n := 2), mul_comm _ ‖z‖⁻¹, ← mul_assoc]
  simp only [fderiv_prod_eq_add_apply (differentiableAt_bottcher m), fderiv_eq_smul_deriv,
    smul_eq_mul, add_sub_assoc, norm_inv, norm_pow, mul_comm dc, mul_comm dz, e]
  refine le_trans (norm_add_le _ _) (add_le_add ?_ ?_)
  · simp only [norm_mul]
    exact mul_le_mul_of_nonneg_right (deriv_sbottcher_c_approx lt2) (by bound)
  · simp only [← add_mul, norm_mul, sub_neg_eq_add]
    exact mul_le_mul_of_nonneg_right (deriv_sbottcher_z_approx le1) (by bound)
