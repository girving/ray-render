import Correct.Dynamics
import Ray.Mandelbrot
import Render.Iterate

/-!
## Mandelbrot iteration

We iterate until either a cutoff is reached or we exceed a given radius, recording why we stopped.

See `Render.Iterate` for the implementation.
-/

open Function (uncurry)
open Set

variable {c z dc dz : Box} {rs : Floating} {c' z' dc' dz' : ℂ} {rs' : ℝ} {k n : ℕ}

/-- All correctness properties of `iterate_deriv'` in a single lemma -/
lemma iterate_deriv'_correct (cm : approx c c') (zm : approx z z') (dcm : approx dc dc')
    (dzm : approx dz dz') (rsm : rs' ≤ rs.val) (k n : ℕ) :
    let i := iterate_deriv' c z dc dz rs k n
    let fn := fun p : ℂ × ℂ ↦ (f' 2 p.1)^[i.n - k] p.2
    let w' := fn ⟨c', z'⟩
    let dw' := fderiv ℂ fn ⟨c', z'⟩ ⟨dc', dz'⟩
    k ≤ i.n ∧ approx i.z w' ∧ approx i.dz dw' ∧ (i.exit = .large → rs' < ‖w'‖ ^ 2) := by
  induction' n with n h generalizing k z z' dz dz'
  · simp only [iterate_deriv', le_refl, tsub_eq_zero_of_le, Function.iterate_zero, id_eq, reduceCtorEq,
      false_implies, and_true, fderiv_snd, ContinuousLinearMap.coe_snd', zm, dzm]
  · simp only [iterate_deriv', Floating.val_lt_val]
    generalize hzr2 : z.re.sqr = zr2
    generalize hzi2 : z.im.sqr = zi2
    generalize hz2 : zr2.lo.add zi2.lo false = z2
    generalize hw : (⟨zr2 - zi2, (z.re * z.im).scaleB 1⟩ : Box) + c = w
    generalize hdw : z.scaleB 1 * dz + dc = dw
    have we : w = z.sqr + c := by rw [← hw, Box.sqr, hzr2, hzi2]
    have wa : approx w (f' 2 c' z') := by rw [we, f']; approx
    generalize hi : iterate_deriv' c w dc dw rs (k + 1) n = i
    generalize hfn : (fun p : ℂ × ℂ ↦ (f' 2 p.1)^[i.n - k] p.2) = fn
    have dwa : approx dw (fderiv ℂ (uncurry (f' 2)) ⟨c', z'⟩ ⟨dc', dz'⟩) := by
      rw [fderiv_f', ← hdw]; approx
    generalize hw' : f' 2 c' z' = w' at wa
    by_cases z2n : z2 = nan
    · simpa only [z2n, ↓reduceIte, le_refl, tsub_eq_zero_of_le, Function.iterate_zero, id_eq,
        reduceCtorEq, false_implies, and_true, true_and, zm, fderiv_snd]
    by_cases rz : rs.val < z2.val
    · simp only [z2n, rz, ite_true, le_refl, tsub_eq_zero_of_le, Function.iterate_zero, id_eq,
        forall_true_left, true_and, Complex.norm_def, Real.sq_sqrt (Complex.normSq_nonneg _),
        if_false, fderiv_snd, ContinuousLinearMap.coe_snd', zm, dzm]
      refine lt_of_le_of_lt rsm (lt_of_lt_of_le rz ?_)
      simp only [Complex.normSq_apply, ← sq, ←hz2, ←hzr2, ←hzi2] at z2n ⊢
      rcases Floating.ne_nan_of_add z2n with ⟨nr, ni⟩
      simp only [ne_eq, Interval.lo_eq_nan] at nr ni
      refine le_trans (Floating.add_le z2n) (add_le_add ?_ ?_)
      · apply Interval.lo_le nr; approx
      · apply Interval.lo_le ni; approx
    · simp only [rz, ite_false, z2n]
      specialize h wa dwa (k+1)
      simp only [hi] at h
      refine ⟨by omega, ?_⟩
      have ie : i.n - k = (i.n - (k + 1)) + 1 := by omega
      rw [ie, Function.iterate_succ_apply, fderiv_iterate_succ, hw']
      exact h.2

/-- `iterate_deriv` produces a correct iterate -/
@[approx] lemma approx_iterate_deriv_z (cm : approx c c') (zm : approx z z') (dcm : approx dc dc')
    (dzm : approx dz dz') (n : ℕ) :
    approx (iterate_deriv c z dc dz rs n).z ((f' 2 c')^[(iterate_deriv c z dc dz rs n).n] z') := by
  rw [iterate_deriv]
  by_cases rsn : rs = nan
  · simpa only [rsn, ite_true, Function.iterate_zero, id_eq]
  · simp only [rsn, ite_false]
    exact (iterate_deriv'_correct cm zm dcm dzm (le_refl _) 0 n).2.1

/-- `iterate_deriv` produces a correct derivative -/
@[approx] lemma approx_iterate_deriv_dz (cm : approx c c') (zm : approx z z') (dcm : approx dc dc')
    (dzm : approx dz dz') (n : ℕ) :
    let i := iterate_deriv c z dc dz rs n
    approx i.dz (fderiv ℂ (fun p : ℂ × ℂ ↦ (f' 2 p.1)^[i.n] p.2) ⟨c', z'⟩ ⟨dc', dz'⟩) := by
  rw [iterate_deriv]
  by_cases rsn : rs = nan
  · simpa only [rsn, ite_true, Function.iterate_zero, id_eq, fderiv_snd]
  · have h := iterate_deriv'_correct cm zm dcm dzm (le_refl _) 0 n (rs := rs)
    simp only [Nat.sub_zero] at h
    simp only [rsn, ite_false, h]

/-- `iterate` produces a correct iterate -/
@[approx] lemma approx_iterate (cm : approx c c') (zm : approx z z') (n : ℕ) :
    approx (iterate c z rs n).z ((f' 2 c')^[(iterate c z rs n).n] z') := by
  simpa using approx_iterate_deriv_z cm zm approx_zero approx_zero n

/-- If `iterate_deriv` claims the result is large, it is` -/
lemma iterate_deriv_large (cm : approx c c') (zm : approx z z') (dcm : approx dc dc')
    (dzm : approx dz dz') (l : (iterate_deriv c z dc dz rs n).exit = .large) :
    rs.val < ‖(f' 2 c')^[(iterate_deriv c z dc dz rs n).n] z'‖ ^ 2 := by
  rw [iterate_deriv] at l ⊢
  by_cases rsn : rs = nan
  · simp only [rsn, ↓reduceIte, reduceCtorEq] at l
  · simp only [rsn, ite_false] at l ⊢
    simpa only [not_lt, Nat.sub_zero] using
      (iterate_deriv'_correct cm zm dcm dzm (le_refl _) 0 n).2.2.2 l

/-- If `iterate` claims the result is large, it is` -/
lemma iterate_large (cm : approx c c') (zm : approx z z') (l : (iterate c z rs n).exit = .large) :
    rs.val < ‖(f' 2 c')^[(iterate c z rs n).n] z'‖ ^ 2 := by
  simpa using iterate_deriv_large cm zm approx_zero approx_zero (by simpa)

/-- `iterate_deriv` exits with `.nan` when `rs = nan` -/
@[simp] lemma iterate_deriv_nan : (iterate_deriv c z dc dz nan n).exit = .nan := by
  rw [iterate_deriv]; simp only [ite_true]

/-- `iterate` exits with `.nan` when `rs = nan` -/
@[simp] lemma iterate_nan : (iterate c z nan n).exit = .nan := by
  rw [iterate]; simp only [ite_true]

/-- `iterate_deriv` exits with `.nan` when `rs = nan` -/
@[simp] lemma ne_nan_of_iterate_deriv (e : (iterate_deriv c z dc dz rs n).exit ≠ .nan) :
    rs ≠ nan := by
  contrapose e
  simp only [e, iterate_deriv_nan]

/-- Iterate exits with `.nan` when `rs = nan` -/
@[simp] lemma ne_nan_of_iterate (e : (iterate c z rs n).exit ≠ .nan) : rs ≠ nan := by
  contrapose e
  simp only [e, iterate_nan]
