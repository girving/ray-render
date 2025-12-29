import Correct.Koebe
import Correct.Potential
import Correct.Square
import Ray.Koebe.KoebePick
import Render.Area

/-!
## Area estimation using the Koebe quarter theorem
-/

open Function (uncurry)
open MeasureTheory
open Metric (ball)
open OneDimension
open Real (log)
open Set
open scoped RiemannSphere

variable {s x dx : Interval} {s' x' dx' : ℝ} {c z dc dz : Box} {c' z' dc' dz' : ℂ} {n : ℕ}

/-- Exact precision free radius using the Koebe-Pick theorem -/
noncomputable def free_radius' (c : ℂ) : ℝ :=
  potential 2 c * (1 - potential 2 c ^ 2) / potential_deriv c / 4

@[simp, bound] lemma free_radius'_nonneg (c : ℂ) : 0 ≤ free_radius' c := by
  simp only [free_radius']
  bound

/-- `free_radius'` returns a radius disjoint from the Mandelbrot set -/
theorem free_radius'_correct (c : ℂ) : ball c (free_radius' c) ⊆ mandelbrotᶜ := by
  simp only [free_radius', mandelbrot_eq_multibrot]
  by_cases m : c ∈ multibrot 2
  · simp [potential_eq_one.mpr m]
  · exact bottcher_koebe m

/-- `free_radius` returns a radius disjoint from the Mandelbrot set -/
theorem free_radius_correct (cm : approx c c') :
    ball c' (free_radius c n).val ⊆ mandelbrotᶜ := by
  rw [free_radius]
  generalize hp : c.potential_deriv c 1 1 n 1000 = p
  generalize hm : p.m = m
  cases m with
  | nan => simp
  | small => simp
  | large =>
    generalize hr : p.p.scaleB (-2) * (1 - p.p.sqr) / p.dp = r
    have a : approx r (free_radius' c') := by
      simp only [free_radius', div_eq_mul_inv, Interval.div_def, mul_comm _ (4 : ℝ)⁻¹, ← mul_assoc,
        ← hp, ← hr]
      rw [mul_comm (4 : ℝ)⁻¹, (by simp; norm_num : (4 : ℝ)⁻¹ = (2 : ℝ) ^ ((-2 : Int64) : ℤ))]
      approx
    simp only [approx, Interval.lo_eq_nan] at a
    rcases a with rn | ⟨le, _⟩
    · simp [rn]
    · exact subset_trans (Metric.ball_subset_ball (by simpa)) (free_radius'_correct c')

/-- `free_radius` is nonnegative, since we replace `nan` with `0` -/
@[simp, bound] lemma free_radius_nonneg (c : Box) (n : ℕ) : 0 ≤ (free_radius c n).val := by
  simp only [free_radius]
  bound

@[simp] private lemma dyadic_2 : Dyadic.toRat 2 = 2 := rfl
@[simp] private lemma dyadic_4 : Dyadic.toRat 4 = 4 := rfl

/-- We correctly upper bound the area of the Mandelbrot set on squares -/
lemma le_upper_area_square {x y s : Dyadic} {d n : ℕ} (s0 : 0 ≤ s) :
    volume.real (mandelbrot ∩ csquare ⟨x.toRat, y.toRat⟩ s.toRat) ≤
      (upper_area_square x y s d n).toRat := by
  induction' d with d up generalizing x y s
  · simp only [upper_area_square, Dyadic.toRat_mul, dyadic_4, Rat.cast_mul, Rat.cast_ofNat]
    refine le_trans (measureReal_mono inter_subset_right (by finiteness)) ?_
    rw [volumeReal_csquare (by bound), pow_two, mul_assoc]
  · simp only [upper_area_square]
    generalize hxi : Interval.ofDyadic x = xi
    generalize hyi : Interval.ofDyadic y = yi
    generalize hc : (⟨xi, yi⟩ : Box) = c
    generalize hc' : (⟨x.toRat, y.toRat⟩ : ℂ) = c'
    split_ifs with sr
    · suffices e : mandelbrot ∩ osquare c' s.toRat = ∅ by
        have ae : (mandelbrot ∩ osquare c' s.toRat : Set ℂ) =ᶠ[ae volume]
            (mandelbrot ∩ csquare c' s.toRat : Set ℂ) :=
          ae_eq_set_inter (by rfl) osquare_ae_eq_csquare
        simp [← measureReal_congr ae, e]
      simp only [← disjoint_iff_inter_eq_empty, ← subset_compl_iff_disjoint_left]
      have cm : approx c c' := by
        simp only [Box.approx_iff_ext, ← hc, ← hc', ← hxi, ← hyi]
        approx
      refine subset_trans (osquare_subset_ball ?_) (free_radius_correct cm (n := n))
      simp only [mul_assoc, ← pow_two, ←  Dyadic.toRat_le_toRat_iff, Dyadic.toRat_pow,
        Dyadic.toRat_mul, dyadic_2, Floating.toRat_vald, ← Rat.cast_le (K := ℝ), Rat.cast_pow,
        Rat.cast_mul, Rat.cast_ofNat, Rat.cast_pow, Floating.coe_valq] at sr
      rwa [← sq_le_sq₀ (by bound) (by bound), mul_pow, Real.sq_sqrt (by norm_num)]
    · generalize hh : div2 s = h
      have h0 : 0 ≤ h := by bound
      simp only [Dyadic.toRat_add, Rat.cast_add]
      have a4 : ∀ {a b c d a' b' c' d' : ℝ}, a ≤ a' → b ≤ b' → c ≤ c' → d ≤ d' →
          a + b + c + d ≤ a' + b' + c' + d' := by bound
      refine le_trans ?_ (a4 (up h0) (up h0) (up h0) (up h0))
      refine le_trans ?_ (add_le_add_left (add_le_add_left (measureReal_union_le _ _) _) _)
      refine le_trans ?_ (add_le_add_left (measureReal_union_le _ _) _)
      refine le_trans ?_ (measureReal_union_le _ _)
      refine measureReal_mono ?_
      simp only [← inter_union_distrib_left, Dyadic.toRat_add, Rat.cast_add, ← sub_eq_add_neg,
        Dyadic.toRat_sub, Rat.cast_sub]
      refine inter_subset_inter_right _ ?_
      simp only [csquare_partition (s := s.toRat), ← hh, div2_eq_mul, Dyadic.toRat_div2,
        ← div_eq_inv_mul, Rat.cast_div, (by norm_num : (2 : ℚ) = (2 : ℝ)), ← hc', subset_refl]

/-- We correctly upper bound the area of the Mandelbrot set on squares -/
lemma le_upper_area {d n : ℕ} : volume.real mandelbrot ≤ (upper_area d n).toRat := by
  simp only [upper_area]
  refine le_trans (measureReal_mono ?_) (le_upper_area_square (by decide))
  simp only [mandelbrot_eq_multibrot, csquare, Dyadic.toRat_zero, Rat.cast_zero, sub_zero, dyadic_2,
    Rat.cast_ofNat, subset_inter_iff, subset_refl, subset_setOf, true_and]
  intro c m
  have r := multibrot_le_two m
  exact ⟨le_trans (Complex.abs_re_le_norm c) r, le_trans (Complex.abs_im_le_norm c) r⟩
