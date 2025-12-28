import Correct.Koebe
import Correct.Potential
import Ray.Koebe.KoebePick
import Render.Area

/-!
## Area estimation using the Koebe quarter theorem
-/

open Function (uncurry)
open Metric (ball)
open OneDimension
open Real (log)
open Set
open scoped RiemannSphere

variable {x dx : Interval} {x' dx' : ℝ} {c z dc dz : Box} {c' z' dc' dz' : ℂ} {n : ℕ}

/-- Exact precision free radius using the Koebe-Pick theorem -/
noncomputable def free_radius' (c : ℂ) : ℝ :=
  potential 2 c * (1 - potential 2 c ^ 2) / potential_deriv c / 4

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
    · simp [rn, Metric.ball_eq_empty.mpr Floating.val_nan_le_zero]
    · exact subset_trans (Metric.ball_subset_ball le) (free_radius'_correct c')
