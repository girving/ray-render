import Correct.Dynamics
import Ray.Koebe.Koebe
import Ray.Mandelbrot
import Ray.Multibrot.Isomorphism

/-!
## Koebe quarter theorem specialised to `bottcher` and `ray`

We can't apply Koebe to the full unit ball of `ray 2`, since it has a pole at the origin.
Therefore, we do the same Möbius transformation as in `KoebePick.lean`, but then shrink the domain
to avoid the pole.

GPT-5.2 discussion: https://chatgpt.com/share/6950c08a-e78c-8009-9534-0a0519bf2b18
-/

open Metric (ball isOpen_ball)
open Set
open scoped ContDiff OnePoint RiemannSphere Topology

variable {c w z : ℂ}
variable {d : ℕ} [Fact (2 ≤ d)]

/-- The Koebe quarter theorem specialised to our `bottcher` case -/
public theorem bottcher_koebe (m : c ∉ multibrot 2) :
    ball c (potential 2 c * (1 - potential 2 c ^ 2) / potential_deriv c / 4) ⊆ (multibrot 2)ᶜ := by
  set p := potential 2 c
  set dp := potential_deriv c
  set z := bottcher 2 c
  have p0 : 0 < p := potential_pos
  have p1 : p < 1 := by simpa only [p, potential_lt_one, multibrotExt_coe]
  have z1 : ‖z‖ < 1 := by simpa only [z, norm_bottcher, p1]
  set g : ℂ → ℂ := OnePoint.toComplex ∘ ray 2 ∘ mobius z
  have sub : ball (0 : ℂ) p ⊆ ball 0 1 := Metric.ball_subset_ball p1.le
  have g0 : g 0 = c := by
    simp only [Function.comp_apply, mobius_zero, g, z]
    rw [ray_bottcher, RiemannSphere.toComplex_coe]
    simpa [multibrotExt_coe]
  have fin : ∀ {w}, w ∈ ball 0 p → ray 2 (mobius z w) ≠ (∞ : 𝕊) := by
    intro w wp
    have w1 : ‖w‖ < 1 := by simp only [Metric.mem_ball, dist_zero_right] at wp; linarith
    have m1 : mobius z w ∈ ball 0 1 := by simpa using norm_mobius_lt_one z1 w1
    simp only [ne_eq, ray_eq_inf m1, mobius_eq_zero_iff z1 w1]
    contrapose wp
    simp [← wp, p, z, norm_bottcher]
  have ga : ContDiffOn ℂ ω g (ball 0 p) := by
    intro w wp
    have w1 : ‖w‖ < 1 := by simp only [Metric.mem_ball, dist_zero_right] at wp; linarith
    have m1 : mobius z w ∈ ball 0 1 := by simpa using norm_mobius_lt_one z1 w1
    refine ContDiffAt.contDiffWithinAt (ContMDiffAt.contDiffAt ?_)
    refine (RiemannSphere.mAnalyticAt_toComplex' (by exact fin wp)).comp _ ?_
    refine (rayMAnalytic 2 _ m1).comp _ ?_
    exact ((contDiffOn_mobius z1 w (by simpa)).contDiffAt
      (isOpen_ball.mem_nhds (by simpa))).contMDiffAt
  have inj : InjOn g (ball 0 p) := by
    intro a am b bm e
    have a1 : mobius z a ∈ ball 0 1 := mapsTo_mobius z1 (sub am)
    have b1 : mobius z b ∈ ball 0 1 := mapsTo_mobius z1 (sub bm)
    simpa only [Function.comp_apply, g, RiemannSphere.toComplex_inj (fin am) (fin bm),
      ray_inj.eq_iff a1 b1, (injOn_mobius z1).eq_iff (sub am) (sub bm)] using e
  have gsub : g '' ball 0 p ⊆ (multibrot 2)ᶜ := by
    intro c m
    obtain ⟨w,wm,e⟩ := m
    simp only [mem_compl_iff, ← multibrotExt_coe, ← e, g, Function.comp_def,
      RiemannSphere.coe_toComplex (fin wm)]
    exact ray_mem_multibrotExt (mapsTo_mobius z1 (sub wm))
  have e1 : ‖(‖z‖ ^ 2 - 1 : ℂ)‖ = 1 - p ^ 2 := by
    norm_cast
    rw [norm_sub_rev, Real.norm_eq_abs, abs_of_nonneg (by bound)]
    simp only [norm_bottcher, z, p]
  have dg : ‖deriv g 0‖ = (1 - p ^ 2) / potential_deriv c := by
    have post := multibrotPost m
    rw [← e1, potential_deriv_eq_deriv m, ← norm_div]
    apply congr_arg
    have eb : (fun w ↦ bottcher' 2 (ray 2 (mobius z w)).toComplex) =ᶠ[𝓝 0] mobius z := by
      have m0 : (0 : ℂ) ∈ ball 0 p := by simp [p0]
      filter_upwards [isOpen_ball.mem_nhds m0] with w wm
      have br := bottcher_ray (d := 2) (z := mobius z w) (mapsTo_mobius z1 (sub wm))
      rwa [← RiemannSphere.coe_toComplex (fin wm), bottcher_coe] at br
    rw [eq_div_iff_mul_eq (deriv_bottcher_ne_zero m), mul_comm (deriv g 0), ← g0, ← deriv_comp]
    · simp only [Function.comp_def, Function.comp_apply, eb.deriv_eq, deriv_mobius_zero z1, g]
    · exact (bottcher_analytic _ (g0 ▸ m)).differentiableAt
    · exact ((ga _ (Metric.mem_ball_self p0)).contDiffAt
        (Metric.ball_mem_nhds _ p0)).differentiableAt le_top
  simpa only [g0, dg, dp, mul_div_assoc] using
    subset_trans (koebe_quarter' (f := g) (ga.analyticOnNhd isOpen_ball) inj) gsub
