import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Cases

/-!
## Calculus lemmas

Derivative facts which are independent of holomorphic dynamics.
-/

open Function (uncurry)
open Set

variable {𝕜 E F G : Type} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedAddCommGroup F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] [NormedSpace 𝕜 G]
variable {c z dc dz : ℂ} {n : ℕ}

@[fun_prop] lemma Differentiable.iterate_fun {f : E → F → F} {g : E → F}
    (df : Differentiable 𝕜 (uncurry f)) (dg : Differentiable 𝕜 g) (n : ℕ) :
    Differentiable 𝕜 (fun x : E ↦ (fun y ↦ f x y)^[n] (g x)) := by
  have e : (fun p : E × F ↦ (p.1, f p.1 p.2))^[n] ∘ (fun x : E ↦ (x, g x)) =
      (fun x : E ↦ (x, (fun y ↦ f x y)^[n] (g x))) := by
    funext x
    induction' n with n h
    · simp
    · simp_all only [Function.iterate_succ', Function.comp_apply]
  replace e : (fun x : E ↦ (fun y ↦ f x y)^[n] (g x)) =
      Prod.snd ∘ (fun p : E × F ↦ (p.1, f p.1 p.2))^[n] ∘ (fun x : E ↦ (x, g x)) := by
    simp only [e, Function.comp_def]
  rw [e]
  fun_prop

/-- Express a 2D `fderiv` application as a sum of two 1D derivatives -/
lemma fderiv_prod_eq_add_apply {f : E × F → G} {p dp : E × F} (df : DifferentiableAt 𝕜 f p) :
    fderiv 𝕜 f p dp =
      fderiv 𝕜 (fun x ↦ f (x, p.2)) p.1 dp.1 + fderiv 𝕜 (fun y ↦ f (p.1, y)) p.2 dp.2 := by
  replace df := df.hasFDerivAt
  have df1 := df.comp p.1 ((hasFDerivAt_id (𝕜 := 𝕜) p.1).prodMk (hasFDerivAt_const p.2 p.1))
  have df2 := df.comp p.2 ((hasFDerivAt_const p.1 p.2).prodMk (hasFDerivAt_id (𝕜 := 𝕜) p.2))
  simp only [id_eq, Function.comp_def] at df1 df2
  simp [df1.fderiv, df2.fderiv, ← ContinuousLinearMap.map_add]
