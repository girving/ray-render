import Correct.Potential
import Render.Mandelbrot

/-!
## Pictures of the Mandelbrot set

See `Render.Mandelbrot` for implementation.
-/

open Classical
open Set

private local instance : Fact (2 ≤ 2) := ⟨by norm_num⟩

/-- Blue outside, black inside -/
noncomputable def solid_image (c : ℂ) : Color ℚ :=
  if c ∈ mandelbrot then inside else outside

/-- Blue outside varying with potential, black inside -/
noncomputable def smooth_image (c : ℂ) : Color ℝ :=
  if c ∈ mandelbrot then (inside : Color ℝ) else
  let p := potential 2 c
  lerp p far outside

/-- Transparent at infinity, blue at the Mandelbrot set -/
noncomputable def potential_image (c : ℂ) : Color ℝ :=
  let p := potential 2 c
  let t := p ^ 16
  lerp t clear outside

/-!
### Bad intervals approximations, evaluating at single points only

This is 'bad' because we're not doing a Koebe quarter theorem-type evaluation that holds in a disk.
-/

/-- `potential_image'` is conservative -/
lemma approx_bad_potential_image {c : ℚ × ℚ} {n : ℕ} {r : Floating} :
    approx (bad_potential_image n r c) (potential_image c) := by
  rw [potential_image, bad_potential_image]
  have e : ∀ p : ℝ, p^16 = (((p^2)^2)^2)^2 := by intro p; simp only [← pow_mul]
  rw [outside', clear', e]
  approx
