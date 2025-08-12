import Interval.Box.Basic
import Interval.Interval.Conversion
import Ray.Dynamics.Mandelbrot
import Render.Color
import Render.Potential

/-!
## Pictures of the Mandelbrot set

We define some maps `ℂ → Color` which illustrate the Mandelbrot set.
-/

open Classical
open Set

private local instance : Fact (2 ≤ 2) := ⟨by norm_num⟩

-- Colors used below
@[irreducible] def clear : Color ℚ := ⟨0, 0, 0, 0⟩
@[irreducible] def inside : Color ℚ := ⟨0, 0, 0, 1⟩
@[irreducible] def outside : Color ℚ := ⟨0.196, 0.274, 0.96, 1⟩
@[irreducible] def green : Color ℚ := ⟨0.196, 0.96, 0.274, 1⟩
@[irreducible] def far : Color ℚ := ⟨0.372, 0.803, 1, 1⟩

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

-- Interval versions of colors
@[irreducible] def clear' : Color Interval := .ofRat clear
@[irreducible] def inside' : Color Interval := .ofRat inside
@[irreducible] def outside' : Color Interval := .ofRat outside
@[irreducible] def green' : Color Interval := .ofRat green
@[irreducible] def far' : Color Interval := .ofRat far

/-- Transparent at infinity, blue at the Mandelbrot set -/
def bad_potential_image (n : ℕ) (r : Floating) (c : ℚ × ℚ) : Color UInt8 :=
  let c := Box.ofRat c
  let p := c.potential c n r
  let t := p.1.sqr.sqr.sqr.sqr
  let i := lerp t clear' outside'
  i.quantize

/-- `potential_image'` is conservative -/
lemma approx_bad_potential_image {c : ℚ × ℚ} {n : ℕ} {r : Floating} :
    potential_image c ∈ approx (bad_potential_image n r c) := by
  rw [potential_image, bad_potential_image]
  have e : ∀ p : ℝ, p^16 = (((p^2)^2)^2)^2 := by intro p; simp only [← pow_mul]
  rw [outside', clear', e]
  approx
