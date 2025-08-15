import Render.Color
import Render.Potential

/-!
## Pictures of the Mandelbrot set

We define some maps `ℂ → Color` which illustrate the Mandelbrot set.

See `Correct.Mandelbrot` for correctness proofs.
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
