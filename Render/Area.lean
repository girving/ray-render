import Render.Potential

/-!
## Area estimation using the Koebe quarter theorem
-/

/-- Given a point, produce the radius of an open disk guaranteed to miss the Mandelbrot set -/
@[irreducible] def free_radius (c : Box) (n : ℕ) : Floating :=
  let r : Floating := 1000
  let p := c.potential_deriv c 1 1 n r
  match p.m with
  | .large => (p.p.scaleB (-2) * (1 - p.p.sqr) / p.dp).lo  -- Rule out a disk using Koebe
  | _ => 0  -- With .nan or .small, we give up and return the empty disk
