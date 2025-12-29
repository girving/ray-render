import Interval.Approx.Dyadic
import Interval.Floating.Dyadic
import Interval.Interval.Dyadic
import Render.Potential

/-!
## Area estimation using the Koebe quarter theorem
-/

/-- Given a point, produce the radius of an open disk guaranteed to miss the Mandelbrot set -/
@[irreducible] def free_radius (c : Box) (n : ℕ) : Floating :=
  let r : Floating := 1000
  let p := c.potential_deriv c 1 1 n r
  match p.m with
  | .large => max 0 (p.p.scaleB (-2) * (1 - p.p.sqr) / p.dp).lo  -- Rule out a disk using Koebe
  | _ => 0  -- With .nan or .small, we give up and return the empty disk

/-- Upper bound the area of the Mandelbrot set contained within the square `(x,y) + [-s, s]²` -/
def upper_area_square (x y s : Dyadic) (d n : ℕ) : Dyadic := match d with
  | 0 => 4 * s * s
  | d + 1 =>
    -- Try to rule out the entire square, in which case our area bound is 0
    let r := (free_radius ⟨.ofDyadic x, .ofDyadic y⟩ n).vald
    if 2 * s * s ≤ r * r then 0 else
    -- Otherwise, sum across the four child squares
    let h := div2 s
    let u := fun dx dy ↦ upper_area_square (x + dx) (y + dy) h d n
    u h h + u (-h) h + u h (-h) + u (-h) (-h)

/-- Upper bound the area of the Mandelbrot set -/
@[irreducible] def upper_area (d n : ℕ) : Dyadic :=
  upper_area_square 0 0 2 d n
