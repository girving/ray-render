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

def Dyadic.toFloat : Dyadic → Float
  | .zero => 0
  | .ofOdd n k _ => (Float.ofInt n).scaleB (-k)

instance : Lean.ToJson Dyadic where
  toJson x := x.toFloat.toJson

/-- The trace of an area computation -/
inductive Trace where
  | leaf : Trace
  | free : (x y s r : Dyadic) → Trace
  | split : (x y s r : Dyadic) → Trace → Trace → Trace → Trace → Trace
  | leafs : (x y s r : Dyadic) → Trace  -- Same as `split` with four implicit leaves
  | top : Trace → Trace → Trace
deriving Lean.ToJson

def Trace.split' (x y s r : Dyadic) (t0 t1 t2 t3 : Trace) : Trace := match t0, t1, t2, t3 with
  | .leaf, .leaf, .leaf, .leaf => .leafs x y s r
  | _, _, _, _ => .split x y s r t0 t1 t2 t3

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

/-- Same as `upper_area_square`, but record the samples used -/
def upper_area_square_sample (x y s : Dyadic) (d n : ℕ) : Dyadic × Trace := match d with
  | 0 => (4 * s * s, .leaf)
  | d + 1 =>
    -- Try to rule out the entire square, in which case our area bound is 0
    let r := (free_radius ⟨.ofDyadic x, .ofDyadic y⟩ n).vald
    if 2 * s * s ≤ r * r then (0, .free x y s r) else
    -- Otherwise, sum across the four child squares
    let h := div2 s
    let u := fun dx dy ↦ upper_area_square_sample (x + dx) (y + dy) h d n
    let (a0, t0) := u h h
    let (a1, t1) := u (-h) h
    let (a2, t2) := u h (-h)
    let (a3, t3) := u (-h) (-h)
    (a0 + a1 + a2 + a3, .split' x y s r t0 t1 t2 t3)

/-- Upper bound the area of the Mandelbrot set -/
@[irreducible] def upper_area (d n : ℕ) : Dyadic := match d with
  | 0 => 16  -- Have a base case so that we don't shift the meaning of `d`
  | d + 1 =>
    -- Use symmetry about the real axis
    2 * (upper_area_square 1 1 1 d n + upper_area_square (-1) 1 1 d n)

/-- Same as `upper_area`, but record the samples used -/
@[irreducible] def upper_area_sample (d n : ℕ) : Dyadic × Trace := match d with
  | 0 => (16, .leaf)  -- Have a base case so that we don't shift the meaning of `d`
  | d + 1 =>
    -- Use symmetry about the real axis
    let (a0, t0) := upper_area_square_sample 1 1 1 d n
    let (a1, t1) := upper_area_square_sample (-1) 1 1 d n
    (2 * (a0 + a1), .top t0 t1)

/-!
### The trace versions are the same as the non-trace versions
-/

variable {x y s : Dyadic} {d n : ℕ}

@[simp] lemma fst_upper_area_square_sample :
    (upper_area_square_sample x y s d n).1 = upper_area_square x y s d n := by
  induction' d with d h generalizing x y s
  · rfl
  · simp only [upper_area_square_sample, upper_area_square, h, apply_ite]
    grind

@[simp] lemma fst_upper_area_sample :
    (upper_area_sample d n).1 = upper_area d n := by
  induction' d
  · simp only [upper_area_sample, upper_area]
  · simp only [upper_area_sample, fst_upper_area_square_sample, upper_area]
