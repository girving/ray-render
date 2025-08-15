import Interval.Interval.Exp
import Interval.Interval.Log
import Render.Iterate

/-!
## Approximate computation of the Mandelbrot potential function

Fix `c`, and let `p z = potential 2 c z` be the potential function for the `c`-Julia set.  Say we
iterate `n` times to get `w = f^[n] z`.  There are two cases

#### Case 1: `abs w ≤ 4`

By `le_potential`, we have

  `0.216 ≤ p w`
  `0.216 ^ (2^n)⁻¹ ≤ p z`.

Not very many iterations will give us a lower bound very close to `1`.

#### Case 2: `4 ≤ abs w`

Increasing `n` by 1 if necessary, we have `6 ≤ abs w`.  By `potential_approx` and
`potential_error_le_of_z6`, we have

  `|p w - 1/abs w| ≤ 0.8095 / abs w ^ 1.927`

Here is an `abs w : 1/abs w, RHS` table for various `abs w` values:

  `w    6: 1/w 0.16667, error 2.563e-2, ratio 0.153`
  `w   32: 1/w 0.03125, error 1.018e-3, ratio 0.032`
  `w 1020: 1/w 0.00098, error 1.290e-6, ratio 0.001`

We then finish with

  `p z = p w ^ (2^n)⁻¹`

See `Correct.Potential` for correctness proofs.
-/

open Real (log)
open Set

private local instance : Fact (2 ≤ 2) := ⟨by norm_num⟩

/-!
### Potential approximation routines
-/

/-- Repeated square roots: `x ^ (2 ^ -n)` -/
@[irreducible] def Interval.iter_sqrt (x : Interval) (n : ℕ) : Interval :=
  exp ((log x).scaleB' (-.ofNat0 n))

/-- Approximate the potential of a large `z`.
    The estimate is independent of `c`, but is only valid if `6, abs c ≤ abs z` -/
@[irreducible] def Box.potential_large (z : Box) : Interval :=
  let s := z.normSq
  -- We have `|p j.z - s ^ (-1/2)| ≤ 0.8095 * s ^ -0.9635`
  -- `s ^ a = exp (a * log s)`, so we'll CSE the `log s`
  let log_s := s.log
  (-log_s.div2).exp.grow (0.8095 * (log_s * -0.9635).exp).hi

/-- Approximate the potential of a small `z` (valid for `abs c, abs z ≤ 4`) -/
@[irreducible] def Box.potential_small : Interval :=
  0.216 ∪ 1

/-- Which potential estimate we used -/
inductive PotentialMode : Type
  | nan
  | large
  | small

/-- Approximate the Mandelbrot potential function at any point.
    We also return the exit mode from our iteration. -/
@[irreducible] def Box.potential (c z : Box) (n : ℕ) (r : Floating) : Interval × PotentialMode :=
  let cs := c.normSq.hi
  let i := iterate c z (cs.max 9) n
  match i.exit with
  | .nan => (nan, .nan)
  | .large =>
    -- We're outside radius `3` after `i.n` iterations.  Iterate a bit more to make `z` very large,
    -- then use our large `z` potential bound.  This should always work, so we use a large count.
    let rc := (r.mul r true).max (cs.max 36)  -- We need `6, abs c ≤ abs z`
    let j := iterate c i.z rc 1000
    match j.exit with
    | .large => ((potential_large j.z).iter_sqrt (i.n + j.n), .large)
    | _ => (nan, .nan)  -- If we fail to leave the large radius, give up
  | .count =>
    -- We know we're `≤ 3`.  Check that we're `≤ 4`, bail if not, and use the small bound if so.
    let zs := i.z.normSq.hi
    if zs = nan ∨ 16 < zs ∨ 16 < cs then (nan, .nan) else
    (potential_small.iter_sqrt i.n, .small)
