import Render.Potential

/-!
## Potential unit tests

The first time I ran this, it failed to compute tight intervals for interior points.  Let's try
some examples.
-/

section debug
/-
def c : Box := .ofRat (-119/256, -763/1280)
def cs := c.normSq.hi
def n := 80
def r : Floating := 1000
def i := iterate c c (cs.max 9) n
def zs' := i.z.normSq
def zs := i.z.normSq.hi
#eval i
#eval zs'
--#eval i200
--#eval i200.z.re.lo.abs.log
--#eval i200.z.re.hi.abs.log
--#eval i200.z.re.size.abs.log
--#eval i200.z.im.lo.abs.log
--#eval i200.z.im.hi.abs.log
#eval zs = nan ∨ 16 < zs ∨ 16 < cs
#eval Box.potential_small
#eval Box.potential_small.iter_sqrt i.n
#eval Box.potential_small.log
#eval Box.potential_small.log.scaleB' (-.ofNat0 n)
#eval Box.potential_small.log.lo.scaleB' (-.ofNat0 n)
#eval Box.potential_small.log.hi
#eval Box.potential_small.log.hi.scaleB' (-.ofNat0 n)
#eval Box.potential c c n r
-/
end debug

private def val (x y : ℚ) (n : ℕ) : Interval :=
  let c : Box := .ofRat (x,y)
  (Box.potential c c n 1000).1
private def close (x y : ℚ) (n : ℕ) (e : ℚ) : Bool := (val x y n).size.valq ≤ e
private def good (x y : ℚ) (n : ℕ) : Bool := val x y n ≠ nan
example : good 0 0 100 := by native_decide
example : good 0.1 0.2 100 := by native_decide
example : good (-21/160) (-133/160) 100 := by native_decide
example : good (-119/256) (-763/1280) 80 := by native_decide
example : good (-1393/1280) (-329/1280) 50 := by native_decide
example : close 0.285 0.01 100 9e-12 := by native_decide

private def dval (x y : ℚ) (n : ℕ) : DPotential :=
  let c : Box := .ofRat (x,y)
  Box.potential_deriv c c 1 1 n 1000
private def dclose (x y : ℚ) (n : ℕ) (e : ℚ) : Bool := (dval x y n).dp.size.valq ≤ e
example : dclose 0.285 0.01 100 1.63e-6 := by native_decide
