import Render.Area

/-!
## Area computations with optional traces
-/

def parseNat (name s : String) : IO ℕ :=
  match s.toNat? with
  | some n => pure n
  | none => throw (IO.userError ("Invalid " ++ name ++ ": " ++ s ++ ", expected ℕ"))

def main (args : List String) : IO Unit := do
  let (trace, d, n) ← match args with
    | ["-t", t, d, n] => pure (some t, d, n)
    | [d, n] => pure (none, d, n)
    | _ => throw (IO.userError "Usage: area [-t] <depth> <iterations>")
  let d ← parseNat "depth" d
  let n ← parseNat "iterations" n
  let print := fun a : Dyadic ↦ IO.println ("area ≤ " ++ repr a ++ " (" ++ repr a.toFloat ++ ")")
  match trace with
  | none =>
    let a := upper_area d n
    print a
  | some path =>
    let (a, t) := upper_area_sample d n
    print a
    IO.println ("Writing trace to " ++ path)
    IO.FS.writeFile path (Lean.toJson t).compress
