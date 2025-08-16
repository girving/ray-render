import Render.Image

/-!
## Write .png images via libpng
-/

@[extern "write_png"]
opaque write_png_helper (path : String) (width height : UInt32) (data : ByteArray) : IO String

def Image.write_png (path : String) (i : Image) : IO Unit := do
  match ← write_png_helper path (.ofNat i.width) (.ofNat i.height) i.data with
  | "" => pure ()
  | error => throw (IO.userError error)
