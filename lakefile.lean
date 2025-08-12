import Lake
open Lake DSL

package render where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`linter.docPrime, false⟩,
    ⟨`autoImplicit, false⟩
  ]

require "leanprover-community" / "mathlib" @ git "master"
require "girving" / "interval" @ git "main"
require "girving" / "ray" @ git "main"

@[default_target]
lean_lib Render

@[default_target]
lean_exe gradient_test {
  root := `Render.GradientTest
  moreLinkArgs := #["-L/opt/homebrew/lib", "-lpng"]
}

@[default_target]
lean_exe bad_mandelbrot {
  root := `Render.BadMandelbrot
  moreLinkArgs := #["-L/opt/homebrew/lib", "-lpng"]
}

@[default_target]
lean_exe primes {
  root := `Render.Primes
}

target png.o pkg : System.FilePath := do
  let o := pkg.buildDir / "Render/png.o"
  let src ← inputTextFile <| pkg.dir / "Render/png.cc"
  let args := #["-I", (←getLeanIncludeDir).toString, "-I/opt/homebrew/include"]
  buildO o src args #["-fPIC"] "c++" getLeanTrace

extern_lib libray pkg := do
  let name := nameToStaticLib "ray"
  let png ← fetch <| pkg.target ``png.o
  buildStaticLib (pkg.staticLibDir / name) #[png]
