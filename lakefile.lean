import Lake
open Lake DSL

package render where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`linter.docPrime, false⟩,
    ⟨`autoImplicit, false⟩
  ]
  testDriver := "RenderTest"

require "leanprover-community" / "mathlib" @ git "master"
require "girving" / "interval" @ git "main"
require "girving" / "ray" @ git "main"

@[default_target]
lean_lib Render

@[default_target]
lean_lib Correct

@[default_target]
lean_lib RenderTest where
  globs := #[.submodules `test]

def run (cmd : String) (args : Array String) (cwd : Option System.FilePath := none) : IO Unit := do
  let _ ← IO.Process.output { cmd := cmd, args := args, cwd := cwd }

-- Helper function to build external libraries with common download/build pattern
def buildDep (pkg : Package) (name : String) (url : String) (libPath : System.FilePath)
    (configureArgs : Array String := #[]) : IO (Job System.FilePath) := do
  let depPath := pkg.buildDir / "deps"
  let srcPath := depPath / name
  let tarFile := depPath / (name ++ ".tar.gz")
  -- Return if already built
  if ← libPath.pathExists then return (pure libPath : Job _)
  -- Download and extract
  if !(← tarFile.pathExists) then
    IO.FS.createDirAll depPath
    run "curl" #["-L", "-o", tarFile.toString, url]
    run "tar" #["-xzf", tarFile.toString, "-C", depPath.toString]
  -- Build library
  run "./configure" (configureArgs ++ #["--prefix=" ++ srcPath.toString]) srcPath
  run "make" #["-j"] srcPath
  run "make" #["install"] srcPath
  return (pure libPath : Job _)

-- Download and build zlib
def zlibName := "zlib-1.3.1"
target zlib pkg : System.FilePath := do
  let depPath := pkg.buildDir / "deps"
  let zlibPath := depPath / zlibName
  let zlibLib := zlibPath / "libz.a"
  buildDep pkg zlibName "https://zlib.net/zlib-1.3.1.tar.gz" zlibLib #["--static"]

-- Download and build libpng
def libpngName := "libpng-1.6.50"
target libpng pkg : System.FilePath := do
  let depPath := pkg.buildDir / "deps"
  let libpngPath := depPath / libpngName
  let libpngLib := libpngPath / ".libs" / "libpng16.a"
  let zlibPath := depPath / zlibName
  let _ ← fetch <| pkg.target ``zlib  -- Ensure zlib is built first
  let configureArgs := #["--enable-static", "--disable-shared",
                        s!"--with-zlib-prefix={zlibPath}",
                        s!"CPPFLAGS=-I{zlibPath}/include",
                        s!"LDFLAGS=-L{zlibPath}/lib"]
  buildDep pkg libpngName "https://download.sourceforge.net/libpng/libpng-1.6.50.tar.gz"
    libpngLib configureArgs

def deps := #[``libpng, ``zlib]
def linkArgs :=
  #[".lake/build/deps/libpng-1.6.50/.libs/libpng16.a", ".lake/build/deps/zlib-1.3.1/libz.a"]

@[default_target]
lean_exe gradient_test {
  root := `Render.GradientTest
  extraDepTargets := deps
  moreLinkArgs := linkArgs
}

@[default_target]
lean_exe bad_mandelbrot {
  root := `Render.BadMandelbrot
  extraDepTargets := deps
  moreLinkArgs := linkArgs
}

@[default_target]
lean_exe primes {
  root := `Render.Primes
}

target png.o pkg : System.FilePath := do
  let o := pkg.buildDir / "Render/png.o"
  let src ← inputTextFile <| pkg.dir / "Render/png.cc"
  let depPath := pkg.buildDir / "deps"
  let zlibPath := depPath / zlibName
  let libpngPath := depPath / libpngName

  -- Ensure both libraries are built first
  let _ ← fetch <| pkg.target ``zlib
  let _ ← fetch <| pkg.target ``libpng

  let args := #["-I", (← getLeanIncludeDir).toString,
                "-I" ++ (libpngPath / "include").toString,
                "-I" ++ (zlibPath / "include").toString]
  buildO o src args #["-fPIC"] "c++" getLeanTrace

extern_lib libray pkg := do
  let name := nameToStaticLib "ray"
  let png ← fetch <| pkg.target ``png.o
  buildStaticLib (pkg.staticLibDir / name) #[png]
