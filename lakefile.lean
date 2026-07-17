import Lake
open Lake DSL System

package «sodium» where

extern_lib libsodium pkg := do
  let libsodiumVersion := "1.0.20"
  let libsodiumUrl := s!"https://download.libsodium.org/libsodium/releases/libsodium-{libsodiumVersion}.tar.gz"
  let buildDir := pkg.buildDir / "libsodium-build"
  let srcDir := buildDir / s!"libsodium-{libsodiumVersion}"
  let staticLib := pkg.staticLibDir / "libsodium.a"
  let sharedLib := pkg.buildDir / "lib" / "libsodium.so"
  let tarFile := buildDir / s!"libsodium-{libsodiumVersion}.tar.gz"

  if !(← tarFile.pathExists) then
    logInfo s!"Downloading LibSodium {libsodiumVersion}..."
    IO.FS.createDirAll buildDir
    proc {
      cmd := "curl"
      args := #["-L", "-o", tarFile.toString, libsodiumUrl]
      cwd := buildDir
    }

  if !(← staticLib.pathExists) then
    logInfo "Building LibSodium from source..."
    IO.FS.createDirAll pkg.staticLibDir
    IO.FS.createDirAll (pkg.buildDir / "lib")

    if !(← srcDir.pathExists) then
      proc {
        cmd := "tar"
        args := #["-xzf", tarFile.toString]
        cwd := buildDir
      }

    let installDir := buildDir / "install"
    IO.FS.createDirAll installDir
    proc {
      cmd := "./configure"
      args := #[
        "--enable-shared=yes",
        "--enable-static=yes",
        "--disable-dependency-tracking",
        "--disable-ssp",
        s!"--prefix={installDir}",
        "CFLAGS=-fPIC -O2",
        "CPPFLAGS=-fPIC"
      ]
      cwd := srcDir
    }

    proc {
      cmd := "make"
      args := #["-j4"]
      cwd := srcDir
    }

    proc {
      cmd := "make"
      args := #["install"]
      cwd := srcDir
    }

    let builtStaticLib := installDir / "lib" / "libsodium.a"
    let builtSharedLib := installDir / "lib" / "libsodium.so"
    proc {
      cmd := "cp"
      args := #[builtStaticLib.toString, staticLib.toString]
    }
    proc {
      cmd := "cp"
      args := #[builtSharedLib.toString, sharedLib.toString]
    }

  pure (Job.pure staticLib)

def buildNativeO {n : Lean.Name} (pkg : NPackage n) (name : Lean.Name) : FetchM (Job FilePath) := do
  let oFile := pkg.buildDir / "c" / s!"{name}.o"
  let srcJob ← inputTextFile <| pkg.dir / "ffi" / s!"{name}.c"
  let weakArgs := #[
    "-I", (← getLeanIncludeDir).toString,
    "-I", (pkg.dir / "ffi").toString,
    "-I", (pkg.dir / ".lake" / "build" / "libsodium-build" / "install" / "include").toString
  ]
  buildO oFile srcJob weakArgs #["-fPIC"] "cc" getLeanTrace

target basic.o pkg : FilePath := buildNativeO pkg `basic
target aead.o pkg : FilePath := buildNativeO pkg `aead
target core.o pkg : FilePath := buildNativeO pkg `core
target curve25519.o pkg : FilePath := buildNativeO pkg `curve25519
target generichash.o pkg : FilePath := buildNativeO pkg `generichash
target kdf.o pkg : FilePath := buildNativeO pkg `kdf
target ristretto255.o pkg : FilePath := buildNativeO pkg `ristretto255

extern_lib lean_sodium_ffi pkg := do
  let name := nameToStaticLib "ffi"
  buildStaticLib (pkg.staticLibDir / name) #[
    ← basic.o.fetch,
    ← aead.o.fetch,
    ← core.o.fetch,
    ← curve25519.o.fetch,
    ← generichash.o.fetch,
    ← kdf.o.fetch,
    ← ristretto255.o.fetch
  ]

@[default_target]
lean_lib «Sodium» where
  precompileModules := true
  moreLeancArgs := #["-fPIC"]
  weakLeancArgs := #[s!"-I{__dir__}/.lake/build/libsodium-build/install/include"]
  moreLinkArgs := #[s!"-L{__dir__}/.lake/build/lib", "-lsodium"]

@[default_target, test_driver]
lean_exe «SodiumTest» where
  supportInterpreter := true
  moreLeancArgs := #["-fPIC"]
  weakLeancArgs := #[s!"-I{__dir__}/.lake/build/libsodium-build/install/include"]
  moreLinkArgs := #[s!"-L{__dir__}/.lake/build/lib", "-lsodium"]
