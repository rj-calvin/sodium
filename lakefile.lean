import Lake
open Lake DSL System

require alloy from git "https://github.com/tydeu/lean4-alloy.git"@"master"
require "leanprover-community" / "batteries" @ git "v4.21.0"

package «sodium» where

module_data alloy.c.o.export : FilePath
module_data alloy.c.o.noexport : FilePath

-- Download and build LibSodium from source as both static and shared libraries
-- Build shared first, then create static lib that Lake can use without TLS conversion
extern_lib libsodium pkg := do
  let libsodiumVersion := "1.0.20"
  let libsodiumUrl := s!"https://download.libsodium.org/libsodium/releases/libsodium-{libsodiumVersion}.tar.gz"
  let buildDir := pkg.buildDir / "libsodium-build"
  let srcDir := buildDir / s!"libsodium-{libsodiumVersion}"
  let staticLib := pkg.staticLibDir / "libsodium.a"
  let sharedLib := pkg.buildDir / "lib" / "libsodium.so"
  let tarFile := buildDir / s!"libsodium-{libsodiumVersion}.tar.gz"

  -- Download source if not present
  if !(← tarFile.pathExists) then
    logInfo s!"Downloading LibSodium {libsodiumVersion}..."
    IO.FS.createDirAll buildDir
    proc {
      cmd := "curl"
      args := #["-L", "-o", tarFile.toString, libsodiumUrl]
      cwd := buildDir
    }

  -- Extract and build
  if !(← staticLib.pathExists) then
    logInfo "Building LibSodium from source..."
    IO.FS.createDirAll pkg.staticLibDir
    IO.FS.createDirAll (pkg.buildDir / "lib")

    -- Extract
    if !(← srcDir.pathExists) then
      proc {
        cmd := "tar"
        args := #["-xzf", tarFile.toString]
        cwd := buildDir
      }

    -- Configure with both shared and static libraries
    let installDir := buildDir / "install"
    IO.FS.createDirAll installDir
    proc {
      cmd := "./configure"
      args := #[
        "--enable-shared=yes",          -- Build shared library
        "--enable-static=yes",          -- Also build static
        "--disable-dependency-tracking", -- Faster build
        "--disable-ssp",                -- Compatibility
        s!"--prefix={installDir}",      -- Install location
        "CFLAGS=-fPIC -O2 -g",          -- Position independent code + debug symbols
        "CPPFLAGS=-fPIC"                -- PIC for preprocessor
      ]
      cwd := srcDir
    }

    -- Build with parallel jobs
    proc {
      cmd := "make"
      args := #["-j4"]
      cwd := srcDir
    }

    -- Install to our build directory
    proc {
      cmd := "make"
      args := #["install"]
      cwd := srcDir
    }

    -- Copy both libraries
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

@[default_target]
lean_lib «Sodium» where
  precompileModules := true
  nativeFacets := fun shouldExport =>
    if shouldExport then
      #[Module.oExportFacet, `module.alloy.c.o.export]
    else
      #[Module.oNoExportFacet, `module.alloy.c.o.noexport]

lean_lib Tests where
  roots := #[`Tests, `Sodium]
  precompileModules := true
  nativeFacets := fun shouldExport =>
    if shouldExport then
      #[Module.oExportFacet, `module.alloy.c.o.export]
    else
      #[Module.oNoExportFacet, `module.alloy.c.o.noexport]
  moreLeancArgs := #["-g", "-O0"]  -- Debug symbols, no optimization
