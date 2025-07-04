import Lake
open Lake DSL

package «M2» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`pp.proofs.withType, false⟩
  ]
  -- add any additional package configuration options here

--require mathlib from git "https://github.com/leanprover-community/mathlib4.git"

require "leanprover-community" / "mathlib" @ git "v4.21.0"


@[default_target]
lean_lib «M2» where

  -- add any library configuration options here

require checkdecls from git "https://github.com/PatrickMassot/checkdecls.git" --@ "lean4.8.0"

--meta if get_config? env = some "dev" then
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "main"

--require "marcusrossel" / "egg" @ git "main"
