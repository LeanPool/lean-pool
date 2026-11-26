/-
Copyright (c) 2026 Lean Pool contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Pool contributors
-/
module

public import LeanPool.ConwaySoifer.Certificates.KernelReplay
meta import Mathlib.Tactic.FinCases  -- shake: keep

/-! Owner enumeration and pointwise extensionality for checkpoint replay. -/

public section

namespace ConwaySoifer.Certificates

/-- Check a predicate on each of the ten possible owners. -/
theorem forall_checkpoint_owners {predicate : Fin 10 → Prop}
    (owner0 : predicate 0) (owner1 : predicate 1) (owner2 : predicate 2)
    (owner3 : predicate 3) (owner4 : predicate 4) (owner5 : predicate 5)
    (owner6 : predicate 6) (owner7 : predicate 7) (owner8 : predicate 8)
    (owner9 : predicate 9) : ∀ owner, predicate owner := by
  intro owner
  fin_cases owner
  · exact owner0
  · exact owner1
  · exact owner2
  · exact owner3
  · exact owner4
  · exact owner5
  · exact owner6
  · exact owner7
  · exact owner8
  · exact owner9

/-- Reconstruct a model equality from the fields checked for each owner. -/
theorem Model.ext_checkpoint_owners (M N : Model)
    (fields : ∀ owner, M.B owner = N.B owner ∧
      M.caps owner = N.caps owner ∧ M.ord owner = N.ord owner) : M = N :=
  Model.ext_fields M N (fun owner => (fields owner).1)
    (fun owner => (fields owner).2.1) (fun owner => (fields owner).2.2)

end ConwaySoifer.Certificates
