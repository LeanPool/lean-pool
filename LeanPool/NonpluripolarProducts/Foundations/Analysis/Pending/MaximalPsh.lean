/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.MongeAmpere

/-!
# Maximal plurisubharmonic functions

A plurisubharmonic function `u` on an open set `Ω ⊆ ℂⁿ` is *maximal* if every
plurisubharmonic `v` on `Ω` with `v ≤ u` outside a compact subset of `Ω` satisfies
`v ≤ u` on `Ω` (Sadullaev; Błocki, *The complex Monge–Ampère operator in pluripotential
theory*, lecture notes, §1.4). For locally bounded functions this is equivalent to the
vanishing of the Monge–Ampère measure (Bedford–Taylor; Błocki, Thm 2.3.1).
-/

@[expose] public section

noncomputable section

open Set TopologicalSpace

namespace SGPT.Foundations.Analysis.Pending.BedfordTaylor

open FirstPass FirstPass.MongeAmpere

variable {n : ℕ}

/-- `u` is a maximal plurisubharmonic function on `Ω`: real-valued plurisubharmonic
competitors lying below `u` off a compact subset of `Ω` lie below `u` on all of `Ω`. -/
def IsMaximalPshOn (Ω : Opens (ComplexModel n)) (u : ComplexModel n → ℝ) : Prop :=
  PlurisubharmonicOn (fun z => (u z : EReal)) Ω ∧
    ∀ v : ComplexModel n → ℝ, PlurisubharmonicOn (fun z => (v z : EReal)) Ω →
      ∀ K : Set (ComplexModel n), IsCompact K → K ⊆ Ω →
        (∀ z ∈ (Ω : Set (ComplexModel n)) \ K, v z ≤ u z) →
        ∀ z ∈ Ω, v z ≤ u z

end SGPT.Foundations.Analysis.Pending.BedfordTaylor

end
