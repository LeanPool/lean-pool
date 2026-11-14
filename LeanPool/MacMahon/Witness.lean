/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
-- Modified for Lean Pool integration.
module

public import LeanPool.MacMahon.Partitions
public import LeanPool.MacMahon.WitnessData

/-!
# Sufficiency of the ten candidate inventories
-/

@[expose] public section
namespace MacMahon
theorem witness_facts : ∀ b : Fin 10, ∀ i j : Label, i ≠ j →
    Function.Injective (witness b i j) ∧ ∀ k : Slot,
      winner b (witness b i j k) = 1 ∧
      HasCorner (witness b i j k) (cornerAt i j k) := by decide +kernel

/-- Every known set has an explicit eight-cube construction for every target. -/
theorem winner_universal (b : Fin 10) : Universal (winner b) := by
  intro i j hij
  obtain ⟨hinj, hfit⟩ := witness_facts b i j hij
  let f : Slot → Stock (winner b) := fun k =>
    ⟨witness b i j k, ⟨0, by rw [(hfit k).1]; decide⟩⟩
  refine ⟨⟨f, ?_⟩, fun k => (hfit k).2⟩
  intro k l heq
  exact hinj (congrArg Sigma.fst heq)

end MacMahon
