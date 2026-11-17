/-
Copyright (c) 2026 Umang Mathur. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Umang Mathur
-/

module

public import LeanPool.Parikh.Activation
import LeanPool.Parikh.GrammarImage

/-! Ported from focs-lab/parikh-theorem at
`9c1cde93f29bbaa91542e401e074ec3cd7646880`; module headers and import paths
adapted for Lean Pool. -/

public section

/-!
# A witness from finite tree families

List one component for each base and activatable subset of bounded contexts.
The periods keep context identities as separate list positions, even when
their weights coincide or vanish. This classical assembly supports the
quantitative existence theorem; executable compilation is a separate task.

Source: `eq:main`, `thm:size-bound`.
-/
namespace Parikh
variable {T : Type*} [DecidableEq T]

/-- Assemble the exact tree formula from finite base and context families. -/
@[expose] noncomputable def familyWitness (g : ContextFreeGrammar T)
    (bases cycles : Finset (ParseTree T g.NT)) : Witness T := by
  classical
  exact ((bases ×ˢ cycles.powerset).filter fun pair =>
    ContextsActivatable g pair.1 pair.2).toList.map fun pair => contextComponent pair.1 pair.2

/-- Component membership retains both its base tree and its selected context subset. -/
theorem mem_familyWitness (g : ContextFreeGrammar T)
    (bases cycles : Finset (ParseTree T g.NT)) (c : Component T) :
    c ∈ familyWitness g bases cycles ↔
      ∃ B ∈ bases, ∃ D : Finset (ParseTree T g.NT),
        D ⊆ cycles ∧ ContextsActivatable g B D ∧ contextComponent B D = c := by
  classical
  simp only [familyWitness, List.mem_map, Finset.mem_toList, Finset.mem_filter,
    Finset.mem_product, Finset.mem_powerset, Prod.exists]
  constructor
  · rintro ⟨B, D, ⟨⟨hB, hD⟩, ha⟩, hc⟩
    exact ⟨B, hB, D, hD, ha, hc⟩
  · rintro ⟨B, hB, D, hD, ha, hc⟩
    exact ⟨B, D, ⟨⟨hB, hD⟩, ha⟩, hc⟩

/-- Activation filtering cannot exceed the number of base/subset pairs. -/
theorem familyWitness_length_le (g : ContextFreeGrammar T)
    (bases cycles : Finset (ParseTree T g.NT)) :
    (familyWitness g bases cycles).length ≤ bases.card * 2 ^ cycles.card := by
  classical
  simpa only [familyWitness, List.length_map, Finset.length_toList,
    Finset.card_product, Finset.card_powerset] using
    Finset.card_filter_le (bases ×ˢ cycles.powerset)
      (fun pair => ContextsActivatable g pair.1 pair.2)

/-- Exact base and cycle families give exactly the grammar's Parikh image. -/
theorem familyWitness_denotation [Finite T] (g : ContextFreeGrammar T)
    (bases cycles : Finset (ParseTree T g.NT))
    (hb : ∀ B, B ∈ bases ↔ IsBase g B)
    (hc : ∀ C, C ∈ cycles ↔ IsBoundedCycle g C) :
    (familyWitness g bases cycles).denotation = image g.language := by
  classical
  rw [← (treeRepresentation_correct g).1]
  ext v
  constructor
  · rintro ⟨c, hmem, hv⟩
    obtain ⟨B, hB, D, hD, ha, rfl⟩ := (mem_familyWitness g bases cycles c).mp hmem
    exact ⟨B, D, (hb B).mp hB, fun C hC => (hc C).mp (hD hC), ha, hv⟩
  · rintro ⟨B, D, hB, hD, ha, hv⟩
    refine ⟨contextComponent B D, ?_, hv⟩
    exact (mem_familyWitness g bases cycles _).mpr
      ⟨B, (hb B).mpr hB, D, fun C hC => (hc C).mpr (hD C hC), ha, rfl⟩

end Parikh
