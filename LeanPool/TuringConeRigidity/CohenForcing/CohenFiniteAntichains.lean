/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/CohenForcing/CohenFiniteAntichains.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.CohenForcing.CohenNiceNames

/-!
# Cohen Finite Antichains
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.CohenFiniteAntichains
open Set CohenSymmetry CohenCoordinates CohenChainCondition CohenNiceNames
universe u
variable {ι : Type u}

theorem finite_extension (U V E : Set (Condition ι)) (hVU : V ⊆ U)
    (hEU : E ⊆ U) (hE : Antichain E) (hfin : E.Finite)
    (n : ℕ) (hn : ∀ p ∈ V, (support p).card ≤ n) :
    ∃ F, F.Finite ∧ E ⊆ F ∧ F ⊆ U ∧ Antichain F ∧
      ∀ p ∈ V, ∃ q ∈ F, Compatible p q := by
  classical
  let W := {p ∈ V | ∀ q ∈ E, ¬ Compatible p q}
  obtain ⟨B,hBW,hB,_,hpred⟩ := countable_predense_antichain W
  have hBfin : B.Finite := bounded_antichain_finite n B hB
    (fun p hp => hn p (hBW hp).1)
  refine ⟨E ∪ B,hfin.union hBfin,Set.subset_union_left,
    Set.union_subset hEU (fun p hp => hVU (hBW hp).1),?_,?_⟩
  · intro p hp q hq hpq
    rcases hp with hp|hp <;> rcases hq with hq|hq
    · exact hE hp hq hpq
    · exact fun hc => (hBW hq).2 p hp (compatible_symm hc)
    · exact (hBW hp).2 q hq
    · exact hB hp hq hpq
  · intro p hp
    by_cases he : ∃ q ∈ E, Compatible p q
    · obtain ⟨q,hq,hpq⟩ := he; exact ⟨q,Or.inl hq,hpq⟩
    · obtain ⟨q,hq,hpq⟩ := hpred p ⟨hp,fun q hq hc => he ⟨q,hq,hc⟩⟩
      exact ⟨q,Or.inr hq,hpq⟩

end TuringRigidity.CohenFiniteAntichains

end OAI
