/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/InternalHartogs.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.CollapseCoding
public import LeanPool.TuringConeRigidity.OrdinalCodes.RankOrdinal

/-!
# Internal Hartogs
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.RelationCollapse
open TransitiveNameModel BoundedSetTheory InternalRank
universe u

theorem internal_hartogs (M d : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : SigmaSeparation M) (hR : SigmaReplacement M) (hI : Infinity M) (hd : d ∈ M) :
    ∃ α ∈ M, α.IsOrdinal ∧ ∀ f ∈ M, ∀ j : ZFSet.{u} → ZFSet.{u},
      Presents α f j → (∀ x ∈ α, j x ∈ d) →
      ¬ (∀ x ∈ α, ∀ y ∈ α, j x = j y → x = y) := by
  obtain ⟨W,hW,hbound⟩ := internal_small_transitive_bound M d hM hP hU hPow hS hR hd
  let k := rankSet W
  have hk : k ∈ M := rankSet_mem_ground M hM hP hU hPow hS.bounded hR hI hW
  have hko : k.IsOrdinal := rankSet_isOrdinal W
  let α := insert k k
  have hα : α ∈ M := by
    have eq : α = ({k} : ZFSet.{u}) ∪ k := by
      apply ZFSet.ext
      intro z
      simp only [α,ZFSet.mem_insert_iff,ZFSet.mem_union,ZFSet.mem_singleton]
    rw [eq]
    exact binary_union_mem M hM hP hU (singleton_mem M hM hP hk) hk
  have hαo : α.IsOrdinal := ZFSet.isOrdinal_succ hko
  refine ⟨α,hα,hαo,?_⟩
  intro f hf j hfj hj hi
  have hαt : Transitive α := fun x hx y hy => hαo.subset_of_mem hx hy
  have hsub := hbound α hα hαt f hf j hfj hj hi
  have hkw : k ∈ W := hsub (ZFSet.mem_insert_iff.mpr (Or.inl rfl))
  have hlt := ZFSet.rank_lt_of_mem hkw
  have heq : k.rank = W.rank := by
    rw [show k = W.rank.toZFSet from rankSet_eq_ordinal W,Ordinal.rank_toZFSet]
  exact (lt_irrefl W.rank) (heq ▸ hlt)

end TuringRigidity.RelationCollapse

end OAI
