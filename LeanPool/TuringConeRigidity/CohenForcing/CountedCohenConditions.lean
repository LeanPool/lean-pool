/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/CohenForcing/CountedCohenConditions.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.InternalCountableProduct
public import LeanPool.TuringConeRigidity.CohenForcing.CohenGroundPoset
public import LeanPool.TuringConeRigidity.SetModels.InternalCountableClosure

/-!
# Counted Cohen Conditions
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.CountedCohenConditions
open TransitiveNameModel BoundedSetTheory InternalFiniteSubsets InternalFiniteExhaustion
open InternalCountableProduct InternalCountableClosure CohenGroundPoset

theorem finite_subsets_countable_or_empty (M A : ZFSet.{0})
    (hM : Transitive M) (hT : SourceT M) (hA : A ∈ M)
    (hct : A = ∅ ∨ InternallyCountable M A) :
    InternallyCountable M (finiteSubsets A) := by
  rcases hct with rfl|hct
  · apply finite_countable M _ hM hT (finiteSubsets_mem M ∅ hM hT hA)
      (finite_subsets_finite ∅ (by simpa only [ZFSet.coe_empty] using Set.finite_empty))
    exact ⟨∅,(mem_finiteSubsets_iff ∅ ∅).mpr
      ⟨ZFSet.empty_subset ∅,by simpa only [ZFSet.coe_empty] using Set.finite_empty⟩⟩
  · exact finite_subsets_countable M A hM hT hA hct

theorem empty_condition (A : ZFSet.{0}) : ∅ ∈ conditions A := by
  apply (mem_conditions A ∅).mpr
  refine ⟨(mem_finiteSubsets_iff _ ∅).mpr
    ⟨ZFSet.empty_subset _,by simpa only [ZFSet.coe_empty] using Set.finite_empty⟩,?_⟩
  intro x _ b _ c _ hb
  exact False.elim (ZFSet.notMem_empty _ hb)

theorem alphabet_countable (M : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M) :
    InternallyCountable M InternalCohen.alphabet := by
  apply finite_countable M _ hM hT (InternalCohen.alphabet_mem M hM hT)
  · have he : (InternalCohen.alphabet : Set ZFSet.{0}) = Set.range InternalCohen.bitSet := by
      ext x
      exact (InternalCohen.mem_alphabet x).trans ⟨fun ⟨b,hb⟩ => ⟨b,hb.symm⟩,
        fun ⟨b,hb⟩ => ⟨b,hb.symm⟩⟩
    rw [he]
    exact Set.finite_range _
  · exact ⟨InternalCohen.bitSet false,(InternalCohen.mem_alphabet _).mpr ⟨false,rfl⟩⟩

theorem conditions_countable (M A : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hA : A ∈ M) (hct : A = ∅ ∨ InternallyCountable M A) :
    InternallyCountable M (conditions A) := by
  have hB := InternalCohen.alphabet_mem M hM hT
  have hP := product_mem M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hA hB
  have hpc := product_countable_or_empty M A InternalCohen.alphabet hM hT hA hB
    hct (Or.inr (alphabet_countable M hM hT))
  have hfc := finite_subsets_countable_or_empty M _ hM hT hP hpc
  exact countable_subset M _ _ hM hT (finiteSubsets_mem M _ hM hT hP)
    (conditions_mem M A hM hT hA) (fun _ hp => ((mem_conditions A _).mp hp).1)
    hfc ⟨∅,empty_condition A⟩

theorem many_column_conditions_countable (M C : ZFSet.{0})
    (hM : Transitive M) (hT : SourceT M) (hC : C ∈ M)
    (hct : C = ∅ ∨ InternallyCountable M C) :
    InternallyCountable M (conditions (ZFSet.prod C ZFSet.omega)) := by
  have hω := sourceT_omega_mem M hM hT
  exact conditions_countable M _ hM hT
    (product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded hC hω)
    (product_countable_or_empty M C ZFSet.omega hM hT hC hω hct
      (Or.inr (omega_countable M hM hT)))

end TuringRigidity.CountedCohenConditions

end OAI
