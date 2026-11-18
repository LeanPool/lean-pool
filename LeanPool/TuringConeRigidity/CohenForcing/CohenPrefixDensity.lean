/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/CohenForcing/CohenPrefixDensity.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.CohenForcing.CohenGroundPoset
public import LeanPool.TuringConeRigidity.SetModels.InternalDenseInclusion

/-!
# Cohen Prefix Density
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.CohenPrefixDensity
open TransitiveNameModel BoundedSetTheory InternalCohen CohenConditionCode InternalFiniteSubsets
attribute [local instance] InternalCollapse.order

theorem word_isCondition (s : List Bool) : IsCondition ZFSet.omega (wordCode s) := by
  refine ⟨(mem_finiteSubsets_iff _ _).mpr ⟨?_,?_⟩,?_⟩
  · intro z hz
    obtain ⟨i,rfl⟩ := (mem_wordCode s z).mp hz
    exact ZFSet.pair_mem_prod.mpr ⟨(mem_omega _).mpr ⟨i.val,rfl⟩,
      (mem_alphabet _).mpr ⟨_,rfl⟩⟩
  · rw [wordCode,ZFSet.coe_range]; exact Set.finite_range _
  · intro x _ b _ c _ hxb hxc
    obtain ⟨i,hi⟩ := (mem_wordCode s _).mp hxb
    have hxn := (ZFSet.pair_inj.mp hi).1
    exact (wordCode_function s).functional
      (hxn.symm ▸ (natSet_mem_natSet _ _).mpr i.isLt) hxb hxc

theorem conditions_subset : InternalCohen.conditions ⊆ CohenGroundPoset.conditions ZFSet.omega := by
  intro p hp
  obtain ⟨s,rfl⟩ := (prefix_iff_wordCode p).mp ((mem_conditions p).mp hp)
  exact (CohenGroundPoset.mem_conditions _ _).mpr (word_isCondition s)

theorem condition_extends_prefix (q : ZFSet.{0})
    (hq : q ∈ CohenGroundPoset.conditions ZFSet.omega) :
    ∃ s : List Bool, q ⊆ wordCode s := by
  classical
  obtain ⟨p,rfl⟩ := (isCondition_iff_graph _ q).mp ((CohenGroundPoset.mem_conditions _ _).mp hq)
  let f (n : ℕ) : Conditions ZFSet.omega :=
    equivShrink _ ⟨natSet n,(mem_omega _).mpr ⟨n,rfl⟩⟩
  have hfl (n : ℕ) : label ZFSet.omega (f n) = natSet n := by simp [f,label]
  have hfi : Function.Injective f := by
    intro n m h
    exact natSet_injective (by simpa only [hfl] using congrArg (label ZFSet.omega) h)
  have hfin := p.finite.preimage hfi.injOn
  obtain ⟨n,hn⟩ := hfin.bddAbove
  let s := List.ofFn (fun i : Fin (n+1) => (p.val (f i.val)).getD false)
  refine ⟨s,?_⟩
  intro z hz
  obtain ⟨i,b,hib,rfl⟩ := (mem_graph _ p z).mp hz
  obtain ⟨k,hk⟩ := (mem_omega _).mp (label_mem ZFSet.omega i)
  have he : i = f k := label_injective _ (hk.trans (hfl k).symm)
  have hkb : p.val (f k) = some b := he ▸ hib
  have hkn : k < n+1 := Nat.lt_succ_of_le (hn (by
    change p.val (f k) ≠ none
    simp [hkb]))
  rw [he,hfl]
  apply (pair_mem_wordCode s k b).mpr
  refine ⟨by simpa only [s,List.length_ofFn] using hkn,?_⟩
  simp only [s,List.getElem_ofFn,hkb,Option.getD_some]

theorem dense_inclusion : ∀ q ∈ CohenGroundPoset.conditions ZFSet.omega,
    ∃ p ∈ InternalCohen.conditions, q ⊆ p := by
  intro q hq
  obtain ⟨s,hs⟩ := condition_extends_prefix q hq
  exact ⟨wordCode s,(mem_conditions _).mpr ⟨s.length,wordCode_function s⟩,hs⟩

theorem internal_dense_inclusion (M : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M) :
    InternalCohen.conditions ∈ M ∧ CohenGroundPoset.conditions ZFSet.omega ∈ M ∧
      InternalDenseInclusion.inclusionGraph InternalCohen.conditions
        (CohenGroundPoset.conditions ZFSet.omega) ∈ M ∧
      FunctionGraph InternalCohen.conditions (CohenGroundPoset.conditions ZFSet.omega)
        (InternalDenseInclusion.inclusionGraph InternalCohen.conditions
          (CohenGroundPoset.conditions ZFSet.omega)) ∧
      ∀ q ∈ CohenGroundPoset.conditions ZFSet.omega, ∃ p ∈ InternalCohen.conditions, q ⊆ p := by
  have ha := InternalCohen.conditions_mem M hM hT
  have hb := CohenGroundPoset.conditions_mem M ZFSet.omega hM hT (sourceT_omega_mem M hM hT)
  exact ⟨ha,hb,InternalDenseInclusion.inclusionGraph_mem M _ _ hM hT ha hb,
    InternalDenseInclusion.inclusionGraph_function _ _ conditions_subset,dense_inclusion⟩

end TuringRigidity.CohenPrefixDensity

end OAI
