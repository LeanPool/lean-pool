/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/CohenForcing/InternalCohenFilters.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.CohenForcing.InternalCohenConditions
public import LeanPool.TuringConeRigidity.SetModels.InternalCollapseDense
public import LeanPool.TuringConeRigidity.CohenForcing.CohenRecursiveName

/-!
# Internal Cohen Filters
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.InternalCohen
open TransitiveNameModel BoundedSetTheory InternalCollapse CohenBorelForcing CountableForcing
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

noncomputable instance cohenTop : OrderTop (Conditions conditions) :=
  InternalCollapse.top conditions ((mem_conditions _).mpr (prefix_empty alphabet))

theorem label_top : label conditions (⊤ : Conditions conditions) = ∅ := by
  have h : label conditions (⊤ : Conditions conditions) ⊆ wordCode [] := by
    have hh : encodeCondition ⟨[]⟩ ≤ (⊤ : Conditions conditions) := le_top
    change label conditions ⊤ ⊆ label conditions (encodeCondition ⟨[]⟩) at hh
    simpa only [label_encodeCondition] using hh
  apply ZFSet.ext; intro z
  constructor
  · intro hz
    obtain ⟨i,_⟩ := (mem_wordCode [] z).mp (h hz)
    exact False.elim (Nat.not_lt_zero _ i.isLt)
  · exact fun hz => False.elim (ZFSet.notMem_empty z hz)

theorem conditionEquiv_top : conditionEquiv (⊤ : Condition) = ⊤ := conditionEquiv.map_top

/-- Pull a filter on set-coded conditions back to word conditions. -/
noncomputable def pullFilter (G : GenericFilter (Conditions conditions)) : GenericFilter Condition
  where
  carrier := {p | conditionEquiv p ∈ G.carrier}
  nonempty := by obtain ⟨q,hq⟩ := G.nonempty; exact ⟨conditionEquiv.symm q,by simpa using hq⟩
  upper := fun h hp => G.upper (conditionEquiv.monotone h) hp
  directed := by
    intro p q hp hq
    obtain ⟨r,hr,hrp,hrq⟩ := G.directed hp hq
    exact ⟨conditionEquiv.symm r,by simpa using hr,
      by simpa using conditionEquiv.symm.monotone hrp,
      by simpa using conditionEquiv.symm.monotone hrq⟩

/-- Push a filter on word conditions forward to set-coded conditions. -/
noncomputable def pushFilter (G : GenericFilter Condition) : GenericFilter (Conditions conditions)
  where
  carrier := {p | conditionEquiv.symm p ∈ G.carrier}
  nonempty := by obtain ⟨q,hq⟩ := G.nonempty; exact ⟨conditionEquiv q,by simpa using hq⟩
  upper := fun h hp => G.upper (conditionEquiv.symm.monotone h) hp
  directed := by
    intro p q hp hq
    obtain ⟨r,hr,hrp,hrq⟩ := G.directed hp hq
    exact ⟨conditionEquiv r,by simpa using hr,
      by simpa using conditionEquiv.monotone hrp,
      by simpa using conditionEquiv.monotone hrq⟩

theorem filter_ext {P : Type*} [Preorder P] (F H : GenericFilter P)
    (h : F.carrier = H.carrier) : F = H := by
  cases F; cases H; cases h; rfl

theorem pull_push (G : GenericFilter Condition) : pullFilter (pushFilter G) = G := by
  have he : (pullFilter (pushFilter G)).carrier = G.carrier := by
    ext p; simp [pullFilter,pushFilter]
  exact filter_ext _ _ he

theorem push_pull (G : GenericFilter (Conditions conditions)) : pushFilter (pullFilter G) = G := by
  have he : (pushFilter (pullFilter G)).carrier = G.carrier := by
    ext p; simp [pullFilter,pushFilter]
  exact filter_ext _ _ he

theorem dense_pull_iff (D : Set (Conditions conditions)) :
    Dense {p : Condition | conditionEquiv p ∈ D} ↔ Dense D := by
  constructor
  · intro h q
    obtain ⟨p,hp,hpD⟩ := h (conditionEquiv.symm q)
    exact ⟨conditionEquiv p,by simpa using conditionEquiv.monotone hp,hpD⟩
  · intro h q
    obtain ⟨p,hp,hpD⟩ := h (conditionEquiv q)
    exact ⟨conditionEquiv.symm p,by simpa using conditionEquiv.symm.monotone hp,
      by simpa using hpD⟩

theorem groundGeneric_iff (M : ZFSet.{0}) (G : GenericFilter (Conditions conditions)) :
    AtomicForcing.GroundGeneric M G ↔
      ∀ D ∈ M, Dense {p : Condition | wordCode p.word ∈ D} →
        ∃ p ∈ (pullFilter G).carrier, wordCode p.word ∈ D := by
  have hl (p : Condition) : label conditions (conditionEquiv p) = wordCode p.word :=
    label_encodeCondition p
  constructor
  · intro h D hD hd
    have hd' := (dense_pull_iff {p | label conditions p ∈ D}).mp (by simpa only
      [Set.mem_ofPred_eq, hl] using hd)
    obtain ⟨q,hq,hqD⟩ := h D hD hd'
    refine ⟨conditionEquiv.symm q,by simpa [pullFilter] using hq,?_⟩
    simpa only [←hl,OrderIso.apply_symm_apply] using hqD
  · intro h D hD hd
    have hd' := (dense_pull_iff {p | label conditions p ∈ D}).mpr hd
    obtain ⟨q,hq,hqD⟩ := h D hD (by simpa only [Set.mem_ofPred_eq,hl] using hd')
    exact ⟨conditionEquiv q,hq,by simpa only [hl] using hqD⟩

theorem groundGeneric_long (M : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (G : GenericFilter (Conditions conditions)) (hG : AtomicForcing.GroundGeneric M G) :
    GenericFor CohenFilterReal.Long (pullFilter G) := by
  have hc := conditions_mem M hM hT
  have ha := alphabet_mem M hM hT
  have hcdef (p : ZFSet.{0}) : p ∈ conditions ↔ p ∈ M ∧ Prefix alphabet p :=
    ⟨fun h => ⟨hM _ hc _ h,(mem_conditions _).mp h⟩,
      fun h => (mem_conditions _).mpr h.2⟩
  intro n
  obtain ⟨q,hq,hqD⟩ := hG (definedAt conditions alphabet n)
    (definedAt_mem M hM hT hc ha n)
    (definedAt_dense M hM hT ha hcdef ⟨bitSet false,(mem_alphabet _).mpr ⟨false,rfl⟩⟩ n)
  let p := conditionEquiv.symm q
  have hp : p ∈ (pullFilter G).carrier := by simpa [pullFilter,p] using hq
  obtain ⟨_,b,hb,hnb⟩ := ZFSet.mem_sep.mp hqD
  obtain ⟨b,rfl⟩ := (mem_alphabet _).mp hb
  have hl : label conditions q = wordCode p.word := by
    rw [←label_encodeCondition p]; congr 1; exact (conditionEquiv.apply_symm_apply q).symm
  rw [hl] at hnb
  exact ⟨p,hp,Nat.le_of_lt ((pair_mem_wordCode _ _ _).mp hnb).1⟩

theorem groundGeneric_real (M : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (G : GenericFilter (Conditions conditions)) (hG : AtomicForcing.GroundGeneric M G) :
    ∃ A : Oracle, G = pushFilter (realFilter A) := by
  obtain ⟨A,hA⟩ := CohenFilterReal.exists_realFilter (pullFilter G) (groundGeneric_long M hM hT G
    hG)
  exact ⟨A,by rw [←hA,push_pull]⟩

end TuringRigidity.InternalCohen

end OAI
