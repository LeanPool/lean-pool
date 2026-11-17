/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/RegularDecisionPartition.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.RegularCodeSplitting

/-!
# Regular Decision Partition
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.RegularDecisionPartition
open TransitiveNameModel BoundedSetTheory InternalRegularOperations InternalRegularAlgebra
open InternalRegularOrder RegularCodeSplitting

noncomputable def meet (U V : ZFSet.{0}) : ZFSet.{0} := U.sep (fun p => p ∈ V)

theorem meet_mem (M U V : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hU : U ∈ M) (hV : V ∈ M) : meet U V ∈ M := by
  simpa only [meet,Formula.Eval,cons_zero,cons_succ] using
    sep_mem M hM hT.separation.finitePrefix.bounded (.member 0 1)
      (fun _ => V) (fun _ => hV) hU

theorem meet_isCode (c U V : ZFSet.{0}) (hU : IsCode c U) (hV : IsCode c V) :
    IsCode c (meet U V) := by
  have he : meet U V = remainder U c (neg c V) := by
    change U.sep (fun p => p ∈ V) = U.sep (fun p => p ∈ regular c V)
    rw [hV.2]
  rw [he]
  exact remainder_isCode c U (neg c V) hU (neg_isCode c V hV)

theorem disjoint_le_neg (c U D : ZFSet.{0}) (hU : IsCode c U) (hD : IsCode c D)
    (he : meet U D = ∅) : U ⊆ neg c D := by
  intro p hp
  refine ZFSet.mem_sep.mpr ⟨hU.1 hp,fun q hq hpq => ?_⟩
  have hqM : q ∈ meet U D := ZFSet.mem_sep.mpr
    ⟨code_lower c U hU p hp q (hD.1 hq) hpq,hq⟩
  exact ZFSet.notMem_empty q (he ▸ hqM)

theorem remainder_empty_le (c U D : ZFSet.{0}) (hU : IsCode c U) (hD : IsCode c D)
    (he : remainder U c D = ∅) : U ⊆ D := by
  classical
  intro p hp
  rw [←hD.2]
  apply (mem_regular c D p).mpr
  refine ⟨hU.1 hp,fun q hq hpq => ?_⟩
  by_contra hn
  have hqR : q ∈ remainder U c D := ZFSet.mem_sep.mpr
    ⟨code_lower c U hU p hp q hq hpq,
      ZFSet.mem_sep.mpr ⟨hq,fun r hr hqr => hn ⟨r,hr,hqr⟩⟩⟩
  exact ZFSet.notMem_empty q (he ▸ hqR)

def Refines (c U D V W : ZFSet.{0}) : Prop :=
  Partition U V W ∧ (V ⊆ D ∨ V ⊆ neg c D) ∧ (W ⊆ D ∨ W ⊆ neg c D)

def decidesFormula (c D V : ℕ) : Formula :=
  .disj (.subset V D) (.allMem V (.conj (.member 0 (c+1))
    (.allMem (D+1) (.neg (.subset 1 0)))))

theorem decidesFormula_spec (c D V : ℕ) (e : ℕ → ZFSet.{0}) :
    (decidesFormula c D V).Eval e ↔ e V ⊆ e D ∨ e V ⊆ neg (e c) (e D) := by
  simp only [decidesFormula,Formula.eval_disj,Formula.eval_subset,Formula.eval_allMem,
    Formula.Eval,cons_zero,cons_succ]
  apply or_congr Iff.rfl
  exact ⟨fun h p hp => ZFSet.mem_sep.mpr (h p hp),
    fun h p hp => ZFSet.mem_sep.mp (h hp)⟩

def refiningFormula (c U D V W : ℕ) : Formula :=
  .conj (partitionFormula U V W) (.conj (decidesFormula c D V) (decidesFormula c D W))

theorem refiningFormula_spec (c U D V W : ℕ) (e : ℕ → ZFSet.{0}) :
    (refiningFormula c U D V W).Eval e ↔ Refines (e c) (e U) (e D) (e V) (e W) := by
  simp only [refiningFormula,Refines,Formula.Eval,partitionFormula_spec,decidesFormula_spec]

theorem refining_partition (M c B : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (hB : ∀ U, U ∈ B ↔ U ∈ M ∧ IsCode c U)
    (hsplit : ∀ p ∈ c, ∃ p0 ∈ c, ∃ p1 ∈ c, p ⊆ p0 ∧ p ⊆ p1 ∧
      ¬ ∃ r ∈ c, p0 ⊆ r ∧ p1 ⊆ r)
    (U D : ZFSet.{0}) (hUB : U ∈ B) (hDB : D ∈ B) (hne : U ≠ ∅) :
    ∃ V ∈ B, ∃ W ∈ B, Refines c U D V W := by
  classical
  have hU := ((hB U).mp hUB).2
  have hD := ((hB D).mp hDB).2
  obtain ⟨V,hVB,W,hWB,hpart⟩ := internal_partition M c B hM hT hc hB hsplit U hUB hne
  by_cases hUD : U ⊆ D
  · exact ⟨V,hVB,W,hWB,hpart,Or.inl (fun _ h => hUD (hpart.1 h)),
      Or.inl (fun _ h => hUD (hpart.2.1 h))⟩
  by_cases hUN : U ⊆ neg c D
  · exact ⟨V,hVB,W,hWB,hpart,Or.inr (fun _ h => hUN (hpart.1 h)),
      Or.inr (fun _ h => hUN (hpart.2.1 h))⟩
  have hL : meet U D ≠ ∅ := fun h => hUN (disjoint_le_neg c U D hU hD h)
  have hR : remainder U c D ≠ ∅ := fun h => hUD (remainder_empty_le c U D hU hD h)
  have hUM := ((hB U).mp hUB).1
  have hDM := ((hB D).mp hDB).1
  refine ⟨meet U D,(hB _).mpr ⟨meet_mem M U D hM hT hUM hDM,meet_isCode c U D hU hD⟩,
    remainder U c D,(hB _).mpr
      ⟨remainder_mem M c U D hM hT hc hUM hDM,remainder_isCode c U D hU hD⟩,
    ⟨(fun _ h => (ZFSet.mem_sep.mp h).1),(fun _ h => (ZFSet.mem_sep.mp h).1),hL,hR,?_,?_⟩,
    Or.inl (fun _ h => (ZFSet.mem_sep.mp h).2),Or.inr (fun _ h => (ZFSet.mem_sep.mp h).2)⟩
  · intro p hp hpR
    exact (ZFSet.mem_sep.mp (ZFSet.mem_sep.mp hpR).2).2 p
      (ZFSet.mem_sep.mp hp).2 (fun _ h => h)
  · intro p hp
    by_cases hex : ∃ q ∈ D, p ⊆ q
    · obtain ⟨q,hq,hpq⟩ := hex
      have hqU := code_lower c U hU p hp q (hD.1 hq) hpq
      exact ⟨q,hqU,hpq,Or.inl (ZFSet.mem_sep.mpr ⟨hqU,hq⟩)⟩
    · exact ⟨p,hp,(fun _ h => h),Or.inr (ZFSet.mem_sep.mpr
        ⟨hp,ZFSet.mem_sep.mpr ⟨hU.1 hp,fun q hq hpq => hex ⟨q,hq,hpq⟩⟩⟩)⟩

end TuringRigidity.RegularDecisionPartition

end OAI
