/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/InternalRegularOrder.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.InternalRegularAlgebra

/-!
# Internal Regular Order
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.InternalRegularOrder
open TransitiveNameModel BoundedSetTheory InternalRegularOperations InternalRegularAlgebra

theorem neg_antitone (c U V : ZFSet.{0}) (h : U ⊆ V) : neg c V ⊆ neg c U := by
  intro p hp
  obtain ⟨hpc,hp⟩ := ZFSet.mem_sep.mp hp
  exact ZFSet.mem_sep.mpr ⟨hpc,fun q hq => hp q (h hq)⟩

theorem regular_mono (c U V : ZFSet.{0}) (h : U ⊆ V) : regular c U ⊆ regular c V :=
  neg_antitone c _ _ (neg_antitone c U V h)

theorem subset_regular (c U : ZFSet.{0}) (hUc : U ⊆ c) (hU : Lower c U) : U ⊆ regular c U := by
  intro p hp
  exact (mem_regular c U p).mpr ⟨hUc hp,fun q hq hpq => ⟨q,hU p hp q hq hpq,fun _ h => h⟩⟩

theorem regular_le_iff (c U V : ZFSet.{0}) (hUc : U ⊆ c) (hU : Lower c U)
    (hV : IsCode c V) : regular c U ⊆ V ↔ U ⊆ V := by
  constructor
  · intro h p hp; exact h (subset_regular c U hUc hU hp)
  · intro h p hp
    have hx := regular_mono c U V h hp
    rwa [hV.2] at hx

theorem union_subset (c F : ZFSet.{0}) (hF : ∀ U ∈ F, IsCode c U) : ZFSet.sUnion F ⊆ c := by
  intro p hp
  obtain ⟨U,hU,hp⟩ := ZFSet.mem_sUnion.mp hp
  exact (hF U hU).1 hp

theorem supCode_le_iff (c F V : ZFSet.{0}) (hF : ∀ U ∈ F, IsCode c U)
    (hV : IsCode c V) : supCode c F ⊆ V ↔ ∀ U ∈ F, U ⊆ V := by
  rw [supCode,regular_le_iff c _ V (union_subset c F hF)
    (union_lower c F (fun U hU => code_lower c U (hF U hU))) hV]
  constructor
  · intro h U hU p hp; exact h (ZFSet.mem_sUnion.mpr ⟨U,hU,hp⟩)
  · intro h p hp
    obtain ⟨U,hU,hp⟩ := ZFSet.mem_sUnion.mp hp
    exact h U hU hp

theorem subset_supCode (c F : ZFSet.{0}) (hF : ∀ U ∈ F, IsCode c U)
    {U : ZFSet.{0}} (hU : U ∈ F) : U ⊆ supCode c F :=
  (supCode_le_iff c F _ hF (join_isCode c F)).mp (fun _ h => h) U hU

/-- The conditions in `c` belonging to every member of `F`. -/
noncomputable def infCode (c F : ZFSet.{0}) : ZFSet.{0} :=
  c.sep (fun p => ∀ U ∈ F, p ∈ U)

theorem inf_subset (c F : ZFSet.{0}) {U : ZFSet.{0}} (hU : U ∈ F) : infCode c F ⊆ U :=
  fun _ hp => (ZFSet.mem_sep.mp hp).2 U hU

theorem subset_inf (c F U : ZFSet.{0}) (hUc : U ⊆ c) (h : ∀ V ∈ F, U ⊆ V) :
    U ⊆ infCode c F := fun _ hp => ZFSet.mem_sep.mpr ⟨hUc hp,fun V hV => h V hV hp⟩

theorem inf_isCode (c F : ZFSet.{0}) (hF : ∀ U ∈ F, IsCode c U) : IsCode c (infCode c F) := by
  have hc : infCode c F ⊆ c := fun _ h => (ZFSet.mem_sep.mp h).1
  have hl : Lower c (infCode c F) := by
    intro p hp q hq hpq
    exact ZFSet.mem_sep.mpr ⟨hq,fun U hU => code_lower c U (hF U hU)
      p ((ZFSet.mem_sep.mp hp).2 U hU) q hq hpq⟩
  refine ⟨hc,ZFSet.ext (fun p => ⟨?_,fun hp => subset_regular c _ hc hl hp⟩)⟩
  intro hp
  refine ZFSet.mem_sep.mpr ⟨neg_subset c _ hp,fun U hU => ?_⟩
  have hx := regular_mono c (infCode c F) U (inf_subset c F hU) hp
  rwa [(hF U hU).2] at hx

theorem inf_mem (M c F : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (hF : F ∈ M) : infCode c F ∈ M := by
  have hs := sep_mem M hM hT.separation.finitePrefix.bounded
    (.allMem 1 (.member 1 0)) (fun _ => F) (fun _ => hF) hc
  simpa only [infCode,Formula.eval_allMem,Formula.Eval,cons_zero,cons_succ] using hs

end TuringRigidity.InternalRegularOrder

end OAI
