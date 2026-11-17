/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/InternalRegularOperations.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.RegularCompletion
public import LeanPool.TuringConeRigidity.CohenForcing.CohenInternalDecision

/-!
# Internal Regular Operations
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.InternalRegularOperations
open Set TransitiveNameModel BoundedSetTheory RegularCompletion
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

/-- The conditions with no extension belonging to `U`, in the inclusion-based graph
presentation. -/
noncomputable def neg (c U : ZFSet.{0}) : ZFSet.{0} :=
  c.sep (fun p => ∀ q ∈ U, ¬ p ⊆ q)

/-- Regularize a condition-set code by applying its complement operation twice. -/
noncomputable def regular (c U : ZFSet.{0}) : ZFSet.{0} := neg c (neg c U)

/-- The family `U` is preserved by extending its condition graphs inside `c`. -/
def Lower (c U : ZFSet.{0}) : Prop :=
  ∀ p ∈ U, ∀ q ∈ c, p ⊆ q → q ∈ U

theorem neg_subset (c U : ZFSet.{0}) : neg c U ⊆ c :=
  fun _ h => (ZFSet.mem_sep.mp h).1

theorem neg_lower (c U : ZFSet.{0}) : Lower c (neg c U) := by
  intro p hp q hq hpq
  refine ZFSet.mem_sep.mpr ⟨hq,?_⟩
  intro r hr hqr
  exact (ZFSet.mem_sep.mp hp).2 r hr (fun z hz => hqr (hpq hz))

theorem neg_mem (M c U : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (hU : U ∈ M) : neg c U ∈ M := by
  have hs := sep_mem M hM hT.separation.finitePrefix.bounded
    (.allMem 1 (.neg (.subset 1 0))) (fun _ => U) (fun _ => hU) hc
  simpa only [neg,Formula.Eval,Formula.eval_allMem,Formula.eval_subset,
    cons_zero,cons_succ] using hs

theorem regular_mem (M c U : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (hU : U ∈ M) : regular c U ∈ M :=
  neg_mem M c _ hM hT hc (neg_mem M c U hM hT hc hU)

/-- Interpret a lower condition-set code as a lower set of condition-label elements. -/
def decode (c U : ZFSet.{0}) (hU : Lower c U) : LowerSet (Conditions c) where
  carrier := {p | label c p ∈ U}
  lower' := by
    intro p q hpq hq
    exact hU _ hq _ (label_mem c q) hpq

theorem decode_injective (c U V : ZFSet.{0}) (hUc : U ⊆ c) (hVc : V ⊆ c)
    (hU : Lower c U) (hV : Lower c V) :
    decode c U hU = decode c V hV → U = V := by
  intro h
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    obtain ⟨p,rfl⟩ := label_surjective c (hUc hz)
    exact (show label c p ∈ U ↔ label c p ∈ V from
      SetLike.ext_iff.mp h p).mp hz
  · intro hz
    obtain ⟨p,rfl⟩ := label_surjective c (hVc hz)
    exact (show label c p ∈ U ↔ label c p ∈ V from
      SetLike.ext_iff.mp h p).mpr hz

theorem decode_neg (c U : ZFSet.{0}) (hUc : U ⊆ c) (hU : Lower c U) :
    decode c (neg c U) (neg_lower c U) = (decode c U hU)ᶜ := by
  apply SetLike.ext
  intro p
  rw [RegularCompletion.mem_compl]
  change (label c p ∈ neg c U) ↔ _
  rw [neg,ZFSet.mem_sep]
  constructor
  · rintro ⟨_,hp⟩ q hqp hq
    exact hp (label c q) hq hqp
  · intro hp
    refine ⟨label_mem c p,?_⟩
    intro q hq hpq
    obtain ⟨q,rfl⟩ := label_surjective c (hUc hq)
    exact hp q hpq hq

theorem decode_regular (c U : ZFSet.{0}) (hUc : U ⊆ c) (hU : Lower c U) :
    decode c (regular c U) (neg_lower c (neg c U)) =
      (Heyting.Regular.toRegular (decode c U hU) : LowerSet (Conditions c)) := by
  change decode c (neg c (neg c U)) _ = _
  rw [decode_neg c _ (neg_subset c U) (neg_lower c U),decode_neg c U hUc hU]
  rfl

theorem regular_idempotent (c U : ZFSet.{0}) : regular c (regular c U) = regular c U := by
  apply decode_injective c _ _ (neg_subset c _) (neg_subset c _)
    (neg_lower c _) (neg_lower c _)
  simp only [regular,decode_neg c _ (neg_subset c _) (neg_lower c _),compl_compl_compl]

theorem neg_regular (c U : ZFSet.{0}) (hUc : U ⊆ c) (hU : Lower c U) : regular c (neg c U) = neg c
  U := by
  apply decode_injective c _ _ (neg_subset c _) (neg_subset c _) (neg_lower c _) (neg_lower c _)
  rw [decode_neg c _ (neg_subset c _) (neg_lower c _),
    decode_neg c _ (neg_subset c _) (neg_lower c _)]
  rw [decode_neg c U hUc hU]
  exact compl_compl_compl _

theorem union_lower (c F : ZFSet.{0}) (hF : ∀ U ∈ F, Lower c U) :
    Lower c (ZFSet.sUnion F) := by
  intro p hp q hq hpq
  obtain ⟨U,hU,hp⟩ := ZFSet.mem_sUnion.mp hp
  exact ZFSet.mem_sUnion.mpr ⟨U,hU,hF U hU p hp q hq hpq⟩

/-- Regularize the union of the family `F` to form its Boolean supremum code. -/
noncomputable def supCode (c F : ZFSet.{0}) : ZFSet.{0} := regular c (ZFSet.sUnion F)

theorem join_mem (M c F : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (hF : F ∈ M) : supCode c F ∈ M :=
  regular_mem M c _ hM hT hc (union_mem M hM hT.union hF)

/-- The regular Boolean value generated by the conditions extending members of `E`. -/
noncomputable def bitCode (c E : ZFSet.{0}) : ZFSet.{0} :=
  regular c (CohenInternalDecision.below c E)

theorem bitCode_mem (M c E : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (hE : E ∈ M) : bitCode c E ∈ M :=
  regular_mem M c _ hM hT hc (CohenInternalDecision.below_mem M c E hM hT hc hE)

end TuringRigidity.InternalRegularOperations

end OAI
