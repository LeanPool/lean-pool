/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/InternalRegularAlgebra.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.InternalRegularOperations

/-!
# Internal Regular Algebra
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.InternalRegularAlgebra
open Set TransitiveNameModel BoundedSetTheory RegularCompletion InternalRegularOperations
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

/-- A subset of `c` fixed by the regularization operation. -/
def IsCode (c U : ZFSet.{0}) : Prop := U ⊆ c ∧ regular c U = U

theorem mem_regular (c U p : ZFSet.{0}) :
    p ∈ regular c U ↔ p ∈ c ∧ ∀ q ∈ c, p ⊆ q → ∃ r ∈ U, q ⊆ r := by
  classical
  simp only [regular,neg,ZFSet.mem_sep]
  constructor
  · rintro ⟨hp,h⟩
    refine ⟨hp,fun q hq hpq => ?_⟩
    by_contra hn
    exact h q ⟨hq,fun r hr hqr => hn ⟨r,hr,hqr⟩⟩ hpq
  · rintro ⟨hp,h⟩
    refine ⟨hp,fun q hq hpq => ?_⟩
    obtain ⟨r,hr,hqr⟩ := h q hq.1 hpq
    exact hq.2 r hr hqr

theorem isCode_iff (c U : ZFSet.{0}) : IsCode c U ↔
    U ⊆ c ∧ ∀ p ∈ c, p ∈ U ↔ ∀ q ∈ c, p ⊆ q → ∃ r ∈ U, q ⊆ r := by
  constructor
  · rintro ⟨hUc,hU⟩
    refine ⟨hUc,fun p hp => ?_⟩
    have h := mem_regular c U p
    rw [hU] at h
    exact h.trans (and_iff_right hp)
  · rintro ⟨hUc,hU⟩
    refine ⟨hUc,ZFSet.ext (fun p => ?_)⟩
    rw [mem_regular]
    exact ⟨fun h => (hU p h.1).mpr h.2,fun h => ⟨hUc h,(hU p (hUc h)).mp h⟩⟩

/-- Bounded formula asserting that a condition-set code is fixed by regularization. -/
def codeFormula (c U : ℕ) : Formula :=
  .conj (.subset U c) (.allMem c (.iff (.member 0 (U+1))
    (.allMem (c+1) (.imp (.subset 1 0) (.existsMem (U+2) (.subset 1 0))))))

theorem codeFormula_spec (c U : ℕ) (e : ℕ → ZFSet.{0}) :
    (codeFormula c U).Eval e ↔ IsCode (e c) (e U) := by
  rw [isCode_iff]
  simp only [codeFormula,Formula.Eval,Formula.eval_subset,Formula.eval_allMem,
    Formula.eval_iff,Formula.eval_imp,cons_zero,cons_succ]

theorem internal_algebra (M c : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) : ∃ B ∈ M, ∀ U, U ∈ B ↔ U ∈ M ∧ IsCode c U := by
  obtain ⟨Q,hQ,hQdef⟩ := internal_power M hM hT.powerSet hc
  let B := Q.sep (IsCode c)
  have hB : B ∈ M := by
    have hs := sep_mem M hM hT.separation.finitePrefix.bounded
      (codeFormula 1 0) (fun _ => c) (fun _ => hc) hQ
    simpa only [codeFormula_spec,cons_zero,cons_succ] using hs
  refine ⟨B,hB,fun U => ?_⟩
  change (U ∈ Q.sep (IsCode c)) ↔ _
  rw [ZFSet.mem_sep,hQdef]
  exact ⟨fun h => ⟨h.1.1,h.2⟩,fun h => ⟨⟨h.1,h.2.1⟩,h.2⟩⟩

theorem code_lower (c U : ZFSet.{0}) (hU : IsCode c U) : Lower c U := by
  rw [← hU.2]
  exact neg_lower c _

/-- Interpret a regular set code as an element of the regular Boolean algebra of the condition
poset. -/
def interpret (c U : ZFSet.{0}) (hU : IsCode c U) : Algebra (Conditions c) :=
  ⟨decode c U (code_lower c U hU),by
    change (decode c U _)ᶜᶜ = decode c U _
    have h := decode_regular c U hU.1 (code_lower c U hU)
    change decode c (regular c U) _ = (decode c U _)ᶜᶜ at h
    apply h.symm.trans
    apply SetLike.ext
    intro p
    change label c p ∈ regular c U ↔ label c p ∈ U
    rw [hU.2]⟩

theorem interpret_le_iff (c U V : ZFSet.{0}) (hU : IsCode c U) (hV : IsCode c V) :
    interpret c U hU ≤ interpret c V hV ↔ U ⊆ V := by
  constructor
  · intro h p hp
    obtain ⟨p,rfl⟩ := label_surjective c (hU.1 hp)
    exact h hp
  · intro h p hp
    exact h hp

theorem interpret_injective (c U V : ZFSet.{0}) (hU : IsCode c U) (hV : IsCode c V) :
    interpret c U hU = interpret c V hV → U = V := by
  intro h
  exact ZFSet.ext (fun p => ⟨fun hp => (interpret_le_iff c U V hU hV).mp (le_of_eq h) hp,
    fun hp => (interpret_le_iff c V U hV hU).mp (le_of_eq h.symm) hp⟩)

theorem neg_isCode (c U : ZFSet.{0}) (hU : IsCode c U) : IsCode c (neg c U) :=
  ⟨neg_subset c U,neg_regular c U hU.1 (code_lower c U hU)⟩

theorem regular_isCode (c U : ZFSet.{0}) : IsCode c (regular c U) :=
  ⟨neg_subset c _,regular_idempotent c U⟩

theorem join_isCode (c F : ZFSet.{0}) : IsCode c (supCode c F) := regular_isCode c _

theorem interpret_neg (c U : ZFSet.{0}) (hU : IsCode c U) :
    interpret c (neg c U) (neg_isCode c U hU) = (interpret c U hU)ᶜ := by
  apply Heyting.Regular.coe_injective
  exact decode_neg c U hU.1 (code_lower c U hU)

theorem internal_complement (M c B : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (hB : ∀ U, U ∈ B ↔ U ∈ M ∧ IsCode c U)
    {U : ZFSet.{0}} (hU : U ∈ B) : neg c U ∈ B :=
  (hB _).mpr ⟨neg_mem M c U hM hT hc ((hB U).mp hU).1,neg_isCode c U ((hB U).mp hU).2⟩

theorem internal_join (M c B F : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (hB : ∀ U, U ∈ B ↔ U ∈ M ∧ IsCode c U) (hF : F ∈ M) :
    supCode c F ∈ B :=
  (hB _).mpr ⟨join_mem M c F hM hT hc hF,join_isCode c F⟩

end TuringRigidity.InternalRegularAlgebra

end OAI
