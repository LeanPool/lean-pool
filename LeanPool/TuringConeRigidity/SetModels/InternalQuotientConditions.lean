/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/InternalQuotientConditions.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Representation.GenericFilterName
public import LeanPool.TuringConeRigidity.SetModels.InternalSameNameGeneric

/-!
# Internal Quotient Conditions
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.InternalQuotientConditions
open TransitiveNameModel BoundedSetTheory CountableForcing
open InternalRegularOperations InternalRegularAlgebra InternalRegularOrder InternalBooleanSyntax
open InternalBooleanProjection InternalBooleanDense InternalProjectedGeneric InternalBooleanGeneric
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder
attribute [local instance] codeOrder codePreorder

/-- The conditions belonging to every member of `A` that contains `p`. -/
noncomputable def cover (c A p : ZFSet.{0}) : ZFSet.{0} :=
  c.sep (fun r => ∀ U ∈ A, p ∈ U → r ∈ U)

theorem cover_eq_project (c A p : ZFSet.{0}) (hp : p ∈ c)
    (hA : ∀ U ∈ A, IsCode c U) : cover c A p = project c A (basicCode c p) := by
  apply ZFSet.ext; intro r
  simp only [cover,project,infCode,uppers,ZFSet.mem_sep]
  apply and_congr_right; intro _
  constructor
  · intro h U hU
    exact h U hU.1 ((basicCode_le_iff c p U hp (hA U hU.1)).mp hU.2)
  · intro h U hU hpU
    exact h U ⟨hU,(basicCode_le_iff c p U hp (hA U hU)).mpr hpU⟩

/-- Bounded formula describing the common-neighborhood cover of the condition `p`. -/
def coverFormula (c A p V : ℕ) : Formula :=
  .conj (.subset V c) (.allMem c (.iff (.member 0 (V+1))
    (.allMem (A+1) (.imp (.member (p+2) 0) (.member 1 0)))))

theorem coverFormula_spec (c A p V : ℕ) (e : ℕ → ZFSet.{0}) :
    (coverFormula c A p V).Eval e ↔ e V = cover (e c) (e A) (e p) := by
  simp only [coverFormula,Formula.Eval,Formula.eval_subset,Formula.eval_allMem,
    Formula.eval_iff,Formula.eval_imp,cons_zero,cons_succ]
  constructor
  · rintro ⟨hVc,hV⟩
    exact ZFSet.ext (fun r => (Iff.intro
      (fun hr => ⟨hVc hr,(hV r (hVc hr)).mp hr⟩)
      (fun hr => (hV r hr.1).mpr hr.2)).trans ZFSet.mem_sep.symm)
  · intro h; rw [h]
    exact ⟨fun _ hr => (ZFSet.mem_sep.mp hr).1,fun r hr =>
      ZFSet.mem_sep.trans (and_iff_right hr)⟩

/-- The conditions whose projected basic Boolean values belong to `h`. -/
noncomputable def conditions (c A h : ZFSet.{0}) : ZFSet.{0} :=
  c.sep (fun p => project c A (basicCode c p) ∈ h)

theorem conditions_subset (c A h : ZFSet.{0}) : conditions c A h ⊆ c :=
  fun _ hp => (ZFSet.mem_sep.mp hp).1

theorem conditions_mem (N c A h : ZFSet.{0}) (hN : Transitive N) (hT : SourceT N)
    (hc : c ∈ N) (hA : A ∈ N) (hh : h ∈ N)
    (hAc : ∀ U ∈ A, IsCode c U) : conditions c A h ∈ N := by
  let e := cons c (cons A (fun _ => h))
  have he : ∀ i, e i ∈ N := by
    intro i
    rcases i with _ | _ | i
    · exact hc
    · exact hA
    · exact hh
  have hs := sep_mem N hN hT.separation.finitePrefix.bounded
    (.existsMem 3 (coverFormula 2 3 1 0)) e he hc
  have heq : c.sep (fun p => (Formula.existsMem 3 (coverFormula 2 3 1 0)).Eval (cons p e)) =
      conditions c A h := by
    apply ZFSet.ext; intro p
    simp only [conditions,ZFSet.mem_sep,Formula.Eval,coverFormula_spec,cons_zero,cons_succ,e]
    apply and_congr_right; intro hp
    rw [cover_eq_project c A p hp hAc]
    exact ⟨fun ⟨V,hV,he⟩ => he ▸ hV,fun hv => ⟨_,hv,rfl⟩⟩
  exact heq ▸ hs

theorem order_mem (N c A h : ZFSet.{0}) (hN : Transitive N) (hT : SourceT N)
    (hc : c ∈ N) (hA : A ∈ N) (hh : h ∈ N)
    (hAc : ∀ U ∈ A, IsCode c U) :
    InternalCollapse.orderSet (conditions c A h) ∈ N :=
  InternalCollapse.orderSet_mem N hN hT (conditions_mem N c A h hN hT hc hA hh hAc)

theorem original_condition_mem (M c B Q A : ZFSet.{0})
    (hM : Transitive M) (hT : SourceT M) (hc : c ∈ M) (hBM : B ∈ M) (hAM : A ∈ M)
    (hB : ∀ U, U ∈ B ↔ U ∈ M ∧ IsCode c U)
    (hQ : ∀ F, F ∈ Q ↔ F ∈ M ∧ F ⊆ B) (hA : Closed c B Q A)
    (G : GenericFilter (Conditions c)) (p : Conditions c) (hp : p ∈ G.carrier) :
    label c p ∈ conditions c A (genericFilterSet (positive A)
      (projected M c B Q A hM hT hc hBM hAM hB hQ hA G).carrier) := by
  obtain ⟨q,hq,he⟩ := InternalSameNameGeneric.projected_condition M c B Q A
    hM hT hc hBM hAM hB hQ hA G p hp
  exact ZFSet.mem_sep.mpr ⟨label_mem c p,
    (mem_genericFilterSet _ _ _).mpr ⟨q,hq,he⟩⟩

end TuringRigidity.InternalQuotientConditions

end OAI
