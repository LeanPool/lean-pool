/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/InternalBooleanTop.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.InternalProjectedGeneric

/-!
# Internal Boolean Top
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.InternalBooleanTop
open TransitiveNameModel BoundedSetTheory CountableForcing
open InternalRegularOperations InternalRegularAlgebra InternalRegularOrder
open InternalBooleanSyntax InternalBooleanProjection InternalProjectedGeneric
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder
attribute [local instance] codeOrder codePreorder

theorem top_mem_part (M c B Q A : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (hBM : B ∈ M)
    (hB : ∀ U, U ∈ B ↔ U ∈ M ∧ IsCode c U)
    (hQ : ∀ F, F ∈ Q ↔ F ∈ M ∧ F ⊆ B) (hA : Closed c B Q A) : c ∈ A := by
  have h0 : (∅ : ZFSet.{0}) ∈ M := hM _ (sourceT_omega_mem M hM hT) _ ZFSet.omega_zero
  have h := closed_inf M c B Q A ∅ hM hT hc hBM hB hQ hA h0
    (fun x hx => False.elim (ZFSet.notMem_empty x hx))
  have he : infCode c ∅ = c := by
    apply ZFSet.ext; intro p
    simp only [infCode,ZFSet.mem_sep,ZFSet.notMem_empty,false_implies,implies_true,and_true]
  rwa [he] at h

/-- The `Top` instance on positive Boolean codes, choosing the full condition set as the
distinguished top element. -/
@[instance_reducible]
noncomputable def booleanTop (c A : ZFSet.{0}) (hcA : c ∈ A) (hc0 : c ≠ ∅) :
    Top (Conditions (positive A)) :=
  ⟨Classical.choose (label_surjective (positive A) (ZFSet.mem_sep.mpr ⟨hcA,hc0⟩))⟩

theorem label_booleanTop (c A : ZFSet.{0}) (hcA : c ∈ A) (hc0 : c ≠ ∅) :
    @label (positive A) (booleanTop c A hcA hc0).top = c :=
  Classical.choose_spec (label_surjective (positive A) (ZFSet.mem_sep.mpr ⟨hcA,hc0⟩))

theorem top_in_filter (c A : ZFSet.{0}) [Top (Conditions (positive A))]
    (hAc : ∀ U ∈ A, U ⊆ c) (ht : label (positive A) ⊤ = c)
    (H : GenericFilter (Conditions (positive A))) : ⊤ ∈ H.carrier := by
  obtain ⟨p,hp⟩ := H.nonempty
  apply H.upper (q := ⊤) _ hp
  change label (positive A) p ⊆ label (positive A) ⊤
  rw [ht]
  exact hAc _ (label_info A p).1

end TuringRigidity.InternalBooleanTop

end OAI
