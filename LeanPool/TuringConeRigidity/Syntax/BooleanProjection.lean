/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Syntax/BooleanProjection.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.CohenForcing.ForcingProjection
public import Mathlib.Order.CompleteSublattice
public import Mathlib.Order.CompleteBooleanAlgebra
public import Mathlib.Data.Set.Countable

/-!
# Boolean Projection
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.BooleanProjection
open Set CountableForcing ForcingProjection
universe u
variable {B : Type u} [CompleteBooleanAlgebra B]

noncomputable def project (A : CompleteSublattice B) (b : B) : B :=
  sInf {a | a ∈ A ∧ b ≤ a}

theorem project_mem (A : CompleteSublattice B) (b : B) : project A b ∈ A :=
  A.sInfClosed (fun _ h => h.1)

theorem le_project (A : CompleteSublattice B) (b : B) : b ≤ project A b :=
  le_sInf (fun _ h => h.2)

theorem project_le_iff (A : CompleteSublattice B) (b a : B) (ha : a ∈ A) :
    project A b ≤ a ↔ b ≤ a :=
  ⟨fun h => (le_project A b).trans h,fun h => sInf_le ⟨ha,h⟩⟩

theorem project_fixed (A : CompleteSublattice B) (a : B) (ha : a ∈ A) :
    project A a = a :=
  le_antisymm ((project_le_iff A a a ha).mpr le_rfl) (le_project A a)

theorem project_mono (A : CompleteSublattice B) : Monotone (project A) := by
  intro b c hbc
  exact (project_le_iff A b _ (project_mem A c)).mpr (hbc.trans (le_project A c))

theorem project_bot (A : CompleteSublattice B) : project A ⊥ = ⊥ :=
  project_fixed A ⊥ A.bot_mem

theorem project_nonzero (A : CompleteSublattice B) {b : B} (hb : b ≠ ⊥) :
    project A b ≠ ⊥ := by
  intro h
  exact hb (le_bot_iff.mp (h ▸ le_project A b))

theorem project_inf (A : CompleteSublattice B)
    (hcompl : ∀ a ∈ A, aᶜ ∈ A) (b a : B) (ha : a ∈ A) :
    project A (b ⊓ a) = project A b ⊓ a := by
  apply le_antisymm
  · exact le_inf (project_mono A inf_le_left) ((project_le_iff A _ a ha).mpr inf_le_right)
  · let c := project A (b ⊓ a)
    have hb : b ≤ c ⊔ aᶜ := by
      calc
        b = b ⊓ a ⊔ b ⊓ aᶜ := (sup_inf_inf_compl).symm
        _ ≤ c ⊔ aᶜ := sup_le_sup (le_project A _) inf_le_right
    have hc : c ⊔ aᶜ ∈ A := A.supClosed' (project_mem A _) (hcompl a ha)
    have hp : project A b ≤ c ⊔ aᶜ := (project_le_iff A _ _ hc).mpr hb
    calc
      project A b ⊓ a ≤ (c ⊔ aᶜ) ⊓ a := inf_le_inf_right a hp
      _ = c ⊓ a := by rw [inf_sup_right]; simp
      _ ≤ c := inf_le_left

def Positive (B : Type u) [Bot B] := {b : B // b ≠ ⊥}

instance positiveOrder : PartialOrder (Positive B) :=
  inferInstanceAs (PartialOrder {b : B // b ≠ ⊥})

def PartPositive (A : CompleteSublattice B) := {a : B // a ∈ A ∧ a ≠ ⊥}

instance partPositiveOrder (A : CompleteSublattice B) : PartialOrder (PartPositive A) :=
  inferInstanceAs (PartialOrder {a : B // a ∈ A ∧ a ≠ ⊥})

noncomputable def forcingProjection (A : CompleteSublattice B)
    (hcompl : ∀ a ∈ A, aᶜ ∈ A) : Projection (Positive B) (PartPositive A) where
  map b := ⟨project A b.val,project_mem A _,project_nonzero A b.property⟩
  mono := fun _ _ h => project_mono A h
  lift := by
    intro b a hab
    have he : project A (b.val ⊓ a.val) = a.val := by
      rw [project_inf A hcompl _ _ a.property.1,inf_eq_right.mpr hab]
    have hn : b.val ⊓ a.val ≠ ⊥ := by
      intro h
      exact a.property.2 (by rw [← he,h,project_bot])
    exact ⟨⟨b.val ⊓ a.val,hn⟩,inf_le_left,he.le⟩

theorem forcingProjection_exact (A : CompleteSublattice B)
    (hcompl : ∀ a ∈ A, aᶜ ∈ A) (b : Positive B) (a : PartPositive A)
    (hab : a ≤ (forcingProjection A hcompl).map b) :
    ∃ c, c ≤ b ∧ (forcingProjection A hcompl).map c = a := by
  change a.val ≤ project A b.val at hab
  have he : project A (b.val ⊓ a.val) = a.val := by
    rw [project_inf A hcompl _ _ a.property.1,inf_eq_right.mpr hab]
  have hn : b.val ⊓ a.val ≠ ⊥ := by
    intro h
    exact a.property.2 (by rw [← he,h,project_bot])
  exact ⟨⟨b.val ⊓ a.val,hn⟩,inf_le_left,Subtype.ext he⟩

theorem projected_dense (A : CompleteSublattice B)
    (hcompl : ∀ a ∈ A, aᶜ ∈ A) (D : Set (Positive B)) (hD : Dense D) :
    Dense ((forcingProjection A hcompl).map '' D) := by
  intro a
  obtain ⟨b,hba,hbD⟩ := hD ⟨a.val,a.property.2⟩
  refine ⟨(forcingProjection A hcompl).map b,?_,b,hbD,rfl⟩
  exact (project_le_iff A b.val a.val a.property.1).mpr hba

theorem projected_countable_dense (A : CompleteSublattice B)
    (hcompl : ∀ a ∈ A, aᶜ ∈ A) (D : Set (Positive B))
    (hc : D.Countable) (hd : Dense D) :
    ∃ E : Set (PartPositive A), E.Countable ∧ Dense E :=
  ⟨(forcingProjection A hcompl).map '' D,hc.image _,projected_dense A hcompl D hd⟩

end TuringRigidity.BooleanProjection

end OAI
