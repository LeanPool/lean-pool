/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Constructibility/RelativeModel.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Constructibility.InternalConstructibleHierarchy

/-!
# Relative Model
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.RelativeConstructible
open BoundedSetTheory TransitiveNameModel
universe u

def InRelativeModel (M R x : ZFSet.{u}) : Prop :=
  ∃ o : Ordinal.{u}, o.toZFSet ∈ M ∧ x ∈ level R o

noncomputable def relativeModel (M R : ZFSet.{u}) : ZFSet.{u} :=
  M.sep (InRelativeModel M R)

theorem relativeModel_subset (M R : ZFSet.{u}) : relativeModel M R ⊆ M :=
  fun _ hx => (ZFSet.mem_sep.mp hx).1

theorem InRelativeModel.mem_ground {M R x : ZFSet.{u}}
    (hM : Transitive M) (hT : SourceT M) (hR : R ∈ M)
    (hx : InRelativeModel M R x) : x ∈ M := by
  obtain ⟨o,ho,hx⟩ := hx
  exact level_subset_model M R hM hT hR o ho hx

theorem mem_relativeModel (M R x : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) (hR : R ∈ M) :
    x ∈ relativeModel M R ↔ InRelativeModel M R x := by
  rw [relativeModel,ZFSet.mem_sep]
  exact ⟨And.right,fun hx => ⟨hx.mem_ground hM hT hR,hx⟩⟩

theorem InRelativeModel.external {M R x : ZFSet.{u}}
    (hx : InRelativeModel M R x) : InRelativeL R x := by
  obtain ⟨o,_,hx⟩ := hx
  exact ⟨o,hx⟩

theorem InRelativeModel.transitive {M R x y : ZFSet.{u}}
    (hx : InRelativeModel M R x) (hy : y ∈ x) : InRelativeModel M R y := by
  obtain ⟨o,ho,hx⟩ := hx
  exact ⟨o,ho,level_transitive R o x hx y hy⟩

theorem relativeModel_transitive (M R : ZFSet.{u}) (hM : Transitive M) :
    Transitive (relativeModel M R) := by
  intro x hx y hy
  obtain ⟨hxM,hx⟩ := ZFSet.mem_sep.mp hx
  exact ZFSet.mem_sep.mpr ⟨hM x hxM y hy,hx.transitive hy⟩

theorem internal_ordinal_zero (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M) :
    (0 : Ordinal.{u}).toZFSet ∈ M := by
  rw [Ordinal.toZFSet_zero]
  exact hM _ (sourceT_omega_mem M hM hT) _ ZFSet.omega_zero

theorem internal_ordinal_succ (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (o : Ordinal.{u}) (ho : o.toZFSet ∈ M) : (o+1).toZFSet ∈ M := by
  rw [Ordinal.toZFSet_add_one]
  have eq : insert o.toZFSet o.toZFSet = ({o.toZFSet} : ZFSet.{u}) ∪ o.toZFSet := by
    apply ZFSet.ext; intro z
    simp only [ZFSet.mem_insert_iff,ZFSet.mem_union,ZFSet.mem_singleton]
  rw [eq]
  exact binary_union_mem M hM hT.pairing hT.union
    (singleton_mem M hM hT.pairing ho) ho

theorem internal_ordinal_max (M : ZFSet.{u}) {i j : Ordinal.{u}}
    (hi : i.toZFSet ∈ M) (hj : j.toZFSet ∈ M) : (max i j).toZFSet ∈ M := by
  rcases le_total i j with h|h
  · simpa only [max_eq_right h] using hj
  · simpa only [max_eq_left h] using hi

theorem parameter_in_relativeModel (M R : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) : InRelativeModel M R R :=
  ⟨0,internal_ordinal_zero M hM hT,level_zero R ▸ parameter_mem_seed R⟩

theorem level_in_relativeModel (M R : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) (o : Ordinal.{u}) (ho : o.toZFSet ∈ M) :
    InRelativeModel M R (level R o) :=
  ⟨o+1,internal_ordinal_succ M hM hT o ho,
    level_mem_level R (lt_add_one o)⟩

theorem relativeModel_ground_reals (M : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) (x : ZFSet.{u}) (hx : x ⊆ ZFSet.omega) :
    x ∈ relativeModel M (groundReals M) ↔ x ∈ M := by
  rw [mem_relativeModel M _ x hM hT (groundReals_mem M hM hT)]
  exact internally_indexed_ground_reals M hM hT x hx

theorem relativeModel_monotone {M N R : ZFSet.{u}} (hMN : M ⊆ N) :
    relativeModel M R ⊆ relativeModel N R := by
  intro x hx
  obtain ⟨hxM,o,ho,hx⟩ := ZFSet.mem_sep.mp hx
  exact ZFSet.mem_sep.mpr ⟨hMN hxM,o,hMN ho,hx⟩

theorem relativeModel_external (M R : ZFSet.{u}) {x : ZFSet.{u}}
    (hx : x ∈ relativeModel M R) : InRelativeL R x :=
  (ZFSet.mem_sep.mp hx).2.external

end TuringRigidity.RelativeConstructible

end OAI
