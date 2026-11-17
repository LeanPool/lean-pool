/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Constructibility/HierarchyCertificatePower.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Constructibility.RelativeModelPower
public import LeanPool.TuringConeRigidity.Constructibility.RelativeModelClosure

/-!
# Hierarchy Certificate Power
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel SentenceCoding BoundedDefinability
  SetModelFunctions
universe u

/-- The set `Q` consists exactly of the subsets of `a` that belong to `M`. -/
def PowerBound (M a Q : ZFSet.{u}) : Prop :=
  ∀ x, x ∈ Q ↔ x ∈ M ∧ x ⊆ a

/-- Bounds containing the model's real codes and its binary natural-number relation codes. -/
def CertificateBounds (M Q B : ZFSet.{u}) : Prop :=
  PowerBound M ZFSet.omega Q ∧ PowerBound M (ZFSet.prod ZFSet.omega ZFSet.omega) B

theorem PowerBound.between {M N a Q : ZFSet.{u}} (h : PowerBound M a Q)
    (hN : Transitive N) (hNM : N ⊆ M) (hQ : Q ∈ N) : PowerBound N a Q := by
  intro x
  exact ⟨fun hx => ⟨hN Q hQ x hx,(h x).mp hx |>.2⟩,
    fun hx => (h x).mpr ⟨hNM hx.1,hx.2⟩⟩

theorem CertificateBounds.coverage {M Q B : ZFSet.{u}} (C : Context M)
    (h : CertificateBounds M Q B) :
    (∀ p : SentenceForm, family p ∈ Q) ∧ (∀ p : SentenceForm, supportGraph p ∈ B) := by
  exact ⟨fun p => (h.1 _).mpr ⟨family_mem M C.transitive C.pairing C.union C.omega_mem p,
    family_subset_omega p⟩,
    fun p => (h.2 _).mpr ⟨supportGraph_mem M C.transitive C.pairing C.union C.omega_mem p,
      supportGraph_subset p⟩⟩

theorem CertificateBounds.between {M N Q B : ZFSet.{u}} (h : CertificateBounds M Q B)
    (hN : Transitive N) (hNM : N ⊆ M) (hQ : Q ∈ N) (hB : B ∈ N) :
    CertificateBounds N Q B :=
  ⟨h.1.between hN hNM hQ,h.2.between hN hNM hB⟩

theorem relative_certificate_bounds (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M) :
    ∃ B ∈ relativeModel M (groundReals M),
      CertificateBounds (relativeModel M (groundReals M)) (groundReals M) B ∧
      (∀ p : SentenceForm, family p ∈ groundReals M) ∧
      (∀ p : SentenceForm, supportGraph p ∈ B) := by
  let R := groundReals M
  let N := relativeModel M R
  have hR := groundReals_mem M hM hT
  let C : Context N := ⟨relativeModel_transitive M R hM,
    relativeModel_pairing M R hM hT hR,relativeModel_union M R hM hT hR,
    relativeModel_power_set M R hM hT hR,relativeModel_bounded_separation M R hM hT hR,
    ground_relativeModel_infinity M hM hT⟩
  obtain ⟨B,hB,hb⟩ := internal_power N C.transitive C.power (C.prod_mem C.omega_mem C.omega_mem)
  have hq : PowerBound N ZFSet.omega R := by
    intro x
    rw [mem_groundReals]
    exact ⟨fun hx => ⟨(relativeModel_ground_reals M hM hT x hx.2).mpr hx.1,hx.2⟩,
      fun hx => ⟨relativeModel_subset M R hx.1,hx.2⟩⟩
  have h : CertificateBounds N R B := ⟨hq,hb⟩
  exact ⟨B,hB,h,h.coverage C⟩

theorem certificate_bounds_at_level (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M) :
    ∃ (B : ZFSet.{u}) (γ : Ordinal.{u}), γ.toZFSet ∈ M ∧
      (∀ p : SentenceForm, family p ∈ groundReals M) ∧
      (∀ p : SentenceForm, supportGraph p ∈ B) ∧
      ∀ δ : Ordinal.{u}, δ.toZFSet ∈ M → γ ≤ δ →
        ZFSet.omega ∈ level (groundReals M) δ ∧
        ZFSet.prod ZFSet.omega ZFSet.omega ∈ level (groundReals M) δ ∧
        groundReals M ∈ level (groundReals M) δ ∧ B ∈ level (groundReals M) δ ∧
        CertificateBounds (level (groundReals M) δ) (groundReals M) B := by
  let R := groundReals M
  let N := relativeModel M R
  have hR := groundReals_mem M hM hT
  let C : Context N := ⟨relativeModel_transitive M R hM,
    relativeModel_pairing M R hM hT hR,relativeModel_union M R hM hT hR,
    relativeModel_power_set M R hM hT hR,relativeModel_bounded_separation M R hM hT hR,
    ground_relativeModel_infinity M hM hT⟩
  obtain ⟨B,hB,hbounds,hq,hb⟩ := relative_certificate_bounds M hM hT
  let e := cons ZFSet.omega (cons (ZFSet.prod ZFSet.omega ZFSet.omega) (cons R (fun _ => B)))
  have he (i : ℕ) (_hi : i < 4) : InRelativeModel M R (e i) := by
    apply (mem_relativeModel M R _ hM hT hR).mp
    rcases i with _|_|_|i
    · exact C.omega_mem
    · exact C.prod_mem C.omega_mem C.omega_mem
    · exact (mem_relativeModel M R R hM hT hR).mpr (parameter_in_relativeModel M R hM hT)
    · exact hB
  obtain ⟨γ,hγ,hγe⟩ := finite_parameters_in_relative_level M R hM hT e 4 he
  refine ⟨B,γ,hγ,hq,hb,?_⟩
  intro δ hδ hγδ
  have hin (i : ℕ) (hi : i < 4) : e i ∈ level R δ := level_mono R hγδ (hγe i hi)
  have hsub : level R δ ⊆ N := fun x hx =>
    (mem_relativeModel M R x hM hT hR).mpr ⟨δ,hδ,hx⟩
  exact ⟨hin 0 (by decide),hin 1 (by decide),hin 2 (by decide),hin 3 (by decide),
    hbounds.between (level_transitive R δ) hsub (hin 2 (by decide)) (hin 3 (by decide))⟩

end TuringRigidity.RelativeConstructible

end OAI
