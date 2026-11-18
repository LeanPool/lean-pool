/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Constructibility/RelativeDefCertificates.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Syntax.CheckedDefSuccessor

/-!
# Relative Def Certificates
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel SentenceCoding
open BoundedDefinability SetModelFunctions
universe u

theorem ground_relative_context (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M) :
    Context (relativeModel M (groundReals M)) := by
  have hR := groundReals_mem M hM hT
  exact ⟨relativeModel_transitive M _ hM,relativeModel_pairing M _ hM hT hR,
    relativeModel_union M _ hM hT hR,relativeModel_power_set M _ hM hT hR,
    relativeModel_bounded_separation M _ hM hT hR,ground_relativeModel_infinity M hM hT⟩

theorem checked_successor_at_level (M A : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (hA : A ∈ relativeModel M (groundReals M)) :
    ∃ γ : Ordinal.{u}, γ.toZFSet ∈ M ∧
      ∀ δ : Ordinal.{u}, δ.toZFSet ∈ M → γ ≤ δ →
        A ∈ level (groundReals M) δ ∧ definablePower A ∈ level (groundReals M) δ ∧
        ∀ D : ZFSet.{u}, CheckedDefSuccessor (level (groundReals M) δ) ZFSet.omega
          (ZFSet.prod ZFSet.omega ZFSet.omega) A D ↔ D = definablePower A := by
  let R := groundReals M
  let N := relativeModel M R
  have hR := groundReals_mem M hM hT
  have C := ground_relative_context M hM hT
  obtain ⟨B,hB,hbounds,hq,hb⟩ := relative_certificate_bounds M hM hT
  obtain ⟨G,hG,T,hTT,H,hH,Z,hZ,hd⟩ := internal_defSystem_of_context N C R B A hA hq hb
  have hD := definablePower_mem_of_context N A C hA
  let e := cons R (cons B (cons A (cons (definablePower A)
    (cons G (cons T (cons H (fun _ => Z)))))))
  have he (i : ℕ) (_hi : i < 8) : InRelativeModel M R (e i) := by
    apply (mem_relativeModel M R _ hM hT hR).mp
    rcases i with _|_|_|_|_|_|_|i
    · exact (mem_relativeModel M R R hM hT hR).mpr (parameter_in_relativeModel M R hM hT)
    · exact hB
    · exact hA
    · exact hD
    · exact hG
    · exact hTT
    · exact hH
    · exact hZ
  obtain ⟨γ,hγ,hγe⟩ := finite_parameters_in_relative_level M R hM hT e 8 he
  refine ⟨γ,hγ,?_⟩
  intro δ hδ hγδ
  have hin (i : ℕ) (hi : i < 8) : e i ∈ level R δ := level_mono R hγδ (hγe i hi)
  have hsub : level R δ ⊆ N := fun x hx =>
    (mem_relativeModel M R x hM hT hR).mpr ⟨δ,hδ,hx⟩
  have hbound := hbounds.between (level_transitive R δ) hsub (hin 0 (by decide)) (hin 1 (by decide))
  refine ⟨hin 2 (by decide),hin 3 (by decide),?_⟩
  intro D
  constructor
  · exact CheckedDefSuccessor.sound
      (fun p => level_transitive R δ R (hin 0 (by decide)) _ (hq p))
      (fun p => level_transitive R δ B (hin 1 (by decide)) _ (hb p))
  · rintro rfl
    exact ⟨R,hin 0 (by decide),B,hin 1 (by decide),hbound,
      G,hin 4 (by decide),T,hin 5 (by decide),H,hin 6 (by decide),Z,hin 7 (by decide),hd⟩

end TuringRigidity.RelativeConstructible

end OAI
