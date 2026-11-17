/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Constructibility/UniformOmegaLevels.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.OrdinalCodes.OmegaCertificateCollection

/-!
# Uniform Omega Levels
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible
open BoundedDefinability SetModelFunctions SentenceCoding
universe u

theorem ordinal_le_internal {M : ZFSet.{u}} (hM : Transitive M)
    {a b : Ordinal.{u}} (ha : a.toZFSet ∈ M) (hb : b ≤ a) : b.toZFSet ∈ M := by
  rcases hb.eq_or_lt with rfl|hb
  · exact ha
  · exact hM _ ha _ (Ordinal.toZFSet_mem_toZFSet_iff.mpr hb)

theorem uniform_omega_certificates_at_levels (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (a : Ordinal.{u}) (ha : a.toZFSet ∈ M) :
    ∃ γ : Ordinal.{u}, γ.toZFSet ∈ M ∧ ∀ δ : Ordinal.{u}, γ ≤ δ →
      ∀ c ≤ a, c.toZFSet ∈ level (groundReals M) δ ∧
        (Ordinal.omega0 ^ c).toZFSet ∈ level (groundReals M) δ ∧
        OmegaPowerCertificates (level (groundReals M) δ) c.toZFSet ∧
        ∀ z ∈ level (groundReals M) δ,
          omegaPowerSentence.Sat (level (groundReals M) δ : Set ZFSet)
            (cons z (fun _ => c.toZFSet)) ↔ z = (Ordinal.omega0 ^ c).toZFSet := by
  let R := groundReals M
  let N := relativeModel M R
  have hR := groundReals_mem M hM hT
  have C := ground_relative_context M hM hT
  have hRep := relativeModel_sigma_replacement M R hM hT hR
  have hColl := relativeModel_sigma_collection M R hM hT hR
  have haN : a.toZFSet ∈ N := (ground_relativeModel_ordinal_iff M hM hT a).mpr ha
  have hyN := relative_omega_power_internal M hM hT a ha
  obtain ⟨G,hG,hgraphs⟩ := omega_graph_collection N C hRep hColl a haN
  obtain ⟨U,hU,hprod⟩ := product_certificate_collection N C hRep hColl
    (Ordinal.omega0 ^ a) Ordinal.omega0 hyN (toZFSet_omega.symm ▸ C.omega_mem)
  let e := cons a.toZFSet (cons (Ordinal.omega0 ^ a).toZFSet (cons G (fun _ => U)))
  have he (i : ℕ) : e i ∈ N := by
    rcases i with _|_|_|i
    · exact haN
    · exact hyN
    · exact hG
    · exact hU
  obtain ⟨γ,hγ,hγe⟩ := finite_parameters_in_relative_level M R hM hT e 4
    (fun i _ => (mem_relativeModel M R _ hM hT hR).mp (he i))
  refine ⟨γ,hγ,?_⟩
  intro δ hδ c hca
  have hL (i : ℕ) (hi : i < 4) : e i ∈ level R δ := level_mono R hδ (hγe i hi)
  have hcL := ordinal_le_internal (level_transitive R δ) (hL 0 (by omega)) hca
  have hyL := ordinal_le_internal (level_transitive R δ) (hL 1 (by omega))
    (Ordinal.opow_le_opow_right Ordinal.omega0_pos hca)
  obtain ⟨f,hf,r,hr,hg⟩ := hgraphs c hca
  have hlt (t : ZFSet.{u}) (ht : t ∈ c.toZFSet) :
      Ordinal.omega0 ^ t.rank < Ordinal.omega0 ^ a := by
    obtain ⟨b,hb,rfl⟩ := Ordinal.mem_toZFSet_iff.mp ht
    rw [Ordinal.rank_toZFSet]
    exact (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mpr (hb.trans_le hca)
  have hc : OmegaPowerCertificates (level R δ) c.toZFSet := by
    have hGsub : G ⊆ level R δ := level_transitive R δ G (hL 2 (by omega))
    refine ⟨hcL,f,hGsub hf,r,hGsub hr,
      hg.relocate (fun t ht => level_transitive R δ _ (hL 1 (by omega)) _
        (Ordinal.toZFSet_mem_toZFSet_iff.mpr (hlt t ht))),?_⟩
    intro t ht
    obtain ⟨hd,hr,f',hf',hcert,_⟩ := hprod _ (hlt t ht)
    have hsub : U ⊆ level R δ := level_transitive R δ U (hL 3 (by omega))
    exact ⟨hsub hd,hsub hr,f',hsub hf',hcert⟩
  refine ⟨hcL,hyL,hc,?_⟩
  intro z hz
  have henv : ∀ i, cons z (fun _ => c.toZFSet) i ∈ level R δ := by
    intro i
    cases i
    · exact hz
    · exact hcL
  have hω := OrdinalCoding.ground_level_omega_mem M hM hT δ
  constructor
  · intro h
    have hval := (omegaPowerSentence_sound _ (level_transitive R δ) hω _ henv h).2
    simpa only [cons_succ,cons_zero,Ordinal.rank_toZFSet] using hval
  · intro h
    apply omegaPowerSentence_of_certificates _ (level_transitive R δ) hω _ henv hc
    simpa only [cons_succ,cons_zero,Ordinal.rank_toZFSet] using h

end TuringRigidity.OrdinalArithmetic

end OAI
