/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Constructibility/RelativeOmegaLevels.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.OrdinalCodes.ProductCertificateCollection
public import LeanPool.TuringConeRigidity.OrdinalCodes.OrdinalDecoderDomains

/-!
# Relative Omega Levels
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible
open BoundedDefinability SetModelFunctions SentenceCoding
universe u

theorem OmegaGraph.relocate {M N d r f : ZFSet.{u}} (hg : OmegaGraph M d r f)
    (hval : ∀ t ∈ d, (Ordinal.omega0 ^ t.rank).toZFSet ∈ N) : OmegaGraph N d r f := by
  refine ⟨hg.1,hg.2.1,?_⟩
  intro t ht v hv hp
  obtain ⟨A,_,hs,ho,he⟩ := hg.2.2 t ht v hv hp
  exact ⟨A,(omegaStageStep_exact hg ht hs).symm ▸ hval t ht,hs,ho,he⟩

theorem omega_certificates_at_levels (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (a : Ordinal.{u}) (ha : a.toZFSet ∈ M) :
    ∃ γ : Ordinal.{u}, γ.toZFSet ∈ M ∧ ∀ δ : Ordinal.{u}, γ ≤ δ →
      a.toZFSet ∈ level (groundReals M) δ ∧
      (Ordinal.omega0 ^ a).toZFSet ∈ level (groundReals M) δ ∧
      OmegaPowerCertificates (level (groundReals M) δ) a.toZFSet ∧
      ∀ z ∈ level (groundReals M) δ,
        omegaPowerSentence.Sat (level (groundReals M) δ : Set ZFSet)
          (cons z (fun _ => a.toZFSet)) ↔ z = (Ordinal.omega0 ^ a).toZFSet := by
  let R := groundReals M
  let N := relativeModel M R
  have hR := groundReals_mem M hM hT
  have C := ground_relative_context M hM hT
  have hRep := relativeModel_sigma_replacement M R hM hT hR
  have hColl := relativeModel_sigma_collection M R hM hT hR
  have haN : a.toZFSet ∈ N := (ground_relativeModel_ordinal_iff M hM hT a).mpr ha
  have hyN := relative_omega_power_internal M hM hT a ha
  obtain ⟨_,f,hf,r,hr,hg,_⟩ := relative_omega_power_certificates M hM hT a ha
  obtain ⟨U,hU,hprod⟩ := product_certificate_collection N C hRep hColl
    (Ordinal.omega0 ^ a) Ordinal.omega0 hyN (toZFSet_omega.symm ▸ C.omega_mem)
  let e := cons a.toZFSet (cons (Ordinal.omega0 ^ a).toZFSet (cons f (cons r (fun _ => U))))
  have he (i : ℕ) : e i ∈ N := by
    rcases i with _|_|_|_|i
    · exact haN
    · exact hyN
    · exact hf
    · exact hr
    · exact hU
  obtain ⟨γ,hγ,hγe⟩ := finite_parameters_in_relative_level M R hM hT e 5
    (fun i _ => (mem_relativeModel M R _ hM hT hR).mp (he i))
  refine ⟨γ,hγ,?_⟩
  intro δ hδ
  have hL (i : ℕ) (hi : i < 5) : e i ∈ level R δ := level_mono R hδ (hγe i hi)
  have hlt (t : ZFSet.{u}) (ht : t ∈ a.toZFSet) :
      Ordinal.omega0 ^ t.rank < Ordinal.omega0 ^ a := by
    obtain ⟨b,hb,rfl⟩ := Ordinal.mem_toZFSet_iff.mp ht
    rw [Ordinal.rank_toZFSet]
    exact (Ordinal.opow_lt_opow_iff_right (by exact Ordinal.one_lt_omega0)).mpr hb
  have hc : OmegaPowerCertificates (level R δ) a.toZFSet := by
    refine ⟨hL 0 (by omega),f,hL 2 (by omega),r,hL 3 (by omega),
      hg.relocate (fun t ht => level_transitive R δ _ (hL 1 (by omega)) _
        (Ordinal.toZFSet_mem_toZFSet_iff.mpr (hlt t ht))),?_⟩
    intro t ht
    obtain ⟨hd,hr,f',hf',hcert,_⟩ := hprod _ (hlt t ht)
    have hsub : U ⊆ level R δ := level_transitive R δ U (hL 4 (by omega))
    exact ⟨hsub hd,hsub hr,f',hsub hf',hcert⟩
  refine ⟨hL 0 (by omega),hL 1 (by omega),hc,?_⟩
  intro z hz
  have henv : ∀ i, cons z (fun _ => a.toZFSet) i ∈ level R δ := by
    intro i
    cases i
    · exact hz
    · exact hL 0 (by omega)
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
