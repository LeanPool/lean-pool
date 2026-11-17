/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Syntax/BoundedHierarchyCertificates.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Constructibility.HierarchyWitnessCollection

/-!
# Bounded Hierarchy Certificates
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel SentenceCoding
open BoundedDefinability SetModelFunctions
universe u

theorem hierarchy_checked_at_levels (M s d r f : ZFSet.{u})
    (hM : Transitive M) (hT : SourceT M)
    (hs : s ∈ relativeModel M (groundReals M))
    (hd : d ∈ relativeModel M (groundReals M))
    (hr : r ∈ relativeModel M (groundReals M))
    (hf : f ∈ relativeModel M (groundReals M))
    (hg : HierarchyGraph (relativeModel M (groundReals M)) s d r f) :
    ∃ γ : Ordinal.{u}, γ.toZFSet ∈ M ∧
      ∀ δ : Ordinal.{u}, δ.toZFSet ∈ M → γ ≤ δ →
        s ∈ level (groundReals M) δ ∧ d ∈ level (groundReals M) δ ∧
        r ∈ level (groundReals M) δ ∧ f ∈ level (groundReals M) δ ∧
        ZFSet.omega ∈ level (groundReals M) δ ∧
        ZFSet.prod ZFSet.omega ZFSet.omega ∈ level (groundReals M) δ ∧
        (∀ p : SentenceForm, family p ∈ level (groundReals M) δ) ∧
        (∀ p : SentenceForm, supportGraph p ∈ level (groundReals M) δ) ∧
        CheckedHierarchyGraph (level (groundReals M) δ) ZFSet.omega
          (ZFSet.prod ZFSet.omega ZFSet.omega) s d r f := by
  let R := groundReals M
  let N := relativeModel M R
  have hR := groundReals_mem M hM hT
  have C := ground_relative_context M hM hT
  have hRN : R ∈ N := (mem_relativeModel M R R hM hT hR).mpr
    (parameter_in_relativeModel M R hM hT)
  obtain ⟨B,hB,hbounds,hq,hb⟩ := relative_certificate_bounds M hM hT
  obtain ⟨W,hW,hw⟩ := hierarchy_witness_collection C
    (relativeModel_sigma_collection M R hM hT hR) hRN hB hq hb hs hd hr hf hg
  let e := cons R (cons B (cons W (cons s (cons d (cons r (cons f
    (cons ZFSet.omega (fun _ => ZFSet.prod ZFSet.omega ZFSet.omega))))))))
  have he (i : ℕ) (_hi : i < 9) : InRelativeModel M R (e i) := by
    apply (mem_relativeModel M R _ hM hT hR).mp
    rcases i with _|_|_|_|_|_|_|_|i
    · exact hRN
    · exact hB
    · exact hW
    · exact hs
    · exact hd
    · exact hr
    · exact hf
    · exact C.omega_mem
    · exact C.prod_mem C.omega_mem C.omega_mem
  obtain ⟨γ,hγ,hγe⟩ := finite_parameters_in_relative_level M R hM hT e 9 he
  refine ⟨γ,hγ,?_⟩
  intro δ hδ hγδ
  have hin (i : ℕ) (hi : i < 9) : e i ∈ level R δ := level_mono R hγδ (hγe i hi)
  have ht := level_transitive R δ
  have hsub : level R δ ⊆ N := fun x hx =>
    (mem_relativeModel M R x hM hT hR).mpr ⟨δ,hδ,hx⟩
  have hbound := hbounds.between ht hsub (hin 0 (by decide)) (hin 1 (by decide))
  refine ⟨hin 3 (by decide),hin 4 (by decide),hin 5 (by decide),hin 6 (by decide),
    hin 7 (by decide),hin 8 (by decide),
    (fun p => ht R (hin 0 (by decide)) _ (hq p)),
    (fun p => ht B (hin 1 (by decide)) _ (hb p)),hg.1,hg.2.1,?_⟩
  intro x hx v hv hpair
  obtain ⟨c,hc,A,hA,v',hv',G,hG,T,hTT,H,hH,Z,hZ,hpair',hstep,hdef⟩ := hw x hx
  obtain ⟨v0,_,_,hu⟩ := hg.2.1.2 x hx
  have heq : v' = v := (hu v' hv' hpair').trans (hu v hv hpair).symm
  subst v'
  have hcL := ht W (hin 2 (by decide)) c hc
  refine ⟨A,ht c hcL A hA,hstep,R,hin 0 (by decide),B,hin 1 (by decide),hbound,
    G,ht c hcL G hG,T,ht c hcL T hTT,H,ht c hcL H hH,Z,ht c hcL Z hZ,hdef⟩

theorem relative_hierarchy_recognition_at_levels (M d r f : ZFSet.{u})
    (hM : Transitive M) (hT : SourceT M)
    (hd : d ∈ relativeModel M (groundReals M))
    (hr : r ∈ relativeModel M (groundReals M))
    (hf : f ∈ relativeModel M (groundReals M))
    (hg : HierarchyGraph (relativeModel M (groundReals M)) (seed (groundReals M)) d r f) :
    ∃ γ : Ordinal.{u}, γ.toZFSet ∈ M ∧
      ∀ δ : Ordinal.{u}, δ.toZFSet ∈ M → γ ≤ δ →
        f ∈ level (groundReals M) δ ∧
        ∀ g : ZFSet.{u}, CheckedHierarchyGraph (level (groundReals M) δ) ZFSet.omega
          (ZFSet.prod ZFSet.omega ZFSet.omega) (seed (groundReals M)) d r g ↔ g = f := by
  have hR := groundReals_mem M hM hT
  have hs := seed_mem_collection _ _ (ground_relative_context M hM hT)
    (relativeModel_sigma_replacement M _ hM hT hR)
    ((mem_relativeModel M _ _ hM hT hR).mpr (parameter_in_relativeModel M _ hM hT))
  obtain ⟨γ,hγ,hγspec⟩ := hierarchy_checked_at_levels M _ d r f hM hT hs hd hr hf hg
  refine ⟨γ,hγ,?_⟩
  intro δ hδ hγδ
  obtain ⟨_,_,_,hfL,_,_,hfamily,hsupport,hchecked⟩ := hγspec δ hδ hγδ
  exact ⟨hfL,fun g => ⟨fun h => (h.sound hfamily hsupport).unique hg,
    fun heq => heq ▸ hchecked⟩⟩

end TuringRigidity.RelativeConstructible

end OAI
