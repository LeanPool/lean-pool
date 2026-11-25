/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.FreeData
public import LeanPool.GraphMinor.GM19.FeatureCount
public import LeanPool.GraphMinor.GM19.Section10s

import LeanPool.GraphMinor.GM19.FragmentOrient

/-!
# Corrected Graph Minors XIX, (10.5)

As in the proof of (10.4) we pick one feature in each class of (5.2), and use `exists_class_free`
for it.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM10

universe w

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]


/-- The data of a freedom flaw. -/
theorem freedomFlaw {cap : IsCappedSurface S Shat} {β : Type w} {χ : ColourScheme S β}
  (D : TangleDatum cap χ) {n : ℕ}
    (hf : D.IsFlawedInFreedom n) : ∃ Δ Z K, IsFreeData D n Δ Z K := by
  obtain ⟨hn, hd, F, hF, hc, h⟩ := hf
  exact TangleDatum.exists_free_data χ.isSurface D.P.fits.internally_three_connected hn hd ⟨F,
    hF, hc, h⟩

/-- Corrected Graph Minors XIX, (10.5) (page 357). The proof uses $\mathbf{S}_3$ for a
fragment with fewer cuffs and $\mathbf{S}_4$ for a refinement. -/
theorem theorem_10_5_proof : Theorem105Statement.{w} := by
  intro S Shat _ _ _ _ β _ cap χ hd 𝒮 hcl hS3 hS4 n
  classical
  have hS := χ.isSurface
  let a₀ : β := Classical.arbitrary β
  obtain ⟨𝓕, hf, h𝓕⟩ := theorem_5_2_proof S hS χ.connected χ.Φ (8 * n)
  let Good : Drawing S → Prop := fun K ↦ ∃ (D : TangleDatum cap χ) (Δ Z : Set Shat), IsFreeData D n
    Δ Z K
  have hpick : ∀ K₀, ∃ K', ∀ K, Good K → FeatureEquiv χ.Φ K₀ K → Good K' ∧ FeatureEquiv χ.Φ K₀ K'
    := fun K₀ ↦ by
    by_cases h : ∃ K, Good K ∧ FeatureEquiv χ.Φ K₀ K
    · obtain ⟨K, h₁, h₂⟩ := h
      exact ⟨K, fun _ _ _ ↦ ⟨h₁, h₂⟩⟩
    · exact ⟨K₀, fun K h₁ h₂ ↦ absurd ⟨K, h₁, h₂⟩ h⟩
  choose p hp using hpick
  have hB : ∀ Kc, ∃ B : Set (Place χ), IsWellBehavedPlaces B ∧ (Good Kc
    → ∀ D : TangleDatum cap χ, D.P ∈ 𝒮 → n + 1 ≤ D.ord →
      ∀ (Δ Z : Set Shat) (K : Drawing S) (α : S ≃ₜ S), IsFreeData D n Δ Z K
        → IsFramePreservingHomeo χ.Φ α →
      α '' Kc.U = K.U → α '' Kc.V = K.V →
      ∃ L : RootedLocation D.P.Γ, L.Isolates D.tb (n + 1) D.ord D.𝒯 ∧ (⟨hd, D.P, L⟩ : Place χ) ∈ B)
        := fun Kc ↦ by
    by_cases hg : Good Kc
    · obtain ⟨B, h₁, h₂⟩ := exists_class_free hS hd hcl n a₀ hS3 hS4 hg
      exact ⟨B, h₁, fun _ ↦ h₂⟩
    · exact ⟨∅, fun Ω hΩ seq hseq ↦ absurd (hseq 0) (notMem_empty _), fun h ↦ absurd h hg⟩
  choose B hBw hBm using hB
  have : Finite 𝓕 := hf
  refine ⟨⋃ K₀ : 𝓕, B (p K₀.1), IsWellBehavedPlaces.iUnion fun _ ↦ hBw _, ?_⟩
  intro D hm hfl
  obtain ⟨Δ, Z, K, hK⟩ := freedomFlaw D hfl
  have hord : n + 1 ≤ D.ord := by
    have h₁ := hfl.1
    have h₂ : D.rep ≤ D.ord := (tangleRep_spec D.rad D.ord D.𝒯).1
    omega
  obtain ⟨K₀, hK₀, f, hfp, hfU, hfV⟩ := h𝓕 K hK.feature hK.size
  have hg : Good K := ⟨D, Δ, Z, hK⟩
  obtain ⟨hg', g, hgp, hgU, hgV⟩ := hp K₀ K hg ⟨f, hfp, hfU, hfV⟩
  have hU : (g.symm.trans f) '' (p K₀).U = K.U := by
    have : (g.symm.trans f) '' (p K₀).U = f '' (g.symm '' (p K₀).U) := by
      rw [image_image]
      rfl
    rw [this, ← hgU, symm_image_image', hfU]
  have hV' : (g.symm.trans f) '' (p K₀).V = K.V := by
    have : (g.symm.trans f) '' (p K₀).V = f '' (g.symm '' (p K₀).V) := by
      rw [image_image]
      rfl
    rw [this, ← hgV, symm_image_image', hfV]
  obtain ⟨L, hL, hmem⟩ := hBm (p K₀) hg' D hm hord Δ Z K (g.symm.trans f) hK
    (hgp.symm.trans hfp) hU hV'
  exact ⟨L, hL, mem_iUnion.2 ⟨⟨K₀, hK₀⟩, hmem⟩⟩

end GraphMinor.GM19
