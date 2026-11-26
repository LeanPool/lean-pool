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
  let Data : TangleDatum cap χ → Drawing S → Prop :=
    fun D K => ∃ Δ Z : Set Shat, IsFreeData D n Δ Z K
  obtain ⟨B, hB, hMem⟩ := exists_wellBehavedPlaces_of_bounded_features hd (𝒮 := 𝒮)
    (8 * n) (n + 1) Data (fun Kc hGood => by
      obtain ⟨B, hB, hMem⟩ := exists_class_free hS hd hcl n a₀ hS3 hS4 (Kc := Kc) hGood
      refine ⟨B, hB, ?_⟩
      rintro D hm hord K ⟨Δ, Z, hData⟩ ⟨f, hfp, hfU, hfV⟩
      exact hMem D hm hord Δ Z K f hData hfp hfU hfV)
  refine ⟨B, hB, fun D hm hfl => ?_⟩
  obtain ⟨Δ, Z, K, hK⟩ := freedomFlaw D hfl
  have hord : n + 1 ≤ D.ord := by
    have h₁ := hfl.1
    have h₂ : D.rep ≤ D.ord := (tangleRep_spec D.rad D.ord D.𝒯).1
    omega
  exact hMem D hm hord K ⟨Δ, Z, hK⟩ hK.feature hK.size

end GraphMinor.GM19
