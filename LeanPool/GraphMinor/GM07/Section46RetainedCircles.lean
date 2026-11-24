/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Defs
import LeanPool.GraphMinor.GM07.Section46CircleCuff
import LeanPool.GraphMinor.GM07.Section2Base
import LeanPool.GraphMinor.GM11.Walks
import LeanPool.GraphMinor.GM11.PaintingFacts
import LeanPool.GraphMinor.Surface.Classification

/-!
# Circles in `U(L)` and in `U(L) ∪ bd(Σ)`

The contact sum on page 226 of VII (4.6) lets hypothesis (ii) apply to
every circle in `U(L) ∪ bd(Σ)`. Normality follows from the normal seam
and properness of `G`. The disc-side argument says such a circle is a
cuff. No circle can lie in `U(L)`, since `L` is proper and its boundary
contacts are finite.
-/

public section

namespace GraphMinor.GM07

open Set GraphMinor.Surface GraphMinor.GM11

/-- Every circle in `U(L) ∪ bd(Σ)` is a cuff, as claimed in VII (4.6),
page 226. The contact bound is the local bound established just before
this claim in the paper. -/
theorem circles_in_retained_union_are_cuffs {S : Type*} [TopologicalSpace S]
    (hS : IsSurface S) (N : Net S) (hcuffs : 2 ≤ (cuffs S).ncard)
    {G J J' L : Drawing S} (hJ : N.IsSeamGraphFor J) (hG : G.IsProper)
    (hnorm : G.IsNormal J.U) (hL : L.IsSubdrawing J') (hU : J'.U = J.U)
    {v : ℕ} (hsum : (G.V ∩ L.U).ncard + (G.V ∩ bd S).ncard ≤ v)
    (hii : ∀ B : Set S, G.IsNormal B → IsOArc B → (G.V ∩ B).ncard ≤ v →
      IsNullHomotopicOArc B ∨
        ∃ C ∈ cuffs S, IsNullHomotopicOArcInCappedCuff C B ∧ G.V ∩ C ⊆ B)
    (hiii : ∀ C ∈ cuffs S, 2 ≤ (G.V ∩ C).ncard)
    {F : Set S} (hF : IsOArc F) (hFU : F ⊆ L.U ∪ bd S) : F ∈ cuffs S := by
  have : T2Space S := hS.2.1
  have hLU : L.U ⊆ J.U := hL.U_subset.trans hU.subset
  have hFN : G.IsNormal F := by
    rintro x ⟨hxF, hxG⟩
    rcases hFU hxF with hxL | hxbd
    · exact hnorm ⟨hLU hxL, hxG⟩
    · exact hG ⟨hxbd, hxG⟩
  have hsub : G.V ∩ F ⊆ (G.V ∩ L.U) ∪ (G.V ∩ bd S) := by
    rintro x ⟨hxV, hxF⟩
    rcases hFU hxF with hxL | hxbd
    · exact .inl ⟨hxV, hxL⟩
    · exact .inr ⟨hxV, hxbd⟩
  have hf₁ : (G.V ∩ L.U).Finite := G.finite_V.subset inter_subset_left
  have hf₂ : (G.V ∩ bd S).Finite := G.finite_V.subset inter_subset_left
  have hcount : (G.V ∩ F).ncard ≤ v :=
    ((ncard_le_ncard hsub (hf₁.union hf₂)).trans (ncard_union_le _ _)).trans hsum
  have hFseam : F ⊆ N.seamU := by
    intro x hx
    rcases hFU hx with hxL | hxbd
    · exact hJ.2.1 ▸ hLU hxL
    · exact N.bd_subset_seamU hxbd
  exact N.small_normal_circle_in_seam_is_cuff hS hcuffs hii hiii hF hFN hcount hFseam

/-- No circle lies in `U(L)`, in VII (4.6), page 226. -/
theorem not_isOArc_of_subset_retained {S : Type*} [TopologicalSpace S]
    (hS : IsSurface S) (N : Net S) (hcuffs : 2 ≤ (cuffs S).ncard)
    {G J J' L : Drawing S} (hJ : N.IsSeamGraphFor J) (hG : G.IsProper)
    (hnorm : G.IsNormal J.U) (hL : L.IsSubdrawing J') (hU : J'.U = J.U)
    (hLp : L.IsProper) {v : ℕ}
    (hsum : (G.V ∩ L.U).ncard + (G.V ∩ bd S).ncard ≤ v)
    (hii : ∀ B : Set S, G.IsNormal B → IsOArc B → (G.V ∩ B).ncard ≤ v →
      IsNullHomotopicOArc B ∨
        ∃ C ∈ cuffs S, IsNullHomotopicOArcInCappedCuff C B ∧ G.V ∩ C ⊆ B)
    (hiii : ∀ C ∈ cuffs S, 2 ≤ (G.V ∩ C).ncard)
    {F : Set S} (hFU : F ⊆ L.U) : ¬IsOArc F := by
  have : T2Space S := hS.2.1
  intro hF
  have hC := circles_in_retained_union_are_cuffs hS N hcuffs hJ hG hnorm hL hU
    hsum hii hiii hF (hFU.trans subset_union_left)
  have hbd : F ⊆ bd S := fun x hx => sUnion_cuffs (S := S) ▸ ⟨F, hC, hx⟩
  have hFV : F ⊆ L.V := fun x hx => hLp ⟨hbd hx, hFU hx⟩
  exact (infinite_of_isOArc hF) (L.finite_V.subset hFV)

end GraphMinor.GM07
