/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Defs
public import LeanPool.GraphMinor.Surface.ArcTools
import LeanPool.GraphMinor.GM07.NetSwapArcs
import LeanPool.GraphMinor.GM07.Section2MinVal

/-!
# Normality after exchanging a net subarc

In VII (2.6), page 218, the new seam is contained in the old
seam together with the image of the cutting line. Both sets
are normal. The seam graph of the new net therefore makes
it a normal net as well.
-/

public section
namespace GraphMinor.GM07
open Set Surface

/-- Every point on the exchanged seam comes from the old boundary
or from the cutting line. This is the normality containment used
in the new-net construction of VII (2.6), page 218. -/
theorem Net.seamU_subset_of_swap_maps
    {S : Type*} [TopologicalSpace S] (N M : Net S) (i : Fin N.r)
    (u v : unitInterval) (huv : u ≤ v)
    {F C A B : Set N.D}
    (hAd : discBd A = range (pieceA (N.f i) u.val v.val) ∪ F)
    (hBd : discBd B = C ∪ F)
    (hcover : range (pieceA (N.f i) u.val v.val) ∪ C = bd N.D)
    (ψ : A ⊕ B → M.D) (hψ : Function.Surjective ψ)
    (hφA : ∀ x : A, M.φ (ψ (Sum.inl x)) = N.φ x.val)
    (hφB : ∀ y : B, M.φ (ψ (Sum.inr y)) = N.φ y.val)
    (hαbd : ∀ x : A, ψ (Sum.inl x) ∈ bd M.D → x.val ∈ discBd A)
    (hβbd : ∀ y : B, ψ (Sum.inr y) ∈ bd M.D → y.val ∈ discBd B) :
    M.seamU ⊆ N.seamU ∪ N.φ '' F := by
  rintro z ⟨w, hw, rfl⟩
  obtain ⟨a, ha⟩ := hψ w
  cases a with
  | inl x =>
    rw [← ha, hφA]
    have hx := hαbd x (ha.symm ▸ hw)
    rcases hAd ▸ hx with hxf | hxF
    · have hxold : x.val ∈ bd N.D := by
        obtain ⟨t, _, htx⟩ := (range_pieceA_unitInterval (N.f i) u v huv).subset hxf
        exact N.range_f_subset_bd i ⟨t, htx⟩
      exact Or.inl ⟨x.val, hxold, rfl⟩
    · exact Or.inr ⟨x.val, hxF, rfl⟩
  | inr y =>
    rw [← ha, hφB]
    have hy := hβbd y (ha.symm ▸ hw)
    rcases hBd ▸ hy with hyC | hyF
    · exact Or.inl ⟨y.val, hcover ▸ Or.inr hyC, rfl⟩
    · exact Or.inr ⟨y.val, hyF, rfl⟩

/-- A net with the same positive number of pairs and a seam contained
in the union of two normal sets is normal. The existence of its seam
graph follows from the proved seam-graph construction for every net.
This supplies normality for the exchange in VII (2.6), page 218. -/
theorem Net.isNormalFor_of_swap_seam_subset
    {S : Type*} [TopologicalSpace S] (hS : IsSurface S) (N M : Net S)
    {G : Drawing S} {F : Set N.D} (hN : N.IsNormalFor G) (hr : M.r = N.r)
    (hU : M.seamU ⊆ N.seamU ∪ N.φ '' F) (hF : G.IsNormal (N.φ '' F)) :
    M.IsNormalFor G := by
  obtain ⟨J, hJN, hGJ⟩ := hN
  obtain ⟨K, hKM⟩ := M.exists_isSeamGraphFor hS (hr.symm ▸ hJN.1)
  refine ⟨K, hKM, ?_⟩
  intro z hz
  have hzM : z ∈ M.seamU := hKM.2.1 ▸ hz.1
  rcases hU hzM with hzN | hzF
  · exact hGJ ⟨hJN.2.1.symm ▸ hzN, hz.2⟩
  · exact hF ⟨hzF, hz.2⟩

end GraphMinor.GM07
