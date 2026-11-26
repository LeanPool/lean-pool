/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Defs
public import LeanPool.GraphMinor.Surface.ArcTools
import LeanPool.GraphMinor.GM07.MinimalNet
import LeanPool.GraphMinor.GM07.NetSwapBasic
import LeanPool.GraphMinor.GM07.NetSwapArcs
import LeanPool.GraphMinor.GM07.NetSwapSides
import LeanPool.GraphMinor.GM07.NetSwapCounts
import LeanPool.GraphMinor.GM07.NetSwapPastingCounts
import LeanPool.GraphMinor.Surface.SurfaceGraph

/-!
# Exact boundary-contact balance for the exchanged net

Apply the finite cutting and pasting identities to the actual
pieces in VII (2.6), page 218. The endpoint contact sets agree
in the two identities and cancel. The remaining change is twice
the inner cutting-line contacts minus twice the open pasted-arc
contacts, with no allowance for endpoints.
-/

public section
namespace GraphMinor.GM07
open Set Surface

/-- The exact contact balance for the new net of VII (2.6), page 218.
The cutting endpoints contribute equally before cutting and after
pasting, including when their images belong to the finite set `V`. -/
theorem Net.swap_contact_balance
    {S : Type*} [TopologicalSpace S] (N M : Net S) (i : Fin N.r)
    (u v : unitInterval) (hu : 0 < u) (huv : u < v) (hv : v < 1)
    {F C A B : Set N.D} (hF : IsLineWithEnds F (N.f i u) (N.f i v))
    (hFbd : F ∩ bd N.D = {N.f i u, N.f i v}) (hI : A ∩ B = F)
    (hAd : discBd A = range (pieceA (N.f i) u.val v.val) ∪ F)
    (hBd : discBd B = C ∪ F)
    (hcover : range (pieceA (N.f i) u.val v.val) ∪ C = bd N.D)
    (α : A → M.D) (β : B → M.D)
    (hiα : Function.Injective α) (hiβ : Function.Injective β)
    (hT : range α ∪ range β = univ)
    (hcross : ∀ (x : A) (y : B), α x = β y ↔
      ∃ t, x.val = pieceA (N.f i) u.val v.val t ∧
        y.val = pieceA (N.g i) u.val v.val t)
    (hφA : ∀ x : A, M.φ (α x) = N.φ x.val)
    (hφB : ∀ y : B, M.φ (β y) = N.φ y.val)
    (hαbd : ∀ x : A, α x ∈ bd M.D ↔ x.val ∈ discBd A ∧
      x.val ∉ pieceA (N.f i) u.val v.val '' Ioo (0 : unitInterval) 1)
    (hβbd : ∀ y : B, β y ∈ bd M.D ↔ y.val ∈ discBd B ∧
      y.val ∉ pieceA (N.g i) u.val v.val '' Ioo (0 : unitInterval) 1)
    (V : Set S) (hV : V.Finite) :
    (bd M.D ∩ M.φ ⁻¹' V).ncard + 2 * (N.φ '' (N.f i '' Ioo u v) ∩ V).ncard =
      (bd N.D ∩ N.φ ⁻¹' V).ncard +
        2 * (N.φ '' (F \ {N.f i u, N.f i v}) ∩ V).ncard := by
  let a₀ := pieceA (N.f i) u.val v.val
  let b₀ := pieceA (N.g i) u.val v.val
  have ha₀ : IsArcMap a₀ := isArcMap_pieceA
    ⟨(N.f i).continuous, N.injective_f i⟩ u.property.1 huv v.property.2
  have haA : ∀ t, a₀ t ∈ A :=
    fun t => discBd_subset A (hAd ▸ Or.inl (mem_range_self t))
  obtain ⟨_, hmates, _, _⟩ := N.sides_on_retained_piece i u v hu huv hv hF hcover hBd
  have hbBd : ∀ t, b₀ t ∈ discBd B := by
    intro t
    obtain ⟨w, _, _, hgw⟩ := pieceA_common_parameter (N.f i) (N.g i) u v huv.le t
    exact hmates i ⟨w, hgw.symm⟩
  have hbB : ∀ t, b₀ t ∈ B := fun t => discBd_subset B (hbBd t)
  let a : unitInterval → A := fun t => ⟨a₀ t, haA t⟩
  let b : unitInterval → B := fun t => ⟨b₀ t, hbB t⟩
  let KA : Set A := {x | x.val ∈ discBd A}
  let KB : Set B := {x | x.val ∈ discBd B}
  have hai : Function.Injective a := fun s t h => ha₀.2 (congrArg Subtype.val h)
  have hcross' : ∀ x y, α x = β y ↔ ∃ t, x = a t ∧ y = b t := by
    intro x y
    rw [hcross]
    constructor
    · rintro ⟨t, hxt, hyt⟩
      exact ⟨t, Subtype.ext hxt, Subtype.ext hyt⟩
    · rintro ⟨t, rfl, rfl⟩
      exact ⟨t, rfl, rfl⟩
  have hAO : ∀ x : A, x ∈ a '' Ioo (0 : unitInterval) 1 ↔
      x.val ∈ a₀ '' Ioo (0 : unitInterval) 1 := by
    intro x
    constructor
    · rintro ⟨t, ht, htx⟩
      exact ⟨t, ht, congrArg Subtype.val htx⟩
    · rintro ⟨t, ht, htx⟩
      exact ⟨t, ht, Subtype.ext htx⟩
  have hBO : ∀ y : B, y ∈ b '' Ioo (0 : unitInterval) 1 ↔
      y.val ∈ b₀ '' Ioo (0 : unitInterval) 1 := by
    intro y
    constructor
    · rintro ⟨t, ht, hty⟩
      exact ⟨t, ht, congrArg Subtype.val hty⟩
    · rintro ⟨t, ht, hty⟩
      exact ⟨t, ht, Subtype.ext hty⟩
  have hBoundary : bd M.D = (α '' KA ∪ β '' KB) \ ((α ∘ a) '' Ioo (0 : unitInterval) 1) := by
    apply pasted_boundary_eq a b α β hiα hai hcross' hT KA KB _ _
    · intro x
      exact (hαbd x).trans (and_congr_right (fun _ => not_congr (hAO x).symm))
    · intro y
      exact (hβbd y).trans (and_congr_right (fun _ => not_congr (hBO y).symm))
  have hPAeq : KA ∩ (M.φ ∘ α) ⁻¹' V =
      {x : A | x.val ∈ discBd A ∩ N.φ ⁻¹' V} := by
    ext x
    change (x.val ∈ discBd A ∧ M.φ (α x) ∈ V) ↔ _
    rw [hφA]
    rfl
  have hPBeq : KB ∩ (M.φ ∘ β) ⁻¹' V =
      {x : B | x.val ∈ discBd B ∩ N.φ ⁻¹' V} := by
    ext x
    change (x.val ∈ discBd B ∧ M.φ (β x) ∈ V) ↔ _
    rw [hφB]
    rfl
  have hPre := N.finite_preimage_of_finite hV
  have hPA : (KA ∩ (M.φ ∘ α) ⁻¹' V).Finite := by
    rw [hPAeq]
    exact (Set.Finite.preimage Subtype.val_injective.injOn hPre).subset (fun _ h => h.2)
  have hPB : (KB ∩ (M.φ ∘ β) ⁻¹' V).Finite := by
    rw [hPBeq]
    exact (Set.Finite.preimage Subtype.val_injective.injOn hPre).subset (fun _ h => h.2)
  have hPACard : (KA ∩ (M.φ ∘ α) ⁻¹' V).ncard = (discBd A ∩ N.φ ⁻¹' V).ncard := by
    rw [hPAeq, ncard_subtype]
    congr 1
    exact inter_eq_left.mpr (fun _ h => discBd_subset A h.1)
  have hPBCard : (KB ∩ (M.φ ∘ β) ⁻¹' V).ncard = (discBd B ∩ N.φ ⁻¹' V).ncard := by
    rw [hPBeq, ncard_subtype]
    congr 1
    exact inter_eq_left.mpr (fun _ h => discBd_subset B h.1)
  have hOE : Disjoint (Ioo (0 : unitInterval) 1) ({0, 1} : Set unitInterval) := by
    apply disjoint_left.mpr
    rintro t ht (rfl | h1)
    · exact lt_irrefl _ ht.1
    · exact ht.2.ne (mem_singleton_iff.mp h1)
  have hCover : Ioo (0 : unitInterval) 1 ∪ ({0, 1} : Set unitInterval) = univ := by
    apply eq_univ_of_forall
    intro t
    by_cases ht0 : t = 0
    · exact Or.inr (Or.inl ht0)
    by_cases ht1 : t = 1
    · exact Or.inr (Or.inr ht1)
    exact Or.inl (Net.mem_Ioo_of_ne ht0 ht1)
  have hKA : range a ⊆ KA := by
    rintro x ⟨t, rfl⟩
    exact (show a₀ t ∈ discBd A from hAd ▸ Or.inl (mem_range_self t))
  have hKB : range b ⊆ KB := by
    rintro y ⟨t, rfl⟩
    exact hbBd t
  have hCount := ncard_pasting_contacts a b α β hiα hiβ hai hcross' KA KB hKA hKB
    (Ioo (0 : unitInterval) 1) {0, 1} hOE hCover M.φ V hPA hPB
  rw [← hBoundary, hPACard, hPBCard] at hCount
  have hMap : M.φ ∘ α ∘ a = N.φ ∘ a₀ := funext (fun t => hφA (a t))
  rw [hMap] at hCount
  have hτi : Function.Injective (N.φ ∘ a₀) := by
    intro s t hst
    have hSource : ∀ r, a₀ r ∈ N.f i '' Ioo (0 : unitInterval) 1 := by
      intro r
      obtain ⟨w, hw, hfw, _⟩ := pieceA_common_parameter (N.f i) (N.g i) u v huv.le r
      exact ⟨w, ⟨hu.trans_le hw.1, hw.2.trans_lt hv⟩, hfw.symm⟩
    exact ha₀.2 (N.injOn_image_open_side i (hSource s) (hSource t) hst)
  have hOpenCard : (Ioo (0 : unitInterval) 1 ∩ (N.φ ∘ a₀) ⁻¹' V).ncard =
      (N.φ '' (N.f i '' Ioo u v) ∩ V).ncard := by
    rw [← hτi.injOn.ncard_image, image_inter_preimage]
    rw [image_comp, image_pieceA_Ioo_unitInterval (N.f i) u v huv]
  have hEndCard : (({0, 1} : Set unitInterval) ∩ (N.φ ∘ a₀) ⁻¹' V).ncard =
      ({N.f i u, N.f i v} ∩ N.φ ⁻¹' V).ncard := by
    rw [← ha₀.2.injOn.ncard_image]
    change (a₀ '' (({0, 1} : Set unitInterval) ∩ a₀ ⁻¹' (N.φ ⁻¹' V))).ncard = _
    rw [image_inter_preimage]
    have hEnds : a₀ '' ({0, 1} : Set unitInterval) = {N.f i u, N.f i v} := by
      rw [image_pair]
      change {pieceA (N.f i) u.val v.val 0, pieceA (N.f i) u.val v.val 1} = _
      rw [pieceA_zero, pieceA_one, extI_coe, extI_coe]
    rw [hEnds]
  rw [hOpenCard, hEndCard] at hCount
  have hCut := N.ncard_cut_piece_contacts i u v hI hAd hBd hcover hFbd V hV
  omega

end GraphMinor.GM07
