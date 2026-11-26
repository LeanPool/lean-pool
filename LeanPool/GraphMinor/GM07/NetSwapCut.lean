/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Defs
public import LeanPool.GraphMinor.Surface.ArcTools
import LeanPool.GraphMinor.GM07.NetSwapBoundary
import LeanPool.GraphMinor.GM07.NetSwapPasting
import LeanPool.GraphMinor.Surface.InvarianceOfDomain

/-!
# The disc and surjection after exchanging a boundary subarc

For VII (2.6), page 218, cut along the proper line with both
ends inside one paired side. The piece cut off meets the old
boundary in that subarc. Its mate lies on the other piece.
Paste these two arcs by their original parameters and descend
the old associated surjection to the resulting closed disc.
-/

public section

namespace GraphMinor.GM07

open Set Topology Metric Surface

/-- Cut maps into the closed unit disc transfer to the net's disc with their fibers and boundary
conditions unchanged. -/
theorem Net.exists_transported_cut_maps {S : Type*} [TopologicalSpace S] (N : Net S)
    {A B : Set N.D} {ψ₀ : A ⊕ B → closedBall (0 : ℂ) 1} {φ₀ : closedBall (0 : ℂ) 1 → S}
    {R : A → B → Prop} {P : A → Prop} {Q : B → Prop}
    (hψ₀ : IsQuotientMap ψ₀) (hφ₀ : IsQuotientMap φ₀)
    (hφA : ∀ x : A, φ₀ (ψ₀ (Sum.inl x)) = N.φ x.val)
    (hφB : ∀ y : B, φ₀ (ψ₀ (Sum.inr y)) = N.φ y.val)
    (hiA : Function.Injective (ψ₀ ∘ Sum.inl)) (hiB : Function.Injective (ψ₀ ∘ Sum.inr))
    (hcross : ∀ x y, ψ₀ (Sum.inl x) = ψ₀ (Sum.inr y) ↔ R x y)
    (hαbd : ∀ x, ψ₀ (Sum.inl x) ∈ bd (closedBall (0 : ℂ) 1) ↔ P x)
    (hβbd : ∀ y, ψ₀ (Sum.inr y) ∈ bd (closedBall (0 : ℂ) 1) ↔ Q y) :
    ∃ e : closedBall (0 : ℂ) 1 ≃ₜ N.D,
      let α : A → N.D := e ∘ ψ₀ ∘ Sum.inl
      let β : B → N.D := e ∘ ψ₀ ∘ Sum.inr
      let φ : N.D → S := φ₀ ∘ e.symm
      Continuous α ∧ Continuous β ∧ Function.Injective α ∧ Function.Injective β ∧
        range α ∪ range β = univ ∧
        (∀ x y, α x = β y ↔ R x y) ∧
        (∀ x, α x ∈ bd N.D ↔ P x) ∧ (∀ y, β y ∈ bd N.D ↔ Q y) ∧
        IsQuotientMap φ ∧ (∀ x, φ (α x) = N.φ x.val) ∧ (∀ y, φ (β y) = N.φ y.val) := by
  obtain ⟨e₀⟩ := isClosedDisc_closedBall.1
  obtain ⟨eN⟩ := N.isClosedDisc_D
  let e : closedBall (0 : ℂ) 1 ≃ₜ N.D :=
    e₀.symm.trans (eN.trans (Homeomorph.Set.univ N.D))
  let α : A → N.D := e ∘ ψ₀ ∘ Sum.inl
  let β : B → N.D := e ∘ ψ₀ ∘ Sum.inr
  let φ : N.D → S := φ₀ ∘ e.symm
  have hT : range α ∪ range β = univ := by
    apply eq_univ_of_forall
    intro z
    obtain ⟨w, hw⟩ := hψ₀.surjective (e.symm z)
    cases w with
    | inl x => exact Or.inl ⟨x, (congrArg e hw).trans (e.apply_symm_apply z)⟩
    | inr y => exact Or.inr ⟨y, (congrArg e hw).trans (e.apply_symm_apply z)⟩
  refine ⟨e, e.continuous.comp (hψ₀.continuous.comp continuous_inl),
    e.continuous.comp (hψ₀.continuous.comp continuous_inr),
    e.injective.comp hiA, e.injective.comp hiB, hT,
    fun x y => e.injective.eq_iff.trans (hcross x y),
    fun x => (mem_bd_homeomorph_iff e _).trans (hαbd x),
    fun y => (mem_bd_homeomorph_iff e _).trans (hβbd y),
    hφ₀.comp e.symm.isQuotientMap, ?_, ?_⟩
  · intro x
    change φ₀ (e.symm (e (ψ₀ (Sum.inl x)))) = _
    rw [e.symm_apply_apply]
    exact hφA x
  · intro y
    change φ₀ (e.symm (e (ψ₀ (Sum.inr y)))) = _
    rw [e.symm_apply_apply]
    exact hφB y

/-- Cutting along a proper line between two interior parameters
of one paired side, then pasting that boundary subarc to its
mate, produces a disc with an associated quotient surjection
to the original surface. This is the geometric operation used
in VII (2.6), page 218. -/
theorem Net.exists_swap_disc
    {S : Type*} [TopologicalSpace S] [T2Space S] (N : Net S) (i : Fin N.r)
    (u v : unitInterval) (hu : 0 < u) (huv : u < v) (hv : v < 1)
    {F : Set N.D} (hF : IsLineWithEnds F (N.f i u) (N.f i v))
    (hFbd : F ∩ bd N.D = {N.f i u, N.f i v}) :
    ∃ (C A B : Set N.D) (ψ : A ⊕ B → closedBall (0 : ℂ) 1)
      (φ : closedBall (0 : ℂ) 1 → S),
      IsClosedDisc A ∧ IsClosedDisc B ∧ A ∪ B = univ ∧ A ∩ B = F ∧
      discBd A = range (pieceA (N.f i) u.val v.val) ∪ F ∧
      discBd B = C ∪ F ∧ range (pieceA (N.f i) u.val v.val) ∪ C = bd N.D ∧
      IsQuotientMap ψ ∧ IsQuotientMap φ ∧
      (∀ x : A, φ (ψ (Sum.inl x)) = N.φ x.val) ∧
      (∀ y : B, φ (ψ (Sum.inr y)) = N.φ y.val) ∧
      Function.Injective (ψ ∘ Sum.inl) ∧ Function.Injective (ψ ∘ Sum.inr) ∧
      (∀ (x : A) (y : B), ψ (Sum.inl x) = ψ (Sum.inr y) ↔
        ∃ t, x.val = pieceA (N.f i) u.val v.val t ∧
          y.val = pieceA (N.g i) u.val v.val t) ∧
      (∀ x : A, ψ (Sum.inl x) ∈ bd (closedBall (0 : ℂ) 1) ↔
        x.val ∈ discBd A ∧ x.val ∉ pieceA (N.f i) u.val v.val '' Ioo (0 : unitInterval) 1) ∧
      (∀ y : B, ψ (Sum.inr y) ∈ bd (closedBall (0 : ℂ) 1) ↔
        y.val ∈ discBd B ∧ y.val ∉ pieceA (N.g i) u.val v.val '' Ioo (0 : unitInterval) 1) := by
  let : T2Space N.D := N.isSurface_D.2.1
  let f := pieceA (N.f i) u.val v.val
  let g := pieceA (N.g i) u.val v.val
  have huv' : u.val < v.val := huv
  have hf : IsArcMap f := isArcMap_pieceA
    ⟨(N.f i).continuous, N.injective_f i⟩ u.property.1 huv' v.property.2
  have hg : IsArcMap g := isArcMap_pieceA
    ⟨(N.g i).continuous, N.injective_g i⟩ u.property.1 huv' v.property.2
  have hparam : ∀ t, ∃ w ∈ Ioo (0 : unitInterval) 1,
      f t = N.f i w ∧ g t = N.g i w := by
    intro t
    let z : ℝ := u.val + t.val * (v.val - u.val)
    have hmul0 : 0 ≤ t.val * (v.val - u.val) := mul_nonneg t.property.1 (sub_pos.mpr huv').le
    have hmul1 : t.val * (v.val - u.val) ≤ v.val - u.val := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right t.property.2 (sub_pos.mpr huv').le
    have hz0 : 0 < z := lt_of_lt_of_le hu (le_add_of_nonneg_right hmul0)
    have hz1 : z < 1 := lt_of_le_of_lt (by dsimp [z]; linarith) hv
    let w : unitInterval := ⟨z, hz0.le, hz1.le⟩
    refine ⟨w, ⟨hz0, hz1⟩, ?_, ?_⟩
    · exact extI_of_mem (N.f i) ⟨hz0.le, hz1.le⟩
    · exact extI_of_mem (N.g i) ⟨hz0.le, hz1.le⟩
  have hbd : discBd (univ : Set N.D) = bd N.D :=
    image_bd_homeomorph (Homeomorph.Set.univ N.D)
  have hfbd : range f ⊆ discBd (univ : Set N.D) := by
    rintro _ ⟨t, rfl⟩
    obtain ⟨w, hw, hfw, hgw⟩ := hparam t
    rw [hfw, hbd]
    exact N.range_f_subset_bd i ⟨w, rfl⟩
  have hgOld : range g ⊆ discBd (univ : Set N.D) := by
    rintro _ ⟨t, rfl⟩
    obtain ⟨w, hw, hfw, hgw⟩ := hparam t
    rw [hgw, hbd]
    exact N.range_g_subset_bd i ⟨w, rfl⟩
  have hfg : Disjoint (range f) (range g) := by
    apply disjoint_left.mpr
    rintro _ ⟨s, rfl⟩ ⟨t, hts⟩
    obtain ⟨w, hw, hfw, hgw⟩ := hparam s
    obtain ⟨z, hz, hfz, hgz⟩ := hparam t
    have heq : N.f i w = N.g i z := hfw.symm.trans (hts.symm.trans hgz)
    exact N.internally_disjoint_fg i i w hw ⟨z, heq.symm⟩
  have hf0 : f 0 = N.f i u := by
    change pieceA (N.f i) u.val v.val 0 = _
    rw [pieceA_zero, extI_coe]
  have hf1 : f 1 = N.f i v := by
    change pieceA (N.f i) u.val v.val 1 = _
    rw [pieceA_one, extI_coe]
  have hFl : IsLineWithEnds F (f 0) (f 1) := by rwa [hf0, hf1]
  have hFb : F ∩ discBd (univ : Set N.D) = {f 0, f 1} := by rwa [hbd, hf0, hf1]
  obtain ⟨C, A, B, hC, hcover, hA, hB, hAB, hI, hbA, hbB, hrest⟩ :=
    exists_disc_cut_with_boundary_arc N.isClosedDisc_D f hf hfbd hFl (subset_univ F) hFb
  have hgB : range g ⊆ discBd B := by
    intro x hx
    have hxf : x ∉ range f := fun h => disjoint_left.mp hfg h hx
    have hxC : x ∈ C := (hcover.symm ▸ hgOld hx).resolve_left hxf
    exact hbB ▸ Or.inl hxC
  have hαβ : ∀ t, N.φ (f t) = N.φ (g t) := by
    intro t
    obtain ⟨w, hw, hfw, hgw⟩ := hparam t
    rw [hfw, hgw]
    exact N.pasting_eq i w
  obtain ⟨ψ, φ, hψ, hcφ, hφA, hφB, hinl, hinr, hcross, hbψA, hbψB⟩ :=
    exists_map_on_pasted_disc hA hB f g hf hg (by intro x hx; exact hbA ▸ Or.inl hx)
      hgB N.φ N.φ N.quotientMap_φ.continuous.continuousOn
      N.quotientMap_φ.continuous.continuousOn hαβ
  have hsφ : Function.Surjective φ := by
    intro z
    obtain ⟨x, hx⟩ := N.quotientMap_φ.surjective z
    have hxAB : x ∈ A ∪ B := hAB.symm ▸ mem_univ x
    rcases hxAB with hxA | hxB
    · exact ⟨ψ (Sum.inl ⟨x, hxA⟩), (hφA ⟨x, hxA⟩).trans hx⟩
    · exact ⟨ψ (Sum.inr ⟨x, hxB⟩), (hφB ⟨x, hxB⟩).trans hx⟩
  have hcover' : range f ∪ C = bd N.D := hbd ▸ hcover
  exact ⟨C, A, B, ψ, φ, hA, hB, hAB, hI, hbA, hbB, hcover', hψ,
    IsQuotientMap.of_surjective_continuous hsφ hcφ, hφA, hφB, hinl, hinr, hcross, hbψA, hbψB⟩

/-- When the two members of a paired side lie on the boundaries of
the two cut pieces, pasting them produces a disc with an associated
quotient surjection to the same surface. This is the separating-pair
configuration of VII (2.6), page 218, after subdividing at the cutting
endpoint images. -/
theorem Net.exists_separating_pair_disc
    {S : Type*} [TopologicalSpace S] [T2Space S] (N : Net S) (i : Fin N.r)
    {A B : Set N.D} (hA : IsClosedDisc A) (hB : IsClosedDisc B)
    (hAB : A ∪ B = univ) (hfA : range (N.f i) ⊆ discBd A)
    (hgB : range (N.g i) ⊆ discBd B) :
    ∃ (ψ : A ⊕ B → closedBall (0 : ℂ) 1) (φ : closedBall (0 : ℂ) 1 → S),
      IsQuotientMap ψ ∧ IsQuotientMap φ ∧
      (∀ x : A, φ (ψ (Sum.inl x)) = N.φ x.val) ∧
      (∀ y : B, φ (ψ (Sum.inr y)) = N.φ y.val) ∧
      Function.Injective (ψ ∘ Sum.inl) ∧ Function.Injective (ψ ∘ Sum.inr) ∧
      (∀ (x : A) (y : B), ψ (Sum.inl x) = ψ (Sum.inr y) ↔
        ∃ t, x.val = N.f i t ∧ y.val = N.g i t) ∧
      (∀ x : A, ψ (Sum.inl x) ∈ bd (closedBall (0 : ℂ) 1) ↔
        x.val ∈ discBd A ∧ x.val ∉ N.f i '' Ioo (0 : unitInterval) 1) ∧
      (∀ y : B, ψ (Sum.inr y) ∈ bd (closedBall (0 : ℂ) 1) ↔
        y.val ∈ discBd B ∧ y.val ∉ N.g i '' Ioo (0 : unitInterval) 1) := by
  let : T2Space N.D := N.isSurface_D.2.1
  obtain ⟨ψ, φ, hψ, hcφ, hφA, hφB, hinl, hinr, hcross, hbA, hbB⟩ :=
    exists_map_on_pasted_disc hA hB (N.f i) (N.g i)
      ⟨(N.f i).continuous, N.injective_f i⟩ ⟨(N.g i).continuous, N.injective_g i⟩
      hfA hgB N.φ N.φ N.quotientMap_φ.continuous.continuousOn
      N.quotientMap_φ.continuous.continuousOn (N.pasting_eq i)
  have hsφ : Function.Surjective φ := by
    intro z
    obtain ⟨x, hx⟩ := N.quotientMap_φ.surjective z
    rcases hAB.symm ▸ mem_univ x with hxA | hxB
    · exact ⟨ψ (Sum.inl ⟨x, hxA⟩), (hφA ⟨x, hxA⟩).trans hx⟩
    · exact ⟨ψ (Sum.inr ⟨x, hxB⟩), (hφB ⟨x, hxB⟩).trans hx⟩
  exact ⟨ψ, φ, hψ, IsQuotientMap.of_surjective_continuous hsφ hcφ,
    hφA, hφB, hinl, hinr, hcross, hbA, hbB⟩

end GraphMinor.GM07
