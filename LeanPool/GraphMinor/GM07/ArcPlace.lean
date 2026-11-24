/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.DiscPlace
import LeanPool.GraphMinor.GM15.LineMove
import LeanPool.GraphMinor.Surface.DiscsInSurface

/-!
# Straightening arcs onto arcs

Step 2 of the proof of (9.1), page 243, takes "a homeomorphism of $\Sigma$ which fixes every point
of $bd(\Sigma)$ and maps the middle third of $f_i$
onto the whole of $e_i$ ($1 \le i \le r$)". This file proves that such a homeomorphism exists, for
any two families of disjoint lines off the
boundary (`exists_line_family_placement`).

The proof has three steps.
1. Each line lies in a closed disc that it crosses as a chord, and the discs of one family are
  disjoint (`exists_line_discs`).
2. A homeomorphism of the surface fixing the boundary moves the first discs onto the second ones,
  with the ends of each line going to the ends of
   the other line (`exists_disc_family_placement`).
3. In each disc of the second family we now have two chords with the same ends. A homeomorphism of
  the disc that fixes its boundary moves one chord
   onto the other (`GM15.exists_homeo_moving_line`), and it extends by the identity to the whole
   surface (`exists_homeo_of_disc`).
-/

public section

namespace GraphMinor.GM07

open Set Topology Function Metric GraphMinor.Surface

universe u

variable {S : Type u} [TopologicalSpace S]

/-- The frontier of a closed disc in a surface lies in the boundary of the disc: the points of the
disc off its boundary are the image of the
open ball under a chart, which is open. -/
theorem frontier_subset_discBd_of_surface [T2Space S] (hS : IsSurface S) {D : Set S}
  (hD : IsClosedDisc D) : frontier D ⊆ discBd D := by
  obtain ⟨h, g, c⟩ := hD.exists_isChart
  have hopen : IsOpen (g '' ball (0 : ℂ) 1) := c.isOpen_image_ball hS.2.2
  have hint : g '' ball (0 : ℂ) 1 ⊆ interior D := hopen.subset_interior_iff.mpr
    (c.g_subset ball_subset_closedBall)
  intro x ⟨hxc, hxi⟩
  have hxD : x ∈ D := hD.isCompact.isClosed.closure_eq ▸ hxc
  rw [← (c.union_ball).1] at hxD
  exact hxD.resolve_left fun hx => hxi (hint hx)

/-- A homeomorphism of a closed disc of a surface that fixes the boundary of the disc extends by the
identity to a homeomorphism of the
surface. -/
theorem exists_homeo_of_disc [T2Space S] (hS : IsSurface S) {D : Set S}
  (hD : IsClosedDisc D) {Ψ Ψ' : S → S} (h1 : MapsTo Ψ D D)
    (h2 : MapsTo Ψ' D D) (h3 : ContinuousOn Ψ D) (h4 : ContinuousOn Ψ' D) (h5 : LeftInvOn Ψ' Ψ D)
      (h6 : LeftInvOn Ψ Ψ' D)
    (h7 : ∀ x ∈ discBd D, Ψ x = x) : ∃ g : S ≃ₜ S, (∀ x ∈ D, g x = Ψ x) ∧ ∀ x ∉ D, g x = x := by
  classical
  have hDc : IsClosed D := hD.isCompact.isClosed
  have hfr := frontier_subset_discBd_of_surface hS hD
  have h7' : ∀ x ∈ discBd D, Ψ' x = x := fun x hx => by
    have := h5 (discBd_subset D hx)
    rwa [h7 x hx] at this
  have hc : ∀ {Φ : S → S}, ContinuousOn Φ D → (∀ x ∈ discBd D, Φ x = x) → Continuous fun x
    => if x ∈ D then Φ x else x := fun hΦ hΦb =>
    continuous_if (fun a ha => hΦb a (hfr ha)) (by rwa [Set.ofPred_mem_eq, hDc.closure_eq])
      continuous_id.continuousOn
  refine ⟨⟨⟨fun x => if x ∈ D then Ψ x else x, fun x => if x ∈ D then Ψ' x else x, fun x => ?_,
    fun x => ?_⟩, hc h3 h7, hc h4 h7'⟩,
    fun x hx => by simp [hx], fun x hx => by simp [hx]⟩
  · by_cases hx : x ∈ D
    · simp only [hx, h1 hx, ↓reduceIte]
      exact h5 hx
    · simp only [hx, ↓reduceIte]
  · by_cases hx : x ∈ D
    · simp only [hx, h2 hx, ↓reduceIte]
      exact h6 hx
    · simp only [hx, ↓reduceIte]

/-- The image of a line under a homeomorphism is a line, with the images of the ends as ends. -/
theorem isLineWithEnds_homeo_image {L : Set S} {a b : S} (hL : IsLineWithEnds L a b)
  (e : S ≃ₜ S) : IsLineWithEnds (e '' L) (e a) (e b) := by
  obtain ⟨f, hfa, hfb⟩ := hL
  refine ⟨f.trans (e.image L), ?_, ?_⟩
  · change e (f 0).1 = e a
    rw [hfa]
  · change e (f 1).1 = e b
    rw [hfb]

/-- The two ends of a line are distinct. -/
theorem ne_of_isLineWithEnds {L : Set S} {a b : S} (hL : IsLineWithEnds L a b) : a ≠ b := by
  obtain ⟨f, hfa, hfb⟩ := hL
  intro he
  have h1 : f 0 = f 1 := Subtype.ext (hfa.trans (he.trans hfb.symm))
  exact zero_ne_one (f.injective h1)

private theorem image_trans (φ ψ : S ≃ₜ S) (X : Set S) : (φ.trans ψ) '' X = ψ '' (φ '' X) := by
  rw [image_image]
  rfl

/-- Disjoint closed discs around finitely many disjoint lines off the boundary, each line a chord of
its disc. -/
theorem exists_line_discs [T2Space S] {M : Type} [TopologicalSpace M] (hM : IsSurface M)
  (h : S ≃ₜ M) {ι : Type*} [Finite ι] (L : ι → Set S)
    (a b : ι → S) (hL : ∀ i, IsLineWithEnds (L i) (a i) (b i)) (hLL : Pairwise fun i j => Disjoint
      (L i) (L j))
    (hLb : ∀ i, Disjoint (L i) (bd S)) :
    ∃ B : ι → Set S, (∀ i, IsClosedDisc (B i) ∧ L i ⊆ B i ∧ Disjoint (B i) (bd S) ∧ L i ∩ discBd
      (B i) = {a i, b i}) ∧
      Pairwise fun i j => Disjoint (B i) (B j) := by
  classical
  have hLc : ∀ i, IsClosed (L i) := fun i => GraphMinor.GM15.isClosed_of_isLineWithEnds (hL i)
  have key : ∀ F : Set ι, F.Finite → ∃ B : ι → Set S,
      (∀ i ∈ F, IsClosedDisc (B i) ∧ L i ⊆ B i ∧ Disjoint (B i) (bd S) ∧ L i ∩ discBd (B i)
        = {a i, b i}) ∧
      (∀ i ∈ F, ∀ j ∉ F, Disjoint (B i) (L j)) ∧ ∀ i ∈ F, ∀ j ∈ F, i ≠ j → Disjoint (B i) (B j)
        := by
    intro F hF
    induction F, hF using Set.Finite.induction_on with
    | empty => exact ⟨fun _ => ∅, by simp, by simp, by simp⟩
    | @insert i F hiF hF ih =>
      obtain ⟨B, h1, h2, h3⟩ := ih
      set Z : Set S := (⋃ j ∈ F, B j) ∪ ⋃ j ∈ (insert i F)ᶜ, L j with hZ
      have hZc : IsClosed Z := (hF.isClosed_biUnion fun j hj => (h1 j
        hj).1.isCompact.isClosed).union
        ((toFinite _).isClosed_biUnion fun j _ => hLc j)
      have hLZ : L i ⊆ Zᶜ := by
        rintro x hx (hxZ | hxZ)
        · obtain ⟨j, hj, hxB⟩ := mem_iUnion₂.mp hxZ
          exact disjoint_left.mp (h2 j hj i hiF) hxB hx
        · obtain ⟨j, hj, hxL⟩ := mem_iUnion₂.mp hxZ
          have hne : i ≠ j := fun he => hj (he ▸ mem_insert i F)
          exact disjoint_left.mp (hLL hne) hx hxL
      obtain ⟨D, hD1, hD2, hD3, hD4, -, -, hD7⟩ := exists_chord_disc hM h (hL i)
        (disjoint_iff_inter_eq_empty.mp (hLb i)) hZc.isOpen_compl hLZ
      have hDoff : ∀ j ∈ F, Disjoint D (B j) := fun j hj => by
        rw [disjoint_left]
        exact fun x hx hx' => hD3 hx (.inl (mem_iUnion₂.mpr ⟨j, hj, hx'⟩))
      have hne : ∀ j ∈ F, j ≠ i := fun j hj he => hiF (he ▸ hj)
      refine ⟨Function.update B i D, ?_, ?_, ?_⟩
      · rintro j (rfl | hj)
        · rw [Function.update_self]
          exact ⟨hD1, hD2, hD4, hD7⟩
        · rw [Function.update_of_ne (hne j hj)]
          exact h1 j hj
      · rintro j (rfl | hj) k hk
        · rw [Function.update_self, disjoint_left]
          exact fun x hx hx' => hD3 hx (.inr (mem_iUnion₂.mpr ⟨k, hk, hx'⟩))
        · rw [Function.update_of_ne (hne j hj)]
          exact h2 j hj k fun hk' => hk (.inr hk')
      · rintro j (rfl | hj) k (rfl | hk) hjk
        · exact absurd rfl hjk
        · rw [Function.update_self, Function.update_of_ne (hne k hk)]
          exact hDoff k hk
        · rw [Function.update_self, Function.update_of_ne (hne j hj)]
          exact (hDoff j hj).symm
        · rw [Function.update_of_ne (hne j hj), Function.update_of_ne (hne k hk)]
          exact h3 j hj k hk hjk
  obtain ⟨B, h1, -, h3⟩ := key univ (toFinite _)
  exact ⟨B, fun i => h1 i (mem_univ i), fun i j hij => h3 i (mem_univ i) j (mem_univ j) hij⟩

/-- **Straightening arcs.** Let `L i` and `L' i` be two finite families of lines, each family
pairwise disjoint and off the boundary. Then a
homeomorphism of the surface fixing every point of the boundary maps each `L i` onto `L' i`, with
the ends `a i, b i` going to `a' i, b' i`.
This is the homeomorphism of step 2 of (9.1), page 243, which "maps the middle third of $f_i$ onto
the whole of $e_i$". -/
theorem exists_line_family_placement (hS : IsSurface S) [ConnectedSpace S] {M : Type}
  [TopologicalSpace M] (hM : IsSurface M) (h : S ≃ₜ M)
    {ι : Type*} [Finite ι] (L L' : ι → Set S) (a b a' b' : ι → S) (hL : ∀ i, IsLineWithEnds (L i)
      (a i) (b i))
    (hL' : ∀ i, IsLineWithEnds (L' i) (a' i) (b' i)) (hLL : Pairwise fun i j => Disjoint (L i)
      (L j))
    (hLL' : Pairwise fun i j => Disjoint (L' i) (L' j)) (hLb : ∀ i, Disjoint (L i) (bd S))
      (hL'b : ∀ i, Disjoint (L' i) (bd S)) :
    ∃ ψ : S ≃ₜ S, (∀ x ∈ bd S, ψ x = x) ∧ ∀ i, ψ '' L i = L' i ∧ ψ (a i) = a' i ∧ ψ (b i) = b' i
      := by
  classical
  have ht2 : T2Space S := hS.2.1
  -- Step 1: discs around the lines.
  obtain ⟨A, hA, hAA⟩ := exists_line_discs hM h L a b hL hLL hLb
  obtain ⟨B, hB, hBB⟩ := exists_line_discs hM h L' a' b' hL' hLL' hL'b
  have hmem : ∀ {D L : Set S} {x y : S}, L ∩ discBd D = {x, y} → x ∈ discBd D ∧ y ∈ discBd D
    := fun {D L x y} he => by
    have hx : x ∈ L ∩ discBd D := he ▸ mem_insert x {y}
    have hy : y ∈ L ∩ discBd D := he ▸ mem_insert_of_mem x rfl
    exact ⟨hx.2, hy.2⟩
  -- Step 2: the discs `A i` go onto the discs `B i`, with the ends of the lines going to the ends.
  obtain ⟨e, hebd, he⟩ := exists_disc_family_placement hS A B (fun i => (hA i).1) (fun i =>
    (hB i).1) hAA hBB (fun i => (hA i).2.2.1)
    (fun i => (hB i).2.2.1) a b a' b' (fun i => (hmem (hA i).2.2.2).1) (fun i => (hmem
      (hA i).2.2.2).2) (fun i => ne_of_isLineWithEnds (hL i))
    (fun i => (hmem (hB i).2.2.2).1) (fun i => (hmem (hB i).2.2.2).2) (fun i
      => ne_of_isLineWithEnds (hL' i))
  -- Step 3: in each disc `B i`, the image of `L i` and the line `L' i` are chords with the same
  -- ends.
  have hchord : ∀ i, ∃ g : S ≃ₜ S, (∀ x ∉ B i, g x = x) ∧ (∀ x ∈ discBd (B i), g x = x) ∧ g ''
    (e '' L i) = L' i := by
    intro i
    obtain ⟨h1, h2, h3⟩ := he i
    have hline : IsLineWithEnds (e '' L i) (a' i) (b' i) := h2 ▸ h3 ▸ isLineWithEnds_homeo_image
      (hL i) e
    have hsub : e '' L i ⊆ B i := h1 ▸ image_mono (hA i).2.1
    have hbd : discBd (B i) = e '' discBd (A i) := by
      rw [← h1]
      exact (isClosedDisc_image_of_injOn (hA i).1 e.continuous e.injective.injOn).2
    have hcap : e '' L i ∩ discBd (B i) = {a' i, b' i} := by
      rw [hbd, ← image_inter e.injective, (hA i).2.2.2, image_pair, h2, h3]
    obtain ⟨Ψ, Ψ', m1, m2, c1, c2, l1, l2, hfix, himg⟩ := GraphMinor.GM15.exists_homeo_moving_line
      (hB i).1 (ne_of_isLineWithEnds (hL' i)) hline (hL' i) hsub
      (hB i).2.1 hcap (hB i).2.2.2
    obtain ⟨g, hg1, hg2⟩ := exists_homeo_of_disc hS (hB i).1 m1 m2 c1 c2 l1 l2 hfix
    refine ⟨g, hg2, fun x hx => (hg1 x (discBd_subset _ hx)).trans (hfix x hx), ?_⟩
    rw [← himg]
    exact image_congr fun x hx => hg1 x (hsub hx)
  choose g hg1 hg2 hg3 using hchord
  -- Compose the moves of the discs; each one is the identity off its disc.
  have key : ∀ F : Set ι, F.Finite → ∃ φ : S ≃ₜ S, (∀ x, (∀ j ∈ F, x ∉ B j) → φ x = x) ∧
    (∀ i ∈ F, φ '' (e '' L i) = L' i) ∧
      ∀ i, ∀ x ∈ discBd (B i), φ x = x := by
    intro F hF
    induction F, hF using Set.Finite.induction_on with
    | empty => exact ⟨Homeomorph.refl S, fun _ _ => rfl, by simp, fun _ _ _ => rfl⟩
    | @insert i F hiF hF ih =>
      obtain ⟨φ, hφ1, hφ2, hφ3⟩ := ih
      have hoff : ∀ {x : S} {j : ι}, x ∈ B j → ∀ k, k ≠ j → x ∉ B k := fun {x j} hx k hk hxk
        => disjoint_left.mp (hBB hk) hxk hx
      refine ⟨φ.trans (g i), fun x hx => ?_, ?_, fun k x hx => ?_⟩
      · rw [Homeomorph.trans_apply, hφ1 x fun j hj => hx j (.inr hj)]
        exact hg1 i x (hx i (mem_insert i F))
      · rintro j (rfl | hj)
        · have hfix : φ '' (e '' L j) = e '' L j := by
            refine (image_congr fun x hx => hφ1 x fun k hk => ?_).trans (image_id _)
            have hxB : x ∈ B j := (he j).1 ▸ image_mono (hA j).2.1 hx
            exact hoff hxB k fun hkj => hiF (hkj ▸ hk)
          rw [image_trans, hfix, hg3]
        · rw [image_trans, hφ2 j hj]
          refine (image_congr fun x hx => hg1 i x ?_).trans (image_id _)
          exact hoff ((hB j).2.1 hx) i fun hij => hiF (hij ▸ hj)
      · rw [Homeomorph.trans_apply, hφ3 k x hx]
        by_cases hki : k = i
        · subst hki
          exact hg2 k x hx
        · exact hg1 i x (hoff (discBd_subset _ hx) i (Ne.symm hki))
  obtain ⟨φ, hφ1, hφ2, hφ3⟩ := key univ (toFinite _)
  have hnotB : ∀ x ∈ bd S, ∀ j ∈ (univ : Set ι), x ∉ B j := fun x hx j _ hxB => disjoint_left.mp
    (hB j).2.2.1 hxB hx
  refine ⟨e.trans φ, fun x hx => ?_, fun i => ⟨?_, ?_, ?_⟩⟩
  · rw [Homeomorph.trans_apply, hebd x hx]
    exact hφ1 x (hnotB x hx)
  · rw [image_trans]
    exact hφ2 i (mem_univ i)
  · rw [Homeomorph.trans_apply, (he i).2.1]
    exact hφ3 i _ (hmem (hB i).2.2.2).1
  · rw [Homeomorph.trans_apply, (he i).2.2]
    exact hφ3 i _ (hmem (hB i).2.2.2).2

end GraphMinor.GM07
