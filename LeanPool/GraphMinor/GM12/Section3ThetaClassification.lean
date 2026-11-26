/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section3ThetaSurrounding
public import LeanPool.GraphMinor.GM12.Section3ThetaCover
public import LeanPool.GraphMinor.GM12.Section3ThetaSphere
import LeanPool.GraphMinor.GM12.Section3PuncturedCuffs
import LeanPool.GraphMinor.GM12.Section3PuncturedSurface
import LeanPool.GraphMinor.GM12.Section3SurroundingDisc
import LeanPool.GraphMinor.GM12.Section3SubspaceArcs

import LeanPool.GraphMinor.GM07.Section7
import LeanPool.GraphMinor.GM07.Bridge

/-!
# The third schismatic shape occurs on the three-cuff sphere

VII Section 8, page 241, used by XII (3.1), page 245, places the third
schismatic shape on the sphere with three cuffs. Its pair circles
surround distinct prescribed cuffs. Their enclosing discs cover the
original surface and exhaust its deletions. The covering-disc sphere
criterion then identifies the original surface as a sphere. This file
assembles those facts for the actual punctured surface.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface

universe u

/-- Three branch-pair circles surrounding distinct prescribed cuffs
force the original surface to be a sphere with exactly three deletions. -/
theorem sphere_card_three_of_surrounding_theta
    {S : Type u} {ι : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S] [Finite ι]
    (hS : IsClosedSurface S) (Δ : ι → Set S) (hΔ : ∀ i, IsClosedDisc (Δ i))
    (hdisj : Pairwise (fun i j => Disjoint (Δ i) (Δ j)))
    {P Q R : Set (discComplement Δ)} {a b : discComplement Δ} (hab : a ≠ b)
    (hP : IsLineWithEnds P a b) (hQ : IsLineWithEnds Q a b) (hR : IsLineWithEnds R a b)
    (hPQ : P ∩ Q = {a, b}) (hPR : P ∩ R = {a, b}) (hQR : Q ∩ R = {a, b})
    {i j k : ι} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hsPQ : GM07.SurroundsCuff (P ∪ Q) (Subtype.val ⁻¹' discBd (Δ i)))
    (hsPR : GM07.SurroundsCuff (P ∪ R) (Subtype.val ⁻¹' discBd (Δ j)))
    (hsQR : GM07.SurroundsCuff (Q ∪ R) (Subtype.val ⁻¹' discBd (Δ k))) :
    IsSphere S ∧ Nat.card ι = 3 := by
  let C := discComplement Δ
  let f : C → S := Subtype.val
  let P' := f '' P
  let Q' := f '' Q
  let R' := f '' R
  obtain ⟨D₀, hD₀, hb₀, hone₀⟩ := surrounding_bounds_disc_including_exactly_one hS Δ hΔ hdisj k
    (isOArc_union_of_lines_inter_eq_ends hQ hR hQR) hsQR
  obtain ⟨D₁, hD₁, hb₁, hone₁⟩ := surrounding_bounds_disc_including_exactly_one hS Δ hΔ hdisj j
    (isOArc_union_of_lines_inter_eq_ends hP hR hPR) hsPR
  obtain ⟨D₂, hD₂, hb₂, hone₂⟩ := surrounding_bounds_disc_including_exactly_one hS Δ hΔ hdisj i
    (isOArc_union_of_lines_inter_eq_ends hP hQ hPQ) hsPQ
  have hbd₀ : discBd D₀ = Q' ∪ R' := hb₀.trans (image_union f Q R)
  have hbd₁ : discBd D₁ = R' ∪ P' := hb₁.trans ((image_union f P R).trans (union_comm _ _))
  have hbd₂ : discBd D₂ = P' ∪ Q' := hb₂.trans (image_union f P Q)
  have hp : IsLineWithEnds P' a.val b.val := isLineWithEnds_subtype_image hP
  have hq : IsLineWithEnds Q' a.val b.val := isLineWithEnds_subtype_image hQ
  have hr : IsLineWithEnds R' a.val b.val := isLineWithEnds_subtype_image hR
  have hi : ∀ L M : Set C, L ∩ M = {a, b} → f '' L ∩ f '' M = {a.val, b.val} := by
    intro L M hLM
    rw [← image_inter Subtype.val_injective, hLM, image_pair]
  have hcover := theta_disc_cover_of_distinct_enclosed_labels hS Δ hp hq hr
    (hi P Q hPQ) (hi P R hPR) (hi Q R hQR) hD₀ hD₁ hD₂ hbd₀ hbd₁ hbd₂
    hjk.symm hik.symm hij.symm ((hone₀ k).mpr rfl) ((hone₁ j).mpr rfl) ((hone₂ i).mpr rfl)
    (fun l => (hone₀ l).mp) (fun l => (hone₁ l).mp) (fun l => (hone₂ l).mp)
  have hsub : P' ∪ Q' ∪ R' ⊆ C := by
    rintro x ((⟨y, _, rfl⟩ | ⟨y, _, rfl⟩) | ⟨y, _, rfl⟩) <;> exact y.property
  have hproper : P' ∪ Q' ∪ R' ≠ univ := by
    intro heq
    obtain ⟨x, hx⟩ := (hΔ i).nonempty_discInt
    have hxC := hsub (heq.symm ▸ mem_univ x)
    exact hx.2 (discComplement_inter_disc_subset_boundary hS Δ hΔ i ⟨hxC, hx.1⟩)
  have hbdsub : ∀ D : Set S, discBd D = Q' ∪ R' ∨ discBd D = R' ∪ P' ∨ discBd D = P' ∪ Q' →
      discBd D ⊆ C := by
    intro D hD
    rcases hD with h | h | h
    · rw [h]
      exact (union_subset (subset_union_right.trans subset_union_left) subset_union_right).trans
        hsub
    · rw [h]
      exact (union_subset subset_union_right (subset_union_left.trans subset_union_left)).trans hsub
    · rw [h]
      exact subset_union_left.trans hsub
  have hex := deletion_labels_exhaust_of_three_disc_cover hS Δ hΔ hD₀ hD₁ hD₂
    (hbdsub D₀ (Or.inl hbd₀)) (hbdsub D₁ (Or.inr (Or.inl hbd₁)))
    (hbdsub D₂ (Or.inr (Or.inr hbd₂))) hcover
    (fun l => (hone₀ l).mp) (fun l => (hone₁ l).mp) (fun l => (hone₂ l).mp)
  exact ⟨isSphere_of_covering_theta_discs hS (fun he => hab (Subtype.ext he)) hp hq hr
    (hi P Q hPQ) (hi P R hPR) (hi Q R hQR) hproper hD₀ hD₁ hD₂ hbd₀ hbd₁ hbd₂ hcover,
    card_eq_three_of_exhausting_labels hjk.symm hik.symm hij.symm hex⟩

/-- The sphere and three-cuff assertion for a schismatic theta in VII
Section 8, page 241, in the actual punctured surface used by XII (3.1).
The three surrounding labels are obtained from the proved cuff theorem. -/
theorem sphere_card_three_of_schismatic_theta
    {S : Type u} {ι : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    [Finite ι] [Nonempty ι]
    (hS : IsClosedSurface S) (Δ : ι → Set S) (hΔ : ∀ i, IsClosedDisc (Δ i))
    (hdisj : Pairwise (fun i j => Disjoint (Δ i) (Δ j)))
    {P Q R : Set (discComplement Δ)} {a b : discComplement Δ} (hab : a ≠ b)
    (hP : IsLineWithEnds P a b) (hQ : IsLineWithEnds Q a b) (hR : IsLineWithEnds R a b)
    (hPQ : P ∩ Q = {a, b}) (hPR : P ∩ R = {a, b}) (hQR : Q ∩ R = {a, b})
    (hX : GM07.IsSchismatic (P ∪ Q ∪ R)) : IsSphere S ∧ Nat.card ι = 3 := by
  let : ConnectedSpace (discComplement Δ) :=
    Subtype.connectedSpace (discComplement_isConnected hS Δ hΔ hdisj)
  obtain ⟨C₁, C₂, C₃, hs₁, hs₂, hs₃, h12, h13, h23⟩ :=
    surrounding_pairs_of_schismatic_theta (discComplement_isSurface hS Δ hΔ hdisj)
      (discComplement_cuffs_nonempty hS Δ hΔ hdisj) hab hP hQ hR hPQ hPR hQR hX
  have hc₁ := hs₁.1
  have hc₂ := hs₂.1
  have hc₃ := hs₃.1
  rw [discComplement_cuffs_eq hS Δ hΔ hdisj] at hc₁ hc₂ hc₃
  obtain ⟨i, rfl⟩ := hc₁
  obtain ⟨j, rfl⟩ := hc₂
  obtain ⟨k, rfl⟩ := hc₃
  exact sphere_card_three_of_surrounding_theta hS Δ hΔ hdisj hab hP hQ hR hPQ hPR hQR
    (fun he => h12 (congrArg (fun l => Subtype.val ⁻¹' discBd (Δ l)) he))
    (fun he => h13 (congrArg (fun l => Subtype.val ⁻¹' discBd (Δ l)) he))
    (fun he => h23 (congrArg (fun l => Subtype.val ⁻¹' discBd (Δ l)) he)) hs₁ hs₂ hs₃

end GraphMinor.GM12
