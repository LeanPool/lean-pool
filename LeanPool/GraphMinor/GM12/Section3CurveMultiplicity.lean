/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section2CyclicEmbedding
public import LeanPool.GraphMinor.GM12.Defs
import Mathlib.Data.Set.Card

/-!
# Counting hits of the short curves in XII (3.2)

For conditions (3.1)(ii)--(iii), the proof of XII (3.2), page 246,
traverses two circles and any joining line so that no drawing vertex
is visited more than twice. Label the visits with two labels, making
the pair consisting of the image point and its label injective. Hits
then inject into the drawing vertices of the shape times the label
set. A cyclic chain can be counted using the unique half-open
parameter piece of each circle parameter.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM07

/-- A normal curve whose visits can be distinguished by `m` labels
has length at most `m` times the number of drawing vertices in its
prescribed image set. The labelled injection also proves finiteness
of its parameter hit set. -/
theorem normal_curve_length_le_of_fibre_labels
    {S : Type*} [TopologicalSpace S] {Γ : Drawing S} {φ : C(Circle, S)}
    {X : Set S} (hX : Γ.IsNormal X) (hφX : range φ ⊆ X)
    {m : ℕ} (label : Circle → Fin m)
    (hinj : Function.Injective (fun z => (φ z, label z))) :
    IsNormalCurve Γ φ ∧ curveLength Γ φ ≤ m * (X ∩ Γ.V).ncard := by
  let H : Set Circle := {z | φ z ∈ Γ.U}
  let F : Circle → S × Fin m := fun z => (φ z, label z)
  let Y : Set (S × Fin m) := (X ∩ Γ.V) ×ˢ univ
  have hY : Y.Finite := (Γ.finite_V.subset inter_subset_right).prod (Set.toFinite univ)
  have hmaps : MapsTo F H Y := by
    intro z hz
    have hx : φ z ∈ X := hφX (mem_range_self z)
    exact ⟨⟨hx, hX ⟨hx, hz⟩⟩, mem_univ _⟩
  have hfinite : H.Finite := (hY.preimage hinj.injOn).subset hmaps
  have hn : Γ.IsNormal (range φ) := fun x hx => hX ⟨hφX hx.1, hx.2⟩
  have hcard := Set.ncard_le_ncard_of_injOn F hmaps hinj.injOn hY
  have hbound : H.ncard ≤ m * (X ∩ Γ.V).ncard := by
    change H.ncard ≤ ((X ∩ Γ.V) ×ˢ (univ : Set (Fin m))).ncard at hcard
    rw [Set.ncard_prod, Set.ncard_univ, Nat.card_fin] at hcard
    simpa only [Nat.mul_comm] using hcard
  exact ⟨⟨hfinite, hn⟩, hbound⟩

/-- Count a cyclic chain by labels on its half-open parameter pieces.
Equal image points with the same label must come from the same piece
and parameter. This is the two-visit counting mechanism in XII (3.2). -/
theorem concatLoop_length_le_of_piece_labels
    {S : Type*} [TopologicalSpace S] {Γ : Drawing S} {X : Set S}
    (hX : Γ.IsNormal X) {n : ℕ} (hn : 0 < n)
    (γ : Fin n → C(unitInterval, S))
    (hmatch : ∀ i, γ i 1 = γ (finNext hn i) 0)
    (hγX : ∀ i, range (γ i) ⊆ X)
    {m : ℕ} (label : Fin n → unitInterval → Fin m)
    (hsep : ∀ (i j : Fin n) (s t : unitInterval), s.val < 1 → t.val < 1 →
      γ i s = γ j t → label i s = label j t → i = j ∧ s = t) :
    IsNormalCurve Γ (concatLoop hn γ hmatch) ∧
      curveLength Γ (concatLoop hn γ hmatch) ≤ m * (X ∩ Γ.V).ncard := by
  classical
  let φ := concatLoop hn γ hmatch
  choose i t ht hz hφ using (fun z => concatLoop_point_representation hn γ hmatch z)
  let L : Circle → Fin m := fun z => label (i z) (t z)
  have hinj : Function.Injective (fun z => (φ z, L z)) := by
    intro z z' heq
    have hpoint := congrArg Prod.fst heq
    have hlabel := congrArg Prod.snd heq
    change concatLoop hn γ hmatch z = concatLoop hn γ hmatch z' at hpoint
    rw [hφ z, hφ z'] at hpoint
    change label (i z) (t z) = label (i z') (t z') at hlabel
    obtain ⟨hi, htime⟩ := hsep (i z) (i z') (t z) (t z') (ht z) (ht z') hpoint hlabel
    apply (hz z).trans
    rw [hi, htime]
    exact (hz z').symm
  have hφX : range φ ⊆ X := by
    rw [range_concatLoop]
    exact iUnion_subset hγX
  exact normal_curve_length_le_of_fibre_labels hX hφX L hinj

end GraphMinor.GM12
