/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM15.Defs
public import LeanPool.GraphMinor.GM15.Section4
import LeanPool.GraphMinor.GM14.Section3

import LeanPool.GraphMinor.GM12.Section77

/-!
# Composing the compressions in XVI (8.1)

The clearings in Section 9 lose `4γ + 2` units of order each. Their
metric losses add.
-/

public section
namespace GraphMinor.GM16
open Set GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM14 GraphMinor.GM15
universe w
variable {S : Type w} [TopologicalSpace S] [T2Space S]

/-- The losses in two successive compressions add, as used in the proof
of Graph Minors XVI, (8.1), page 71. -/
theorem compression_comp {H H₁ H₂ : Drawing S} {θ lam₁ lam₂ : ℕ}
    {T T₁ T₂ : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d d₁ d₂ : Set S → Set S → ℕ}
    (h₁ : IsLambdaCompression H H₁ θ lam₁ T T₁ d d₁)
    (h₂ : IsLambdaCompression H₁ H₂ (θ - lam₁) lam₂ T₁ T₂ d₁ d₂) :
    IsLambdaCompression H H₂ θ (lam₁ + lam₂) T T₂ d d₂ := by
  refine ⟨by have := h₂.lam_lt; omega, h₁.hasMetric, ?_, ?_⟩
  · simpa only [Nat.sub_sub] using h₂.hasMetric'
  · intro x y
    have hxy₁ := h₁.dist_le x y
    have hxy₂ := h₂.dist_le x y
    omega

/-- Uniqueness of the total compression used in XVI (8.1), page 72.
Apply XV (4.1) in both directions, using one radial drawing for both
representations. XII (7.7) identifies the metrics of the second tangle. -/
theorem compression_unique
    {H H' : Drawing S} {θ lam : ℕ}
    {T T₁ T₂ : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d d₁ d₂ : Set S → Set S → ℕ} (hS : IsClosedSurface S) (hConn : ConnectedSpace S)
    (h₁ : IsLambdaCompression H H' θ lam T T₁ d d₁)
    (h₂ : IsLambdaCompression H H' θ lam T T₂ d d₂) : T₁ = T₂ := by
  obtain ⟨_, K, ins₁, hK, hins₁, hd₁⟩ := h₁.hasMetric'
  obtain ⟨ins₂, hins₂⟩ := exists_derivedSlope h₂.hasMetric'.1 hK.2.1
  let d₂K := tangleMetric H' K ins₂ (θ - lam)
  have hM₂K : HasTangleMetric H' (θ - lam) T₂ d₂K :=
    ⟨h₂.hasMetric'.1, K, ins₂, hK, hins₂, fun _ _ _ _ => rfl⟩
  have hEq := (tangleMetric_eq_of_hasTangleMetric hS hConn h₂.hasMetric' hM₂K).2.1
  have h₂K : IsLambdaCompression H H' θ lam T T₂ d d₂K :=
    ⟨h₂.lam_lt, h₂.hasMetric, hM₂K, fun x y => by rw [← hEq x y]; exact h₂.dist_le x y⟩
  have h12 := (GraphMinor.GM15.theorem_4_1_proof.{w} H H' H' K K θ lam lam T T₁ T₂ d d₁ d₂K ins₁
    ins₂
    hS h₁ h₂K hK hins₁ hd₁ hK hins₂ (fun _ _ _ _ => rfl)).2 rfl rfl le_rfl
  have h21 := (GraphMinor.GM15.theorem_4_1_proof.{w} H H' H' K K θ lam lam T T₂ T₁ d d₂K d₁ ins₂
    ins₁
    hS h₂K h₁ hK hins₂ (fun _ _ _ _ => rfl) hK hins₁ hd₁).2 rfl rfl le_rfl
  exact subset_antisymm h12 h21

/-- A clearing is a compression with loss `4γ + 2`. The point distances
are compared by taking the atoms containing the two points. -/
theorem compression_of_clearing {H : Drawing S} {θ γ : ℕ} {Λ : Set S}
    {T T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d d' : Set S → Set S → ℕ} (hMet : HasTangleMetric H θ T d)
    (hθ : 4 * γ + 2 < θ) (hClear : IsClearedTangle H T d θ γ Λ T' d') :
    IsLambdaCompression H (clearedSubdrawing H Λ) θ (4 * γ + 2) T T' d d' := by
  refine ⟨hθ, hMet, ?_, ?_⟩
  · simpa only [Nat.sub_sub] using hClear.hasMetric
  · intro x y
    obtain ⟨a, ha, hxa⟩ := exists_atom_of_point H x
    obtain ⟨b, hb, hyb⟩ := exists_atom_of_point H y
    obtain ⟨a', ha', hxa'⟩ := exists_atom_of_point (clearedSubdrawing H Λ) x
    obtain ⟨b', hb', hyb'⟩ := exists_atom_of_point (clearedSubdrawing H Λ) y
    have hSub := clearedSubdrawing_isSubdrawing H Λ
    have hbound := (hClear.dist_bounds a ha b hb a' ha' b' hb'
      (atom_subset_of_isSubdrawing hSub ha ha' hxa hxa')
      (atom_subset_of_isSubdrawing hSub hb hb' hyb hyb')).1
    rw [pointDist_eq_of_mem_atom ha hb hxa hyb,
      pointDist_eq_of_mem_atom ha' hb' hxa' hyb']
    omega

/-- Clearing does not increase point distances. Together with the preceding
compression bound this gives both metric comparisons used in XVI (8.1). -/
theorem clearing_pointDist_le {H : Drawing S} {θ γ : ℕ} {Λ : Set S}
    {T T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d d' : Set S → Set S → ℕ} (hClear : IsClearedTangle H T d θ γ Λ T' d')
    (x y : S) : pointDist (clearedSubdrawing H Λ) d' x y ≤ pointDist H d x y := by
  obtain ⟨a, ha, hxa⟩ := exists_atom_of_point H x
  obtain ⟨b, hb, hyb⟩ := exists_atom_of_point H y
  obtain ⟨a', ha', hxa'⟩ := exists_atom_of_point (clearedSubdrawing H Λ) x
  obtain ⟨b', hb', hyb'⟩ := exists_atom_of_point (clearedSubdrawing H Λ) y
  have hSub := clearedSubdrawing_isSubdrawing H Λ
  rw [pointDist_eq_of_mem_atom ha hb hxa hyb,
    pointDist_eq_of_mem_atom ha' hb' hxa' hyb']
  exact (hClear.dist_bounds a ha b hb a' ha' b' hb'
    (atom_subset_of_isSubdrawing hSub ha ha' hxa hxa')
    (atom_subset_of_isSubdrawing hSub hb hb' hyb hyb')).2

end GraphMinor.GM16
