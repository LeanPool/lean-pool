/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Defs
import LeanPool.GraphMinor.GM16.Section9NestedZones
import Mathlib.Data.Set.Card

/-!
# Choosing an annulus untouched by the separator

After Claim (12) of XVI (8.1), Section 9 takes `κ` annuli at indices
spaced by `ψ + 5`. The gap between consecutive annuli is at least
three, so their closed point sets are disjoint. A set with fewer than
`κ` points misses one of them.
-/

public section
namespace GraphMinor.GM16
open Set GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM14
universe u w

/-- The pigeonhole argument after Claim (12) in XVI (8.1), page 74. -/
theorem exists_disjoint_of_pairwise_disjoint {α : Type u} {κ : ℕ}
    (A : Fin κ → Set α) (hDis : Pairwise (fun i j => Disjoint (A i) (A j)))
    (Z : Set α) (hZ : Z.Finite) (hCard : Z.ncard < κ) : ∃ i, Disjoint (A i) Z := by
  classical
  by_contra hn
  have hex : ∀ i, ∃ x, x ∈ A i ∧ x ∈ Z := by
    intro i
    have hNot : ¬ Disjoint (A i) Z := fun h => hn ⟨i, h⟩
    exact not_disjoint_iff.mp hNot
  choose x hxA hxZ using hex
  have hinj : Function.Injective x := by
    intro i j heq
    by_contra hij
    exact (hDis hij).notMem_of_mem_left (hxA i) (heq.symm ▸ hxA j)
  have hsub : range x ⊆ Z := range_subset_iff.mpr hxZ
  have hc := ncard_le_ncard hsub hZ
  rw [ncard_range_of_injective hinj, Nat.card_fin] at hc
  omega

variable {S : Type w} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]

/-- The annuli chosen after Claim (12) of XVI (8.1), page 74, are
pairwise disjoint. The inner and outer indices lie in the specified
range of the zone family. -/
theorem section9_annuli_pairwise_disjoint {H : Drawing S} {d : Set S → Set S → ℕ}
    {y : S} {M : ℕ → Set S} {β κ ψ : ℕ}
    (hκ : 3 ≤ κ) (hψ : 3 ≤ ψ)
    (hMax : κ + (κ - 1) * (ψ + 5) ≤ β - ψ - 5)
    (hM : ∀ i, 3 ≤ i → i ≤ β - 3 →
      IsLambdaZoneAround H d (i + 2) {y} (M i) ∧
      ∀ a ∈ H.A, d {y} a < i → a ⊆ M i) :
    Pairwise (fun r s : Fin κ =>
      Disjoint (closure (M (κ + r.val * (ψ + 5) + ψ + 2)) \ M (κ + r.val * (ψ + 5)))
        (closure (M (κ + s.val * (ψ + 5) + ψ + 2)) \ M (κ + s.val * (ψ + 5)))) := by
  have hIndex : ∀ r : Fin κ,
      3 ≤ κ + r.val * (ψ + 5) ∧ κ + r.val * (ψ + 5) + ψ + 2 ≤ β - 3 := by
    intro r
    have hr : r.val ≤ κ - 1 := by omega
    have hm := Nat.mul_le_mul_right (ψ + 5) hr
    omega
  have hOrdered : ∀ r s : Fin κ, r < s →
      Disjoint (closure (M (κ + r.val * (ψ + 5) + ψ + 2)) \ M (κ + r.val * (ψ + 5)))
        (closure (M (κ + s.val * (ψ + 5) + ψ + 2)) \ M (κ + s.val * (ψ + 5))) := by
    intro r s hrs
    have hmul := Nat.mul_le_mul_right (ψ + 5) (Nat.succ_le_of_lt hrs)
    rw [Nat.succ_mul] at hmul
    have hgap : κ + r.val * (ψ + 5) + ψ + 2 + 3 ≤ κ + s.val * (ψ + 5) := by omega
    have hr := hIndex r
    have hs := hIndex s
    have hSub := section9_nested_closures (hM _ (by omega) hr.2).1
      (hM _ hs.1 (by omega)).2 hgap
    exact disjoint_left.mpr fun x hx hy => hy.2 (hSub hx.1)
  intro r s hrs
  rcases lt_or_gt_of_ne hrs with hlt | hgt
  · exact hOrdered r s hlt
  · exact (hOrdered s r hgt).symm

/-- The clean annulus used for Claim (14) in XVI (8.1), page 74. -/
theorem section9_exists_clean_annulus {H : Drawing S} {d : Set S → Set S → ℕ}
    {y : S} {M : ℕ → Set S} {β κ ψ : ℕ}
    (hκ : 3 ≤ κ) (hψ : 3 ≤ ψ)
    (hMax : κ + (κ - 1) * (ψ + 5) ≤ β - ψ - 5)
    (hM : ∀ i, 3 ≤ i → i ≤ β - 3 →
      IsLambdaZoneAround H d (i + 2) {y} (M i) ∧
      ∀ a ∈ H.A, d {y} a < i → a ⊆ M i)
    (Z : Set S) (hZ : Z.Finite) (hCard : Z.ncard < κ) :
    ∃ r : Fin κ, Disjoint
      (closure (M (κ + r.val * (ψ + 5) + ψ + 2)) \ M (κ + r.val * (ψ + 5))) Z :=
  exists_disjoint_of_pairwise_disjoint _ (section9_annuli_pairwise_disjoint hκ hψ hMax hM) Z hZ
    hCard

end GraphMinor.GM16
