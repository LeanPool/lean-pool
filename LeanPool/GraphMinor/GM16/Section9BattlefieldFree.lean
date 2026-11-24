/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Cited
public import LeanPool.GraphMinor.GM15.Section4
import LeanPool.GraphMinor.GM16.Section9FreeFamily
import LeanPool.GraphMinor.GM16.Section9Compressions
import LeanPool.GraphMinor.GM16.Section9Dials
import LeanPool.GraphMinor.GM16.Section9ZonePreservation
import LeanPool.GraphMinor.GM11.Section810

import LeanPool.GraphMinor.GM11.CitedResults

import LeanPool.GraphMinor.GM12.Section710

import LeanPool.GraphMinor.GM12.Section77

/-!
# Free battlefield boundaries after all clearings

For Claim (3) in XVI (8.1), clear a chosen battlefield first. Its
boundary set is free by the definition of a battlefield. Separation
of the centres keeps this set far from every later clearing. The
uniqueness of the total compression identifies this order of clearing
with any previously chosen order.
-/

public section
namespace GraphMinor.GM16
open Set GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11 GraphMinor.GM14 GraphMinor.GM15
universe w
variable {S : Type w} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]

/-- Graph Minors XVI, proof of (8.1), Claim (3), page 72, including the
order-independence argument following the claim. The displayed parameter
bound below is supplied by Section 9's choices of constants. -/
theorem battlefield_free_after_clearFamily
     (hS : IsClosedSurface S)
    {H : Drawing S} {θ β sep : ℕ} {ys : Finset S}
    {Λ : S → Set S} {C : S → Drawing S} {X : S → Set S}
    {T T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d d' : Set S → Set S → ℕ} (hY : ∀ y ∈ ys, y ∈ H.V)
    (hBattle : ∀ y ∈ ys, IsBattlefield H T d θ β {y} (Λ y) (C y) (X y))
    (hdis : ∀ y ∈ ys, ∀ z ∈ ys, y ≠ z → Disjoint (closure (Λ y)) (closure (Λ z)))
    (hsep : ∀ y ∈ ys, ∀ z ∈ ys, y ≠ z → sep ≤ d {y} {z})
    (hparam : 2 * β + 6 * (3 * β + 3) + 2 + (4 * (3 * β + 3) + 2) * ys.card < sep)
    (hComp : IsLambdaCompression H (clearEnvelopeDrawing H (ys : Set S) Λ)
      θ ((4 * (3 * β + 3) + 2) * ys.card) T T' d d') :
    ∀ j ∈ ys, IsFreeSet (clearEnvelopeDrawing H (ys : Set S) Λ).toHypergraph T'
      (θ - (4 * (3 * β + 3) + 2) * ys.card) (X j) := by
  classical
  intro j hj
  let γ := 3 * β + 3
  let c := 4 * γ + 2
  let zs := ys.erase j
  have hcard : zs.card + 1 = ys.card := Finset.card_erase_add_one hj
  have hθj : c < θ := by
    have hc := hComp.lam_lt
    change c * ys.card < θ at hc
    have hmul := Nat.mul_le_mul_left c (show 1 ≤ ys.card by omega)
    omega
  obtain ⟨hXbd, hXcard, T₁, d₁, hClear, hFree₁⟩ := (hBattle j hj).isFree_X
  have hMet₁ : HasTangleMetric (clearedSubdrawing H (Λ j)) (θ - c) T₁ d₁ := by
    simpa only [γ, c, Nat.sub_sub] using hClear.hasMetric
  have hFree₁' : IsFreeSet (clearedSubdrawing H (Λ j)).toHypergraph T₁ (θ - c) (X j) := by
    simpa only [γ, c, Nat.sub_sub] using hFree₁
  have hZone := fun y hy => (hBattle y hy).isZone
  have hY₁ : ∀ y ∈ zs, y ∈ (clearedSubdrawing H (Λ j)).V := by
    intro y hy
    obtain ⟨hyj, hy⟩ := Finset.mem_erase.mp hy
    exact (mem_interSet_V_iff (isClosed_univ.sdiff (hZone j hj).isOpenDisc.1)).mpr
      ⟨hY y hy, mem_univ _, fun hyΩ => (hdis y hy j hj hyj).notMem_of_mem_left
        (subset_closure ((hZone y hy).z_subset (mem_singleton y))) (subset_closure hyΩ)⟩
  have hZone₁ : ∀ y ∈ zs,
      IsLambdaZoneAround (clearedSubdrawing H (Λ j)) d₁ γ {y} (Λ y) := by
    intro y hy
    obtain ⟨hyj, hy⟩ := Finset.mem_erase.mp hy
    exact zone_after_disjoint_clearing (hY y hy) (hZone y hy) (hZone j hj)
      (hdis y hy j hj hyj) hClear
  obtain ⟨_, _, _, hsymm, htri, _⟩ := GraphMinor.GM11.gm15_theorem_9_1.{w} H θ T d hS inferInstance
    hComp.hasMetric
  have hFar : ∀ y ∈ zs, ∀ v ∈ X j,
      2 * (X j).ncard + 5 * γ + 2 + c * zs.card < d₁ {y} {v} := by
    intro y hy v hv
    obtain ⟨hyj, hy⟩ := Finset.mem_erase.mp hy
    have hyA : ({y} : Set S) ∈ H.A := Or.inl (Or.inl ⟨y, hY y hy, rfl⟩)
    have hjA := (hZone j hj).z_mem
    have hvH := (hXbd hv).1
    have hvA : ({v} : Set S) ∈ H.A := Or.inl (Or.inl ⟨v, hvH, rfl⟩)
    have hdv := (hZone j hj).dist_le {v} hvA
      (singleton_subset_iff.mpr (hXbd hv).2.1)
    have htri' := htri {y} hyA {v} hvA {j} hjA
    rw [hsymm {v} hvA {j} hjA] at htri'
    have hsep' := hsep y hy j hj hyj
    have hc := (compression_of_clearing hComp.hasMetric hθj hClear).dist_le y v
    rw [pointDist_eq_of_mem_atom hyA hvA (mem_singleton y) (mem_singleton v),
      pointDist_eq_of_mem_atom (Or.inl (Or.inl ⟨y, hY₁ y (Finset.mem_erase.mpr ⟨hyj, hy⟩), rfl⟩))
        (Or.inl (Or.inl ⟨v, hFree₁'.1 hv, rfl⟩)) (mem_singleton y) (mem_singleton v)] at hc
    change d {y} {v} ≤ d₁ {y} {v} + c at hc
    change d {j} {v} ≤ γ at hdv
    change d {y} {j} ≤ d {y} {v} + d {j} {v} at htri'
    have hpc : 2 * β + 6 * γ + 2 + c * ys.card < sep := hparam
    rw [← hcard, Nat.mul_add c, Nat.mul_one] at hpc
    rw [hXcard]
    omega
  have hθrem : c * zs.card < θ - c := by
    have hc := hComp.lam_lt
    change c * ys.card < θ at hc
    rw [← hcard, Nat.mul_add, Nat.mul_one] at hc
    omega
  obtain ⟨T₂, d₂, hComp₂, _, hFree₂⟩ := exists_free_compression_clearFamily hS zs Λ γ
    (by dsimp [γ]; omega) (X j) hMet₁ hY₁ hZone₁
    (fun y hy z hz hne => hdis y (Finset.mem_of_mem_erase hy) z (Finset.mem_of_mem_erase hz) hne)
    hθrem hFree₁' hFar
  have hSet : insert j (zs : Set S) = (ys : Set S) := by
    rw [← Finset.coe_insert, Finset.insert_erase hj]
  have hDraw : clearEnvelopeDrawing (clearedSubdrawing H (Λ j)) (zs : Set S) Λ =
      clearEnvelopeDrawing H (ys : Set S) Λ := by
    have hopen : ∀ y ∈ insert j (zs : Set S), IsOpen (Λ y) := by
      intro y hy
      have hmem : y ∈ ys := by
        change y ∈ (ys : Set S)
        rw [← hSet]
        exact hy
      exact (hZone y hmem).isOpenDisc.1
    rw [clearFamily_after_single _ _ _ _ hopen, hSet]
  have hTot := compression_comp (compression_of_clearing hComp.hasMetric hθj hClear) hComp₂
  rw [hDraw] at hTot hFree₂
  have hLoss : c + c * zs.card = c * ys.card := by
    rw [← hcard, Nat.mul_add, Nat.mul_one, Nat.add_comm]
  rw [hLoss] at hTot
  have hT : T₂ = T' := compression_unique hS inferInstance hTot hComp
  rw [hT] at hFree₂
  have hOrder : θ - c - c * zs.card = θ - c * ys.card := by rw [Nat.sub_sub, hLoss]
  rw [hOrder] at hFree₂
  exact hFree₂

end GraphMinor.GM16
