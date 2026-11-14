/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.BoundedDifference
public import LeanPool.ApollonianSuperharmonic.FourNeighborConnected
public import LeanPool.ApollonianSuperharmonic.FourNeighborLaplacian
public import LeanPool.ApollonianSuperharmonic.P4849T1MinimumTruncation
public import LeanPool.ApollonianSuperharmonic.P4849T1ComponentRestriction
public import LeanPool.ApollonianSuperharmonic.P4849T1PeriodResidues
public import LeanPool.ApollonianSuperharmonic.P4849T1LargePositiveComponents
public import LeanPool.ApollonianSuperharmonic.P4849T1PeriodAnchoring
public import LeanPool.ApollonianSuperharmonic.P4849T1SetDiagonalSubsequence
public import LeanPool.ApollonianSuperharmonic.P4849T1LocalLimitAdmissibility
public import LeanPool.ApollonianSuperharmonic.P4849T1InfiniteLimitComponent
public import Mathlib.Order.Int.LeastGreatest

-- [TABLET NODE: SufficientBoundedMaximality]

/-!
# SufficientBoundedMaximality

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem SufficientBoundedMaximality (g : IntegerLatticeFunction)
    (hlap : ∀ x, FourNeighborLaplacian g x ≤ 1)
    (hperiod : ∃ u v : GaussianInt,
      u.re * v.im - u.im * v.re ≠ 0 ∧
      (∀ x, FourNeighborLaplacian g (x + u) = FourNeighborLaplacian g x) ∧
      ∀ x, FourNeighborLaplacian g (x + v) = FourNeighborLaplacian g x)
    (hrigid : ∀ X : Set GaussianInt, X.Infinite → FourNeighborConnected X →
      (∀ x, FourNeighborLaplacian
        (fun y => g y + Set.indicator X (fun _ => (1 : ℤ)) y) x ≤ 1) →
      X = Set.univ) :
    ∀ f : IntegerLatticeFunction, (∀ x, g x ≤ f x) →
      (∀ x, FourNeighborLaplacian f x ≤ 1) → BoundedDifference f g := by
-- BODY
  classical
  intro f hfg hflap
  by_contra hnot
  obtain ⟨m, ⟨z₀, hz₀⟩, hmin⟩ := Int.exists_least_of_bdd
    (P := fun t => ∃ x, f x - g x = t)
    ⟨0, by rintro t ⟨x, rfl⟩; exact sub_nonneg.mpr (hfg x)⟩
    ⟨f 0 - g 0, 0, rfl⟩
  let q : IntegerLatticeFunction := fun x => f x - m - g x
  have hq (x : GaussianInt) : 0 ≤ q x := by
    have := hmin (f x - g x) ⟨x, rfl⟩
    dsimp [q]
    omega
  have hzero : ∃ z, q z = 0 := ⟨z₀, by dsimp [q]; omega⟩
  have hunbounded : ∀ B : ℤ, ∃ x, B < q x := by
    intro B
    by_contra hb
    push Not at hb
    apply hnot
    refine ⟨(B + m).natAbs, ?_⟩
    intro x
    have hx := hb x
    have hn := sub_nonneg.mpr (hfg x)
    have heq := Int.natAbs_of_nonneg hn
    have hB := Int.le_natAbs (a := B + m)
    dsimp [q] at hx
    omega
  have hplus : ∀ x, FourNeighborLaplacian (fun y => g y + q y) x ≤ 1 := by
    intro x
    have h := hflap x
    simp only [FourNeighborLaplacian, q] at h ⊢
    linarith
  have hS := P4849T1MinimumTruncation g q hlap hq hplus
  obtain ⟨u, v, hdet, hu, hv⟩ := hperiod
  obtain ⟨R, hres, hper⟩ :=
    P4849T1PeriodResidues (FourNeighborLaplacian g) u v hdet hu hv
  let M : ℕ := ∑ r ∈ R, (1 - FourNeighborLaplacian g r).natAbs
  have hM (x : GaussianInt) : 1 - FourNeighborLaplacian g x ≤ (M : ℤ) := by
    obtain ⟨r, hr, a, b, hx⟩ := hres x
    have hp : FourNeighborLaplacian g x = FourNeighborLaplacian g r := by
      rw [hx, hper a b r]
    have hrM : (1 - FourNeighborLaplacian g r).natAbs ≤ M :=
      Finset.single_le_sum (fun s _ => Nat.zero_le ((1 - FourNeighborLaplacian g s).natAbs)) hr
    rw [hp]
    have := Int.le_natAbs (a := 1 - FourNeighborLaplacian g r)
    omega
  have hqlap (x : GaussianInt) : FourNeighborLaplacian q x ≤ (M : ℤ) := by
    have hf := hflap x
    have hb := hM x
    simp only [FourNeighborLaplacian, q] at hf hb ⊢
    linarith
  have hfamily : ∀ N : ℕ, ∃ C : Set GaussianInt,
      FourNeighborConnected C ∧
      (∀ x, FourNeighborLaplacian
        (fun y => g y + Set.indicator C (fun _ => (1 : ℤ)) y) x ≤ 1) ∧
      ∃ z a : GaussianInt, z ∉ C ∧ a ∈ C ∧ FourNeighborAdjacent z a ∧
        ∃ F : Finset GaussianInt, (↑F : Set GaussianInt) ⊆ C ∧ N < F.card := by
    intro N
    obtain ⟨C, hC, z, a, hz, ha, hza, F, hF, hcard⟩ :=
      P4849T1LargePositiveComponents q M hq (by omega) hqlap hzero hunbounded N
    refine ⟨C, hC.1, P4849T1ComponentRestriction g _ C hlap hS hC,
      z, a, ?_, ha, hza, F, hF, hcard⟩
    intro hzc
    have hpos := hC.2.1 hzc
    change 0 < q z at hpos
    omega
  obtain ⟨z, a, C, hza, hC⟩ := P4849T1PeriodAnchoring g u v R hres hper hfamily
  obtain ⟨σ, hσ, L, hlocal⟩ := P4849T1SetDiagonalSubsequence C
  have hlarge (n : ℕ) : ∃ F : Finset GaussianInt,
      (↑F : Set GaussianInt) ⊆ C (σ n) ∧ n < F.card := by
    obtain ⟨F, hF, hcard⟩ := (hC (σ n)).2.2.2.2
    exact ⟨F, hF, lt_of_le_of_lt (hσ.id_le n) hcard⟩
  have hL := P4849T1LocalLimitAdmissibility g (fun n => C (σ n)) L
    (fun n => (hC (σ n)).2.2.2.1) hlocal
  obtain ⟨X, hX, hXinf, _, hzX⟩ :=
    P4849T1InfiniteLimitComponent (fun n => C (σ n)) L z a hza
      (fun n => (hC (σ n)).1) (fun n => (hC (σ n)).2.1)
      (fun n => (hC (σ n)).2.2.1) hlarge hlocal
  have hXlap := P4849T1ComponentRestriction g L X hlap hL hX
  have hXuniv := hrigid X hXinf hX.1 hXlap
  exact hzX (hXuniv.symm ▸ Set.mem_univ z)

end ApollonianSuperharmonic

end
