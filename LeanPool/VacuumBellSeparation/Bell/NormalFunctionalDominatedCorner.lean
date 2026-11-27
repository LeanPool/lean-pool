/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Bell.OrthogonalProjectionSupremum
public import LeanPool.VacuumBellSeparation.Bell.CornerProjectionFunctionalOrder
public import Mathlib.Order.Zorn
public import Mathlib.Data.Set.Pairwise.Basic

/-!
The maximal orthogonal-family argument for a positive order-normal functional.
The prescribed ambient corner r may be any nonzero projection. Domination is
concluded on every positive observable supported in the constructed corner;
it is not an input hypothesis or a field of a representation structure.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation.Bipartite

open Filter
open scoped Topology ComplexOrder InnerProductSpace BigOperators

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A strict comparison on r produces a nonzero subcorner on which the
inequality is reversed for all positive observables. The vector is arbitrary;
normality is used only at the actual arbitrary orthogonal supremum. -/
theorem exists_nonzero_dominated_subcorner_of_mass_lt (M : VonNeumannAlgebra H)
    (φ : M.toStarSubalgebra →ₚ[ℂ] ℂ) (hn : IsNormalFunctional M φ)
    (r : M.toStarSubalgebra) (hr : IsStarProjection r) (η : H)
    (hmass : (φ r).re < (vectorPositiveLinearMap M η r).re) :
    ∃ p : M.toStarSubalgebra, IsStarProjection p ∧ p ≠ 0 ∧ p ≤ r ∧
      ∀ a : M.toStarSubalgebra, 0 ≤ a → p * a = a →
        (φ a).re ≤ (vectorPositiveLinearMap M η a).re := by
  classical
  let ψ := vectorPositiveLinearMap M η
  let good : Set (Set M.toStarSubalgebra) := {s |
    (∀ p ∈ s, IsStarProjection p ∧ p ≠ 0 ∧ p ≤ r ∧ (ψ p).re ≤ (φ p).re) ∧
    s.Pairwise (fun p q => p * q = 0)}
  obtain ⟨s, hs⟩ : ∃ s, Maximal (· ∈ good) s := by
    apply zorn_subset
    intro c hc hchain
    refine ⟨⋃₀ c, ⟨?_, ?_⟩, fun t ht => Set.subset_sUnion_of_mem ht⟩
    · rintro p ⟨t, ht, hpt⟩
      exact (hc ht).1 p hpt
    · rintro p ⟨t, ht, hpt⟩ q ⟨u, hu, hqu⟩ hpq
      by_cases htu : t = u
      · subst u
        exact (hc ht).2 hpt hqu hpq
      · rcases hchain ht hu htu with htu | hut
        · exact (hc hu).2 (htu hpt) hqu hpq
        · exact (hc ht).2 hpt (hut hqu) hpq
  let P : s → M.toStarSubalgebra := fun i => i.1
  have hp (i : s) : IsStarProjection (P i) := (hs.prop.1 i.1 i.2).1
  have ho : Pairwise (fun i j : s => P i * P j = 0) := by
    intro i j hij
    exact hs.prop.2 i.2 j.2 (fun h => hij (Subtype.ext h))
  obtain ⟨Q, hQ, hsup, hPQ, _⟩ := exists_orthogonal_projection_supremum M P hp ho
  have hQr : Q ≤ r := by
    apply hsup.2
    rintro _ ⟨F, rfl⟩
    apply (isStarProjection_finite_sum_vna M P hp ho F).le_iff_mul_eq_right hr |>.mpr
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    exact (hp i).le_iff_mul_eq_right hr |>.mp (hs.prop.1 i.1 i.2).2.2.1
  have hcompare : (ψ Q).re ≤ (φ Q).re :=
    normalFunctional_comparison_orthogonal_supremum M φ ψ hn
      (vectorFunctional_isNormal M η) P hp (fun i => (hs.prop.1 i.1 i.2).2.2.2) Q hsup
  let p := r - Q
  have hpstar : IsStarProjection p := (hQ.le_iff_sub hr).mp hQr
  have hpr : p ≤ r := sub_le_self _ hQ.nonneg
  have hpne : p ≠ 0 := by
    intro hz
    have hQrEq : Q = r := (sub_eq_zero.mp hz).symm
    rw [hQrEq] at hcompare
    exact (not_le_of_gt hmass) hcompare
  have hpQ : p * Q = 0 := by
    dsimp only [p]
    rw [sub_mul, (hQ.le_iff_mul_eq_right hr).mp hQr, hQ.isIdempotentElem.eq, sub_self]
  have htest (q : M.toStarSubalgebra) (hq : IsStarProjection q) (hqp : q ≤ p) :
      (φ q).re ≤ (ψ q).re := by
    by_cases hqzero : q = 0
    · simp only [hqzero, map_zero, Complex.zero_re, le_refl]
    by_contra hbad
    have hbad' : (ψ q).re ≤ (φ q).re := (lt_of_not_ge hbad).le
    have hqQ : q * Q = 0 := by
      calc
        q * Q = (q * p) * Q := by rw [(hq.le_iff_mul_eq_left hpstar).mp hqp]
        _ = q * (p * Q) := mul_assoc _ _ _
        _ = 0 := by rw [hpQ, mul_zero]
    have hqs (b : M.toStarSubalgebra) (hb : b ∈ s) : q * b = 0 := by
      have hbQ := (hs.prop.1 b hb).1.le_iff_mul_eq_right hQ |>.mp (hPQ ⟨b, hb⟩)
      calc
        q * b = q * (Q * b) := by rw [hbQ]
        _ = (q * Q) * b := (mul_assoc _ _ _).symm
        _ = 0 := by rw [hqQ, zero_mul]
    have hinsert : insert q s ∈ good := by
      constructor
      · intro b hb
        rcases hb with rfl | hb
        · exact ⟨hq, hqzero, hqp.trans hpr, hbad'⟩
        · exact hs.prop.1 b hb
      · apply hs.prop.2.insert
        intro b hb hqb
        refine ⟨hqs b hb, ?_⟩
        simpa only [star_mul, hq.isSelfAdjoint.star_eq,
          (hs.prop.1 b hb).1.isSelfAdjoint.star_eq, star_zero] using congrArg star (hqs b hb)
    have hqin : q ∈ s := hs.mem_of_prop_insert hinsert
    have hqq : q * q = 0 := hqs q hqin
    exact hqzero (hq.isIdempotentElem.eq.symm.trans hqq)
  exact ⟨p, hpstar, hpne, hpr, fun a ha hpa =>
    positiveFunctional_re_le_on_corner_of_subprojections M p hpstar φ ψ htest a ha hpa⟩

/-- Every nonzero concrete projection has a vector in its range of arbitrarily
large norm. This does not assume the full Hilbert space is separable. -/
theorem exists_large_vector_in_projection (M : VonNeumannAlgebra H)
    (r : M.toStarSubalgebra) (hr : IsStarProjection r) (hne : r ≠ 0) (c : ℝ) :
    ∃ η : H, (r : H →L[ℂ] H) η = η ∧ c < ‖η‖ := by
  classical
  have hx : ∃ x : H, (r : H →L[ℂ] H) x ≠ 0 := by
    by_contra hh
    push Not at hh
    apply hne
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    exact hh
  obtain ⟨x, hx⟩ := hx
  let K : Submodule ℂ H := LinearMap.range (r : H →L[ℂ] H).toLinearMap
  let z : K := ⟨(r : H →L[ℂ] H) x, ⟨x, rfl⟩⟩
  let : Nontrivial K := ⟨⟨z, 0, fun h => hx (congrArg Subtype.val h)⟩⟩
  obtain ⟨η, hη⟩ := NormedSpace.exists_lt_norm ℂ K c
  refine ⟨η, ?_, hη⟩
  obtain ⟨y, hy⟩ := η.2
  rw [← hy]
  exact congrArg (fun T : M.toStarSubalgebra => (T : H →L[ℂ] H) y) hr.isIdempotentElem.eq

/-- The actual nonzero-corner conclusion needed at every step of a maximal
corner family. Neither a vector representation nor domination is assumed. -/
theorem exists_nonzero_vector_dominated_subcorner (M : VonNeumannAlgebra H)
    (φ : M.toStarSubalgebra →ₚ[ℂ] ℂ) (hn : IsNormalFunctional M φ)
    (r : M.toStarSubalgebra) (hr : IsStarProjection r) (hne : r ≠ 0) :
    ∃ (p : M.toStarSubalgebra) (η : H), IsStarProjection p ∧ p ≠ 0 ∧ p ≤ r ∧
      (r : H →L[ℂ] H) η = η ∧
      ∀ a : M.toStarSubalgebra, 0 ≤ a → p * a = a →
        (φ a).re ≤ (vectorPositiveLinearMap M η a).re := by
  obtain ⟨η, hrη, hη⟩ := exists_large_vector_in_projection M r hr hne
    (Real.sqrt (φ r).re + 1)
  have hpos : 0 ≤ (φ r).re := (Complex.le_def.mp (map_nonneg φ hr.nonneg)).1
  have hmass : (φ r).re < (vectorPositiveLinearMap M η r).re := by
    change (φ r).re < (inner ℂ η ((r : H →L[ℂ] H) η)).re
    have hi : (inner ℂ η η).re = ‖η‖ ^ 2 :=
      inner_self_eq_norm_sq (𝕜 := ℂ) η
    rw [hrη, hi]
    nlinarith [Real.sq_sqrt hpos, Real.sqrt_nonneg (φ r).re, norm_nonneg η]
  obtain ⟨p, hp, hpne, hpr, hdom⟩ :=
    exists_nonzero_dominated_subcorner_of_mass_lt M φ hn r hr η hmass
  exact ⟨p, η, hp, hpne, hpr, hrη, hdom⟩

/-- The zero Hilbert space has only the zero positive functional. No nonzero
corner conclusion is asserted at this boundary. -/
theorem positiveFunctional_eq_zero_of_subsingleton [Subsingleton H]
    (M : VonNeumannAlgebra H) (φ : M.toStarSubalgebra →ₚ[ℂ] ℂ) : φ = 0 := by
  ext a
  have ha : a = 0 := Subtype.ext (Subsingleton.elim _ _)
  simp only [ha, map_zero]

end VacuumBellSeparation.Bipartite
