/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Hilbert.FilteredIntersection

/-! Balanced coordinate-power reductions imply eventual generation by a
linear parameter in arbitrary ambient dimension. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The degree filtration of the coordinate ring `MvPolynomial σ K ⧸ I` is increasing. -/
lemma filteredCoordinateSpace_mono {K σ : Type*} [Field K]
    (I : Ideal (MvPolynomial σ K)) {m n : ℕ} (hmn : m ≤ n) :
    filteredCoordinateSpace I m ≤ filteredCoordinateSpace I n := by
  apply Submodule.map_mono
  intro f hf
  exact (mem_restrictTotalDegree _ _ _).mpr (((mem_restrictTotalDegree _ _ _).mp hf).trans hmn)

/-- The degree filtration of the coordinate ring is multiplicative: a product of classes of
degree at most `m` and `n` has degree at most `m + n`. -/
lemma filteredCoordinateSpace_mul_mem {K σ : Type*} [Field K]
    (I : Ideal (MvPolynomial σ K)) {m n : ℕ} {x y : MvPolynomial σ K ⧸ I}
    (hx : x ∈ filteredCoordinateSpace I m) (hy : y ∈ filteredCoordinateSpace I n) :
    x * y ∈ filteredCoordinateSpace I (m + n) := by
  obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.mp hx
  obtain ⟨g, hg, rfl⟩ := Submodule.mem_map.mp hy
  apply Submodule.mem_map.mpr
  refine ⟨f * g, ?_, by simp⟩
  rw [mem_restrictTotalDegree] at hf hg ⊢
  exact (totalDegree_mul _ _).trans (Nat.add_le_add hf hg)

/-- An exponent vector of positive degree at least `Fintype.card σ * N` has some coordinate
at least `N`. -/
lemma large_exponent_of_degree {σ : Type*} [Fintype σ]
    (e : σ →₀ ℕ) (N : ℕ) (hpos : 0 < e.degree)
    (he : Fintype.card σ * N ≤ e.degree) : ∃ j, N ≤ e j := by
  classical
  by_contra! hn
  have hs := Finsupp.degree_eq_sum e
  have hnon : (Finset.univ : Finset σ).Nonempty := by
    by_contra h
    have hz : (Finset.univ : Finset σ) = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    rw [hz, Finset.sum_empty] at hs
    omega
  have hlt := Finset.sum_lt_sum_of_nonempty hnon (fun j _ => hn j)
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul] at hlt
  omega

/-- Let `l` have total degree at most `1`. If each coordinate power `X j ^ N` is congruent
modulo `I` to `r + l * s` with `r` and `s` of total degree at most `N - 1`, then for every
`n ≥ Fintype.card σ * N` the degree-`(n + 1)` piece of the filtered coordinate ring is the
degree-`n` piece plus `l` times the degree-`n` piece. -/
theorem eventual_generation_of_power_reductions {K σ : Type*} [Field K] [Fintype σ]
    (I : Ideal (MvPolynomial σ K)) (l : MvPolynomial σ K) (hl : l.totalDegree ≤ 1)
    (N : ℕ) (hN : 0 < N)
    (hpow : ∀ j : σ, ∃ r s : MvPolynomial σ K,
      r.totalDegree ≤ N - 1 ∧ s.totalDegree ≤ N - 1 ∧
      (Ideal.Quotient.mk I) (X j ^ N) = (Ideal.Quotient.mk I) r +
        (Ideal.Quotient.mk I) l * (Ideal.Quotient.mk I) s) :
    ∀ n ≥ Fintype.card σ * N, filteredCoordinateSpace I (n + 1) =
      filteredCoordinateSpace I n ⊔ (filteredCoordinateSpace I n).map
        (LinearMap.mulLeft K ((Ideal.Quotient.mk I) l)) := by
  classical
  intro n hn
  have hlmem : (Ideal.Quotient.mk I) l ∈ filteredCoordinateSpace I 1 :=
    ⟨l, (mem_restrictTotalDegree _ _ _).mpr hl, rfl⟩
  apply le_antisymm
  · have hmono (e : σ →₀ ℕ) (c : K) (he : e.degree ≤ n + 1) :
        (Ideal.Quotient.mk I) (monomial e c) ∈ filteredCoordinateSpace I n ⊔
          (filteredCoordinateSpace I n).map (LinearMap.mulLeft K ((Ideal.Quotient.mk I) l)) := by
      by_cases hsmall : e.degree ≤ n
      · apply (le_sup_left : filteredCoordinateSpace I n ≤ _)
        exact ⟨monomial e c, (mem_restrictTotalDegree _ _ _).mpr
          ((totalDegree_monomial_le e c).trans hsmall), rfl⟩
      have heq : e.degree = n + 1 := by omega
      obtain ⟨j, hj⟩ := large_exponent_of_degree e N (by omega) (by omega)
      obtain ⟨r, s, hr, hs, hrel⟩ := hpow j
      let u := e - Finsupp.single j N
      have hu : u + Finsupp.single j N = e := tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr hj)
      have hud : u.degree + N = e.degree := by
        simpa only [map_add, Finsupp.degree_single] using congrArg Finsupp.degree hu
      have hm : monomial e c = monomial u c * X j ^ N := by
        rw [X_pow_eq_monomial, monomial_mul_monomial, mul_one, hu]
      have hr' : (monomial u c * r).totalDegree ≤ n := by
        apply (totalDegree_mul _ _).trans
        have hh := totalDegree_monomial_le u c
        change (monomial u c).totalDegree ≤ u.degree at hh
        omega
      have hs' : (monomial u c * s).totalDegree ≤ n := by
        apply (totalDegree_mul _ _).trans
        have hh := totalDegree_monomial_le u c
        change (monomial u c).totalDegree ≤ u.degree at hh
        omega
      rw [hm, map_mul, hrel, mul_add]
      apply Submodule.add_mem
      · apply (le_sup_left : filteredCoordinateSpace I n ≤ _)
        exact ⟨monomial u c * r, (mem_restrictTotalDegree _ _ _).mpr hr', by simp⟩
      · apply (le_sup_right : (filteredCoordinateSpace I n).map
          (LinearMap.mulLeft K ((Ideal.Quotient.mk I) l)) ≤ _)
        refine ⟨(Ideal.Quotient.mk I) (monomial u c * s),
          ⟨monomial u c * s, (mem_restrictTotalDegree _ _ _).mpr hs', rfl⟩, ?_⟩
        simp only [LinearMap.mulLeft_apply, map_mul]
        ring
    intro x hx
    obtain ⟨f, hf, rfl⟩ := hx
    have hfd := (mem_restrictTotalDegree _ _ _).mp hf
    change (Ideal.Quotient.mk I) f ∈ _
    rw [← f.support_sum_monomial_coeff, map_sum]
    apply Submodule.sum_mem
    intro e he
    exact hmono e (f.coeff e) ((Finset.le_sup he).trans hfd)
  · apply sup_le
    · exact filteredCoordinateSpace_mono I (by omega)
    · rintro x ⟨y, hy, rfl⟩
      simpa only [LinearMap.mulLeft_apply, Nat.add_comm] using
        filteredCoordinateSpace_mul_mem I hlmem hy

end
end CCDN
