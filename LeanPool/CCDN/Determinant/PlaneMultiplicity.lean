/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Determinant.SingularPlaneChart

/-! Positive singular multiplicity is derived from a nonzero equation
vanishing at the origin; it is bounded by the equation's total degree. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The first nonzero homogeneous component realizes the order at the origin. -/
theorem exists_origin_multiplicity {K σ : Type*} [Field K]
    (f : MvPolynomial σ K) (hf : f ≠ 0) (hz : eval (0 : σ → K) f = 0) :
    ∃ μ : ℕ, 0 < μ ∧ μ ≤ f.totalDegree ∧
      f ∈ idealOfVars σ K ^ μ ∧ homogeneousComponent μ f ≠ 0 := by
  classical
  have hex : ∃ n, homogeneousComponent n f ≠ 0 := by
    by_contra h
    push Not at h
    apply hf
    rw [← sum_homogeneousComponent f]
    simp only [h, Finset.sum_const_zero]
  let μ := Nat.find hex
  have hμ : homogeneousComponent μ f ≠ 0 := Nat.find_spec hex
  have hpow : f ∈ idealOfVars σ K ^ μ := by
    rw [mem_pow_idealOfVars_iff']
    intro e he
    have hzero : homogeneousComponent e.degree f = 0 :=
      not_not.mp (Nat.find_min hex he)
    have hc := congrArg (fun u : MvPolynomial σ K => u.coeff e) hzero
    simpa [coeff_homogeneousComponent] using hc
  have hpos : 0 < μ := by
    by_contra h
    have he : μ = 0 := by omega
    have hconst : f.coeff 0 = 0 := by simpa only [eval_zero, constantCoeff_eq] using hz
    apply hμ
    rw [he, homogeneousComponent_zero, hconst, map_zero]
  have hdeg : μ ≤ f.totalDegree := by
    by_contra h
    exact hμ (homogeneousComponent_eq_zero μ f (by omega))
  exact ⟨μ, hpos, hdeg, hpow, hμ⟩

/-- Substituting affine linear polynomials does not increase total degree. -/
theorem linear_eval₂_totalDegree_le {R S σ τ : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (g : σ → MvPolynomial τ S) (hg : ∀ j, (g j).totalDegree ≤ 1)
    (f : MvPolynomial σ R) :
    (eval₂Hom (C.comp φ) g f).totalDegree ≤ f.totalDegree := by
  classical
  conv_lhs => rw [f.as_sum, map_sum]
  apply totalDegree_finsetSum_le
  intro e he
  rw [eval₂Hom_monomial, RingHom.comp_apply]
  apply (totalDegree_mul _ _).trans
  rw [totalDegree_C, zero_add]
  change (∏ j ∈ e.support, g j ^ e j).totalDegree ≤ f.totalDegree
  calc _ ≤ ∑ j ∈ e.support, (g j ^ e j).totalDegree := totalDegree_finsetProd _ _
    _ ≤ ∑ j ∈ e.support, e j := by
      apply Finset.sum_le_sum
      intro j _
      exact (totalDegree_pow _ _).trans (by simpa using Nat.mul_le_mul_left (e j) (hg j))
    _ ≤ f.totalDegree := le_totalDegree he

/-- A reduced hypersurface point determines a positive, degree-bounded
multiplicity in every ambient dimension. -/
theorem exists_hypersurface_reduction_multiplicity {p : ℕ} [Fact p.Prime] {σ : Type*}
    (f : MvPolynomial σ ℤ) (a : σ → ℤ)
    (hf : map (Int.castRingHom (ZMod p)) f ≠ 0)
    (ha : eval₂ (Int.castRingHom (ZMod p)) (fun j => (a j : ZMod p)) f = 0) :
    ∃ μ : ℕ, 0 < μ ∧ μ ≤ f.totalDegree ∧
      map (Int.castRingHom (ZMod p)) (originShift a f) ∈ idealOfVars σ (ZMod p) ^ μ ∧
      homogeneousComponent μ (map (Int.castRingHom (ZMod p)) (originShift a f)) ≠ 0 := by
  let φ := Int.castRingHom (ZMod p)
  have hshift := originShift_map φ a f
  have hn : map φ (originShift a f) ≠ 0 := by
    rw [hshift]
    exact originShift_ne_zero _ hf
  have hz : eval (0 : σ → ZMod p) (map φ (originShift a f)) = 0 := by
    rw [hshift, eval_zero_originShift, eval_map]
    exact ha
  have he : map φ (originShift a f) =
      eval₂Hom (C.comp φ) (fun j => X j + C (φ (a j))) f := by
    rw [hshift]
    exact eval₂Hom_map_hom φ _ C f
  have hdeg : (map φ (originShift a f)).totalDegree ≤ f.totalDegree := by
    rw [he]
    apply linear_eval₂_totalDegree_le
    intro j
    exact (totalDegree_add _ _).trans
      (max_le (le_of_eq (totalDegree_X _)) (by rw [totalDegree_C]; omega))
  obtain ⟨μ, hpos, hμdeg, hpow, hμ⟩ := exists_origin_multiplicity _ hn hz
  exact ⟨μ, hpos, hμdeg.trans hdeg, hpow, hμ⟩

end
end CCDN
