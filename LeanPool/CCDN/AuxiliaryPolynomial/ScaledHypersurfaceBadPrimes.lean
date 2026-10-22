/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Algebra.HomogeneousSlice
public import LeanPool.CCDN.AuxiliaryPolynomial.HypersurfaceBadPrimeFactor
import LeanPool.CCDN.Algebra.ScaledHypersurfaceModel
import LeanPool.CCDN.ForMathlib.MvPolynomial

/-! Prime scaling changes the geometric bad-prime factor by at most an
absolute constant. Outside the scaling prime, the homogeneous models are
related by an invertible change of coordinates and a nonzero scalar. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

private lemma firstCoordinateScaleHom_scaledHomogenize {R : Type*} [CommRing R] {n d : ℕ}
    (h : R) (f : MvPolynomial (Fin n) R) (hd : f.totalDegree ≤ d) :
    firstCoordinateScaleHom R h (scaledHomogenize d h f) =
      C (h ^ d) * scaledHomogenize d 1 f := by
  apply affineChart_injective_on_homogeneous
    (firstCoordinateScaleHom_homogeneous h (scaledHomogenize_homogeneous h f hd))
    ((scaledHomogenize_homogeneous 1 f hd).C_mul (h ^ d))
  rw [← homogeneousSlice_eq_chart_scale, homogeneousSlice_scaledHomogenize h f hd,
    map_mul, affineChart_scaledHomogenize_one]
  simp [affineChart]

private lemma scaledHomogenize_irreducible_iff {K : Type*} [Field K] {n d : ℕ}
    (h : K) (hh : h ≠ 0) (f : MvPolynomial (Fin n) K) (hd : f.totalDegree ≤ d) :
    Irreducible (scaledHomogenize d h f) ↔ Irreducible (scaledHomogenize d 1 f) := by
  have hu : IsUnit (C (h ^ d) : MvPolynomial (Fin (n + 1)) K) :=
    (isUnit_iff_ne_zero.mpr (pow_ne_zero d hh)).map C
  have he := MulEquiv.irreducible_iff (f := firstCoordinateScale K h hh)
    (x := scaledHomogenize d h f)
  change Irreducible (firstCoordinateScaleHom K h (scaledHomogenize d h f)) ↔
    Irreducible (scaledHomogenize d h f) at he
  rw [firstCoordinateScaleHom_scaledHomogenize h f hd, irreducible_isUnit_mul hu] at he
  exact he.symm

private lemma scaledHomogenize_map_irreducible_iff {K : Type*} [Field K] {n d : ℕ}
    (φ : ℤ →+* K) (h : ℤ) (hh : φ h ≠ 0)
    (f : MvPolynomial (Fin n) ℤ) (hd : f.totalDegree ≤ d) :
    Irreducible (map φ (scaledHomogenize d h f)) ↔
      Irreducible (map φ (scaledHomogenize d 1 f)) := by
  rw [scaledHomogenize_map, scaledHomogenize_map, map_one]
  apply scaledHomogenize_irreducible_iff _ hh
  exact (totalDegree_map_le _ _).trans hd

private lemma hypersurfaceBadReduction_scaledHomogenize {n d : ℕ}
    (f : MvPolynomial (Fin n) ℤ) (hf : f ≠ 0) (hd : f.totalDegree ≤ d)
    {p q : ℕ} (hp : p.Prime) (hqp : q ≠ p) :
    HypersurfaceBadReduction (scaledHomogenize d (p : ℤ) f) q ↔
      HypersurfaceBadReduction (scaledHomogenize d 1 f) q := by
  by_cases hq : q.Prime
  · let : Fact q.Prime := ⟨hq⟩
    have hpZ : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hpK : (p : AlgebraicClosure (ZMod q)) ≠ 0 := by
      rw [Ne, CharP.cast_eq_zero_iff _ q]
      exact fun h => hqp ((Nat.prime_dvd_prime_iff_eq hq hp).mp h)
    rw [homogeneous_hypersurfaceBadReduction_iff _ (scaledHomogenize_homogeneous _ _ hd)
        (scaledHomogenize_ne_zero d hpZ hf),
      homogeneous_hypersurfaceBadReduction_iff _ (scaledHomogenize_homogeneous _ _ hd)
        (scaledHomogenize_ne_zero d one_ne_zero hf)]
    apply not_congr
    exact scaledHomogenize_map_irreducible_iff _ (p : ℤ) (by simpa using hpK) f hd
  · constructor <;> intro h <;> exact (hq h.1).elim

/-- Enlarging the bad-prime set at one prime costs at most `exp 1`. The
nonabsolute case is included, using the paper's zero convention. -/
private theorem hypersurfaceBadPrimeFactor_le_of_badReduction_imp {n : ℕ}
    (f g : MvPolynomial (Fin (n + 1)) ℤ) {p : ℕ} (hp : 0 < p)
    (hd : f.totalDegree = g.totalDegree)
    (habs : AbsolutelyIrreducible f → AbsolutelyIrreducible g)
    (hbad : ∀ q, q ≠ p → HypersurfaceBadReduction f q → HypersurfaceBadReduction g q) :
    hypersurfaceBadPrimeFactor f ≤ Real.exp 1 * hypersurfaceBadPrimeFactor g := by
  classical
  by_cases hf : AbsolutelyIrreducible f
  · have hg := habs hf
    let S := (finite_fin_hypersurface_bad_primes f hf
      (absolute_integer_polynomial_totalDegree_pos f hf)).toFinset
    let T := (finite_fin_hypersurface_bad_primes g hg
      (absolute_integer_polynomial_totalDegree_pos g hg)).toFinset
    have hS : ∀ q, q ∈ S ↔ stepanovThreshold f.totalDegree < q ∧ HypersurfaceBadReduction f q := by
      intro q
      exact Set.Finite.mem_toFinset _
    have hT : ∀ q, q ∈ T ↔ stepanovThreshold g.totalDegree < q ∧ HypersurfaceBadReduction g q := by
      intro q
      exact Set.Finite.mem_toFinset _
    have hsub : S ⊆ insert p T := by
      intro q hq
      by_cases he : q = p
      · exact Finset.mem_insert.mpr (Or.inl he)
      · apply Finset.mem_insert.mpr ∘ Or.inr
        exact (hT q).mpr ⟨hd ▸ ((hS q).mp hq).1, hbad q he ((hS q).mp hq).2⟩
    have hnonneg (q : ℕ) : 0 ≤ Real.log q / q := by
      by_cases hq : q = 0
      · simp only [hq, Nat.cast_zero, Real.log_zero, zero_div, le_refl]
      · exact div_nonneg (Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hq))
          (Nat.cast_nonneg q)
    have hsum : (∑ q ∈ S, Real.log q / q) ≤ (∑ q ∈ T, Real.log q / q) + 1 := by
      have h₁ : (∑ q ∈ S, Real.log q / q) ≤ (∑ q ∈ insert p T, Real.log q / q) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun q _ _ => hnonneg q)
      have h₂ : (∑ q ∈ insert p T, Real.log q / q) ≤
          (∑ q ∈ T, Real.log q / q) + Real.log p / p := by
        by_cases hmem : p ∈ T
        · rw [Finset.insert_eq_of_mem hmem]
          exact le_add_of_nonneg_right (hnonneg p)
        · rw [Finset.sum_insert hmem]
          exact (add_comm _ _).le
      have h₃ : Real.log p / p ≤ 1 := by
        have hpR : (0 : ℝ) < p := by exact_mod_cast hp
        apply (div_le_one hpR).mpr
        linarith [Real.log_le_sub_one_of_pos hpR]
      linarith
    rw [hypersurfaceBadPrimeFactor_eq_exp f hf rfl S hS,
      hypersurfaceBadPrimeFactor_eq_exp g hg rfl T hT,
      ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith
  · rw [hypersurfaceBadPrimeFactor_eq_zero f hf]
    exact mul_nonneg (Real.exp_pos _).le (hypersurfaceBadPrimeFactor_nonneg g)

/-- Prime scaling preserves all geometric bad primes away from the scaling
prime, and therefore multiplies the paper's bad-prime factor by at most `e`. -/
theorem hypersurfaceBadPrimeFactor_scaledHomogenize_le {n : ℕ}
    (f : MvPolynomial (Fin n) ℤ) (hf : f ≠ 0) {p : ℕ} (hp : p.Prime) :
    hypersurfaceBadPrimeFactor (scaledHomogenize f.totalDegree (p : ℤ) f) ≤
      Real.exp 1 * hypersurfaceBadPrimeFactor (scaledHomogenize f.totalDegree 1 f) := by
  have hpZ : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  apply hypersurfaceBadPrimeFactor_le_of_badReduction_imp _ _ hp.pos
  · rw [(scaledHomogenize_homogeneous (p : ℤ) f le_rfl).totalDegree
        (scaledHomogenize_ne_zero f.totalDegree hpZ hf),
      (scaledHomogenize_homogeneous (1 : ℤ) f le_rfl).totalDegree
        (scaledHomogenize_ne_zero f.totalDegree one_ne_zero hf)]
  · exact (scaledHomogenize_map_irreducible_iff _ (p : ℤ)
      (by simpa only [Int.coe_castRingHom, Int.cast_natCast] using
        (show (p : AlgebraicClosure ℚ) ≠ 0 by exact_mod_cast hp.ne_zero))
      f le_rfl).mp
  · intro q hq
    exact (hypersurfaceBadReduction_scaledHomogenize f hf le_rfl hp hq).mp

end
end CCDN
