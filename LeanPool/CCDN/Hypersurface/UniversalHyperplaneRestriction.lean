/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Algebra.CoefficientwiseHomogeneous
public import LeanPool.CCDN.Hypersurface.GraphHyperplaneRestriction
import LeanPool.CCDN.Height.ProjectiveZeroLocus
import LeanPool.CCDN.Hypersurface.CoefficientwiseSubstitution

/-! A homogeneous universal hyperplane restriction without denominators.
The normal A cuts out A₀x₀+ΣAᵢxᵢ=0; the chart A₀≠0 is represented by
x₀=−ΣAᵢxᵢ and xᵢ=A₀xᵢ before evaluating a degree-d equation. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The universal restriction of an integer polynomial to the hyperplane
`A none * x_none + ∑ A (some j) * x j = 0`, whose normal coefficients `A` are indeterminates,
without denominators: it substitutes `x_none ↦ -∑ A (some j) * x j` and `x j ↦ A none * x j`. -/
def universalHyperplaneRestriction {σ : Type*} [Fintype σ] :
    MvPolynomial (Option σ) ℤ →ₐ[ℤ]
      MvPolynomial σ (MvPolynomial (Option σ) ℤ) :=
  aeval (fun i => Option.elim i
    (-(∑ j, C (X (some j)) * X j)) (fun j => C (X none) * X j))

/-- The restriction of a polynomial to the hyperplane `A none * x_none + ∑ A (some j) * x j = 0`
without denominators, obtained by substituting `x_none ↦ -∑ A (some j) * x j` and
`x j ↦ A none * x j`. -/
def scaledHyperplaneRestriction {K σ : Type*} [CommRing K] [Fintype σ]
    (A : Option σ → K) : MvPolynomial (Option σ) K →ₐ[K] MvPolynomial σ K :=
  aeval (fun i => Option.elim i
    (-(∑ j, C (A (some j)) * X j)) (fun j => C (A none) * X j))

/-- Specializing the coefficient indeterminates of the universal hyperplane restriction at a
normal vector `A` gives the scaled hyperplane restriction for `A`. -/
lemma universalHyperplaneRestriction_specialize {K σ : Type*}
    [CommRing K] [Fintype σ] (A : Option σ → K) (f : MvPolynomial (Option σ) ℤ) :
    map (eval₂Hom (Int.castRingHom K) A) (universalHyperplaneRestriction f) =
      scaledHyperplaneRestriction A (map (Int.castRingHom K) f) := by
  have he : (map (eval₂Hom (Int.castRingHom K) A)).comp
      (universalHyperplaneRestriction (σ := σ)).toRingHom =
      (scaledHyperplaneRestriction A).toRingHom.comp (map (Int.castRingHom K)) := by
    apply MvPolynomial.ringHom_ext
    · intro z
      simp [universalHyperplaneRestriction, scaledHyperplaneRestriction]
    · intro i
      cases i <;> simp [universalHyperplaneRestriction, scaledHyperplaneRestriction]
  exact RingHom.congr_fun he f

/-- The universal hyperplane restriction of a homogeneous polynomial of degree `d` has
coefficients that are homogeneous of degree `d` in the normal coefficients. -/
lemma universalHyperplaneRestriction_coefficientwiseHomogeneous
    {σ : Type*} [Fintype σ] {d : ℕ} {f : MvPolynomial (Option σ) ℤ}
    (hf : f.IsHomogeneous d) :
    CoefficientwiseHomogeneous (universalHyperplaneRestriction f) d := by
  have hx (i : Option σ) (j : σ) : CoefficientwiseHomogeneous
      (C (X i) * X j : MvPolynomial σ (MvPolynomial (Option σ) ℤ)) 1 := by
    have hh := (CoefficientwiseHomogeneous.C_of_isHomogeneous (isHomogeneous_X ℤ i)).mul
      (CoefficientwiseHomogeneous.map_C (X j : MvPolynomial σ ℤ))
    simpa only [map_X, add_zero] using hh
  have hg (i : Option σ) : CoefficientwiseHomogeneous
      (Option.elim i (-(∑ j, C (X (some j)) * X j))
        (fun j => C (X none) * X j) :
          MvPolynomial σ (MvPolynomial (Option σ) ℤ)) 1 := by
    cases i with
    | none => exact (CoefficientwiseHomogeneous.sum _ _ _ (fun j _ => hx (some j) j)).neg
    | some j => exact hx none j
  have hc (z : ℤ) : CoefficientwiseHomogeneous
      (C (C z) : MvPolynomial σ (MvPolynomial (Option σ) ℤ)) 0 :=
    CoefficientwiseHomogeneous.C_of_isHomogeneous (isHomogeneous_C _ z)
  have he : algebraMap ℤ (MvPolynomial σ (MvPolynomial (Option σ) ℤ)) = C.comp C := by
    ext z
    simp
  simpa only [universalHyperplaneRestriction, aeval_def, coe_eval₂Hom, he, one_mul] using
    CoefficientwiseHomogeneous.eval₂ hf (C.comp C) _ hc hg

/-- The scaled hyperplane restriction preserves homogeneity of degree `d`. -/
lemma scaledHyperplaneRestriction_homogeneous {K σ : Type*}
    [CommRing K] [Fintype σ] (A : Option σ → K)
    {d : ℕ} {f : MvPolynomial (Option σ) K} (hf : f.IsHomogeneous d) :
    (scaledHyperplaneRestriction A f).IsHomogeneous d := by
  have hg (i : Option σ) :
      (Option.elim i (-(∑ j, C (A (some j)) * X j))
        (fun j => C (A none) * X j) : MvPolynomial σ K).IsHomogeneous 1 := by
    cases i with
    | none =>
      exact (IsHomogeneous.sum _ _ _ (fun j _ =>
        (isHomogeneous_X _ j).C_mul (A (some j)))).neg
    | some j => exact (isHomogeneous_X _ j).C_mul (A none)
  simpa only [scaledHyperplaneRestriction, one_mul] using hf.aeval _ hg

/-- For `A none ≠ 0` and `f` homogeneous of degree `d`, the scaled hyperplane restriction of `f`
is `A none ^ d` times its restriction to the graph hyperplane
`x_none = ∑ -(A (some i) / A none) * x i`. -/
lemma scaledHyperplaneRestriction_eq_graph {K σ : Type*}
    [Field K] [Fintype σ] (A : Option σ → K) (hA : A none ≠ 0)
    {d : ℕ} {f : MvPolynomial (Option σ) K} (hf : f.IsHomogeneous d) :
    scaledHyperplaneRestriction A f =
      C (A none ^ d) * graphHyperplaneRestriction (fun i => -A (some i) / A none) f := by
  let v : Option σ → MvPolynomial σ K :=
    fun i => Option.elim i (∑ j, C (-A (some j) / A none) * X j) X
  have hv : (fun i => Option.elim i (-(∑ j, C (A (some j)) * X j))
      (fun j => C (A none) * X j)) = (C (A none) : MvPolynomial σ K) • v := by
    funext i
    cases i with
    | none =>
      change -(∑ j, C (A (some j)) * X j) =
        C (A none) * (∑ j, C (-A (some j) / A none) * X j)
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro j _
      rw [← mul_assoc, ← map_mul]
      have he : A none * (-A (some j) / A none) = -A (some j) := by field_simp
      rw [he, map_neg, neg_mul]
    | some j => rfl
  change eval₂ C _ f = C (A none ^ d) * eval₂ C v f
  rw [hv, eval₂_eq_eval_map, homogeneous_eval_smul (hf.map C), ← eval₂_eq_eval_map,
    ← map_pow]

/-- The scaled hyperplane restriction for the normal vector `(1, -a)` is the restriction to the
graph hyperplane `x_none = ∑ a i * x i`. -/
lemma scaledHyperplaneRestriction_normalized {K σ : Type*}
    [CommRing K] [Fintype σ] (a : σ → K) (f : MvPolynomial (Option σ) K) :
    scaledHyperplaneRestriction (fun i => Option.elim i 1 (fun j => -a j)) f =
      graphHyperplaneRestriction a f := by
  congr 1
  apply MvPolynomial.algHom_ext
  intro i
  cases i <;> simp [scaledHyperplaneRestriction, graphHyperplaneRestriction,
    ← Finset.sum_neg_distrib]

end
end CCDN
