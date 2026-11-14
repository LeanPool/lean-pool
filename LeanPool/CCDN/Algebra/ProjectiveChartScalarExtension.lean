/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Algebra.PolynomialLinearDescent
public import LeanPool.CCDN.Algebra.ProjectiveChartIdeal
import LeanPool.CCDN.Algebra.HomogeneousLinearDescent
import LeanPool.CCDN.Algebra.IdealScalarDescent
import LeanPool.CCDN.Algebra.ProjectionScalarExtension
import LeanPool.CCDN.Algebra.ScaledHypersurfaceModel
import LeanPool.CCDN.ForMathlib.MvPolynomial

/-! Projective affine charts commute with extension of coefficients.
In particular the standard chart of a geometrically integral projective
variety is geometrically integral. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- Applying a `K`-linear map `φ : L → K` to the coefficients commutes with the affine chart
`affineChart n` (setting the first variable to `1`). -/
lemma polynomialCoefficientLinear_affineChart
    {K L : Type*} [Field K] [Field L] [Algebra K L] {n : ℕ}
    (φ : L →ₗ[K] K) (f : MvPolynomial (Fin (n + 1)) L) :
    polynomialCoefficientLinear φ (affineChart n f) =
      affineChart n (polynomialCoefficientLinear φ f) := by
  have h := polynomialCoefficientLinear_aeval φ
    (Fin.cons (1 : MvPolynomial (Fin n) K) X) f
  have he : (fun i : Fin (n + 1) => map (algebraMap K L)
      ((Fin.cons (1 : MvPolynomial (Fin n) K) X :
        Fin (n + 1) → MvPolynomial (Fin n) K) i)) =
      (Fin.cons 1 X : Fin (n + 1) → MvPolynomial (Fin n) L) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  rw [he] at h
  exact h

private lemma polynomialCoefficientLinear_scaledHomogenize_one
    {K L : Type*} [Field K] [Field L] [Algebra K L] {n D : ℕ}
    (φ : L →ₗ[K] K) (f : MvPolynomial (Fin n) L) (hf : f.totalDegree ≤ D) :
    polynomialCoefficientLinear φ (scaledHomogenize D 1 f) =
      scaledHomogenize D 1 (polynomialCoefficientLinear φ f) := by
  apply affineChart_injective_on_homogeneous
    (polynomialCoefficientLinear_homogeneous φ _ (scaledHomogenize_homogeneous 1 f hf))
    (scaledHomogenize_homogeneous 1 _ ((polynomialCoefficientLinear_totalDegree_le φ f).trans hf))
  rw [← polynomialCoefficientLinear_affineChart,
    affineChart_scaledHomogenize_one, affineChart_scaledHomogenize_one]

/-- For a prime ideal `I` not containing `X 0`, a polynomial `f` of total degree at most `D`
lies in the chart ideal `projectiveChartIdeal I` if and only if its homogenization
`scaledHomogenize D 1 f` in degree `D` lies in `I`. -/
lemma projectiveChartIdeal_mem_iff_scaledHomogenize
    {K : Type*} [Field K] {n D : ℕ}
    (I : Ideal (MvPolynomial (Fin (n + 1)) K)) [I.IsPrime]
    (hX : X 0 ∉ I) (f : MvPolynomial (Fin n) K) (hf : f.totalDegree ≤ D) :
    f ∈ projectiveChartIdeal I ↔ scaledHomogenize D 1 f ∈ I := by
  apply coordinate_kernel_mem_iff_homogenize I _ (IsFractionRing.injective _ _) _ f hf
  intro h
  apply hX
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  exact (IsFractionRing.injective (MvPolynomial (Fin (n + 1)) K ⧸ I)
    (FractionRing (MvPolynomial (Fin (n + 1)) K ⧸ I))) (by simpa using h)

private theorem projectiveChartIdeal_scalar_extension
    {K L : Type*} [Field K] [Field L] [Algebra K L] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin (n + 1)) K)) [I.IsPrime]
    [(I.map (map (algebraMap K L))).IsPrime] (hX : X 0 ∉ I) :
    (projectiveChartIdeal I).map (map (algebraMap K L)) =
      projectiveChartIdeal (I.map (map (algebraMap K L))) := by
  have hXL : X 0 ∉ I.map (map (algebraMap K L)) := by
    simpa only [map_X] using
      (not_congr (mem_ideal_scalar_extension_iff (L := L) I (X 0))).mpr hX
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro f hf
    rw [Ideal.mem_comap, projectiveChartIdeal_mem_iff_scaledHomogenize
      _ hXL _ (totalDegree_map_le _ f)]
    have hm : map (algebraMap K L) (scaledHomogenize f.totalDegree 1 f) =
        scaledHomogenize f.totalDegree 1 (map (algebraMap K L) f) := by
      rw [scaledHomogenize_map, map_one]
    rw [← hm]
    exact Ideal.mem_map_of_mem _
      ((projectiveChartIdeal_mem_iff_scaledHomogenize I hX f le_rfl).mp hf)
  · intro g hg
    by_contra hnot
    obtain ⟨φ, hφ⟩ :=
      exists_polynomialCoefficientLinear_not_mem (projectiveChartIdeal I) g hnot
    apply hφ
    rw [projectiveChartIdeal_mem_iff_scaledHomogenize I hX _
      (polynomialCoefficientLinear_totalDegree_le φ g),
      ← polynomialCoefficientLinear_scaledHomogenize_one φ g le_rfl]
    exact polynomialCoefficientLinear_mem_scalar_extension I _
      ((projectiveChartIdeal_mem_iff_scaledHomogenize _ hXL g le_rfl).mp hg) φ

/-- If a prime ideal `I` not containing `X 0` stays prime after extending scalars from `K` to
`L`, then so does its affine chart ideal `projectiveChartIdeal I`. -/
theorem projectiveChartIdeal_geometrically_prime
    {K L : Type*} [Field K] [Field L] [Algebra K L] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin (n + 1)) K)) [I.IsPrime]
    [(I.map (map (algebraMap K L))).IsPrime] (hX : X 0 ∉ I) :
    ((projectiveChartIdeal I).map (map (algebraMap K L))).IsPrime := by
  rw [projectiveChartIdeal_scalar_extension I hX]
  infer_instance

end
end CCDN
