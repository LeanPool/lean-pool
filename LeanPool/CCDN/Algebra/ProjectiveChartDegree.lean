/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Algebra.HomogeneousChart
public import LeanPool.CCDN.Algebra.ProjectiveSection
public import LeanPool.CCDN.Hilbert.AffineCurveDegree
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import LeanPool.CCDN.Height.ProjectiveZeroLocus

/-! The affine chart of a projective coordinate domain, constructed from
coordinate ratios in a field. Its filtered Hilbert function agrees exactly
with the homogeneous Hilbert function before dehomogenization. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

private lemma aeval_affineChart {K F : Type*} [Field K] [Field F] [Algebra K F] {n : ℕ}
    (f : MvPolynomial (Fin (n + 1)) K) (x : Fin n → F) :
    aeval x (affineChart n f) = aeval (Fin.cons 1 x) f := by
  change eval₂ (algebraMap K F) x (affineChart n f) =
    eval₂ (algebraMap K F) (Fin.cons 1 x) f
  rw [← eval_map, ← affineChart_map, affineChart_eval, eval_map]

/-- A homogeneous polynomial of degree `d` satisfies `f(a • v) = a ^ d * f(v)` for evaluations in
any field `F` that is a `K`-algebra. -/
lemma homogeneous_aeval_smul {K F σ : Type*} [Field K] [Field F] [Algebra K F]
    {f : MvPolynomial σ K} {d : ℕ} (hf : f.IsHomogeneous d) (a : F) (v : σ → F) :
    aeval (a • v) f = a ^ d * aeval v f := by
  change eval₂ (algebraMap K F) (a • v) f = a ^ d * eval₂ (algebraMap K F) v f
  rw [← eval_map, ← eval_map]
  exact homogeneous_eval_smul (hf.map _) a v

/-- Given a `K`-algebra map `q` from the coordinate ring of `I` to a field `F`, the
`K`-algebra map from polynomials in the affine coordinates to `F` sending `Xⱼ` to the ratio
`q Xⱼ₊₁ / q X₀`. -/
def projectiveChartCoordinateMap {K F : Type*} [Field K] [Field F] [Algebra K F] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin (n + 1)) K))
    (q : (MvPolynomial (Fin (n + 1)) K ⧸ I) →ₐ[K] F) :
    MvPolynomial (Fin n) K →ₐ[K] F :=
  aeval (fun j => q ((Ideal.Quotient.mk I) (X j.succ)) / q ((Ideal.Quotient.mk I) (X 0)))

/-- When `q X₀ ≠ 0`, the coordinate-ratio map sends the dehomogenization of a homogeneous
polynomial `f` of degree `M` to `(q X₀)⁻¹ ^ M * q f`. -/
lemma projectiveChartCoordinateMap_chart {K F : Type*} [Field K] [Field F] [Algebra K F]
    {n M : ℕ} (I : Ideal (MvPolynomial (Fin (n + 1)) K))
    (q : (MvPolynomial (Fin (n + 1)) K ⧸ I) →ₐ[K] F)
    (h0 : q ((Ideal.Quotient.mk I) (X 0)) ≠ 0)
    (f : MvPolynomial (Fin (n + 1)) K) (hf : f.IsHomogeneous M) :
    projectiveChartCoordinateMap I q (affineChart n f) =
      (q ((Ideal.Quotient.mk I) (X 0)))⁻¹ ^ M * q ((Ideal.Quotient.mk I) f) := by
  let v : Fin (n + 1) → F := fun j => q ((Ideal.Quotient.mk I) (X j))
  have he : aeval v = q.comp (Ideal.Quotient.mkₐ K I) := by
    apply MvPolynomial.algHom_ext
    intro j
    simp [v]
  have hnorm : Fin.cons 1 (fun j => v j.succ / v 0) = (v 0)⁻¹ • v := by
    funext j
    refine Fin.cases ?_ (fun k => ?_) j
    · simp [v, h0]
    · simp [div_eq_mul_inv, mul_comm]
  change aeval (fun j => v j.succ / v 0) (affineChart n f) = _
  rw [aeval_affineChart, hnorm, homogeneous_aeval_smul hf, he]
  rfl

private lemma projectiveChartCoordinateMap_homogenize {K F : Type*} [Field K] [Field F]
    [Algebra K F] {n M : ℕ} (I : Ideal (MvPolynomial (Fin (n + 1)) K))
    (q : (MvPolynomial (Fin (n + 1)) K ⧸ I) →ₐ[K] F)
    (h0 : q ((Ideal.Quotient.mk I) (X 0)) ≠ 0)
    (f : MvPolynomial (Fin n) K) (hf : f.totalDegree ≤ M) :
    projectiveChartCoordinateMap I q f =
      (q ((Ideal.Quotient.mk I) (X 0)))⁻¹ ^ M *
        q ((Ideal.Quotient.mk I) (scaledHomogenize M 1 f)) := by
  have h := projectiveChartCoordinateMap_chart I q h0 (scaledHomogenize M 1 f)
    (scaledHomogenize_homogeneous 1 f hf)
  rwa [affineChart_scaledHomogenize_one] at h

/-- Let `q` embed the coordinate ring of `I` into a field with `q X₀ ≠ 0`. In every degree `M`,
the filtered Hilbert function of the kernel of the coordinate-ratio map
`projectiveChartCoordinateMap I q` equals the homogeneous Hilbert function of `I`. -/
theorem projective_chart_filtered_finrank {K F : Type*} [Field K] [Field F] [Algebra K F]
    {n : ℕ} (I : Ideal (MvPolynomial (Fin (n + 1)) K))
    (q : (MvPolynomial (Fin (n + 1)) K ⧸ I) →ₐ[K] F) (hq : Function.Injective q)
    (h0 : q ((Ideal.Quotient.mk I) (X 0)) ≠ 0) (M : ℕ) :
    Module.finrank K (filteredCoordinateSpace (RingHom.ker (projectiveChartCoordinateMap I q)) M) =
      projectiveHilbertFunction I M := by
  let ψ := projectiveChartCoordinateMap I q
  let η := Ideal.kerLiftAlg ψ
  let V := homogeneousCoordinateSpace I M
  let W := filteredCoordinateSpace (RingHom.ker ψ) M
  let c := (q ((Ideal.Quotient.mk I) (X 0)))⁻¹ ^ M
  let φ : (MvPolynomial (Fin (n + 1)) K ⧸ I) →ₗ[K] F :=
    (LinearMap.mulLeft K c).comp q.toLinearMap
  have hφ : Function.Injective φ := by
    intro x y h
    exact hq (mul_left_cancel₀ (pow_ne_zero _ (inv_ne_zero h0)) h)
  have himage : V.map φ = W.map η.toLinearMap := by
    ext x
    constructor
    · intro hx
      obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hx
      obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.mp hu
      refine Submodule.mem_map.mpr ⟨(Ideal.Quotient.mk (RingHom.ker ψ)) (affineChart n f), ?_, ?_⟩
      · exact Submodule.mem_map.mpr ⟨affineChart n f,
          (mem_restrictTotalDegree _ _ _).mpr
            ((affineChart_totalDegree_le f).trans hf.totalDegree_le),
          rfl⟩
      · exact projectiveChartCoordinateMap_chart I q h0 f hf
    · intro hx
      obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hx
      obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.mp hu
      refine Submodule.mem_map.mpr ⟨(Ideal.Quotient.mk I) (scaledHomogenize M 1 f), ?_, ?_⟩
      · exact Submodule.mem_map.mpr ⟨scaledHomogenize M 1 f,
          scaledHomogenize_homogeneous 1 f ((mem_restrictTotalDegree _ _ _).mp hf), rfl⟩
      · exact (projectiveChartCoordinateMap_homogenize I q h0 f
          ((mem_restrictTotalDegree _ _ _).mp hf)).symm
  have hV := (Submodule.equivMapOfInjective φ hφ V).finrank_eq
  have hW :=
    (Submodule.equivMapOfInjective η.toLinearMap (Ideal.kerLiftAlg_injective ψ) W).finrank_eq
  rw [himage] at hV
  exact hW.trans hV.symm

/-- Let `q` embed the coordinate ring of `I` into a field with `q X₀ ≠ 0`. If `I` defines a
projective curve of degree `d`, then the kernel of the coordinate-ratio map
`projectiveChartCoordinateMap I q` defines an affine curve of degree `d`. -/
theorem projective_chart_degree {F : Type*} [Field F] [Algebra ℚ F] {n d : ℕ}
    (I : Ideal (MvPolynomial (Fin (n + 1)) ℚ))
    (q : (MvPolynomial (Fin (n + 1)) ℚ ⧸ I) →ₐ[ℚ] F) (hq : Function.Injective q)
    (h0 : q ((Ideal.Quotient.mk I) (X 0)) ≠ 0)
    (hdegree : HasProjectiveCurveDegree I d) :
    HasAffineCurveDegree (RingHom.ker (projectiveChartCoordinateMap I q)) d := by
  obtain ⟨N, c, hN⟩ := hdegree
  refine ⟨N, c, ?_⟩
  intro M hM
  have he := projective_chart_filtered_finrank I q hq h0 M
  change (Module.finrank ℚ (filteredCoordinateSpace _ M) : ℤ) = _
  rw [he]
  exact hN M hM

end
end CCDN
