/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Algebra.IdealZeroLocus
public import LeanPool.CCDN.ForMathlib.KrullHeight
public import LeanPool.CCDN.Hilbert.AffineCurveDegree
public import LeanPool.CCDN.Plane.IntegralAffineLine
import LeanPool.CCDN.Algebra.CoordinatePowerGeneration
import LeanPool.CCDN.Hilbert.CriticalFilteredGrowth
import LeanPool.CCDN.Hilbert.PrimeComponentTranscendence

/-!
# Degree-one prime curves are affine lines

The eventual Hilbert-degree definition implies a one-dimensional increase in
successive filtered spaces. Critical growth forces every coordinate to be affine
in one transcendental coordinate, giving polynomial containment of an affine line.
-/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

private lemma coordinate_mul_filtered_mem {K σ : Type*} [Field K]
    (I : Ideal (MvPolynomial σ K)) (j : σ) (N : ℕ)
    {u : MvPolynomial σ K ⧸ I} (hu : u ∈ filteredCoordinateSpace I N) :
    (Ideal.Quotient.mk I) (X j) * u ∈ filteredCoordinateSpace I (N + 1) := by
  obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.mp hu
  apply Submodule.mem_map.mpr
  refine ⟨X j * f, ?_, by simp⟩
  rw [mem_restrictTotalDegree] at hf ⊢
  apply (totalDegree_mul _ _).trans
  rw [totalDegree_X]
  omega

/-- Affine coordinate formulas in a prime quotient give polynomial containment
of an affine line through each base-field-valued point. -/
private theorem affine_coordinates_line_polynomial_identity {K : Type*} [Field K]
    (p : Ideal (MvPolynomial (Fin 3) K))
    (j : Fin 3) (c d : Fin 3 → K)
    (hj : Transcendental K ((Ideal.Quotient.mk p) (X j)))
    (hcd : ∀ k, (Ideal.Quotient.mk p) (X k) =
      c k • (Ideal.Quotient.mk p) (X j) + algebraMap K (MvPolynomial (Fin 3) K ⧸ p) (d k))
    (z : Fin 3 → K) (hz : z ∈ idealZeroLocus p) :
    ∀ f ∈ p,
      MvPolynomial.aeval
        (fun k => Polynomial.C (z k) + Polynomial.C (c k) * Polynomial.X) f = 0 := by
  let x := (Ideal.Quotient.mk p) (X j)
  let φ : MvPolynomial (Fin 3) K →ₐ[K] Polynomial K :=
    MvPolynomial.aeval (fun k => Polynomial.C (d k) + Polynomial.C (c k) * Polynomial.X)
  have hcomp : (Polynomial.aeval x).comp φ = Ideal.Quotient.mkₐ K p := by
    apply MvPolynomial.algHom_ext
    intro k
    simp only [AlgHom.comp_apply, φ, aeval_X, map_add, map_mul,
      Polynomial.aeval_C, Polynomial.aeval_X]
    rw [Ideal.Quotient.mkₐ_eq_mk, hcd k]
    have hsmul : c k • (Ideal.Quotient.mk p) (X j) =
        algebraMap K _ (c k) * (Ideal.Quotient.mk p) (X j) :=
        Algebra.smul_def (R := K) (A := MvPolynomial (Fin 3) K ⧸ p) (c k)
          ((Ideal.Quotient.mk p) (X j))
    rw [hsmul]
    exact add_comm _ _
  have hφ (f : MvPolynomial (Fin 3) K) (hf : f ∈ p) : φ f = 0 := by
    apply (transcendental_iff_injective.mp hj)
    change ((Polynomial.aeval x).comp φ) f = _
    rw [hcomp]
    simpa using Ideal.Quotient.eq_zero_iff_mem.mpr hf
  have hpoint (k : Fin 3) : z k = d k + c k * z j := by
    have hrel : X k - (C (d k) + C (c k) * X j) ∈ p := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      simp only [map_sub, map_add, map_mul]
      change (Ideal.Quotient.mk p) (X k) -
        (algebraMap K _ (d k) + algebraMap K _ (c k) * (Ideal.Quotient.mk p) (X j)) = 0
      rw [hcd k]
      have hsmul : c k • (Ideal.Quotient.mk p) (X j) =
          algebraMap K _ (c k) * (Ideal.Quotient.mk p) (X j) :=
        Algebra.smul_def (R := K) (A := MvPolynomial (Fin 3) K ⧸ p) (c k)
          ((Ideal.Quotient.mk p) (X j))
      rw [hsmul]
      ring
    have he := hz _ hrel
    simpa only [eval_sub, eval_add, eval_mul, eval_X, eval_C, sub_eq_zero] using he
  have htranslate :
      (Polynomial.aeval (Polynomial.C (z j) + Polynomial.X)).comp φ =
      MvPolynomial.aeval (fun k => Polynomial.C (z k) + Polynomial.C (c k) * Polynomial.X) := by
    apply MvPolynomial.algHom_ext
    intro k
    simp only [AlgHom.comp_apply, φ, aeval_X, map_add, map_mul,
      Polynomial.aeval_C, Polynomial.aeval_X]
    rw [hpoint k]
    simp only [Polynomial.C_add, Polynomial.C_mul, Polynomial.algebraMap_eq]
    ring
  intro f hf
  rw [← htranslate, AlgHom.comp_apply, hφ f hf, map_zero]

/-- A degree-one prime curve containing a base-field point has affine coordinate
formulas over that same field. In particular this holds directly over `ℚ`. -/
private theorem degree_one_coordinates_affine_of_point {K : Type*} [Field K]
    (p : Ideal (MvPolynomial (Fin 3) K)) [p.IsPrime] (hp : p.height = 2)
    (hdegree : HasFilteredCurveDegree p 1)
    (z : Fin 3 → K) (hz : z ∈ idealZeroLocus p) :
    ∃ (j : Fin 3) (c d : Fin 3 → K), c j ≠ 0 ∧
      Transcendental K ((Ideal.Quotient.mk p) (X j)) ∧ ∀ k,
      (Ideal.Quotient.mk p) (X k) =
        c k • (Ideal.Quotient.mk p) (X j) + algebraMap K (MvPolynomial (Fin 3) K ⧸ p) (d k) := by
  obtain ⟨N, b, hN⟩ := hdegree
  obtain ⟨j, hj⟩ := height_two_transcendental_coordinate_of_point p hp z hz
  have hdim : Module.finrank K (filteredCoordinateSpace p (N + 1)) =
      Module.finrank K (filteredCoordinateSpace p N) + 1 := by
    have h0 := hN N le_rfl
    have h1 := hN (N + 1) (by omega)
    push_cast at h0 h1
    omega
  have hUone : (1 : MvPolynomial (Fin 3) K ⧸ p) ∈ filteredCoordinateSpace p N := by
    apply Submodule.mem_map.mpr
    refine ⟨1, ?_, by simp⟩
    rw [mem_restrictTotalDegree, totalDegree_one]
    omega
  have hex (k : Fin 3) : ∃ c d : K,
      (Ideal.Quotient.mk p) (X k) = c • (Ideal.Quotient.mk p) (X j) +
        algebraMap K (MvPolynomial (Fin 3) K ⧸ p) d :=
    affine_of_critical_growth_of_point (coordinatePoint p z hz)
      (filteredCoordinateSpace p N) (filteredCoordinateSpace p (N + 1))
      (filteredCoordinateSpace_mono p (by omega)) hUone hdim hj
      (fun _ hu => coordinate_mul_filtered_mem p j N hu)
      (fun _ hu => coordinate_mul_filtered_mem p k N hu)
  choose c d hcd using hex
  have hcj : c j ≠ 0 := by
    intro hc
    have he := hcd j
    rw [hc, zero_smul, zero_add] at he
    apply hj
    rw [he]
    exact isAlgebraic_algebraMap (d j)
  exact ⟨j, c, d, hcj, hj, hcd⟩

/-- Affine coordinate identities identify the entire base-field zero set
with the parameterized line, in both directions. -/
private theorem zeroLocus_eq_line_of_affine_coordinates {K : Type*} [Field K]
    (p : Ideal (MvPolynomial (Fin 3) K))
    (j : Fin 3) (c d : Fin 3 → K)
    (hj : Transcendental K ((Ideal.Quotient.mk p) (X j)))
    (hcd : ∀ k, (Ideal.Quotient.mk p) (X k) =
      c k • (Ideal.Quotient.mk p) (X j) + algebraMap K (MvPolynomial (Fin 3) K ⧸ p) (d k))
    (z : Fin 3 → K) (hz : z ∈ idealZeroLocus p) :
    idealZeroLocus p = {x | ∃ t : K, x = z + t • c} := by
  have hpoint (x : Fin 3 → K) (hx : x ∈ idealZeroLocus p) (k : Fin 3) :
      x k = c k * x j + d k := by
    have he := congrArg (coordinatePoint p x hx) (hcd k)
    simpa only [coordinatePoint_mk, eval_X, map_add, map_smul,
      AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, smul_eq_mul] using he
  ext x
  constructor
  · intro hx
    refine ⟨x j - z j, ?_⟩
    funext k
    change x k = z k + (x j - z j) * c k
    rw [hpoint x hx k, hpoint z hz k]
    ring
  · rintro ⟨t, rfl⟩ f hf
    have hpoly := affine_coordinates_line_polynomial_identity p j c d hj hcd z hz f hf
    have he : (Polynomial.aeval t).comp
        (MvPolynomial.aeval (fun k => Polynomial.C (z k) + Polynomial.C (c k) * Polynomial.X)) =
        MvPolynomial.aeval (z + t • c) := by
      apply MvPolynomial.algHom_ext
      intro k
      simp only [AlgHom.comp_apply, aeval_X, map_add, map_mul,
        Polynomial.aeval_C, Polynomial.aeval_X, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        Algebra.algebraMap_self, RingHom.id_apply]
      ring
    have hz' := congrArg (Polynomial.aeval t) hpoly
    change ((Polynomial.aeval t).comp
      (MvPolynomial.aeval (fun k => Polynomial.C (z k) + Polynomial.C (c k) * Polynomial.X))) f =
        (Polynomial.aeval t) 0 at hz'
    rw [he, map_zero, MvPolynomial.aeval_eq_eval] at hz'
    exact hz'

/-- A degree-one prime component with a rational point is exactly a
rational affine line. This is equality of zero sets, not just containment. -/
theorem degree_one_zeroLocus_eq_rationalAffineLine
    (p : Ideal (CoordinatePolynomial 3)) [p.IsPrime] (hp : p.height = 2)
    (hdegree : HasAffineCurveDegree p 1)
    (z : RatPoint 3) (hz : z ∈ idealZeroLocus p) :
    ∃ v : RatPoint 3, v ≠ 0 ∧ idealZeroLocus p = rationalAffineLine z v ∧
      ∀ f ∈ p, MvPolynomial.aeval
        (fun k => Polynomial.C (z k) + Polynomial.C (v k) * Polynomial.X) f = 0 := by
  obtain ⟨j, c, d, hcj, hj, hcd⟩ :=
    degree_one_coordinates_affine_of_point p hp hdegree z hz
  refine ⟨c, fun h => hcj (congrFun h j), ?_,
    affine_coordinates_line_polynomial_identity p j c d hj hcd z hz⟩
  exact zeroLocus_eq_line_of_affine_coordinates p j c d hj hcd z hz

end
end CCDN
