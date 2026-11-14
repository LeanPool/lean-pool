/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Hilbert.FilteredHilbertPolynomial
public import LeanPool.CCDN.Hilbert.LinearProjectionFiltration
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import LeanPool.CCDN.Hilbert.PolynomialComparison
import LeanPool.CCDN.Hilbert.TranscendenceBasis
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-! Integral linear projections preserve Hilbert dimension and
do not increase its multiplicity. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- An integral map `ψ` from a polynomial ring to the quotient by a prime `I` preserves Hilbert
dimension: the filtered Hilbert polynomials of `ker ψ` and of `I` have the same degree. -/
theorem integral_projection_hilbert_dimension_eq
    {K σ τ : Type*} [Field K] [Fintype σ] [Fintype τ]
    [LinearOrder σ] [LinearOrder τ]
    (I : Ideal (MvPolynomial τ K)) [I.IsPrime]
    (ψ : MvPolynomial σ K →ₐ[K] (MvPolynomial τ K ⧸ I))
    (hint : ψ.IsIntegral) :
    (filteredHilbertPolynomial (RingHom.ker ψ)).natDegree =
      (filteredHilbertPolynomial I).natDegree := by
  have : (RingHom.ker ψ).IsPrime := RingHom.ker_isPrime ψ.toRingHom
  exact integral_embedding_hilbert_dimension_eq (RingHom.ker ψ) I
    (Ideal.kerLiftAlg ψ) (Ideal.kerLiftAlg_injective ψ) hint.kerLift

private theorem integral_linear_projection_multiplicity
    {K σ τ : Type*} [Field K] [Fintype σ] [Fintype τ]
    [LinearOrder σ] [LinearOrder τ]
    (I : Ideal (MvPolynomial τ K)) [I.IsPrime]
    (a : σ → MvPolynomial τ K) (ha : ∀ i, (a i).totalDegree ≤ 1)
    (hint : (projectionCoordinateMap I a).IsIntegral) (d : ℕ)
    (hdegree : (filteredHilbertPolynomial I).leadingCoeff =
      (d : ℚ) / (filteredHilbertPolynomial I).natDegree.factorial) :
    (filteredHilbertPolynomial (RingHom.ker (projectionCoordinateMap I a))).natDegree =
        (filteredHilbertPolynomial I).natDegree ∧
      ∃ e : ℕ, 0 < e ∧ e ≤ d ∧
        (filteredHilbertPolynomial (RingHom.ker (projectionCoordinateMap I a))).leadingCoeff =
          (e : ℚ) / (filteredHilbertPolynomial I).natDegree.factorial := by
  let J := RingHom.ker (projectionCoordinateMap I a)
  have hJ : J ≠ ⊤ := RingHom.ker_ne_top _
  have hI : I ≠ ⊤ := Ideal.IsPrime.ne_top ‹I.IsPrime›
  have hdim := integral_projection_hilbert_dimension_eq I _ hint
  obtain ⟨e, he, _, hlc⟩ := filteredHilbertPolynomial_positive_multiplicity J hJ
  have hle := filteredHilbertPolynomial_leadingCoeff_le J I hJ hI hdim
    (fun N => linear_projection_filtered_finrank_le I a ha N)
  rw [hdim] at hlc
  refine ⟨hdim, e, he, ?_, hlc⟩
  rw [hlc, hdegree] at hle
  exact_mod_cast (div_le_div_iff_of_pos_right
    (by positivity : (0 : ℚ) < (filteredHilbertPolynomial I).natDegree.factorial)).mp hle

/-- An integral linear projection of a prime of dimension `m` and degree `d` has dimension `m`
and a positive degree at most `d`. -/
theorem integral_linear_projection_dimension_degree
    {K σ τ : Type*} [Field K] [Fintype σ] [Fintype τ]
    [LinearOrder σ] [LinearOrder τ]
    (I : Ideal (MvPolynomial τ K)) [I.IsPrime]
    (a : σ → MvPolynomial τ K) (ha : ∀ i, (a i).totalDegree ≤ 1)
    (hint : (projectionCoordinateMap I a).IsIntegral) {m d : ℕ}
    (hdimdeg : HasAffineDimensionDegree I m d) :
    ∃ e : ℕ, 0 < e ∧ e ≤ d ∧
      HasAffineDimensionDegree (RingHom.ker (projectionCoordinateMap I a)) m e := by
  obtain ⟨hdim, e, he, hed, hlc⟩ := integral_linear_projection_multiplicity I a ha hint d
    (by rw [hdimdeg.natDegree_eq]; exact hdimdeg.leadingCoeff_eq)
  rw [hdimdeg.natDegree_eq] at hdim hlc
  exact ⟨e, he, hed, hdim, hlc⟩

end
end CCDN
