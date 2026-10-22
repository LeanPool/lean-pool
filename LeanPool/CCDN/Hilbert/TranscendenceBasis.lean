/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Hilbert.FilteredHilbertPolynomial
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import LeanPool.CCDN.Hilbert.BoundedDegreeFunctionFieldRank
import LeanPool.CCDN.Hilbert.CoordinateIndependence
import Mathlib.RingTheory.AlgebraicIndependent.AlgebraicClosure
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis

/-!
The constructed Hilbert dimension equals transcendence-basis cardinality.
Consequently integral embeddings preserve Hilbert dimension.

Construct a finite linear parameter field from coordinate
functions, in arbitrary Hilbert dimension.
-/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

private def coordinateParameterField {K F σ : Type*} [Field K] [Field F] [Algebra K F]
    (I : Ideal (MvPolynomial σ K)) [Algebra (MvPolynomial σ K ⧸ I) F]
    (U : Set σ) : IntermediateField K F :=
  IntermediateField.adjoin K (Set.range (fun i : U =>
    algebraMap (MvPolynomial σ K ⧸ I) F ((Ideal.Quotient.mk I) (X i.val))))

/-- There is a subset of coordinate functions whose generated field
has finite extension degree at most the Hilbert multiplicity. -/
private theorem exists_finite_coordinate_parameter_field
    {K F σ : Type*} [Field K] [Field F] [Fintype σ] [LinearOrder σ] [Algebra K F]
    (I : Ideal (MvPolynomial σ K)) [I.IsPrime]
    [Algebra (MvPolynomial σ K ⧸ I) F] [IsScalarTower K (MvPolynomial σ K ⧸ I) F]
    [IsFractionRing (MvPolynomial σ K ⧸ I) F]
    (d : ℕ)
    (hdegree : (filteredHilbertPolynomial I).leadingCoeff =
      (d : ℚ) / (filteredHilbertPolynomial I).natDegree.factorial) :
    ∃ U : Set σ, Nat.card U = (filteredHilbertPolynomial I).natDegree ∧
      AlgebraicIndependent K (fun i : U => (Ideal.Quotient.mk I) (X i.val)) ∧
      Module.Finite (coordinateParameterField (F := F) I U) F ∧
      Module.finrank (coordinateParameterField (F := F) I U) F ≤ d := by
  classical
  obtain ⟨U, hU, hAI⟩ := exists_hilbert_dimension_independent_coordinates I
    (Ideal.IsPrime.ne_top ‹I.IsPrime›)
  refine ⟨U, hU, hAI, ?_⟩
  let R := coordinateParameterField (F := F) I U
  let φ := IsScalarTower.toAlgHom K (MvPolynomial σ K ⧸ I) F
  let u : U → R := fun i => ⟨φ ((Ideal.Quotient.mk I) (X i.val)),
    IntermediateField.subset_adjoin K _ ⟨i, rfl⟩⟩
  have huF : AlgebraicIndependent K
      (fun i : U => φ ((Ideal.Quotient.mk I) (X i.val))) :=
    hAI.map' (IsFractionRing.injective _ _)
  have hu : AlgebraicIndependent K u := by
    apply AlgebraicIndependent.of_comp R.val
    exact huF
  have hdim : (filteredHilbertPolynomial I).natDegree = Fintype.card U := by
    simpa only [Nat.card_eq_fintype_card] using hU.symm
  exact hilbert_functionField_finite_rank_le I d ⟨hdim, by simpa only [← hdim] using hdegree⟩
    (fun i : U => X i.val) (fun _ => by simp) u hu (fun _ => rfl)

end
end CCDN

namespace CCDN
noncomputable section
open MvPolynomial

/-- For a prime ideal `I`, some set of coordinate functions, of size the Hilbert dimension of `I`,
is a transcendence basis of `K[X] ⧸ I` over `K`. -/
theorem exists_hilbert_coordinate_transcendence_basis
    {K σ : Type*} [Field K] [Fintype σ] [LinearOrder σ]
    (I : Ideal (MvPolynomial σ K)) [I.IsPrime] :
    ∃ U : Set σ, Nat.card U = (filteredHilbertPolynomial I).natDegree ∧
      IsTranscendenceBasis K (fun i : U => (Ideal.Quotient.mk I) (X i.val)) := by
  classical
  let A := MvPolynomial σ K ⧸ I
  let F := FractionRing A
  let φ := IsScalarTower.toAlgHom K A F
  obtain ⟨d, _, _, hd⟩ := filteredHilbertPolynomial_positive_multiplicity I
    (Ideal.IsPrime.ne_top ‹I.IsPrime›)
  obtain ⟨U, hU, hAI, hfinite, _⟩ :=
    exists_finite_coordinate_parameter_field (F := F) I d hd
  let R := coordinateParameterField (F := F) I U
  let : Module.Finite R F := hfinite
  have hfieldalg : Algebra.IsAlgebraic R F :=
    ⟨fun x => (IsIntegral.of_finite R x).isAlgebraic⟩
  have huF : AlgebraicIndependent K
      (fun i : U => φ ((Ideal.Quotient.mk I) (X i.val))) :=
    hAI.map' (IsFractionRing.injective _ _)
  have hBF : IsTranscendenceBasis K
      (fun i : U => φ ((Ideal.Quotient.mk I) (X i.val))) := by
    apply huF.isTranscendenceBasis_iff_isAlgebraic.mpr
    exact IntermediateField.isAlgebraic_adjoin_iff_top.mp hfieldalg
  exact ⟨U, hU, IsTranscendenceBasis.of_comp φ (IsFractionRing.injective _ _) hBF⟩

/-- For a prime ideal `I`, the Hilbert dimension of `I` equals the cardinality of any transcendence
basis of `K[X] ⧸ I` over `K`. -/
theorem hilbert_dimension_eq_transcendence_basis_card
    {K σ ι : Type*} [Field K] [Fintype σ] [LinearOrder σ] [Fintype ι]
    (I : Ideal (MvPolynomial σ K)) [I.IsPrime]
    (x : ι → MvPolynomial σ K ⧸ I) (hx : IsTranscendenceBasis K x) :
    (filteredHilbertPolynomial I).natDegree = Fintype.card ι := by
  classical
  obtain ⟨U, hU, hBU⟩ := exists_hilbert_coordinate_transcendence_basis I
  have hc := hBU.lift_cardinalMk_eq hx
  have hcard : Fintype.card U = Fintype.card ι := by
    simpa only [Cardinal.mk_fintype, Cardinal.lift_natCast, Nat.cast_inj] using hc
  rw [Nat.card_eq_fintype_card] at hU
  omega

/-- Integral embeddings preserve the filtered Hilbert dimension,
without assuming a normalization or a Hilbert polynomial. -/
theorem integral_embedding_hilbert_dimension_eq
    {K σ τ : Type*} [Field K] [Fintype σ] [Fintype τ]
    [LinearOrder σ] [LinearOrder τ]
    (I : Ideal (MvPolynomial σ K)) [I.IsPrime]
    (J : Ideal (MvPolynomial τ K)) [J.IsPrime]
    (ψ : (MvPolynomial σ K ⧸ I) →ₐ[K] (MvPolynomial τ K ⧸ J))
    (hψ : Function.Injective ψ) (hint : ψ.IsIntegral) :
    (filteredHilbertPolynomial I).natDegree = (filteredHilbertPolynomial J).natDegree := by
  classical
  let A := MvPolynomial σ K ⧸ I
  let B := MvPolynomial τ K ⧸ J
  let : Algebra A B := ψ.toRingHom.toAlgebra
  let : IsScalarTower K A B := IsScalarTower.of_algHom ψ
  let : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).mpr hψ
  let : Algebra.IsIntegral A B := ⟨hint⟩
  let : Algebra.IsAlgebraic A B :=
    ⟨fun x => (show IsIntegral A x from hint x).isAlgebraic⟩
  obtain ⟨U, hU, hBU⟩ := exists_hilbert_coordinate_transcendence_basis I
  have hb := hBU.algebraMap_comp (A := B)
  have hJ := hilbert_dimension_eq_transcendence_basis_card J _ hb
  rw [Nat.card_eq_fintype_card] at hU
  exact hU.symm.trans hJ.symm

end
end CCDN
