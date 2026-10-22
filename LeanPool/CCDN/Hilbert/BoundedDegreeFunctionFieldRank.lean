/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Hilbert.FilteredHilbertPolynomial
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
import LeanPool.CCDN.ForMathlib.MvPolynomial
import LeanPool.CCDN.Hilbert.CurveFunctionField
import LeanPool.CCDN.Hilbert.FunctionFieldRank
import LeanPool.CCDN.Hilbert.LinearProjectionFiltration
import LeanPool.CCDN.Hilbert.ScaledHilbertBlockComparison
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.RingTheory.Localization.Integer
import Mathlib.RingTheory.SimpleModule.Basic

/-! Function-field rank bounds for polynomial parameters of bounded
degree, obtained from the geometric Hilbert multiplicity. Linear parameters are the case of
degree one. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

private theorem bounded_degree_polynomial_parameters_rank_le
    {K R F σ τ ι : Type*} [Field K] [Field R] [Field F]
    [Algebra K R] [Algebra R F] [Algebra K F] [IsScalarTower K R F]
    [Fintype σ] [LinearOrder σ] [Fintype τ] [Fintype ι]
    (I : Ideal (MvPolynomial σ K)) (hI : I ≠ ⊤) (d q : ℕ) (hq : 0 < q)
    (hdimdeg : HasAffineDimensionDegree I (Fintype.card τ) d)
    (φ : (MvPolynomial σ K ⧸ I) →ₐ[K] F)
    (l : τ → MvPolynomial σ K) (hl : ∀ i, (l i).totalDegree ≤ q)
    (u : τ → R) (hu : AlgebraicIndependent K u)
    (he : ∀ i, φ ((Ideal.Quotient.mk I) (l i)) = algebraMap R F (u i))
    (h : ι → MvPolynomial σ K)
    (hi : LinearIndependent R (fun i => φ ((Ideal.Quotient.mk I) (h i)))) :
    Fintype.card ι ≤ d * q ^ Fintype.card τ := by
  classical
  let D := Finset.univ.sup (fun i => (h i).totalDegree)
  apply hilbert_scaled_block_count_le_multiplicity I hI (Fintype.card τ) d
    (Fintype.card ι) D q hq hdimdeg
  intro N
  let V := restrictTotalDegree τ K N
  let b := Module.finBasis K V
  let p : Fin (Module.finrank K V) → MvPolynomial τ K := fun j => (b j).val
  let uN : Fin (Module.finrank K V) → R := fun j => aeval u (p j)
  have huN : LinearIndependent K uN := by
    have hinj : Function.Injective ((aeval u).toLinearMap.comp V.subtype) :=
      (show Function.Injective (aeval u) from hu).comp Subtype.val_injective
    exact b.linearIndependent.map' ((aeval u).toLinearMap.comp V.subtype)
      (LinearMap.ker_eq_bot.mpr hinj)
  have hmap : (φ.comp (Ideal.Quotient.mkₐ K I)).comp (aeval l) =
      (IsScalarTower.toAlgHom K R F).comp (aeval u) := by
    ext i
    simp only [AlgHom.comp_apply, aeval_X]
    exact he i
  let v : ι × Fin (Module.finrank K V) → filteredCoordinateSpace I (D + q * N) :=
    fun t => ⟨(Ideal.Quotient.mk I) (h t.1 * aeval l (p t.2)), by
      apply Submodule.mem_map.mpr
      refine ⟨_, ?_, rfl⟩
      rw [mem_restrictTotalDegree]
      have hh : (h t.1).totalDegree ≤ D :=
        Finset.le_sup (f := fun i => (h i).totalDegree) (Finset.mem_univ _)
      have hq : (p t.2).totalDegree ≤ N :=
        (mem_restrictTotalDegree _ _ _).mp (b t.2).property
      have hlq : (aeval l (p t.2)).totalDegree ≤ q * N :=
        (aeval_totalDegree_le l hl _).trans (Nat.mul_le_mul_left q hq)
      exact (totalDegree_mul _ _).trans (Nat.add_le_add hh hlq)⟩
  have hli : LinearIndependent K (fun t => φ (v t).val) := by
    have hprod := tower_smul_independent _ hi uN huN
    convert hprod using 1
    funext t
    have heq := DFunLike.congr_fun hmap (p t.2)
    change φ ((Ideal.Quotient.mk I) (aeval l (p t.2))) =
      algebraMap R F (aeval u (p t.2)) at heq
    simp only [v, map_mul, heq, Algebra.smul_def, uN]
    rw [mul_comm]
  have hv : LinearIndependent K v :=
    LinearIndependent.of_comp
      (φ.toLinearMap.comp (filteredCoordinateSpace I (D + q * N)).subtype) hli
  have hh := hv.fintype_card_le_finrank
  simp only [Fintype.card_prod, Fintype.card_fin] at hh
  change Fintype.card ι * Module.finrank K (restrictTotalDegree τ K N) ≤ _ at hh
  rw [finrank_restrictTotalDegree, ← Nat.choose_symm_add] at hh
  exact hh

variable {K R F σ : Type*} [Field K] [Field R] [Field F]
  [Algebra K R] [Algebra R F] [Algebra K F] [IsScalarTower K R F] [Fintype σ] [LinearOrder σ]
  (I : Ideal (MvPolynomial σ K)) [I.IsPrime]
  [Algebra (MvPolynomial σ K ⧸ I) F] [IsScalarTower K (MvPolynomial σ K ⧸ I) F]
  [IsFractionRing (MvPolynomial σ K ⧸ I) F]

/-- Clearing common denominators gives the same sharp bound for arbitrary
independent functions in the fraction field. -/
private theorem bounded_degree_fraction_parameters_rank_le
    {τ ι : Type*} [Fintype τ] [Fintype ι]
    (d q : ℕ) (hq : 0 < q) (hdimdeg : HasAffineDimensionDegree I (Fintype.card τ) d)
    (l : τ → MvPolynomial σ K) (hl : ∀ i, (l i).totalDegree ≤ q)
    (u : τ → R) (hu : AlgebraicIndependent K u)
    (he : ∀ i, algebraMap (MvPolynomial σ K ⧸ I) F ((Ideal.Quotient.mk I) (l i)) =
      algebraMap R F (u i))
    (v : ι → F) (hv : LinearIndependent R v) : Fintype.card ι ≤ d * q ^ Fintype.card τ := by
  classical
  let A := MvPolynomial σ K ⧸ I
  let φ := IsScalarTower.toAlgHom K A F
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors A) v
  choose a ha using hb
  have hrep (i : ι) : ∃ h : MvPolynomial σ K, (Ideal.Quotient.mk I) h = a i :=
    Ideal.Quotient.mk_surjective (a i)
  choose h hh using hrep
  have hbne : algebraMap A F b.val ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.property
  have hli := field_common_multiple_independent v hv (algebraMap A F b.val) hbne
  have hlin : LinearIndependent R (fun i => φ ((Ideal.Quotient.mk I) (h i))) := by
    convert hli using 1
    funext i
    rw [hh]
    exact (ha i).trans (Algebra.smul_def _ _)
  exact bounded_degree_polynomial_parameters_rank_le I (Ideal.IsPrime.ne_top ‹I.IsPrime›) d q hq
    hdimdeg φ l hl u hu he h hlin

/-- The function field is finite over the field generated by the
expected number of independent degree-q parameters. Its degree is at most
the geometric multiplicity times q to the Hilbert dimension. -/
theorem bounded_degree_hilbert_functionField_finite_rank_le
    {τ : Type*} [Fintype τ]
    (d q : ℕ) (hq : 0 < q) (hdimdeg : HasAffineDimensionDegree I (Fintype.card τ) d)
    (l : τ → MvPolynomial σ K) (hl : ∀ i, (l i).totalDegree ≤ q)
    (u : τ → R) (hu : AlgebraicIndependent K u)
    (he : ∀ i, algebraMap (MvPolynomial σ K ⧸ I) F ((Ideal.Quotient.mk I) (l i)) =
      algebraMap R F (u i)) :
    Module.Finite R F ∧ Module.finrank R F ≤ d * q ^ Fintype.card τ := by
  have hrank : Module.rank R F ≤ ((d * q ^ Fintype.card τ : ℕ) : Cardinal) := by
    by_contra! hbad
    have hs : ((d * q ^ Fintype.card τ + 1 : ℕ) : Cardinal) ≤ Module.rank R F := by
      simpa only [Nat.cast_add, Nat.cast_one] using Cardinal.add_one_le_of_lt hbad
    obtain ⟨v, hv⟩ := exists_linearIndependent_of_le_rank hs
    have hh := bounded_degree_fraction_parameters_rank_le I d q hq hdimdeg l hl u hu he v hv
    simp only [Fintype.card_fin] at hh
    omega
  let : Module.Finite R F := Module.rank_lt_aleph0_iff.mp
    (hrank.trans_lt Cardinal.natCast_lt_aleph0)
  refine ⟨inferInstance, ?_⟩
  have hh := bounded_degree_fraction_parameters_rank_le I d q hq hdimdeg l hl u hu he
    (Module.finBasis R F) (Module.finBasis R F).linearIndependent
  simpa only [Fintype.card_fin] using hh

/-- The function field is finite over any field containing the expected
number of independent linear parameters, of rank at most the multiplicity. -/
theorem hilbert_functionField_finite_rank_le
    {τ : Type*} [Fintype τ]
    (d : ℕ) (hdimdeg : HasAffineDimensionDegree I (Fintype.card τ) d)
    (l : τ → MvPolynomial σ K) (hl : ∀ i, (l i).totalDegree ≤ 1)
    (u : τ → R) (hu : AlgebraicIndependent K u)
    (he : ∀ i, algebraMap (MvPolynomial σ K ⧸ I) F ((Ideal.Quotient.mk I) (l i)) =
      algebraMap R F (u i)) :
    Module.Finite R F ∧ Module.finrank R F ≤ d := by
  simpa only [one_pow, mul_one] using
    bounded_degree_hilbert_functionField_finite_rank_le I d 1 one_pos hdimdeg l hl u hu he

end
end CCDN
