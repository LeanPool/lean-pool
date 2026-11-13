/-
Copyright (c) 2026 Raúl E. Pariente-Martín, Pedro Tradacete. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raúl E. Pariente-Martín, Pedro Tradacete
-/

module

public import LeanPool.FBLOrderContinuity.Model
public import Mathlib.Analysis.Normed.Module.DoubleDual
public import Mathlib.Analysis.InnerProductSpace.PiL2



/-!
# Finite Euclidean families in an infinite-dimensional dual

This module proves the geometric estimate needed for the convexity obstruction.
`dual_euclidean_family` produces n dual functionals with weak ell-two norm at most
one and with every individual norm greater than 1/4.

The proof maximizes a determinant on a finite-dimensional operator unit ball.
Scaling an orthogonal subspace by 1/2 and its complement by 2 forces a maximizing
operator to be large on enough orthogonal directions. Applying this construction
in a 2n-dimensional subspace of the dual gives the family. Infinite-dimensionality
of the dual follows from the isometric embedding into the bidual. This direct
Dvoretzky–Rogers argument does not require completeness of the original space.
-/

@[expose] public section

noncomputable section
open scoped BigOperators Topology
open Filter Set Module

namespace FBLOrderContinuousLH
namespace EuclideanFamilies

/-- For isomorphic finite-dimensional normed spaces H and B, choose a contraction T
maximizing the absolute determinant in fixed coordinates. Any endomorphism A for
which T composed with A is still a contraction then has absolute determinant at most one. -/
private theorem volume_maximizer {H B : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [FiniteDimensional ℝ H] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [FiniteDimensional ℝ B] (e : H ≃L[ℝ] B) :
    ∃ T : H →L[ℝ] B, ‖T‖ ≤ 1 ∧
      ∀ A : H →L[ℝ] H, ‖T.comp A‖ ≤ 1 → |A.det| ≤ 1 := by
  let D (T : H →L[ℝ] B) := |(e.symm.toContinuousLinearMap.comp T).det|
  have hD : Continuous D :=
    (ContinuousLinearMap.continuous_det.comp (continuous_const.clm_comp continuous_id)).abs
  let c : ℝ := (1 + ‖e.toContinuousLinearMap‖)⁻¹
  have hc : 0 < c := inv_pos.mpr (by positivity)
  have hcnorm : ‖c • e.toContinuousLinearMap‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc]
    change (1 + ‖e.toContinuousLinearMap‖)⁻¹ * ‖e.toContinuousLinearMap‖ ≤ 1
    rw [inv_mul_eq_div]
    exact (div_le_one (by positivity)).mpr (by linarith)
  have hcomp : e.symm.toContinuousLinearMap.comp (c • e.toContinuousLinearMap) =
      c • ContinuousLinearMap.id ℝ H := by
    ext x
    simp
  have hDpos : 0 < D (c • e.toContinuousLinearMap) := by
    dsimp only [D]
    rw [hcomp]
    change 0 < |LinearMap.det (c • LinearMap.id)|
    rw [LinearMap.det_smul, LinearMap.det_id, mul_one, abs_of_pos (pow_pos hc _)]
    exact pow_pos hc _
  obtain ⟨T, hT, hmax⟩ := (isCompact_closedBall (0 : H →L[ℝ] B) 1).exists_isMaxOn
    ⟨0, by simp⟩ hD.continuousOn
  have hDT : 0 < D T := hDpos.trans_le (hmax (by simpa using hcnorm))
  refine ⟨T, by simpa using hT, fun A hA => ?_⟩
  have hh : D (T.comp A) ≤ D T := hmax (by simpa using hA)
  have hprod : D (T.comp A) = D T * |A.det| := by
    change |LinearMap.det ((e.symm.toLinearMap.comp T.toLinearMap).comp A.toLinearMap)| = _
    rw [LinearMap.det_comp, abs_mul]
    rfl
  rw [hprod] at hh
  exact le_of_mul_le_mul_left (by simpa only [mul_one] using hh) hDT

/-- Scaling a subspace S by a and its orthogonal complement by b has determinant
`a^(dim S) * b^(dim Sᗮ)`. The proof conjugates the sum of the orthogonal projections
to the corresponding product of scalar identity maps. -/
private theorem det_orthogonal_scaling {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [FiniteDimensional ℝ H] (S : Submodule ℝ H) (a b : ℝ) :
    ((a • S.starProjection + b • Sᗮ.starProjection).det) =
      a ^ finrank ℝ S * b ^ finrank ℝ Sᗮ := by
  let e := S.prodEquivOfIsCompl Sᗮ S.isCompl_orthogonal
  let L : (S × Sᗮ) →ₗ[ℝ] (S × Sᗮ) := LinearMap.prodMap
    (a • LinearMap.id) (b • LinearMap.id)
  have hzero₂ (y : Sᗮ) : S.starProjection y = 0 :=
    S.starProjection_apply_eq_zero_iff.mpr y.property
  have heq : (a • S.starProjection + b • Sᗮ.starProjection).toLinearMap =
      e.toLinearMap.comp (L.comp e.symm.toLinearMap) := by
    apply LinearMap.ext
    intro z
    obtain ⟨⟨x, y⟩, rfl⟩ := e.surjective z
    simp [e, L, Submodule.coe_prodEquivOfIsCompl', hzero₂]
  change LinearMap.det _ = _
  rw [heq, LinearMap.det_conj, LinearMap.det_prodMap, LinearMap.det_smul,
    LinearMap.det_smul, LinearMap.det_id, LinearMap.det_id, mul_one, mul_one]

/-- A determinant-maximizing contraction is larger than 1/4 on some unit vector in
Sᗮ whenever that complement has greater dimension than S. Otherwise scaling S by
1/2 and Sᗮ by 2 would preserve the contraction bound while increasing the determinant. -/
private theorem large_on_orthogonal {H B : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    (T : H →L[ℝ] B) (hT : ‖T‖ ≤ 1)
    (hmax : ∀ A : H →L[ℝ] H, ‖T.comp A‖ ≤ 1 → |A.det| ≤ 1)
    (S : Submodule ℝ H) (hdim : finrank ℝ S < finrank ℝ Sᗮ) :
    ∃ x : Sᗮ, ‖x‖ = 1 ∧ (1 / 4 : ℝ) < ‖T x‖ := by
  by_contra! hsmall
  have hp : ‖T.comp Sᗮ.subtypeL‖ ≤ (1 / 4 : ℝ) :=
    (T.comp Sᗮ.subtypeL).opNorm_le_of_unit_norm (by norm_num) hsmall
  have hp₁ : ‖T.comp S.starProjection‖ ≤ 1 := by
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (by simpa using mul_le_mul hT S.starProjection_norm_le (norm_nonneg _) zero_le_one)
  have hp₂ : ‖T.comp Sᗮ.starProjection‖ ≤ (1 / 4 : ℝ) := by
    change ‖(T.comp Sᗮ.subtypeL).comp Sᗮ.orthogonalProjectionOnto‖ ≤ _
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (by
        simpa using mul_le_mul hp Sᗮ.orthogonalProjectionOnto_norm_le
          (norm_nonneg Sᗮ.orthogonalProjectionOnto) (by norm_num : (0 : ℝ) ≤ 1 / 4))
  let A : H →L[ℝ] H := (1 / 2 : ℝ) • S.starProjection + (2 : ℝ) • Sᗮ.starProjection
  have hA : ‖T.comp A‖ ≤ 1 := by
    calc
      _ = ‖(1 / 2 : ℝ) • T.comp S.starProjection + (2 : ℝ) • T.comp Sᗮ.starProjection‖ := by
        congr 1
        ext x
        simp [A]
      _ ≤ ‖(1 / 2 : ℝ) • T.comp S.starProjection‖ + ‖(2 : ℝ) • T.comp Sᗮ.starProjection‖ :=
        norm_add_le _ _
      _ ≤ 1 := by
        rw [norm_smul, norm_smul]
        norm_num
        linarith
  have hh := hmax A hA
  rw [det_orthogonal_scaling] at hh
  rw [abs_of_nonneg (by positivity), one_div, inv_pow, inv_mul_eq_div] at hh
  have hpow : (2 : ℝ) ^ finrank ℝ S < 2 ^ finrank ℝ Sᗮ :=
    pow_lt_pow_right₀ (by norm_num) hdim
  exact (not_le_of_gt hpow) ((div_le_one (by positivity)).mp hh)

/-- A determinant-maximizing contraction from a space of dimension at least 2n
has norm greater than 1/4 on n orthonormal vectors. Inductively apply
`large_on_orthogonal` to the span of the vectors already chosen. -/
private theorem orthonormal_large_family {H B : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    (T : H →L[ℝ] B) (hT : ‖T‖ ≤ 1)
    (hmax : ∀ A : H →L[ℝ] H, ‖T.comp A‖ ≤ 1 → |A.det| ≤ 1)
    (n : ℕ) (hn : 2 * n ≤ finrank ℝ H) :
    ∃ v : Fin n → H, Orthonormal ℝ v ∧ ∀ i, (1 / 4 : ℝ) < ‖T (v i)‖ := by
  classical
  induction n with
  | zero =>
    exact ⟨Fin.elim0, by simp [Orthonormal], by simp⟩
  | succ n ih =>
    obtain ⟨v, hv, hlarge⟩ := ih (by omega)
    let S := Submodule.span ℝ (Set.range v)
    have hS : finrank ℝ S = n := by
      simpa using finrank_span_eq_card hv.linearIndependent
    have hdim := S.finrank_add_finrank_orthogonal
    obtain ⟨x, hx, hTx⟩ := large_on_orthogonal T hT hmax S (by omega)
    have horth (i : Fin n) : inner ℝ (v i) (x : H) = 0 :=
      (S.mem_orthogonal x).mp x.property (v i) (Submodule.subset_span (Set.mem_range_self i))
    have horth' (i : Fin n) : inner ℝ (x : H) (v i) = 0 := by
      rw [real_inner_comm]
      exact horth i
    refine ⟨Fin.cons (x : H) v, ?_, ?_⟩
    · rw [orthonormal_iff_ite]
      intro i j
      refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
      · simp [show ‖(x : H)‖ = 1 from hx]
      · simp [horth', eq_comm]
      · simp [horth]
      · simpa using (orthonormal_iff_ite.mp hv) _ _
    · exact Fin.forall_fin_succ.mpr ⟨hTx, hlarge⟩

/-- For every n, an infinite-dimensional real normed space has n continuous dual
functionals with weak ell-two norm at most one and individual operator norms greater
than 1/4. Apply the determinant-maximization argument in a 2n-dimensional subspace
of the dual. The uniform lower bound drives the free-norm growth obstruction;
completeness of E is unnecessary. -/
theorem dual_euclidean_family {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hE : ¬ FiniteDimensional ℝ E) (n : ℕ) :
    ∃ φ : Fin n → Dual E, NormAdmissible Exponent.two φ ∧
      ∀ i, (1 / 4 : ℝ) < ‖φ i‖ := by
  classical
  have hdual : ¬ FiniteDimensional ℝ (Dual E) := by
    intro h
    let := h
    exact hE (FiniteDimensional.of_injective
      (NormedSpace.inclusionInDoubleDualLi ℝ (E := E)).toLinearMap
      (NormedSpace.inclusionInDoubleDualLi ℝ (E := E)).injective)
  have hrank : (2 * n : ℕ) ≤ Module.rank ℝ (Dual E) :=
    Cardinal.natCast_lt_aleph0.le.trans
      (not_lt.mp (fun h => hdual (Module.rank_lt_aleph0_iff.mp h)))
  obtain ⟨b, hb⟩ := exists_linearIndependent_of_le_rank hrank
  let B := Submodule.span ℝ (Set.range b)
  let : FiniteDimensional ℝ B := FiniteDimensional.span_of_finite (K := ℝ) (Set.finite_range b)
  let : Module.Free ℝ B := Module.Free.of_divisionRing ℝ B
  let H := EuclideanSpace ℝ (Fin (2 * n))
  have hdim : finrank ℝ H = finrank ℝ B := by
    simp only [H, finrank_euclideanSpace, Fintype.card_fin, B, finrank_span_eq_card hb]
  let e : H ≃L[ℝ] B := LinearEquiv.toContinuousLinearEquiv (𝕜 := ℝ) (E := H) (F := B)
    (LinearEquiv.ofFinrankEq (R := ℝ) H B hdim)
  obtain ⟨T, hT, hmax⟩ := volume_maximizer (H := H) (B := B) e
  obtain ⟨v, hv, hlarge⟩ := orthonormal_large_family T hT hmax n (by simp [H])
  let φ (i : Fin n) : Dual E := T (v i)
  have hsum (a : Fin n → ℝ) : ‖∑ i, a i • φ i‖ ≤ Real.sqrt (∑ i, a i ^ 2) := by
    have hvnorm : ‖∑ i, a i • v i‖ = Real.sqrt (∑ i, a i ^ 2) := by
      rw [← Real.sqrt_sq (norm_nonneg _), ← real_inner_self_eq_norm_sq, hv.inner_sum]
      simp [sq]
    calc
      _ = ‖T (∑ i, a i • v i)‖ := by
        simp only [map_sum, map_smul]
        change ‖∑ i, a i • φ i‖ = ‖((∑ i, a i • T (v i) : B) : Dual E)‖
        simp [φ]
      _ ≤ ‖∑ i, a i • v i‖ :=
        (T.le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) hT)
      _ = _ := hvnorm
  refine ⟨φ, ?_, hlarge⟩
  intro x hx
  have hnonneg : 0 ≤ ∑ i, (φ i x) ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have heval : (∑ i, (φ i x) • φ i) x = ∑ i, (φ i x) ^ 2 := by
    simp [sum_apply, smul_apply, smul_eq_mul, sq]
  have hh := (∑ i, (φ i x) • φ i).le_opNorm x
  simp only [heval, Real.norm_eq_abs, abs_of_nonneg hnonneg] at hh
  have hupper : ∑ i, (φ i x) ^ 2 ≤ Real.sqrt (∑ i, (φ i x) ^ 2) :=
    hh.trans ((mul_le_mul_of_nonneg_right (hsum (fun i => φ i x)) (norm_nonneg x)).trans
      (mul_le_of_le_one_right (Real.sqrt_nonneg _) hx))
  have hsqrt : Real.sqrt (∑ i, (φ i x) ^ 2) ≤ 1 := by
    nlinarith [Real.sq_sqrt hnonneg]
  simpa [scalarPSum, Exponent.two, Real.sqrt_eq_rpow, sq_abs] using hsqrt

end EuclideanFamilies
end FBLOrderContinuousLH
