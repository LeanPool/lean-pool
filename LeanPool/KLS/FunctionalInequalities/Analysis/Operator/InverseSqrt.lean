/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.Operator.Coordinates
public import LeanPool.KLS.FunctionalInequalities.Analysis.Operator.Positive
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# The principal inverse square root of a positive operator

For a positive invertible operator `A` on a finite-dimensional real inner product space, the
principal
(positive) inverse square root `A^{-1/2}` is obtained from Mathlib's canonical matrix square root
`CFC.sqrt` of the inverse matrix in an orthonormal basis, pulled back to an operator. It is
positive,
self-adjoint, satisfies `σ² = σσ* = Ring.inverse A` and `A σσ* = σσ* A = 1`, is a unit, strictly
positive,
unique among positive operators with that square, and independent of the basis. Used for the
diffusion
coefficient `A_t^{-1/2}` of the BKL localization (67) (`KLS/BKL/Posterior/Covariance.lean`). At the
pinned
Mathlib the real continuous functional calculus on `E →L[ℝ] E` itself is not available (no instance
is
claimed). The root sandwiches the operator to the identity, `σ A σ = 1`, so it whitens the
covariance; no
transported-law whitening API (image law with mean `0` and covariance `Id`) is claimed yet. Section
`LocalLipschitz`: along a positive definite matrix profile the canonical
`CFC.sqrt` is locally Lipschitz (relative continuity of `CFC.sqrt` on the nonnegative cone, a local
positive floor,
and the Sylvester estimate of `Matrix/Positivity`), and `inverseSqrt ∘ A` is locally Lipschitz
whenever `Ring.inverse ∘ A`
is `C¹` with positive invertible values; nothing is claimed off the self-adjoint positive cone.
-/

@[expose] public section

noncomputable section
open scoped MatrixOrder RealInnerProductSpace

namespace FunctionalInequalities.Analysis

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

/--
The principal (positive) inverse square root of `A` computed in the orthonormal basis `b`: the
canonical
matrix `CFC.sqrt` of `(operatorMatrix b A)⁻¹`, pulled back to an operator. -/
def inverseSqrtIn (b : OrthonormalBasis ι ℝ E) (A : E →L[ℝ] E) : E →L[ℝ] E :=
  operatorOfMatrix b (CFC.sqrt ((operatorMatrix b A)⁻¹))

@[simp] theorem operatorMatrix_inverseSqrtIn (b : OrthonormalBasis ι ℝ E) (A : E →L[ℝ] E) :
    operatorMatrix b (inverseSqrtIn b A) = CFC.sqrt ((operatorMatrix b A)⁻¹) :=
  operatorMatrix_operatorOfMatrix b _

theorem inverseSqrtIn_isPositive (b : OrthonormalBasis ι ℝ E) (A : E →L[ℝ] E) :
    (inverseSqrtIn b A).IsPositive :=
  operatorOfMatrix_isPositive b _ (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg _))

theorem inverseSqrtIn_isSelfAdjoint (b : OrthonormalBasis ι ℝ E) (A : E →L[ℝ] E) :
    IsSelfAdjoint (inverseSqrtIn b A) := (inverseSqrtIn_isPositive b A).isSelfAdjoint

/-- `σ² = Ring.inverse A` for a positive unit `A`. -/
theorem inverseSqrtIn_mul_self (b : OrthonormalBasis ι ℝ E) (A : E →L[ℝ] E)
    (hpos : A.IsPositive) (hunit : IsUnit A) :
    inverseSqrtIn b A * inverseSqrtIn b A = Ring.inverse A := by
  apply operatorMatrix_injective b
  rw [operatorMatrix_mul]
  rw [operatorMatrix_inverseSqrtIn]
  rw [CFC.sqrt_mul_sqrt_self _ ((operatorMatrix_posSemidef_iff b A).mpr hpos).inv.nonneg,
    operatorMatrix_ringInverse b A hunit]

/-- `σ σ* = Ring.inverse A`. -/
theorem inverseSqrtIn_mul_adjoint (b : OrthonormalBasis ι ℝ E) (A : E →L[ℝ] E)
    (hpos : A.IsPositive) (hunit : IsUnit A) :
    inverseSqrtIn b A * (inverseSqrtIn b A).adjoint = Ring.inverse A := by
  have hsa : (inverseSqrtIn b A).adjoint = inverseSqrtIn b A :=
    inverseSqrtIn_isSelfAdjoint b A
  rw [hsa]
  exact inverseSqrtIn_mul_self b A hpos hunit

/-- `A σσ* = 1 = σσ* A`. -/
theorem inverseSqrtIn_mul_adjoint_cancel (b : OrthonormalBasis ι ℝ E) (A : E →L[ℝ] E)
    (hpos : A.IsPositive) (hunit : IsUnit A) :
    A * (inverseSqrtIn b A * (inverseSqrtIn b A).adjoint) = 1 ∧
      (inverseSqrtIn b A * (inverseSqrtIn b A).adjoint) * A = 1 := by
  rw [inverseSqrtIn_mul_adjoint b A hpos hunit]
  exact ⟨Ring.mul_inverse_cancel A hunit, Ring.inverse_mul_cancel A hunit⟩

/--
Uniqueness of the positive branch: any positive `S` with `S² = A⁻¹` equals `inverseSqrtIn b A`. -/
theorem inverseSqrtIn_unique (b : OrthonormalBasis ι ℝ E) (A S : E →L[ℝ] E) (hunit : IsUnit A)
    (hS : S.IsPositive) (hSquare : S * S = Ring.inverse A) : inverseSqrtIn b A = S := by
  apply operatorMatrix_injective b
  rw [operatorMatrix_inverseSqrtIn]
  apply CFC.sqrt_unique
  · rw [← operatorMatrix_mul, hSquare, operatorMatrix_ringInverse b A hunit]
  · exact ((operatorMatrix_posSemidef_iff b S).mpr hS).nonneg

theorem inverseSqrtIn_isUnit (b : OrthonormalBasis ι ℝ E) (A : E →L[ℝ] E)
    (hpos : A.IsPositive) (hunit : IsUnit A) : IsUnit (inverseSqrtIn b A) := by
  have hp : (operatorMatrix b A).PosDef :=
    ((operatorMatrix_posSemidef_iff b A).mpr hpos).posDef_iff_isUnit.mpr
      ((operatorMatrix_isUnit_iff b A).mpr hunit)
  apply (operatorMatrix_isUnit_iff b _).mp
  rw [operatorMatrix_inverseSqrtIn]
  exact (IsStrictlyPositive.sqrt _ hp.inv.isStrictlyPositive).isUnit

theorem inverseSqrtIn_inner_self_pos (b : OrthonormalBasis ι ℝ E) (A : E →L[ℝ] E)
    (hpos : A.IsPositive) (hunit : IsUnit A) {v : E} (hv : v ≠ 0) :
    0 < ⟪inverseSqrtIn b A v, v⟫ :=
  inner_self_pos_of_isPositive_of_isUnit b _ (inverseSqrtIn_isPositive b A)
    (inverseSqrtIn_isUnit b A hpos hunit) hv

/-- Basis independence (from uniqueness). -/
theorem inverseSqrtIn_eq_of_basis {κ : Type*} [Fintype κ] [DecidableEq κ]
    (b : OrthonormalBasis ι ℝ E) (c : OrthonormalBasis κ ℝ E) (A : E →L[ℝ] E)
    (hpos : A.IsPositive) (hunit : IsUnit A) :
    inverseSqrtIn b A = inverseSqrtIn c A :=
  inverseSqrtIn_unique b A _ hunit (inverseSqrtIn_isPositive c A)
    (inverseSqrtIn_mul_self c A hpos hunit)

/--
The principal inverse square root `A^{-1/2}` (in the standard orthonormal basis; basis independent
for
positive units). -/
def inverseSqrt (A : E →L[ℝ] E) : E →L[ℝ] E :=
  inverseSqrtIn (stdOrthonormalBasis ℝ E) A

/--
**Specification of `A^{-1/2}`** for a positive unit `A`: positive, self-adjoint, `σ² = σσ* =
Ring.inverse A`,
`A σσ* = σσ* A = 1`. -/
theorem inverseSqrt_spec (A : E →L[ℝ] E) (hpos : A.IsPositive) (hunit : IsUnit A) :
    (inverseSqrt A).IsPositive ∧
      IsSelfAdjoint (inverseSqrt A) ∧
        inverseSqrt A * inverseSqrt A = Ring.inverse A ∧
          inverseSqrt A * (inverseSqrt A).adjoint = Ring.inverse A ∧
            A * (inverseSqrt A * (inverseSqrt A).adjoint) = 1 ∧
              (inverseSqrt A * (inverseSqrt A).adjoint) * A = 1 := by
  exact
    ⟨inverseSqrtIn_isPositive _ A, inverseSqrtIn_isSelfAdjoint _ A,
      inverseSqrtIn_mul_self _ A hpos hunit, inverseSqrtIn_mul_adjoint _ A hpos hunit,
      inverseSqrtIn_mul_adjoint_cancel _ A hpos hunit⟩

theorem inverseSqrt_unique (A S : E →L[ℝ] E)
    (hunit : IsUnit A) (hS : S.IsPositive) (hSquare : S * S = Ring.inverse A) :
    inverseSqrt A = S := inverseSqrtIn_unique _ A S hunit hS hSquare

/--
**Root sandwich** `σ A σ = 1` for a positive unit `A` and `σ = inverseSqrt A`: from `A σσ = 1` and
`σ` a unit,
`(σ A σ) σ = σ`, so `σ A σ = 1` (no commutation of `σ` with `A` is used).
-/
theorem inverseSqrt_mul_mul_inverseSqrt (A : E →L[ℝ] E) (hpos : A.IsPositive)
    (hunit : IsUnit A) : inverseSqrt A * A * inverseSqrt A = 1 := by
  have hspec := inverseSqrt_spec A hpos hunit
  have hsa : IsSelfAdjoint (inverseSqrt A) := by aesop
  have hlraw : A * (inverseSqrt A * (inverseSqrt A).adjoint) = 1 := by aesop
  have hl : A * (inverseSqrt A * inverseSqrt A) = 1 := by
    simpa only [hsa.adjoint_eq] using hlraw
  have hσ : IsUnit (inverseSqrt A) := by
    change IsUnit (inverseSqrtIn (stdOrthonormalBasis ℝ E) A)
    exact inverseSqrtIn_isUnit (stdOrthonormalBasis ℝ E) A hpos hunit
  have heq : (inverseSqrt A * A * inverseSqrt A) * inverseSqrt A = 1 * inverseSqrt A := by
    calc
      (inverseSqrt A * A * inverseSqrt A) * inverseSqrt A =
          inverseSqrt A * (A * (inverseSqrt A * inverseSqrt A)) := by
        simp only [mul_assoc]
      _ = inverseSqrt A * 1 := by rw [hl]
      _ = 1 * inverseSqrt A := by simp
  exact hσ.mul_right_cancel heq

section LocalLipschitz

open Matrix Set Filter Topology
open scoped Matrix.Norms.L2Operator NNReal ContDiff

private theorem continuousOn_matrix_sqrt :
    ContinuousOn (CFC.sqrt : Matrix ι ι ℝ → Matrix ι ι ℝ) {M | 0 ≤ M} := CFC.continuousOn_sqrt

/--
**Local Lipschitz property of the canonical matrix square root** along a positive definite profile
`M`,
in the Frobenius norm: continuity of `CFC.sqrt` on the nonnegative cone gives a neighbourhood with a
common
positive floor, and the Sylvester estimate converts the Lipschitz estimate of `M` into one for `√M`.
No
regularity of the root is assumed. -/
theorem locallyLipschitz_matrixEntries_sqrt {X : Type*} [PseudoMetricSpace X]
    (M : X → Matrix ι ι ℝ) (hM : Continuous M) (hPD : ∀ x, (M x).PosDef)
    (hInput : LocallyLipschitz (fun x => matrixEntries (M x))) :
    LocallyLipschitz (fun x => matrixEntries (CFC.sqrt (M x))) := by
  have hroot : Continuous (fun x => CFC.sqrt (M x)) :=
    continuousOn_matrix_sqrt.comp_continuous hM (fun x => (hPD x).posSemidef.nonneg)
  have hE : Continuous (fun x => matrixEntries (CFC.sqrt (M x))) :=
    continuous_matrixEntries.comp hroot
  intro x0
  have hp0 : (CFC.sqrt (M x0)).PosDef :=
    (IsStrictlyPositive.sqrt _ (hPD x0).isStrictlyPositive).posDef
  obtain ⟨a, ha, hfloor⟩ := exists_quadraticFloor_of_posDef hp0
  have hclose : ∀ᶠ x in 𝓝 x0, ‖matrixEntries (CFC.sqrt (M x) - CFC.sqrt (M x0))‖ < a / 2 := by
    have h :=
      (hE.continuousAt (x := x0)).eventually
        (Metric.ball_mem_nhds (matrixEntries (CFC.sqrt (M x0))) (half_pos ha))
    simpa only [Metric.mem_ball, dist_eq_norm, matrixEntries_sub] using h
  obtain ⟨K, U, hU, hK⟩ := hInput x0
  let V := U ∩ {x | ‖matrixEntries (CFC.sqrt (M x) - CFC.sqrt (M x0))‖ < a / 2}
  have hV : V ∈ 𝓝 x0 := inter_mem hU hclose
  have hf (x : X) (hx : x ∈ V) : QuadraticFloor (CFC.sqrt (M x)) (a / 2) :=
    quadraticFloor_of_close hfloor hx.2.le
  refine ⟨K / (NNReal.mk a ha.le), V, hV, ?_⟩
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  have hSym : ∀ i j, CFC.sqrt (M y) i j = CFC.sqrt (M y) j i := by
    intro i j
    simpa only [star_trivial] using
      (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (M y))).isHermitian.apply j i
  have hbound :=
    root_difference_le_div (CFC.sqrt (M x)) (CFC.sqrt (M y)) (half_pos ha) (half_pos ha)
      (hf x hx) (hf y hy) hSym
  rw [CFC.sqrt_mul_sqrt_self _ (hPD x).posSemidef.nonneg,
    CFC.sqrt_mul_sqrt_self _ (hPD y).posSemidef.nonneg] at hbound
  have harg := hK.dist_le_mul x hx.1 y hy.1
  have hsum : a / 2 + a / 2 = a := by ring
  rw [hsum] at hbound
  simp only [dist_eq_norm, ← matrixEntries_sub] at harg ⊢
  have hc : ((K / (NNReal.mk a ha.le) : ℝ≥0) : ℝ) = (K : ℝ) / a := rfl
  rw [hc]
  calc
    ‖matrixEntries (CFC.sqrt (M x) - CFC.sqrt (M y))‖ ≤ ‖matrixEntries (M x - M y)‖ / a :=
      hbound
    _ ≤ ((K : ℝ) * dist x y) / a := div_le_div_of_nonneg_right harg ha.le
    _ = ((K : ℝ) / a) * dist x y := by ring

/-- The same, with the root read back as an operator in the operator norm. -/
theorem locallyLipschitz_operatorOfMatrix_sqrt {X : Type*} [PseudoMetricSpace X]
    (b : OrthonormalBasis ι ℝ E) (M : X → Matrix ι ι ℝ)
    (hM : Continuous M) (hPD : ∀ x, (M x).PosDef)
    (hInput : LocallyLipschitz (fun x => matrixEntries (M x))) :
    LocallyLipschitz (fun x => operatorOfMatrix b (CFC.sqrt (M x))) := by
  have h := (operatorOfMatrixL b).lipschitzWith.locallyLipschitz.comp
    (locallyLipschitz_matrixEntries_sqrt M hM hPD hInput)
  simpa only [Function.comp_def, operatorOfMatrixL_matrixEntries] using h

/--
**Local Lipschitz property of the principal inverse square root** along an operator profile `A` on a
normed parameter space: if `Ring.inverse ∘ A` is `C¹` with positive values and every `A p` is a
unit, then
`p ↦ inverseSqrt (A p)` is locally Lipschitz in the operator norm. -/
theorem locallyLipschitz_inverseSqrt_of_contDiff_ringInverse {P : Type*} [NormedAddCommGroup P]
    [NormedSpace ℝ P] (A : P → (E →L[ℝ] E)) (hpos : ∀ p, (Ring.inverse (A p)).IsPositive)
    (hunit : ∀ p, IsUnit (A p)) (hInverse : ContDiff ℝ 1 (fun p => Ring.inverse (A p))) :
    LocallyLipschitz (fun p => inverseSqrt (A p)) := by
  let b := stdOrthonormalBasis ℝ E
  let M := fun p => operatorMatrix b (Ring.inverse (A p))
  have hChart : ContDiff ℝ 1 (fun p => matrixEntries (M p)) := by
    simpa only [Function.comp_def, operatorMatrixL_apply] using
      (operatorMatrixL b).contDiff.comp hInverse
  have hPD : ∀ p, (M p).PosDef := by
    intro p
    apply ((operatorMatrix_posSemidef_iff b _).mpr (hpos p)).posDef_iff_isUnit.mpr
    apply (operatorMatrix_isUnit_iff b _).mpr
    exact (hunit p).ringInverse
  have hM : Continuous M := by
    exact
      (((LinearMap.toMatrixOrthonormal b).toAlgEquiv.toLinearMap.comp
              LinearMap.toContinuousLinearMap.symm.toLinearMap).toContinuousLinearMap).continuous.comp
        hInverse.continuous
  have h := locallyLipschitz_operatorOfMatrix_sqrt b M hM hPD hChart.locallyLipschitz
  have heq : (fun p => operatorOfMatrix b (CFC.sqrt (M p))) = (fun p => inverseSqrt (A p)) := by
    funext p
    unfold inverseSqrt inverseSqrtIn
    rw [operatorMatrix_ringInverse _ _ (hunit p)]
  rwa [heq] at h

end LocalLipschitz

end FunctionalInequalities.Analysis

namespace FunctionalInequalities.Analysis
open Filter Topology
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Inverse square roots of operators converging to `1` converge to `1`. -/
theorem tendsto_inverseSqrt_one [CompleteSpace E] [FiniteDimensional ℝ E] {Sg : ℕ → E →L[ℝ] E}
    (hSg : Tendsto Sg atTop (𝓝 1)) (hpos : ∀ᶠ R in atTop, (Sg R).IsPositive)
    (hunit : ∀ᶠ R in atTop, IsUnit (Sg R)) :
    Tendsto (fun R => inverseSqrt (Sg R)) atTop (𝓝 1) := by
  have hinv : Tendsto (fun R => Ring.inverse (Sg R)) atTop (𝓝 1) := by
    have := (NormedRing.inverse_continuousAt (1 : (E →L[ℝ] E)ˣ)).tendsto.comp hSg
    simpa [Function.comp_def] using this
  rw [tendsto_iff_norm_sub_tendsto_zero] at hinv ⊢
  refine squeeze_zero' (Eventually.of_forall fun R => norm_nonneg _) ?_ hinv
  filter_upwards [hpos, hunit] with R hp hu
  exact
    FunctionalInequalities.Analysis.norm_sub_one_le_of_isPositive_mul_self
      (inverseSqrt_spec _ hp hu).1 (inverseSqrt_spec _ hp hu).2.2.1


end FunctionalInequalities.Analysis
