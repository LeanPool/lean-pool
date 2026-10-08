/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.RowSupplyAssembly.H10AffinePullback

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.Duality.H10AffinePullbackAssembly

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The `H10Function` affine pullback, assembled: the potential half

`HCPoly.Analytic.AffineWeakGradient` transports `H1Function` along an
invertible matrix, and
`HCPoly.Provider.PolynomialHomogenization.Root.RowSupplyAssembly.H10AffinePullback` supplies the
two
`eLpNorm` convergences of the approximating sequence.  This file assembles the
six `H10Function` fields and reads off the covariant transport of
`IsPotentialZeroTraceOn`, which is the potential half of the affine gauge move.

The `H1Function` pullback is built here as an explicit structure rather than
taken from the existential `exists_h1Function_affinePullback`, so that its two
projections reduce by `rfl` and the convergence fields are never matched through
an opaque witness.
-/

namespace HCPolySupport
namespace HighContrast
namespace RowSupply

open MeasureTheory _root_.Filter
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- Matrix action is additive on differences of vectors. -/
private theorem matVecMul_sub_vec (A : Mat d) (x y : Vec d) :
    matVecMul A (x - y) = matVecMul A x - matVecMul A y := by
  rw [sub_eq_add_neg, matVecMul_add, matVecMul_neg, ← sub_eq_add_neg]

/-- Componentwise form of the previous identity. -/
private theorem matVecMul_sub_apply (A : Mat d) (x y : Vec d) (i : Fin d) :
    matVecMul A (fun j => x j - y j) i = matVecMul A x i - matVecMul A y i :=
  congrFun (matVecMul_sub_vec A x y) i

/-- The gradient `L²` condition transports with the transpose matrix.  (The
proof of `exists_h1Function_affinePullback` uses a private lemma of the
same content; it is reproved here rather than imported.) -/
theorem gradMemL2On_affinePullbackTranspose {L : Mat d} (hL : IsUnit L.det)
    {U : Set (Vec d)} (hU : MeasurableSet U) {Du : Vec d → Vec d}
    (hDu : GradMemL2On U Du) :
    GradMemL2On (matImage L⁻¹ U)
      (fun y => matVecMul (matTranspose L) (Du (matVecMul L y))) := by
  intro i
  change MemL2On (matImage L⁻¹ U)
    (fun y => ∑ j, L j i * Du (matVecMul L y) j)
  exact memLp_finsetSum Finset.univ fun j _ =>
    (memL2On_affinePullback hL hU (hDu j)).const_mul (L j i)

/-- Almost-everywhere strong measurability survives the affine pullback. -/
private theorem aestronglyMeasurable_comp_matVecMul {L : Mat d} (hL : IsUnit L.det)
    {U : Set (Vec d)} (hU : MeasurableSet U) {f : Vec d → ℝ}
    (hf : AEStronglyMeasurable f (volume.restrict U)) :
    AEStronglyMeasurable (fun y => f (matVecMul L y))
      (volume.restrict (matImage L⁻¹ U)) := by
  have hmap := map_restrict_volume_affinePullback hL hU
  have haem : AEStronglyMeasurable f
      (Measure.map (matVecMul L) (volume.restrict (matImage L⁻¹ U))) := by
    rw [hmap]
    exact hf.smul_measure _
  exact haem.comp_aemeasurable (continuous_matVecMul L).measurable.aemeasurable

/-- Measurability of the scalar approximation defect. -/
private theorem aestronglyMeasurable_approx_sub {U : Set (Vec d)}
    (u : H10Function U) (n : ℕ) :
    AEStronglyMeasurable (fun x => u.approx n x - u.toH1Function.toFun x)
      (volume.restrict U) :=
  (u.approx_smooth n).continuous.aestronglyMeasurable.sub
    u.toH1Function.memL2.aestronglyMeasurable

/-- Measurability of the gradient approximation defect, componentwise. -/
private theorem aestronglyMeasurable_approxGrad_sub {U : Set (Vec d)}
    (u : H10Function U) (n : ℕ) (j : Fin d) :
    AEStronglyMeasurable
      (fun x => smoothGrad (u.approx n) x j - u.toH1Function.grad x j)
      (volume.restrict U) :=
  (((u.approx_smooth n).continuous_fderiv (by simp)).clm_apply
      continuous_const).aestronglyMeasurable.sub
    (u.toH1Function.gradMemL2 j).aestronglyMeasurable

/-- The scalar convergence field of the pulled-back `H¹₀` witness. -/
theorem tendsto_pullback_approx {L : Mat d} (hL : IsUnit L.det)
    {U : Set (Vec d)} (hU : MeasurableSet U) (u : H10Function U) :
    Tendsto (fun n => eLpNorm
        (fun y => u.approx n (matVecMul L y) -
          u.toH1Function.toFun (matVecMul L y)) 2
        (volume.restrict (matImage L⁻¹ U))) atTop (nhds 0) := by
  exact tendsto_eLpNorm_comp_matVecMul_zero hL hU
    (F := fun n x => u.approx n x - u.toH1Function.toFun x)
    (fun n => aestronglyMeasurable_approx_sub u n) u.tendsto_approx

/-- The gradient convergence field of the pulled-back `H¹₀` witness. -/
theorem tendsto_pullback_approx_grad {L : Mat d} (hL : IsUnit L.det)
    {U : Set (Vec d)} (hU : MeasurableSet U) (u : H10Function U) (i : Fin d) :
    Tendsto (fun n => eLpNorm
        (fun y => (fderiv ℝ (fun x => u.approx n (matVecMul L x)) y) (basisVec i) -
          matVecMul (matTranspose L) (u.toH1Function.grad (matVecMul L y)) i) 2
        (volume.restrict (matImage L⁻¹ U))) atTop (nhds 0) := by
  have hbase := tendsto_eLpNorm_transpose_comp_zero hL hU
    (D := fun n x j => smoothGrad (u.approx n) x j - u.toH1Function.grad x j)
    (fun n j => aestronglyMeasurable_approxGrad_sub u n j)
    (fun n j => aestronglyMeasurable_comp_matVecMul hL hU
      (aestronglyMeasurable_approxGrad_sub u n j))
    (fun j => u.tendsto_approx_grad j) i
  have heq : ∀ n : ℕ,
      (fun y => (fderiv ℝ (fun x => u.approx n (matVecMul L x)) y) (basisVec i) -
          matVecMul (matTranspose L) (u.toH1Function.grad (matVecMul L y)) i) =
        (fun y => matVecMul (matTranspose L)
          (fun j => smoothGrad (u.approx n) (matVecMul L y) j -
            u.toH1Function.grad (matVecMul L y) j) i) := by
    intro n
    funext y
    have hleft : (fderiv ℝ (fun x => u.approx n (matVecMul L x)) y) (basisVec i) =
        matVecMul (matTranspose L)
          (smoothGrad (u.approx n) (matVecMul L y)) i :=
      congrFun (smoothGrad_comp_matVecMul L (u.approx_smooth n) y) i
    rw [hleft, matVecMul_sub_apply]
  exact hbase.congr fun n => by rw [heq n]

/-- The affine pullback of an `H¹` witness, as an explicit structure. -/
@[expose]
public def h1AffinePullback {L : Mat d} (hL : IsUnit L.det)
    {U : Set (Vec d)} (hU : MeasurableSet U) (u : H1Function U) :
    H1Function (matImage L⁻¹ U) where
  toFun := fun y => u.toFun (matVecMul L y)
  grad := fun y => matVecMul (matTranspose L) (u.grad (matVecMul L y))
  memL2 := memL2On_affinePullback hL hU u.memL2
  gradMemL2 := gradMemL2On_affinePullbackTranspose hL hU u.gradMemL2
  hasWeakGradient :=
    hasWeakGradientOn_affinePullback hL hU u.memL2 u.gradMemL2 u.hasWeakGradient

/-- The affine pullback of an `H¹₀` witness, as an explicit structure. -/
@[expose]
public def h10AffinePullback {L : Mat d} (hL : IsUnit L.det)
    {U : Set (Vec d)} (hU : MeasurableSet U) (u : H10Function U) :
    H10Function (matImage L⁻¹ U) where
  toH1Function := h1AffinePullback hL hU u.toH1Function
  approx := fun n y => u.approx n (matVecMul L y)
  approx_smooth := fun n =>
    (isLocalTest_comp_matVecMul hL (f := u.approx n)
      ⟨u.approx_smooth n, u.approx_hasCompactSupport n,
        u.approx_support_subset n⟩).contDiff
  approx_hasCompactSupport := fun n =>
    (isLocalTest_comp_matVecMul hL (f := u.approx n)
      ⟨u.approx_smooth n, u.approx_hasCompactSupport n,
        u.approx_support_subset n⟩).hasCompactSupport
  approx_support_subset := fun n =>
    (isLocalTest_comp_matVecMul hL (f := u.approx n)
      ⟨u.approx_smooth n, u.approx_hasCompactSupport n,
        u.approx_support_subset n⟩).tsupport_subset
  tendsto_approx := by exact tendsto_pullback_approx hL hU u
  tendsto_approx_grad := fun i => by exact tendsto_pullback_approx_grad hL hU u i

/-- The covariant transport of the zero-trace potential predicate under an
invertible matrix: this is the potential half of the affine gauge move. -/
theorem isPotentialZeroTraceOn_affinePullback {L : Mat d} (hL : IsUnit L.det)
    {U : Set (Vec d)} (hU : MeasurableSet U) {f : Vec d → Vec d}
    (hf : IsPotentialZeroTraceOn U f) :
    IsPotentialZeroTraceOn (matImage L⁻¹ U)
      (fun y => matVecMul (matTranspose L) (f (matVecMul L y))) := by
  obtain ⟨u, hu⟩ := hf
  refine ⟨h10AffinePullback hL hU u, ?_⟩
  change (fun y => matVecMul (matTranspose L)
      (u.toH1Function.grad (matVecMul L y))) =
    fun y => matVecMul (matTranspose L) (f (matVecMul L y))
  rw [hu]

end

end RowSupply
end HighContrast
end HCPolySupport
