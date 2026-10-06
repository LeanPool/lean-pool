/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Analytic.AffineWeakGradient
public import LeanPool.HighContrastHomogenization.Support.Sobolev.PotentialSolenoidal

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.RowSupplyAssembly.H10AffinePullback

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The `H10Function` affine pullback: the zero-trace half

`HCPoly.Analytic.AffineWeakGradient` already transports `H1Function` along
an invertible affine map (`exists_h1Function_affinePullback`).  What is missing —
and what `IsPotentialZeroTraceOn` needs, since it is stated as *existence of an
`H10Function` whose gradient is the field* — is the zero-trace half: the
approximating sequence and its two `eLpNorm` convergences.

Three of the six `H10Function` fields come free from the `isLocalTest_comp_matVecMul`, which is
exactly "smooth, compactly supported,
supported in the preimage".  The two convergences transport through the measure pushforward
`map_restrict_volume_affinePullback`, which contributes the
fixed Jacobian factor `|det L|⁻¹`; since that factor is a nonzero constant,
convergence to `0` is preserved.
-/

namespace HCPolySupport
namespace HighContrast
namespace RowSupply

open MeasureTheory _root_.Filter
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- `eLpNorm` of an affine pullback, in terms of the original, with the Jacobian
factor supplied by `map_restrict_volume_affinePullback`. -/
theorem eLpNorm_comp_matVecMul {L : Mat d} (hL : IsUnit L.det)
    {U : Set (Vec d)} (hU : MeasurableSet U) {f : Vec d → ℝ}
    (hf : AEStronglyMeasurable f (volume.restrict U)) :
    eLpNorm (fun y => f (matVecMul L y)) 2
        (volume.restrict (matImage L⁻¹ U)) =
      (ENNReal.ofReal (|L.det|⁻¹)) ^ (1 / (2 : ℝ)) *
        eLpNorm f 2 (volume.restrict U) := by
  have hmap := map_restrict_volume_affinePullback hL hU
  have hmeasL : Measurable (matVecMul L) := (continuous_matVecMul L).measurable
  have haem : AEStronglyMeasurable f
      (Measure.map (matVecMul L) (volume.restrict (matImage L⁻¹ U))) := by
    rw [hmap]
    exact hf.smul_measure _
  have hstep :
      eLpNorm (fun y => f (matVecMul L y)) 2
          (volume.restrict (matImage L⁻¹ U)) =
        eLpNorm f 2
          (Measure.map (matVecMul L)
            (volume.restrict (matImage L⁻¹ U))) :=
    (eLpNorm_map_measure haem hmeasL.aemeasurable).symm
  rw [hstep, hmap, eLpNorm_smul_measure_of_ne_top (by norm_num) _ _ hf]
  simp [ENNReal.toReal_ofNat]

/-- Convergence to zero of an `L²` sequence survives the affine pullback. -/
theorem tendsto_eLpNorm_comp_matVecMul_zero {L : Mat d} (hL : IsUnit L.det)
    {U : Set (Vec d)} (hU : MeasurableSet U) {F : ℕ → Vec d → ℝ}
    (hmeas : ∀ n, AEStronglyMeasurable (F n) (volume.restrict U))
    (h : Tendsto (fun n => eLpNorm (F n) 2 (volume.restrict U)) atTop (nhds 0)) :
    Tendsto (fun n => eLpNorm (fun y => F n (matVecMul L y)) 2
      (volume.restrict (matImage L⁻¹ U))) atTop (nhds 0) := by
  have hrw : ∀ n,
      eLpNorm (fun y => F n (matVecMul L y)) 2
          (volume.restrict (matImage L⁻¹ U)) =
        (ENNReal.ofReal (|L.det|⁻¹)) ^ (1 / (2 : ℝ)) *
          eLpNorm (F n) 2 (volume.restrict U) :=
    fun n => eLpNorm_comp_matVecMul hL hU (hmeas n)
  simp only [hrw]
  have hfin : (ENNReal.ofReal (|L.det|⁻¹)) ^ (1 / (2 : ℝ)) ≠ ⊤ :=
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top).ne
  simpa only [mul_zero] using
    ENNReal.Tendsto.const_mul h (Or.inr hfin)

/-- Componentwise convergence of the transposed pullback gradient. -/
theorem tendsto_eLpNorm_transpose_comp_zero {L : Mat d} (hL : IsUnit L.det)
    {U : Set (Vec d)} (hU : MeasurableSet U) {D : ℕ → Vec d → Vec d}
    (hmeas : ∀ n j, AEStronglyMeasurable (fun x => D n x j) (volume.restrict U))
    (hmeasV : ∀ n j, AEStronglyMeasurable
      (fun y => D n (matVecMul L y) j) (volume.restrict (matImage L⁻¹ U)))
    (h : ∀ j : Fin d,
      Tendsto (fun n => eLpNorm (fun x => D n x j) 2 (volume.restrict U))
        atTop (nhds 0)) (i : Fin d) :
    Tendsto (fun n => eLpNorm
      (fun y => matVecMul (matTranspose L) (D n (matVecMul L y)) i) 2
      (volume.restrict (matImage L⁻¹ U))) atTop (nhds 0) := by
  set V : Set (Vec d) := matImage L⁻¹ U with hV
  have hbound : ∀ n,
      eLpNorm (fun y => matVecMul (matTranspose L) (D n (matVecMul L y)) i) 2
          (volume.restrict V) ≤
        ∑ j : Fin d, eLpNorm
          (fun y => L j i * D n (matVecMul L y) j) 2 (volume.restrict V) := by
    intro n
    have hEq : (fun y => matVecMul (matTranspose L) (D n (matVecMul L y)) i) =
        ∑ j : Fin d, fun y => L j i * D n (matVecMul L y) j := by
      funext y
      simp only [Finset.sum_apply, matVecMul, matTranspose,
        Matrix.transpose_apply]
    rw [hEq]
    exact eLpNorm_sum_le (by norm_num)
  have hterm : ∀ j : Fin d,
      Tendsto (fun n => eLpNorm
        (fun y => L j i * D n (matVecMul L y) j) 2 (volume.restrict V))
        atTop (nhds 0) := by
    intro j
    have hbase := tendsto_eLpNorm_comp_matVecMul_zero hL hU
      (F := fun n x => D n x j) (fun n => hmeas n j) (h j)
    have hle : ∀ n,
        eLpNorm (fun y => L j i * D n (matVecMul L y) j) 2 (volume.restrict V) ≤
          ENNReal.ofReal (|L j i|) *
            eLpNorm (fun y => D n (matVecMul L y) j) 2 (volume.restrict V) := by
      intro n
      exact eLpNorm_le_mul_eLpNorm_of_ae_le_mul ((hmeasV n j).const_mul _)
        (_root_.Filter.Eventually.of_forall (fun y => by
          simp)) 2
    have hmul : Tendsto (fun n => ENNReal.ofReal (|L j i|) *
        eLpNorm (fun y => D n (matVecMul L y) j) 2 (volume.restrict V))
        atTop (nhds 0) := by
      simpa only [mul_zero] using
        ENNReal.Tendsto.const_mul hbase (Or.inr ENNReal.ofReal_ne_top)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hmul
      (_root_.Filter.Eventually.of_forall (fun _ => zero_le))
      (_root_.Filter.Eventually.of_forall hle)
  have hsum : Tendsto (fun n => ∑ j : Fin d, eLpNorm
      (fun y => L j i * D n (matVecMul L y) j) 2 (volume.restrict V))
      atTop (nhds 0) := by
    simpa using tendsto_finsetSum (Finset.univ : Finset (Fin d))
      (fun j _ => hterm j)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (_root_.Filter.Eventually.of_forall (fun _ => zero_le))
    (_root_.Filter.Eventually.of_forall hbound)

end

end RowSupply
end HighContrast
end HCPolySupport
