/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.RoundedUnitCubeDirichletEuclideanHsRegularity
public import LeanPool.HighContrastHomogenization.Support.Deterministic.ConstantCoefficientDirichletBesov.CenteredCubeHsRegularity

/-!
# High-contrast homogenization:
Provider.Regularity.RoundedCenteredCubeDirichletEuclideanHsRegularity

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Rounded-reference Euclidean fractional regularity on centered cubes

The rounded-reference unit-cube response is pushed forward by the normalized
centered-cube dilation.  Its gradient is unchanged under pullback, the
constant-coefficient weak equation is preserved exactly, and the homogeneous
physical Euclidean fractional full norm gives the same scale factor on the
input and output.  Thus the unit-cube constant controls every centered
triadic scale.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory Set
open scoped ENNReal Matrix.Norms.L2Operator Pointwise

noncomputable section

variable {d : ℕ} {m : ℤ}

private theorem castH10Function_grad_roundedCenteredScale
    {U V : Set (Vec d)} (hUV : U = V) (u : H10Function U) (x : Vec d) :
    (hUV ▸ u).toH1Function.grad x = u.toH1Function.grad x := by
  subst V
  rfl

private theorem centeredOpenCube_eq_smul_unitCenteredOpenCube_rounded
    (m : ℤ) :
    openCubeSet (originCube d m) =
      centeredCubeScale m • openCubeSet (originCube d 0) := by
  simpa only [centeredCubeScale, cubeScaleFactor_originCube] using
    openCubeSet_originCube_eq_smul_originCube_zero (d := d) m

theorem unitCenteredOpenCube_eq_inv_smul_centeredOpenCube_rounded
    (m : ℤ) :
    openCubeSet (originCube d 0) =
      (centeredCubeScale m)⁻¹ • openCubeSet (originCube d m) := by
  rw [openCubeSet_originCube_eq_smul_originCube_zero (d := d) m]
  rw [show cubeScaleFactor (originCube d m) = centeredCubeScale m by rfl]
  rw [smul_smul, inv_mul_cancel₀ (centeredCubeScale_ne_zero m), one_smul]

/-- Inverse normalized dilation of a unit-cube zero-trace response to the
physical centered cube. -/
@[expose]
public noncomputable def roundedCenteredCubeNormalizedPushforward
    (m : ℤ) (u : H10Function (openCubeSet (originCube d 0))) :
    H10Function (openCubeSet (originCube d m)) :=
  centeredCubeScale m •
    H10Function.unscale (inv_pos.mpr (centeredCubeScale_pos m))
      (unitCenteredOpenCube_eq_inv_smul_centeredOpenCube_rounded m ▸ u)

private theorem roundedCenteredCubeNormalizedPushforward_grad
    (m : ℤ) (u : H10Function (openCubeSet (originCube d 0)))
    (y : Vec d) :
    (roundedCenteredCubeNormalizedPushforward m u).toH1Function.grad y =
      u.toH1Function.grad ((centeredCubeScale m)⁻¹ • y) := by
  unfold roundedCenteredCubeNormalizedPushforward
  change centeredCubeScale m •
      (H10Function.unscale (inv_pos.mpr (centeredCubeScale_pos m))
        (unitCenteredOpenCube_eq_inv_smul_centeredOpenCube_rounded m ▸
          u)).toH1Function.grad y = _
  rw [H10Function.unscale_toH1Function, H1Function.unscale_grad]
  rw [castH10Function_grad_roundedCenteredScale]
  ext i
  simp only [Pi.smul_apply, smul_eq_mul]
  field_simp [centeredCubeScale_ne_zero m]

private theorem setIntegral_centeredCube_comp_dilation_rounded
    (m : ℤ) (f : Vec d → ℝ) :
    ∫ x in openCubeSet (originCube d 0), f (centeredCubeScale m • x)
        ∂volume =
      ((centeredCubeScale m) ^ d)⁻¹ *
        ∫ y in openCubeSet (originCube d m), f y ∂volume := by
  have hchange := Measure.setIntegral_comp_smul_of_pos
    (μ := volume) (f := f) (s := openCubeSet (originCube d 0))
    (centeredCubeScale_pos m)
  rw [← centeredOpenCube_eq_smul_unitCenteredOpenCube_rounded (d := d) m]
    at hchange
  simpa only [centeredCubeScale, cubeScaleFactor_originCube,
    Module.finrank_fin_fun, smul_eq_mul] using hchange

/-- Normalized centered-cube pushforward preserves a constant-coefficient
zero-trace divergence-form weak equation. -/
private theorem
    isZeroTraceDirichletRhsWeakSolution_roundedCenteredCubeNormalizedPushforward
    (A : Mat d) (m : ℤ) (h : CenteredCubeEuclideanL2Field d m)
    (u : H10Function (openCubeSet (originCube d 0)))
    (hunit : IsZeroTraceDirichletRhsWeakSolution (constantCoeffField A)
      (openCubeSet (originCube d 0)) u (fun x ↦ -h.pullbackToUnit x)) :
    IsZeroTraceDirichletRhsWeakSolution (constantCoeffField A)
      (openCubeSet (originCube d m))
      (roundedCenteredCubeNormalizedPushforward m u) (fun y ↦ -h y) := by
  intro psi
  let w : H10Function (openCubeSet (originCube d m)) :=
    roundedCenteredCubeNormalizedPushforward m u
  let phi : H10Function (openCubeSet (originCube d 0)) :=
    centeredCubeNormalizedPullback psi
  let lhsPhysical : Vec d → ℝ := fun y ↦
    vecDot (matVecMul A (w.toH1Function.grad y))
      (psi.toH1Function.grad y)
  let rhsPhysical : Vec d → ℝ := fun y ↦
    vecDot (-h y) (psi.toH1Function.grad y)
  have hwGrad (x : Vec d) :
      w.toH1Function.grad (centeredCubeScale m • x) =
        u.toH1Function.grad x := by
    rw [show w = roundedCenteredCubeNormalizedPushforward m u by rfl]
    rw [roundedCenteredCubeNormalizedPushforward_grad]
    congr 2
    simp [centeredCubeScale_ne_zero m]
  have hphiGrad (x : Vec d) :
      phi.toH1Function.grad x =
        psi.toH1Function.grad (centeredCubeScale m • x) := by
    rw [show phi = centeredCubeNormalizedPullback psi by rfl]
    exact centeredCubeNormalizedPullback_grad psi x
  have hlhsPointwise (x : Vec d) :
      lhsPhysical (centeredCubeScale m • x) =
        vecDot (matVecMul A (u.toH1Function.grad x))
          (phi.toH1Function.grad x) := by
    dsimp only [lhsPhysical]
    rw [hwGrad, hphiGrad]
  have hrhsPointwise (x : Vec d) :
      rhsPhysical (centeredCubeScale m • x) =
        vecDot (-h.pullbackToUnit x) (phi.toH1Function.grad x) := by
    dsimp only [rhsPhysical]
    rw [CenteredCubeEuclideanL2Field.pullbackToUnit_apply, hphiGrad]
  have hlhsChange :
      ∫ x in openCubeSet (originCube d 0),
          vecDot (matVecMul A (u.toH1Function.grad x))
            (phi.toH1Function.grad x) ∂volume =
        ((centeredCubeScale m) ^ d)⁻¹ *
          ∫ y in openCubeSet (originCube d m), lhsPhysical y ∂volume := by
    rw [← setIntegral_centeredCube_comp_dilation_rounded m lhsPhysical]
    apply integral_congr_ae
    filter_upwards with x
    exact (hlhsPointwise x).symm
  have hrhsChange :
      ∫ x in openCubeSet (originCube d 0),
          vecDot (-h.pullbackToUnit x) (phi.toH1Function.grad x) ∂volume =
        ((centeredCubeScale m) ^ d)⁻¹ *
          ∫ y in openCubeSet (originCube d m), rhsPhysical y ∂volume := by
    rw [← setIntegral_centeredCube_comp_dilation_rounded m rhsPhysical]
    apply integral_congr_ae
    filter_upwards with x
    exact (hrhsPointwise x).symm
  have hunit' :
      ∫ x in openCubeSet (originCube d 0),
          vecDot (matVecMul A (u.toH1Function.grad x))
            (phi.toH1Function.grad x) ∂volume =
        ∫ x in openCubeSet (originCube d 0),
          vecDot (-h.pullbackToUnit x) (phi.toH1Function.grad x) ∂volume := by
    simpa only [constantCoeffField] using hunit phi
  have hscaled :
      ((centeredCubeScale m) ^ d)⁻¹ *
          ∫ y in openCubeSet (originCube d m), lhsPhysical y ∂volume =
        ((centeredCubeScale m) ^ d)⁻¹ *
          ∫ y in openCubeSet (originCube d m), rhsPhysical y ∂volume := by
    rw [← hlhsChange, ← hrhsChange]
    exact hunit'
  change
    (∫ y in openCubeSet (originCube d m), lhsPhysical y ∂volume) =
      ∫ y in openCubeSet (originCube d m), rhsPhysical y ∂volume
  exact mul_left_cancel₀
    (inv_ne_zero (pow_ne_zero d (centeredCubeScale_ne_zero m))) hscaled

private theorem unitCubeEuclideanL2Field_ext_roundedCenteredScale
    (F G : UnitCubeEuclideanL2Field d) (hFG : F.toField = G.toField) :
    F = G := by
  cases F with
  | mk F hF =>
      cases G with
      | mk G hG =>
          dsimp only at hFG
          subst G
          rfl

private theorem roundedCenteredCubeNormalizedPushforward_gradient_pullback
    (m : ℤ) (u : H10Function (openCubeSet (originCube d 0))) :
    (centeredCubeGradientEuclideanL2Field
        (roundedCenteredCubeNormalizedPushforward m u)).pullbackToUnit =
      unitCubeGradientEuclideanL2Field u := by
  apply unitCubeEuclideanL2Field_ext_roundedCenteredScale
  funext x
  rw [CenteredCubeEuclideanL2Field.pullbackToUnit_apply,
    centeredCubeGradientEuclideanL2Field_apply,
    roundedCenteredCubeNormalizedPushforward_grad,
    unitCubeGradientEuclideanL2Field_apply]
  congr 2
  simp [centeredCubeScale_ne_zero m]

/-- One selected order and one finite constant control rounded-reference
zero-trace responses on every centered triadic cube.  Physical output
membership and the homogeneous full-norm estimate are conclusions. -/
theorem exists_roundedCenteredCubeDirichletEuclideanHsRegularity
    (d : ℕ) [NeZero d] :
    ∃ s : FractionalOrder, s.1 < (1 : ℝ) / 12 ∧
      ∃ C : ℝ≥0∞, C < ∞ ∧
        ∀ (m : ℤ) (abar : Mat d) (hS : (symmPart abar).PosDef)
          (h : CenteredCubeEuclideanL2Field d m),
          MemCenteredCubeEuclideanHs s h →
            ∃ w : H10Function (openCubeSet (originCube d m)),
              IsZeroTraceDirichletRhsWeakSolution
                (constantCoeffField (roundedReferenceMatrix abar hS))
                (openCubeSet (originCube d m)) w (fun y ↦ -h y) ∧
              MemCenteredCubeEuclideanHs s
                (centeredCubeGradientEuclideanL2Field w) ∧
              centeredCubeEuclideanHsFullENorm s
                  (centeredCubeGradientEuclideanL2Field w) ≤
                C * centeredCubeEuclideanHsFullENorm s h := by
  rcases exists_roundedUnitCubeDirichletEuclideanHsRegularity d with
    ⟨s, hs, C, hC, hunit⟩
  refine ⟨s, hs, C, hC, ?_⟩
  intro m abar hS h hh
  have hhUnit : MemEuclideanHs s h.pullbackToUnit :=
    (memCenteredCubeEuclideanHs_iff_pullbackToUnit s h).mp hh
  rcases hunit abar hS h.pullbackToUnit hhUnit with
    ⟨u, huWeak, huMem, huEstimate⟩
  let w : H10Function (openCubeSet (originCube d m)) :=
    roundedCenteredCubeNormalizedPushforward m u
  have hwWeak : IsZeroTraceDirichletRhsWeakSolution
      (constantCoeffField (roundedReferenceMatrix abar hS))
      (openCubeSet (originCube d m)) w (fun y ↦ -h y) := by
    simpa only [w] using
      isZeroTraceDirichletRhsWeakSolution_roundedCenteredCubeNormalizedPushforward
        (roundedReferenceMatrix abar hS) m h u huWeak
  have hgradient :
      (centeredCubeGradientEuclideanL2Field w).pullbackToUnit =
        unitCubeGradientEuclideanL2Field u := by
    simpa only [w] using
      roundedCenteredCubeNormalizedPushforward_gradient_pullback m u
  have hwMem : MemCenteredCubeEuclideanHs s
      (centeredCubeGradientEuclideanL2Field w) := by
    apply (memCenteredCubeEuclideanHs_iff_pullbackToUnit s
      (centeredCubeGradientEuclideanL2Field w)).mpr
    rw [hgradient]
    exact huMem
  have hwEstimate : centeredCubeEuclideanHsFullENorm s
      (centeredCubeGradientEuclideanL2Field w) ≤
        C * centeredCubeEuclideanHsFullENorm s h := by
    rw [centeredCubeEuclideanHsFullENorm_eq_scale_mul_pullbackToUnit,
      centeredCubeEuclideanHsFullENorm_eq_scale_mul_pullbackToUnit,
      hgradient]
    calc
      (ENNReal.ofReal (centeredCubeScale m)) ^ (-s.1) *
          euclideanHsFullENorm s (unitCubeGradientEuclideanL2Field u) ≤
        (ENNReal.ofReal (centeredCubeScale m)) ^ (-s.1) *
          (C * euclideanHsFullENorm s h.pullbackToUnit) := by
            gcongr
      _ = C * ((ENNReal.ofReal (centeredCubeScale m)) ^ (-s.1) *
          euclideanHsFullENorm s h.pullbackToUnit) := by ring
  exact ⟨w, hwWeak, hwMem, hwEstimate⟩

end

end HighContrast
end HCPolySupport
