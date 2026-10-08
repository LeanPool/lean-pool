/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.CorrectorLocalEquation
public import LeanPool.HighContrastHomogenization.Support.Deterministic.HomogenizationBlackBoxes.DualityPositiveBridge

/-!
# High-contrast homogenization: Provider.Regularity.CorrectorIntrinsicSlope

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Intrinsic slope and growth classes for local correctors

The normalized slope is read directly from each local `L²` gradient class.
Raw vector fields enter only through an explicit almost-everywhere representative
lemma.  The admissibility predicates therefore carry no Cauchy certificate,
starting scale, or chosen pointwise global representative.
-/

open scoped ENNReal

namespace HCPolySupport
namespace HighContrast

noncomputable section

open MeasureTheory

private instance intrinsicSlopeCubeFiniteMeasure (d n : ℕ) :
    IsFiniteMeasure (volumeMeasureOn (localGradientCube d n)) := by
  simpa [localGradientCube, volumeMeasureOn] using
    (isOpenBoundedConvexDomain_openCubeSet
      (originCube d (n : ℤ))).isFiniteMeasure_restrict_volume

/-- The normalized coordinate integral of a local gradient `L²` class. -/
@[expose]
noncomputable def localGradientClassAverage {d n : ℕ}
    (g : LocalGradientL2 d n) : Vec d :=
  fun i =>
    (cubeVolume (originCube d (n : ℤ)))⁻¹ *
      hilbertVectorL2CoordSetIntegralCLM
        (U := localGradientCube d n)
        (localGradientCube d n)
        (by simpa only [localGradientCube] using
          measurableSet_openCubeSet (originCube d (n : ℤ))) i g

/-- The class average is the usual cube average of any raw representative
which agrees with the class almost everywhere on the open cube. -/
theorem localGradientClassAverage_eq_cubeAverageVec_of_ae {d n : ℕ}
    (g : LocalGradientL2 d n) (G : Vec d → Vec d)
    (hG : g =ᵐ[volumeMeasureOn (localGradientCube d n)]
      fun x => HilbertVec.ofVec (G x)) :
    localGradientClassAverage g = cubeAverageVec (originCube d (n : ℤ)) G := by
  funext i
  rw [localGradientClassAverage, hilbertVectorL2CoordSetIntegralCLM_apply]
  rw [cubeAverageVec, cubeAverage_eq_inv_cubeVolume_mul_setIntegral_openCubeSet]
  congr 1
  let U : Set (Vec d) := openCubeSet (originCube d (n : ℤ))
  have hU : MeasurableSet U := measurableSet_openCubeSet _
  change
    (∫ x, g x i ∂(volume.restrict U).restrict U) =
      ∫ x, G x i ∂volume.restrict U
  rw [Measure.restrict_restrict hU, Set.inter_self]
  apply integral_congr_ae
  change (fun x => g x i) =ᵐ[volumeMeasureOn (localGradientCube d n)] fun x => G x i
  exact hG.mono fun _x hx => congrFun (congrArg HilbertVec.toVec hx) i

/-- Local gradient-class averaging is additive. -/
@[simp] theorem localGradientClassAverage_add {d n : ℕ}
    (g h : LocalGradientL2 d n) :
    localGradientClassAverage (g + h) =
      localGradientClassAverage g + localGradientClassAverage h := by
  funext i
  simp only [localGradientClassAverage, Pi.add_apply,
    map_add, mul_add]

/-- Local gradient-class averaging commutes with real scalar multiplication. -/
@[simp] theorem localGradientClassAverage_smul {d n : ℕ}
    (c : ℝ) (g : LocalGradientL2 d n) :
    localGradientClassAverage (c • g) = c • localGradientClassAverage g := by
  funext i
  simp only [localGradientClassAverage, Pi.smul_apply, smul_eq_mul,
    map_smul]
  ring

/-- The average of the zero local class is zero. -/
@[simp] theorem localGradientClassAverage_zero {d n : ℕ} :
    localGradientClassAverage (0 : LocalGradientL2 d n) = 0 := by
  funext i
  simp only [localGradientClassAverage, map_zero, mul_zero, Pi.zero_apply]

/-- Local gradient-class averaging commutes with negation. -/
@[simp] theorem localGradientClassAverage_neg {d n : ℕ}
    (g : LocalGradientL2 d n) :
    localGradientClassAverage (-g) = -localGradientClassAverage g := by
  simpa only [neg_one_smul] using
    localGradientClassAverage_smul (d := d) (n := n) (-1) g

/-- Local gradient-class averaging commutes with subtraction. -/
@[simp] theorem localGradientClassAverage_sub {d n : ℕ}
    (g h : LocalGradientL2 d n) :
    localGradientClassAverage (g - h) =
      localGradientClassAverage g - localGradientClassAverage h := by
  rw [sub_eq_add_neg, localGradientClassAverage_add,
    localGradientClassAverage_neg, sub_eq_add_neg]

/-- The full affine-plus-corrector local representative attached to an
intrinsic local carrier. -/
@[expose]
noncomputable def affinePlusLocalCarrierH1 {d : ℕ}
    (e : Vec d) (z : NormalizedLocalH1Carrier d) (n : ℕ) :
    H1Function (localGradientCube d n) :=
  (show H1Function (localGradientCube d n) from by
    simpa only [localGradientCube, Book.Ch02.cubeDomain_coe] using
      finiteAffineBoundaryH1 (n : ℤ) e) +
    z.localH1Function n

/-- The local class of the constant affine gradient has normalized average
equal to the declared affine slope. -/
theorem localGradientClassAverage_finiteAffineBoundaryH1
    {d : ℕ} (e : Vec d) (n : ℕ) :
    localGradientClassAverage
      (show LocalGradientL2 d n from
        Eq.mp (by simp only [LocalGradientL2, localGradientCube, Book.Ch02.cubeDomain_coe]; rfl)
          (finiteAffineBoundaryH1 (n : ℤ) e).gradToHilbertVectorL2) = e := by
  let u : H1Function (localGradientCube d n) := by
    simp only [localGradientCube]
    exact finiteAffineBoundaryH1 (n : ℤ) e
  have hcast :
      (show LocalGradientL2 d n from
        Eq.mp (by simp only [LocalGradientL2, localGradientCube, Book.Ch02.cubeDomain_coe]; rfl)
          (finiteAffineBoundaryH1 (n : ℤ) e).gradToHilbertVectorL2) =
        u.gradToHilbertVectorL2 := rfl
  rw [hcast, localGradientClassAverage_eq_cubeAverageVec_of_ae
    u.gradToHilbertVectorL2 u.grad u.coeFn_gradToHilbertVectorL2]
  have hugrad : u.grad = fun _ => e := finiteAffineBoundaryH1_grad (n : ℤ) e
  rw [hugrad]
  exact cubeAverageVec_const (originCube d (n : ℤ)) e

/-- The recovered full local gradient class is the affine constant class plus
the stored projective corrector component. -/
@[simp] theorem affinePlusLocalCarrierH1_gradToHilbertVectorL2
    {d : ℕ} (e : Vec d) (z : NormalizedLocalH1Carrier d)
    (n : ℕ) :
    (affinePlusLocalCarrierH1 e z n).gradToHilbertVectorL2 =
      (show LocalGradientL2 d n from
        Eq.mp (by simp only [LocalGradientL2, localGradientCube, Book.Ch02.cubeDomain_coe]; rfl)
          (finiteAffineBoundaryH1 (n : ℤ) e).gradToHilbertVectorL2) +
        z.gradientComponent n := by
  rw [affinePlusLocalCarrierH1, H1Function.gradToHilbertVectorL2_add,
    NormalizedLocalH1Carrier.localH1Function_gradToHilbertVectorL2]
  rfl

/-- Intrinsic normalized slope, stated only through local gradient classes. -/
@[expose]
def HasIntrinsicNormalizedSlope {d : ℕ}
    (e : Vec d) (z : NormalizedLocalH1Carrier d) : Prop :=
  Filter.Tendsto
    (fun n => localGradientClassAverage
      ((show LocalGradientL2 d n from
          Eq.mp (by simp only [LocalGradientL2, localGradientCube, Book.Ch02.cubeDomain_coe]; rfl)
            (finiteAffineBoundaryH1 (n : ℤ) e).gradToHilbertVectorL2) +
        z.gradientComponent n))
    Filter.atTop (nhds e)

end

end HighContrast
end HCPolySupport
