/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.ProductTestForms
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.SmoothDDCForm

/-!
# Genuine higher-degree complex differentials for Xiao's test forms

The complex structure is the existing real continuous linear map `v ↦ I • v`.
Holomorphic chart derivatives commute with this map, so composing every tensor
argument produces actual global smooth forms. The normalization agrees exactly
with the existing scalar `smoothDc` and `SmoothDDCForm.ddcForm`.
-/

@[expose] public section

open Set Filter
open scoped Topology Manifold ContDiff

namespace SGPT.Foundations.Analysis.Pending.XiaoComplexDifferential

open FirstPass FirstPass.MongeAmpere ProductTestForms StronglyPositiveForms

noncomputable section

variable {n k : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Pull every argument of an actual smooth form through the complex structure. -/
def complexTwist (a : SmoothRealForm n M k) : SmoothRealForm n M k where
  coeff e z := (a.coeff e z).compContinuousLinearMap (modelComplexStructure n)
  smooth e := SmoothRealForm.contDiffOn_compContinuousLinearMap (a.smooth e)
    contDiffOn_const
  compatible := by
    intro e f z hz v
    change a.coeff e z (fun i => Complex.I • v i) =
      a.coeff f (chartTransition e f z)
        (fun i => Complex.I • chartTransitionDerivative e f z (v i))
    rw [a.compatible e f z hz]
    congr 1
    funext i
    exact chartTransitionDerivative_complex_smul e f z hz Complex.I (v i)

@[simp] theorem complexTwist_coeff (a : SmoothRealForm n M k)
    (e : ComplexChart n M) (z : ComplexModel n) :
    (complexTwist a).coeff e z =
      (a.coeff e z).compContinuousLinearMap (modelComplexStructure n) := rfl

/-- The action of the complex structure on smooth forms is genuinely linear. -/
def complexTwistLM : SmoothRealForm n M k →ₗ[ℝ] SmoothRealForm n M k where
  toFun := complexTwist
  map_add' a b := smoothRealForm_ext fun e z => by
    ext v
    rfl
  map_smul' c a := smoothRealForm_ext fun e z => by
    ext v
    rfl

/-- The square of the complex action extracts one minus sign per argument. -/
theorem complexTwist_sq (a : SmoothRealForm n M k) :
    complexTwist (complexTwist a) = (-1 : ℝ) ^ k • a := by
  apply smoothRealForm_ext
  intro e z
  ext v
  change a.coeff e z (fun i => Complex.I • (Complex.I • v i)) =
    (-1 : ℝ) ^ k * a.coeff e z v
  have hvec : (fun i => Complex.I • (Complex.I • v i)) =
      fun i => (-1 : ℝ) • v i := by
    funext i
    simp [smul_smul, Complex.I_mul_I]
  rw [hvec, ContinuousAlternatingMap.map_smul_univ]
  simp

/-- The normalized actual complex differential of an arbitrary degree form. -/
def dc (a : SmoothRealForm n M k) : SmoothRealForm n M (k + 1) :=
  ((-1 : ℝ) ^ (k + 1) / (4 * Real.pi)) •
    complexTwist (complexTwist a).exteriorDerivative

/-- The actual second-order differential needed for Gauduchon test forms. -/
def ddc (a : SmoothRealForm n M k) : SmoothRealForm n M (k + 1 + 1) :=
  (dc a).exteriorDerivative

/-- The complex differential depends only on the actual form on chart targets. -/
theorem dc_geometricallyEq {a b : SmoothRealForm n M k}
    (h : a.GeometricallyEq b) : (dc a).GeometricallyEq (dc b) := by
  have htw : (complexTwist a).GeometricallyEq (complexTwist b) := by
    intro e z hz
    simp only [complexTwist_coeff, h e hz]
  have hd := htw.exteriorDerivative
  intro e z hz
  change _ • (complexTwist (complexTwist a).exteriorDerivative).coeff e z =
    _ • (complexTwist (complexTwist b).exteriorDerivative).coeff e z
  simp only [complexTwist_coeff, hd e hz]

/-- The genuine second-order differential respects geometric equality. -/
theorem ddc_geometricallyEq {a b : SmoothRealForm n M k}
    (h : a.GeometricallyEq b) : (ddc a).GeometricallyEq (ddc b) :=
  (dc_geometricallyEq h).exteriorDerivative

/-- Every actual `ddᶜ` form is closed by the actual exterior derivative theorem. -/
theorem ddc_isClosed (a : SmoothRealForm n M k) : (ddc a).IsClosed :=
  (dc a).exteriorDerivative_isClosed

/-- The actual chart formula for the normalized complex differential in degree `k`. -/
def localDc (a : ComplexModel n → RealForm n k) (z : ComplexModel n) : RealForm n (k + 1) :=
  ((-1 : ℝ) ^ (k + 1) / (4 * Real.pi)) •
    (extDeriv (fun y => (a y).compContinuousLinearMap (modelComplexStructure n))
      z).compContinuousLinearMap
      (modelComplexStructure n)

/-- The local construction is precisely the existing actual global coefficient. -/
theorem localDc_eq_dc_coeff
    (a : SmoothRealForm n M k) (e : ComplexChart n M) (z : ComplexModel n) :
    localDc (a.coeff e) z = (dc a).coeff e z := rfl

/-- On smooth scalar zero-forms the normalization is exactly the existing `dᶜ`. -/
theorem dc_smulFun_unitForm (f : M → ℝ) (hf : ChartSmooth (n := n) f) :
    dc (smulFun f hf (unitForm : SmoothRealForm n M 0)) = SmoothDDCForm.dcForm f hf := by
  apply smoothRealForm_ext
  intro e z
  have hcoeff : (complexTwist (smulFun f hf (unitForm : SmoothRealForm n M 0))).coeff e =
      fun y => ContinuousAlternatingMap.constOfIsEmpty ℝ (ComplexModel n) (Fin 0)
        (f (e.val.symm y)) := by
    funext y
    ext v
    simp [complexTwist, smulFun_coeff, unitForm_coeff, coordinateWedgeUnit]
  ext v
  simp only [dc, coeff_smul, complexTwist_coeff,
    SmoothRealForm.exteriorDerivative_coeff, hcoeff, extDeriv_constOfIsEmpty,
    ContinuousAlternatingMap.compContinuousLinearMap_apply,
    ContinuousAlternatingMap.smul_apply, SmoothDDCForm.dcForm_coeff]
  simp [modelComplexStructure_apply]

/-- The higher-degree construction extends the existing actual scalar `ddᶜ`. -/
theorem ddc_smulFun_unitForm (f : M → ℝ) (hf : ChartSmooth (n := n) f) :
    ddc (smulFun f hf (unitForm : SmoothRealForm n M 0)) = SmoothDDCForm.ddcForm f hf := by
  unfold ddc SmoothDDCForm.ddcForm
  rw [dc_smulFun_unitForm]

end

end SGPT.Foundations.Analysis.Pending.XiaoComplexDifferential
