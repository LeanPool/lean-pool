/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.LocalPotentialIndependence
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.MongeAmpere
public import Mathlib.LinearAlgebra.Alternating.DomCoprod

/-!
# The geometric meaning of the smooth Monge--Ampère density

This file connects the genuine real two-form `smoothDDC u z` with the complex
Hessian used by the smooth Monge--Ampère measure.  For a real two-form `A`, a
candidate normalized complex coefficient matrix is extracted from the standard
real complex frame by

`π * (A(eⱼ, I eₖ) - i A(eⱼ, eₖ))`.

For `A = ddᶜu`, this matrix is exactly `complexHessian u z`.  The determinant
coefficient `normalizedTopPowerDensity` is therefore the density
`smoothDensity u z`.

Mathlib currently has no bundled wedge operation on continuous alternating
maps.  We therefore wrap its algebraic finite-shuffle wedge and prove the
result continuous.  Iterating this operation gives a genuine continuous
alternating top-degree form, including the usual empty-product convention in
dimension zero.

The remaining geometric-density step is the finite-dimensional algebraic
identity
`actualTopPowerDensity A = normalizedTopPowerDensity A` for real `(1,1)` forms.
The definitions below keep the genuine wedge evaluation and the determinant
coefficient separate until that shuffle/determinant identity is proved.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory TopologicalSpace
open scoped ContDiff

namespace SGPT.Foundations.Analysis.FirstPass.MongeAmpere

variable {n : ℕ}

/-- A real continuous two-form on the standard complex model. -/
abbrev CoordinateRealTwoForm (n : ℕ) :=
  (ComplexModel n) [⋀^Fin 2]→L[ℝ] ℝ

/-- The algebraic exterior product of two real continuous alternating forms,
with the arguments reindexed from `Fin p ⊕ Fin q` to `Fin (p + q)`. -/
def coordinateWedgeAlternating {p q : ℕ}
    (A : (ComplexModel n) [⋀^Fin p]→L[ℝ] ℝ)
    (B : (ComplexModel n) [⋀^Fin q]→L[ℝ] ℝ) :
    (ComplexModel n) [⋀^Fin (p + q)]→ₗ[ℝ] ℝ :=
  (((TensorProduct.lid ℝ ℝ).toLinearMap.compAlternatingMap
      (A.toAlternatingMap.domCoprod B.toAlternatingMap)).domDomCongr
        finSumFinEquiv)

/-- The continuous multilinear concatenation used before alternatizing the
exterior product. -/
def coordinateWedgeRaw {p q : ℕ}
    (A : (ComplexModel n) [⋀^Fin p]→L[ℝ] ℝ)
    (B : (ComplexModel n) [⋀^Fin q]→L[ℝ] ℝ) : ContinuousMultilinearMap ℝ
      (fun _ : Fin p ⊕ Fin q => ComplexModel n) ℝ :=
  { toMultilinearMap := (TensorProduct.lid ℝ ℝ).toLinearMap.compMultilinearMap
      (MultilinearMap.domCoprod A.toAlternatingMap.toMultilinearMap
        B.toAlternatingMap.toMultilinearMap)
    cont := by
      change Continuous (fun v : Fin p ⊕ Fin q → ComplexModel n =>
        A (v ∘ Sum.inl) * B (v ∘ Sum.inr))
      fun_prop }

/-- The exterior product before reindexing its arguments from a sum to a
single finite type. -/
def coordinateWedgeSum {p q : ℕ}
    (A : (ComplexModel n) [⋀^Fin p]→L[ℝ] ℝ)
    (B : (ComplexModel n) [⋀^Fin q]→L[ℝ] ℝ) :
    (ComplexModel n) [⋀^(Fin p ⊕ Fin q)]→L[ℝ] ℝ :=
  ((p.factorial * q.factorial : ℝ)⁻¹) •
    (coordinateWedgeRaw A B).alternatization

/-- The genuine exterior product of two real continuous alternating forms. -/
def coordinateWedge {p q : ℕ}
    (A : (ComplexModel n) [⋀^Fin p]→L[ℝ] ℝ)
    (B : (ComplexModel n) [⋀^Fin q]→L[ℝ] ℝ) :
    (ComplexModel n) [⋀^Fin (p + q)]→L[ℝ] ℝ :=
  let alt := coordinateWedgeSum A B
  { alt.toAlternatingMap.domDomCongr finSumFinEquiv with
    toContinuousMultilinearMap :=
      { alt.toContinuousMultilinearMap.toMultilinearMap.domDomCongr finSumFinEquiv with
        cont := by
          change Continuous fun v => alt (v ∘ finSumFinEquiv)
          fun_prop } }

@[simp] theorem coordinateWedgeSum_toAlternatingMap {p q : ℕ}
    (A : (ComplexModel n) [⋀^Fin p]→L[ℝ] ℝ)
    (B : (ComplexModel n) [⋀^Fin q]→L[ℝ] ℝ) :
    (coordinateWedgeSum A B).toAlternatingMap =
      (TensorProduct.lid ℝ ℝ).toLinearMap.compAlternatingMap
        (A.toAlternatingMap.domCoprod B.toAlternatingMap) := by
  unfold coordinateWedgeSum
  rw [ContinuousAlternatingMap.toAlternatingMap_smul,
    ContinuousMultilinearMap.alternatization_apply_toAlternatingMap]
  unfold coordinateWedgeRaw
  rw [LinearMap.compMultilinearMap_alternatization,
    MultilinearMap.domCoprod_alternatization_eq
      A.toAlternatingMap B.toAlternatingMap]
  simp only [Fintype.card_fin, LinearMap.compAlternatingMap_smul]
  rw [← Nat.cast_smul_eq_nsmul ℝ, ← mul_smul]
  have hp : (p.factorial : ℝ) ≠ 0 := by positivity
  have hq : (q.factorial : ℝ) ≠ 0 := by positivity
  have hscale : ((p.factorial * q.factorial : ℝ)⁻¹) *
      ((p.factorial * q.factorial : ℕ) : ℝ) = 1 := by
    rw [Nat.cast_mul]
    exact inv_mul_cancel₀ (mul_ne_zero hp hq)
  rw [hscale, one_smul]

@[simp] theorem coordinateWedge_toAlternatingMap {p q : ℕ}
    (A : (ComplexModel n) [⋀^Fin p]→L[ℝ] ℝ)
    (B : (ComplexModel n) [⋀^Fin q]→L[ℝ] ℝ) :
    (coordinateWedge A B).toAlternatingMap = coordinateWedgeAlternating A B := by
  change (coordinateWedgeSum A B).toAlternatingMap.domDomCongr finSumFinEquiv =
    coordinateWedgeAlternating A B
  rw [coordinateWedgeSum_toAlternatingMap]
  rfl

/-- The empty real form, used as the unit for exterior powers. -/
def coordinateWedgeUnit :
    (ComplexModel n) [⋀^Fin 0]→L[ℝ] ℝ :=
  ContinuousAlternatingMap.constOfIsEmpty ℝ (ComplexModel n) (Fin 0) 1

/-- The genuine `k`-fold exterior power of a continuous real two-form. -/
def coordinateWedgePower (A : CoordinateRealTwoForm n) :
    (k : ℕ) → (ComplexModel n) [⋀^Fin (k * 2)]→L[ℝ] ℝ
  | 0 => coordinateWedgeUnit
  | 1 => A
  | k + 2 => by
      simpa [Nat.add_mul] using coordinateWedge (coordinateWedgePower A (k + 1)) A

/-- The standard interleaved real frame
`e₀, I e₀, e₁, I e₁, ...`. -/
def coordinateRealFrame (i : Fin (n * 2)) : ComplexModel n :=
  let ji := finProdFinEquiv.symm i
  if ji.2 = 0 then coordinateVector ji.1
  else Complex.I • coordinateVector ji.1

/-- Evaluation of a genuine top exterior power in the standard complex
orientation.  In dimension zero this evaluates the empty wedge on the empty
frame and hence equals one. -/
def actualTopPowerDensity (A : CoordinateRealTwoForm n) : ℝ :=
  coordinateWedgePower A n coordinateRealFrame

@[simp] theorem actualTopPowerDensity_zero
    (A : CoordinateRealTwoForm 0) : actualTopPowerDensity A = 1 := by
  simp [actualTopPowerDensity, coordinateWedgePower, coordinateWedgeUnit]

@[simp] theorem coordinateRealFrame_one_zero :
    coordinateRealFrame (0 : Fin 2) = coordinateVector (0 : Fin 1) := by
  rfl

@[simp] theorem coordinateRealFrame_one_one :
    coordinateRealFrame (1 : Fin 2) =
      Complex.I • coordinateVector (0 : Fin 1) := by
  rfl

/-- In complex dimension one, the actual top exterior power is just the
original two-form evaluated on the positively oriented real frame. -/
theorem actualTopPowerDensity_one (A : CoordinateRealTwoForm 1) :
    actualTopPowerDensity A =
      A ![coordinateVector (0 : Fin 1),
        Complex.I • coordinateVector (0 : Fin 1)] := by
  change A (@coordinateRealFrame 1) = _
  congr 1
  funext i
  fin_cases i <;> rfl

/-- The candidate normalized complex coefficient matrix extracted from a real
two-form in the standard complex frame.  If the form is of normalized real
type `(1,1)` and
`A = (i/(2π)) ∑ Hⱼₖ dzⱼ ∧ dzBarₖ`, this recovers `H`. -/
def normalizedHermitianMatrix (A : CoordinateRealTwoForm n) :
    Matrix (Fin n) (Fin n) ℂ := fun j k =>
  (Real.pi : ℂ) *
    ((A ![coordinateVector j, Complex.I • coordinateVector k] : ℂ) -
      Complex.I * (A ![coordinateVector j, coordinateVector k] : ℂ))

/-- The standard real-orientation coefficient of the top power of a normalized
real `(1,1)`-form, expressed by the determinant expansion. -/
def normalizedTopPowerDensity (A : CoordinateRealTwoForm n) : ℝ :=
  (complexTopCoefficient (normalizedHermitianMatrix A)).re

/-- The actual normalized exterior derivative of a twice differentiable real
function is of real type `(1,1)`. -/
theorem smoothDDC_isOneOne {u : ComplexModel n → ℝ} {z : ComplexModel n}
    (hu : ContDiffAt ℝ 2 u z) (v w : ComplexModel n) :
    smoothDDC u z ![Complex.I • v, Complex.I • w] = smoothDDC u z ![v, w] := by
  have hs (a b : ComplexModel n) : realHessian u z a b = realHessian u z b a := by
    simpa only [realHessian_eq_fderiv] using
      hu.isSymmSndFDerivAt (by norm_num) a b
  rw [smoothDDC_apply_eq_realHessian hu, smoothDDC_apply_eq_realHessian hu]
  simp only [smul_smul, Complex.I_mul_I, neg_one_smul]
  rw [show -v = (-1 : ℝ) • v by simp, realHessian_smul_right,
    show -w = (-1 : ℝ) • w by simp, realHessian_smul_right]
  norm_num
  rw [hs (Complex.I • w) v, hs (Complex.I • v) w]
  ring

/-- The coefficient matrix recovered from the genuine two-form `ddᶜu` is the
coordinate complex Hessian of `u`. -/
theorem normalizedHermitianMatrix_smoothDDC {u : ComplexModel n → ℝ}
    {z : ComplexModel n} (hu : ContDiffAt ℝ 2 u z) :
    normalizedHermitianMatrix (smoothDDC u z) = complexHessian u z := by
  have hs (a b : ComplexModel n) : realHessian u z a b = realHessian u z b a := by
    simpa only [realHessian_eq_fderiv] using
      hu.isSymmSndFDerivAt (by norm_num) a b
  have hA1 (j k : Fin n) :
      smoothDDC u z ![coordinateVector j, Complex.I • coordinateVector k] =
        (realHessian u z (Complex.I • coordinateVector j)
            (Complex.I • coordinateVector k) +
          realHessian u z (coordinateVector j) (coordinateVector k)) /
            (4 * Real.pi) := by
    rw [smoothDDC_apply_eq_realHessian hu]
    simp only [smul_smul, Complex.I_mul_I, neg_one_smul]
    rw [show -(coordinateVector k) = (-1 : ℝ) • coordinateVector k by simp,
      realHessian_smul_right]
    norm_num
    rw [hs (Complex.I • coordinateVector k) (Complex.I • coordinateVector j)]
  have hA2 (j k : Fin n) :
      smoothDDC u z ![coordinateVector j, coordinateVector k] =
        (realHessian u z (Complex.I • coordinateVector j) (coordinateVector k) -
          realHessian u z (coordinateVector j) (Complex.I • coordinateVector k)) /
            (4 * Real.pi) := by
    rw [smoothDDC_apply_eq_realHessian hu,
      hs (coordinateVector k) (Complex.I • coordinateVector j)]
  ext j k
  rw [normalizedHermitianMatrix, hA1, hA2]
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.sub_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      zero_mul, mul_zero, sub_zero, complexHessian, Complex.add_re,
      Complex.div_ofNat_re]
    field_simp [Real.pi_ne_zero]
    ring
  · simp only [Complex.mul_im, Complex.sub_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      zero_mul, one_mul, mul_zero, zero_add, complexHessian, Complex.add_im,
      Complex.div_ofNat_im]
    field_simp [Real.pi_ne_zero]
    ring

/-- Pointwise coordinate identity: the determinant coefficient recovered from
`ddᶜu` is the density used by `smoothDensity`.  This theorem does not identify
that coefficient with `actualTopPowerDensity`; that is precisely the remaining
shuffle/determinant identity described in the module documentation. -/
theorem normalizedTopPowerDensity_smoothDDC {u : ComplexModel n → ℝ}
    {z : ComplexModel n} (hu : ContDiffAt ℝ 2 u z) :
    normalizedTopPowerDensity (smoothDDC u z) = smoothDensity u z := by
  rw [normalizedTopPowerDensity, normalizedHermitianMatrix_smoothDDC hu]
  exact (smoothDensity_eq_re_topCoefficient u z).symm

/-- The smooth measure obtained from the determinant coefficient. -/
def coefficientSmoothMeasure (U : Opens (ComplexModel n))
    (u : ComplexModel n → ℝ) (_hu : IsSmoothPshOn U u) : Measure (ComplexModel n) :=
  (volume.restrict (U : Set (ComplexModel n))).withDensity
    (fun z => ENNReal.ofReal (normalizedTopPowerDensity (smoothDDC u z)))

/-- The coefficient measure is exactly the Hessian-density measure already used
in the Bedford--Taylor interface. -/
theorem coefficientSmoothMeasure_eq_smoothMeasure (U : Opens (ComplexModel n))
    (u : ComplexModel n → ℝ) (hu : IsSmoothPshOn U u) :
    coefficientSmoothMeasure U u hu = smoothMeasure U u hu := by
  unfold coefficientSmoothMeasure smoothMeasure
  apply withDensity_congr_ae
  apply ae_restrict_of_forall_mem U.isOpen.measurableSet
  intro z hz
  have hinf : ContDiffAt ℝ ∞ u z :=
    (hu.1 z hz).contDiffAt (U.isOpen.mem_nhds hz)
  have h2 : ContDiffAt ℝ 2 u z :=
    hinf.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  change ENNReal.ofReal (normalizedTopPowerDensity (smoothDDC u z)) =
    ENNReal.ofReal (smoothDensity u z)
  rw [normalizedTopPowerDensity_smoothDDC h2]

end SGPT.Foundations.Analysis.FirstPass.MongeAmpere
