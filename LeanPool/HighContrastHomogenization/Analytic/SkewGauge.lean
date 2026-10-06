/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Analytic.CenteringInvariance
public import LeanPool.HighContrastHomogenization.Geometry.BlockBridge
public import LeanPool.HighContrastHomogenization.Geometry.SizeAlignment
public import LeanPool.HighContrastHomogenization.Provider.Response.ConstantSkewCentered
public import LeanPool.HighContrastHomogenization.Provider.SourceControl.SchurHelpers
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.DeterministicIdentities

/-!
# High-contrast homogenization: Analytic.SkewGauge

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Constant-skew gauge covariance

A constant skew matrix sends a Sobolev gradient to a solenoidal field.  This
makes its pairing with every compactly supported smooth gradient vanish and
shows that adding it to a coefficient field does not change the weak equation.
The same shift leaves every quantity built from the symmetric coefficient part
unchanged.  The final identities record the already available covariance of
the variational response under the matching shear of its loads.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- The weak pairing for a coefficient shifted by a constant matrix splits
into the original pairing and the constant-matrix pairing. -/
theorem weakPairing_add_const (b : CoeffField d) (k : Mat d)
    (F : Vec d → Vec d) (φ : Vec d → ℝ) :
    (fun x => vecDot (smoothGrad φ x) (matVecMul (b x + k) (F x))) =
      fun x => vecDot (smoothGrad φ x) (matVecMul (b x) (F x)) +
        vecDot (smoothGrad φ x) (matVecMul k (F x)) := by
  funext x
  simp only [vecDot, matVecMul, Matrix.add_apply, add_mul, mul_add,
    Finset.sum_add_distrib]

/-- A constant skew matrix paired with a weak gradient and a smooth test
gradient is absolutely integrable and has integral zero. -/
theorem integrableOn_and_integral_smoothGrad_skew_weakGradient_eq_zero
    {U : Set (Vec d)} [IsFiniteMeasure (volumeMeasureOn U)]
    (hU : IsOpen U) {u : Vec d → ℝ} {Du : Vec d → Vec d}
    (hu : MemScalarL2 U u) (hDu : ∀ i, MemScalarL2 U fun x => Du x i)
    (hweak : HasWeakGradientOn U u Du) (k : Mat d) (hk : IsSkewMat k)
    {φ : Vec d → ℝ} (hφ : IsLocalTest U φ) :
    IntegrableOn
        (fun x => vecDot (smoothGrad φ x) (matVecMul k (Du x))) U volume ∧
      ∫ x in U, vecDot (smoothGrad φ x) (matVecMul k (Du x)) ∂volume = 0 := by
  let v : H1Function U :=
    { toFun := u
      grad := Du
      memL2 := hu
      gradMemL2 := hDu
      hasWeakGradient := hweak }
  let φ₀ : H10Function U :=
    H10Function.ofContDiff hU hφ.contDiff hφ.hasCompactSupport hφ.tsupport_subset
  have hkDu : MemVectorL2 U (fun x => matVecMul k (v.grad x)) :=
    Response.memVectorL2_constMatrix_mul_gradient k v
  have hint : IntegrableOn
      (fun x => vecDot (φ₀.toH1Function.grad x) (matVecMul k (v.grad x))) U volume :=
    integrableOn_vecDot_of_memVectorL2 φ₀.toH1Function.grad_memVectorL2 hkDu
  have hzero :
      ∫ x in U, vecDot (matVecMul k (v.grad x)) (φ₀.toH1Function.grad x)
        ∂volume = 0 :=
    (Response.isSolenoidalOn_constSkew_mul_gradient hU k hk v) φ₀
  constructor
  · simpa [v, φ₀, H10Function.ofContDiff, H1Function.ofContDiff, smoothGrad] using! hint
  · calc
      ∫ x in U, vecDot (smoothGrad φ x) (matVecMul k (Du x)) ∂volume =
          ∫ x in U, vecDot (matVecMul k (Du x)) (smoothGrad φ x) ∂volume := by
            apply integral_congr_ae
            filter_upwards with x
            exact vecDot_comm _ _
      _ = 0 := by
        simpa [v, φ₀, H10Function.ofContDiff, H1Function.ofContDiff,
          smoothGrad] using! hzero

/-- Adding a constant skew matrix to a coefficient field leaves its weak
solution class unchanged on Sobolev gradients. -/
theorem isWeakSolutionOn_add_constSkew_iff
    {U : Set (Vec d)} [IsFiniteMeasure (volumeMeasureOn U)]
    (hU : IsOpen U) (b : CoeffField d) {u : Vec d → ℝ} {Du : Vec d → Vec d}
    (hu : MemScalarL2 U u) (hDu : ∀ i, MemScalarL2 U fun x => Du x i)
    (hweak : HasWeakGradientOn U u Du) (k : Mat d) (hk : IsSkewMat k) :
    IsWeakSolutionOn (fun x => b x + k) U Du ↔ IsWeakSolutionOn b U Du := by
  constructor
  · intro hshift φ hφ
    obtain ⟨hskewInt, hskewZero⟩ :=
      integrableOn_and_integral_smoothGrad_skew_weakGradient_eq_zero
        hU hu hDu hweak k hk hφ
    obtain ⟨hshiftInt, hshiftZero⟩ := hshift φ hφ
    have hsplit := weakPairing_add_const b k Du φ
    have hbaseEq :
        (fun x => vecDot (smoothGrad φ x) (matVecMul (b x) (Du x))) =
          fun x => vecDot (smoothGrad φ x) (matVecMul (b x + k) (Du x)) -
            vecDot (smoothGrad φ x) (matVecMul k (Du x)) := by
      funext x
      rw [congrFun hsplit x]
      ring
    constructor
    · rw [hbaseEq]
      exact hshiftInt.sub hskewInt
    · rw [hbaseEq, integral_sub hshiftInt hskewInt, hshiftZero, hskewZero,
        sub_zero]
  · intro hbase φ hφ
    obtain ⟨hskewInt, hskewZero⟩ :=
      integrableOn_and_integral_smoothGrad_skew_weakGradient_eq_zero
        hU hu hDu hweak k hk hφ
    obtain ⟨hbaseInt, hbaseZero⟩ := hbase φ hφ
    rw [weakPairing_add_const]
    exact ⟨hbaseInt.add hskewInt, by
      rw [integral_add hbaseInt hskewInt, hbaseZero, hskewZero, add_zero]⟩

/-- Adding a constant skew matrix does not change the weighted gradient norm. -/
theorem weightedGradNorm_add_constSkew (b : CoeffField d) (U : Set (Vec d))
    (F : Vec d → Vec d) (k : Mat d) (hk : IsSkewMat k) :
    weightedGradNorm (fun x => b x + k) U F = weightedGradNorm b U F := by
  unfold weightedGradNorm
  congr 2
  funext x
  rw [symmPart_add_isSkewMat hk]

/-- Adding a constant skew matrix does not change the symmetric energy. -/
theorem sEnergyOn_add_constSkew (b : CoeffField d) (U : Set (Vec d))
    (F : Vec d → Vec d) (k : Mat d) (hk : IsSkewMat k) :
    sEnergyOn (fun x => b x + k) U F = sEnergyOn b U F := by
  unfold sEnergyOn
  congr 2
  funext x
  rw [symmPart_add_isSkewMat hk]

/-- The full symmetric Sobolev energy is invariant under a constant skew
shift of the coefficient. -/
theorem h1sNormSqOn_add_constSkew (b : CoeffField d) (U : Set (Vec d))
    (u : Vec d → ℝ) (Du : Vec d → Vec d) (k : Mat d) (hk : IsSkewMat k) :
    h1sNormSqOn (fun x => b x + k) U u Du = h1sNormSqOn b U u Du := by
  unfold h1sNormSqOn
  rw [sEnergyOn_add_constSkew b U Du k hk]

end

end HighContrast
end HCPolySupport
