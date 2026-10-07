/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.FourierLeray
public import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# Real fields for Fourier multiplier operators

The Fourier symbols act on complex Euclidean component fields. These maps
connect them to the real Euclidean carriers used by `eq:reg-leray-symbol` and
`lem:reg-multiplier-bounds`.
-/

public section

open MeasureTheory
open scoped ENNReal FourierTransform

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic

/-- Real Euclidean tensor values on the three component indices. -/
abbrev RealTensor3 := PiLp 2 (fun _ : Fin 3 => L2Vec3)

/-- Real vector-valued spatial `L²` on the Euclidean three-dimensional carrier. -/
abbrev RealVectorL2 := Lp (α := L2Vec3) L2Vec3 2

/-- Complex vector-valued spatial `L²` on the Euclidean three-dimensional carrier. -/
abbrev ComplexVectorL2 := Lp (α := L2Vec3) ComplexVec3 2

/-- Real tensor-valued spatial `L²` on the Euclidean three-dimensional carrier. -/
abbrev RealTensorL2 := Lp (α := L2Vec3) RealTensor3 2

/-- Complex tensor-valued spatial `L²` on the Euclidean three-dimensional carrier. -/
abbrev ComplexTensorL2 := Lp (α := L2Vec3) ComplexTensor3 2

/-- The coordinate embedding of a real Euclidean vector into its complexification. -/
@[expose]
def complexifyValueLinear : L2Vec3 →ₗ[ℝ] ComplexVec3 where
  toFun := complexifyFrequency
  map_add' x y := by
    apply PiLp.ext
    intro i
    simp [complexifyFrequency]
  map_smul' c x := by
    apply PiLp.ext
    intro i
    simp [complexifyFrequency]

theorem complexifyValue_norm (x : L2Vec3) :
    ‖complexifyValueLinear x‖ = ‖x‖ := by
  exact complexifyFrequency_norm x

/-- The norm-preserving real-linear embedding of real Euclidean vectors into complex vectors. -/
@[expose]
def complexifyValue : L2Vec3 →L[ℝ] ComplexVec3 :=
  complexifyValueLinear.mkContinuous 1 (by
    intro x
    simp [complexifyValue_norm])

/-- Coordinatewise real part as a real-linear contraction on Euclidean vectors. -/
@[expose]
def realPartValueLinear : ComplexVec3 →ₗ[ℝ] L2Vec3 where
  toFun z := WithLp.toLp 2 (fun i => (z i).re)
  map_add' z w := by
    apply PiLp.ext
    intro i
    simp
  map_smul' c z := by
    apply PiLp.ext
    intro i
    simp [Complex.mul_re]

theorem realPartValue_norm_le (z : ComplexVec3) :
    ‖realPartValueLinear z‖ ≤ ‖z‖ := by
  rw [PiLp.norm_eq_of_L2, PiLp.norm_eq_of_L2]
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro i hi
  have hcoord : |(z i).re| ≤ ‖z i‖ := Complex.abs_re_le_norm (z i)
  have hsq : ((z i).re) ^ 2 ≤ ‖z i‖ ^ 2 := by
    have habs := abs_le.mp hcoord
    nlinarith only [habs.1, habs.2, norm_nonneg (z i)]
  simpa [realPartValueLinear] using hsq

/-- The coordinatewise real-part map on Euclidean vectors. -/
@[expose]
def realPartValue : ComplexVec3 →L[ℝ] L2Vec3 :=
  realPartValueLinear.mkContinuous 1 (by
    intro z
    simpa [one_mul] using realPartValue_norm_le z)

/-- Complexification of a real vector-valued spatial `L²` field. -/
@[expose]
def complexifyVectorL2 : RealVectorL2 →L[ℝ] ComplexVectorL2 :=
  complexifyValue.compLpL 2 volume

/-- Taking real parts of a complex vector-valued spatial `L²` field. -/
@[expose]
def realPartVectorL2 : ComplexVectorL2 →L[ℝ] RealVectorL2 :=
  realPartValue.compLpL 2 volume

theorem complexifyVectorL2_norm_le (f : RealVectorL2) :
    ‖complexifyVectorL2 f‖ ≤ ‖f‖ := by
  have hvalue : ‖complexifyValue‖ ≤ 1 :=
    LinearMap.mkContinuous_norm_le _ (by norm_num) (by
      intro x
      simp [complexifyValue_norm])
  calc
    ‖complexifyVectorL2 f‖ ≤ ‖complexifyVectorL2‖ * ‖f‖ :=
      complexifyVectorL2.le_opNorm f
    _ ≤ 1 * ‖f‖ := by
      gcongr
      exact (ContinuousLinearMap.norm_compLpL_le complexifyValue).trans hvalue
    _ = ‖f‖ := by ring

theorem realPartVectorL2_norm_le (f : ComplexVectorL2) :
    ‖realPartVectorL2 f‖ ≤ ‖f‖ := by
  have hvalue : ‖realPartValue‖ ≤ 1 :=
    LinearMap.mkContinuous_norm_le _ (by norm_num) (by
      intro x
      simpa [one_mul] using realPartValue_norm_le x)
  calc
    ‖realPartVectorL2 f‖ ≤ ‖realPartVectorL2‖ * ‖f‖ :=
      realPartVectorL2.le_opNorm f
    _ ≤ 1 * ‖f‖ := by
      gcongr
      exact (ContinuousLinearMap.norm_compLpL_le realPartValue).trans hvalue
    _ = ‖f‖ := by ring

/-- The coordinatewise complexification used by `lem:reg-multiplier-bounds`. -/
@[expose]
def complexifyTensorLinear : RealTensor3 →ₗ[ℝ] ComplexTensor3 where
  toFun F := WithLp.toLp 2 (fun i => complexifyValueLinear (F i))
  map_add' F G := by
    apply PiLp.ext
    intro i
    exact complexifyValueLinear.map_add (F i) (G i)
  map_smul' c F := by
    apply PiLp.ext
    intro i
    exact complexifyValueLinear.map_smul c (F i)

theorem complexifyTensor_norm (F : RealTensor3) :
    ‖complexifyTensorLinear F‖ = ‖F‖ := by
  rw [PiLp.norm_eq_of_L2, PiLp.norm_eq_of_L2]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  change ‖complexifyValueLinear (F i)‖ ^ 2 = ‖F i‖ ^ 2
  rw [complexifyValue_norm]

/-- The continuous tensor complexification used by `lem:reg-multiplier-bounds`. -/
@[expose]
def complexifyTensorValue : RealTensor3 →L[ℝ] ComplexTensor3 :=
  complexifyTensorLinear.mkContinuous 1 (by
    intro F
    simp [complexifyTensor_norm])

/-- Complexification of a real tensor-valued spatial `L²` field. -/
@[expose]
def complexifyTensorL2 : RealTensorL2 →L[ℝ] ComplexTensorL2 :=
  complexifyTensorValue.compLpL 2 volume

theorem complexifyTensorL2_norm_le (F : RealTensorL2) :
    ‖complexifyTensorL2 F‖ ≤ ‖F‖ := by
  have hvalue : ‖complexifyTensorValue‖ ≤ 1 :=
    LinearMap.mkContinuous_norm_le _ (by norm_num) (by
      intro x
      simp [complexifyTensor_norm])
  calc
    ‖complexifyTensorL2 F‖ ≤ ‖complexifyTensorL2‖ * ‖F‖ :=
      complexifyTensorL2.le_opNorm F
    _ ≤ 1 * ‖F‖ := by
      gcongr
      exact (ContinuousLinearMap.norm_compLpL_le complexifyTensorValue).trans hvalue
    _ = ‖F‖ := by ring

/-- The real heat multiplier operator, defined by complexification and real part. -/
@[expose]
noncomputable def realHeatOperator (t : ℝ) (ht : 0 ≤ t) :
    RealVectorL2 → RealVectorL2 :=
  fun f => realPartVectorL2 (heatSemigroup t ht (complexifyVectorL2 f))

/-- The real heat operator is an `L²` contraction, as in `lem:reg-multiplier-bounds`. -/
theorem realHeatOperator_norm_le (t : ℝ) (ht : 0 ≤ t) (f : RealVectorL2) :
    ‖realHeatOperator t ht f‖ ≤ ‖f‖ := by
  exact (realPartVectorL2_norm_le _).trans
    ((heatSemigroup_norm_le t ht _).trans (complexifyVectorL2_norm_le f))

/-- The real Leray projection, defined by complexification and real part. -/
@[expose]
noncomputable def realLerayProjection (f : RealVectorL2) : RealVectorL2 :=
  realPartVectorL2 (lerayProjectionL2 (complexifyVectorL2 f))

/-- The real Leray projection is an `L²` contraction, as in `lem:reg-multiplier-bounds`. -/
theorem realLerayProjection_norm_le (f : RealVectorL2) :
    ‖realLerayProjection f‖ ≤ ‖f‖ := by
  exact (realPartVectorL2_norm_le _).trans
    ((lerayProjectionL2_norm_le _).trans (complexifyVectorL2_norm_le f))

/-- The real Stokes operator, defined by complexification and real part. -/
@[expose]
noncomputable def realStokesOperator {t : ℝ} (ht : 0 < t) :
    RealTensorL2 → RealVectorL2 :=
  fun F => realPartVectorL2 (stokesL2Operator ht (complexifyTensorL2 F))

/-- The real Stokes operator has the Fourier multiplier bound of
`lem:reg-multiplier-bounds`. -/
theorem realStokesOperator_norm_le {t : ℝ} (ht : 0 < t) (F : RealTensorL2) :
    ‖realStokesOperator ht F‖ ≤ 1 / √(2 * Real.exp 1 * t) * ‖F‖ := by
  calc
    ‖realStokesOperator ht F‖ ≤ ‖stokesL2Operator ht (complexifyTensorL2 F)‖ :=
      realPartVectorL2_norm_le _
    _ ≤ 1 / √(2 * Real.exp 1 * t) * ‖complexifyTensorL2 F‖ :=
      stokesL2Operator_norm_le ht _
    _ ≤ 1 / √(2 * Real.exp 1 * t) * ‖F‖ := by
      gcongr
      exact complexifyTensorL2_norm_le F

end CKN.Leray
