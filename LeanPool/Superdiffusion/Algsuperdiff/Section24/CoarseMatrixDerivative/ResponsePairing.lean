/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section24.CoarseMatrixDerivative.BoundedField
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.Existence
public import LeanPool.Superdiffusion.Support.Book.Ch02.Theorems.GradientLinearity
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.GradientUniqueness

/-!
# ResponsePairing

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The response pairing defining `D_h`

This module builds the canonical bilinear pairing used internally to construct
the matrix and proves that its value agrees with every choice of maximizing
representatives in the source statement.
-/

namespace Algsuperdiff.Section24.CoarseMatrixDerivative.Internal

open Algsuperdiff.Frozen.Section24
open HCPolySupport HCPolySupport.Book.Ch02 MeasureTheory

noncomputable section

variable {d : ℕ}

/-- The canonical response gradient for the transposed coefficient. -/
def adjointResponseGradient (U : Domain d) (a : CoeffOn U) :
    BlockVec d → Vec d → Vec d :=
  fun P =>
    (canonicalMaximizer
      (responseExistenceTheory U a.transpose) P.1 P.2).toSolution.toH1.grad

/-- The canonical response gradient for the primal coefficient. -/
def primalResponseGradient (U : Domain d) (a : CoeffOn U) :
    BlockVec d → Vec d → Vec d :=
  fun P =>
    (canonicalMaximizer
      (responseExistenceTheory U a) P.1 (-P.2)).toSolution.toH1.grad

/-- The averaged perturbation pairing of adjoint and primal response gradients. -/
def pairing (U : Domain d) (a : CoeffOn U) (h : LInfMatrixFieldOn U)
    (P Q : BlockVec d) : ℝ :=
  volumeAverage (U : Set (Vec d)) (fun x =>
    vecDot (adjointResponseGradient U a P x)
      (matVecMul (h.1 x) (primalResponseGradient U a Q x)))

/-- The diagonal quadratic form of the response-gradient perturbation pairing. -/
def quadraticForm (U : Domain d) (a : CoeffOn U) (h : LInfMatrixFieldOn U)
    (P : BlockVec d) : ℝ :=
  pairing U a h P P

theorem adjointResponseGradient_add (U : Domain d) (a : CoeffOn U)
    (X Y : BlockVec d) :
    adjointResponseGradient U a (X + Y)
      =ᵐ[volumeMeasureOn (U : Set (Vec d))]
        fun x => adjointResponseGradient U a X x + adjointResponseGradient U a Y x := by
  have h := canonicalMaximizer_add_gradientAE (responseExistenceTheory U a.transpose)
    (responseGradientLinearityTheory U a.transpose) X.1 X.2 Y.1 Y.2
  simpa [adjointResponseGradient] using h

theorem adjointResponseGradient_smul (U : Domain d) (a : CoeffOn U)
    (c : ℝ) (X : BlockVec d) :
    adjointResponseGradient U a (c • X)
      =ᵐ[volumeMeasureOn (U : Set (Vec d))]
        fun x => c • adjointResponseGradient U a X x := by
  have h := canonicalMaximizer_smul_gradientAE (responseExistenceTheory U a.transpose)
    (responseGradientLinearityTheory U a.transpose) c X.1 X.2
  simpa [adjointResponseGradient] using h

theorem primalResponseGradient_add (U : Domain d) (a : CoeffOn U)
    (X Y : BlockVec d) :
    primalResponseGradient U a (X + Y)
      =ᵐ[volumeMeasureOn (U : Set (Vec d))]
        fun x => primalResponseGradient U a X x + primalResponseGradient U a Y x := by
  have h := canonicalMaximizer_add_gradientAE (responseExistenceTheory U a)
    (responseGradientLinearityTheory U a) X.1 (-X.2) Y.1 (-Y.2)
  have hsign : -X.2 + -Y.2 = -(X.2 + Y.2) := (neg_add X.2 Y.2).symm
  rw [hsign] at h
  simpa [primalResponseGradient] using h

theorem primalResponseGradient_smul (U : Domain d) (a : CoeffOn U)
    (c : ℝ) (X : BlockVec d) :
    primalResponseGradient U a (c • X)
      =ᵐ[volumeMeasureOn (U : Set (Vec d))]
        fun x => c • primalResponseGradient U a X x := by
  have h := canonicalMaximizer_smul_gradientAE (responseExistenceTheory U a)
    (responseGradientLinearityTheory U a) c X.1 (-X.2)
  have hsign : c • (-X.2) = -(c • X.2) := smul_neg c X.2
  rw [hsign] at h
  simpa [primalResponseGradient] using h

theorem pairing_integrable (U : Domain d) (a : CoeffOn U)
    (h : LInfMatrixFieldOn U) (P Q : BlockVec d) :
    IntegrableOn (fun x =>
      vecDot (adjointResponseGradient U a P x)
        (matVecMul (h.1 x) (primalResponseGradient U a Q x)))
      (U : Set (Vec d)) := by
  apply integrableOn_vecDot_of_memVectorL2
  · exact (canonicalMaximizer
      (responseExistenceTheory U a.transpose) P.1 P.2).toSolution.toH1.grad_memVectorL2
  · apply Algsuperdiff.Section24.memVectorL2_matVecMul_of_lInfMatrixFieldOn U h
    exact (canonicalMaximizer
      (responseExistenceTheory U a) Q.1 (-Q.2)).toSolution.toH1.grad_memVectorL2

theorem volumeAverage_congr_ae {U : Set (Vec d)} {f g : Vec d → ℝ}
    (hfg : f =ᵐ[volumeMeasureOn U] g) : volumeAverage U f = volumeAverage U g := by
  unfold volumeAverage
  congr 1
  exact integral_congr_ae hfg

theorem average_eq_of_isResponseMaximizers
    (U : Domain d) (a : CoeffOn U) (h : LInfMatrixFieldOn U)
    (p q : Vec d) (vAdj : Solution U a.transpose) (v : Solution U a)
    (hvAdj : IsResponseMaximizer U a.transpose p q vAdj)
    (hv : IsResponseMaximizer U a p (-q) v) :
    average U (fun x =>
      vecDot
        ((canonicalMaximizer
          (responseExistenceTheory U a.transpose) p q).toSolution.toH1.grad x)
        (matVecMul (h.1 x)
          ((canonicalMaximizer
            (responseExistenceTheory U a) p (-q)).toSolution.toH1.grad x))) =
      average U (fun x =>
        vecDot (vAdj.toH1.grad x) (matVecMul (h.1 x) (v.toH1.grad x))) := by
  change
    volumeAverage (U : Set (Vec d)) (fun x =>
      vecDot
        ((canonicalMaximizer
          (responseExistenceTheory U a.transpose) p q).toSolution.toH1.grad x)
        (matVecMul (h.1 x)
          ((canonicalMaximizer
            (responseExistenceTheory U a) p (-q)).toSolution.toH1.grad x))) =
      volumeAverage (U : Set (Vec d)) (fun x =>
        vecDot (vAdj.toH1.grad x) (matVecMul (h.1 x) (v.toH1.grad x)))
  apply volumeAverage_congr_ae
  have hadj := canonicalMaximizer_sameGradientAE_of_isResponseMaximizer hvAdj
  have hprimal := canonicalMaximizer_sameGradientAE_of_isResponseMaximizer hv
  filter_upwards [hadj, hprimal] with x hxadj hxprimal
  simp only [hxadj, hxprimal]

theorem pairing_add_left (U : Domain d) (a : CoeffOn U)
    (h : LInfMatrixFieldOn U) (X Y Z : BlockVec d) :
    pairing U a h (X + Y) Z = pairing U a h X Z + pairing U a h Y Z := by
  unfold pairing
  have hcongr :
      (fun x => vecDot (adjointResponseGradient U a (X + Y) x)
        (matVecMul (h.1 x) (primalResponseGradient U a Z x)))
        =ᵐ[volumeMeasureOn (U : Set (Vec d))]
      fun x => vecDot (adjointResponseGradient U a X x)
        (matVecMul (h.1 x) (primalResponseGradient U a Z x)) +
        vecDot (adjointResponseGradient U a Y x)
          (matVecMul (h.1 x) (primalResponseGradient U a Z x)) := by
    filter_upwards [adjointResponseGradient_add U a X Y] with x hx
    simp only [hx, vecDot_add_left]
  rw [volumeAverage_congr_ae hcongr]
  exact volumeAverage_add (pairing_integrable U a h X Z) (pairing_integrable U a h Y Z)

theorem pairing_smul_left (U : Domain d) (a : CoeffOn U)
    (h : LInfMatrixFieldOn U) (c : ℝ) (X Y : BlockVec d) :
    pairing U a h (c • X) Y = c * pairing U a h X Y := by
  unfold pairing
  have hcongr :
      (fun x => vecDot (adjointResponseGradient U a (c • X) x)
        (matVecMul (h.1 x) (primalResponseGradient U a Y x)))
        =ᵐ[volumeMeasureOn (U : Set (Vec d))]
      fun x => c • vecDot (adjointResponseGradient U a X x)
        (matVecMul (h.1 x) (primalResponseGradient U a Y x)) := by
    filter_upwards [adjointResponseGradient_smul U a c X] with x hx
    simp only [hx, vecDot_smul_left, smul_eq_mul]
  rw [volumeAverage_congr_ae hcongr]
  simpa [smul_eq_mul] using!
    (volumeAverage_smul (U : Set (Vec d)) c (fun x =>
      vecDot (adjointResponseGradient U a X x)
        (matVecMul (h.1 x) (primalResponseGradient U a Y x))))

theorem pairing_add_right (U : Domain d) (a : CoeffOn U)
    (h : LInfMatrixFieldOn U) (X Y Z : BlockVec d) :
    pairing U a h X (Y + Z) = pairing U a h X Y + pairing U a h X Z := by
  unfold pairing
  have hcongr :
      (fun x => vecDot (adjointResponseGradient U a X x)
        (matVecMul (h.1 x) (primalResponseGradient U a (Y + Z) x)))
        =ᵐ[volumeMeasureOn (U : Set (Vec d))]
      fun x => vecDot (adjointResponseGradient U a X x)
        (matVecMul (h.1 x) (primalResponseGradient U a Y x)) +
        vecDot (adjointResponseGradient U a X x)
          (matVecMul (h.1 x) (primalResponseGradient U a Z x)) := by
    filter_upwards [primalResponseGradient_add U a Y Z] with x hx
    simp only [hx, matVecMul_add, vecDot_add_right]
  rw [volumeAverage_congr_ae hcongr]
  exact volumeAverage_add (pairing_integrable U a h X Y) (pairing_integrable U a h X Z)

theorem pairing_smul_right (U : Domain d) (a : CoeffOn U)
    (h : LInfMatrixFieldOn U) (c : ℝ) (X Y : BlockVec d) :
    pairing U a h X (c • Y) = c * pairing U a h X Y := by
  unfold pairing
  have hcongr :
      (fun x => vecDot (adjointResponseGradient U a X x)
        (matVecMul (h.1 x) (primalResponseGradient U a (c • Y) x)))
        =ᵐ[volumeMeasureOn (U : Set (Vec d))]
      fun x => c • vecDot (adjointResponseGradient U a X x)
        (matVecMul (h.1 x) (primalResponseGradient U a Y x)) := by
    filter_upwards [primalResponseGradient_smul U a c Y] with x hx
    simp only [hx, matVecMul_smul, vecDot_smul_right, smul_eq_mul]
  rw [volumeAverage_congr_ae hcongr]
  simpa [smul_eq_mul] using!
    (volumeAverage_smul (U : Set (Vec d)) c (fun x =>
      vecDot (adjointResponseGradient U a X x)
        (matVecMul (h.1 x) (primalResponseGradient U a Y x))))

end

end Algsuperdiff.Section24.CoarseMatrixDerivative.Internal
