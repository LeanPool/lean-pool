/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
/- Modified by Lean Pool contributors for this port. -/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Integral.Interpolation
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Integral.Upper.Coefficients
public import LeanPool.ExactMatrixExponents.LinearAlgebra.TensorSpectrum.SeparationWeights
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Polynomial.ComplexPolynomialApproximation
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Tensor.ComplexTensorRestrictionComposition
public import LeanPool.ExactMatrixExponents.LinearAlgebra.TensorSpectrum.Blocks
public import LeanPool.ExactMatrixExponents.LinearAlgebra.TensorSpectrum.SeparationPolynomial

/-!
# Charged finite separation by local Fourier maps

The source is exactly `6 * M` full copies of the shared-first-leg tensor.
The target is the full direct sum of the sector tensors, each multiplied by
a length-`M` pairing on the second and third legs.  Local variables may have
negative weights; after Fourier projection every surviving total weight is
a nonnegative square, so the resulting coefficient array is polynomial.
-/

@[expose] public section

open MatrixMultiplicationAllFields.MatrixExponent.Integral
    MatrixMultiplicationAllFields.TensorSpectrum

noncomputable section

open MatrixMultiplicationAllFields.TensorSpectrum.Separation

open scoped BigOperators
open MatrixMultiplicationAllFields.MatrixMultiplication.Foundation

namespace MatrixMultiplicationAllFields.MatrixExponent.Integral.Upper.Separation

variable {X Y Z : Type*}

/-- The branch labels occur only on the last two legs of the input. -/
abbrev shared {M : ℕ} (A : Fin M → Tensor O X Y Z) :
    Tensor O X (Fin M × Y) (Fin M × Z) :=
  Tensor.sharedFirst A

export MatrixMultiplicationAllFields.TensorSpectrum.Separation
  (dotPairingX separated phase projected squareDegree separationPolynomial
    squareDegree_eq_zero_iff separationPolynomial_constant separationPolynomial_degree weightX
    weightY weightZ)

/-- Copy a specified source coordinate with a scalar depending only on the
target coordinate and the source's direct-sum copy number. -/
def copyLocal {L : ℕ} {S T : Type*} [DecidableEq S]
    (f : T → S) (a : T → Fin L → O) : T → (Fin L × S) → O :=
  fun t s => if s.2 = f t then a t s.1 else 0

section CopyCalculation

variable {L : ℕ} {X' Y' Z' : Type*}
variable [Fintype X] [Fintype Y] [Fintype Z]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq Z]

/-- Summing the full source copies, rather than target coordinate labels, is
what produces the Fourier average. All three source copy indices must agree. -/
theorem restrict_copies (T : Tensor O X Y Z)
    (fx : X' → X) (fy : Y' → Y) (fz : Z' → Z)
    (a : X' → Fin L → O) (b : Y' → Fin L → O) (c : Z' → Fin L → O) :
    Tensor.restrict (copyLocal fx a) (copyLocal fy b) (copyLocal fz c)
      (Tensor.directSum (fun _ : Fin L => T)) =
      fun x y z => (∑ r, a x r * b y r * c z r) * T (fx x) (fy y) (fz z) := by
  funext x y z
  simp [Tensor.restrict, Tensor.directSum, copyLocal, Fintype.sum_prod_type,
    ite_and, ite_mul, mul_ite, ← Finset.sum_mul]

omit [DecidableEq X] [DecidableEq Y] [DecidableEq Z] in
/-- Scaling each target coordinate is itself a local linear operation. -/
theorem restrict_scaled (T : Tensor O X Y Z)
    (a : X' → X → O) (b : Y' → Y → O) (c : Z' → Z → O)
    (u : X' → O) (v : Y' → O) (w : Z' → O) :
    Tensor.restrict (fun x i => u x * a x i)
      (fun y j => v y * b y j) (fun z k => w z * c z k) T =
      fun x y z => u x * v y * w z * Tensor.restrict a b c T x y z := by
  funext x y z
  simp only [Tensor.restrict, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  ring

end CopyCalculation

section Projection

variable {M : ℕ}
variable [Fintype X] [Fintype Y] [Fintype Z]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq Z]

/-- The quantity computed by `copyLocal (fun x => x.2.1) (fun x r => ζ ^ ((r : ℤ) * (2 * (x.1 :
ℤ))))`. -/
def fourierX (ζ : O) :
    (Fin M × (X × Unit)) → (Fin (6 * M) × X) → O :=
  copyLocal (fun x => x.2.1)
    (fun x r => ζ ^ ((r : ℤ) * (2 * (x.1 : ℤ))))

/-- The quantity computed by `copyLocal (fun y => (y.1, y.2.1)) (fun y r => ζ ^ ((r : ℤ) *
((y.2.2 : ℤ) - (y.1 : ℤ))))`. -/
def fourierY (ζ : O) :
    (Fin M × (Y × Fin M)) → (Fin (6 * M) × (Fin M × Y)) → O :=
  copyLocal (fun y => (y.1, y.2.1))
    (fun y r => ζ ^ ((r : ℤ) * ((y.2.2 : ℤ) - (y.1 : ℤ))))

/-- The quantity computed by `copyLocal (fun z => (z.1, z.2.1)) (fun z r => w r * ζ ^ ((r : ℤ) *
(-(z.2.2 : ℤ) - (z.1 : ℤ))))`. -/
def fourierZ (ζ : O) (w : Fin (6 * M) → O) :
    (Fin M × (Z × Fin M)) → (Fin (6 * M) × (Fin M × Z)) → O :=
  copyLocal (fun z => (z.1, z.2.1))
    (fun z r => w r *
      ζ ^ ((r : ℤ) * (-(z.2.2 : ℤ) - (z.1 : ℤ))))

/-- The actual independent local maps give exactly the projected tensor. -/
theorem fourier_restrict (A : Fin M → Tensor O X Y Z)
    (ζ : O) (w : Fin (6 * M) → O) (hζ : IsUnit ζ)
    (haverage : ∀ e : ℤ, -(3 * (M : ℤ)) < e → e < 3 * (M : ℤ) →
      (∑ r : Fin (6 * M), w r * ζ ^ ((r : ℤ) * e)) = if e = 0 then 1 else 0) :
    Tensor.restrict (fourierX ζ) (fourierY ζ) (fourierZ ζ w)
      (Tensor.directSum (fun _ : Fin (6 * M) => shared A)) = projected A := by
  classical
  rw [fourierX, fourierY, fourierZ, restrict_copies]
  funext x y z
  by_cases hyz : y.1 = z.1
  · have hphase : (∑ r : Fin (6 * M),
        ζ ^ ((r : ℤ) * (2 * (x.1 : ℤ))) *
          ζ ^ ((r : ℤ) * ((y.2.2 : ℤ) - (y.1 : ℤ))) *
          (w r *
            ζ ^ ((r : ℤ) * (-(z.2.2 : ℤ) - (z.1 : ℤ))))) =
        if phase y.1 x.1 y.2.2 z.2.2 = 0 then 1 else 0 := by
      calc
        _ = ∑ r : Fin (6 * M), w r * ζ ^ ((r : ℤ) * phase y.1 x.1 y.2.2 z.2.2) := by
          apply Finset.sum_congr rfl
          intro r hr
          rw [← hyz]
          calc
            _ = w r *
                ((ζ ^ ((r : ℤ) * (2 * (x.1 : ℤ))) *
                  ζ ^ ((r : ℤ) * ((y.2.2 : ℤ) - (y.1 : ℤ)))) *
                  ζ ^ ((r : ℤ) * (-(z.2.2 : ℤ) - (y.1 : ℤ)))) := by ring
            _ = _ := by
              rw [← upow_add hζ, ← upow_add hζ]
              congr 2
              dsimp [phase]
              ring
        _ = _ := by
          apply haverage <;> unfold phase <;> omega
    rw [hphase]
    simp [shared, Tensor.sharedFirst, projected, hyz, ite_mul]
  · simp [shared, Tensor.sharedFirst, projected, hyz]

end Projection

section Polynomial

variable {M : ℕ}

/-- On the complete projected support, the local weights add to the actual
polynomial degree, including all zero and mismatched coefficients. -/
theorem separationPolynomial_eval (A : Fin M → Tensor O X Y Z)
    (t : O) (ht : IsUnit t) :
    (fun x y z => (separationPolynomial A x y z).eval t) =
      fun x y z => t ^ weightX x * t ^ weightY y * t ^ weightZ z * projected A x y z :=
  TensorSpectrum.Separation.separationPolynomial_eval A t (fun e => t ^ e)
    (fun a b => upow_add ht a b) (fun n => upow_nat t n)

end Polynomial

section Realization

variable {M : ℕ}
variable [Fintype X] [Fintype Y] [Fintype Z]

/-- Every nonzero specialization comes from exactly the charged number of
source copies by three actual local linear maps. -/
theorem separationPolynomial_specializes
    (A : Fin M → Tensor O X Y Z) (t : O) (ht : IsUnit t) :
    (fun x y z => (separationPolynomial A x y z).eval t) ∈
      LocalTensor.orbit (Tensor.directSum (fun _ : Fin (6 * M) => shared A)) := by
  classical
  obtain ⟨ζ, w, hζ, haverage⟩ := phases (M := M)
  refine ⟨(fun x i => t ^ weightX x * fourierX ζ x i),
    (fun y j => t ^ weightY y * fourierY ζ y j),
    (fun z k => t ^ weightZ z * fourierZ ζ w z k), ?_⟩
  rw [restrict_scaled, fourier_restrict A ζ w hζ haverage]
  exact separationPolynomial_eval A t ht

/-- The complete finite construction, without a rank or character premise.
The nonzero-evaluation witnesses are restrictions of the full source direct
sum; the constant tensor is itself a full direct sum of products. -/
theorem finite_charged_separation
    (A : Fin M → Tensor O X Y Z) :
    ∃ P : Tensor (Polynomial O) (Fin M × (X × Unit))
        (Fin M × (Y × Fin M)) (Fin M × (Z × Fin M)),
      (∀ x y z, (P x y z).coeff 0 = separated A x y z) ∧
      (∀ x y z, (P x y z).degree ≤ ((M - 1) ^ 2 : ℕ)) ∧
      (∀ t : O, IsUnit t → (fun x y z => (P x y z).eval t) ∈
        LocalTensor.orbit (Tensor.directSum (fun _ : Fin (6 * M) => shared A))) := by
  refine ⟨separationPolynomial A, ?_, separationPolynomial_degree A,
    separationPolynomial_specializes A⟩
  intro x y z
  exact congrFun (congrFun (congrFun (separationPolynomial_constant A) x) y) z

end Realization

end MatrixMultiplicationAllFields.MatrixExponent.Integral.Upper.Separation
