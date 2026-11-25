/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
/- Modified by Lean Pool contributors for this port. -/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Coefficients
public import LeanPool.ExactMatrixExponents.LinearAlgebra.TensorSpectrum.SeparationWeights
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Fourier
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Polynomial.ComplexPolynomialApproximation
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Tensor.ComplexTensorRestrictionComposition
public import LeanPool.ExactMatrixExponents.LinearAlgebra.TensorSpectrum.Blocks
public import LeanPool.ExactMatrixExponents.LinearAlgebra.TensorSpectrum.SeparationPolynomial
public import LeanPool.ExactMatrixExponents.LinearAlgebra.TensorSpectrum.SeparationFourier

/-!
# Charged finite separation by local Fourier maps

The source is exactly `5 * M` full copies of the shared-first-leg tensor.
The target is the full direct sum of the sector tensors, each multiplied by
a length-`M` pairing on the second and third legs.  Local variables may have
negative weights; after Fourier projection every surviving total weight is
a nonnegative square, so the resulting coefficient array is polynomial.
-/

@[expose] public section

open MatrixMultiplicationAllFields.MatrixExponent
    MatrixMultiplicationAllFields.TensorSpectrum

noncomputable section

open MatrixMultiplicationAllFields.TensorSpectrum.Separation

open scoped BigOperators
open MatrixMultiplicationAllFields.MatrixMultiplication.Foundation

namespace MatrixMultiplicationAllFields.MatrixExponent.Upper.Separation

variable {X Y Z : Type*}

/-- The branch labels occur only on the last two legs of the input. -/
abbrev shared {M : ℕ} (A : Fin M → Tensor Coeff X Y Z) :
    Tensor Coeff X (Fin M × Y) (Fin M × Z) :=
  Tensor.sharedFirst A

export MatrixMultiplicationAllFields.TensorSpectrum.Separation
  (dotPairingX separated phase projected squareDegree separationPolynomial
    squareDegree_eq_zero_iff separationPolynomial_constant separationPolynomial_degree weightX
    weightY weightZ)

export MatrixMultiplicationAllFields.TensorSpectrum.Separation
  (copyLocal restrict_copies restrict_scaled)

section Projection

variable {M : ℕ}
variable [Fintype X] [Fintype Y] [Fintype Z]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq Z]

/-- The quantity computed by `copyLocal (fun x => x.2.1) (fun x r => ζ ^ ((r : ℤ) * (2 * (x.1 :
ℤ))))`. -/
abbrev fourierX (ζ : Coeff) :
    (Fin M × (X × Unit)) → (Fin (5 * M) × X) → Coeff :=
  TensorSpectrum.Separation.fourierX (M := M) (L := 5 * M) (fun e => ζ ^ e)

/-- The quantity computed by `copyLocal (fun y => (y.1, y.2.1)) (fun y r => ζ ^ ((r : ℤ) *
((y.2.2 : ℤ) - (y.1 : ℤ))))`. -/
abbrev fourierY (ζ : Coeff) :
    (Fin M × (Y × Fin M)) → (Fin (5 * M) × (Fin M × Y)) → Coeff :=
  TensorSpectrum.Separation.fourierY (M := M) (L := 5 * M) (fun e => ζ ^ e)

/-- The quantity computed by `copyLocal (fun z => (z.1, z.2.1)) (fun z r => w r * ζ ^ ((r : ℤ) *
(-(z.2.2 : ℤ) - (z.1 : ℤ))))`. -/
abbrev fourierZ (ζ : Coeff) (w : Fin (5 * M) → Coeff) :
    (Fin M × (Z × Fin M)) → (Fin (5 * M) × (Fin M × Z)) → Coeff :=
  TensorSpectrum.Separation.fourierZ (M := M) (L := 5 * M) (fun e => ζ ^ e) w

/-- The actual independent local maps give exactly the projected tensor. -/
theorem fourier_restrict (A : Fin M → Tensor Coeff X Y Z)
    (ζ : Coeff) (w : Fin (5 * M) → Coeff) (hζ : ζ ≠ 0)
    (haverage : ∀ e : ℤ, -(3 * (M : ℤ)) < e → e < 3 * (M : ℤ) →
      (∑ r : Fin (5 * M), w r * ζ ^ ((r : ℤ) * e)) = if e = 0 then 1 else 0) :
    Tensor.restrict (fourierX ζ) (fourierY ζ) (fourierZ ζ w)
      (Tensor.directSum (fun _ : Fin (5 * M) => shared A)) = projected A :=
  TensorSpectrum.Separation.fourier_restrict A (fun e => ζ ^ e) w
    (fun a b => zpow_add₀ hζ a b) haverage

end Projection

section Polynomial

variable {M : ℕ}

/-- On the complete projected support, the local weights add to the actual
polynomial degree, including all zero and mismatched coefficients. -/
theorem separationPolynomial_eval (A : Fin M → Tensor Coeff X Y Z)
    (t : Coeff) (ht : t ≠ 0) :
    (fun x y z => (separationPolynomial A x y z).eval t) =
      fun x y z => t ^ weightX x * t ^ weightY y * t ^ weightZ z * projected A x y z :=
  TensorSpectrum.Separation.separationPolynomial_eval A t (fun e => t ^ e)
    (fun a b => zpow_add₀ ht a b) (fun n => zpow_natCast t n)

end Polynomial

section Realization

variable {M : ℕ}
variable [Fintype X] [Fintype Y] [Fintype Z]

/-- Every nonzero specialization comes from exactly the charged number of
source copies by three actual local linear maps. -/
theorem separationPolynomial_specializes (hM : 0 < M)
    (A : Fin M → Tensor Coeff X Y Z) (t : Coeff) (ht : t ≠ 0) :
    (fun x y z => (separationPolynomial A x y z).eval t) ∈
      LocalTensor.orbit (Tensor.directSum (fun _ : Fin (5 * M) => shared A)) := by
  classical
  obtain ⟨ζ, w, hζ, haverage⟩ := Fourier.exists_weights hM
  refine ⟨(fun x i => t ^ weightX x * fourierX ζ x i),
    (fun y j => t ^ weightY y * fourierY ζ y j),
    (fun z k => t ^ weightZ z * fourierZ ζ w z k), ?_⟩
  rw [restrict_scaled, fourier_restrict A ζ w hζ haverage]
  exact separationPolynomial_eval A t ht

/-- The complete finite construction, without a rank or character premise.
The nonzero-evaluation witnesses are restrictions of the full source direct
sum; the constant tensor is itself a full direct sum of products. -/
theorem finite_charged_separation (hM : 0 < M)
    (A : Fin M → Tensor Coeff X Y Z) :
    ∃ P : Tensor (Polynomial Coeff) (Fin M × (X × Unit))
        (Fin M × (Y × Fin M)) (Fin M × (Z × Fin M)),
      (∀ x y z, (P x y z).coeff 0 = separated A x y z) ∧
      (∀ x y z, (P x y z).degree ≤ ((M - 1) ^ 2 : ℕ)) ∧
      (∀ t : Coeff, t ≠ 0 → (fun x y z => (P x y z).eval t) ∈
        LocalTensor.orbit (Tensor.directSum (fun _ : Fin (5 * M) => shared A))) := by
  refine ⟨separationPolynomial A, ?_, separationPolynomial_degree A,
    separationPolynomial_specializes hM A⟩
  intro x y z
  exact congrFun (congrFun (congrFun (separationPolynomial_constant A) x) y) z

end Realization

end MatrixMultiplicationAllFields.MatrixExponent.Upper.Separation
