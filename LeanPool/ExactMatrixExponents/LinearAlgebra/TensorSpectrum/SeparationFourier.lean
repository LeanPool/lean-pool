/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
/- Modified by Lean Pool contributors for this port. -/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.TensorSpectrum.SeparationPolynomial
public import LeanPool.ExactMatrixExponents.LinearAlgebra.TensorSpectrum.Blocks
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.LocalTensor

/-!
# Local Fourier restriction of a shared tensor

The averaging identity and the integer power law determine the projected
coefficients. The number of complete source copies is an input.
-/

@[expose] public section

noncomputable section

open scoped BigOperators
open MatrixMultiplicationAllFields.MatrixExponent
open MatrixMultiplicationAllFields.MatrixMultiplication.Foundation

namespace MatrixMultiplicationAllFields.TensorSpectrum.Separation

variable {R X Y Z : Type*} [CommSemiring R]

/-- Copy a specified source coordinate with a scalar depending only on the
target coordinate and the source's direct-sum copy number. -/
def copyLocal {L : ℕ} {S T : Type*} [DecidableEq S]
    (f : T → S) (a : T → Fin L → R) : T → (Fin L × S) → R :=
  fun t s => if s.2 = f t then a t s.1 else 0

section CopyCalculation

variable {L : ℕ} {X' Y' Z' : Type*}
variable [Fintype X] [Fintype Y] [Fintype Z]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq Z]

/-- Summing the full source copies, rather than target coordinate labels, is
what produces the Fourier average. All three source copy indices must agree. -/
theorem restrict_copies (T : Tensor R X Y Z)
    (fx : X' → X) (fy : Y' → Y) (fz : Z' → Z)
    (a : X' → Fin L → R) (b : Y' → Fin L → R) (c : Z' → Fin L → R) :
    Tensor.restrict (copyLocal fx a) (copyLocal fy b) (copyLocal fz c)
      (Tensor.directSum (fun _ : Fin L => T)) =
      fun x y z => (∑ r, a x r * b y r * c z r) * T (fx x) (fy y) (fz z) := by
  funext x y z
  simp [Tensor.restrict, Tensor.directSum, copyLocal, Fintype.sum_prod_type,
    ite_and, ite_mul, mul_ite, ← Finset.sum_mul]

omit [DecidableEq X] [DecidableEq Y] [DecidableEq Z] in
/-- Scaling each target coordinate is itself a local linear operation. -/
theorem restrict_scaled (T : Tensor R X Y Z)
    (a : X' → X → R) (b : Y' → Y → R) (c : Z' → Z → R)
    (u : X' → R) (v : Y' → R) (w : Z' → R) :
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

variable {M L : ℕ}
variable [Fintype X] [Fintype Y] [Fintype Z]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq Z]

/-- The Fourier substitution on the first leg. -/
def fourierX (power : ℤ → R) :
    (Fin M × (X × Unit)) → (Fin L × X) → R :=
  copyLocal (fun x => x.2.1)
    (fun x r => power ((r : ℤ) * (2 * (x.1 : ℤ))))

/-- The Fourier substitution on the second leg. -/
def fourierY (power : ℤ → R) :
    (Fin M × (Y × Fin M)) → (Fin L × (Fin M × Y)) → R :=
  copyLocal (fun y => (y.1, y.2.1))
    (fun y r => power ((r : ℤ) * ((y.2.2 : ℤ) - (y.1 : ℤ))))

/-- The Fourier substitution on the third leg. -/
def fourierZ (power : ℤ → R) (w : Fin L → R) :
    (Fin M × (Z × Fin M)) → (Fin L × (Fin M × Z)) → R :=
  copyLocal (fun z => (z.1, z.2.1))
    (fun z r => w r *
      power ((r : ℤ) * (-(z.2.2 : ℤ) - (z.1 : ℤ))))

/-- The actual independent local maps give exactly the projected tensor. -/
theorem fourier_restrict (A : Fin M → Tensor R X Y Z)
    (power : ℤ → R) (w : Fin L → R) (hadd : ∀ a b, power (a + b) = power a * power b)
    (haverage : ∀ e : ℤ, -(3 * (M : ℤ)) < e → e < 3 * (M : ℤ) →
      (∑ r : Fin L, w r * power ((r : ℤ) * e)) = if e = 0 then 1 else 0) :
    Tensor.restrict (fourierX power) (fourierY power) (fourierZ power w)
      (Tensor.directSum (fun _ : Fin L => Tensor.sharedFirst A)) = projected A := by
  classical
  rw [fourierX, fourierY, fourierZ, restrict_copies]
  funext x y z
  by_cases hyz : y.1 = z.1
  · have hphase : (∑ r : Fin L,
        power ((r : ℤ) * (2 * (x.1 : ℤ))) *
          power ((r : ℤ) * ((y.2.2 : ℤ) - (y.1 : ℤ))) *
          (w r *
            power ((r : ℤ) * (-(z.2.2 : ℤ) - (z.1 : ℤ))))) =
        if phase y.1 x.1 y.2.2 z.2.2 = 0 then 1 else 0 := by
      calc
        _ = ∑ r : Fin L, w r * power ((r : ℤ) * phase y.1 x.1 y.2.2 z.2.2) := by
          apply Finset.sum_congr rfl
          intro r hr
          rw [← hyz]
          calc
            _ = w r *
                ((power ((r : ℤ) * (2 * (x.1 : ℤ))) *
                  power ((r : ℤ) * ((y.2.2 : ℤ) - (y.1 : ℤ)))) *
                  power ((r : ℤ) * (-(z.2.2 : ℤ) - (y.1 : ℤ)))) := by ring
            _ = _ := by
              rw [← hadd, ← hadd]
              congr 2
              dsimp [phase]
              ring
        _ = _ := by
          apply haverage <;> unfold phase <;> omega
    rw [hphase]
    simp [Tensor.sharedFirst, projected, hyz, ite_mul]
  · simp [Tensor.sharedFirst, projected, hyz]

/-- Realize a polynomial evaluation as a restriction using the Fourier maps
scaled by the signed coordinate weights. -/
theorem separationPolynomial_specializes (A : Fin M → Tensor R X Y Z)
    (power : ℤ → R) (w : Fin L → R) (t : R) (integerPower : ℤ → R)
    (projection : Tensor.restrict (fourierX power) (fourierY power) (fourierZ power w)
      (Tensor.directSum (fun _ : Fin L => Tensor.sharedFirst A)) = projected A)
    (evaluation : (fun x y z => (separationPolynomial A x y z).eval t) =
      fun x y z => integerPower (weightX x) * integerPower (weightY y) *
        integerPower (weightZ z) * projected A x y z) :
    (fun x y z => (separationPolynomial A x y z).eval t) ∈
      LocalTensor.orbit (Tensor.directSum (fun _ : Fin L => Tensor.sharedFirst A)) := by
  refine ⟨(fun x i => integerPower (weightX x) * fourierX power x i),
    (fun y j => integerPower (weightY y) * fourierY power y j),
    (fun z k => integerPower (weightZ z) * fourierZ power w z k), ?_⟩
  rw [restrict_scaled, projection]
  exact evaluation

end Projection

/-- Package the polynomial and its specialization certificates for a specified
number of shared source copies and a specified set of evaluation points. -/
theorem finite_charged_separation {M L : ℕ} [Fintype X] [Fintype Y] [Fintype Z]
    (A : Fin M → Tensor R X Y Z) (valid : R → Prop)
    (specializes : ∀ t, valid t → (fun x y z => (separationPolynomial A x y z).eval t) ∈
      LocalTensor.orbit (Tensor.directSum (fun _ : Fin L => Tensor.sharedFirst A))) :
    ∃ P : Tensor (Polynomial R) (Fin M × (X × Unit))
        (Fin M × (Y × Fin M)) (Fin M × (Z × Fin M)),
      (∀ x y z, (P x y z).coeff 0 = separated A x y z) ∧
      (∀ x y z, (P x y z).degree ≤ ((M - 1) ^ 2 : ℕ)) ∧
      (∀ t, valid t → (fun x y z => (P x y z).eval t) ∈
        LocalTensor.orbit (Tensor.directSum (fun _ : Fin L => Tensor.sharedFirst A))) := by
  refine ⟨separationPolynomial A, ?_, separationPolynomial_degree A, specializes⟩
  intro x y z
  exact congrFun (congrFun (congrFun (separationPolynomial_constant A) x) y) z

end MatrixMultiplicationAllFields.TensorSpectrum.Separation
