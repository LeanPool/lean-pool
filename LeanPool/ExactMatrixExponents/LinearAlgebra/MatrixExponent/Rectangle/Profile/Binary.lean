/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
/- Modified by Lean Pool contributors for this port. -/
module

public import Mathlib.Data.Fintype.EquivFin
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Rectangle.Profile.Pairing
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Upper.Tensor.Semiring
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Rectangle.Poly

/-!
# The binary profile bound over the coefficient field

Interpret a three-leg tensor class on three labelled sites to apply the
binary spectral estimate to rectangular matrix multiplication.
-/

@[expose] public section

/- # Interpreting the three-leg tensor semiring on labelled sites -/

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Rectangle.Profile
open Upper Spectral

local notation "CT" => MatrixMultiplicationAllFields.MatrixMultiplication.Foundation.Tensor
variable {X Y Z U V W : Type} [Fintype X] [Fintype Y] [Fintype Z] [Fintype U] [Fintype V]
    [Fintype W]

theorem restricts {A : CT Coeff X Y Z} {B : CT Coeff U V W}
    (h : CoefficientTensor.Restricts A B) : (triple A).Restricts (triple B) := by
  obtain ⟨a, b, c, rfl⟩ := h
  exact restricts_triple _ _ a b c fun _ _ _ => rfl

/-- Extends the representative-level operation to quotient classes. -/
def interp : TensorClass → Tensor Coeff Site :=
  Quotient.lift (fun A : TensorRep => Tensor.ofRaw (triple A.coeff))
    (fun _ _ h => Tensor.ofRaw_eq ⟨restricts h.1, restricts h.2⟩)

theorem interp_tensor (T : CT Coeff X Y Z) :
    interp (TensorClass.ofTensor T) = Tensor.ofRaw (triple T) :=
  Tensor.ofRaw_eq ⟨restricts (TensorRep.ofTensor_restricts T),
    restricts (TensorRep.restricts_ofTensor T)⟩

theorem read_mul (A B : Raw Coeff Site) :
    read (A * B) = MatrixMultiplicationAllFields.MatrixMultiplication.Foundation.Tensor.product
      (read A) (read B) := by
  funext x y z
  rw [read, Raw.coeff_mul]
  unfold MatrixMultiplicationAllFields.MatrixMultiplication.Foundation.Tensor.product read
  congr 2 <;> funext s <;> rcases s with _ | (_ | _) <;> rfl

theorem read_add (A B : Raw Coeff Site) :
    read (A + B) = CoefficientTensor.blockSum (read A) (read B) := by
  funext x y z
  rw [read_apply]
  change (∑ i : A.term ⊕ B.term, (A + B).factor i (some false) x *
    (A + B).factor i (some true) y * (A + B).factor i none z) = _
  have h₁ (l : A.term) s (u : A.leg s ⊕ B.leg s) :
      (A + B).factor (.inl l) s u = Sum.elim (A.factor l s) (fun _ => 0) u := rfl
  have h₂ (l : B.term) s (u : A.leg s ⊕ B.leg s) :
      (A + B).factor (.inr l) s u = Sum.elim (fun _ => 0) (B.factor l s) u := rfl
  rw [Fintype.sum_sum_type]
  change A.leg (some false) ⊕ B.leg (some false) at x
  change A.leg (some true) ⊕ B.leg (some true) at y
  change A.leg none ⊕ B.leg none at z
  rcases x with x | x <;> rcases y with y | y <;> rcases z with z | z <;>
    simp [h₁, h₂, CoefficientTensor.blockSum, read_apply]

/-- Builds `TensorClass →+* Tensor Coeff Site where toFun` with the specified `toFun`,
`map_zero'`, `change`, `rw`. -/
def interpret : TensorClass →+* Tensor Coeff Site where
  toFun := interp
  map_zero' := by
    change interp (TensorClass.ofTensor TensorClass.emptyTensor) = 0
    rw [interp_tensor, Tensor.ofRaw_eq_zero]
    exact fun x => Empty.elim (x none)
  map_one' := by
    change interp (TensorClass.ofTensor TensorClass.unitTensor) = Tensor.ofRaw 1
    rw [interp_tensor, ← triple_read (1 : Raw Coeff Site)]
    have he : read (1 : Raw Coeff Site) = TensorClass.unitTensor := by
      funext x y z
      change (∑ _ : Unit, ∏ _ : Site, (1 : Coeff)) = 1
      simp
    rw [he]
  map_mul' X Y := by
    refine Quotient.inductionOn₂ X Y fun A B => ?_
    change interp (TensorClass.ofTensor
      (MatrixMultiplicationAllFields.MatrixMultiplication.Foundation.Tensor.product
        A.coeff B.coeff)) =
        Tensor.ofRaw (triple A.coeff * triple B.coeff)
    rw [interp_tensor, ← triple_read (triple A.coeff * triple B.coeff), read_mul,
      read_triple, read_triple]
    rfl
  map_add' X Y := by
    refine Quotient.inductionOn₂ X Y fun A B => ?_
    change interp (TensorClass.ofTensor (CoefficientTensor.blockSum A.coeff B.coeff)) =
      Tensor.ofRaw (triple A.coeff + triple B.coeff)
    rw [interp_tensor, ← triple_read (triple A.coeff + triple B.coeff), read_add,
      read_triple, read_triple]
    rfl

theorem interpret_tensor (T : CT Coeff X Y Z) :
    interpret (TensorClass.ofTensor T) = Tensor.ofRaw (triple T) := interp_tensor T

theorem interpret_mono : Monotone interpret :=
  fun X Y => Quotient.inductionOn₂ X Y fun _ _ h => restricts h

end MatrixMultiplicationAllFields.MatrixExponent.Rectangle.Profile
end

/- # Determinant and tripling for spectral points on labelled sites -/

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Rectangle.Profile
open Upper Upper.TensorClass Spectral

private theorem interpret_dot :
    interpret (dotX 2) = Tensor.wire Coeff (some true) none 2 := by
  let W := Raw.wire Coeff (some true) none 2
  let T (x y z : Fin 2) : Coeff := if x = 0 ∧ y = z then 1 else 0
  have he : read W = T := by
    funext x y z
    change Fin 2 at x y z
    refine (read_apply W x y z).trans ?_
    change (∑ i : Fin 2, (if x = 0 then (1 : Coeff) else 0) *
      (if y = i then 1 else 0) * (if z = i then 1 else 0)) = T x y z
    by_cases he : x = 0 <;> simp [T, he, mul_ite]
  rw [dotX, TensorSpectrum.TensorClass.dotX, interpret_tensor]
  change _ = Tensor.ofRaw W
  rw [← triple_read W, he]
  change Tensor.ofRaw (triple (CoefficientTensor.dotXCoeff 2)) = Tensor.ofRaw (triple T)
  let δ (x y : Fin 2) : Coeff := if x = y then 1 else 0
  apply Tensor.ofRaw_eq
  constructor
  · refine restricts_triple _ _ (fun x _ => δ x 0) δ δ fun x y z => ?_
    fin_cases x <;> fin_cases y <;> fin_cases z <;>
      simp [δ, T, TensorSpectrum.CoefficientTensor.dotXCoeff]
  · refine restricts_triple _ _ (fun _ x => δ x 0) δ δ fun x y z => ?_
    fin_cases y <;> fin_cases z <;>
      simp [δ, T, TensorSpectrum.CoefficientTensor.dotXCoeff, Fin.sum_univ_two]

theorem coeff_binary : BinaryLaw Coeff := by
  intro f hf p hp he m
  let g : Character := ⟨f.comp interpret, hf.comp interpret_mono⟩
  have hg : g.pX = p := by
    apply (Real.rpow_right_inj (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)).mp
    have hd := TensorSpectrum.TensorClass.Character.dotXValue_eq_rpow g 2 (by decide)
    change (f (interpret (dotX 2)) : ℝ) = (2 : ℝ) ^ g.pX at hd
    rw [interpret_dot, he] at hd
    exact hd.symm
  have h := poly_row g (hg.symm ▸ hp) m
  rw [hg] at h
  change Row (fun n => (f (interpret (ofTensor (polynomialTensor (m + 1) (n + 1)))) : ℝ) ^ (1 / p))
    (fun n => (f (interpret (swapYZ (ofTensor (polynomialTensor (m + 1) (n
      + 1))))) : ℝ) ^ (1 / p)) m at h
  simp only [swapYZ_ofTensor, interpret_tensor] at h
  exact h

end MatrixMultiplicationAllFields.MatrixExponent.Rectangle.Profile
end
