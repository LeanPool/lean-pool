/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.DiagonalWeakNormEnergy
public import LeanPool.HighContrastHomogenization.Geometry.CoarseSchurBridge
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.GradientUniqueness
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.MatrixPositivity

/-!
# High-contrast homogenization: Provider.Response.DiagonalWeakNormState

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Optimizer states for the diagonal weak estimate

The diagonal weak estimate is stated for the canonical response optimizer of a
coefficient sample on an adapted parent cell.  This file turns that description
into a source-facing object: a sample is restricted to the parent domain, the
public canonical maximizer is selected, and its gradient and flux form the
doubled state.  Its energy is the square root of the normalized variational
energy.

The adjoint sample is also constructed on the a.e.-quotient coefficient space.
Its domain-local coefficient is a.e. equal to the transpose of the original
domain-local coefficient, so the Chapter 2 transpose congruence applies without
choosing an additional representative.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory

variable {d : ℕ}

/-! ## The adjoint coefficient sample -/

namespace CoeffSpace

noncomputable section

/-- The adjoint sample `aᵗ`, obtained by transposing the coefficient matrix
at almost every point. -/
@[expose]
def transpose (a : CoeffSpace d) : CoeffSpace d where
  val := AEEqFun.comp matTranspose continuous_id.matrix_transpose a.1
  property := by
    intro R hR
    obtain ⟨lam, Lam, hlam, hle, hEll⟩ := a.2 R hR
    refine ⟨lam, Lam, hlam, hle, ?_⟩
    filter_upwards [hEll,
      AEEqFun.coeFn_comp matTranspose continuous_id.matrix_transpose a.1] with x hx htranspose hxb
    rw [htranspose]
    exact isEllipticMatrix_transpose (hx hxb)

/-- The adjoint sample is represented almost everywhere by the pointwise
transpose of the original sample. -/
theorem transpose_ae (a : CoeffSpace d) :
    (⇑(a.transpose.1) : CoeffField d) =ᵐ[volume]
      fun x => matTranspose ((⇑a.1 : CoeffField d) x) :=
  AEEqFun.coeFn_comp matTranspose continuous_id.matrix_transpose a.1

/-- Taking the adjoint twice returns the original coefficient sample. -/
@[simp] theorem transpose_transpose (a : CoeffSpace d) : a.transpose.transpose = a := by
  apply Subtype.ext
  apply AEEqFun.ext
  filter_upwards [transpose_ae a.transpose, transpose_ae a] with x hx hxa
  rw [hx, hxa]
  simp only [matTranspose, Matrix.transpose_transpose]

/-- On a Chapter 2 domain, restricting the adjoint sample agrees almost
everywhere with transposing the restricted original sample. -/
theorem coeffOn_transpose_aeeq (a : CoeffSpace d) (U : Book.Ch02.Domain d) :
    Book.Ch02.CoeffOn.AEEq (a.transpose.coeffOn U) (a.coeffOn U).transpose := by
  exact ae_restrict_of_ae (transpose_ae a)

/-- A sample admits one representative shared by every domain, elliptic at every
point of each of them with that domain's own constants, together with the a.e.
equality needed to transport its canonical optimizer. -/
theorem exists_pointwise_coeffOn_family_aeeq (a : CoeffSpace d) :
    ∃ f : CoeffField d,
      (⇑a.1 : CoeffField d) =ᵐ[volume] f ∧
        ∀ U : Book.Ch02.Domain d, ∃ (b : Book.Ch02.CoeffOn U) (lam Lam : ℝ),
          b.toCoeffField = f ∧ b.lam = lam ∧ b.Lam = Lam ∧
            IsEllipticFieldOn lam Lam (U : Set (Vec d)) f ∧
              Book.Ch02.CoeffOn.AEEq (a.coeffOn U) b := by
  obtain ⟨f, hfm, hae, hloc⟩ :=
    exists_locally_pointwise_elliptic_representative a.2
  refine ⟨f, hae, fun U => ?_⟩
  obtain ⟨R, hR, hUR⟩ :=
    exists_ball_of_isBounded U.isDomain.isBoundedDomain.isBounded
  obtain ⟨lam, Lam, hlam, hle, hell⟩ := hloc R hR
  obtain ⟨b, hbf, hblam, hbLam, hbEll⟩ :=
    Response.exists_coeffOn_of_measurable hlam hle hfm U
      (fun x hx => hell x (hUR hx))
  refine ⟨b, lam, Lam, hbf, hblam, hbLam, ?_, ?_⟩
  · exact hbEll
  · show (⇑a.1 : CoeffField d) =ᵐ[volumeMeasureOn (U : Set (Vec d))]
      b.toCoeffField
    rw [hbf]
    exact ae_restrict_of_ae hae

end

end CoeffSpace

namespace Response

open Book.Ch02

noncomputable section

variable {q : Mat d}

/-- Coarse response of an adjoint sample is the signed block congruence of the
original response. -/
theorem coarseBlock_transpose (a : CoeffSpace d) (U : Book.Ch02.Domain d) :
    coarseBlock (U : Set (Vec d)) a.transpose =
      blockMatMul (blockDiag 1 (-1))
        (blockMatMul (coarseBlock (U : Set (Vec d)) a) (blockDiag 1 (-1))) := by
  rw [coarseBlock_eq_coarseBlockMatrix a.transpose U,
    Book.Ch02.coarseBlockMatrix_eq_ofAEEq (CoeffSpace.coeffOn_transpose_aeeq a U),
    coarseBlockMatrix_transpose, ← coarseBlock_eq_coarseBlockMatrix a U]

/-- The adjoint congruence on one adapted response block. -/
theorem adaptedResponse_transpose (hq : q.PosDef) (k : ℤ) (w : Fin d → ℤ)
    (a : CoeffSpace d) :
    adaptedResponse q k w a.transpose =
      blockMatMul (blockDiag 1 (-1))
        (blockMatMul (adaptedResponse q k w a) (blockDiag 1 (-1))) := by
  simpa only [adaptedResponse, adaptedDomainAt_carrier] using
    coarseBlock_transpose a (adaptedDomainAt hq k w)

/-! ## The canonical parent optimizer and its state -/

/-- The canonical variational maximizer `v_t` on the adapted parent cell
`U_t = q◇_t`. -/
@[expose]
def diagonalWeakOptimizer (hq : q.PosDef) (t : ℤ) (a : CoeffSpace d)
    (p r : Vec d) : Solution (adaptedDomain hq t) (a.coeffOn (adaptedDomain hq t)) :=
  (canonicalMaximizer
    (responseExistenceTheory (adaptedDomain hq t) (a.coeffOn (adaptedDomain hq t))) p r).toSolution

/-- The chosen optimizer is a response maximizer at the printed load. -/
theorem diagonalWeakOptimizer_isMaximizer (hq : q.PosDef) (t : ℤ)
    (a : CoeffSpace d) (p r : Vec d) :
    Book.Ch02.IsResponseMaximizer (adaptedDomain hq t)
      (a.coeffOn (adaptedDomain hq t)) p r
      (diagonalWeakOptimizer hq t a p r) :=
  (canonicalMaximizer
    (responseExistenceTheory (adaptedDomain hq t) (a.coeffOn (adaptedDomain hq t))) p r).isMaximizer

/-- The doubled optimizer state `X_t = (∇v_t,a∇v_t)`. -/
@[expose]
def diagonalWeakState (hq : q.PosDef) (t : ℤ) (a : CoeffSpace d)
    (p r : Vec d) : Vec d → BlockVec d :=
  fun x =>
    ((diagonalWeakOptimizer hq t a p r).toH1.grad x,
      matVecMul ((a.coeffOn (adaptedDomain hq t)).toCoeffField x)
        ((diagonalWeakOptimizer hq t a p r).toH1.grad x))

/-- The defining equation of the doubled optimizer state. -/
theorem diagonalWeakState_eq (hq : q.PosDef) (t : ℤ) (a : CoeffSpace d)
    (p r : Vec d) (x : Vec d) :
    diagonalWeakState hq t a p r x =
      ((diagonalWeakOptimizer hq t a p r).toH1.grad x,
        matVecMul ((a.coeffOn (adaptedDomain hq t)).toCoeffField x)
          ((diagonalWeakOptimizer hq t a p r).toH1.grad x)) := rfl

/-- The normalized optimizer energy
`ℰ_t = ‖symm(a)¹⁄² ∇v_t‖_{L_underlined²(U_t)}`. -/
@[expose]
def diagonalWeakEnergy (hq : q.PosDef) (t : ℤ) (a : CoeffSpace d)
    (p r : Vec d) : ℝ :=
  Real.sqrt
    (variationEnergyValue (adaptedDomain hq t) (a.coeffOn (adaptedDomain hq t))
      (diagonalWeakOptimizer hq t a p r))

/-- The defining equation of the normalized optimizer energy. -/
theorem diagonalWeakEnergy_eq (hq : q.PosDef) (t : ℤ) (a : CoeffSpace d)
    (p r : Vec d) :
    diagonalWeakEnergy hq t a p r =
      Real.sqrt
        (variationEnergyValue (adaptedDomain hq t) (a.coeffOn (adaptedDomain hq t))
          (diagonalWeakOptimizer hq t a p r)) := rfl

/-- The normalized optimizer energy is nonnegative. -/
theorem diagonalWeakEnergy_nonneg (hq : q.PosDef) (t : ℤ) (a : CoeffSpace d)
    (p r : Vec d) : 0 ≤ diagonalWeakEnergy hq t a p r :=
  Real.sqrt_nonneg _

/-- The square of the normalized optimizer energy is the variational energy. -/
theorem sq_diagonalWeakEnergy (hq : q.PosDef) (t : ℤ) (a : CoeffSpace d)
    (p r : Vec d) :
    diagonalWeakEnergy hq t a p r ^ 2 =
      variationEnergyValue (adaptedDomain hq t) (a.coeffOn (adaptedDomain hq t))
        (diagonalWeakOptimizer hq t a p r) := by
  rw [diagonalWeakEnergy_eq, Real.sq_sqrt]
  have hJ := Book.Ch02.responseJ_nonneg (adaptedDomain hq t)
    (a.coeffOn (adaptedDomain hq t)) p r
  have henergy := responseJ_eq_energy (a.coeffOn (adaptedDomain hq t))
    (diagonalWeakOptimizer_isMaximizer hq t a p r)
  linarith only [hJ, henergy]

/-- The response value is one half of the squared optimizer energy. -/
theorem responseJ_eq_sq_diagonalWeakEnergy (hq : q.PosDef) (t : ℤ)
    (a : CoeffSpace d) (p r : Vec d) :
    responseJ (adaptedDomain hq t) (a.coeffOn (adaptedDomain hq t)) p r =
      (1 / 2 : ℝ) * diagonalWeakEnergy hq t a p r ^ 2 := by
  rw [sq_diagonalWeakEnergy]
  exact responseJ_eq_energy (a.coeffOn (adaptedDomain hq t))
    (diagonalWeakOptimizer_isMaximizer hq t a p r)

/-- The two slots of the optimizer state are square integrable on the parent
cell. -/
theorem diagonalWeakState_memVectorL2 (hq : q.PosDef) (t : ℤ)
    (a : CoeffSpace d) (p r : Vec d) :
    MemVectorL2 (adaptedCell q t) (fun x => (diagonalWeakState hq t a p r x).1) ∧
      MemVectorL2 (adaptedCell q t) (fun x => (diagonalWeakState hq t a p r x).2) := by
  let b := a.coeffOn (adaptedDomain hq t)
  let v := diagonalWeakOptimizer hq t a p r
  have hgrad : MemVectorL2 (adaptedCell q t) v.toH1.grad := v.toH1.grad_memVectorL2
  have hEll : IsAEEllipticFieldOn b.lam b.Lam (adaptedCell q t) b.toCoeffField :=
    ⟨(adaptedDomain hq t).measurableSet, b.aeStronglyMeasurable, b.aeElliptic⟩
  refine ⟨?_, ?_⟩
  · simpa only [diagonalWeakState, v] using hgrad
  · simpa only [diagonalWeakState, b, v] using hEll.memVectorL2_matVecMul hgrad

/-- The parent average of the optimizer state is the average-gradient/average-
flux pair used by the variational identities. -/
theorem blockCellAverage_diagonalWeakState (hq : q.PosDef) (t : ℤ)
    (a : CoeffSpace d) (p r : Vec d) :
    blockCellAverage (adaptedCell q t) (diagonalWeakState hq t a p r) =
      ((averageGradient (adaptedDomain hq t) (a.coeffOn (adaptedDomain hq t))
          (diagonalWeakOptimizer hq t a p r),
        averageFlux (adaptedDomain hq t) (a.coeffOn (adaptedDomain hq t))
          (diagonalWeakOptimizer hq t a p r)) : BlockVec d) :=
  blockCellAverage_gradFlux (adaptedDomain hq t) (a.coeffOn (adaptedDomain hq t))
    (diagonalWeakOptimizer hq t a p r)

/-- The source average formula
`(X_t)_{U_t} = (R A_t + I)(-p,r)`. -/
theorem blockCellAverage_diagonalWeakState_eq_response [NeZero d]
    (hq : q.PosDef) (t : ℤ) (a : CoeffSpace d) (p r : Vec d) :
    blockCellAverage (adaptedCell q t) (diagonalWeakState hq t a p r) =
      blockMatVecMul (blockR d)
          (blockMatVecMul (coarseBlock (adaptedCell q t) a)
            ((-p, r) : BlockVec d)) +
        ((-p, r) : BlockVec d) := by
  rw [blockCellAverage_diagonalWeakState]
  exact blockAverage_adaptedCell hq t
    (coarseBlock_eq_coarseBlockMatrix a (adaptedDomain hq t)).symm
    (diagonalWeakOptimizer_isMaximizer hq t a p r)

/-! ## The source adjoint state -/

/-- The adjoint doubled state `X_t⁺ = (∇v_t⁺,aᵗ∇v_t⁺)`. -/
@[expose]
def diagonalWeakAdjointState (hq : q.PosDef) (t : ℤ) (a : CoeffSpace d)
    (p r : Vec d) : Vec d → BlockVec d :=
  diagonalWeakState hq t a.transpose p r

/-- The adjoint optimizer energy. -/
@[expose]
def diagonalWeakAdjointEnergy (hq : q.PosDef) (t : ℤ) (a : CoeffSpace d)
    (p r : Vec d) : ℝ :=
  diagonalWeakEnergy hq t a.transpose p r

theorem diagonalWeakAdjointState_eq (hq : q.PosDef) (t : ℤ)
    (a : CoeffSpace d) (p r : Vec d) :
    diagonalWeakAdjointState hq t a p r =
      diagonalWeakState hq t a.transpose p r := rfl

theorem diagonalWeakAdjointEnergy_eq (hq : q.PosDef) (t : ℤ)
    (a : CoeffSpace d) (p r : Vec d) :
    diagonalWeakAdjointEnergy hq t a p r =
      diagonalWeakEnergy hq t a.transpose p r := rfl

end

end Response
end HighContrast
end HCPolySupport
