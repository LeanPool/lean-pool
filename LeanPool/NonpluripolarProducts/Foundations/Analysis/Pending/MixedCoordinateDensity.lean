/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.CoordinateWedgeFamilyPairing
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.SymmetricMultilinearDiagonal
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.MixedMongeAmpere
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.KahlerCurrentPerturbation

/-!
# The geometric meaning of the mixed Monge--Ampère density

The blueprint statement `fpmma:geometric-density`: for smooth real potentials the density of
`ddᶜu₁ ∧ ⋯ ∧ ddᶜuₙ` in the standard complex orientation is the mixed determinant density
`D_{u₁,…,uₙ}` of `FirstPass.MixedMongeAmpere`.

Both sides are symmetric `ℝ`-multilinear functions of the `n` two-forms:

* the wedge side by `Pending.CoordinateWedgeFamilyPairing` (the mixed Pfaffian formula);
* the determinant side because `normalizedHermitianMatrix` is `ℝ`-linear and
  `mixedCoefficient` is row-multilinear, its `i`-th slot occupying the single row `σ⁻¹ i`
  of each permutation summand.

They agree on the diagonal: that is exactly the pure identity
`Pending.CoordinateDensityHermitian.actualTopPowerDensity_eq_normalizedTopPowerDensity`,
which holds for an ARBITRARY real `(1,1)`-form.  The intermediate forms `∑ᵢ tᵢ ddᶜuᵢ` of
the polarization are sign-indefinite, so the semipositive-only identity could not have been
used here.  Polarization over the submodule of `(1,1)`-forms
(`Pending.SymmetricMultilinearDiagonal.eq_of_diagonal_eq`) closes the argument; the only
scalar inverted is `n!`, so dimension `0` is included, where both sides are the empty
product `1`.
-/

@[expose] public section

noncomputable section

open Matrix

namespace SGPT.Foundations.Analysis.FirstPass.MongeAmpere

open SGPT.Foundations.Analysis.Pending.SymmetricMultilinearDiagonal

variable {n : ℕ}

/-! ## The determinant side is symmetric and multilinear -/

theorem normalizedHermitianMatrix_add (A B : CoordinateRealTwoForm n) :
    normalizedHermitianMatrix (A + B) =
      normalizedHermitianMatrix A + normalizedHermitianMatrix B := by
  funext j k
  simp only [normalizedHermitianMatrix, Matrix.add_apply,
    ContinuousAlternatingMap.add_apply, Complex.ofReal_add]
  ring

theorem normalizedHermitianMatrix_smul (r : ℝ) (A : CoordinateRealTwoForm n) :
    normalizedHermitianMatrix (r • A) = r • normalizedHermitianMatrix A := by
  funext j k
  simp only [normalizedHermitianMatrix, Matrix.smul_apply,
    ContinuousAlternatingMap.smul_apply, smul_eq_mul, Complex.ofReal_mul,
    Complex.real_smul]
  ring

/-- The coefficient matrix of a real two-form, as an `ℝ`-linear map. -/
def normalizedHermitianMatrixₗ :
    CoordinateRealTwoForm n →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ where
  toFun := normalizedHermitianMatrix
  map_add' := normalizedHermitianMatrix_add
  map_smul' := normalizedHermitianMatrix_smul

/-- Updating one slot of the family of Hessians updates a single row of every permutation
summand of `mixedCoefficient`. -/
theorem mixedCoefficient_updateRow
    (H : Fin n → Matrix (Fin n) (Fin n) ℂ) (i : Fin n)
    (C : Matrix (Fin n) (Fin n) ℂ) (σ : Equiv.Perm (Fin n)) :
    (Matrix.of fun j k => (Function.update H i C) (σ j) j k) =
      Matrix.updateRow (Matrix.of fun j k => H (σ j) j k) (σ.symm i) (C (σ.symm i)) := by
  ext j k
  by_cases hj : j = σ.symm i
  · subst hj
    simp
  · have hσj : σ j ≠ i := fun h => hj (by rw [← h, Equiv.symm_apply_apply])
    rw [Matrix.updateRow_ne hj]
    simp [Function.update_of_ne hσj]

theorem mixedCoefficient_update_add
    (H : Fin n → Matrix (Fin n) (Fin n) ℂ) (i : Fin n)
    (X Y : Matrix (Fin n) (Fin n) ℂ) :
    MixedMongeAmpere.mixedCoefficient (Function.update H i (X + Y)) =
      MixedMongeAmpere.mixedCoefficient (Function.update H i X) +
        MixedMongeAmpere.mixedCoefficient (Function.update H i Y) := by
  unfold MixedMongeAmpere.mixedCoefficient
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun σ _ => ?_
  change Matrix.det (Matrix.of fun j k => (Function.update H i (X + Y)) (σ j) j k) =
      Matrix.det (Matrix.of fun j k => (Function.update H i X) (σ j) j k) +
        Matrix.det (Matrix.of fun j k => (Function.update H i Y) (σ j) j k)
  rw [mixedCoefficient_updateRow, mixedCoefficient_updateRow, mixedCoefficient_updateRow]
  have hXY : (X + Y) (σ.symm i) = X (σ.symm i) + Y (σ.symm i) := rfl
  rw [hXY, Matrix.det_updateRow_add]

theorem mixedCoefficient_update_smul
    (H : Fin n → Matrix (Fin n) (Fin n) ℂ) (i : Fin n)
    (r : ℝ) (X : Matrix (Fin n) (Fin n) ℂ) :
    MixedMongeAmpere.mixedCoefficient (Function.update H i (r • X)) =
      (r : ℂ) * MixedMongeAmpere.mixedCoefficient (Function.update H i X) := by
  unfold MixedMongeAmpere.mixedCoefficient
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  change Matrix.det (Matrix.of fun j k => (Function.update H i (r • X)) (σ j) j k) =
      (r : ℂ) * Matrix.det (Matrix.of fun j k => (Function.update H i X) (σ j) j k)
  rw [mixedCoefficient_updateRow, mixedCoefficient_updateRow]
  have hrX : (r • X) (σ.symm i) = (r : ℂ) • X (σ.symm i) := by
    funext k
    simp [Complex.real_smul]
  rw [hrX, Matrix.det_updateRow_smul]

/-- The mixed determinant density of a family of coefficient matrices, as an
`ℝ`-multilinear function. -/
def mixedCoefficientDensityMultilinear :
    MultilinearMap (RingHom.id ℝ) (fun _ : Fin n => Matrix (Fin n) (Fin n) ℂ) ℝ where
  toFun H := (MixedMongeAmpere.mixedCoefficient H).re / Real.pi ^ n
  map_update_add' := by
    intro inst H i X Y
    have hinst : inst = instDecidableEqFin n := by
      funext a b
      exact Subsingleton.elim _ _
    subst hinst
    rw [mixedCoefficient_update_add H i X Y, Complex.add_re]
    ring
  map_update_smul' := by
    intro inst H i r X
    have hinst : inst = instDecidableEqFin n := by
      funext a b
      exact Subsingleton.elim _ _
    subst hinst
    rw [mixedCoefficient_update_smul H i r X, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im]
    simp only [RingHom.id_apply, smul_eq_mul, zero_mul, sub_zero]
    ring

/-- The mixed analogue of `normalizedTopPowerDensity`. -/
def normalizedMixedTopDensity (A : Fin n → CoordinateRealTwoForm n) : ℝ :=
  (MixedMongeAmpere.mixedCoefficient (fun i => normalizedHermitianMatrix (A i))).re /
    Real.pi ^ n

/-- The diagonal of the mixed determinant density is the determinant density. -/
@[simp] theorem normalizedMixedTopDensity_const (A : CoordinateRealTwoForm n) :
    normalizedMixedTopDensity (fun _ => A) = normalizedTopPowerDensity A := by
  rw [normalizedMixedTopDensity, MixedMongeAmpere.mixedCoefficient_diagonal,
    normalizedTopPowerDensity, complexTopCoefficient_eq]
  simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero,
    Complex.ofReal_re, Complex.ofReal_im]
  have hpi : (Real.pi : ℝ) ^ n ≠ 0 := by positivity
  field_simp

theorem normalizedMixedTopDensity_perm (A : Fin n → CoordinateRealTwoForm n)
    (τ : Equiv.Perm (Fin n)) :
    normalizedMixedTopDensity (fun i => A (τ i)) = normalizedMixedTopDensity A := by
  rw [normalizedMixedTopDensity, normalizedMixedTopDensity,
    MixedMongeAmpere.mixedCoefficient_perm (fun i => normalizedHermitianMatrix (A i)) τ]

/-- The mixed determinant density as an `ℝ`-multilinear function of the two-forms. -/
def normalizedMixedTopDensityMultilinear :
    MultilinearMap (RingHom.id ℝ) (fun _ : Fin n => CoordinateRealTwoForm n) ℝ :=
  mixedCoefficientDensityMultilinear.compLinearMap fun _ => normalizedHermitianMatrixₗ

@[simp] theorem normalizedMixedTopDensityMultilinear_apply
    (A : Fin n → CoordinateRealTwoForm n) :
    normalizedMixedTopDensityMultilinear A = normalizedMixedTopDensity A := rfl

/-! ## Polarization over the `(1,1)`-forms -/

/-- The real `(1,1)`-forms form an `ℝ`-submodule of the real two-forms. -/
def oneOneSubmodule (n : ℕ) : Submodule ℝ (CoordinateRealTwoForm n) where
  carrier := {A | IsOneOne A}
  add_mem' := fun hA hB => isOneOne_add hA hB
  zero_mem' := by
    intro u v
    simp
  smul_mem' := fun r _ hA => isOneOne_smul r hA

@[simp] theorem mem_oneOneSubmodule {A : CoordinateRealTwoForm n} :
    A ∈ oneOneSubmodule n ↔ IsOneOne A := Iff.rfl

/-- The wedge density restricted to `(1,1)`-forms. -/
def actualMixedOneOne : MultilinearMap (RingHom.id ℝ) (fun _ : Fin n => oneOneSubmodule n) ℝ :=
  actualMixedTopDensityMultilinear.compLinearMap fun _ => (oneOneSubmodule n).subtype

/-- The determinant density restricted to `(1,1)`-forms. -/
def normalizedMixedOneOne : MultilinearMap (RingHom.id ℝ) (fun _ : Fin n => oneOneSubmodule n) ℝ :=
  normalizedMixedTopDensityMultilinear.compLinearMap fun _ => (oneOneSubmodule n).subtype

theorem isSymmetric_actualMixedOneOne :
    IsSymmetricMultilinear (actualMixedOneOne (n := n)) := by
  intro x τ
  exact actualMixedTopDensity_perm (fun i => (x i : CoordinateRealTwoForm n)) τ

theorem isSymmetric_normalizedMixedOneOne :
    IsSymmetricMultilinear (normalizedMixedOneOne (n := n)) := by
  intro x τ
  exact normalizedMixedTopDensity_perm (fun i => (x i : CoordinateRealTwoForm n)) τ

/-- **The mixed exterior-power/determinant density identity.**  For a family of real
`(1,1)`-forms the genuine mixed exterior product on the standard real frame is the mixed
determinant density of the coefficient matrices. -/
theorem actualMixedTopDensity_eq_normalizedMixedTopDensity
    (A : Fin n → CoordinateRealTwoForm n) (hA : ∀ i, IsOneOne (A i)) :
    actualMixedTopDensity A = normalizedMixedTopDensity A := by
  have hdiag : ∀ y : oneOneSubmodule n,
      actualMixedOneOne (fun _ => y) = normalizedMixedOneOne (fun _ => y) := by
    intro y
    change actualMixedTopDensity (fun _ => (y : CoordinateRealTwoForm n)) =
      normalizedMixedTopDensity (fun _ => (y : CoordinateRealTwoForm n))
    rw [actualMixedTopDensity_const, normalizedMixedTopDensity_const]
    exact actualTopPowerDensity_eq_normalizedTopPowerDensity _ y.2
  exact eq_of_diagonal_eq _ _ isSymmetric_actualMixedOneOne isSymmetric_normalizedMixedOneOne
    hdiag (fun i => ⟨A i, hA i⟩)

/-- **The geometric meaning of the mixed density** (blueprint `fpmma:geometric-density`).
For twice differentiable real potentials `u₁, …, uₙ`, the density of the genuine mixed
exterior product `ddᶜu₁ ∧ ⋯ ∧ ddᶜuₙ` with respect to Lebesgue measure in the standard
complex orientation is `D_{u₁,…,uₙ}`.  No plurisubharmonicity is assumed. -/
theorem actualMixedTopDensity_smoothDDC {u : Fin n → ComplexModel n → ℝ}
    {z : ComplexModel n} (hu : ∀ i, ContDiffAt ℝ 2 (u i) z) :
    actualMixedTopDensity (fun i => smoothDDC (u i) z) =
      MixedMongeAmpere.mixedDensity u z := by
  rw [actualMixedTopDensity_eq_normalizedMixedTopDensity _
      (fun i => smoothDDC_isOneOne (hu i)),
    normalizedMixedTopDensity, MixedMongeAmpere.mixedDensity]
  have hmat : (fun i => normalizedHermitianMatrix (smoothDDC (u i) z)) =
      fun i => complexHessian (u i) z := by
    funext i
    exact normalizedHermitianMatrix_smoothDDC (hu i)
  rw [hmat]

end SGPT.Foundations.Analysis.FirstPass.MongeAmpere
