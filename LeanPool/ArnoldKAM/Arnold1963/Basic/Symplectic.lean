/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Basic.Spaces
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.SymplecticGroup
public import Mathlib.Tactic.Ring

/-!
The standard symplectic form in (p, q) coordinates, its nondegeneracy, and covector duality.
Symplecticity means preservation of this concrete bilinear form; it implies linear invertibility.
-/

@[expose] public section

noncomputable section

namespace KamProject.Arnold1963

/-- The action-coordinate basis direction in phase space. -/
def pDirection {n : ℕ} (j : Fin n) : ComplexPhaseSpace n := (Pi.single j 1, 0)
/-- The angle-coordinate basis direction in phase space. -/
def qDirection {n : ℕ} (j : Fin n) : ComplexPhaseSpace n := (0, Pi.single j 1)

@[simp] theorem norm_pDirection {n : ℕ} (j : Fin n) : ‖pDirection j‖ = 1 := by
  simp [pDirection, Pi.norm_single]

@[simp] theorem norm_qDirection {n : ℕ} (j : Fin n) : ‖qDirection j‖ = 1 := by
  simp [qDirection, Pi.norm_single]

/-- The standard complex symplectic form in action-angle coordinates. -/
def symplecticForm {n : ℕ} (v w : ComplexPhaseSpace n) : ℂ :=
  ∑ j, (v.1 j * w.2 j - v.2 j * w.1 j)

theorem phase_decomposition {n : ℕ} (v : ComplexPhaseSpace n) :
    v = (∑ j, v.1 j • pDirection j) + ∑ j, v.2 j • qDirection j := by
  simp only [pDirection, qDirection, Prod.smul_mk, smul_zero, ← prod_mk_sum]
  simp only [Finset.sum_const_zero, Prod.mk_add_mk, add_zero, zero_add]
  exact Prod.ext (pi_eq_sum_univ' v.1) (pi_eq_sum_univ' v.2)

@[simp] theorem symplecticForm_pDirection {n : ℕ} (j : Fin n)
    (w : ComplexPhaseSpace n) : symplecticForm (pDirection j) w = w.2 j := by
  simp [symplecticForm, pDirection, Pi.single_apply]

@[simp] theorem symplecticForm_qDirection {n : ℕ} (j : Fin n)
    (w : ComplexPhaseSpace n) : symplecticForm (qDirection j) w = -w.1 j := by
  simp [symplecticForm, qDirection, Pi.single_apply]

theorem symplecticForm_skew {n : ℕ} (v w : ComplexPhaseSpace n) :
    symplecticForm v w = -symplecticForm w v := by
  rw [symplecticForm, symplecticForm, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

@[simp] theorem symplecticForm_self {n : ℕ} (v : ComplexPhaseSpace n) :
    symplecticForm v v = 0 := by simp [symplecticForm, mul_comm]

theorem symplecticForm_add_left {n : ℕ} (u v w : ComplexPhaseSpace n) :
    symplecticForm (u + v) w = symplecticForm u w + symplecticForm v w := by
  simp only [symplecticForm, Prod.fst_add, Prod.snd_add, Pi.add_apply, add_mul]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem symplecticForm_smul_left {n : ℕ} (c : ℂ) (v w : ComplexPhaseSpace n) :
    symplecticForm (c • v) w = c * symplecticForm v w := by
  simp only [symplecticForm, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem symplecticForm_ext_right {n : ℕ} {u w : ComplexPhaseSpace n}
    (h : ∀ v, symplecticForm v u = symplecticForm v w) : u = w := by
  apply Prod.ext
  · funext j
    have hj := h (qDirection j)
    simpa using hj
  · funext j
    simpa using h (pDirection j)

/-- The phase vector associated with a linear functional by the symplectic form. -/
def symplecticSharp {n : ℕ} (L : ComplexPhaseSpace n →ₗ[ℂ] ℂ) :
    ComplexPhaseSpace n := (fun j => -L (qDirection j), fun j => L (pDirection j))

theorem linearForm_decomposition {n : ℕ} (L : ComplexPhaseSpace n →ₗ[ℂ] ℂ)
    (v : ComplexPhaseSpace n) :
    L v = (∑ j, v.1 j * L (pDirection j)) + ∑ j, v.2 j * L (qDirection j) := by
  conv_lhs => rw [phase_decomposition v]
  simp

theorem symplecticForm_sharp {n : ℕ} (L : ComplexPhaseSpace n →ₗ[ℂ] ℂ)
    (v : ComplexPhaseSpace n) : symplecticForm v (symplecticSharp L) = L v := by
  rw [linearForm_decomposition L v]
  simp [symplecticForm, symplecticSharp, Finset.sum_add_distrib]

/-- Preservation of the standard symplectic form by a linear phase transformation. -/
def IsSymplecticLinear {n : ℕ} (A : ComplexPhaseSpace n →ₗ[ℂ] ComplexPhaseSpace n) :
    Prop := ∀ v w, symplecticForm (A v) (A w) = symplecticForm v w

theorem IsSymplecticLinear.injective {n : ℕ}
    {A : ComplexPhaseSpace n →ₗ[ℂ] ComplexPhaseSpace n} (hA : IsSymplecticLinear A) :
    Function.Injective A := by
  intro x y hxy
  apply symplecticForm_ext_right
  intro v
  rw [← hA v x, ← hA v y, hxy]

theorem IsSymplecticLinear.surjective {n : ℕ}
    {A : ComplexPhaseSpace n →ₗ[ℂ] ComplexPhaseSpace n} (hA : IsSymplecticLinear A) :
    Function.Surjective A := LinearMap.surjective_of_injective hA.injective

theorem IsSymplecticLinear.comp {n : ℕ}
    {A B : ComplexPhaseSpace n →ₗ[ℂ] ComplexPhaseSpace n}
    (hA : IsSymplecticLinear A) (hB : IsSymplecticLinear B) :
    IsSymplecticLinear (A.comp B) := by
  intro v w
  exact (hA (B v) (B w)).trans (hB v w)

theorem IsSymplecticLinear.map_sharp_comp {n : ℕ}
    {A : ComplexPhaseSpace n →ₗ[ℂ] ComplexPhaseSpace n} (hA : IsSymplecticLinear A)
    (L : ComplexPhaseSpace n →ₗ[ℂ] ℂ) :
    A (symplecticSharp (L.comp A)) = symplecticSharp L := by
  apply symplecticForm_ext_right
  intro v
  obtain ⟨w, rfl⟩ := hA.surjective v
  rw [hA, symplecticForm_sharp, symplecticForm_sharp]
  rfl

/-- A unified action-angle basis indexed by the disjoint union of coordinate indices. -/
def phaseDirection {n : ℕ} : Fin n ⊕ Fin n → ComplexPhaseSpace n
  | .inl j => pDirection j
  | .inr j => qDirection j

/-- The matrix of the chosen symplectic sign convention in the unified phase basis. -/
def symplecticMatrix (n : ℕ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ :=
  -Matrix.J (Fin n) ℂ

@[simp] theorem symplecticMatrix_pp {n : ℕ} (i j : Fin n) :
    symplecticMatrix n (.inl i) (.inl j) = 0 := by
  simp [symplecticMatrix, Matrix.J]

@[simp] theorem symplecticMatrix_pq {n : ℕ} (i j : Fin n) :
    symplecticMatrix n (.inl i) (.inr j) = if i = j then 1 else 0 := by
  simp [symplecticMatrix, Matrix.J, Matrix.one_apply]

@[simp] theorem symplecticMatrix_qp {n : ℕ} (i j : Fin n) :
    symplecticMatrix n (.inr i) (.inl j) = -(if i = j then 1 else 0) := by
  simp [symplecticMatrix, Matrix.J, Matrix.one_apply]

@[simp] theorem symplecticMatrix_qq {n : ℕ} (i j : Fin n) :
    symplecticMatrix n (.inr i) (.inr j) = 0 := by
  simp [symplecticMatrix, Matrix.J]

theorem symplecticMatrix_apply {n : ℕ} (i j : Fin n ⊕ Fin n) :
    symplecticMatrix n i j = symplecticForm (phaseDirection i) (phaseDirection j) := by
  rcases i with i | i <;> rcases j with j | j <;>
    simp [phaseDirection, pDirection, qDirection, symplecticForm, Pi.single_apply, eq_comm]

end KamProject.Arnold1963
