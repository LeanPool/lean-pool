/-
Copyright (c) 2026 Mark Gladden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mark Gladden
-/

/- Modified from the C145 v0.6 release for Lean Pool's pinned toolchain. -/

module

public import LeanPool.C145.C145DRE8CommonUnit
public import LeanPool.C145.C145H2NumeratorData
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Shared literal Euclidean realization of the source Frobenius tensor space.
The norm is unweighted; calibrated overlaps belong inside the response map. -/

@[expose] public section

noncomputable section
namespace C145DRE8
open scoped BigOperators
variable {N : ℕ}

/-- The Euclidean space whose coordinates are triples of finite indices. -/
abbrev TensorSpace (N : ℕ) := EuclideanSpace ℝ (Fin N × Fin N × Fin N)

/-- Read the Euclidean coordinate at an index triple as a tensor entry. -/
def toTensor (E : TensorSpace N) : C145.H2.Tensor N := fun i j k => E (i,j,k)
/-- Place the tensor entries into Euclidean space indexed by triples. -/
def fromTensor (E : C145.H2.Tensor N) : TensorSpace N :=
  WithLp.toLp 2 (fun p => E p.1 p.2.1 p.2.2)

@[simp] theorem toTensor_apply (E : TensorSpace N) (i j k : Fin N) :
    toTensor E i j k = E (i,j,k) := rfl
@[simp] theorem fromTensor_apply (E : C145.H2.Tensor N) (p : Fin N × Fin N × Fin N) :
    fromTensor E p = E p.1 p.2.1 p.2.2 := rfl
@[simp] theorem toTensor_fromTensor (E : C145.H2.Tensor N) :
    toTensor (fromTensor E) = E := rfl
@[simp] theorem fromTensor_toTensor (E : TensorSpace N) : fromTensor (toTensor E) = E := by
  ext p
  rfl

/-- Exact unweighted Frobenius-coordinate linear equivalence. -/
def tensorEquiv : TensorSpace N ≃ₗ[ℝ] C145.H2.Tensor N where
  toFun := toTensor
  invFun := fromTensor
  left_inv := fromTensor_toTensor
  right_inv := toTensor_fromTensor
  map_add' E F := by funext i j k; rfl
  map_smul' c E := by funext i j k; rfl

@[simp] theorem tensorEquiv_apply (E : TensorSpace N) : tensorEquiv E = toTensor E := rfl
@[simp] theorem tensorEquiv_symm_apply (E : C145.H2.Tensor N) :
    tensorEquiv.symm E = fromTensor E := rfl

/-- The Hilbert norm is literally the source squared Frobenius norm. -/
theorem norm_sq_eq_tensorSq (E : TensorSpace N) : ‖E‖ ^ 2 = tensorSq (toTensor E) := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [tensorSq, toTensor, Fintype.sum_prod_type]

theorem norm_fromTensor_sq (E : C145.H2.Tensor N) : ‖fromTensor E‖ ^ 2 = tensorSq E := by
  rw [norm_sq_eq_tensorSq, toTensor_fromTensor]

end C145DRE8

end
