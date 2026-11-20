/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Fourier.PeriodicH2

/-!
# The pointwise horizontal projection `ℂ³ → ℂ²` and its isometric right inverse

The paper writes the torus operator `eq:torus-sector` and the whole-plane local generator
`eq:local-generator` on the **two horizontal components only**, while the velocity data stay
three-component.  Both sides of that comparison — the torus fixed-sector chain of
`Operator/HorizontalSector.lean` and the whole-plane chain of `Operator/WholePlaneLocalC2.lean`
— need the same two pointwise fibre maps:

* `horizontalProjPoint : ℂ³ → ℂ²`, dropping the axial coordinate;
* `verticalZeroExtendPoint : ℂ² → ℂ³`, appending a vanishing axial coordinate.

They are pure fibre maps: nothing about them is specific to the torus, to the plane, or to the
seed.  They live here, upstream of both chains, so that both chains share them.

`horizontalProjPoint` is a left inverse of `verticalZeroExtendPoint`, which is in addition an
isometry for the Hermitian inner product; that is what lets a fibre-diagonal three-component
identity (diffusion, transport, axial multiplier) be read on two components.  The stretching
term is the one term that does **not** commute with either map — the `(3, ⊥)` block recorded in
`Operator/HorizontalSector.lean`.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

/-! ## The horizontal projection -/

/-- Drop the axial coordinate of `ℂ³`, as a continuous complex linear map `π⊥`. -/
def horizontalProjPoint : C3 →L[ℂ] C2 :=
  (PiLp.continuousLinearEquiv 2 ℂ
      (fun _ : Fin 2 ↦ ℂ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun j : Fin 2 ↦ PiLp.proj 2 (fun _ : Fin 3 ↦ ℂ) j.castSucc)

/-- The horizontal projection acts coordinatewise: its `j`-th entry is the `j`-th entry of the
original vector, for `j < 2`. -/
@[simp] theorem horizontalProjPoint_apply (v : C3) (j : Fin 2) :
    horizontalProjPoint v j = v j.castSucc :=
  rfl

/-- The horizontal projection does not increase the Euclidean norm: it drops one coordinate. -/
theorem norm_horizontalProjPoint_le (v : C3) : ‖horizontalProjPoint v‖ ≤ ‖v‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  refine Real.sqrt_le_sqrt ?_
  rw [Fin.sum_univ_two, Fin.sum_univ_three]
  have h0 : ‖horizontalProjPoint v 0‖ = ‖v 0‖ := by
    rw [horizontalProjPoint_apply]
    rfl
  have h1 : ‖horizontalProjPoint v 1‖ = ‖v 1‖ := by
    rw [horizontalProjPoint_apply]
    rfl
  rw [h0, h1]
  have h2 : (0 : ℝ) ≤ ‖v 2‖ ^ 2 := sq_nonneg _
  linarith

/-! ## The vertical zero-extension -/

/-- Append a vanishing axial coordinate, as a continuous complex linear map `ℂ² → ℂ³`. -/
def verticalZeroExtendPoint : C2 →L[ℂ] C3 :=
  (PiLp.continuousLinearEquiv 2 ℂ
      (fun _ : Fin 3 ↦ ℂ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i : Fin 3 ↦
      if h : (i : ℕ) < 2 then PiLp.proj 2 (fun _ : Fin 2 ↦ ℂ) ⟨i, h⟩ else 0)

/-- The zero-extension keeps the horizontal coordinates. -/
@[simp] theorem verticalZeroExtendPoint_apply_castSucc (v : C2) (j : Fin 2) :
    verticalZeroExtendPoint v j.castSucc = v j := by
  fin_cases j <;> rfl

/-- The zero-extension has vanishing axial coordinate. -/
@[simp] theorem verticalZeroExtendPoint_apply_two (v : C2) :
    verticalZeroExtendPoint v 2 = 0 :=
  rfl

/-- The horizontal projection undoes the zero-extension. -/
@[simp] theorem horizontalProjPoint_verticalZeroExtendPoint (v : C2) :
    horizontalProjPoint (verticalZeroExtendPoint v) = v := by
  apply PiLp.ext
  intro j
  rw [horizontalProjPoint_apply, verticalZeroExtendPoint_apply_castSucc]

/-- The zero-extension preserves the Hermitian inner product. -/
theorem inner_verticalZeroExtendPoint (v w : C2) :
    (inner ℂ (verticalZeroExtendPoint v) (verticalZeroExtendPoint w) : ℂ) =
      inner ℂ v w := by
  rw [PiLp.inner_apply, PiLp.inner_apply, Fin.sum_univ_three, Fin.sum_univ_two]
  have h0 : verticalZeroExtendPoint v 0 = v 0 :=
    verticalZeroExtendPoint_apply_castSucc v 0
  have h0' : verticalZeroExtendPoint w 0 = w 0 :=
    verticalZeroExtendPoint_apply_castSucc w 0
  have h1 : verticalZeroExtendPoint v 1 = v 1 :=
    verticalZeroExtendPoint_apply_castSucc v 1
  have h1' : verticalZeroExtendPoint w 1 = w 1 :=
    verticalZeroExtendPoint_apply_castSucc w 1
  rw [h0, h0', h1, h1', verticalZeroExtendPoint_apply_two,
    verticalZeroExtendPoint_apply_two]
  simp

end

end FastDynamo
