/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedComplexFiniteDimensional

/-!
# Full Fréchet derivative bound for Schwartz mollification

Coordinate bounds for the differentiated mollifier control the full
multilinear derivative norm uniformly in the velocity field.
-/

public section

open MeasureTheory
open scoped ENNReal SchwartzMap

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic LineDeriv

/-- The full finite-order spatial derivative of a Schwartz mollified
complex vector field. -/
@[expose]
def regularisedSchwartzMollifyDerivative
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (n : ℕ) (ψ : 𝓢(L2Vec3, ComplexVec3)) (x : L2Vec3) :
    ContinuousMultilinearMap ℝ (fun _ : Fin n => L2Vec3) ComplexVec3 :=
  iteratedFDeriv ℝ n (regularisedSchwartzMollify ρ ε hε ψ) x

private theorem regularisedSchwartzMollifyDerivative_apply
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (n : ℕ) (ψ : 𝓢(L2Vec3, ComplexVec3))
    (m : Fin n → L2Vec3) (x : L2Vec3) :
    regularisedSchwartzMollifyDerivative ρ ε hε n ψ x m =
      ∂^{m} (regularisedSchwartzMollify ρ ε hε ψ) x := by
  exact (SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv).symm

/-- The full derivative bound constant for mollifying a Schwartz function. -/
@[expose]
noncomputable def regularisedSchwartzMollifyFullConstant
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (n : ℕ) : ℝ :=
  (Fintype.card (Fin n → Fin 3) : ℝ) *
    Classical.choose
      (regularisedSchwartzMollify_coordinateDerivative_uniformBound
        ρ ε hε n)

/-- The full real Fréchet derivative of the complex Schwartz mollified
velocity has a pointwise L²-input bound for every fixed order. -/
theorem regularisedSchwartzMollify_iteratedFDeriv_norm_le
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (n : ℕ) (ψ : 𝓢(L2Vec3, ComplexVec3)) (x : L2Vec3) :
    ‖regularisedSchwartzMollifyDerivative ρ ε hε n ψ x‖ ≤
      regularisedSchwartzMollifyFullConstant ρ ε hε n * ‖ψ.toLp 2‖ := by
  let C := Classical.choose
    (regularisedSchwartzMollify_coordinateDerivative_uniformBound ρ ε hε n)
  have hSpec := Classical.choose_spec
    (regularisedSchwartzMollify_coordinateDerivative_uniformBound ρ ε hε n)
  have hC : 0 ≤ C := hSpec.1
  have hCoord := hSpec.2
  have hCdef : C = Classical.choose
      (regularisedSchwartzMollify_coordinateDerivative_uniformBound
        ρ ε hε n) := rfl
  clear_value C
  let T : ContinuousMultilinearMap ℝ (fun _ : Fin n => L2Vec3) ComplexVec3 :=
    regularisedSchwartzMollifyDerivative ρ ε hε n ψ x
  have hTdef : T = regularisedSchwartzMollifyDerivative ρ ε hε n ψ x := rfl
  clear_value T
  let V : ℝ := ‖ψ.toLp 2‖
  have hVdef : V = ‖ψ.toLp 2‖ := rfl
  clear_value V
  have hPoint (w : Fin n → Fin 3) :
      ‖T (fun k => regularisedSchwartzCoordinateDirection (w k))‖ ≤
        C * V := by
    have h := hCoord ψ w x
    rw [← regularisedSchwartzMollifyDerivative_apply] at h
    rw [show regularisedSchwartzCoordinateTuple w =
      (fun k => regularisedSchwartzCoordinateDirection (w k)) from rfl] at h
    rw [← hTdef] at h
    rw [hCdef, hVdef]
    exact h
  have hNorm : ‖T‖ ≤
      (Fintype.card (Fin n → Fin 3) : ℝ) *
        (C * V) := by
    clear hSpec hCoord hCdef hTdef
    apply regularisedComplexMultilinear_norm_le_coordinateBound
      (T := T) (B := C * V)
    · exact mul_nonneg hC (hVdef ▸ norm_nonneg _)
    · exact hPoint
  rw [hTdef] at hNorm
  rw [hVdef] at hNorm
  rw [hCdef] at hNorm
  simpa only [regularisedSchwartzMollifyFullConstant,
    mul_assoc] using hNorm

/-- A fixed mollifier and derivative order admit one nonnegative
constant for every complex Schwartz velocity field and spatial point. -/
theorem regularisedSchwartzMollify_iteratedFDeriv_uniformBound
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (ψ : 𝓢(L2Vec3, ComplexVec3)) (x : L2Vec3),
        ‖regularisedSchwartzMollifyDerivative ρ ε hε n ψ x‖ ≤
          C * ‖ψ.toLp 2‖ := by
  let C := regularisedSchwartzMollifyFullConstant ρ ε hε n
  have hC : 0 ≤ C := by
    unfold C regularisedSchwartzMollifyFullConstant
    apply mul_nonneg (by positivity)
    exact (Classical.choose_spec
      (regularisedSchwartzMollify_coordinateDerivative_uniformBound
        ρ ε hε n)).1
  refine ⟨C, hC, ?_⟩
  intro ψ x
  exact regularisedSchwartzMollify_iteratedFDeriv_norm_le
    ρ ε hε n ψ x

end CKN.Leray

end
