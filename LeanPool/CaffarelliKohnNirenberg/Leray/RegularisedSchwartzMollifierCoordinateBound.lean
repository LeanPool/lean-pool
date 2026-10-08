/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedSchwartzMollifierDerivativeBound
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Ambient.Basis

/-!
# Uniform coordinate derivative constants for mollification

For each fixed order, one finite constant bounds every ordered
coordinate derivative of the mollified velocity.
-/

public section

open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform SchwartzMap Convolution

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic LineDeriv

/-- A CKN coordinate direction in the Fourier spatial carrier. -/
@[expose]
def regularisedSchwartzCoordinateDirection (i : Fin 3) : L2Vec3 :=
  WithLp.toLp 2 (CKN.basisVec i)

/-- An ordered tuple of Fourier spatial coordinate directions. -/
@[expose]
def regularisedSchwartzCoordinateTuple {n : ℕ}
    (w : Fin n → Fin 3) : Fin n → L2Vec3 :=
  fun k => regularisedSchwartzCoordinateDirection (w k)

/-- The finite family of coordinate kernel directions used in the Schwartz mollifier estimate. -/
@[expose]
def regularisedSchwartzCoordinateKernelSum
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (n : ℕ) : ℝ :=
  ∑ w : Fin n → Fin 3,
    ‖(∂^{regularisedSchwartzCoordinateTuple w}
      (regularisedComplexMollifierSchwartz ρ ε hε)).toLp 2‖

/-- One constant, chosen before the velocity field, controls every
ordered coordinate derivative of fixed-order Schwartz mollification. -/
theorem regularisedSchwartzMollify_coordinateDerivative_norm_le
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (n : ℕ) (ψ : 𝓢(L2Vec3, ComplexVec3))
    (w : Fin n → Fin 3) (x : L2Vec3) :
    ‖∂^{regularisedSchwartzCoordinateTuple w}
      (regularisedSchwartzMollify ρ ε hε ψ) x‖ ≤
        regularisedSchwartzCoordinateKernelSum ρ ε hε n * ‖ψ.toLp 2‖ := by
  classical
  let κ := regularisedComplexMollifierSchwartz ρ ε hε
  let M : (Fin n → Fin 3) → ℝ := fun w =>
    ‖(∂^{regularisedSchwartzCoordinateTuple w} κ).toLp 2‖
  let C : ℝ := regularisedSchwartzCoordinateKernelSum ρ ε hε n
  have hM' : M w ≤ ∑ v : Fin n → Fin 3, M v := by
    apply Finset.single_le_sum (f := M)
    · intro v _
      exact norm_nonneg _
    · exact Finset.mem_univ w
  have hM : M w ≤ C := by
    simpa only [C, regularisedSchwartzCoordinateKernelSum,
      M, κ] using hM'
  exact (regularisedSchwartzMollify_iteratedLineDeriv_norm_le
    ρ ε hε ψ n (regularisedSchwartzCoordinateTuple w) x).trans
      (mul_le_mul_of_nonneg_right hM (norm_nonneg _))

/-- For each derivative order, one finite nonnegative constant chosen
before the velocity controls every ordered coordinate derivative. -/
theorem regularisedSchwartzMollify_coordinateDerivative_uniformBound
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (ψ : 𝓢(L2Vec3, ComplexVec3))
        (w : Fin n → Fin 3) (x : L2Vec3),
        ‖∂^{regularisedSchwartzCoordinateTuple w}
          (regularisedSchwartzMollify ρ ε hε ψ) x‖ ≤
            C * ‖ψ.toLp 2‖ := by
  let C := regularisedSchwartzCoordinateKernelSum ρ ε hε n
  have hC : 0 ≤ C := by
    dsimp only [C, regularisedSchwartzCoordinateKernelSum]
    exact Finset.sum_nonneg (fun w _ => norm_nonneg _)
  refine ⟨C, hC, ?_⟩
  intro ψ w x
  exact regularisedSchwartzMollify_coordinateDerivative_norm_le
    ρ ε hε n ψ w x

end CKN.Leray

end
