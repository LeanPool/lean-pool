/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.JointPolynomialOperatorIdentification

/-! # Self-adjointness from the literal symmetric spatial polynomial -/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation
open Gaussian MvPolynomial MeasureTheory
open scoped InnerProductSpace

/-- Exchange the two spatial arguments of the joint kernel. -/
def jointKernelSwap (x : JointKernelSpace) : JointKernelSpace := WithLp.toLp 2 (x.snd, x.fst)

theorem integral_jointKernel_swap (F : JointKernelSpace → ℂ) :
    (∫ x : JointKernelSpace, F (jointKernelSwap x)) = ∫ x : JointKernelSpace, F x := by
  calc
    _ = ∫ p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3),
        F (WithLp.toLp 2 (p.2, p.1)) :=
      integral_jointKernel_ofLp (fun p => F (WithLp.toLp 2 (p.2, p.1)))
    _ = ∫ p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3), F (WithLp.toLp 2 p) :=
      integral_prod_swap (fun p => F (WithLp.toLp 2 p))
    _ = _ := (integral_jointKernel_ofLp (fun p => F (WithLp.toLp 2 p))).symm

theorem jointPhysicalMidpoint_swap (s : ℝ) (x : JointKernelSpace) :
    jointPhysicalMidpoint s (jointComplexCoordinates (jointKernelSwap x)) =
      jointPhysicalMidpoint s (jointComplexCoordinates x) ∘ swapSpatialSix := by
  funext j
  fin_cases j <;> rfl

theorem jointPhysicalPolynomial_kernel_symmetric (F : (Fin 6 → ℂ) → ℂ)
    (s : ℝ) (n : ℕ) (x : JointKernelSpace) :
    eval (jointPhysicalMidpoint s (jointComplexCoordinates (jointKernelSwap x)))
        (jointMidpointPolynomial F n) =
      eval (jointPhysicalMidpoint s (jointComplexCoordinates x)) (jointMidpointPolynomial F n) := by
  rw [jointPhysicalMidpoint_swap, eval_jointMidpointPolynomial_symmetric]

theorem jointPhysicalPolynomial_test_integral_swap (F : (Fin 6 → ℂ) → ℂ)
    (s : ℝ) (n : ℕ) (f g : SpatialTestFunction) :
    (∫ x : JointKernelSpace, (f.1 x.fst : ℂ) * (g.1 x.snd : ℂ) *
      eval (jointPhysicalMidpoint s (jointComplexCoordinates x)) (jointMidpointPolynomial F n)) =
    (∫ x : JointKernelSpace, (g.1 x.fst : ℂ) * (f.1 x.snd : ℂ) *
      eval (jointPhysicalMidpoint s (jointComplexCoordinates x))
        (jointMidpointPolynomial F n)) := by
  rw [← integral_jointKernel_swap (fun x => (f.1 x.fst : ℂ) * (g.1 x.snd : ℂ) *
    eval (jointPhysicalMidpoint s (jointComplexCoordinates x)) (jointMidpointPolynomial F n))]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    beta_reduce
    rw [jointPhysicalPolynomial_kernel_symmetric]
    change (f.1 x.snd : ℂ) * (g.1 x.fst : ℂ) * _ = _
    ring

theorem jointFieldMomentPolynomial_isSelfAdjoint {μ : ℝ} (hμ : 0 < μ)
    (U : Set (EuclideanSpace ℝ (Fin 3))) (v : JointSourceMomentFamily hμ U)
    (F : (Fin 6 → ℂ) → ℂ) (s : ℝ) (n : ℕ) :
    IsSelfAdjoint (jointPolynomialMomentOperator (𝕜 := ℝ) v.field
      (jointPhysicalPolynomial s (jointMidpointPolynomial F n))) := by
  apply completionOperator_isSelfAdjoint_of_test_pairings
  intro x y
  rw [real_inner_comm, jointPhysicalPolynomial_field_pairing, jointPhysicalPolynomial_field_pairing]
  exact congrArg Complex.re (jointPhysicalPolynomial_test_integral_swap F s n y.1.1 x.1.1)

theorem jointMomentumMomentPolynomial_isSelfAdjoint {μ : ℝ} (hμ : 0 < μ)
    (U : Set (EuclideanSpace ℝ (Fin 3))) (v : JointSourceMomentFamily hμ U)
    (F : (Fin 6 → ℂ) → ℂ) (s : ℝ) (n : ℕ) :
    IsSelfAdjoint (jointPolynomialMomentOperator (𝕜 := ℝ) v.momentum
      (jointPhysicalPolynomial s (jointMidpointPolynomial F n))) := by
  apply completionOperator_isSelfAdjoint_of_test_pairings
  intro x y
  rw [real_inner_comm, jointPhysicalPolynomial_momentum_pairing,
    jointPhysicalPolynomial_momentum_pairing]
  exact congrArg Complex.re (jointPhysicalPolynomial_test_integral_swap F s n y.1.2 x.1.2)

theorem jointPolynomialKernelOperator_isSelfAdjoint {μ s : ℝ}
    (hμ : 0 < μ) (hs : 600 ≤ s) (v : JointSourceMomentFamily hμ (jointSourceRegion s)) (n : ℕ) :
    IsSelfAdjoint (jointPolynomialKernelOperator hμ hs n) := by
  rw [jointPolynomialKernelOperator_eq_moments hμ hs v n]
  exact (jointFieldMomentPolynomial_isSelfAdjoint hμ _ v _ s n).add
    (jointMomentumMomentPolynomial_isSelfAdjoint hμ _ v _ s n)

end VacuumBellSeparation
