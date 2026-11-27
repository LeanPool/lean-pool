/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.JointSmoothKernelPatchPartition

/-!
# Actual four-patch operators on one joint completion

Finite addition is performed on the same original total-source Hilbert
space. Test-integral reconstruction derives integrability of the original
kernel against the supported tests before identifying the bounded form.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation

open MeasureTheory Set Metric
open scoped SchwartzMap InnerProductSpace

theorem jointKernel_four_integrals (c : Fin 2 → EuclideanSpace ℝ (Fin 3))
    (K : Fin 2 → Fin 2 → SchwartzMap JointKernelSpace ℂ) (F : JointKernelSpace → ℂ)
    (hF : ∀ x, x.fst ∈ closedBall (c 0) 1 ∪ closedBall (c 1) 1 →
      x.snd ∈ closedBall (c 0) 1 ∪ closedBall (c 1) 1 → (∑ i : Fin 2, ∑ j : Fin 2, K i j x) = F x)
    (f g : SpatialTestFunction)
    (hf : Function.support f.1 ⊆ closedBall (c 0) 1 ∪ closedBall (c 1) 1)
    (hg : Function.support g.1 ⊆ closedBall (c 0) 1 ∪ closedBall (c 1) 1) :
    Integrable (fun x : JointKernelSpace => (f.1 x.fst : ℂ) * (g.1 x.snd : ℂ) * F x) ∧
      (∫ x : JointKernelSpace, (f.1 x.fst : ℂ) * (g.1 x.snd : ℂ) * F x) =
        ∑ i : Fin 2, ∑ j : Fin 2,
          ∫ x : JointKernelSpace, (f.1 x.fst : ℂ) * (g.1 x.snd : ℂ) * K i j x := by
  have he (x : JointKernelSpace) :
      (f.1 x.fst : ℂ) * (g.1 x.snd : ℂ) * F x =
        ∑ i : Fin 2, ∑ j : Fin 2, (f.1 x.fst : ℂ) * (g.1 x.snd : ℂ) * K i j x := by
    by_cases hx : f.1 x.fst = 0
    · simp only [hx, Complex.ofReal_zero, zero_mul, Finset.sum_const_zero]
    by_cases hy : g.1 x.snd = 0
    · simp only [hy, Complex.ofReal_zero, mul_zero, zero_mul, Finset.sum_const_zero]
    rw [← hF x (hf hx) (hg hy)]
    simp only [Finset.mul_sum]
  have hi (i : Fin 2) := integrable_finsetSum Finset.univ
    (fun j _ => integrable_jointKernelTest (K i j) f g)
  constructor
  · have hh := integrable_finsetSum Finset.univ (fun i _ => hi i)
    exact hh.congr (Filter.Eventually.of_forall fun x => (he x).symm)
  · simp_rw [he]
    rw [integral_finsetSum Finset.univ (fun i _ => hi i)]
    apply Finset.sum_congr rfl
    intro i hi'
    exact integral_finsetSum Finset.univ (fun j _ => integrable_jointKernelTest (K i j) f g)

/-- Continuous linear map for the joint four field kernel operator, of type `SourceHilbert hμ U
→L[ℝ] SourceHilbert hμ U`. -/
def jointFourFieldKernelOperator {μ : ℝ} (hμ : 0 < μ)
    (U : Set (EuclideanSpace ℝ (Fin 3)))
    (K : Fin 2 → Fin 2 → SchwartzMap JointKernelSpace ℂ) : SourceHilbert hμ U →L[ℝ]
      SourceHilbert hμ U :=
  ∑ i : Fin 2, ∑ j : Fin 2, jointFieldKernelOperator hμ U (K i j)

/-- Continuous linear map for the joint four momentum kernel operator, of type `SourceHilbert hμ
(ball p 1 ∪ ball q 1) →L[ℝ] SourceHilbert hμ (ball p 1 ∪ ball q 1)`. -/
def jointFourMomentumKernelOperator {μ : ℝ} (hμ : 0 < μ)
    (p q : EuclideanSpace ℝ (Fin 3)) (K : Fin 2 → Fin 2 → SchwartzMap JointKernelSpace ℂ) :
    SourceHilbert hμ (ball p 1 ∪ ball q 1) →L[ℝ] SourceHilbert hμ (ball p 1 ∪ ball q 1) :=
  ∑ i : Fin 2, ∑ j : Fin 2, jointMomentumKernelOperator hμ p q (K i j)

private theorem norm_four_sum_le {E : Type*} [SeminormedAddCommGroup E]
    (A : Fin 2 → Fin 2 → E) {M : ℝ} (hA : ∀ i j, ‖A i j‖ ≤ M) :
    ‖∑ i : Fin 2, ∑ j : Fin 2, A i j‖ ≤ 4 * M := by
  calc
    _ ≤ ∑ i : Fin 2, ∑ j : Fin 2, ‖A i j‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => norm_sum_le _ _)
    _ ≤ ∑ _ : Fin 2, ∑ _ : Fin 2, M :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hA i j
    _ = _ := by simp only [Fin.sum_univ_two]; ring

/-- Four independently localized patches retain one universal constant,
with the explicit finite factor four. -/
theorem jointLocalKernel_four_operator_bounds {μ M : ℝ} (hμ : 0 < μ) (hM : 0 ≤ M)
    (c : Fin 2 → EuclideanSpace ℝ (Fin 3))
    (H : Fin 2 → Fin 2 → JointKernelSpace → ℂ)
    (O : Fin 2 → Fin 2 → Set JointKernelSpace) (hO : ∀ i j, IsOpen (O i j))
    (hbox : ∀ i j, jointKernelBox (c i) (c j) 2 ⊆ O i j)
    (hH : ∀ i j, ContDiffOn ℝ (⊤ : ℕ∞) (H i j) (O i j))
    (hbound : ∀ i j n, n ≤ 2 → ∀ x ∈ jointKernelBox (c i) (c j) 2,
      ‖iteratedFDeriv ℝ n (H i j) x‖ ≤ M) :
    let K := fun i j => cutOffJointLocalKernel (c i) (c j) (H i j) (O i j)
      (hO i j) (hbox i j) (hH i j)
    ‖jointFourFieldKernelOperator hμ (ball (c 0) 1 ∪ ball (c 1) 1) K‖ ≤
        (4 * jointSmoothKernelUniversalConstant) * max 1 μ * M ∧
      ‖jointFourMomentumKernelOperator hμ (c 0) (c 1) K‖ ≤
        (4 * jointSmoothKernelUniversalConstant) * M := by
  dsimp only
  have hb (i j : Fin 2) := jointLocalKernel_uniform_operator_bounds hμ hM
    (c i) (c j) (c 0) (c 1) (ball (c 0) 1 ∪ ball (c 1) 1)
      (H i j) (O i j) (hO i j) (hbox i j) (hH i j) (hbound i j)
  constructor
  · simpa only [jointFourFieldKernelOperator, mul_assoc] using
      norm_four_sum_le (E := SourceHilbert hμ (ball (c 0) 1 ∪ ball (c 1) 1) →L[ℝ]
        SourceHilbert hμ (ball (c 0) 1 ∪ ball (c 1) 1))
        (fun i j => jointFieldKernelOperator hμ (ball (c 0) 1 ∪ ball (c 1) 1)
          (cutOffJointLocalKernel (c i) (c j) (H i j) (O i j) (hO i j) (hbox i j) (hH i j)))
        (fun i j => (hb i j).1)
  · simpa only [jointFourMomentumKernelOperator, mul_assoc] using
      norm_four_sum_le (E := SourceHilbert hμ (ball (c 0) 1 ∪ ball (c 1) 1) →L[ℝ]
        SourceHilbert hμ (ball (c 0) 1 ∪ ball (c 1) 1))
        (fun i j => jointMomentumKernelOperator hμ (c 0) (c 1)
          (cutOffJointLocalKernel (c i) (c j) (H i j) (O i j) (hO i j) (hbox i j) (hH i j)))
        (fun i j => (hb i j).2)

end VacuumBellSeparation
