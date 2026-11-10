/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.EhrhardGaussian.Ehrhard.TimeInterpolationSign
public import LeanPool.EhrhardGaussian.Ehrhard.OUEndpointContinuity

/-! # Finite-time sufficient comparison inside a strict sublevel -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Set
open EhrhardGaussian.Gaussian (coordinateDerivative standardGaussianMeasure)
open scoped Matrix BigOperators

namespace EhrhardGaussian.Ehrhard

/-- On a finite time interval, the matrix condition below a threshold implies the restricted
interpolation comparison. -/
theorem time_interpolation_comparison {n k : ℕ} {f : Fin k → (Fin n → ℝ) → ℝ}
    (hf : ∀ i, HasPolynomiallyBoundedThirdCoordinateDerivatives (f i))
    {lo hi G H : ℝ} (hG : 0 ≤ G) (hH : 0 ≤ H)
    (hbound : ∀ i y, f i y ∈ Icc lo hi) (hgrad : ∀ i y, ‖fderiv ℝ (f i) y‖ ≤ G)
    (hsecond : ∀ i j l y, |coordinateDerivative (coordinateDerivative (f i) j) l y| ≤ H)
    {l c T : ℝ} (hl : 0 < l) (hlc : l < c) (hcT : c ≤ T)
    {J : ℝ × (Fin k → ℝ) → ℝ}
    (hJ : ∀ s ∈ Icc l T, ∀ z : Fin k → ℝ, (∀ i, z i ∈ Icc lo hi) → ContDiffAt ℝ 2 J (s, z))
    (C : Matrix (Fin k) (Fin n) ℝ) (v : ℝ → (Fin n → ℝ) → (Fin k → ℝ))
    (D : ℝ → (Fin k → ℝ) → Matrix (Fin k) (Fin k) ℝ) (K : ℝ → ℝ)
    (hK : ∀ s ∈ Icc c T, 0 < K s)
    (hshape : ∀ s ∈ Icc c T, ∀ y i j,
      coordinateDerivative (fun z => ouAverage (f i) z s) j y = v s y i * C i j)
    (hgradient : ∀ s ∈ Icc c T, ∀ y,
      v s y ⬝ᵥ (D s (ouFamily f (s, y)) *ᵥ v s y) ≤ 1 / K s)
    {a b : ℝ}
    (hconditions : ∀ s ∈ Icc c T, ∀ y, J (s, ouFamily f (s, y)) < a →
      fderiv ℝ J (s, ouFamily f (s, y)) (1, 0) ≤ 0 ∧
      (((C * Cᵀ) ⊙ coordinateHessian (fun z => J (s, z)) (ouFamily f (s, y))) -
        (K s * fderiv ℝ J (s, ouFamily f (s, y)) (1, 0)) • D s (ouFamily f (s, y))).PosSemidef)
    (hsublevel : ∀ s ∈ Icc c T, ∀ y, J (s, ouFamily f (s, y)) < a)
    (hstart : ∀ y, J (c, ouFamily f (c, y)) ≤ b) :
    ∀ x, J (T, ouFamily f (T, x)) ≤
        ouAverage (fun y => J (c, ouFamily f (c, y))) x (T - c) ∧
      J (T, ouFamily f (T, x)) ≤ b := by
  have hf₂ := fun i => hasPolynomiallyBoundedSecond_of_third (hf i)
  have hf₁ := fun i => hasPolynomiallyBoundedCoordinateDerivatives_of_second (hf₂ i)
  let F := J ∘ ouSpaceTimeFamily f
  have hpoint (s) (hs : s ∈ Icc c T) (y : Fin n → ℝ) :
      fderiv ℝ J (s, ouFamily f (s, y)) (1, 0) -
        ouHessianContraction (fun z => J (s, z)) f s y ≤ 0 := by
    obtain ⟨htime, hmatrix⟩ := hconditions s hs y (hsublevel s hs y)
    exact time_interpolation_integrand_nonpos J f s y C (v s y) (hshape s hs y)
      (hK s hs) htime hmatrix (hgradient s hs y)
  have hcompact : IsCompact (Icc l T ×ˢ {z : Fin k → ℝ | ∀ i, z i ∈ Icc lo hi}) :=
    isCompact_Icc.prod (isCompact_probabilitySubbox (k := k) lo hi)
  obtain ⟨M, _, hM⟩ := exists_bound_firstDerivatives_on_compact hcompact
    (fun p hp => (hJ p.1 hp.1 p.2 hp.2).of_le (by norm_num))
  have hFcont : ContinuousOn F (Icc c T ×ˢ univ) := by
    intro p hp
    have hs : 0 < p.1 := hl.trans (hlc.trans_le hp.1.1)
    have hrange := ouFamily_mem_Icc hf₁ hbound p.2 p.1
    have hinner := (contDiffOn_ouSpaceTimeFamily hf₁).contDiffAt
      ((isOpen_Ioi.prod isOpen_univ).mem_nhds ⟨hs, mem_univ _⟩)
    exact (((hJ p.1 ⟨hlc.le.trans hp.1.1, hp.1.2⟩ _ hrange).of_le (by norm_num : (1 : WithTop ℕ∞) ≤
      2)).comp
      p hinner).continuousAt.continuousWithinAt
  have hFbound (s) (hs : s ∈ Icc c T) (y) : |F (s, y)| ≤ M :=
    (hM (s, ouFamily f (s, y))
      ⟨⟨hlc.le.trans hs.1, hs.2⟩, ouFamily_mem_Icc hf₁ hbound y s⟩).1
  intro x
  have hcontinuous := continuousOn_ouSpaceTimeAverage hFcont hFbound x
  have hder (s) (hs : s ∈ Ioo c T) :=
    hasDerivAt_time_ou_nonlinear_commutation_local hf hG hH hbound hgrad hsecond
      hl (hlc.trans hs.1) hs.2 le_rfl hJ x
  have hanti : AntitoneOn (ouSpaceTimeAverage F T x) (Icc c T) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _) hcontinuous
    · intro s hs
      rw [interior_Icc] at hs
      exact (hder s hs).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      rw [(hder s hs).deriv]
      apply integral_nonpos
      intro z
      exact hpoint s ⟨hs.1.le, hs.2.le⟩ _
  have hcomp := hanti ⟨le_rfl, hcT⟩ ⟨hcT, le_rfl⟩ hcT
  rw [ouSpaceTimeAverage_self, ouSpaceTimeAverage_eq_ouAverage] at hcomp
  have hsection : Continuous (fun y => F (c, y)) :=
    hFcont.comp_continuous (by fun_prop : Continuous (fun y : Fin n → ℝ => (c, y)))
      (fun _ => ⟨⟨le_rfl, hcT⟩, mem_univ _⟩)
  exact ⟨hcomp, hcomp.trans
    (ouAverage_le_of_bounded hsection (hFbound c ⟨le_rfl, hcT⟩) hstart x (T - c))⟩

end EhrhardGaussian.Ehrhard

end
