/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.EhrhardGaussian.Ehrhard.OUComposition
import Mathlib.Analysis.Normed.Operator.Prod

/-! # Domination for a time-dependent functional of OU-smoothed inputs -/

@[expose] public noncomputable section

open Set
open EhrhardGaussian.Gaussian (coordinateDerivative)

namespace EhrhardGaussian.Ehrhard

/-- A continuously differentiable function and its derivative have a common bound on a compact set.
-/
theorem exists_bound_firstDerivatives_on_compact {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {K : Set E} (hK : IsCompact K)
    {J : E → ℝ} (hJ : ∀ z ∈ K, ContDiffAt ℝ 1 J z) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z ∈ K, |J z| ≤ M ∧ ‖fderiv ℝ J z‖ ≤ M := by
  let Q := fun z => (J z, fderiv ℝ J z)
  have hQ : ContinuousOn Q K := fun z hz =>
    ((hJ z hz).continuousAt.prodMk ((hJ z hz).continuousAt_fderiv one_ne_zero)).continuousWithinAt
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hQ
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro z hz
  constructor
  · simpa only [Real.norm_eq_abs] using
      (norm_fst_le (Q z)).trans ((hC z hz).trans (le_max_left _ _))
  · exact (norm_snd_le (Q z)).trans ((hC z hz).trans (le_max_left _ _))

/-- Keep time together with the vector of smoothed inputs. -/
def ouSpaceTimeFamily {n k : ℕ} (f : Fin k → (Fin n → ℝ) → ℝ)
    (p : ℝ × (Fin n → ℝ)) : ℝ × (Fin k → ℝ) := (p.1, ouFamily f p)

/-- The Ornstein–Uhlenbeck space–time family is continuously differentiable at positive times. -/
theorem contDiffOn_ouSpaceTimeFamily {n k : ℕ} {f : Fin k → (Fin n → ℝ) → ℝ}
    (hf : ∀ i, HasPolynomiallyBoundedCoordinateDerivatives (f i)) :
    ContDiffOn ℝ 1 (ouSpaceTimeFamily f) (Ioi (0 : ℝ) ×ˢ univ) :=
  contDiffOn_fst.prodMk (contDiffOn_ouFamily hf)

/-- Uniform value and derivative bounds give a linear spatial growth bound for the space–time family
derivative. -/
theorem norm_fderiv_ouSpaceTimeFamily_le {n k : ℕ} {f : Fin k → (Fin n → ℝ) → ℝ}
    (hf : ∀ i, HasPolynomiallyBoundedSecondCoordinateDerivatives (f i)) {B G H : ℝ}
    (hB : 0 ≤ B) (hG : 0 ≤ G) (hH : 0 ≤ H)
    (hvalue : ∀ i y, |f i y| ≤ B) (hgrad : ∀ i y, ‖fderiv ℝ (f i) y‖ ≤ G)
    (hsecond : ∀ i j y, |coordinateDerivative (coordinateDerivative (f i) j) j y| ≤ H)
    {t : ℝ} (ht : 0 < t) (x : Fin n → ℝ) :
    ‖fderiv ℝ (ouSpaceTimeFamily f) (t, x)‖ ≤
      1 + (B + (n : ℝ) * H + G) * (1 + ‖x‖) := by
  have hp : (t, x) ∈ Ioi (0 : ℝ) ×ˢ (univ : Set (Fin n → ℝ)) := ⟨ht, mem_univ _⟩
  have hdiff := ((contDiffOn_ouFamily (fun i =>
    hasPolynomiallyBoundedCoordinateDerivatives_of_second (hf i))).contDiffAt
    ((isOpen_Ioi.prod isOpen_univ).mem_nhds hp)).differentiableAt_one
  have hder := (hasFDerivAt_fst (𝕜 := ℝ) (p := (t, x))).prodMk hdiff.hasFDerivAt
  change ‖fderiv ℝ (fun p => (p.1, ouFamily f p)) (t, x)‖ ≤ _
  rw [hder.fderiv,
    ContinuousLinearMap.opNorm_prod, Prod.norm_mk]
  apply max_le
  · exact (ContinuousLinearMap.norm_fst_le ℝ ℝ (Fin n → ℝ)).trans
      (by have h : 0 ≤ (B + (n : ℝ) * H + G) * (1 + ‖x‖) := by positivity
          linarith only [h])
  · exact (norm_fderiv_ouFamily_le hf hB hG hH hvalue hgrad hsecond ht x).trans
      (le_add_of_nonneg_left zero_le_one)

/-- A smooth time dependent composition with an Ornstein–Uhlenbeck family is continuously
differentiable on the interior time interval. -/
theorem contDiffOn_time_ouComposition {n k : ℕ} {f : Fin k → (Fin n → ℝ) → ℝ}
    (hf : ∀ i, HasPolynomiallyBoundedCoordinateDerivatives (f i)) {a b l u : ℝ}
    (hl : 0 < l) (hbound : ∀ i y, f i y ∈ Icc a b) {J : ℝ × (Fin k → ℝ) → ℝ}
    (hJ : ∀ s ∈ Icc l u, ∀ z : Fin k → ℝ, (∀ i, z i ∈ Icc a b) → ContDiffAt ℝ 2 J (s, z)) :
    ContDiffOn ℝ 1 (J ∘ ouSpaceTimeFamily f) (Ioo l u ×ˢ univ) := by
  intro p hp
  exact ((hJ p.1 ⟨hp.1.1.le, hp.1.2.le⟩ _ (ouFamily_mem_Icc hf hbound p.2 p.1)).of_le
    (by norm_num)).comp_contDiffWithinAt p
    ((contDiffOn_ouSpaceTimeFamily hf).mono (fun _ h => ⟨hl.trans h.1.1, h.2⟩) p hp)

/-- Compact time slabs provide the domination needed to differentiate the
time-dependent nonlinear interpolation. No derivative of the composite is
assumed bounded independently of the given smooth input and functional. -/
theorem exists_time_ouComposition_bound {n k : ℕ} {f : Fin k → (Fin n → ℝ) → ℝ}
    (hf : ∀ i, HasPolynomiallyBoundedSecondCoordinateDerivatives (f i))
    {a b l u G H : ℝ} (hl : 0 < l) (hG : 0 ≤ G) (hH : 0 ≤ H)
    (hbound : ∀ i y, f i y ∈ Icc a b) (hgrad : ∀ i y, ‖fderiv ℝ (f i) y‖ ≤ G)
    (hsecond : ∀ i j y, |coordinateDerivative (coordinateDerivative (f i) j) j y| ≤ H)
    {J : ℝ × (Fin k → ℝ) → ℝ}
    (hJ : ∀ s ∈ Icc l u, ∀ z : Fin k → ℝ, (∀ i, z i ∈ Icc a b) → ContDiffAt ℝ 2 J (s, z)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Ioo l u, ∀ y : Fin n → ℝ,
      |J (s, ouFamily f (s, y))| + ‖fderiv ℝ (J ∘ ouSpaceTimeFamily f) (s, y)‖ ≤
        C * (1 + ‖y‖) := by
  have hf₁ := fun i => hasPolynomiallyBoundedCoordinateDerivatives_of_second (hf i)
  have hcompact : IsCompact (Icc l u ×ˢ {z : Fin k → ℝ | ∀ i, z i ∈ Icc a b}) :=
    isCompact_Icc.prod (isCompact_probabilitySubbox (k := k) a b)
  obtain ⟨M, hM, hMbound⟩ := exists_bound_firstDerivatives_on_compact hcompact
    (fun p hp => (hJ p.1 hp.1 p.2 hp.2).of_le (by norm_num))
  let B := max |a| |b|
  let A := B + (n : ℝ) * H + G
  have hB : 0 ≤ B := (abs_nonneg a).trans (le_max_left _ _)
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hvalue (i) (y) : |f i y| ≤ B := abs_le_max_abs_abs (hbound i y).1 (hbound i y).2
  refine ⟨M * (2 + A), by positivity, ?_⟩
  intro s hs y
  have hrange := ouFamily_mem_Icc hf₁ hbound y s
  have hjoint : (s, ouFamily f (s, y)) ∈ Icc l u ×ˢ {z : Fin k → ℝ | ∀ i, z i ∈ Icc a b} :=
    ⟨⟨hs.1.le, hs.2.le⟩, hrange⟩
  have hp : (s, y) ∈ Ioi (0 : ℝ) ×ˢ (univ : Set (Fin n → ℝ)) := ⟨hl.trans hs.1, mem_univ _⟩
  have hdiff := ((contDiffOn_ouSpaceTimeFamily hf₁).contDiffAt
    ((isOpen_Ioi.prod isOpen_univ).mem_nhds hp)).differentiableAt_one
  have houter : DifferentiableAt ℝ J (s, ouFamily f (s, y)) :=
    (hJ s ⟨hs.1.le, hs.2.le⟩ _ hrange).differentiableAt (by norm_num : (2 : WithTop ℕ∞) ≠ 0)
  have hnorm : ‖fderiv ℝ (J ∘ ouSpaceTimeFamily f) (s, y)‖ ≤ M * (1 + A * (1 + ‖y‖)) := by
    rw [fderiv_comp (s, y) (g := J) (f := ouSpaceTimeFamily f) houter hdiff]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul (hMbound _ hjoint).2
        (norm_fderiv_ouSpaceTimeFamily_le hf hB hG hH hvalue hgrad hsecond (hl.trans hs.1) y)
        (norm_nonneg _) hM)
  calc
    _ ≤ M + M * (1 + A * (1 + ‖y‖)) := add_le_add (hMbound _ hjoint).1 hnorm
    _ ≤ M * (2 + A) * (1 + ‖y‖) := by
      have h := mul_nonneg hM (norm_nonneg y)
      nlinarith only [h]

end EhrhardGaussian.Ehrhard

end
