/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Closure.EnstrophyBalanceTerms

/-!
# Regularity facts about the cutoff enstrophy

This file exposes, as public reusable facts, the nonnegativity of the cutoff enstrophy `Y` and
its dissipation `M` of `lem:aniso:closure` (currently only proved inline, privately, inside
`CIV.energy_inequality_of_mixed_term_bound`'s own proof) and the continuity/one-sided-derivative
consequences of the differentiation-under-the-integral-sign fact
`hasDerivAt_cutoffEnstrophy`. These four facts are exactly the `hM`, `hY`, `hcont`, `hderiv`,
`hY0` data that `CIV.deriv_le_of_closure_energy` and `CIV.closure_gronwall_bound` need to
run on the concrete quantities `Y := cutoffEnstrophy χ u` and `M := cutoffEnstrophyDissipation χ u`.
-/

public section

open MeasureTheory Set Filter Topology
open CKN.Foundation.Parabolic CKN

noncomputable section
namespace CIV



theorem cutoffEnstrophy_nonneg (χ : Vec3 → ℝ) (u : ParabolicPoint → Vec3) (t : ℝ) :
    0 ≤ cutoffEnstrophy χ u t := by
  unfold cutoffEnstrophy
  exact integral_nonneg (fun x =>
    mul_nonneg (sq_nonneg (χ x)) (Finset.sum_nonneg (fun i _ => sq_nonneg _)))

theorem cutoffEnstrophyDissipation_nonneg (χ : Vec3 → ℝ) (u : ParabolicPoint → Vec3) (t : ℝ) :
    0 ≤ cutoffEnstrophyDissipation χ u t := by
  unfold cutoffEnstrophyDissipation
  exact integral_nonneg (fun x =>
    mul_nonneg (sq_nonneg (χ x))
      (Finset.sum_nonneg (fun i _ =>
        Finset.sum_nonneg (fun j _ => sq_nonneg _))))

theorem continuousOn_cutoffEnstrophy {u : ParabolicPoint → Vec3}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    {χ : Vec3 → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχs : HasCompactSupport χ)
    (hχU : tsupport χ ⊆ vec3Ball 0 1) {tη s : ℝ} (htη : tη ∈ Ioo (-1 : ℝ) 0)
    (hs : s ∈ Ico tη 0) :
    ContinuousOn (cutoffEnstrophy χ u) (Icc tη s) := by
  intro s' hs'
  have hs'_left : tη ≤ s' := hs'.1
  have hs'_right : s' ≤ s := hs'.2
  have h_neg_one_lt_s' : -1 < s' := lt_of_lt_of_le htη.1 hs'_left
  have hs'_lt_zero : s' < 0 := lt_of_le_of_lt hs'_right hs.2
  have h_cont_at : ContinuousAt (cutoffEnstrophy χ u) s' :=
    (hasDerivAt_cutoffEnstrophy hu hχ hχs hχU
      ⟨h_neg_one_lt_s', hs'_lt_zero⟩).continuousAt
  exact h_cont_at.continuousWithinAt

theorem hasDerivWithinAt_Ici_cutoffEnstrophy {u : ParabolicPoint → Vec3}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    {χ : Vec3 → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχs : HasCompactSupport χ)
    (hχU : tsupport χ ⊆ vec3Ball 0 1) {tη t : ℝ} (htη : tη ∈ Ioo (-1 : ℝ) 0)
    (ht : t ∈ Ioo tη 0) :
    HasDerivWithinAt (cutoffEnstrophy χ u) (deriv (cutoffEnstrophy χ u) t) (Ici t) t := by
  have ht_mem : t ∈ Ioo (-1 : ℝ) 0 := ⟨lt_trans htη.1 ht.1, ht.2⟩
  have hd := hasDerivAt_cutoffEnstrophy hu hχ hχs hχU ht_mem
  rw [hd.deriv]
  exact hd.hasDerivWithinAt

end CIV
