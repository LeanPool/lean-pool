/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Frozen.CoarseEllipticityDagger
public import LeanPool.HighContrastHomogenization.Support.Probability.IndependentSums.Triangle

/-!
# High-contrast homogenization: Annealed.SourceIntegrability

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The source scale has a first moment

The gauge tail bound of `e.coarse.ellipticity` together with the growth
witness `t Ψ(t) ≤ Ψ(K t)` forces the gauge to outgrow every polynomial, so the
source scale is integrable over the law.  This is the probabilistic half of the
argument that makes the annealed block an honest expectation at every scale.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- The growth witness of a gauge may be enlarged. -/
theorem hasPsiGrowth_mono {Ψ : ℝ → ℝ} {K K' : ℝ}
    (hadm : IndependentSums.AdmissiblePsi Ψ) (hK : 1 ≤ K) (hKK' : K ≤ K')
    (hgrow : IndependentSums.HasPsiGrowth Ψ K) :
    IndependentSums.HasPsiGrowth Ψ K' := by
  intro t ht
  refine le_trans (hgrow ht) ?_
  have ht0 : (0 : ℝ) ≤ t := le_trans zero_le_one ht
  have hK0 : (0 : ℝ) ≤ K := le_trans zero_le_one hK
  have hK'0 : (0 : ℝ) ≤ K' := le_trans hK0 hKK'
  exact hadm.1 (Set.mem_Ici.2 (mul_nonneg hK0 ht0))
    (Set.mem_Ici.2 (mul_nonneg hK'0 ht0))
    (mul_le_mul_of_nonneg_right hKK' ht0)

/-- **The source scale is integrable.**  The gauge tail bound of
`e.coarse.ellipticity` together with the growth witness makes the tail of the
source integrable. -/
theorem integrable_source_of_coarseEllipticityDagger
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P] {g : ℝ} {E : BlockMat d}
    {Ψ : ℝ → ℝ} {K : ℝ} {S : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S) :
    Integrable S P := by
  have hK1 : (1 : ℝ) ≤ K := le_of_lt hdag.one_lt_growthWitness
  have hK2 : (2 : ℝ) ≤ max 2 K := le_max_left _ _
  have hgrow : IndependentSums.HasPsiGrowth Ψ (max 2 K) :=
    hasPsiGrowth_mono hdag.gauge_admissible hK1 (le_max_right _ _) hdag.gauge_growth
  have hD := IndependentSums.admissiblePsi_hasPsiAbstractDoubling_two hK2 hgrow
    hdag.gauge_admissible
  have hbigO : IndependentSums.IsBigOWith P Ψ S 1 := by
    intro t ht
    rw [one_mul]
    exact hdag.source_tail t (lt_of_lt_of_le zero_lt_one ht)
  have htail : Integrable (IndependentSums.upperTailIndicator S (1 * 1)) P :=
    IndependentSums.integrable_upperTailIndicator_of_isBigOWith hD
      hdag.gauge_admissible (by norm_num) zero_lt_one le_rfl hbigO
      hdag.source_measurable
  rw [one_mul] at htail
  refine Integrable.mono' (htail.add (integrable_const (1 : ℝ)))
    hdag.source_measurable.aestronglyMeasurable (ae_of_all _ fun a => ?_)
  have hSa := hdag.source_nonneg a
  simp only [Pi.add_apply, Real.norm_eq_abs, abs_of_nonneg hSa]
  by_cases hc : 1 < S a
  · have hind : IndependentSums.upperTailIndicator S 1 a = S a :=
      Set.indicator_of_mem (by exact hc) _
    rw [hind]
    linarith only []
  · have hind : IndependentSums.upperTailIndicator S 1 a = 0 :=
      Set.indicator_of_notMem (by exact hc) _
    rw [hind]
    linarith only [not_lt.1 hc]

end

end HighContrast
end HCPolySupport
