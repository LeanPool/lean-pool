/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Probability.BrunnMinkowski
public import LeanPool.KLS.FunctionalInequalities.Analysis.Hausdorff.Measure

/-!
# The isodiametric inequality

Bounded sets have volume at most that of a ball of the same diameter. No measurability
assumption or positive-dimensional assumption is added.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff Pointwise

namespace FunctionalInequalities

universe u

namespace Analysis

section Isodiametric

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- **Isodiametric inequality**: a bounded set of diameter `d` has Lebesgue measure at most
`ω_n (d / 2)^n`, the volume of a ball of diameter `d`.  Stated for bounded sets with `Metric.diam`
because `Metric.diam` of an unbounded set is `0`; for unbounded sets the right-hand side with
`EMetric.diam` would be `⊤` in positive dimension and the statement is vacuous.  No measurability
is assumed: `volume` is the outer measure, and `closure S` has the same diameter. -/
theorem isodiametric (S : Set V) (hS : Bornology.IsBounded S) :
    volume S ≤
      ENNReal.ofReal
        (KLS.unitBallVolume (Module.finrank ℝ V) * (Metric.diam S / 2) ^ Module.finrank ℝ V) := by
  rcases Set.eq_empty_or_nonempty S with rfl | hSne
  · simp
  have hdiam0 : (0 : ℝ) ≤ Metric.diam S := Metric.diam_nonneg
  have hω0 : (0 : ℝ) ≤ KLS.unitBallVolume (Module.finrank ℝ V) := by
    unfold KLS.unitBallVolume;
    positivity
  rcases subsingleton_or_nontrivial V with hsub | hnt
  · have hn0 : Module.finrank ℝ V = 0 := Module.finrank_zero_of_subsingleton
    rw [hn0, pow_zero, mul_one, show KLS.unitBallVolume 0 = 1 by simp [KLS.unitBallVolume],
      ENNReal.ofReal_one]
    refine (measure_mono (Set.subset_univ _)).trans ?_
    have hb := (stdOrthonormalBasis ℝ V).toBasis.addHaar_self
    have hne : (parallelepiped ((stdOrthonormalBasis ℝ V).toBasis)).Nonempty :=
      ⟨0, 0, by simp, by simp⟩
    rw [Subsingleton.eq_univ_of_nonempty hne] at hb
    exact
      hb.le
  -- the nondegenerate case
  set C := closure S with hC
  have hCc : IsCompact C := hS.isCompact_closure
  have hCne : C.Nonempty := hSne.closure
  have hCb : Bornology.IsBounded C := hCc.isBounded
  have hCdiam : Metric.diam C = Metric.diam S := Metric.diam_closure S
  have hCtop : volume C ≠ ⊤ := hCc.measure_lt_top.ne
  by_cases hC0 : volume C = 0
  · exact le_trans ((measure_mono subset_closure).trans hC0.le) (by simp)
  set T : Set V := (-1 : ℝ) • C with hT
  have hTc : IsCompact T := by
    rw [hT, ← Set.image_smul];
    exact hCc.image (continuous_const_smul _)
  have hTne : T.Nonempty := hCne.image _
  have hTvol : volume T = volume C := by
    rw [hT, Measure.addHaar_smul]
    simp
  have hsub :
    {z : V | ∃ x ∈ C, ∃ y ∈ T, z = (1 / 2 : ℝ) • x + (1 - 1 / 2 : ℝ) • y} ⊆
      Metric.closedBall (0 : V) (Metric.diam S / 2) := by
    rintro _ ⟨x, hx, -, ⟨y, hy, rfl⟩, rfl⟩
    have hxy : ‖x - y‖ ≤ Metric.diam S := by
      rw [← dist_eq_norm, ← hCdiam]
      exact Metric.dist_le_diam_of_mem hCb hx hy
    simp only [Metric.mem_closedBall, dist_zero_right]
    have : (1 / 2 : ℝ) • x + (1 - 1 / 2 : ℝ) • ((-1 : ℝ) • y) = (1 / 2 : ℝ) • (x - y) := by
      rw [smul_smul]; module
    rw [this, norm_smul]
    simp only [one_div, norm_inv, Real.norm_ofNat]
    rw [inv_mul_eq_div, div_le_div_iff_of_pos_right (by norm_num)]
    exact hxy
  have hBM :=
    volume_rpow_mul_le_volume_combination hCc.measurableSet hCne hTc.measurableSet hTne
      (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  rw [hTvol] at hBM
  have hhalf : volume C ^ (1 / 2 : ℝ) * volume C ^ (1 - 1 / 2 : ℝ) = volume C := by
    rw [←
      ENNReal.rpow_add_of_nonneg (x := volume C) (1 / 2) (1 - 1 / 2) (by norm_num)
        (by norm_num)]
    simp
  rw [hhalf] at hBM
  calc
    volume S ≤ volume C := measure_mono subset_closure
    _ ≤ volume (Metric.closedBall (0 : V) (Metric.diam S / 2)) :=
      le_trans hBM (measure_mono hsub)
    _ =
        ENNReal.ofReal
          (KLS.unitBallVolume (Module.finrank ℝ V) *
            (Metric.diam S / 2) ^ Module.finrank ℝ V) := by
      rw [InnerProductSpace.volume_closedBall, ← ENNReal.ofReal_pow (by positivity), ←
        ENNReal.ofReal_mul (by positivity), KLS.unitBallVolume]
      ring_nf

end Isodiametric

end Analysis

end FunctionalInequalities
