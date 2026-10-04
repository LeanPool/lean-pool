/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
module

public import LeanPool.EllipticPDE.Extension.Translate
public import LeanPool.EllipticPDE.Embedding.H01Sobolev
public import Mathlib.MeasureTheory.Function.ContinuousMapDense


/-!
# Continuity of translation in `Lᵖ`

An `Lᵖ` function is close in `Lᵖ` to its own translates by small vectors. This is the statement
the global approximation theorem shifts on: a function is moved into the domain by a small
translation, and the shift has to be small in the norm the approximation is measured in.

Mathlib has the two halves and not the statement. Translation is measure preserving, so it is an
`Lᵖ` isometry, and the continuous compactly supported functions are dense in `Lᵖ`
(`MeasureTheory.MemLp.exists_hasCompactSupport_eLpNorm_sub_le`). Between them the usual
three-term argument runs: approximate, translate the approximant, and pay twice for the
approximation.

For a continuous compactly supported `g` the translate estimate is uniform continuity together
with one compact set containing the support of every difference `g(· + h) - g` with `‖h‖ ≤ 1`, so
the sup bound converts to an `Lᵖ` bound against the measure of that set.

## Main declarations

* `EllipticPdes.Analysis.tendsto_eLpNorm_translate_sub`: the `Lᵖ` distance to a translate tends
  to zero with the translation.

## References

L. C. Evans, *Partial Differential Equations* (2nd ed.), §5.3.3, Theorem 3; H. Brezis,
*Functional Analysis, Sobolev Spaces and Partial Differential Equations*, Lemma 4.3.
-/

@[expose] public section

open MeasureTheory Metric Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

namespace EllipticPdes.Analysis

open EllipticPdes.Extension

variable {d : ℕ}

/-- A translate of an `Lᵖ` function is an `Lᵖ` function, translation being measure
preserving. -/
lemma memLp_comp_translate {p : ℝ≥0∞} {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hf : MemLp f p volume) (h : EuclideanSpace ℝ (Fin d)) :
    MemLp (fun y => f (y + h)) p volume := by
  rw [memLp_iff, eLpNorm_comp_translate hf.aestronglyMeasurable h p]
  exact hf.eLpNorm_lt_top

/-- **Compactly supported case.** For a continuous `g` with compact support, the `Lᵖ`
distance to its translates tends to zero: uniform continuity bounds the difference uniformly,
and every difference with `‖h‖ ≤ 1` is supported in one compact set. -/
theorem tendsto_eLpNorm_translate_sub_of_hasCompactSupport {p : ℝ≥0∞}
    {g : EuclideanSpace ℝ (Fin d) → ℝ} (hgc : Continuous g) (hgs : HasCompactSupport g) :
    Tendsto (fun h : EuclideanSpace ℝ (Fin d) =>
      eLpNorm (fun y => g (y + h) - g y) p volume) (𝓝 0) (𝓝 0) := by
  -- One compact set contains the support of every difference with `‖h‖ ≤ 1`.
  set K : Set (EuclideanSpace ℝ (Fin d)) := cthickening 1 (tsupport g) with hK
  have hKc : IsCompact K := hgs.cthickening
  have hKm : MeasurableSet K := hKc.isClosed.measurableSet
  have hKfin : volume K ≠ ⊤ := hKc.measure_lt_top.ne
  have hsupp : ∀ h : EuclideanSpace ℝ (Fin d), ‖h‖ ≤ 1 →
      tsupport (fun y => g (y + h) - g y) ⊆ K := by
    intro h hh
    refine closure_minimal (fun y hy => ?_) isClosed_cthickening
    by_cases hy0 : g y = 0 ∧ g (y + h) = 0
    · exact absurd (by simp [hy0.1, hy0.2] : (fun y => g (y + h) - g y) y = 0) hy
    · rcases not_and_or.mp hy0 with hne | hne
      · exact self_subset_cthickening _ (subset_closure hne)
      · have hmem : y + h ∈ tsupport g := subset_closure hne
        refine mem_cthickening_of_dist_le y (y + h) 1 _ hmem ?_
        rw [dist_eq_norm]
        simpa using hh
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  set C : ℝ≥0∞ := volume K ^ p.toReal⁻¹ with hC
  have hCtop : C ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by positivity) hKfin
  -- A positive real the constant multiplies into `ε`.
  obtain ⟨c, hc0, hcle⟩ : ∃ c : ℝ, 0 < c ∧ ENNReal.ofReal c ≤ ε / C := by
    rcases eq_or_ne (ε / C) ⊤ with htop | hne
    · exact ⟨1, one_pos, by rw [htop]; exact le_top⟩
    · have hpos : 0 < ε / C := ENNReal.div_pos hε.ne' hCtop
      exact ⟨(ε / C).toReal, ENNReal.toReal_pos hpos.ne' hne,
        le_of_eq (ENNReal.ofReal_toReal hne)⟩
  have hCc : C * ENNReal.ofReal c ≤ ε :=
    le_trans (mul_le_mul_right hcle C) ENNReal.mul_div_le
  -- Uniform continuity turns the target into a sup bound.
  obtain ⟨δ, hδ0, hδ⟩ := Metric.uniformContinuous_iff.mp
    (hgs.uniformContinuous_of_continuous hgc) c hc0
  filter_upwards [Metric.ball_mem_nhds (0 : EuclideanSpace ℝ (Fin d)) (lt_min hδ0 one_pos)]
    with h hh
  have hnorm : ‖h‖ < min δ 1 := by
    simpa [Metric.mem_ball, dist_zero_right] using hh
  have hh1 : ‖h‖ ≤ 1 := le_of_lt (lt_of_lt_of_le hnorm (min_le_right _ _))
  have hbound : ∀ y, ‖g (y + h) - g y‖ ≤ c := by
    intro y
    have hd : dist (y + h) y < δ := by
      rw [dist_eq_norm]
      simpa using lt_of_lt_of_le hnorm (min_le_left _ _)
    have := hδ hd
    rw [Real.dist_eq] at this
    simpa [Real.norm_eq_abs] using this.le
  calc eLpNorm (fun y => g (y + h) - g y) p volume
      = eLpNorm (fun y => g (y + h) - g y) p (volume.restrict K) :=
        (EllipticPdes.Embedding.eLpNorm_restrict_eq_of_tsupport_subset hKm
          (hsupp h hh1) p).symm
    _ ≤ (volume.restrict K) Set.univ ^ p.toReal⁻¹ * ENNReal.ofReal c :=
        eLpNorm_le_of_ae_bound
          (((hgc.comp (continuous_id.add continuous_const)).sub hgc).aestronglyMeasurable.restrict)
          (Filter.Eventually.of_forall hbound)
    _ = C * ENNReal.ofReal c := by rw [Measure.restrict_apply_univ]
    _ ≤ ε := hCc

/-- **Continuity of translation in `Lᵖ`.** The `Lᵖ` distance between an `Lᵖ` function and its
translate tends to zero with the translation.

The three-term argument: approximate `f` by a continuous compactly supported `g`, translate `g`,
and count the approximation twice, once on each side. Translation being an `Lᵖ` isometry is what
makes the two terms equal. -/
theorem tendsto_eLpNorm_translate_sub {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hptop : p ≠ ∞)
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : MemLp f p volume) :
    Tendsto (fun h : EuclideanSpace ℝ (Fin d) =>
      eLpNorm (fun y => f (y + h) - f y) p volume) (𝓝 0) (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hq0 : ε / 2 / 2 ≠ 0 := by
    refine ENNReal.div_ne_zero.mpr ⟨ENNReal.div_ne_zero.mpr ⟨hε.ne', by norm_num⟩, by norm_num⟩
  obtain ⟨g, hgs, hfg, hgc, hgm⟩ := hf.exists_hasCompactSupport_eLpNorm_sub_le hptop hq0
  -- The three pieces, and their measurability.
  have hfgm : AEStronglyMeasurable (fun y => f y - g y) volume := hf.aestronglyMeasurable.sub
      hgc.aestronglyMeasurable
  have hgfm : AEStronglyMeasurable (fun y => g y - f y) volume := hgc.aestronglyMeasurable.sub
      hf.aestronglyMeasurable
  have htrans : ∀ h : EuclideanSpace ℝ (Fin d),
      AEStronglyMeasurable (fun y => f (y + h) - g (y + h)) volume := fun h =>
    hfgm.comp_measurePreserving (measurePreserving_translate h)
  have hgt : ∀ h : EuclideanSpace ℝ (Fin d),
      AEStronglyMeasurable (fun y => g (y + h) - g y) volume := fun h =>
    ((hgc.aestronglyMeasurable.comp_measurePreserving
      (measurePreserving_translate h))).sub hgc.aestronglyMeasurable
  -- The translated approximation is as close as the approximation.
  have hfirst : ∀ h : EuclideanSpace ℝ (Fin d),
      eLpNorm (fun y => f (y + h) - g (y + h)) p volume ≤ ε / 2 / 2 := by
    intro h
    have := eLpNorm_comp_translate (f := fun y => f y - g y) hfgm h p
    refine le_trans (le_of_eq this) ?_
    refine le_trans (le_of_eq (eLpNorm_congr_ae ?_)) hfg
    exact Filter.EventuallyEq.of_eq (funext fun y => rfl)
  have hthird : eLpNorm (fun y => g y - f y) p volume ≤ ε / 2 / 2 := by
    refine le_trans (le_of_eq ?_) hfg
    rw [← eLpNorm_neg (f := fun y => g y - f y)]
    exact eLpNorm_congr_ae (Filter.EventuallyEq.of_eq (funext fun y => by simp))
  -- The middle piece is the compactly supported case.
  have hmid := (ENNReal.tendsto_nhds_zero.mp
    (tendsto_eLpNorm_translate_sub_of_hasCompactSupport (p := p) hgc hgs))
    (ε / 2) (ENNReal.div_pos hε.ne' (by norm_num))
  filter_upwards [hmid] with h hh
  have hsplit : (fun y => f (y + h) - f y)
      = ((fun y => f (y + h) - g (y + h)) + (fun y => g (y + h) - g y))
        + (fun y => g y - f y) := by
    funext y
    simp only [Pi.add_apply]
    ring
  calc eLpNorm (fun y => f (y + h) - f y) p volume
      = eLpNorm (((fun y => f (y + h) - g (y + h)) + (fun y => g (y + h) - g y))
          + (fun y => g y - f y)) p volume := by rw [hsplit]
    _ ≤ eLpNorm ((fun y => f (y + h) - g (y + h)) + (fun y => g (y + h) - g y)) p volume
          + eLpNorm (fun y => g y - f y) p volume :=
        eLpNorm_add_le hp1
    _ ≤ (eLpNorm (fun y => f (y + h) - g (y + h)) p volume
          + eLpNorm (fun y => g (y + h) - g y) p volume)
          + eLpNorm (fun y => g y - f y) p volume :=
        add_le_add (eLpNorm_add_le hp1) le_rfl
    _ ≤ (ε / 2 / 2 + ε / 2) + ε / 2 / 2 :=
        add_le_add (add_le_add (hfirst h) hh) hthird
    _ = ε := by
        rw [add_comm (ε / 2 / 2) (ε / 2), add_assoc, ENNReal.add_halves, ENNReal.add_halves]

end EllipticPdes.Analysis
