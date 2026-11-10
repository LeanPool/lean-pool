/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.EhrhardGaussian.Ehrhard.CompactSetInequality
public import Mathlib.Analysis.Convex.Measure
import LeanPool.EhrhardGaussian.Gaussian.Poincare
import Mathlib.MeasureTheory.Measure.Regular

/-! # Inner approximation and the standard Gaussian set inequality -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open EhrhardGaussian.Gaussian (standardGaussianMeasure)
open scoped Topology Pointwise

namespace EhrhardGaussian.Ehrhard

/-- Finite dimensional standard Gaussian measure is absolutely continuous with respect to volume. -/
theorem standardGaussian_absolutelyContinuous (n : ℕ) :
    standardGaussianMeasure n ≪ (volume : Measure (Fin n → ℝ)) := by
  rw [EhrhardGaussian.Gaussian.standardGaussianMeasure_eq_withDensity]
  exact withDensity_absolutelyContinuous _ _

/-- A set measurable in the Gaussian completion contains a nonempty compact subset with mass
exceeding any smaller nonnegative threshold. -/
theorem exists_compact_gaussian_mass {n : ℕ} {A : Set (Fin n → ℝ)}
    (hA : NullMeasurableSet A (standardGaussianMeasure n)) {r : ℝ} (hr : 0 ≤ r)
    (h : r < (standardGaussianMeasure n A).toReal) :
    ∃ K ⊆ A, IsCompact K ∧ K.Nonempty ∧ r < (standardGaussianMeasure n K).toReal := by
  obtain ⟨S, hSA, hS, heq⟩ := hA.exists_measurable_subset_ae_eq
  have hmass : standardGaussianMeasure n S = standardGaussianMeasure n A := measure_congr heq
  have hlt : ENNReal.ofReal r < standardGaussianMeasure n S := by
    rw [hmass]
    exact (ENNReal.ofReal_lt_iff_lt_toReal hr (measure_ne_top _ _)).2 h
  obtain ⟨K, hKS, hK, hrK⟩ := hS.exists_lt_isCompact hlt
  have hrK' := (ENNReal.ofReal_lt_iff_lt_toReal hr (measure_ne_top _ _)).1 hrK
  refine ⟨K, hKS.trans hSA, hK, ?_, hrK'⟩
  by_contra hn
  rw [Set.not_nonempty_iff_eq_empty.mp hn, measure_empty, ENNReal.toReal_zero] at hrK'
  exact (not_lt_of_ge hr) hrK'

/-- Strict Gaussian mass lower bounds imply Ehrhard’s inequality for sets measurable in the Gaussian
completion. -/
theorem standard_set_ehrhard_strict {n : ℕ} {A B : Set (Fin n → ℝ)}
    (hA : NullMeasurableSet A (standardGaussianMeasure n))
    (hB : NullMeasurableSet B (standardGaussianMeasure n))
    {p q : ℝ} (hp : 0 < p) (hq : 0 < q) (hsum : p + q = 1) {a b : ℝ}
    (ha : gaussianCDF a < (standardGaussianMeasure n A).toReal)
    (hb : gaussianCDF b < (standardGaussianMeasure n B).toReal) :
    gaussianCDF (p * a + q * b) ≤ (standardGaussianMeasure n (p • A + q • B)).toReal := by
  obtain ⟨K, hKA, hK, hKne, haK⟩ := exists_compact_gaussian_mass hA (gaussianCDF_pos a).le ha
  obtain ⟨L, hLB, hL, hLne, hbL⟩ := exists_compact_gaussian_mass hB (gaussianCDF_pos b).le hb
  exact (compact_set_ehrhard hK hL hKne hLne hp hq hsum haK.le hbL.le).trans
    (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono
      (Set.add_subset_add (Set.smul_set_mono hKA) (Set.smul_set_mono hLB))))

/-- Gaussian mass lower bounds imply Ehrhard’s inequality for sets measurable in the Gaussian
completion. -/
theorem standard_set_ehrhard {n : ℕ} {A B : Set (Fin n → ℝ)}
    (hA : NullMeasurableSet A (standardGaussianMeasure n))
    (hB : NullMeasurableSet B (standardGaussianMeasure n))
    {p q : ℝ} (hp : 0 < p) (hq : 0 < q) (hsum : p + q = 1) {a b : ℝ}
    (ha : gaussianCDF a ≤ (standardGaussianMeasure n A).toReal)
    (hb : gaussianCDF b ≤ (standardGaussianMeasure n B).toReal) :
    gaussianCDF (p * a + q * b) ≤ (standardGaussianMeasure n (p • A + q • B)).toReal := by
  let ε := fun j : ℕ => 1 / ((j : ℝ) + 1)
  have hε (j) : 0 < ε j := by dsimp only [ε]; positivity
  have hεlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hcomp (j) := standard_set_ehrhard_strict hA hB hp hq hsum
    ((strictMono_gaussianCDF (sub_lt_self a (hε j))).trans_le ha)
    ((strictMono_gaussianCDF (sub_lt_self b (hε j))).trans_le hb)
  have halim := (tendsto_const_nhds : Tendsto (fun _ : ℕ => a) atTop (𝓝 a)).sub hεlim
  have hblim := (tendsto_const_nhds : Tendsto (fun _ : ℕ => b) atTop (𝓝 b)).sub hεlim
  have hlim := continuous_gaussianCDF.continuousAt.tendsto.comp ((halim.const_mul p).add
    (hblim.const_mul q))
  simpa only [sub_zero] using le_of_tendsto hlim (Eventually.of_forall hcomp)

/-- Ehrhard's inequality holds for convex sets under standard Gaussian measure. -/
theorem standard_convex_set_ehrhard {n : ℕ} {A B : Set (Fin n → ℝ)}
    (hA : Convex ℝ A) (hB : Convex ℝ B)
    {p q : ℝ} (hp : 0 < p) (hq : 0 < q) (hsum : p + q = 1) {a b : ℝ}
    (ha : gaussianCDF a ≤ (standardGaussianMeasure n A).toReal)
    (hb : gaussianCDF b ≤ (standardGaussianMeasure n B).toReal) :
    gaussianCDF (p * a + q * b) ≤ (standardGaussianMeasure n (p • A + q • B)).toReal :=
  standard_set_ehrhard ((hA.nullMeasurableSet volume).mono_ac (standardGaussian_absolutelyContinuous
    n))
    ((hB.nullMeasurableSet volume).mono_ac (standardGaussian_absolutelyContinuous n)) hp hq hsum ha
      hb

end EhrhardGaussian.Ehrhard

end
