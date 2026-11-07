/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
module

import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import LeanPool.Copula.Classical.Approximation
import LeanPool.Copula.Classical.Regularity
public import LeanPool.Copula.Classical.Basic
import LeanPool.Copula.CDF.Extensionality

/-! # The classical characterization of finite-dimensional copulas

Atomic approximations have uniformly convergent CDFs. Compactness of probability
measures on the unit cube gives a weakly convergent subsequence. The portmanteau
inequalities and the derived Lipschitz estimate identify its CDF, including on
the boundary. No continuity or countable-additivity assumption is added.
-/

public section

open MeasureTheory Set Filter
open scoped unitInterval Topology ENNReal BigOperators

namespace ProbabilityTheory.Copula

variable {d : ℕ} {F : (Fin d → I) → ℝ}

private theorem IsClassical.identify_weak_limit (hF : IsClassical F)
    (μs : ℕ → ProbabilityMeasure (Fin d → I)) (μ : ProbabilityMeasure (Fin d → I))
    (hweak : Tendsto μs atTop (𝓝 μ))
    (hcdf : ∀ u, Tendsto (fun n => (μs n).toMeasure.real (Iic u)) atTop (𝓝 (F u)))
    (u : Fin d → I) : μ.toMeasure.real (Iic u) = F u := by
  have hnonneg (v : Fin d → I) : 0 ≤ F v := by
    rw [← hF.rectangleIncrement_zero_lower]
    exact hF.increasing _ _ (fun i => (v i).property.1)
  have hcdf' (v : Fin d → I) : Tendsto (fun n => (μs n).toMeasure (Iic v)) atTop
      (𝓝 (ENNReal.ofReal (F v))) := by
    have h := ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hcdf v)
    simpa only [Function.comp_def, Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _)] using h
  apply le_antisymm
  · apply le_of_forall_pos_le_add
    intro ε hε
    let δ : ℝ := ε / ((d : ℝ) + 1)
    have hδ : 0 < δ := by dsimp [δ]; positivity
    let v : Fin d → I := fun i => ⟨min ((u i : ℝ) + δ) 1,
      le_min (by linarith [(u i).property.1]) zero_le_one, min_le_right _ _⟩
    let O : Set (Fin d → I) := {x | ∀ i, (x i : ℝ) < (u i : ℝ) + δ}
    have hO : IsOpen O := by
      dsimp only [O]
      rw [ofPred_forall]
      exact isOpen_iInter_of_finite (fun i => isOpen_lt (by fun_prop) continuous_const)
    have huO : Iic u ⊆ O := by
      intro x hx i
      exact lt_of_le_of_lt (hx i) (lt_add_of_pos_right _ hδ)
    have hOv : O ⊆ Iic v := by
      intro x hx i
      exact le_min (hx i).le (x i).property.2
    have hliminf : atTop.liminf (fun n => (μs n).toMeasure O) ≤ ENNReal.ofReal (F v) := by
      rw [← (hcdf' v).liminf_eq]
      exact liminf_le_liminf (Eventually.of_forall (fun n => measure_mono hOv))
    have hm : μ.toMeasure (Iic u) ≤ ENNReal.ofReal (F v) :=
      (measure_mono huO).trans
        ((ProbabilityMeasure.le_liminf_measure_open_of_tendsto hweak hO).trans hliminf)
    have hmr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hm
    rw [ENNReal.toReal_ofReal (hnonneg v)] at hmr
    have huv : u ≤ v := by
      intro i
      exact le_min (le_add_of_nonneg_right hδ.le) (u i).property.2
    have hdiff := hF.sub_le_sum_of_le u v huv
    have hsum : ∑ i, ((v i : ℝ) - (u i : ℝ)) ≤ (d : ℝ) * δ := by
      calc
        _ ≤ ∑ _ : Fin d, δ := Finset.sum_le_sum (fun i _ => by
          dsimp [v]
          have := min_le_left ((u i : ℝ) + δ) 1
          linarith)
        _ = _ := by simp
    have hδε : (d : ℝ) * δ ≤ ε := by
      have he : ((d : ℝ) + 1) * δ = ε := by dsimp [δ]; field_simp
      nlinarith
    change μ.toMeasure.real (Iic u) ≤ F v at hmr
    linarith
  · have h := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hweak
      (isClosed_Iic : IsClosed (Iic u))
    rw [(hcdf' u).limsup_eq] at h
    have hh := ENNReal.toReal_mono (measure_ne_top μ.toMeasure _) h
    change F u ≤ (μ.toMeasure (Iic u)).toReal
    simpa only [ENNReal.toReal_ofReal (hnonneg u)] using hh

/-- A classical copula function is the CDF of a probability measure on the cube. -/
theorem IsClassical.exists_probabilityMeasure (hF : IsClassical F) :
    ∃ μ : ProbabilityMeasure (Fin d → I), ∀ u, μ.toMeasure.real (Iic u) = F u := by
  obtain ⟨μ, φ, hφ, hμ⟩ := CompactSpace.tendsto_subseq (ClassicalConstruction.approximation hF)
  refine ⟨μ, hF.identify_weak_limit _ μ hμ ?_⟩
  intro u
  exact (ClassicalConstruction.approximation_cdf_tendsto hF u).comp hφ.tendsto_atTop

/-- The classical characterization, valid in every finite dimension including zero. -/
theorem IsClassical.existsUnique (hF : IsClassical F) : ∃! C : Copula d, C.cdf = F := by
  obtain ⟨μ, hμ⟩ := hF.exists_probabilityMeasure
  refine ⟨hF.ofMeasure μ hμ, hF.cdf_ofMeasure μ hμ, ?_⟩
  intro C hC
  exact unique_representation F hC (hF.cdf_ofMeasure μ hμ)

/-- Build the unique copula represented by classical boundary and rectangle data. -/
@[expose]
noncomputable def ofClassical (F : (Fin d → I) → ℝ) (hF : IsClassical F) : Copula d :=
  hF.existsUnique.choose

@[simp]
theorem cdf_ofClassical (F : (Fin d → I) → ℝ) (hF : IsClassical F) :
    (ofClassical F hF).cdf = F := hF.existsUnique.choose_spec.1

@[simp]
theorem ofClassical_cdf (C : Copula d) : ofClassical C.cdf C.isClassical_cdf = C := by
  apply cdf_injective
  exact cdf_ofClassical _ _

theorem isClassical_iff_existsUnique : IsClassical F ↔ ∃! C : Copula d, C.cdf = F := by
  refine ⟨IsClassical.existsUnique, ?_⟩
  rintro ⟨C, rfl, _⟩
  exact C.isClassical_cdf

end ProbabilityTheory.Copula
