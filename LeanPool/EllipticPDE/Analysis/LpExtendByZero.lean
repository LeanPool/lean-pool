/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator


/-!
# Extension by zero as an `Lp` isometry

For a measurable set `s`, extension by zero identifies `Lᵖ` on the restricted measure
`μ.restrict s` with the subspace of `Lᵖ μ` of functions supported in `s`. The map
`f ↦ s.indicator f` preserves the `Lᵖ` norm, because the seminorm on `μ.restrict s`
equals the seminorm of the indicator on `μ`. We package it as a linear isometry
`MeasureTheory.lpExtendByZero`.

This is the bridge that lets a compact-embedding argument on a bounded domain `Ω` be run in
the ambient space `Lᵖ(ℝⁿ)`: a class on `L²(Ω) = Lp ℝ 2 (volume.restrict Ω)` is sent to its
extension by zero in `L²(ℝⁿ) = Lp ℝ 2 volume`, where the Fréchet-Kolmogorov criterion applies.

## Main definitions

* `MeasureTheory.lpExtendByZero`: extension by zero `Lp ℝ p (μ.restrict s) →ₗᵢ[ℝ] Lp ℝ p μ`.
-/

@[expose] public section

open Set Filter
open scoped ENNReal

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {p : ℝ≥0∞} {s : Set α}

/-- The indicator of a class on the restricted measure is `p`-integrable for the full measure. -/
theorem memLp_indicator_extend (hs : MeasurableSet s) (f : Lp ℝ p (μ.restrict s)) :
    MemLp (s.indicator (f : α → ℝ)) p μ := by
  rw [memLp_iff, eLpNorm_indicator_eq_eLpNorm_restrict hs]
  exact Lp.memLp f

variable [Fact (1 ≤ p)]

variable (μ p s) in
/-- **Extension by zero** as a linear isometry `Lp ℝ p (μ.restrict s) →ₗᵢ[ℝ] Lp ℝ p μ`. A class
on the restricted measure is sent to the `Lp` class of its extension by zero, with the `Lp` norm
preserved. -/
noncomputable def lpExtendByZero (hs : MeasurableSet s) :
    Lp ℝ p (μ.restrict s) →ₗᵢ[ℝ] Lp ℝ p μ where
  toFun f := (memLp_indicator_extend hs f).toLp (s.indicator (f : α → ℝ))
  map_add' f g := by
    rw [Lp.ext_iff]
    have hr : ∀ᵐ x ∂(μ.restrict s), (⇑(f + g) : α → ℝ) x = (⇑f + ⇑g) x := Lp.coeFn_add f g
    have h5 : ∀ᵐ x ∂μ, x ∈ s → (⇑(f + g) : α → ℝ) x = (⇑f + ⇑g) x := (ae_restrict_iff' hs).mp hr
    filter_upwards [MemLp.coeFn_toLp (memLp_indicator_extend hs (f + g)),
      Lp.coeFn_add ((memLp_indicator_extend hs f).toLp (s.indicator (f : α → ℝ)))
        ((memLp_indicator_extend hs g).toLp (s.indicator (g : α → ℝ))),
      MemLp.coeFn_toLp (memLp_indicator_extend hs f),
      MemLp.coeFn_toLp (memLp_indicator_extend hs g), h5] with x h1 h2 h3 h4 h5x
    rw [h1, h2, Pi.add_apply, h3, h4]
    by_cases hxs : x ∈ s
    · rw [Set.indicator_of_mem hxs, Set.indicator_of_mem hxs, Set.indicator_of_mem hxs, h5x hxs,
        Pi.add_apply]
    · rw [Set.indicator_of_notMem hxs, Set.indicator_of_notMem hxs, Set.indicator_of_notMem hxs,
        add_zero]
  map_smul' c f := by
    rw [Lp.ext_iff]
    have hr : ∀ᵐ x ∂(μ.restrict s), (⇑(c • f) : α → ℝ) x = (c • ⇑f) x := Lp.coeFn_smul c f
    have h4 : ∀ᵐ x ∂μ, x ∈ s → (⇑(c • f) : α → ℝ) x = (c • ⇑f) x := (ae_restrict_iff' hs).mp hr
    filter_upwards [MemLp.coeFn_toLp (memLp_indicator_extend hs (c • f)),
      Lp.coeFn_smul c ((memLp_indicator_extend hs f).toLp (s.indicator (f : α → ℝ))),
      MemLp.coeFn_toLp (memLp_indicator_extend hs f), h4] with x h1 h2 h3 h4x
    rw [RingHom.id_apply, h1, h2, Pi.smul_apply, h3]
    by_cases hxs : x ∈ s
    · rw [Set.indicator_of_mem hxs, Set.indicator_of_mem hxs, h4x hxs, Pi.smul_apply]
    · rw [Set.indicator_of_notMem hxs, Set.indicator_of_notMem hxs, smul_zero]
  norm_map' f := by
    change ‖(memLp_indicator_extend hs f).toLp (s.indicator (f : α → ℝ))‖ = ‖f‖
    rw [Lp.norm_toLp, eLpNorm_indicator_eq_eLpNorm_restrict hs, Lp.norm_def]

/-- The extension by zero is represented almost everywhere by the indicator of `s`. -/
@[simp] theorem coeFn_lpExtendByZero (hs : MeasurableSet s) (f : Lp ℝ p (μ.restrict s)) :
    (lpExtendByZero μ p s hs f : α → ℝ) =ᵐ[μ] s.indicator (f : α → ℝ) :=
  MemLp.coeFn_toLp (memLp_indicator_extend hs f)

/-- The extension by zero is almost everywhere zero off `s`. -/
theorem lpExtendByZero_ae_eq_zero (hs : MeasurableSet s) (f : Lp ℝ p (μ.restrict s)) :
    ∀ᵐ x ∂μ, x ∉ s → (lpExtendByZero μ p s hs f : α → ℝ) x = 0 := by
  filter_upwards [coeFn_lpExtendByZero hs f] with x hx hxs
  rw [hx, Set.indicator_of_notMem hxs]

end MeasureTheory
