/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import Mathlib.Topology.Semicontinuity.Basic
public import Mathlib.Topology.Algebra.Order.Field

/-!
# Upper semicontinuity under positive continuous weights

A real upper semicontinuous function times a positive continuous function is
upper semicontinuous on an arbitrary topological source. This shared topological
tool supports concave density tilts and Gaussian posterior densities in the BKL
arXiv:2610.05474v1 regular approximation and localization construction.
-/

@[expose] public section
open Filter Topology
namespace FunctionalInequalities.Analysis

/-- Multiplication by a positive continuous weight preserves upper semicontinuity. -/
theorem upperSemicontinuous_mul_of_continuous_pos {E : Type*} [TopologicalSpace E] {f g : E → ℝ}
    (hf : UpperSemicontinuous f) (hg : Continuous g) (hgpos : ∀ y, 0 < g y) :
    UpperSemicontinuous (fun y => f y * g y) := by
  intro y c hc
  obtain ⟨a, ha, hac⟩ := exists_between hc
  have hfu : f y < a / g y := (lt_div_iff₀ (hgpos y)).2 ha
  have htc : a / g y * g y < c := by
    simpa only [div_mul_cancel₀ a (hgpos y).ne'] using hac
  have hgc : ∀ᶠ z in 𝓝 y, a / g y * g z < c :=
    (hg.const_mul (a / g y)).continuousAt.eventually (isOpen_Iio.mem_nhds htc)
  filter_upwards [hf y _ hfu, hgc] with z hz hgz
  exact (mul_le_mul_of_nonneg_right hz.le (hgpos z).le).trans_lt hgz


end FunctionalInequalities.Analysis
