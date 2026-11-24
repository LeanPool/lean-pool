/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import Mathlib.Analysis.Distribution.TestFunction

/-!
# Smooth multiplication by a cutoff

A function smooth on an open set can be multiplied by a smooth cutoff supported there.
-/

@[expose] public section

open Set Filter
open scoped Topology ContDiff

namespace SGPT.Foundations.Analysis.SmoothCutoff

/-- A function smooth on an open set becomes globally smooth after
multiplication by a smooth cutoff whose support lies in that set. -/
theorem contDiff_smul_of_tsupport_subset
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U : Set E} (hU : IsOpen U) {χ : E → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hsupp : tsupport χ ⊆ U) {f : E → F} (hf : ContDiffOn ℝ ∞ f U) :
    ContDiff ℝ ∞ (fun x ↦ χ x • f x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ U
  · exact hχ.contDiffAt.smul (hf.contDiffAt (hU.mem_nhds hx))
  · have hmem : (tsupport χ)ᶜ ∈ 𝓝 x :=
      (isClosed_tsupport χ).isOpen_compl.mem_nhds fun h ↦ hx (hsupp h)
    have hzero : (fun x ↦ χ x • f x) =ᶠ[𝓝 x] fun _ ↦ 0 := by
      filter_upwards [hmem] with y hy
      simp [image_eq_zero_of_notMem_tsupport hy]
    exact contDiffAt_const.congr_of_eventuallyEq hzero

end SGPT.Foundations.Analysis.SmoothCutoff
