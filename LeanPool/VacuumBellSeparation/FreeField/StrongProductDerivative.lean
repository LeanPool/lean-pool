/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Tactic.TypeStar
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Differentiating a strongly varying operator on a differentiable vector

Only the fixed-vector derivative and continuity needed by the product rule
are assumed. A local uniform operator bound controls the moving-vector
residual. Operator-norm differentiability is not required.
-/

@[expose] public section

namespace VacuumBellSeparation

open Filter Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem hasDerivAt_strong_operator_apply (A : ℝ → E →L[ℝ] F)
    {u : ℝ → E} {u' : E} {t : ℝ} {d : F} {C : ℝ}
    (hu : HasDerivAt u u' t)
    (hfixed : HasDerivAt (fun s => A s (u t)) d t)
    (hcont : ContinuousAt (fun s => A s u') t)
    (hbound : ∀ᶠ s in 𝓝 t, ‖A s‖ ≤ C) :
    HasDerivAt (fun s => A s (u s)) (A t u' + d) t := by
  let l := 𝓝[≠] t
  have hres : Tendsto (fun s => slope u t s - u') l (𝓝 0) := by
    simpa only [sub_self] using hu.tendsto_slope.sub (tendsto_const_nhds (x := u'))
  have hterm₁ : Tendsto (fun s => A s (slope u t s - u')) l (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
      ((hbound.filter_mono nhdsWithin_le_nhds).mono fun s hs =>
        (A s).le_opNorm (slope u t s - u') |>.trans
          (mul_le_mul_of_nonneg_right hs (norm_nonneg _)))
    simpa only [norm_zero, mul_zero] using hres.norm.const_mul C
  have hterm₂ : Tendsto (fun s => A s u') l (𝓝 (A t u')) :=
    hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hterm₃ : Tendsto (fun s => slope (fun r => A r (u t)) t s) l (𝓝 d) :=
    hfixed.tendsto_slope
  rw [hasDerivAt_iff_tendsto_slope]
  have ht := (hterm₁.add hterm₂).add hterm₃
  have heq (s : ℝ) : A s (slope u t s - u') + A s u' +
      slope (fun r => A r (u t)) t s = slope (fun r => A r (u r)) t s := by
    simp only [slope_def_module, map_sub, map_smul, smul_sub]
    abel
  simpa only [zero_add] using ht.congr' (Eventually.of_forall heq)

end VacuumBellSeparation
