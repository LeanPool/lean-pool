/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortPhaseDerivatives

/-!
# Derivatives of the extended normal phase

On the active region, the smooth global phase extension has the same
derivatives as the normal Carleman phase.
-/

public section


open Filter
open scoped Topology

noncomputable section

namespace ESS

/-- The first height derivative of the smooth extension agrees with the
normal phase above height two. -/
theorem buShortFExt_deriv_height_eq
    {y s : ℝ} (hy : 2 < y) (hs : 1 / 2 ≤ s) :
    deriv (fun r : ℝ => buShortFExt r s) y =
      deriv (fun r : ℝ => buShortF r s) y := by
  have heq : (fun r : ℝ => buShortFExt r s) =ᶠ[𝓝 y]
      (fun r => buShortF r s) := by
    filter_upwards [Ioi_mem_nhds hy] with r hr
    exact buShortFExt_eq hr.le hs
  exact heq.deriv_eq

/-- The second height derivative of the smooth extension agrees with
that of the normal phase above height two. -/
theorem buShortFExt_deriv_height_twice_eq
    {y s : ℝ} (hy : 2 < y) (hs : 1 / 2 ≤ s) :
    deriv (fun r : ℝ => deriv (fun q : ℝ => buShortFExt q s) r) y =
      deriv (fun r : ℝ => deriv (fun q : ℝ => buShortF q s) r) y := by
  have heq : (fun r : ℝ => deriv (fun q : ℝ => buShortFExt q s) r) =ᶠ[𝓝 y]
      (fun r => deriv (fun q : ℝ => buShortF q s) r) := by
    filter_upwards [Ioi_mem_nhds hy] with r hr
    exact buShortFExt_deriv_height_eq hr hs
  exact heq.deriv_eq

/-- The time derivative of the smooth extension agrees with the normal
phase after time one half. -/
theorem buShortFExt_deriv_time_eq
    {y s : ℝ} (hy : 2 ≤ y) (hs : 1 / 2 < s) :
    deriv (fun t : ℝ => buShortFExt y t) s =
      deriv (fun t : ℝ => buShortF y t) s := by
  have heq : (fun t : ℝ => buShortFExt y t) =ᶠ[𝓝 s]
      (fun t => buShortF y t) := by
    filter_upwards [Ioi_mem_nhds hs] with t ht
    exact buShortFExt_eq hy ht.le
  exact heq.deriv_eq

/-- The first height derivative of the smooth phase has square-root
height growth on the active region. -/
theorem buShortFExt_deriv_height_bound
    {y s : ℝ} (hy : 2 < y) (hs : 1 / 2 ≤ s) (hs1 : s ≤ 1) :
    |deriv (fun r : ℝ => buShortFExt r s) y| ≤
      6 * y ^ (1 / 2 : ℝ) := by
  rw [buShortFExt_deriv_height_eq hy hs]
  exact buShortF_deriv_height_bound (by linarith only [hy]) hs hs1

/-- The second height derivative of the smooth phase decays as the
inverse square root of height. -/
theorem buShortFExt_deriv_height_twice_bound
    {y s : ℝ} (hy : 2 < y) (hs : 1 / 2 ≤ s) (hs1 : s ≤ 1) :
    |deriv (fun r : ℝ => deriv (fun q : ℝ => buShortFExt q s) r) y| ≤
      3 * y ^ (-(1 / 2 : ℝ)) := by
  rw [buShortFExt_deriv_height_twice_eq hy hs]
  exact buShortF_deriv_height_twice_bound (by linarith only [hy]) hs hs1

/-- The time derivative of the smooth phase has three-halves power
height growth on the active region. -/
theorem buShortFExt_deriv_time_bound
    {y s : ℝ} (hy : 2 ≤ y) (hs : 1 / 2 < s) (hs1 : s ≤ 1) :
    |deriv (fun t : ℝ => buShortFExt y t) s| ≤
      7 * y ^ (3 / 2 : ℝ) := by
  rw [buShortFExt_deriv_time_eq hy hs]
  exact buShortF_deriv_time_bound (by linarith only [hy]) hs.le hs1

end ESS
