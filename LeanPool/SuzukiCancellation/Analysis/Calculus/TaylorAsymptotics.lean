/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/

/- Modified for Lean Pool: updated module paths. -/

module

public import LeanPool.SuzukiCancellation.Analysis.Calculus.Taylor

/-!
# Leading Taylor terms and sharp norm limits

Vanishing derivatives determine the leading Taylor term of a vector-valued
curve. Its normalized vector converges on the punctured neighborhood, and its
normalized norm converges from the right.

## Main results

* `isLittleO_sub_pow_smul_of_iteratedDeriv`: the leading Taylor term.
* `tendsto_inv_pow_smul_of_isLittleO`: the normalized vector limit.
* `tendsto_inv_pow_mul_norm_of_isLittleO`: the normalized norm limit from the right.
-/

@[expose] public noncomputable section

open Asymptotics Filter
open scoped Topology

namespace TrotterError

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A curve whose lower derivatives vanish has its prescribed leading Taylor
term, with a little-o remainder of the same order. -/
theorem isLittleO_sub_pow_smul_of_iteratedDeriv (F : ℝ → E) (n : ℕ) (L : E)
    (hF : ContDiff ℝ n F) (hzero : ∀ k < n, iteratedDeriv k F 0 = 0)
    (hlead : iteratedDeriv n F 0 = (Nat.factorial n : ℝ) • L) :
    (fun t ↦ F t - t ^ n • L) =o[𝓝 (0 : ℝ)] (fun t ↦ t ^ n) := by
  have htaylor := taylor_isLittleO_univ (x₀ := 0) hF
  refine htaylor.congr_left (fun t ↦ ?_) |>.congr_right (fun t ↦ by simp)
  rw [taylorWithinEval_eq_smul_of_iteratedDeriv_eq_zero_below F n hzero, hlead]
  simp [smul_smul, show (Nat.factorial n : ℝ) ≠ 0 by positivity]

/-- A leading power asymptotic gives the normalized vector limit on the
punctured neighborhood, without requiring a nonzero leading coefficient. -/
theorem tendsto_inv_pow_smul_of_isLittleO {F : ℝ → E} {n : ℕ} {L : E}
    (hF : (fun t ↦ F t - t ^ n • L) =o[𝓝 (0 : ℝ)] (fun t ↦ t ^ n)) :
    Tendsto (fun t ↦ (t ^ n)⁻¹ • F t) (𝓝[≠] (0 : ℝ)) (𝓝 L) := by
  have hrem := hF.tendsto_inv_smul_nhds_zero.mono_left
    (show 𝓝[≠] (0 : ℝ) ≤ 𝓝 (0 : ℝ) from nhdsWithin_le_nhds)
  have hlimit := hrem.add_const L
  simp only [zero_add] at hlimit
  apply hlimit.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : t ≠ 0 := ht
  simp [smul_sub, smul_smul, pow_ne_zero n ht0]

/-- The norm of a curve with a leading power term has the sharp coefficient as
its normalized limit from positive times. -/
theorem tendsto_inv_pow_mul_norm_of_isLittleO {F : ℝ → E} {n : ℕ} {L : E}
    (hF : (fun t ↦ F t - t ^ n • L) =o[𝓝 (0 : ℝ)] (fun t ↦ t ^ n)) :
    Tendsto (fun t ↦ (t ^ n)⁻¹ * ‖F t‖) (𝓝[>] (0 : ℝ)) (𝓝 ‖L‖) := by
  have hfilter : 𝓝[>] (0 : ℝ) ≤ 𝓝[≠] (0 : ℝ) :=
    nhdsWithin_mono _ (fun _ hx ↦ ne_of_gt hx)
  have hlimit := (tendsto_inv_pow_smul_of_isLittleO hF).norm.mono_left hfilter
  apply hlimit.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (pow_pos ht n))]

end TrotterError
