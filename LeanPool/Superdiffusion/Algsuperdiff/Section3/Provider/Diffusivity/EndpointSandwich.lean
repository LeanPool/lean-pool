/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.FlowArithmetic
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Annealed.RunningDiffusivity.Characterization
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Disorder.Cstar
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# EndpointSandwich

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The endpoint sandwich for the running diffusivity

This module is deterministic arithmetic infrastructure.  It transports the
scalar squeeze `sq_sandwich_of_relative_error` to the running diffusivity
`Annealed.sigmaBar`: a relative-error estimate against
`√(ν² + c⋆ γ⁻¹ 3^{2γm})` with deviation coefficient at most `1/4` yields the
two-sided comparison with `max (c⋆ γ⁻¹ 3^{2γm}) (ν²)` in the constants `1/4`
and `4`.

The relative-error estimate is an explicit input binder: nothing here produces
it, and no recurrence, probability space, or analytic producer is referenced.
The only model facts used are the positivity of `ν`, `γ`, `c⋆` and of
`Annealed.sigmaBar` itself.

## Main statement

* `endpoint_sandwich_of_relative_error`.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity

noncomputable section

variable {d : ℕ}

/-- Pure-arithmetic step: with `a, b ≥ 0`, the sum `b + a` and `max a b` differ
by at most a factor `2`, so a factor-`2` squeeze against `b + a` becomes a
factor-`4` squeeze against `max a b`. -/
private theorem sandwich_max_of_sq_sandwich {x a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h1 : (b + a) / 2 ≤ x ^ 2) (h2 : x ^ 2 ≤ 2 * (b + a)) :
    (1 / 4 : ℝ) * max a b ≤ x ^ 2 ∧ x ^ 2 ≤ 4 * max a b := by
  have hmax_le : max a b ≤ b + a :=
    max_le (by linarith only [hb]) (by linarith only [ha])
  have hle_max : b + a ≤ 2 * max a b := by
    have h3 : a ≤ max a b := le_max_left a b
    have h4 : b ≤ max a b := le_max_right a b
    linarith only [h3, h4]
  exact ⟨by linarith only [h1, hmax_le, ha, hb],
    by linarith only [h2, hle_max]⟩

/-- **Endpoint sandwich from a relative-error flow estimate.**

If the running diffusivity at scale `m` deviates from
`√(ν² + c⋆ γ⁻¹ 3^{2γm})` by at most `θ · σ_m` with `0 ≤ θ ≤ 1/4`, then

  `¼ max (c⋆ γ⁻¹ 3^{2γm}) ν² ≤ σ_m² ≤ 4 max (c⋆ γ⁻¹ 3^{2γm}) ν²`.

The deviation hypothesis is an explicit input; no producer of it is asserted
here. -/
theorem endpoint_sandwich_of_relative_error {M : ABKModel d} {m : ℤ} {theta : ℝ}
    (htheta : 0 ≤ theta) (htheta' : theta ≤ 1 / 4)
    (hdev : |(Annealed.sigmaBar M m : ℝ) -
        Real.sqrt
          (M.nu ^ 2 +
            Disorder.cstar M * M.gamma⁻¹ * (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)))|
      ≤ theta * (Annealed.sigmaBar M m : ℝ)) :
    (1 / 4 : ℝ) *
        max (Disorder.cstar M * M.gamma⁻¹ * (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)))
          (M.nu ^ 2)
        ≤ (Annealed.sigmaBar M m : ℝ) ^ 2 ∧
      (Annealed.sigmaBar M m : ℝ) ^ 2
        ≤ 4 *
          max (Disorder.cstar M * M.gamma⁻¹ * (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)))
            (M.nu ^ 2) := by
  have hx : (0 : ℝ) < (Annealed.sigmaBar M m : ℝ) := (Annealed.sigmaBar M m).2
  have hnu : (0 : ℝ) < M.nu ^ 2 := pow_pos M.nu_pos 2
  have hgamma : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hcstar : 0 < Disorder.cstar M := (Disorder.cstar_characterization M).1
  have hgeom : (0 : ℝ) < (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have ha : (0 : ℝ) ≤
      Disorder.cstar M * M.gamma⁻¹ * (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)) :=
    le_of_lt (mul_pos (mul_pos hcstar (inv_pos.mpr hgamma)) hgeom)
  have hP : (0 : ℝ) <
      M.nu ^ 2 +
        Disorder.cstar M * M.gamma⁻¹ * (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)) := by
    linarith only [hnu, ha]
  obtain ⟨h1, h2⟩ := sq_sandwich_of_relative_error hx hP htheta htheta' hdev
  exact sandwich_max_of_sq_sandwich ha hnu.le h1 h2

end

end Algsuperdiff.Section3.Provider.Diffusivity
