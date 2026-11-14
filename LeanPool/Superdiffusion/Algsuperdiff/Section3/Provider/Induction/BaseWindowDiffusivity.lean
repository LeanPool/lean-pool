/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.Section3.InductionState
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Base.PlateauLandmarks

/-!
# BaseWindowDiffusivity

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The diffusivity conjunct of the induction state on the whole base window `m ≤ m*`

ABK26, the induction hypothesis `d.mathcalS.def` and its first clause
`e.shom.h.bounds`:

`¼ max{c⋆ γ⁻¹ 3^(2γm), ν²} ≤ σ_m² ≤ 4 max{c⋆ γ⁻¹ 3^(2γm), ν²}`.

## Main results

* `inductionState_diffusivity_le_mStar`: the clause at every `m ≤ mStar M`.

## Route

The window characterization `Provider.Scales.le_mStar_iff`
(`Provider/Scales/Landmarks.lean`) turns `m ≤ mStar M` into

`2 (log 3) c⁺ γ⁻¹ 3^(2γm) ≤ ν²`.

The standing dimension bound `2 ≤ d` (`M.shellPrefix.dimension`) and the proved
`Disorder.dim_mul_cstar_le_cstarPlus` (`Section3/Disorder/Cstar.lean`) give `2
c⋆ ≤ d c⋆ ≤ c⁺`, so with `log 3 > 1`

`c⋆ γ⁻¹ 3^(2γm) ≤ ½ c⁺ γ⁻¹ 3^(2γm) ≤ ν² / (4 log 3) ≤ ν²`,

and the `max` collapses to `ν²`.  The proved plateau specialization
`Provider.Base.annealedPlateau_le_mStar`
(`Provider/Base/PlateauLandmarks.lean`), which is the diffusivity conjunct of
`e.basecase.diffusivity`, then gives `ν ≤ σ_m ≤ 2 ν`; squaring proves inside
the printed window `[ν²/4, 4 ν²]`, the constants `¼` and `4` being exactly the
squares of `1` and `2`.

No hypothesis beyond `m ≤ mStar M` is used: `2 ≤ d` is not a binder here, it is
read off the standing model through `M.shellPrefix.dimension`, exactly as the
near-twin does.

## References

* ABK26, (`d.mathcalS.def`), (`e.shom.h.bounds`).
* ABK26, (`e.basecase.diffusivity`), proof reference.
* ABK26, (`e.mstar`).
* ABK26, (the printed split at `m*`).
-/

namespace Algsuperdiff.Section3.Provider.Induction

variable {d : ℕ}

/-! ## The numeric input -/

/-- `log 3 > 1`, the only transcendental fact the window collapse needs. -/
private theorem one_lt_log_three : (1 : ℝ) < Real.log 3 :=
  (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3)).2
    (lt_trans Real.exp_one_lt_d9 (by norm_num))

/-! ## The abstract collapse

Stated on bare reals so that the geometric factor never appears in a linear
arithmetic goal: `Y` below is instantiated at `γ⁻¹ 3^(2γm)`, which is an `rpow`
and stays an opaque nonnegative atom throughout. -/

/-- If `2 L c⁺ Y ≤ ν²` with `L > 1`, `0 < c`, `2 c ≤ c⁺` and `0 ≤ Y`, then
already `c Y ≤ ν²`.  The slack thrown away is the factor `4 L`. -/
private theorem mul_le_of_two_mul_mul_le {L cp c Y nu2 : ℝ}
    (hL : 1 < L) (hc : 0 < c) (h2c : 2 * c ≤ cp) (hY : 0 ≤ Y)
    (h : 2 * L * cp * Y ≤ nu2) : c * Y ≤ nu2 := by
  have hcp : (0 : ℝ) < cp := by linarith
  have hLcp : cp ≤ L * cp := le_mul_of_one_le_left hcp.le hL.le
  have hle : c ≤ 2 * L * cp := by linarith
  have h1 : c * Y ≤ 2 * L * cp * Y := mul_le_mul_of_nonneg_right hle hY
  linarith

/-! ## The window collapse of the comparison quantity -/

/-- **On the whole base window the comparison quantity is dominated by `ν²`.**

`e.mstar` gives `2 (log 3) c⁺ γ⁻¹ 3^(2γm) ≤ ν²`; the standing `2 ≤ d` and
`d c⋆ ≤ c⁺` give `2 c⋆ ≤ c⁺`; and `log 3 > 1`.  Hence
`c⋆ γ⁻¹ 3^(2γm) ≤ ν² / (4 log 3) ≤ ν²`. -/
private theorem cstar_mul_rpow_le_nu_sq (M : ABKModel d) (m : ℤ)
    (hm : m ≤ mStar M) :
    Disorder.cstar M * M.gamma⁻¹ * (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)) ≤ M.nu ^ 2 := by
  have hg : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hcs : (0 : ℝ) < Disorder.cstar M := (Disorder.cstar_characterization M).1
  have hd : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast M.shellPrefix.dimension
  have h2c : 2 * Disorder.cstar M ≤ Disorder.cstarPlus M := by
    have hdc := Disorder.dim_mul_cstar_le_cstarPlus M
    have h2 : 2 * Disorder.cstar M ≤ (d : ℝ) * Disorder.cstar M :=
      mul_le_mul_of_nonneg_right hd hcs.le
    linarith
  have hY : (0 : ℝ) ≤ M.gamma⁻¹ * (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)) :=
    mul_nonneg (inv_nonneg.mpr hg.le) (Real.rpow_nonneg (by norm_num) _)
  have hlm : 2 * Real.log 3 * Disorder.cstarPlus M *
      (M.gamma⁻¹ * (3 : ℝ) ^ (2 * M.gamma * (m : ℝ))) ≤ M.nu ^ 2 := by
    have h := (Provider.Scales.le_mStar_iff M m).mp hm
    calc 2 * Real.log 3 * Disorder.cstarPlus M *
          (M.gamma⁻¹ * (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)))
        = 2 * Real.log 3 * Disorder.cstarPlus M * M.gamma⁻¹ *
            (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)) := by ring
      _ ≤ M.nu ^ 2 := h
  have hcollapse := mul_le_of_two_mul_mul_le one_lt_log_three hcs h2c hY hlm
  calc Disorder.cstar M * M.gamma⁻¹ * (3 : ℝ) ^ (2 * M.gamma * (m : ℝ))
      = Disorder.cstar M * (M.gamma⁻¹ * (3 : ℝ) ^ (2 * M.gamma * (m : ℝ))) := by ring
    _ ≤ M.nu ^ 2 := hcollapse

/-! ## The diffusivity conjunct on the base window -/

/-- **`e.shom.h.bounds` on the whole base window `m ≤ m*`.**

This is the first conjunct of `Algsuperdiff.Frozen.Section3.inductionState`,
which does not mention `E`, on the printed range of `e.basecase.diffusivity`.
Unconditional: no residual input, no caller-supplied proposition.

For `m ≤ m*` the landmark `e.mstar` collapses the `max` to `ν²`
(`cstar_mul_rpow_le_nu_sq`), and the proved plateau specialization
`Provider.Base.annealedPlateau_le_mStar` gives `ν ≤ σ_m ≤ 2 ν`, hence `ν²/4 ≤
ν² ≤ σ_m² ≤ 4 ν²`. -/
theorem inductionState_diffusivity_le_mStar (M : ABKModel d) :
    ∀ m : ℤ, m ≤ mStar M →
      (1 / 4 : ℝ) *
          max
            (Disorder.cstar M * M.gamma⁻¹ * (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)))
            (M.nu ^ 2)
        ≤ (Annealed.sigmaBar M m : ℝ) ^ 2 ∧
      (Annealed.sigmaBar M m : ℝ) ^ 2
        ≤ 4 *
          max
            (Disorder.cstar M * M.gamma⁻¹ * (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)))
            (M.nu ^ 2) := by
  intro m hm
  have hnu : (0 : ℝ) < M.nu := M.nu_pos
  have hkey := cstar_mul_rpow_le_nu_sq M m hm
  obtain ⟨hlow, hup⟩ := Provider.Base.annealedPlateau_le_mStar M m hm
  have hsig : (0 : ℝ) < (Annealed.sigmaBar M m : ℝ) := lt_of_lt_of_le hnu hlow
  have hsq1 : M.nu ^ 2 ≤ (Annealed.sigmaBar M m : ℝ) ^ 2 := by
    rw [pow_two, pow_two]
    exact mul_self_le_mul_self hnu.le hlow
  have hsq2 : (Annealed.sigmaBar M m : ℝ) ^ 2 ≤ 4 * M.nu ^ 2 :=
    calc (Annealed.sigmaBar M m : ℝ) ^ 2 ≤ (2 * M.nu) ^ 2 := by
          rw [pow_two, pow_two]
          exact mul_self_le_mul_self hsig.le hup
      _ = 4 * M.nu ^ 2 := by ring
  rw [max_eq_right hkey]
  exact ⟨by linarith [sq_nonneg M.nu], hsq2⟩

/-- **The window form: the first conjunct of the induction state at every top
scale `m0 ≤ m*`.**

`Algsuperdiff.Frozen.Section3.inductionState M m0 E` opens with
`∀ m : ℤ, m ≤ m0 → e.shom.h.bounds at m`.  For `m0 ≤ mStar M` that clause is
exactly the previous theorem composed with transitivity, so it is available
unconditionally and for every budget `E`. -/
theorem inductionState_diffusivity_of_le_mStar (M : ABKModel d) {m0 : ℤ}
    (hm0 : m0 ≤ mStar M) :
    ∀ m : ℤ, m ≤ m0 →
      (1 / 4 : ℝ) *
          max
            (Disorder.cstar M * M.gamma⁻¹ * (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)))
            (M.nu ^ 2)
        ≤ (Annealed.sigmaBar M m : ℝ) ^ 2 ∧
      (Annealed.sigmaBar M m : ℝ) ^ 2
        ≤ 4 *
          max
            (Disorder.cstar M * M.gamma⁻¹ * (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)))
            (M.nu ^ 2) :=
  fun m hm => inductionState_diffusivity_le_mStar M m (hm.trans hm0)

end Algsuperdiff.Section3.Provider.Induction
