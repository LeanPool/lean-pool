/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Base.AnnealedPlateau
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Scales.Landmarks

/-!
# PlateauLandmarks

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The landmark specializations of the annealed plateau bound

ABK26, records two consequences of the unconditional plateau display
`e.basecase.shom.m`.  For every `m` below the base landmark `m**`,

`nu Id <= shom_m <= (1 + gamma^2) nu Id`  (`e.basecase.homogenization`),

and for every `m` below the plateau landmark `m*`,

`nu Id <= shom_m <= 2 nu Id`  (`e.basecase.diffusivity`).

The proof of `p.base.case` says these "follow immediately from
`e.basecase.shom.m`. by using the definitions of `m**` and `m*`", and that is
exactly the route taken here.  This file delivers only the *diffusivity*
conjuncts of the two displays; their homogenization-error conjuncts are the
business of other modules.

## Route

Write

`A_m := c+ (2 nu^2)^{-1} gamma^{-1} (1 + 4 gamma) 3^{2 gamma m}`

for the plateau amplitude of `annealedPlateau`, so that
`sigmaBar_m <= nu (1 + A_m)` unconditionally.  Both landmark characterizations
have the quotient form `3^{2 gamma m} <= nu^2 w / (2 (log 3) c+)`, with weight
`w = gamma^3` at `m**` and `w = gamma` at `m*`.  Substituting the quotient bound
into `A_m` cancels `c+` and `nu^2` and leaves

`A_m <= (1 + 4 gamma) w gamma^{-1} / (4 log 3) <= w gamma^{-1}`,

because `gamma <= 1/4` gives `1 + 4 gamma <= 2` while `log 3 > 1` gives
`4 log 3 > 4`.  That single estimate is `plateau_amplitude_le`; the two branches
are its `w = gamma^3` instance (`w gamma^{-1} = gamma^2`) and its `w = gamma`
instance (`w gamma^{-1} = 1`).

## Main results

* `annealedPlateau_le_mStarStar`: the diffusivity conjunct of
  `e.basecase.homogenization`.
* `annealedPlateau_le_mStar`: the diffusivity conjunct of
  `e.basecase.diffusivity`.

## References

* ABK26, `e.basecase.homogenization`, `e.basecase.diffusivity`, with the proof
  reference.
* ABK26, `e.mstarstar`, `e.mstar`.
-/

namespace Algsuperdiff.Section3.Provider.Base

variable {d : ℕ}

/-! ## The numeric input -/

/-- `log 3 > 1`, the only transcendental fact the landmark collapse needs.  It
follows from `Real.exp 1 < 3`. -/
private theorem one_lt_log_three : (1 : ℝ) < Real.log 3 :=
  (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3)).2
    (lt_trans Real.exp_one_lt_d9 (by norm_num))

/-! ## The common landmark collapse -/

/-- **The landmark collapse of the plateau amplitude.**

If the geometric factor obeys the quotient threshold
`3 ^ (2 gamma m) <= nu ^ 2 w / (2 (log 3) c+)` carried by the landmark
characterizations, then the plateau amplitude of `annealedPlateau` collapses to
`w gamma⁻¹`.  The slack is the factor `(1 + 4 gamma) / (4 log 3)`, which is at
most `1` because `gamma <= 1/4` and `log 3 > 1`. -/
private theorem plateau_amplitude_le (M : ABKModel d) (m : ℤ) {w : ℝ} (hw : 0 ≤ w)
    (hb : (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)) ≤
      M.nu ^ 2 * w / (2 * Real.log 3 * Disorder.cstarPlus M)) :
    Disorder.cstarPlus M * (2 * M.nu ^ 2)⁻¹ * M.gamma⁻¹ * (1 + 4 * M.gamma) *
        (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)) ≤ w * M.gamma⁻¹ := by
  have hnu : (0 : ℝ) < M.nu := M.nu_pos
  have hg : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hq : M.gamma ≤ (1 : ℝ) / 4 := M.shellPrefix.gamma_le_quarter
  have hc : (0 : ℝ) < Disorder.cstarPlus M := Disorder.cstarPlus_pos M
  have hlog : (1 : ℝ) < Real.log 3 := one_lt_log_three
  have hnu' : M.nu ≠ 0 := hnu.ne'
  have hg' : M.gamma ≠ 0 := hg.ne'
  have hc' : Disorder.cstarPlus M ≠ 0 := hc.ne'
  have hlog' : Real.log 3 ≠ 0 := by
    have : (0 : ℝ) < Real.log 3 := by linarith
    exact this.ne'
  have hginv : (0 : ℝ) ≤ M.gamma⁻¹ := inv_nonneg.mpr hg.le
  have hu : (0 : ℝ) ≤ w * M.gamma⁻¹ := mul_nonneg hw hginv
  have hK : (0 : ℝ) ≤ Disorder.cstarPlus M * (2 * M.nu ^ 2)⁻¹ * M.gamma⁻¹ *
      (1 + 4 * M.gamma) := by
    have h1 : (0 : ℝ) ≤ (2 * M.nu ^ 2)⁻¹ := by positivity
    exact mul_nonneg (mul_nonneg (mul_nonneg hc.le h1) hginv) (by linarith)
  calc Disorder.cstarPlus M * (2 * M.nu ^ 2)⁻¹ * M.gamma⁻¹ * (1 + 4 * M.gamma) *
        (3 : ℝ) ^ (2 * M.gamma * (m : ℝ))
      ≤ Disorder.cstarPlus M * (2 * M.nu ^ 2)⁻¹ * M.gamma⁻¹ * (1 + 4 * M.gamma) *
          (M.nu ^ 2 * w / (2 * Real.log 3 * Disorder.cstarPlus M)) :=
        mul_le_mul_of_nonneg_left hb hK
    _ = (1 + 4 * M.gamma) * (w * M.gamma⁻¹) / (4 * Real.log 3) := by
        field_simp
        ring
    _ ≤ w * M.gamma⁻¹ := by
        rw [div_le_iff₀ (by linarith : (0 : ℝ) < 4 * Real.log 3)]
        calc (1 + 4 * M.gamma) * (w * M.gamma⁻¹)
            ≤ (4 * Real.log 3) * (w * M.gamma⁻¹) :=
              mul_le_mul_of_nonneg_right (by linarith) hu
          _ = w * M.gamma⁻¹ * (4 * Real.log 3) := by ring

/-! ## The two landmark displays -/

/-- **ABK26, `e.basecase.homogenization`, diffusivity conjunct.**

For every `m <= m**`, the annealed running diffusivity of the coefficient cutoff
satisfies `nu <= sigmaBar_m <= (1 + gamma^2) nu`.

The lower leg is the unconditional plateau's own lower leg.  For the upper leg,
`e.mstarstar` gives `3 ^ (2 gamma m) <= nu^2 gamma^3 / (2 (log 3) c+)`, so the
plateau amplitude is at most `gamma^3 gamma⁻¹ = gamma^2`. -/
theorem annealedPlateau_le_mStarStar (M : ABKModel d) (m : ℤ)
    (hm : m ≤ mStarStar M) :
    M.nu ≤ (Annealed.sigmaBar M m : ℝ) ∧
      (Annealed.sigmaBar M m : ℝ) ≤ (1 + M.gamma ^ 2) * M.nu := by
  obtain ⟨hlow, hup⟩ := annealedPlateau M m
  refine ⟨hlow, ?_⟩
  have hg : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hA := plateau_amplitude_le M m (pow_nonneg hg.le 3)
    ((Provider.Scales.le_mStarStar_iff_rpow_le M m).mp hm)
  have hcollapse : M.gamma ^ 3 * M.gamma⁻¹ = M.gamma ^ 2 := by
    rw [pow_succ, mul_assoc, mul_inv_cancel₀ hg.ne', mul_one]
  rw [hcollapse] at hA
  calc (Annealed.sigmaBar M m : ℝ)
      ≤ M.nu * (1 + Disorder.cstarPlus M * (2 * M.nu ^ 2)⁻¹ * M.gamma⁻¹ *
          (1 + 4 * M.gamma) * (3 : ℝ) ^ (2 * M.gamma * (m : ℝ))) := hup
    _ ≤ M.nu * (1 + M.gamma ^ 2) :=
        mul_le_mul_of_nonneg_left (by linarith) M.nu_pos.le
    _ = (1 + M.gamma ^ 2) * M.nu := by ring

/-- **ABK26, `e.basecase.diffusivity`, diffusivity conjunct.**

For every `m <= m*`, the annealed running diffusivity of the coefficient cutoff
satisfies `nu <= sigmaBar_m <= 2 nu`.

The `m*` window is the wider of the two landmark windows: `e.mstar` gives only
`3 ^ (2 gamma m) <= nu^2 gamma / (2 (log 3) c+)`, so the plateau amplitude is
bounded by `gamma gamma⁻¹ = 1`, which is exactly what the printed constant `2`
accommodates. -/
theorem annealedPlateau_le_mStar (M : ABKModel d) (m : ℤ)
    (hm : m ≤ mStar M) :
    M.nu ≤ (Annealed.sigmaBar M m : ℝ) ∧
      (Annealed.sigmaBar M m : ℝ) ≤ 2 * M.nu := by
  obtain ⟨hlow, hup⟩ := annealedPlateau M m
  refine ⟨hlow, ?_⟩
  have hg : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hA := plateau_amplitude_le M m hg.le
    ((Provider.Scales.le_mStar_iff_rpow_le M m).mp hm)
  rw [mul_inv_cancel₀ hg.ne'] at hA
  calc (Annealed.sigmaBar M m : ℝ)
      ≤ M.nu * (1 + Disorder.cstarPlus M * (2 * M.nu ^ 2)⁻¹ * M.gamma⁻¹ *
          (1 + 4 * M.gamma) * (3 : ℝ) ^ (2 * M.gamma * (m : ℝ))) := hup
    _ ≤ M.nu * 2 := mul_le_mul_of_nonneg_left (by linarith) M.nu_pos.le
    _ = 2 * M.nu := by ring

end Algsuperdiff.Section3.Provider.Base
