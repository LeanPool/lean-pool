/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.HomogenizedExitTime
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.IntrinsicScale

/-!
# LengthTimeScale

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The time scale of a length scale

The time scale attached to a length scale `r` is

```text
  T(r) = r² ν_eff(r)⁻¹ ,      ν_eff(r) = (ν² + c⋆ γ⁻¹ r^{2γ})^{1/2} ,
```

and it is the quantity in which the exit-time estimates of Section 5.2 are
written.  The exit-time comparison is proved at the running scale
`exitTimeScale M n = 3^{2n} σ_n⁻¹`, where `σ_n` is the running diffusivity of
the coefficient cutoff at scale `n`.

The two scales agree up to a factor `1 ± C γ^{1/2} |log γ|`, because the
running diffusivity is within that relative distance of the profile
`ν_eff(3^n)`.  This file defines `T(r)` and converts that relative distance
into the two explicit inequalities

```text
  T(3^n) ≤ 2 · exitTimeScale M n ,     exitTimeScale M n ≤ (3/2) · T(3^n) ,
```

which hold as soon as the relative distance is at most `1/2`.

The relative distance is a hypothesis of every statement below, so that this
file depends on nothing but the two scales it compares.  It is a theorem: it
is the second conclusion of `Algsuperdiff.Frozen.Section3.induction_bounds`,
read at a triadic scale, and
`Algsuperdiff.Section5.Support.SigmaBarProfile` discharges it there in
`exists_sigmaBar_close_to_effectiveDiffusivity`, together with the smallness
of its amplitude.  The premise-free forms of the two conversions below are
`exists_lengthTimeScale_conversions` in that module.

## Main definitions

* `lengthTimeScale nu cstar gamma r` — the time scale `T(r) = r² ν_eff(r)⁻¹`.

## Main results

* `lengthTimeScale_le_two_mul_exitTimeScale` and
  `exitTimeScale_le_three_halves_mul_lengthTimeScale` — the two conversions.
* `lengthTimeScale_pos_of_profile` — positivity of `T(3^n)` under the same
  premise.

## References

* ABK26, the time scale of a length scale in Section 5.3, and the induction
  bounds for the running diffusivity of Section 3.
-/

namespace Algsuperdiff.Section5.Support

open Algsuperdiff.Section3

noncomputable section

variable {d : ℕ}

/-! ## 1. The time scale -/

/-- **The time scale attached to a length scale**, `T(r) = r² ν_eff(r)⁻¹`. -/
def lengthTimeScale (nu cstar gamma r : ℝ) : ℝ :=
  r ^ (2 : ℕ) / effectiveDiffusivity nu cstar gamma r

/-! ## 2. The elementary comparison -/

/-- A relative distance at most `1/2` between two reals, the first positive,
puts the second between half and three halves of the first. -/
private theorem halves_of_abs_sub_le {s e eps : ℝ} (hs : 0 < s) (heps : eps ≤ 1 / 2)
    (h : |s - e| ≤ eps * s) : s / 2 ≤ e ∧ e ≤ 3 * s / 2 := by
  obtain ⟨hlow, hhigh⟩ := abs_le.mp h
  have hbound : eps * s ≤ s / 2 := by
    have := mul_le_mul_of_nonneg_right heps hs.le
    linarith only [this]
  exact ⟨by linarith only [hhigh, hbound], by linarith only [hlow, hbound]⟩

/-- With the second real at least half the first, the quotients compare with
the factor two. -/
private theorem div_le_two_mul_div {R s e : ℝ} (hR : 0 ≤ R) (hs : 0 < s)
    (hhalf : s / 2 ≤ e) : R / e ≤ 2 * (R / s) := by
  have hs0 : s ≠ 0 := hs.ne'
  have he : 0 < e := lt_of_lt_of_le (by linarith only [hs]) hhalf
  rw [div_le_iff₀ he, ← sub_nonneg]
  have hexp : 2 * (R / s) * e - R = R / s * (2 * e - s) := by
    field_simp
  rw [hexp]
  exact mul_nonneg (div_nonneg hR hs.le) (by linarith only [hhalf])

/-- With the second real at most three halves of the first, the quotients
compare with the factor three halves in the other direction. -/
private theorem div_le_three_halves_mul_div {R s e : ℝ} (hR : 0 ≤ R) (hs : 0 < s)
    (hhalf : s / 2 ≤ e) (hhigh : e ≤ 3 * s / 2) : R / s ≤ 3 / 2 * (R / e) := by
  have hs0 : s ≠ 0 := hs.ne'
  have he : 0 < e := lt_of_lt_of_le (by linarith only [hs]) hhalf
  have he0 : e ≠ 0 := he.ne'
  rw [div_le_iff₀ hs, ← sub_nonneg]
  have hexp : 3 / 2 * (R / e) * s - R = R / e * (3 * s / 2 - e) := by
    field_simp
  rw [hexp]
  exact mul_nonneg (div_nonneg hR he.le) (by linarith only [hhigh])

/-! ## 3. The conversion at a triadic scale -/

section Conversion

variable (M : ABKModel d) (n : ℤ) {cstar C : ℝ}

/-- The running diffusivity at a triadic scale is between half and three
halves of the profile there, once the relative distance is at most `1/2`. -/
private theorem halves_effectiveDiffusivity
    (hsmall : C * Real.sqrt M.gamma * |Real.log M.gamma| ≤ 1 / 2)
    (hprofile : |(Annealed.sigmaBar M n : ℝ) -
        effectiveDiffusivity M.nu cstar M.gamma ((3 : ℝ) ^ n)| ≤
      C * Real.sqrt M.gamma * |Real.log M.gamma| * (Annealed.sigmaBar M n : ℝ)) :
    (Annealed.sigmaBar M n : ℝ) / 2 ≤
        effectiveDiffusivity M.nu cstar M.gamma ((3 : ℝ) ^ n) ∧
      effectiveDiffusivity M.nu cstar M.gamma ((3 : ℝ) ^ n) ≤
        3 * (Annealed.sigmaBar M n : ℝ) / 2 :=
  halves_of_abs_sub_le (Provider.Orlicz.sigmaBar_pos M n) hsmall hprofile

/-- **The time scale of the length scale `3^n` is positive.** -/
theorem lengthTimeScale_pos_of_profile
    (hsmall : C * Real.sqrt M.gamma * |Real.log M.gamma| ≤ 1 / 2)
    (hprofile : |(Annealed.sigmaBar M n : ℝ) -
        effectiveDiffusivity M.nu cstar M.gamma ((3 : ℝ) ^ n)| ≤
      C * Real.sqrt M.gamma * |Real.log M.gamma| * (Annealed.sigmaBar M n : ℝ)) :
    0 < lengthTimeScale M.nu cstar M.gamma ((3 : ℝ) ^ n) := by
  have hs : (0 : ℝ) < (Annealed.sigmaBar M n : ℝ) := Provider.Orlicz.sigmaBar_pos M n
  have hhalf := (halves_effectiveDiffusivity M n hsmall hprofile).1
  have he : 0 < effectiveDiffusivity M.nu cstar M.gamma ((3 : ℝ) ^ n) :=
    lt_of_lt_of_le (by linarith only [hs]) hhalf
  have h3 : (0 : ℝ) < (3 : ℝ) ^ n := zpow_pos (by norm_num) n
  rw [lengthTimeScale]
  positivity

/-- **The time scale of the length scale `3^n` is at most twice the running
scale `3^{2n} σ_n⁻¹`.** -/
theorem lengthTimeScale_le_two_mul_exitTimeScale
    (hsmall : C * Real.sqrt M.gamma * |Real.log M.gamma| ≤ 1 / 2)
    (hprofile : |(Annealed.sigmaBar M n : ℝ) -
        effectiveDiffusivity M.nu cstar M.gamma ((3 : ℝ) ^ n)| ≤
      C * Real.sqrt M.gamma * |Real.log M.gamma| * (Annealed.sigmaBar M n : ℝ)) :
    lengthTimeScale M.nu cstar M.gamma ((3 : ℝ) ^ n) ≤ 2 * exitTimeScale M n := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ n := zpow_pos (by norm_num) n
  have hR : (0 : ℝ) ≤ ((3 : ℝ) ^ n) ^ (2 : ℕ) := by positivity
  exact div_le_two_mul_div hR (Provider.Orlicz.sigmaBar_pos M n)
    (halves_effectiveDiffusivity M n hsmall hprofile).1

/-- **The running scale `3^{2n} σ_n⁻¹` is at most three halves of the time
scale of the length scale `3^n`.** -/
theorem exitTimeScale_le_three_halves_mul_lengthTimeScale
    (hsmall : C * Real.sqrt M.gamma * |Real.log M.gamma| ≤ 1 / 2)
    (hprofile : |(Annealed.sigmaBar M n : ℝ) -
        effectiveDiffusivity M.nu cstar M.gamma ((3 : ℝ) ^ n)| ≤
      C * Real.sqrt M.gamma * |Real.log M.gamma| * (Annealed.sigmaBar M n : ℝ)) :
    exitTimeScale M n ≤ 3 / 2 * lengthTimeScale M.nu cstar M.gamma ((3 : ℝ) ^ n) := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ n := zpow_pos (by norm_num) n
  have hR : (0 : ℝ) ≤ ((3 : ℝ) ^ n) ^ (2 : ℕ) := by positivity
  obtain ⟨hhalf, hhigh⟩ := halves_effectiveDiffusivity M n hsmall hprofile
  exact div_le_three_halves_mul_div hR (Provider.Orlicz.sigmaBar_pos M n) hhalf hhigh

end Conversion

end

end Algsuperdiff.Section5.Support
