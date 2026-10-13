/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.Section3.InductionBounds
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.FlowArithmetic
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.LengthTimeScale

/-!
# SigmaBarProfile

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The running diffusivity against the effective diffusivity profile

The running diffusivity `σ_n` of the coefficient cutoff at scale `n` lies
within the relative distance `C γ^{1/2} |log γ|` of the effective diffusivity
profile

```text
  ν_eff(3^n) = (ν² + c⋆ γ⁻¹ 3^{2γn})^{1/2} ,
```

for every scale `n`, with a constant `C = C(d) c⋆^{-2}`.  This is the induction
estimate for the running diffusivity of Section 3, read at a triadic scale
through `effectiveDiffusivity_three_zpow`.

The amplitude `γ^{1/2}|log γ|` tends to `0` with `γ`, so the relative distance
is at most `1/2` as soon as the disorder parameter lies below an explicit
threshold.  Both halves are packaged together here, which turns the two
comparisons of `LengthTimeScale` between

```text
  T(3^n) = 3^{2n} ν_eff(3^n)⁻¹    and    exitTimeScale M n = 3^{2n} σ_n⁻¹
```

into statements with no remaining premise beyond the threshold on `γ`.

## Main results

* `exists_sqrt_mul_abs_log_le` — any multiple of the amplitude
  `γ^{1/2}|log γ|` is below any prescribed positive bound once `γ` is below an
  explicit threshold.
* `exists_sigmaBar_close_to_effectiveDiffusivity` — the relative bound between
  the running diffusivity and the profile, at every triadic scale, together
  with the smallness of its amplitude.
* `exists_lengthTimeScale_conversions` — the resulting comparison of the two
  time scales, with the explicit factors `2` and `3/2`.

## References

* ABK26, the induction bounds for the running diffusivity of Section 3, and
  the time scale of a length scale of Section 5.3.
-/

namespace Algsuperdiff.Section5.Support

open Algsuperdiff.Section3

noncomputable section

/-! ## 1. The disorder threshold -/

/-- **The amplitude `γ^{1/2}|log γ| ` is uniformly small for small disorder.**
For every positive multiplier `K` and every prescribed positive bound `eps`
there is a threshold below which `K γ^{1/2}|log γ| ≤ eps`.

The threshold is explicit: with `A = max 1 (4 K / eps)` it is `A⁻⁴`, because
`γ^{1/2}|log γ| ≤ 4 γ^{1/4}`. -/
theorem exists_sqrt_mul_abs_log_le {K eps : ℝ} (hK : 0 < K) (heps : 0 < eps) :
    ∃ gamma0 : ℝ, 0 < gamma0 ∧ ∀ gamma : ℝ, 0 < gamma → gamma ≤ gamma0 →
      K * (Real.sqrt gamma * |Real.log gamma|) ≤ eps := by
  set A : ℝ := max 1 (4 * K / eps)
  have hA : 0 < A := zero_lt_one.trans_le (le_max_left _ _)
  have hAone : 1 ≤ A := le_max_left _ _
  have hAK : 4 * K / eps ≤ A := le_max_right _ _
  refine ⟨A⁻¹ ^ (4 : ℕ), by positivity, ?_⟩
  intro gamma hgamma hgamma0
  have hinv : 0 ≤ A⁻¹ := (inv_pos.2 hA).le
  have hgamma1 : gamma ≤ 1 := by
    have hpow : A⁻¹ ^ (4 : ℕ) ≤ 1 :=
      pow_le_one₀ hinv ((inv_le_one₀ hA).2 hAone)
    exact hgamma0.trans hpow
  have hsqrt : Real.sqrt gamma ≤ A⁻¹ ^ (2 : ℕ) := by
    rw [Real.sqrt_le_iff]
    refine ⟨pow_nonneg hinv 2, ?_⟩
    nlinarith only [hgamma0]
  have hsqrtsqrt : Real.sqrt (Real.sqrt gamma) ≤ A⁻¹ := by
    rw [Real.sqrt_le_iff]
    exact ⟨hinv, hsqrt⟩
  have hlog := Algsuperdiff.Section3.Provider.Diffusivity.sqrt_mul_abs_log_le hgamma hgamma1
  have hKA : K * 4 * A⁻¹ ≤ eps := by
    rw [← div_eq_mul_inv, div_le_iff₀ hA]
    have h := mul_le_mul_of_nonneg_left hAK heps.le
    have heq : eps * (4 * K / eps) = 4 * K := by field_simp
    rw [heq] at h
    linarith only [h]
  calc
    K * (Real.sqrt gamma * |Real.log gamma|) ≤
        K * (4 * Real.sqrt (Real.sqrt gamma)) :=
      mul_le_mul_of_nonneg_left hlog hK.le
    _ ≤ K * (4 * A⁻¹) := by gcongr
    _ = K * 4 * A⁻¹ := by ring
    _ ≤ eps := hKA

/-! ## 2. The running diffusivity against the profile -/

/-- **The running diffusivity is within a small relative distance of the
effective diffusivity profile.**  For a fixed value `c⋆` of the disorder
strength there are a threshold `γ₀` and a constant `C` such that every model
with that disorder strength and with `γ ≤ γ₀` satisfies both

```text
  C γ^{1/2}|log γ| ≤ 1/2
```

and, at every triadic scale `3^n`,

```text
  |σ_n − ν_eff(3^n)| ≤ C γ^{1/2}|log γ| σ_n .
```

The constant is `C = C(d) c⋆^{-2}` and the threshold is the smaller of the
disorder threshold of the induction estimate and the threshold that makes the
amplitude at most `1/2`. -/
theorem exists_sigmaBar_close_to_effectiveDiffusivity (d : ℕ) (cstar : ℝ) (hcstar : 0 < cstar) :
    ∃ gamma0 C : ℝ, 0 < gamma0 ∧ 0 < C ∧
      ∀ M : ABKModel d, Disorder.cstar M = cstar → M.gamma ≤ gamma0 →
        C * Real.sqrt M.gamma * |Real.log M.gamma| ≤ 1 / 2 ∧
        ∀ n : ℤ,
          |(Annealed.sigmaBar M n : ℝ) -
              effectiveDiffusivity M.nu cstar M.gamma ((3 : ℝ) ^ n)| ≤
            C * Real.sqrt M.gamma * |Real.log M.gamma| * (Annealed.sigmaBar M n : ℝ) := by
  obtain ⟨Cind, hCind, hind⟩ := Algsuperdiff.Frozen.Section3.induction_bounds d
  have hC : 0 < Cind * cstar⁻¹ ^ (2 : ℕ) := by positivity
  obtain ⟨g1, hg1, hthr⟩ := exists_sqrt_mul_abs_log_le hC (by norm_num : (0 : ℝ) < 1 / 2)
  have hreg : 0 < (Cind⁻¹) ^ (10 : ℕ) * cstar ^ (10 : ℕ) := by positivity
  refine ⟨min g1 ((Cind⁻¹) ^ (10 : ℕ) * cstar ^ (10 : ℕ)), Cind * cstar⁻¹ ^ (2 : ℕ),
    lt_min hg1 hreg, hC, ?_⟩
  intro M hcs hgam
  refine ⟨?_, ?_⟩
  · have heq : Cind * cstar⁻¹ ^ (2 : ℕ) * Real.sqrt M.gamma * |Real.log M.gamma| =
        Cind * cstar⁻¹ ^ (2 : ℕ) * (Real.sqrt M.gamma * |Real.log M.gamma|) := mul_assoc _ _ _
    rw [heq]
    exact hthr M.gamma M.shellPrefix.gamma_pos (hgam.trans (min_le_left _ _))
  · intro n
    have hgammaInd : M.gamma ≤ (Cind⁻¹) ^ (10 : ℕ) * (Disorder.cstar M) ^ (10 : ℕ) := by
      simpa only [hcs] using hgam.trans (min_le_right _ _)
    have h := (hind M hgammaInd).2 n
    rw [hcs] at h
    rw [effectiveDiffusivity_three_zpow]
    exact h

/-! ## 3. The two time scales are comparable -/

/-- **The time scale of the length scale `3^n` and the running scale
`3^{2n} σ_n⁻¹` are comparable, with no premise beyond a threshold on the
disorder parameter.**  For a fixed value `c⋆` of the disorder strength there is
a threshold `γ₀` such that every model with that disorder strength and with
`γ ≤ γ₀` satisfies, at every scale `n`,

```text
  0 < T(3^n) ,    T(3^n) ≤ 2 · exitTimeScale M n ,
  exitTimeScale M n ≤ (3/2) · T(3^n) .
``` -/
theorem exists_lengthTimeScale_conversions (d : ℕ) (cstar : ℝ) (hcstar : 0 < cstar) :
    ∃ gamma0 : ℝ, 0 < gamma0 ∧
      ∀ M : ABKModel d, Disorder.cstar M = cstar → M.gamma ≤ gamma0 → ∀ n : ℤ,
        0 < lengthTimeScale M.nu cstar M.gamma ((3 : ℝ) ^ n) ∧
        lengthTimeScale M.nu cstar M.gamma ((3 : ℝ) ^ n) ≤ 2 * exitTimeScale M n ∧
        exitTimeScale M n ≤ 3 / 2 * lengthTimeScale M.nu cstar M.gamma ((3 : ℝ) ^ n) := by
  obtain ⟨gamma0, C, hgamma0, -, hmain⟩ :=
    exists_sigmaBar_close_to_effectiveDiffusivity d cstar hcstar
  refine ⟨gamma0, hgamma0, ?_⟩
  intro M hcs hgam n
  obtain ⟨hsmall, hprofile⟩ := hmain M hcs hgam
  exact ⟨lengthTimeScale_pos_of_profile M n hsmall (hprofile n),
    lengthTimeScale_le_two_mul_exitTimeScale M n hsmall (hprofile n),
    exitTimeScale_le_three_halves_mul_lengthTimeScale M n hsmall (hprofile n)⟩

end

end Algsuperdiff.Section5.Support
