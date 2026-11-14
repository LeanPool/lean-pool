/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.Section4.AnomalousRegularity
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomSpineResidueCore

/-!
# HomProviderBAssembly

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Theorem B, §4.5: the Theorem-B assembly off Theorem C

## What this file supplies

`exists_regularity_minimalScale` — the Theorem-C export re-shaped at the §4.5
parameter web: at `α:= homAlpha M = 1 - s/2` the minimal scale `X_m(α)` exists
with a tail at ONE model-independent constant `C⋆ ≥ 1`, together with the per-`ω`
energy-density display.  This produces exactly the `htail` hypothesis of the
§4.5 spine's close step (the `Cst` slot) plus the display the residual step
consumes.  It is UNCONDITIONAL.

Two arithmetic facts carry it: the printed observation in the paper that
`α ∈ (0, 1 - C₀ γ^{1/2}]` for small `γ` (`homAlpha_le_one_sub` here, off
`absLog_mul_sqrt_le`), and the monotonicity of the printed tail profile in its
own constant (`regTail_mono_const`).
-/

open Algsuperdiff.Section3
open HCPolySupport MeasureTheory
open scoped ENNReal

namespace Algsuperdiff.Section4.Provider.Homogenization

open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

/-! ## 1. The Theorem-C display, transcribed -/

/-- **The per-`ω` conclusion of `anomalous_regularity`**, byte for
byte from the frozen statement's `∀ᵐ ω` body, with the root's `C` and `alpha`
and its minimal scale `X` as parameters.

This is the ONLY thing the §4.5 Step-2 energy slot consumes from Theorem C. -/
def RegularityDisplayAt (M : ABKModel d) (Creg alpha : ℝ) (m : ℤ)
    (X : Cutoff.CutoffSample d → ℕ∞) (omega : Cutoff.CutoffSample d) : Prop :=
  ∀ L : ℤ, m ≤ L →
    ∀ (u h : H1Function (openCubeSet (originCube d m))) (g : Vec d → Vec d) (Kg Kh : ℝ),
      IsDirichletSolutionOn (Cutoff.coefficientCutoff M.nu L omega).toCoeffField
        (originCube d m) u h g →
      HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) Kg g →
      HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) Kh h.grad →
      (∀ y ∈ openCubeSet (originCube d m),
        ‖h.grad y‖ ≤ Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh) →
      HasGradientOn (openCubeSet (originCube d m)) h.toFun h.grad →
      ∀ x : Vec d, x ∈ openCubeSet (originCube d m) →
        ∀ n : ℤ, n ≤ m → X omega ≤ (((m - n).toNat : ℕ) : ℕ∞) →
          (ENNReal.ofReal (Real.sqrt M.nu) *
                eLpNorm (fun y => Real.sqrt (vecNormSq (u.grad y))) 2
                  (normalizedVolumeMeasureOn
                    (((fun y => x + y) '' openCubeSet (originCube d n)) ∩
                      openCubeSet (originCube d m))) ≤
              ENNReal.ofReal (Creg * Real.rpow (3 : ℝ) ((1 - alpha) * ((m : ℝ) - (n : ℝ)))) *
                (ENNReal.ofReal (Real.sqrt M.nu) *
                    eLpNorm (fun y => Real.sqrt (vecNormSq (u.grad y))) 2
                      (normalizedVolumeMeasureOn (openCubeSet (originCube d m))) +
                  ENNReal.ofReal
                    (Real.sqrt (Annealed.sigmaBar M m : ℝ)⁻¹ *
                      Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kg) +
                  ENNReal.ofReal
                    (Real.sqrt (Annealed.sigmaBar M m : ℝ) *
                      Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh))) ∧
            (x ∈ openCubeSet (originCube d (m - 1)) →
              ENNReal.ofReal (Real.sqrt M.nu) *
                  eLpNorm (fun y => Real.sqrt (vecNormSq (u.grad y))) 2
                    (normalizedVolumeMeasureOn
                      (((fun y => x + y) '' openCubeSet (originCube d n)) ∩
                        openCubeSet (originCube d m))) ≤
                ENNReal.ofReal
                    (Creg * Real.rpow (3 : ℝ) ((1 - alpha) * ((m : ℝ) - (n : ℝ)))) *
                  (ENNReal.ofReal (Real.sqrt M.nu) *
                      eLpNorm (fun y => Real.sqrt (vecNormSq (u.grad y))) 2
                        (normalizedVolumeMeasureOn (openCubeSet (originCube d m))) +
                    ENNReal.ofReal
                      (Real.sqrt (Annealed.sigmaBar M m : ℝ)⁻¹ *
                        Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kg)))

/-! ## 2. The two arithmetic facts of the re-shaping -/

/-- **The printed observation, formalized**: at the §4.5 web `α = 1 - s/2` sits inside
Theorem C's admissible range `α ≤ 1 - C₀ √γ` once `γ ≤ (8C₀)⁻⁴`.

The only ingredient is `|log γ|√γ ≤ 4 γ^{1/4}` (`absLog_mul_sqrt_le`): the
printed "if `γ` is sufficiently small" made explicit. -/
theorem homAlpha_le_one_sub {M : ABKModel d} {Creg : ℝ} (hCreg : 0 < Creg)
    (hg1 : M.gamma < 1) (hgle : M.gamma ≤ ((8 * Creg)⁻¹) ^ (4 : ℕ)) :
    homAlpha M ≤ 1 - Creg * Real.sqrt M.gamma := by
  have hgpos : 0 < M.gamma := M.shellPrefix.gamma_pos
  have h8 : (0 : ℝ) < 8 * Creg := by linarith only [hCreg]
  have ht : Real.sqrt (Real.sqrt M.gamma) ≤ (8 * Creg)⁻¹ :=
    quarticRoot_le hgpos.le (inv_pos.mpr h8).le hgle
  have hkey : |Real.log M.gamma| * Real.sqrt M.gamma ≤ 4 * Real.sqrt (Real.sqrt M.gamma) :=
    absLog_mul_sqrt_le hgpos hg1
  have hstep : 4 * Real.sqrt (Real.sqrt M.gamma) ≤ 4 * (8 * Creg)⁻¹ := by
    linarith only [ht]
  have hmul : (8 * Creg) * (4 * (8 * Creg)⁻¹) = 4 := by
    field_simp
  /- `2 C √γ |log γ| ≤ 1`, i.e. `C √γ ≤ s/2` -/
  have hlogpos : (0 : ℝ) < |Real.log M.gamma| := by
    have hne : Real.log M.gamma ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one hgpos (ne_of_lt hg1)
    exact abs_pos.mpr hne
  have hprod : (8 * Creg) * (|Real.log M.gamma| * Real.sqrt M.gamma) ≤ 4 := by
    calc (8 * Creg) * (|Real.log M.gamma| * Real.sqrt M.gamma)
        ≤ (8 * Creg) * (4 * (8 * Creg)⁻¹) :=
          mul_le_mul_of_nonneg_left (le_trans hkey hstep) h8.le
      _ = 4 := hmul
  have hhalf : Creg * Real.sqrt M.gamma * |Real.log M.gamma| ≤ 1 / 2 := by
    linarith only [hprod]
  have hSeq : homS M = |Real.log M.gamma|⁻¹ := rfl
  have hCS : Creg * Real.sqrt M.gamma ≤ homS M / 2 := by
    have hinv : (0 : ℝ) < |Real.log M.gamma|⁻¹ := inv_pos.mpr hlogpos
    have h := mul_le_mul_of_nonneg_right hhalf hinv.le
    rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt hlogpos), mul_one] at h
    rw [hSeq]
    linarith only [h]
  rw [homAlpha]
  linarith only [hCS]

/-- **The printed tail profile is monotone in its own constant.**

`K ↦ K exp(-(a(N-K))/(Kγ)) = K exp((a/γ)(1 - N/K))` increases in `K > 0` for
every `N ≥ 0`, so Theorem C's tail at its own `C` implies the spine's tail at
any `C⋆ ≥ C`.  This is what lets the spine's `Cst` slot be filled by
`max 1 C`. -/
theorem regTail_mono_const {K K' a gamma : ℝ} (N : ℕ) (hK : 0 < K) (hKK' : K ≤ K')
    (ha : 0 ≤ a) (hgamma : 0 < gamma) :
    K * Real.exp (-(a * ((N : ℝ) - K)) / (K * gamma)) ≤
      K' * Real.exp (-(a * ((N : ℝ) - K')) / (K' * gamma)) := by
  have hK' : 0 < K' := lt_of_lt_of_le hK hKK'
  have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hdiv : (N : ℝ) / K' ≤ (N : ℝ) / K := by gcongr
  have hL : -(a * ((N : ℝ) - K)) / (K * gamma) = a / gamma * (1 - (N : ℝ) / K) := by
    field_simp
    ring
  have hR : -(a * ((N : ℝ) - K')) / (K' * gamma) = a / gamma * (1 - (N : ℝ) / K') := by
    field_simp
    ring
  have hag : (0 : ℝ) ≤ a / gamma := div_nonneg ha hgamma.le
  have hexp : -(a * ((N : ℝ) - K)) / (K * gamma) ≤
      -(a * ((N : ℝ) - K')) / (K' * gamma) := by
    rw [hL, hR]
    exact mul_le_mul_of_nonneg_left (by linarith only [hdiv]) hag
  have hmono : Real.exp (-(a * ((N : ℝ) - K)) / (K * gamma)) ≤
      Real.exp (-(a * ((N : ℝ) - K')) / (K' * gamma)) := Real.exp_le_exp.mpr hexp
  exact mul_le_mul hKK' hmono (Real.exp_pos _).le hK'.le

/-! ## 3. Theorem C, re-shaped at the §4.5 web -/

/-- **THE MINIMAL SCALE, AT THE §4.5 PARAMETER WEB.**

The `anomalous_regularity` read at `α:= homAlpha M = 1 - s/2`: one
model-independent `C⋆ ≥ 1` and one threshold `γ₀ > 0` such that for every model
and every scale `m` the minimal scale `X` exists, is measurable, has the
spine's own tail profile at `C⋆`, and carries the per-`ω` energy-density
display.

`htail` of the §4.5 spine's close step is exactly the second conjunct. -/
theorem exists_regularity_minimalScale (d : ℕ) (cstar : ℝ) (hcstar : 0 < cstar) :
    ∃ Cst Creg gamma0 : ℝ, 1 ≤ Cst ∧ 0 < Creg ∧ 0 < gamma0 ∧
      ∀ M : ABKModel d, Disorder.cstar M = cstar → M.gamma ≤ gamma0 →
        ∀ m : ℤ, ∃ X : Cutoff.CutoffSample d → ℕ∞,
          Measurable X ∧
          (∀ N : ℕ,
            (Cutoff.cutoffSampleLaw M).toMeasure {omega | (N : ℕ∞) ≤ X omega} ≤
              ENNReal.ofReal (Cst *
                Real.exp (-((1 - homAlpha M) ^ (2 : ℕ) * ((N : ℝ) - Cst)) /
                  (Cst * M.gamma)))) ∧
          (∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
            RegularityDisplayAt M Creg (homAlpha M) m X omega) := by
  obtain ⟨g0, Creg, hg0, hCreg, hreg⟩ :=
    Algsuperdiff.Frozen.Section4.anomalous_regularity d cstar hcstar
  have h8 : (0 : ℝ) < 8 * Creg := by linarith only [hCreg]
  have hquart : (0 : ℝ) < ((8 * Creg)⁻¹) ^ (4 : ℕ) := pow_pos (inv_pos.mpr h8) 4
  refine ⟨max 1 Creg, Creg, min g0 (min (1 / 81) (((8 * Creg)⁻¹) ^ (4 : ℕ))),
    le_max_left _ _, hCreg,
    lt_min hg0 (lt_min (by norm_num) hquart), ?_⟩
  intro M hcs hgamma m
  have hgpos : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hg_g0 : M.gamma ≤ g0 := le_trans hgamma (min_le_left _ _)
  have hg_81 : M.gamma ≤ 1 / 81 :=
    le_trans hgamma (le_trans (min_le_right _ _) (min_le_left _ _))
  have hg_C : M.gamma ≤ ((8 * Creg)⁻¹) ^ (4 : ℕ) :=
    le_trans hgamma (le_trans (min_le_right _ _) (min_le_right _ _))
  have hg1 : M.gamma < 1 := by linarith only [hg_81]
  have hL4 : 4 ≤ |Real.log M.gamma| := four_le_absLog hgpos hg_81
  have halpha0 : 0 < homAlpha M := homAlpha_pos hL4
  have halpha1 : homAlpha M ≤ 1 - Creg * Real.sqrt M.gamma :=
    homAlpha_le_one_sub hCreg hg1 hg_C
  obtain ⟨X, hXmeas, hXtail, hXdisp⟩ :=
    hreg M hcs hg_g0 (homAlpha M) halpha0 halpha1 m
  refine ⟨X, hXmeas, ?_, ?_⟩
  · intro N
    refine le_trans (hXtail N) (ENNReal.ofReal_le_ofReal ?_)
    exact regTail_mono_const N hCreg (le_max_right _ _)
      (sq_nonneg (1 - homAlpha M)) hgpos
  · filter_upwards [hXdisp] with omega hom
    intro L hL u h g Kg Kh hsol hKg hKh hKhsup hgrad x hx n hn hX
    exact hom L hL u h g Kg Kh hsol hKg hKh hKhsup hgrad x hx n hn hX

end

end Algsuperdiff.Section4.Provider.Homogenization
