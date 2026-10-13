/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Probability.CesaroWindow
public import LeanPool.Superdiffusion.Algsuperdiff.Probability.ColoredAverage

/-!
# CesaroEngine

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The independent-family Cesàro concentration engine

ABK26, proof of `l.minimal.scale.sep`.

Each of the paper's three Steps ends, after a deterministic rearrangement, with a
Cesàro average over the window `[n, m]` of the shape
  `(m − n + 1)⁻¹ ( a · Σ_{k = n}^{m} X_k(ω)  +  T(ω) )`,

where `{X_k}` is an independent family with `X_k ≤ O_{Γ₂}(K)` and `E[X_k] ≤ μ₀`,
and `T` is a boundary/tail term with `T ≤ O_{Γ₂}(b)`. The Step's conclusion is
  `≤  a·μ₀  +  O_{Γ₂}( C (a K + b) (m − n + 1)^{-1/2} )`.

This module **proves** that implication for genuinely independent families. Its
`r`-dependent counterpart — the form Step 1 actually needs, where independence is
weakened to finite-range dependence — is
`Algsuperdiff/Probability/ColoredCesaro.lean`; the two are deliberately parallel,
and this one is the cheaper route whenever full independence is available.

The route is the paper's own:

1. `integral_le_of_isBigO_gammaSigma` — `e.moments.OGamma2`: a `Γ_σ` tail gives
   integrability and the first-moment bound `∫ X ≤ C_mom(σ) K` (the modulus
   version and the integrability are in `CesaroWindow.lean`).
2. `centered_isBigO_gammaSigma_moment` (`CesaroWindow.lean`) — centering `X ↦ X
   − E X` costs only a constant factor in the `Γ_σ` scale.
3. `isBigO_cesaroAvg_of_iIndepFun_centered` — CoarseGraining's averaged
   `p.concentration` transported to the `cesaroAvg`/`Finset.Icc n m`
   bookkeeping, with the `√N / N = N^{-1/2}` rewrite done once and for all.
4. `cesaroAvg_isBigO_of_iIndepFun` — the headline engine.
5. `cesaroAvg_isBigO_of_iIndepFun_with_tail` — the engine with the boundary term,
   absorbed by `(m − n + 1)⁻¹ ≤ (m − n + 1)^{-1/2}`.

Everything is generic over the sample space: no carrier, no coefficient field and
no scale geometry enters.

## Main results

* `Algsuperdiff.Probability.cesaroEngineConst`
* `Algsuperdiff.Probability.isBigO_cesaroAvg_of_iIndepFun_centered`
* `Algsuperdiff.Probability.cesaroAvg_isBigO_of_iIndepFun`
* `Algsuperdiff.Probability.cesaroAvg_isBigO_of_iIndepFun_with_tail`

## References

* ABK26, Proposition `p.concentration`.
* ABK26, `e.moments.OGamma2`.
-/

namespace Algsuperdiff.Probability

open MeasureTheory
open HCPolySupport.IndependentSums
open HCPolySupport.Book.Ch04 (gammaSigmaIndependentSumConst
  isBigO_gammaSigma_finsetAverage_of_iIndepFun_of_isBigO_of_integral_eq_zero)
open scoped BigOperators

noncomputable section

/-! ## Explicit constants -/

/-- The Cesàro engine constant: CoarseGraining's centered independent-sum constant
for `σ = 2` times the centering cost. -/
def cesaroEngineConst : ℝ :=
  gammaSigmaIndependentSumConst 2 * cesaroCenterConst 2

/-- The Cesàro engine constant in the presence of an additive boundary/tail
term. -/
def cesaroTailEngineConst : ℝ :=
  (1 + Real.log 2) ^ (2 : ℝ)⁻¹ * (cesaroEngineConst + 1)

theorem cesaroEngineConst_pos : 0 < cesaroEngineConst :=
  mul_pos (gammaSigmaIndependentSumConst_pos (by norm_num))
    (cesaroCenterConst_pos (by norm_num))

theorem cesaroTailEngineConst_pos : 0 < cesaroTailEngineConst := by
  have h1 : (0 : ℝ) < (1 + Real.log 2) ^ (2 : ℝ)⁻¹ :=
    Real.rpow_pos_of_pos one_add_log_two_pos _
  have h2 := cesaroEngineConst_pos
  simp only [cesaroTailEngineConst]
  exact mul_pos h1 (by linarith only [h2])

/-! ## `rpow` bookkeeping -/

/-- `(x + 1)^{-1/2} ≤ x^{-1/2}` for `x > 0` — the little monotonicity fact that
converts the engine's natural `(m − n + 1)^{-1/2}` envelope into the paper's
`(m − n)^{-1/2}` envelope. -/
theorem rpow_neg_half_le_rpow_neg_half {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    y ^ (-(1 : ℝ) / 2) ≤ x ^ (-(1 : ℝ) / 2) :=
  Real.rpow_le_rpow_of_nonpos hx hxy (by norm_num)

/-! ## Moments from `Γ_σ` tails (`e.moments.OGamma2`) -/

section Moments

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- `E X ≤ C_mom(σ) K` under a `Γ_σ` tail bound. -/
theorem integral_le_of_isBigO_gammaSigma [IsProbabilityMeasure P]
    {X : Ω → ℝ} {σ K : ℝ} (hσ : 0 < σ) (hK : 0 < K)
    (hXm : AEMeasurable X P) (hX : IsBigO P (gammaSigma σ) X K) :
    ∫ ω, X ω ∂P ≤ gammaMomentConst σ * K :=
  le_trans (le_abs_self _) (abs_integral_le_of_isBigO_gammaSigma hσ hK hXm hX)

end Moments

/-! ## The averaged concentration bound for a centered family -/

section CenteredAverage

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **Averaged `p.concentration` in `cesaroAvg` form.** For a centered,
independent, `Γ₂`-controlled family `{Y_j}`, the Cesàro average over `[n, m]`
obeys `O_{Γ₂}( C · K · (m − n + 1)^{-1/2} )`. -/
theorem isBigO_cesaroAvg_of_iIndepFun_centered [IsProbabilityMeasure P]
    (Y : ℤ → Ω → ℝ) {Kc : ℝ} (hKc : 0 < Kc)
    (hindep : ProbabilityTheory.iIndepFun Y P)
    (hmeas : ∀ j, Measurable (Y j))
    (hY : ∀ j, IsBigO P (gammaSigma 2) (Y j) Kc)
    (hmean : ∀ j, ∫ ω, Y j ω ∂P = 0)
    {n m : ℤ} (hnm : n ≤ m) :
    IsBigO P (gammaSigma 2) (fun ω => cesaroAvg (fun j => Y j ω) n m)
      (gammaSigmaIndependentSumConst 2 * Kc
        * (((m - n + 1 : ℤ) : ℝ)) ^ (-(1 : ℝ) / 2)) := by
  have hcard : (((Finset.Icc n m).card : ℕ) : ℝ) = ((m - n + 1 : ℤ) : ℝ) :=
    natCast_card_Icc_int hnm
  have hcpos : (0 : ℝ) < ((m - n + 1 : ℤ) : ℝ) := window_pos hnm
  have hs : (Finset.Icc n m).Nonempty := ⟨n, Finset.mem_Icc.mpr ⟨le_rfl, hnm⟩⟩
  have hconc :=
    isBigO_gammaSigma_finsetAverage_of_iIndepFun_of_isBigO_of_integral_eq_zero
      (μ := P) (X := Y) (s := Finset.Icc n m) (σ := 2) (K := Kc)
      hindep hmeas hs (by norm_num) le_rfl hKc (fun j _ => hY j) (fun j _ => hmean j)
  -- Rewrite the averaging prefactor into `cesaroAvg` form.
  have hfun :
      (fun ω => ((((Finset.Icc n m).card : ℕ) : ℝ))⁻¹ * ∑ i ∈ Finset.Icc n m, Y i ω)
        = fun ω => cesaroAvg (fun j => Y j ω) n m := by
    funext ω
    simp only [cesaroAvg, hcard, one_div]
  -- Rewrite the scale.
  have hscale :
      gammaSigmaIndependentSumConst 2 *
          (Real.sqrt (((Finset.Icc n m).card : ℕ) : ℝ) /
            ((((Finset.Icc n m).card : ℕ) : ℝ))) * Kc
        = gammaSigmaIndependentSumConst 2 * Kc
            * (((m - n + 1 : ℤ) : ℝ)) ^ (-(1 : ℝ) / 2) := by
    rw [hcard, sqrt_div_self_eq_rpow_neg_half hcpos]
    ring
  rw [hfun, hscale] at hconc
  exact hconc

end CenteredAverage

/-! ## The engine -/

section Engine

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **The Cesàro concentration engine.** For an independent family `{X_j}` with
`X_j ≤ O_{Γ₂}(K)` and `E X_j ≤ μ₀`, the Cesàro average over a window `[n, m]` splits as
`μ₀` plus a fluctuation of scale `cesaroEngineConst · K · (m − n + 1)^{-1/2}`.

This is the shared probabilistic core of Steps 1--3 in the proof of ABK26
`l.minimal.scale.sep`, in the fully independent regime. -/
theorem cesaroAvg_isBigO_of_iIndepFun [IsProbabilityMeasure P]
    (X : ℤ → Ω → ℝ) {K mu0 : ℝ} (hK : 0 < K)
    (hindep : ProbabilityTheory.iIndepFun X P)
    (hmeas : ∀ j, Measurable (X j))
    (hX : ∀ j, IsBigO P (gammaSigma 2) (X j) K)
    (hmean : ∀ j, ∫ ω, X j ω ∂P ≤ mu0)
    (n m : ℤ) (hnm : n ≤ m) :
    ∃ Xfluc : Ω → ℝ,
      (∀ ω, cesaroAvg (fun j => X j ω) n m ≤ mu0 + Xfluc ω) ∧
      IsBigO P (gammaSigma 2) Xfluc
        (cesaroEngineConst * K * (((m - n + 1 : ℤ) : ℝ)) ^ (-(1 : ℝ) / 2)) := by
  have hσ : (0 : ℝ) < 2 := by norm_num
  have hint : ∀ j, Integrable (X j) P := fun j =>
    integrable_of_isBigO_gammaSigma hσ hK (hmeas j).aemeasurable (hX j)
  have hKc : 0 < cesaroCenterConst 2 * K := mul_pos (cesaroCenterConst_pos hσ) hK
  have hYmeas : ∀ j, Measurable (fun ω => X j ω - ∫ ω', X j ω' ∂P) := fun j =>
    (hmeas j).sub measurable_const
  have hYindep : ProbabilityTheory.iIndepFun
      (fun (j : ℤ) (ω : Ω) => X j ω - ∫ ω', X j ω' ∂P) P :=
    hindep.comp (fun (j : ℤ) (x : ℝ) => x - ∫ ω', X j ω' ∂P)
      (fun _ => measurable_id.sub measurable_const)
  have hYtail : ∀ j, IsBigO P (gammaSigma 2)
      (fun ω => X j ω - ∫ ω', X j ω' ∂P) (cesaroCenterConst 2 * K) := fun j =>
    centered_isBigO_gammaSigma_moment hσ hK (hmeas j).aemeasurable (hX j)
  have hYmean : ∀ j, ∫ ω, (X j ω - ∫ ω', X j ω' ∂P) ∂P = 0 := by
    intro j
    rw [MeasureTheory.integral_sub (hint j) (MeasureTheory.integrable_const _)]
    simp
  refine ⟨fun ω => cesaroAvg (fun j => X j ω - ∫ ω', X j ω' ∂P) n m, ?_, ?_⟩
  · intro ω
    exact cesaroAvg_le_add_cesaroAvg_sub (f := fun j => X j ω)
      (g := fun j => ∫ ω', X j ω' ∂P) hnm hmean
  · have hbig := isBigO_cesaroAvg_of_iIndepFun_centered (P := P)
      (Y := fun (j : ℤ) (ω : Ω) => X j ω - ∫ ω', X j ω' ∂P) hKc hYindep hYmeas hYtail
      hYmean hnm
    have hcst : gammaSigmaIndependentSumConst 2 * (cesaroCenterConst 2 * K)
          * (((m - n + 1 : ℤ) : ℝ)) ^ (-(1 : ℝ) / 2)
        = cesaroEngineConst * K * (((m - n + 1 : ℤ) : ℝ)) ^ (-(1 : ℝ) / 2) := by
      simp only [cesaroEngineConst]; ring
    rwa [hcst] at hbig

/-- **The Cesàro engine with an additive boundary/tail term.** This is the exact
shape produced by each of the paper's Steps 1--3 after the deterministic
rearrangement: `D ≤ a · avsum X + (m − n + 1)⁻¹ · T` with `T ≤ O_{Γ₂}(b)` gives
`D ≤ a μ₀ + O_{Γ₂}( C (aK + b)(m − n + 1)^{-1/2} )`. -/
theorem cesaroAvg_isBigO_of_iIndepFun_with_tail [IsProbabilityMeasure P]
    (X : ℤ → Ω → ℝ) (T Dbar : Ω → ℝ) {K mu0 a b : ℝ}
    (hK : 0 < K) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hindep : ProbabilityTheory.iIndepFun X P)
    (hmeas : ∀ j, Measurable (X j))
    (hX : ∀ j, IsBigO P (gammaSigma 2) (X j) K)
    (hmean : ∀ j, ∫ ω, X j ω ∂P ≤ mu0)
    (hT : IsBigO P (gammaSigma 2) T b)
    (n m : ℤ) (hnm : n ≤ m)
    (hdom : ∀ ω, Dbar ω ≤ a * cesaroAvg (fun j => X j ω) n m
                    + (1 / (((m - n + 1 : ℤ) : ℝ))) * T ω) :
    ∃ Xdet Xfluc : Ω → ℝ,
      (∀ ω, Dbar ω ≤ Xdet ω + Xfluc ω) ∧
      (∀ ω, Xdet ω ≤ a * mu0) ∧
      IsBigO P (gammaSigma 2) Xfluc
        (cesaroTailEngineConst * (a * K + b)
          * (((m - n + 1 : ℤ) : ℝ)) ^ (-(1 : ℝ) / 2)) := by
  obtain ⟨Xf, hXfpt, hXfbig⟩ :=
    cesaroAvg_isBigO_of_iIndepFun (P := P) X hK hindep hmeas hX hmean n m hnm
  have hc1 : (1 : ℝ) ≤ ((m - n + 1 : ℤ) : ℝ) := one_le_window hnm
  have hcpos : (0 : ℝ) < ((m - n + 1 : ℤ) : ℝ) := window_pos hnm
  have hpow_nonneg : (0 : ℝ) ≤ (((m - n + 1 : ℤ) : ℝ)) ^ (-(1 : ℝ) / 2) :=
    Real.rpow_nonneg hcpos.le _
  refine ⟨fun _ => a * mu0,
    fun ω => a * Xf ω + (1 / (((m - n + 1 : ℤ) : ℝ))) * T ω, ?_, fun _ => le_rfl, ?_⟩
  · intro ω
    have hmul : a * cesaroAvg (fun j => X j ω) n m ≤ a * (mu0 + Xf ω) :=
      mul_le_mul_of_nonneg_left (hXfpt ω) ha
    have hexp : a * (mu0 + Xf ω) = a * mu0 + a * Xf ω := by ring
    linarith only [hdom ω, hmul, hexp.le, hexp.ge]
  · -- the `Γ₂` envelope
    have h1 : IsBigO P (gammaSigma 2) (fun ω => a * Xf ω)
        (a * (cesaroEngineConst * K * (((m - n + 1 : ℤ) : ℝ)) ^ (-(1 : ℝ) / 2))) :=
      IsBigO.const_mul ha hXfbig
    have h2 : IsBigO P (gammaSigma 2) (fun ω => (1 / (((m - n + 1 : ℤ) : ℝ))) * T ω)
        ((1 / (((m - n + 1 : ℤ) : ℝ))) * b) :=
      IsBigO.const_mul (by positivity) hT
    have hle : (1 / (((m - n + 1 : ℤ) : ℝ))) * b
        ≤ b * (((m - n + 1 : ℤ) : ℝ)) ^ (-(1 : ℝ) / 2) := by
      have hmono := inv_le_rpow_neg_half hc1
      have hstep := mul_le_mul_of_nonneg_right hmono hb
      linarith only [hstep]
    have h2' := IsBigO.mono_scale h2 hle
    have hA1 : (0 : ℝ) ≤ a * (cesaroEngineConst * K
        * (((m - n + 1 : ℤ) : ℝ)) ^ (-(1 : ℝ) / 2)) := by
      have hbase : (0 : ℝ) ≤ cesaroEngineConst * K :=
        mul_nonneg cesaroEngineConst_pos.le hK.le
      exact mul_nonneg ha (mul_nonneg hbase hpow_nonneg)
    have hA2 : (0 : ℝ) ≤ b * (((m - n + 1 : ℤ) : ℝ)) ^ (-(1 : ℝ) / 2) :=
      mul_nonneg hb hpow_nonneg
    have h3 := isBigO_gammaSigma_add2' (μ := P) (by norm_num : (0 : ℝ) < 2) hA1 hA2 h1 h2'
    refine IsBigO.mono_scale h3 ?_
    -- the constant comparison
    have hL : (0 : ℝ) ≤ (1 + Real.log 2) ^ (2 : ℝ)⁻¹ :=
      (Real.rpow_pos_of_pos one_add_log_two_pos _).le
    have hdiff : cesaroTailEngineConst * (a * K + b)
          * (((m - n + 1 : ℤ) : ℝ)) ^ (-(1 : ℝ) / 2)
        - (1 + Real.log 2) ^ (2 : ℝ)⁻¹ *
            (a * (cesaroEngineConst * K * (((m - n + 1 : ℤ) : ℝ)) ^ (-(1 : ℝ) / 2))
              + b * (((m - n + 1 : ℤ) : ℝ)) ^ (-(1 : ℝ) / 2))
        = (1 + Real.log 2) ^ (2 : ℝ)⁻¹ * (((m - n + 1 : ℤ) : ℝ)) ^ (-(1 : ℝ) / 2)
            * (a * K + cesaroEngineConst * b) := by
      simp only [cesaroTailEngineConst]; ring
    have hnn : (0 : ℝ) ≤ (1 + Real.log 2) ^ (2 : ℝ)⁻¹
        * (((m - n + 1 : ℤ) : ℝ)) ^ (-(1 : ℝ) / 2)
        * (a * K + cesaroEngineConst * b) := by
      have h5 : (0 : ℝ) ≤ a * K + cesaroEngineConst * b :=
        add_nonneg (mul_nonneg ha hK.le) (mul_nonneg cesaroEngineConst_pos.le hb)
      exact mul_nonneg (mul_nonneg hL hpow_nonneg) h5
    linarith only [hdiff.le, hdiff.ge, hnn]

end Engine

end

end Algsuperdiff.Probability
