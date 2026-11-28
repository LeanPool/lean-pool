/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Probability.Laws.QuantileConvergence
public import LeanPool.MathFin.Risk.Credit.BernoulliMixture
public import LeanPool.MathFin.Risk.ValueAtRisk

/-!
# The Basel IRB formula as the quantile of the large-portfolio loss

In the one-factor Gaussian threshold model of `Risk/Credit/BernoulliMixture.lean`, obligor `i`
defaults when its asset value `√ρ F + √(1 − ρ) εᵢ` falls below `Φ⁻¹(π)`. The systematic factor `F`
is standard normal and the idiosyncratic terms `εᵢ` are standard normals. The **loss fraction**
of the first `m` obligors is `L_m = (1/m) #{i < m | obligor i defaults}`
(`oneFactorLossFraction`). This file proves the theorem behind the internal-ratings-based (IRB)
capital formula of Basel II/III (Vasicek 2002; Gordy 2003, the asymptotic single-risk-factor
model):

  `VaR_α(L_m) → Φ((Φ⁻¹(π) + √ρ Φ⁻¹(α)) / √(1 − ρ))`   as `m → ∞`

(`tendsto_valueAtRisk_oneFactorLossFraction`). The right side is `asrfQuantile π ρ α`, the IRB
worst-case default rate at confidence `α`. Basel sets `α = 0.999`. The rest of the regulatory
capital formula is not modelled here: loss given default, the subtraction of expected loss, the
maturity adjustment and the 12.5 risk-weight scaling.

The proof has three steps.

1. **The large-portfolio limit** (`tendsto_oneFactorLossFraction_ae`): `L_m → p(F)` almost surely,
   where `p(f) = Φ((Φ⁻¹(π) − √ρ f)/√(1 − ρ))` is the conditional default probability. Obligor `i`
   defaults exactly when `εᵢ ≤ T = (Φ⁻¹(π) − √ρ F)/√(1 − ρ)`, so `L_m` is the empirical CDF of the
   `εᵢ` at the random point `T`. By the strong law for the empirical CDF
   (`Probability/Laws/QuantileConvergence.lean`) it converges to `Φ(T) = p(F)`. Only pairwise
   independence of the idiosyncratic terms enters. Independence of `F` from them is needed for the
   finite-portfolio mixture formulas (`oneFactor_measureReal_iInter_default`) but not for the
   limit.
2. **The quantile of the limit** (`valueAtRisk_oneFactorPD`). `p(F) = h(−F)` with
   `h(z) = Φ((Φ⁻¹(π) + √ρ z)/√(1 − ρ))` continuous and increasing, and `−F` is standard normal. So
   `VaR_α(p(F)) = h(Φ⁻¹(α))`, by equivariance of VaR (`valueAtRisk_comp`).
3. **VaR passes to the limit** (`tendsto_valueAtRisk_of_tendsto_ae`). The `α`-quantile of `p(F)`
   is strict (`lt_measureReal_oneFactorPD_le`): the law of `p(F)` has no flat stretch at level `α`.
   So the quantiles of the `L_m` converge by `tendsto_quantile_of_tendsto_ae`.

The statements hold for every `π` and every `ρ < 1` (with Lean's `√ρ = 0` for `ρ < 0`). The credit
reading needs `π ∈ (0, 1)`, where `π` is each obligor's default probability
(`oneFactor_measureReal_default`), and `ρ ∈ [0, 1)`, where `ρ` is the asset correlation.

## Main definitions

* `oneFactorLossFraction`: the fraction of the first `m` obligors of the one-factor Gaussian
  threshold model whose asset value `√ρ F + √(1 − ρ) εᵢ` is at most `Φ⁻¹(π)`.
* `asrfQuantile`: the asymptotic single-risk-factor quantile
  `Φ((Φ⁻¹(π) + √ρ Φ⁻¹(α)) / √(1 − ρ))`, the Basel IRB worst-case default rate at confidence `α`.

## Main results

* `tendsto_valueAtRisk_of_tendsto_ae`: VaR converges along almost-sure convergence to a loss with
  a strict quantile.
* `oneFactorLossFraction_eq_empiricalCDF`: the loss fraction is an empirical CDF at a random point.
* `tendsto_oneFactorLossFraction_ae`: `L_m → p(F)` almost surely.
* `valueAtRisk_oneFactorPD`: `VaR_α(p(F)) = asrfQuantile π ρ α`.
* `tendsto_valueAtRisk_oneFactorLossFraction`: **the IRB formula is the limit of `VaR_α(L_m)`**.

## References

* [Gordy (2003)][Gordy2003]
* [A. J. McNeil, R. Frey and P. Embrechts, *Quantitative Risk Management: Concepts, Techniques and
  Tools*][McNeilFreyEmbrechts], Section 11.3.2
* [*QRM Exercise Book*][QRMExerciseBook], Ex. 11.16, 11.17
* [O. Vasicek, *Loan portfolio value*][Vasicek2002]

## Tags

Basel IRB formula, Vasicek model, asymptotic single risk factor, Gordy, large portfolio limit,
worst-case default rate, regulatory capital, one-factor model, MSC 91G40, MSC 60F15, JEL G28,
JEL G32
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Set Filter Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {π ρ α : ℝ}

/-! ### VaR along almost-sure convergence -/

/-- **VaR is continuous along almost-sure convergence** to a loss whose `α`-quantile is strict,
meaning every level above `VaR_α(Y)` is reached with probability more than `α`. -/
theorem tendsto_valueAtRisk_of_tendsto_ae {X : ℕ → Ω → ℝ} {Y : Ω → ℝ}
    (hX : ∀ n, AEMeasurable (X n) P) (hY : AEMeasurable Y P)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n ↦ X n ω) atTop (𝓝 (Y ω))) (hα : α ∈ Ioo 0 1)
    (hstrict : ∀ x, valueAtRisk Y P α < x → α < P.real {ω | Y ω ≤ x}) :
    Tendsto (fun n ↦ valueAtRisk (X n) P α) atTop (𝓝 (valueAtRisk Y P α)) :=
  tendsto_quantile_of_tendsto_ae hX hY hlim hα fun x hx ↦ by
    rw [cdf_map_eq_measureReal hY]
    exact hstrict x hx

/-! ### The loss fraction of the one-factor model -/

/-- The **loss fraction** of the first `m` obligors of the one-factor Gaussian threshold model: the
fraction of them whose asset value `√ρ F + √(1 − ρ) εᵢ` is at most `Φ⁻¹(π)`. -/
noncomputable def oneFactorLossFraction (π ρ : ℝ) (F : Ω → ℝ) (ε : ℕ → Ω → ℝ) (m : ℕ)
    (ω : Ω) : ℝ :=
  (m : ℝ)⁻¹ * ∑ i ∈ Finset.range m, (Iic (PhiInv π)).indicator 1 (√ρ * F ω + √(1 - ρ) * ε i ω)

/-- The **asymptotic single-risk-factor quantile**, the Basel IRB worst-case default rate at
confidence `α`: `Φ((Φ⁻¹(π) + √ρ Φ⁻¹(α))/√(1 − ρ))`. -/
noncomputable def asrfQuantile (π ρ α : ℝ) : ℝ :=
  Phi ((PhiInv π + √ρ * PhiInv α) / √(1 - ρ))

omit [IsProbabilityMeasure P] in
lemma aemeasurable_oneFactorLossFraction {F : Ω → ℝ} {ε : ℕ → Ω → ℝ} (hF : AEMeasurable F P)
    (hε : ∀ i, AEMeasurable (ε i) P) (m : ℕ) :
    AEMeasurable (oneFactorLossFraction π ρ F ε m) P := by
  have hdef (i : ℕ) : AEMeasurable
      (fun ω ↦ (Iic (PhiInv π)).indicator (1 : ℝ → ℝ) (√ρ * F ω + √(1 - ρ) * ε i ω)) P :=
    (measurable_const.indicator measurableSet_Iic).comp_aemeasurable
      ((hF.const_mul _).add ((hε i).const_mul _))
  exact (Finset.aemeasurable_fun_sum _ fun i _ ↦ hdef i).const_mul _

omit [IsProbabilityMeasure P] in
/-- The loss fraction is the empirical CDF of the idiosyncratic terms at the random threshold
`(Φ⁻¹(π) − √ρ F)/√(1 − ρ)`. -/
lemma oneFactorLossFraction_eq_empiricalCDF (hρ : ρ < 1) (F : Ω → ℝ) (ε : ℕ → Ω → ℝ) (m : ℕ)
    (ω : Ω) :
    oneFactorLossFraction π ρ F ε m ω = empiricalCDF ε m ω ((PhiInv π - √ρ * F ω) / √(1 - ρ)) := by
  refine congrArg _ (Finset.sum_congr rfl fun i _ ↦ ?_)
  simp only [indicator_apply, mem_Iic, oneFactor_asset_le_iff hρ, Pi.one_apply]

/-- **The large-portfolio limit**: the loss fraction converges almost surely to the conditional
default probability `p(F)`. The idiosyncratic terms are pairwise independent standard normals;
the systematic factor `F` is arbitrary. -/
theorem tendsto_oneFactorLossFraction_ae {ε : ℕ → Ω → ℝ}
    (hε : ∀ i, HasLaw (ε i) (gaussianReal 0 1) P) (hind : Pairwise fun i j ↦ ε i ⟂ᵢ[P] ε j)
    (hρ : ρ < 1) (F : Ω → ℝ) :
    ∀ᵐ ω ∂P, Tendsto (fun m ↦ oneFactorLossFraction π ρ F ε m ω) atTop
      (𝓝 (oneFactorPD π ρ (F ω))) := by
  filter_upwards
      [tendsto_empiricalCDF_ae hε hind (by rw [cdf_gaussianReal_zero_one]; exact continuous_Phi)]
    with ω hω
  simp_rw [oneFactorLossFraction_eq_empiricalCDF hρ]
  simpa only [cdf_gaussianReal_zero_one, oneFactorPD] using
    hω ((PhiInv π - √ρ * F ω) / √(1 - ρ))

/-! ### The quantile of the limit -/

/-- The increasing profile `h(z) = Φ((Φ⁻¹(π) + √ρ z)/√(1 − ρ))` with `p(f) = h(−f)`. -/
private lemma monotone_asrfProfile (hρ : ρ < 1) :
    Monotone fun z ↦ Phi ((PhiInv π + √ρ * z) / √(1 - ρ)) :=
  strictMono_Phi.monotone.comp fun _ _ hzw ↦ by
    have := (Real.sqrt_pos.2 (sub_pos.2 hρ)).le
    gcongr

private lemma continuous_asrfProfile : Continuous fun z ↦ Phi ((PhiInv π + √ρ * z) / √(1 - ρ)) :=
  continuous_Phi.comp (by fun_prop)

private lemma oneFactorPD_eq (f : ℝ) :
    oneFactorPD π ρ f = Phi ((PhiInv π + √ρ * -f) / √(1 - ρ)) := by
  rw [oneFactorPD, mul_neg, ← sub_eq_add_neg]

/-- **The quantile of the limiting loss**: for a standard normal factor `F`,
`VaR_α(p(F)) = Φ((Φ⁻¹(π) + √ρ Φ⁻¹(α))/√(1 − ρ))`. The loss `p(F)` is the increasing continuous
profile `h` applied to the standard normal `−F`, and VaR commutes with `h`. -/
theorem valueAtRisk_oneFactorPD {F : Ω → ℝ} (hF : HasLaw F (gaussianReal 0 1) P) (hρ : ρ < 1)
    (hα : α ∈ Ioo 0 1) :
    valueAtRisk (fun ω ↦ oneFactorPD π ρ (F ω)) P α = asrfQuantile π ρ α := by
  have hG : HasLaw (fun ω ↦ -F ω) (gaussianReal 0 1) P := by
    have h := gaussianReal_neg hF
    rw [neg_zero] at h
    exact h
  simp_rw [oneFactorPD_eq]
  rw [valueAtRisk_comp (h := fun z ↦ Phi ((PhiInv π + √ρ * z) / √(1 - ρ))) hG.aemeasurable
    (monotone_asrfProfile hρ) continuous_asrfProfile.lowerSemicontinuous hα,
    valueAtRisk_eq_quantile hG]
  rfl

/-- **The `α`-quantile of the limiting loss is strict**: every level above
`asrfQuantile π ρ α` is reached by `p(F)` with probability more than `α`. -/
theorem lt_measureReal_oneFactorPD_le {F : Ω → ℝ} (hF : HasLaw F (gaussianReal 0 1) P)
    (hρ : ρ < 1) (hα : α ∈ Ioo 0 1) {x : ℝ} (hx : asrfQuantile π ρ α < x) :
    α < P.real {ω | oneFactorPD π ρ (F ω) ≤ x} := by
  -- continuity of the profile at `Φ⁻¹(α)` gives `z > Φ⁻¹(α)` whose image is still below `x`
  obtain ⟨z, hzx, hz⟩ := (((continuous_asrfProfile (π := π) (ρ := ρ)).tendsto (PhiInv α)).eventually
    (gt_mem_nhds hx) |>.filter_mono nhdsWithin_le_nhds |>.and
      (self_mem_nhdsWithin (s := Ioi (PhiInv α)))).exists
  have hG : HasLaw (fun ω ↦ -F ω) (gaussianReal 0 1) P := by
    have h := gaussianReal_neg hF
    rw [neg_zero] at h
    exact h
  have hNz : P.real {ω | -F ω ≤ z} = Phi z := by
    rw [hG.measureReal_eq (p := (· ≤ z)) measurableSet_Iic,
      ← cdf_gaussianReal_zero_one, cdf_eq_real]
    rfl
  calc α = Phi (PhiInv α) := (Phi_PhiInv hα).symm
    _ < Phi z := strictMono_Phi hz
    _ = P.real {ω | -F ω ≤ z} := hNz.symm
    _ ≤ P.real {ω | oneFactorPD π ρ (F ω) ≤ x} := measureReal_mono fun ω hω ↦ by
      rw [mem_ofPred_eq, oneFactorPD_eq]
      exact (monotone_asrfProfile hρ hω).trans hzx.le

/-! ### The IRB formula as a limit theorem -/

/-- **The Basel IRB formula is the quantile of the large-portfolio loss** (Vasicek 2002;
Gordy 2003). In the one-factor Gaussian threshold model with a standard normal factor `F` and
pairwise independent standard normal idiosyncratic terms, the value-at-risk of the loss fraction
of the first `m` obligors converges, as `m → ∞`, to
`Φ((Φ⁻¹(π) + √ρ Φ⁻¹(α))/√(1 − ρ))`. -/
theorem tendsto_valueAtRisk_oneFactorLossFraction {F : Ω → ℝ} {ε : ℕ → Ω → ℝ}
    (hF : HasLaw F (gaussianReal 0 1) P) (hε : ∀ i, HasLaw (ε i) (gaussianReal 0 1) P)
    (hind : Pairwise fun i j ↦ ε i ⟂ᵢ[P] ε j) (hρ : ρ < 1) (hα : α ∈ Ioo 0 1) :
    Tendsto (fun m ↦ valueAtRisk (oneFactorLossFraction π ρ F ε m) P α) atTop
      (𝓝 (asrfQuantile π ρ α)) := by
  rw [← valueAtRisk_oneFactorPD hF hρ hα]
  exact tendsto_valueAtRisk_of_tendsto_ae
    (aemeasurable_oneFactorLossFraction hF.aemeasurable fun i ↦ (hε i).aemeasurable)
    ((measurable_oneFactorPD π ρ).comp_aemeasurable hF.aemeasurable)
    (tendsto_oneFactorLossFraction_ae hε hind hρ F) hα fun x hx ↦
      lt_measureReal_oneFactorPD_le hF hρ hα (by rwa [valueAtRisk_oneFactorPD hF hρ hα] at hx)

end MathFin
