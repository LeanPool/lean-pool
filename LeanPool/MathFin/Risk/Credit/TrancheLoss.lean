/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Risk.Credit.VasicekIRB
public import LeanPool.MathFin.Probability.Gaussian.BivariateNormalCDF
public import Mathlib.MeasureTheory.Order.Group.Lattice

/-!
# Tranche losses in the large homogeneous portfolio

A CDO tranche with attachment `a` and detachment `d > a` absorbs the slice `[a, d]` of the
portfolio loss fraction `L`. Its loss, as a fraction of the tranche notional, is
`((L − a)⁺ − (L − d)⁺)/(d − a)` (`tranchePayoff`; S. Bagaria, *Notes on Fixed Income
Derivative Pricing* (lecture notes), ch. 18, eq. 18.9; Hull ch. 25).
So every tranche expected loss is `(d − a)⁻¹` times a difference of two stop-loss expectations
`E[(L − K)⁺]`. That decomposition is not stated for a general `L`; it is used only inside the
proof of the LHP result `integral_tranchePayoff_oneFactorPD` below.

In the **large homogeneous portfolio** (LHP) limit of the one-factor Gaussian threshold model,
the loss fraction is the conditional default probability `p(F) = Φ((Φ⁻¹(π) − √ρ F)/√(1 − ρ))` of
the standard normal systematic factor `F` (`tendsto_oneFactorLossFraction_ae` in
`Risk/Credit/VasicekIRB.lean`). For it, with `π, K ∈ (0, 1)` and `0 ≤ ρ < 1`, the stop-loss
expectation has the closed form

  `E[(p(F) − K)⁺] = π − N₂(Φ⁻¹(π), Φ⁻¹(K); √(1 − ρ))`

(`integral_posPart_oneFactorPD_sub`; O. Vasicek, "Loan portfolio value", *Risk* 15(12) (2002),
the unnumbered stop-loss price — Hull's own tranche-pricing route, ch. 25 eqs. 25.9–25.11, is the
discretized expected-tranche-principal recursion and never states this closed form), where
`N₂(·, ·; r)` is the standard bivariate normal CDF with correlation `r` (`bivariateNormalCDF`,
`Probability/Gaussian/BivariateNormalCDF.lean`). The proof writes `K = Φ(k)` and, with `ε` a
standard normal independent of `F`, reads `(Φ(T) − Φ(k))⁺` as the conditional probability of
`{k < ε ≤ T}` given `F`. Fubini on `N(0,1) ⊗ N(0,1)` turns the expectation into
`P(√ρ F + √(1 − ρ) ε ≤ Φ⁻¹(π)) − P(√ρ F + √(1 − ρ) ε ≤ Φ⁻¹(π), ε ≤ k)`. The first term is `π`;
the second is `N₂` at correlation `√(1 − ρ)`, since `√(1 − (√(1 − ρ))²) = √ρ`.

## Main definitions

* `tranchePayoff`: the loss `((L − a)⁺ − (L − d)⁺)/(d − a)` of the tranche `[a, d]` as a fraction
  of its notional, when the portfolio loss fraction is `L`.

## Main results

* `tranchePayoff_mem_Icc`, `monotone_tranchePayoff`: for `a < d` the tranche loss
  lies in `[0, 1]` and is nondecreasing in the portfolio loss.
* `integral_posPart_oneFactorPD_sub`: the LHP stop-loss closed form.
* `integral_tranchePayoff_oneFactorPD`: the LHP tranche expected loss as a difference of two
  bivariate normal CDFs.
* `tendsto_integral_tranchePayoff_oneFactorLossFraction`: the finite-pool tranche expected loss
  converges to the LHP closed form.

## References

* [J. C. Hull, *Options, Futures, and Other Derivatives*][Hull], ch. 25
* [O. Vasicek, *Loan portfolio value*][Vasicek2002]

## Tags

CDO tranche, tranche expected loss, large homogeneous portfolio, attachment and detachment,
stop-loss, Vasicek model, bivariate normal, structured credit, MSC 91G40, MSC 60E05, JEL G24,
JEL G32
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Set Filter Topology

/-! ### The tranche payoff -/

/-- The loss of the tranche `[a, d]` as a fraction of its notional when the portfolio loss
fraction is `L`: `((L − a)⁺ − (L − d)⁺)/(d − a)`. -/
noncomputable def tranchePayoff (a d L : ℝ) : ℝ :=
  ((L - a)⁺ - (L - d)⁺) / (d - a)

/-- For `a < d`, the tranche loss lies in `[0, 1]`. -/
theorem tranchePayoff_mem_Icc {a d : ℝ} (had : a < d) (L : ℝ) :
    tranchePayoff a d L ∈ Icc 0 1 := by
  have hda : 0 < d - a := sub_pos.2 had
  rw [tranchePayoff, mem_Icc, div_le_one hda]
  refine ⟨div_nonneg ?_ hda.le, ?_⟩ <;> simp only [posPart_def] <;>
    rcases max_cases (L - a) 0 with h | h <;> rcases max_cases (L - d) 0 with h' | h' <;>
    linarith [h.1, h'.1, h.2, h'.2]

/-- For `a < d`, the tranche loss is nondecreasing (`Monotone`) in the portfolio loss; it is
constant outside `[a, d]`. -/
theorem monotone_tranchePayoff {a d : ℝ} (had : a < d) : Monotone (tranchePayoff a d) := by
  intro L L' hL
  refine div_le_div_of_nonneg_right ?_ (sub_pos.2 had).le
  simp only [posPart_def]
  rcases max_cases (L - a) 0 with h | h <;> rcases max_cases (L - d) 0 with h' | h' <;>
    rcases max_cases (L' - a) 0 with g | g <;> rcases max_cases (L' - d) 0 with g' | g' <;>
    linarith [h.1, h'.1, h.2, h'.2, g.1, g'.1, g.2, g'.2]

/-! ### The LHP stop-loss closed form -/

/-- **The LHP stop-loss closed form** (Vasicek 2002, the unnumbered stop-loss price; the
one-factor model itself is Hull ch. 25): for a standard normal systematic factor, `π, K ∈ (0, 1)`
and `0 ≤ ρ < 1`, the large-pool loss fraction
`p(F) = Φ((Φ⁻¹(π) − √ρ F)/√(1 − ρ))` satisfies
`E[(p(F) − K)⁺] = π − N₂(Φ⁻¹(π), Φ⁻¹(K); √(1 − ρ))`. -/
theorem integral_posPart_oneFactorPD_sub {π ρ K : ℝ} (hπ : π ∈ Ioo 0 1) (hρ0 : 0 ≤ ρ)
    (hρ1 : ρ < 1) (hK : K ∈ Ioo 0 1) :
    ∫ f, (oneFactorPD π ρ f - K)⁺ ∂gaussianReal 0 1 =
      π - bivariateNormalCDF (PhiInv π) (PhiInv K) √(1 - ρ) := by
  set μ := gaussianReal 0 1
  set k := PhiInv K
  set T : ℝ → ℝ := fun f ↦ (PhiInv π - √ρ * f) / √(1 - ρ)
  have hT : Measurable T := by fun_prop
  -- the stop-loss payoff is the conditional probability of `{k < ε ≤ T(F)}`
  have hpay (f : ℝ) : (oneFactorPD π ρ f - K)⁺ = μ.real (Prod.mk f ⁻¹'
      {p : ℝ × ℝ | k < p.2 ∧ p.2 ≤ T p.1}) := by
    rw [oneFactorPD, ← Phi_PhiInv hK, posPart_Phi_sub_Phi]; rfl
  set S : Set (ℝ × ℝ) := {p | k < p.2 ∧ p.2 ≤ T p.1}
  have hS : MeasurableSet S :=
    (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd (hT.comp measurable_fst))
  -- Fubini on `N(0,1) ⊗ N(0,1)`
  have hfub : ∫ f, (oneFactorPD π ρ f - K)⁺ ∂μ = (μ.prod μ).real S := by
    simp_rw [hpay]
    rw [measureReal_def, Measure.prod_apply hS, integral_eq_lintegral_of_nonneg_ae
      (ae_of_all _ fun _ ↦ measureReal_nonneg)
      (measurable_measure_prodMk_left hS).ennreal_toReal.aestronglyMeasurable]
    congr 1
    exact lintegral_congr fun f ↦ ENNReal.ofReal_toReal (measure_ne_top _ _)
  -- the default event `{√ρ F + √(1 − ρ) ε ≤ Φ⁻¹(π)}` splits off the event `{ε ≤ k}`
  set A : Set (ℝ × ℝ) := {p | √ρ * p.1 + √(1 - ρ) * p.2 ≤ PhiInv π}
  have hA : MeasurableSet A := measurableSet_le (by fun_prop) measurable_const
  have hSA : S = A \ (A ∩ {p | p.2 ≤ k}) := by
    ext p
    simp only [S, A, T, mem_ofPred_eq, Set.mem_sdiff, mem_inter_iff,
      oneFactor_asset_le_iff hρ1, not_and, not_le]
    tauto
  have hdef : (μ.prod μ).real A = π := by
    have hind : IndepFun Prod.fst Prod.snd (μ.prod μ) :=
      indepFun_prod (X := id) (Y := id) measurable_id measurable_id
    exact oneFactor_measureReal_default (P := μ.prod μ) (F := Prod.fst) (e := Prod.snd)
      ⟨measurable_fst.aemeasurable, by simp [μ]⟩ ⟨measurable_snd.aemeasurable, by simp [μ]⟩
      hind hπ hρ0 hρ1.le
  have hN₂ : (μ.prod μ).real (A ∩ {p | p.2 ≤ k}) =
      bivariateNormalCDF (PhiInv π) k √(1 - ρ) := by
    rw [bivariateNormalCDF, stdNormalPair, Real.sq_sqrt (sub_nonneg.2 hρ1.le), sub_sub_cancel]
    congr 1
    ext p
    simp only [A, mem_inter_iff, mem_ofPred_eq]
    rw [add_comm (√(1 - ρ) * p.2)]
  rw [hfub, hSA, measureReal_sdiff inter_subset_left (hA.inter (measurableSet_le measurable_snd
    measurable_const)), hdef, hN₂]

/-- **The LHP tranche expected loss** for attachment `a` and detachment `d` with
`0 < a < d < 1`, `π ∈ (0, 1)` and `0 ≤ ρ < 1`, and `F` standard normal:
`E[tranchePayoff a d (p(F))]` is
`(N₂(Φ⁻¹(π), Φ⁻¹(d); √(1 − ρ)) − N₂(Φ⁻¹(π), Φ⁻¹(a); √(1 − ρ)))/(d − a)`. -/
theorem integral_tranchePayoff_oneFactorPD {π ρ a d : ℝ} (hπ : π ∈ Ioo 0 1) (hρ0 : 0 ≤ ρ)
    (hρ1 : ρ < 1) (ha : 0 < a) (had : a < d) (hd : d < 1) :
    ∫ f, tranchePayoff a d (oneFactorPD π ρ f) ∂gaussianReal 0 1 =
      (bivariateNormalCDF (PhiInv π) (PhiInv d) √(1 - ρ) -
        bivariateNormalCDF (PhiInv π) (PhiInv a) √(1 - ρ)) / (d - a) := by
  have hint {K : ℝ} (hK : 0 ≤ K) :
      Integrable (fun f ↦ (oneFactorPD π ρ f - K)⁺) (gaussianReal 0 1) :=
    .of_bound ((measurable_oneFactorPD π ρ).sub_const K).posPart.aestronglyMeasurable 1
      (ae_of_all _ fun f ↦ by
        rw [Real.norm_of_nonneg (posPart_nonneg _), posPart_def]
        exact max_le (by linarith [(Phi_mem_Ioo ((PhiInv π - √ρ * f) / √(1 - ρ))).2,
          show oneFactorPD π ρ f = Phi ((PhiInv π - √ρ * f) / √(1 - ρ)) from rfl]) zero_le_one)
  simp only [tranchePayoff]
  rw [integral_div, integral_sub (hint ha.le) (hint (ha.trans had).le),
    integral_posPart_oneFactorPD_sub hπ hρ0 hρ1 ⟨ha, had.trans hd⟩,
    integral_posPart_oneFactorPD_sub hπ hρ0 hρ1 ⟨ha.trans had, hd⟩]
  ring

/-! ### From the finite pool to the LHP limit -/

/-- The tranche payoff is continuous in the portfolio loss. -/
lemma continuous_tranchePayoff (a d : ℝ) : Continuous (tranchePayoff a d) := by
  unfold tranchePayoff
  fun_prop

/-- **The finite-pool tranche expected loss converges to the LHP closed form.** With `F` and the
`εᵢ` standard normals, the `εᵢ` pairwise independent, the expected loss of the tranche `[a, d]`
on the first `m` obligors of the one-factor Gaussian threshold model converges, as `m → ∞`, to
`(N₂(Φ⁻¹(π), Φ⁻¹(d); √(1 − ρ)) − N₂(Φ⁻¹(π), Φ⁻¹(a); √(1 − ρ)))/(d − a)`, for `π ∈ (0, 1)`,
`0 ≤ ρ < 1` and `0 < a < d < 1`. Independence of `F` from the `εᵢ` is not assumed. The proof is
dominated convergence (the tranche loss lies in `[0, 1]`) along the almost-sure large-portfolio
limit. -/
theorem tendsto_integral_tranchePayoff_oneFactorLossFraction {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] {π ρ a d : ℝ} {F : Ω → ℝ} {ε : ℕ → Ω → ℝ}
    (hF : HasLaw F (gaussianReal 0 1) P) (hε : ∀ i, HasLaw (ε i) (gaussianReal 0 1) P)
    (hind : Pairwise fun i j ↦ ε i ⟂ᵢ[P] ε j) (hπ : π ∈ Ioo 0 1) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (ha : 0 < a) (had : a < d) (hd : d < 1) :
    Tendsto (fun m ↦ ∫ ω, tranchePayoff a d (oneFactorLossFraction π ρ F ε m ω) ∂P) atTop
      (𝓝 ((bivariateNormalCDF (PhiInv π) (PhiInv d) √(1 - ρ) -
        bivariateNormalCDF (PhiInv π) (PhiInv a) √(1 - ρ)) / (d - a))) := by
  have hcont := continuous_tranchePayoff a d
  rw [← integral_tranchePayoff_oneFactorPD hπ hρ0 hρ1 ha had hd,
    ← hF.integral_comp (f := fun x ↦ tranchePayoff a d (oneFactorPD π ρ x))
      (hcont.measurable.comp (measurable_oneFactorPD π ρ)).aestronglyMeasurable]
  refine tendsto_integral_of_dominated_convergence (fun _ ↦ 1)
    (fun m ↦ (hcont.measurable.comp_aemeasurable (aemeasurable_oneFactorLossFraction
      hF.aemeasurable (fun i ↦ (hε i).aemeasurable) m)).aestronglyMeasurable)
    (integrable_const 1) (fun m ↦ ae_of_all _ fun ω ↦ ?_) ?_
  · have h := tranchePayoff_mem_Icc had (oneFactorLossFraction π ρ F ε m ω)
    rw [Real.norm_of_nonneg h.1]
    exact h.2
  · filter_upwards [tendsto_oneFactorLossFraction_ae hε hind hρ1 F] with ω hω
    exact (hcont.tendsto _).comp hω

end MathFin
