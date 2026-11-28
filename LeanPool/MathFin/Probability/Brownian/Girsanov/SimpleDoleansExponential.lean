/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Probability.Brownian.BrownianMartingale
public import Mathlib.MeasureTheory.Order.Group.Lattice

/-!
# The simple Doléans exponential — the martingale foundation of adapted Girsanov (Track α)

Route-α, brick α1 (`docs/plans/2026-07-06-girsanov-track-alpha.md`). The market price
of risk `θ` of the general Girsanov theorem (`gir-thm-9.1.8`) is **adapted** (path
dependent), so the Doléans density `exp(∫θ dB − ½∫θ² ds)` has a *random* multiplier in
each partition cell. The constant-θ Wald exponential (`waldExponential_isMartingale`)
freezes each increment against a **deterministic** function of the past
(`IsFilteredPreBrownian.condExp_comp_increment_eq_const`); the adapted case needs the same
freezing against an `𝓕_r`-measurable **random** multiplier `c`.

This file proves that genuinely new estimate:

* `MathFin.condExp_exp_adapted_mul_increment` —
  `𝔼[exp(c·(X_t − X_r)) | 𝓕_r] = exp(½ c² (t − r))` a.e., for `c` `𝓕_r`-measurable and
  bounded, `r ≤ t`.

The mechanism is the **freezing lemma**: the increment `Δ = X_t − X_r` is independent of
`𝓕_r` (`hX.indep`), so the joint law of the `𝓕_r`-measurable pair `(c, ·)` and `Δ`
factorizes (`indepFun_iff_map_prod_eq_prod_map_map`), and Fubini (`integral_prod`) freezes
`c` while the inner Gaussian MGF `∫ exp(c·z) d𝒩(0,t−r) = exp(½c²(t−r))`
(`integral_exp_mul_gaussianReal_zero`) collapses the increment.

Everything else in Track α (the running exponential's martingale property α2, the simple-θ
Girsanov α3) reuses the constant-θ apparatus in `GirsanovConstantTheta.lean` once this
brick lands.

## Main definitions

* `cellExp`: the single-cell Doléans exponential over `(a, b]` with multiplier `c`, clamped to
  `[0, t]`.
* `simpleDoleansExp`: the running simple Doléans exponential over the first `N` cells of a
  partition `s` with multipliers `d`.

## Main results

* `condExp_exp_adapted_mul_increment`: the conditional MGF of a Brownian increment against a
  bounded `𝓕_r`-measurable multiplier `c`.
* `condExp_expCell_eq_one`: the normalised cell factor `exp(c·(X_t − X_r) − c²(t − r)/2)` has
  conditional expectation `1` given `𝓕_r`.
* `cellExp_isMartingale`: the single-cell exponential over `(a, b]` is a `P`-martingale for a
  bounded `𝓕_a`-measurable multiplier.
* `mul_cellExp_isMartingale`: appending one cell to a martingale frozen after `p` gives a
  martingale.
* `simpleDoleansExp_isMartingale`: for a monotone partition and uniformly bounded adapted
  multipliers, the simple Doléans exponential is a `P`-martingale.

## Tags

Doléans exponential, Girsanov theorem, exponential martingale, freezing lemma, market price of risk,
Wald exponential, MSC 60G44, MSC 60H05, MSC 91G20
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓕 : Filtration ℝ≥0 mΩ}

/-- **The freezing set-integral identity.** For a bounded `𝓕_r`-measurable multiplier `c`
and an increment `Δ` with law `𝒩(0,v)` independent of `𝓕_r`, and any `A ∈ 𝓕_r`,
`∫_A exp(c·Δ) = ∫_A exp(½ c² v)`. The `𝓕_r`-measurable `(c, 𝟙_A)` is independent of `Δ`, so
the joint law factorizes (`indepFun_iff_map_prod_eq_prod_map_map`) and Fubini
(`integral_prod`) freezes `c`, leaving the inner Gaussian MGF `∫ exp(c·z) d𝒩(0,v) =
exp(½c²v)` (`integral_exp_mul_gaussianReal_zero`). -/
lemma condExp_exp_adapted_freeze_setIntegral
    {c : Ω → ℝ} {r : ℝ≥0} (hc_frf : Measurable[(𝓕 r : MeasurableSpace Ω)] c)
    {K : ℝ} (hK : ∀ ω, |c ω| ≤ K)
    {Δ : Ω → ℝ} (hΔ_meas : Measurable Δ) {v : ℝ≥0} (hΔlaw : HasLaw Δ (gaussianReal 0 v) P)
    (hindep0 : Indep (MeasurableSpace.comap Δ (borel ℝ)) (𝓕 r) P)
    {A : Set Ω} (hA : MeasurableSet[(𝓕 r : MeasurableSpace Ω)] A) :
    ∫ ω in A, Real.exp (c ω * Δ ω) ∂P = ∫ ω in A, Real.exp ((c ω) ^ 2 * (v : ℝ) / 2) ∂P := by
  classical
  have hc_meas : Measurable c := hc_frf.mono (𝓕.le r) le_rfl
  have hA_mΩ : MeasurableSet A := (𝓕.le r) A hA
  -- Pointwise domination of `exp(c·Δ)` by two Gaussian-MGF terms (no `0 ≤ K` needed).
  have hbound : ∀ ω, Real.exp (c ω * Δ ω)
      ≤ Real.exp (K * Δ ω) + Real.exp (-K * Δ ω) := by
    intro ω
    obtain ⟨hlo, hhi⟩ := abs_le.mp (hK ω)
    rcases le_total 0 (Δ ω) with hΔ | hΔ
    · exact le_add_of_le_of_nonneg (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hhi hΔ))
        (Real.exp_nonneg _)
    · exact le_add_of_nonneg_of_le (Real.exp_nonneg _)
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_right hlo hΔ))
  have hbnd_int : Integrable (fun ω ↦ Real.exp (K * Δ ω) + Real.exp (-K * Δ ω)) P :=
    (hΔlaw.integrable_fun_comp (integrable_exp_mul_gaussianReal K)).add
      (hΔlaw.integrable_fun_comp (integrable_exp_mul_gaussianReal (-K)))
  -- The `𝓕_r`-measurable pair `Y = (c, 𝟙_A)` and the coupling `F ((cc,ind),z) = ind·exp(cc·z)`.
  set Y : Ω → ℝ × ℝ := fun ω ↦ (c ω, A.indicator (fun _ ↦ (1 : ℝ)) ω) with hYdef
  set F : (ℝ × ℝ) × ℝ → ℝ := fun p ↦ p.1.2 * Real.exp (p.1.1 * p.2) with hFdef
  have hY_meas : Measurable Y := hc_meas.prodMk (measurable_const.indicator hA_mΩ)
  have hY_frf : Measurable[(𝓕 r : MeasurableSpace Ω)] Y :=
    hc_frf.prodMk (measurable_const.indicator hA)
  have hF_meas : Measurable F :=
    (measurable_fst.snd).mul ((measurable_fst.fst.mul measurable_snd).exp)
  -- Independence of `Y` and `Δ`, hence the joint law factorizes.
  have hindepYΔ : IndepFun Y Δ P :=
    Indep.symm (indep_of_indep_of_le_right hindep0 hY_frf.comap_le)
  have hjoint : P.map (fun ω ↦ (Y ω, Δ ω)) = (P.map Y).prod (P.map Δ) :=
    (indepFun_iff_map_prod_eq_prod_map_map hY_meas.aemeasurable hΔ_meas.aemeasurable).mp hindepYΔ
  have hYΔ_aem : AEMeasurable (fun ω ↦ (Y ω, Δ ω)) P := (hY_meas.prodMk hΔ_meas).aemeasurable
  -- `F` is integrable against the joint law (dominated by the two Gaussian-MGF terms).
  have hFcomp_le : ∀ ω, ‖F (Y ω, Δ ω)‖ ≤ Real.exp (K * Δ ω) + Real.exp (-K * Δ ω) := by
    intro ω
    have hval : F (Y ω, Δ ω) = A.indicator (fun _ ↦ (1 : ℝ)) ω * Real.exp (c ω * Δ ω) := by
      simp only [hFdef, hYdef]
    rw [hval, Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
    by_cases hω : ω ∈ A
    · rw [Set.indicator_of_mem hω]; simp only [abs_one, one_mul]; exact hbound ω
    · rw [Set.indicator_apply, ite_eq_right hω, abs_zero, zero_mul]; positivity
  have hFcomp_int : Integrable (fun ω ↦ F (Y ω, Δ ω)) P :=
    Integrable.mono' hbnd_int (hF_meas.comp (hY_meas.prodMk hΔ_meas)).aestronglyMeasurable
      (Filter.Eventually.of_forall hFcomp_le)
  have hF_int_prod : Integrable F ((P.map Y).prod (P.map Δ)) := by
    rw [← hjoint, integrable_map_measure hF_meas.aestronglyMeasurable hYΔ_aem]
    exact hFcomp_int
  -- Compute the inner integral (freeze `y`, evaluate the Gaussian MGF).
  have hinner : ∀ y : ℝ × ℝ, ∫ z, F (y, z) ∂(P.map Δ)
      = y.2 * Real.exp (y.1 ^ 2 * (v : ℝ) / 2) := by
    intro y
    rw [hΔlaw.map_eq]
    have : (fun z ↦ F (y, z)) = fun z ↦ y.2 * Real.exp (y.1 * z) := by funext z; rw [hFdef]
    rw [this, integral_const_mul, integral_exp_mul_gaussianReal_zero]
  -- Chain: setIntegral → integral of `F∘(Y,Δ)` → joint law → Fubini → back.
  rw [← integral_indicator hA_mΩ, ← integral_indicator hA_mΩ]
  have hLHS : (fun ω ↦ A.indicator (fun ω ↦ Real.exp (c ω * Δ ω)) ω)
      = fun ω ↦ F (Y ω, Δ ω) := by
    funext ω; rw [hFdef, hYdef]
    by_cases hω : ω ∈ A <;> simp [hω]
  have hRHS : (fun ω ↦ A.indicator (fun ω ↦ Real.exp ((c ω) ^ 2 * (v : ℝ) / 2)) ω)
      = fun ω ↦ (Y ω).2 * Real.exp ((Y ω).1 ^ 2 * (v : ℝ) / 2) := by
    funext ω; rw [hYdef]
    by_cases hω : ω ∈ A <;> simp [hω]
  rw [hLHS, hRHS]
  rw [← integral_map hYΔ_aem hF_meas.aestronglyMeasurable, hjoint,
    integral_prod F hF_int_prod]
  rw [← integral_map hY_meas.aemeasurable
        (by fun_prop : AEStronglyMeasurable
          (fun y : ℝ × ℝ ↦ y.2 * Real.exp (y.1 ^ 2 * (v : ℝ) / 2)) (P.map Y))]
  exact integral_congr_ae (Filter.Eventually.of_forall hinner)

variable [SigmaFiniteFiltration P 𝓕] {X : ℝ≥0 → Ω → ℝ}
  [hX : IsFilteredPreBrownian X 𝓕 P]

/-- **Conditional MGF of a Brownian increment against a random adapted multiplier.**
For `c` `𝓕_r`-measurable and bounded, and `r ≤ t`,
`𝔼[exp(c·(X_t − X_r)) | 𝓕_r] = exp(½ c² (t − r))` a.e.

The `𝓕_r`-measurable `c` is *frozen*: `Δ = X_t − X_r` is independent of `𝓕_r`, so the joint
law factorizes and Fubini evaluates the inner Gaussian MGF `∫ exp(c·z) d𝒩(0,t−r)`. This is
the adapted-multiplier generalization of the constant-`α` freezing inside
`waldExponential_isMartingale`. -/
theorem condExp_exp_adapted_mul_increment
    {c : Ω → ℝ} {r : ℝ≥0} (hc : StronglyMeasurable[(𝓕 r : MeasurableSpace Ω)] c)
    {K : ℝ} (hK : ∀ ω, |c ω| ≤ K) {t : ℝ≥0} (hrt : r ≤ t) :
    P[fun ω ↦ Real.exp (c ω * (X t ω - X r ω)) | (𝓕 r : MeasurableSpace Ω)]
      =ᵐ[P] fun ω ↦ Real.exp ((c ω) ^ 2 * ((t : ℝ) - (r : ℝ)) / 2) := by
  have hc_meas : Measurable c := (hc.mono (𝓕.le r)).measurable
  have h_meas_diff : Measurable (fun ω ↦ X t ω - X r ω) :=
    (((hX.stronglyAdapted t).mono (𝓕.le t)).measurable).sub
      (((hX.stronglyAdapted r).mono (𝓕.le r)).measurable)
  -- The increment law, with variance `t − r`.
  have hΔlaw : HasLaw (fun ω ↦ X t ω - X r ω) (gaussianReal 0 (t - r)) P :=
    hasLaw_increment hX.toIsPreBrownianReal hrt
  have hindep0 : Indep (MeasurableSpace.comap (fun ω ↦ X t ω - X r ω) (borel ℝ)) (𝓕 r) P :=
    hX.indep r t hrt
  -- The candidate conditional expectation `g = exp(½ c² (t−r))` is `𝓕_r`-measurable.
  have hg_sm : StronglyMeasurable[(𝓕 r : MeasurableSpace Ω)]
      (fun ω ↦ Real.exp ((c ω) ^ 2 * ((t : ℝ) - (r : ℝ)) / 2)) :=
    Real.continuous_exp.comp_stronglyMeasurable
      ((((continuous_pow 2).comp_stronglyMeasurable hc).mul stronglyMeasurable_const).div
        stronglyMeasurable_const)
  -- Integrability of `f = exp(c·Δ)` and `g`.
  have hf_int : Integrable (fun ω ↦ Real.exp (c ω * (X t ω - X r ω))) P := by
    refine Integrable.mono'
      ((hΔlaw.integrable_fun_comp (integrable_exp_mul_gaussianReal K)).add
        (hΔlaw.integrable_fun_comp (integrable_exp_mul_gaussianReal (-K))))
      (hc_meas.mul h_meas_diff).exp.aestronglyMeasurable (Filter.Eventually.of_forall fun ω ↦ ?_)
    rw [Real.norm_of_nonneg (Real.exp_nonneg _)]
    obtain ⟨hlo, hhi⟩ := abs_le.mp (hK ω)
    rcases le_total 0 (X t ω - X r ω) with hΔ | hΔ
    · exact le_add_of_le_of_nonneg (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hhi hΔ))
        (Real.exp_nonneg _)
    · exact le_add_of_nonneg_of_le (Real.exp_nonneg _)
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_right hlo hΔ))
  have hg_int : Integrable (fun ω ↦ Real.exp ((c ω) ^ 2 * ((t : ℝ) - (r : ℝ)) / 2)) P := by
    refine Integrable.mono' (integrable_const (Real.exp (K ^ 2 * ((t : ℝ) - (r : ℝ)) / 2)))
      (hg_sm.mono (𝓕.le r)).aestronglyMeasurable (Filter.Eventually.of_forall fun ω ↦ ?_)
    rw [Real.norm_of_nonneg (Real.exp_nonneg _)]
    refine Real.exp_le_exp.mpr ?_
    have hsq : (c ω) ^ 2 ≤ K ^ 2 := by
      obtain ⟨hlo, hhi⟩ := abs_le.mp (hK ω); nlinarith [abs_nonneg (c ω), hK ω]
    have hnn : (0 : ℝ) ≤ (t : ℝ) - (r : ℝ) := sub_nonneg.mpr (NNReal.coe_le_coe.mpr hrt)
    have := mul_le_mul_of_nonneg_right hsq hnn
    linarith
  -- Assemble via the set-integral characterization of conditional expectation.
  refine (ae_eq_condExp_of_forall_setIntegral_eq (𝓕.le r) hf_int
    (fun A _ _ ↦ hg_int.integrableOn) (fun A hA _ ↦ ?_) hg_sm.aestronglyMeasurable).symm
  have hfreeze := condExp_exp_adapted_freeze_setIntegral (P := P) (𝓕 := 𝓕) hc.measurable hK
    h_meas_diff hΔlaw hindep0 hA
  rw [NNReal.coe_sub hrt] at hfreeze
  exact hfreeze.symm

/-- **The normalized cell factor conditionally integrates to `1`.** For `c` `𝓕_r`-measurable
bounded and `r ≤ t`, `𝔼[exp(c·(X_t − X_r) − ½ c² (t − r)) | 𝓕_r] = 1` a.e. — the
martingale-difference form of `condExp_exp_adapted_mul_increment`, obtained by pulling the
`𝓕_r`-measurable factor `exp(−½ c² (t − r))` out and collapsing with the conditional MGF. -/
theorem condExp_expCell_eq_one {c : Ω → ℝ} {r : ℝ≥0}
    (hc : StronglyMeasurable[(𝓕 r : MeasurableSpace Ω)] c)
    {K : ℝ} (hK : ∀ ω, |c ω| ≤ K) {t : ℝ≥0} (hrt : r ≤ t) :
    P[fun ω ↦ Real.exp (c ω * (X t ω - X r ω) - (c ω) ^ 2 * ((t : ℝ) - (r : ℝ)) / 2) |
        (𝓕 r : MeasurableSpace Ω)] =ᵐ[P] fun _ ↦ (1 : ℝ) := by
  have hc_meas : Measurable c := (hc.mono (𝓕.le r)).measurable
  have hXt : Measurable (X t) := ((hX.stronglyAdapted t).mono (𝓕.le t)).measurable
  have hXr : Measurable (X r) := ((hX.stronglyAdapted r).mono (𝓕.le r)).measurable
  have h_meas_diff : Measurable (fun ω ↦ X t ω - X r ω) := hXt.sub hXr
  have hΔlaw : HasLaw (fun ω ↦ X t ω - X r ω) (gaussianReal 0 (nndist (t : ℝ) (r : ℝ))) P :=
    hX.hasLaw_sub t r
  have htr : (0 : ℝ) ≤ (t : ℝ) - (r : ℝ) := sub_nonneg.mpr (NNReal.coe_le_coe.mpr hrt)
  set ft : Ω → ℝ := fun ω ↦ Real.exp (c ω * (X t ω - X r ω)) with hftdef
  set gr : Ω → ℝ := fun ω ↦ Real.exp (-((c ω) ^ 2 * ((t : ℝ) - (r : ℝ)) / 2)) with hgrdef
  have hgr_sm : StronglyMeasurable[(𝓕 r : MeasurableSpace Ω)] gr :=
    Real.continuous_exp.comp_stronglyMeasurable
      ((by fun_prop : Continuous fun x : ℝ ↦
          -(x ^ 2 * ((t : ℝ) - (r : ℝ)) / 2)).comp_stronglyMeasurable
        hc)
  -- Domination bound reused for both `ft` and `gr·ft`.
  have hbnd_int : Integrable (fun ω ↦ Real.exp (K * (X t ω - X r ω))
      + Real.exp (-K * (X t ω - X r ω))) P :=
    (hΔlaw.integrable_fun_comp (integrable_exp_mul_gaussianReal K)).add
      (hΔlaw.integrable_fun_comp (integrable_exp_mul_gaussianReal (-K)))
  have hft_int : Integrable ft P := by
    refine Integrable.mono' hbnd_int (by fun_prop) (Filter.Eventually.of_forall fun ω ↦ ?_)
    rw [hftdef, Real.norm_of_nonneg (Real.exp_nonneg _)]
    obtain ⟨hlo, hhi⟩ := abs_le.mp (hK ω)
    rcases le_total 0 (X t ω - X r ω) with hΔ | hΔ
    · exact le_add_of_le_of_nonneg (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hhi hΔ))
        (Real.exp_nonneg _)
    · exact le_add_of_nonneg_of_le (Real.exp_nonneg _)
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_right hlo hΔ))
  have hprod : (fun ω ↦ Real.exp (c ω * (X t ω - X r ω) - (c ω) ^ 2 * ((t : ℝ) - (r : ℝ)) / 2))
      = gr * ft := by
    funext ω; show _ = (gr * ft) ω
    rw [Pi.mul_apply, hgrdef, hftdef, ← Real.exp_add]; congr 1; ring
  have hprod_int : Integrable (gr * ft) P := by
    rw [← hprod]
    refine Integrable.mono' hbnd_int (by fun_prop) (Filter.Eventually.of_forall fun ω ↦ ?_)
    rw [Real.norm_of_nonneg (Real.exp_nonneg _)]
    have hstep : Real.exp (c ω * (X t ω - X r ω) - (c ω) ^ 2 * ((t : ℝ) - (r : ℝ)) / 2)
        ≤ Real.exp (c ω * (X t ω - X r ω)) :=
      Real.exp_le_exp.mpr (by nlinarith [sq_nonneg (c ω), htr])
    refine hstep.trans ?_
    obtain ⟨hlo, hhi⟩ := abs_le.mp (hK ω)
    rcases le_total 0 (X t ω - X r ω) with hΔ | hΔ
    · exact le_add_of_le_of_nonneg (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hhi hΔ))
        (Real.exp_nonneg _)
    · exact le_add_of_nonneg_of_le (Real.exp_nonneg _)
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_right hlo hΔ))
  rw [hprod]
  have hpull := condExp_mul_of_stronglyMeasurable_left (m := (𝓕 r : MeasurableSpace Ω))
    hgr_sm hprod_int hft_int
  have hcond := condExp_exp_adapted_mul_increment (P := P) (𝓕 := 𝓕) (X := X) hc hK hrt
  filter_upwards [hpull, hcond] with ω hp hc'
  rw [hp, Pi.mul_apply,
    show (P[ft | (𝓕 r : MeasurableSpace Ω)]) ω = Real.exp ((c ω) ^ 2 * ((t : ℝ) - (r : ℝ)) / 2)
      from hc', hgrdef, ← Real.exp_add, neg_add_cancel, Real.exp_zero]

/-- **The single-cell Doléans exponential over `(a,b]`, clamped to `[0,t]`.** For a multiplier
`c`, `cellExp a b c t = exp(c·(X_{b∧t} − X_{a∧t}) − ½ c² (b∧t − a∧t))`: it is `1` before `a`,
the running Wald exponential `exp(c(X_t − X_a) − ½c²(t−a))` inside `[a,b]`, and frozen at its
`b`-value after `b`. -/
noncomputable def cellExp (a b : ℝ≥0) (c : Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  Real.exp (c ω * (X (min b t) ω - X (min a t) ω)
    - (c ω) ^ 2 * (NNReal.toReal (min b t) - NNReal.toReal (min a t)) / 2)

lemma cellExp_of_le_left {a b : ℝ≥0} (hab : a ≤ b) {c : Ω → ℝ} {t : ℝ≥0}
    (ht : t ≤ a) (ω : Ω) : cellExp (X := X) a b c t ω = 1 := by
  rw [cellExp, min_eq_right (ht.trans hab), min_eq_right ht]; simp

lemma cellExp_of_mem {a b : ℝ≥0} {c : Ω → ℝ} {t : ℝ≥0} (hat : a ≤ t) (htb : t ≤ b) (ω : Ω) :
    cellExp (X := X) a b c t ω
      = Real.exp (c ω * (X t ω - X a ω) - (c ω) ^ 2 * ((t : ℝ) - (a : ℝ)) / 2) := by
  rw [cellExp, min_eq_right htb, min_eq_left hat]

lemma cellExp_of_ge_right {a b : ℝ≥0} (hab : a ≤ b) {c : Ω → ℝ} {t : ℝ≥0} (hbt : b ≤ t) (ω : Ω) :
    cellExp (X := X) a b c t ω
      = Real.exp (c ω * (X b ω - X a ω) - (c ω) ^ 2 * ((b : ℝ) - (a : ℝ)) / 2) := by
  rw [cellExp, min_eq_left hbt, min_eq_left (hab.trans hbt)]

include hX in
omit [IsProbabilityMeasure P] [SigmaFiniteFiltration P 𝓕] in
/-- Integrability of an increment cell factor `exp(c·(X_q − X_p) − ½c²(q−p))` for a bounded
multiplier and `p ≤ q` — the increment `X_q − X_p` is Gaussian, dominated by two Gaussian MGFs. -/
lemma integrable_cellIncrement {c : Ω → ℝ} (hc_meas : Measurable c) {K : ℝ}
    (hK : ∀ ω, |c ω| ≤ K) (p q : ℝ≥0) (hpq : p ≤ q) :
    Integrable (fun ω ↦ Real.exp (c ω * (X q ω - X p ω)
      - (c ω) ^ 2 * (NNReal.toReal q - NNReal.toReal p) / 2)) P := by
  have hXq : Measurable (X q) := ((hX.stronglyAdapted q).mono (𝓕.le q)).measurable
  have hXp : Measurable (X p) := ((hX.stronglyAdapted p).mono (𝓕.le p)).measurable
  have hΔlaw : HasLaw (fun ω ↦ X q ω - X p ω) (gaussianReal 0 (nndist (q : ℝ) (p : ℝ))) P :=
    hX.hasLaw_sub q p
  have hpqr : (0 : ℝ) ≤ NNReal.toReal q - NNReal.toReal p :=
      sub_nonneg.mpr (NNReal.coe_le_coe.mpr hpq)
  refine Integrable.mono'
    ((hΔlaw.integrable_fun_comp (integrable_exp_mul_gaussianReal K)).add
      (hΔlaw.integrable_fun_comp (integrable_exp_mul_gaussianReal (-K))))
    (by fun_prop) (Filter.Eventually.of_forall fun ω ↦ ?_)
  rw [Real.norm_of_nonneg (Real.exp_nonneg _)]
  have hstep : Real.exp
      (c ω * (X q ω - X p ω) - (c ω) ^ 2 * (NNReal.toReal q - NNReal.toReal p) / 2)
      ≤ Real.exp (c ω * (X q ω - X p ω)) :=
    Real.exp_le_exp.mpr (by nlinarith [sq_nonneg (c ω), hpqr])
  refine hstep.trans ?_
  obtain ⟨hlo, hhi⟩ := abs_le.mp (hK ω)
  rcases le_total 0 (X q ω - X p ω) with hΔ | hΔ
  · exact le_add_of_le_of_nonneg (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hhi hΔ))
      (Real.exp_nonneg _)
  · exact le_add_of_nonneg_of_le (Real.exp_nonneg _)
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_right hlo hΔ))

include hX in
/-- **The single-cell Doléans exponential over `(a,b]` is a `P`-martingale.** For `a ≤ b` and a
bounded `𝓕_a`-measurable multiplier `c`, `t ↦ cellExp a b c t` is a martingale w.r.t. `𝓕`.

`cellExp` is `1` before `a`, the running Wald exponential inside `[a,b]`, and frozen after `b`.
The conditional expectation splits into four regions of `(s,t)` relative to `[a,b]`, each closing
by `condExp_expCell_eq_one` (the random-multiplier freezing) — through the tower `𝓕_s ⊆ 𝓕_a`
when `s ≤ a ≤ t`, and by pulling the `𝓕_s`-measurable `cellExp_s` out when `a ≤ s`. -/
theorem cellExp_isMartingale {a b : ℝ≥0} (hab : a ≤ b) {c : Ω → ℝ}
    (hc : StronglyMeasurable[(𝓕 a : MeasurableSpace Ω)] c) {K : ℝ} (hK : ∀ ω, |c ω| ≤ K) :
    Martingale (fun t ω ↦ cellExp (X := X) a b c t ω) 𝓕 P := by
  have hc_meas : Measurable c := (hc.mono (𝓕.le a)).measurable
  -- Integrability at every time, from the increment cell helper.
  have hcell_int : ∀ u : ℝ≥0, Integrable (fun ω ↦ cellExp (X := X) a b c u ω) P := fun u ↦
    integrable_cellIncrement (𝓕 := 𝓕) hc_meas hK (min a u) (min b u) (min_le_min_right u hab)
  -- Adaptedness.
  have hadapt : ∀ u : ℝ≥0, StronglyMeasurable[(𝓕 u : MeasurableSpace Ω)]
      (fun ω ↦ cellExp (X := X) a b c u ω) := by
    intro u
    rcases le_total a u with hau | hua
    · have hcu : StronglyMeasurable[(𝓕 u : MeasurableSpace Ω)] c := hc.mono (𝓕.mono hau)
      have hXbu : StronglyMeasurable[(𝓕 u : MeasurableSpace Ω)] (X (min b u)) :=
        (hX.stronglyAdapted (min b u)).mono (𝓕.mono (min_le_right b u))
      have hXau : StronglyMeasurable[(𝓕 u : MeasurableSpace Ω)] (X (min a u)) :=
        (hX.stronglyAdapted (min a u)).mono (𝓕.mono (min_le_right a u))
      exact Real.continuous_exp.comp_stronglyMeasurable ((hcu.mul (hXbu.sub hXau)).sub
        ((((continuous_pow 2).comp_stronglyMeasurable hcu).mul stronglyMeasurable_const).div
          stronglyMeasurable_const))
    · rw [funext fun ω ↦ cellExp_of_le_left hab hua ω]; exact stronglyMeasurable_const
  refine ⟨hadapt, fun s t hst ↦ ?_⟩
  change P[fun ω ↦ cellExp (X := X) a b c t ω | (𝓕 s : MeasurableSpace Ω)]
    =ᵐ[P] fun ω ↦ cellExp (X := X) a b c s ω
  rcases le_total t a with hta | hta
  · -- (A) `t ≤ a`: both `1`.
    rw [funext fun ω ↦ cellExp_of_le_left hab hta ω,
      funext fun ω ↦ cellExp_of_le_left hab (hst.trans hta) ω]
    exact (condExp_const (𝓕.le s) (1 : ℝ)).eventuallyEq
  rcases le_total b s with hbs | hbs
  · -- (B) `b ≤ s`: both frozen at the `b`-value.
    have hsm : StronglyMeasurable[(𝓕 s : MeasurableSpace Ω)]
        (fun ω ↦ Real.exp (c ω * (X b ω - X a ω) - (c ω) ^ 2 * ((b : ℝ) - (a : ℝ)) / 2)) := by
      have hcs : StronglyMeasurable[(𝓕 s : MeasurableSpace Ω)] c := hc.mono (𝓕.mono (hab.trans hbs))
      have hXbs : StronglyMeasurable[(𝓕 s : MeasurableSpace Ω)] (X b) :=
        (hX.stronglyAdapted b).mono (𝓕.mono hbs)
      have hXas : StronglyMeasurable[(𝓕 s : MeasurableSpace Ω)] (X a) :=
        (hX.stronglyAdapted a).mono (𝓕.mono (hab.trans hbs))
      exact Real.continuous_exp.comp_stronglyMeasurable ((hcs.mul (hXbs.sub hXas)).sub
        ((((continuous_pow 2).comp_stronglyMeasurable hcs).mul stronglyMeasurable_const).div
          stronglyMeasurable_const))
    have hfr : (fun ω ↦ cellExp (X := X) a b c t ω)
        = fun ω ↦ Real.exp (c ω * (X b ω - X a ω) - (c ω) ^ 2 * ((b : ℝ) - (a : ℝ)) / 2) :=
      funext fun ω ↦ cellExp_of_ge_right hab (hbs.trans hst) ω
    rw [hfr, funext fun ω ↦ cellExp_of_ge_right hab hbs ω]
    exact (condExp_of_stronglyMeasurable (𝓕.le s) hsm (hfr ▸ hcell_int t)).eventuallyEq
  rcases le_total s a with hsa | hsa
  · -- (C) `s ≤ a ≤ t`: `cellExp_s = 1`, tower through `𝓕_a`.
    have hEa : P[(fun ω ↦ cellExp (X := X) a b c t ω) | (𝓕 a : MeasurableSpace Ω)]
        =ᵐ[P] fun _ ↦ (1 : ℝ) := by
      rw [funext fun ω ↦ show cellExp (X := X) a b c t ω
          = Real.exp (c ω * (X (min b t) ω - X a ω)
            - (c ω) ^ 2 * (NNReal.toReal (min b t) - NNReal.toReal a) / 2) by
        rw [cellExp, min_eq_left hta]]
      exact condExp_expCell_eq_one hc hK (le_min hab hta)
    rw [funext fun ω ↦ cellExp_of_le_left hab hsa ω]
    refine (condExp_condExp_of_le (𝓕.mono hsa) (𝓕.le a)).symm.trans ?_
    exact (condExp_congr_ae hEa).trans (condExp_const (𝓕.le s) (1 : ℝ)).eventuallyEq
  · -- (D) `a ≤ s ≤ b`: pull out the `𝓕_s`-measurable `cellExp_s`, freeze the `(s, b∧t]` increment.
    have hcs : StronglyMeasurable[(𝓕 s : MeasurableSpace Ω)] c := hc.mono (𝓕.mono hsa)
    have hsβ : s ≤ min b t := le_min hbs hst
    have hfactor : (fun ω ↦ cellExp (X := X) a b c t ω)
        = (fun ω ↦ cellExp (X := X) a b c s ω)
          * fun ω ↦ Real.exp (c ω * (X (min b t) ω - X s ω)
            - (c ω) ^ 2 * (NNReal.toReal (min b t) - NNReal.toReal s) / 2) := by
      funext ω
      simp only [Pi.mul_apply]
      rw [cellExp, min_eq_left hta, cellExp_of_mem hsa hbs ω, ← Real.exp_add]
      congr 1; ring
    rw [hfactor]
    have hpull := condExp_mul_of_stronglyMeasurable_left (m := (𝓕 s : MeasurableSpace Ω))
      (hadapt s) (hfactor ▸ hcell_int t)
          (integrable_cellIncrement (𝓕 := 𝓕) hc_meas hK s (min b t) hsβ)
    refine hpull.trans ?_
    filter_upwards [condExp_expCell_eq_one (P := P) (𝓕 := 𝓕) (X := X) hcs hK hsβ] with ω hg
    rw [Pi.mul_apply, show (P[(fun ω ↦ Real.exp (c ω * (X (min b t) ω - X s ω)
        - (c ω) ^ 2 * (NNReal.toReal (min b t) - NNReal.toReal s) / 2)) |
        (𝓕 s : MeasurableSpace Ω)]) ω = 1 from hg, mul_one]

include hX in
/-- **Appending one cell preserves the martingale.** If `M` is a `P`-martingale that is *frozen
after* `p` (constant in time past `p`), then multiplying by a fresh cell `cellExp p q c`
(`c` bounded `𝓕_p`-measurable, `p ≤ q`) is again a `P`-martingale. Cross-cell integrability uses
only the pairwise independence of the `(p, b∧t]` increment from `𝓕_p` (`IndepFun.integrable_mul`);
the conditional expectation splits on `s`, `t` versus `p`, closing by `cellExp_isMartingale`. -/
theorem mul_cellExp_isMartingale {M : ℝ≥0 → Ω → ℝ} (hM : Martingale M 𝓕 P)
    {p : ℝ≥0} (hMfroz : ∀ u ω, p ≤ u → M u ω = M p ω)
    {q : ℝ≥0} (hpq : p ≤ q) {c : Ω → ℝ} (hc : StronglyMeasurable[(𝓕 p : MeasurableSpace Ω)] c)
    {K : ℝ} (hK : ∀ ω, |c ω| ≤ K) :
    Martingale (fun t ω ↦ M t ω * cellExp (X := X) p q c t ω) 𝓕 P := by
  have hc_meas : Measurable c := (hc.mono (𝓕.le p)).measurable
  have hMp_meas : Measurable (M p) := ((hM.1 p).mono (𝓕.le p)).measurable
  have hG_mart := cellExp_isMartingale (X := X) (P := P) hpq hc hK
  -- Integrability at each time, in the frozen `M_p` form used by every case.
  have hMpG_int : ∀ t : ℝ≥0, Integrable (fun ω ↦ M p ω * cellExp (X := X) p q c t ω) P := by
    intro t
    rcases le_total t p with htp | hpt
    · rw [show (fun ω ↦ M p ω * cellExp (X := X) p q c t ω) = M p from
        funext fun ω ↦ by rw [cellExp_of_le_left hpq htp ω, mul_one]]
      exact hM.integrable p
    · have hpqt : p ≤ min q t := le_min hpq hpt
      have hXqt : Measurable (X (min q t)) :=
        ((hX.stronglyAdapted (min q t)).mono (𝓕.le _)).measurable
      have hXp : Measurable (X p) := ((hX.stronglyAdapted p).mono (𝓕.le p)).measurable
      have hcellval : (fun ω ↦ M p ω * cellExp (X := X) p q c t ω)
          = fun ω ↦ M p ω * Real.exp (c ω * (X (min q t) ω - X p ω)
            - (c ω) ^ 2 * (NNReal.toReal (min q t) - NNReal.toReal p) / 2) := by
        funext ω; rw [cellExp, min_eq_left hpt]
      have hΔlaw : HasLaw (fun ω ↦ X (min q t) ω - X p ω)
          (gaussianReal 0 (nndist ((min q t : ℝ≥0) : ℝ) ((p : ℝ≥0) : ℝ))) P :=
        hX.hasLaw_sub (min q t) p
      have hindepΔ : IndepFun (M p) (fun ω ↦ X (min q t) ω - X p ω) P :=
        Indep.symm (indep_of_indep_of_le_right (hX.indep p (min q t) hpqt)
          (hM.1 p).measurable.comap_le)
      have hindepK : IndepFun (fun ω ↦ |M p ω|)
          (fun ω ↦ Real.exp (K * (X (min q t) ω - X p ω))) P :=
        hindepΔ.comp (ψ := fun x ↦ Real.exp (K * x)) measurable_abs (by fun_prop)
      have hindepnK : IndepFun (fun ω ↦ |M p ω|)
          (fun ω ↦ Real.exp (-K * (X (min q t) ω - X p ω))) P :=
        hindepΔ.comp (ψ := fun x ↦ Real.exp (-K * x)) measurable_abs (by fun_prop)
      have hMabs_int : Integrable (fun ω ↦ |M p ω|) P := (hM.integrable p).abs
      have hbnd : Integrable (fun ω ↦ |M p ω| * Real.exp (K * (X (min q t) ω - X p ω))
          + |M p ω| * Real.exp (-K * (X (min q t) ω - X p ω))) P :=
        (hindepK.integrable_mul hMabs_int
          (hΔlaw.integrable_fun_comp (integrable_exp_mul_gaussianReal K))).add
          (hindepnK.integrable_mul hMabs_int
            (hΔlaw.integrable_fun_comp (integrable_exp_mul_gaussianReal (-K))))
      rw [hcellval]
      have hpqr : (0 : ℝ) ≤ NNReal.toReal (min q t) - NNReal.toReal p :=
        sub_nonneg.mpr (NNReal.coe_le_coe.mpr hpqt)
      refine Integrable.mono' hbnd (by fun_prop) (Filter.Eventually.of_forall fun ω ↦ ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
      have hle1 : c ω * (X (min q t) ω - X p ω)
          - (c ω) ^ 2 * (NNReal.toReal (min q t) - NNReal.toReal p) / 2
          ≤ c ω * (X (min q t) ω - X p ω) := by nlinarith [sq_nonneg (c ω), hpqr]
      have hGle : Real.exp (c ω * (X (min q t) ω - X p ω)
          - (c ω) ^ 2 * (NNReal.toReal (min q t) - NNReal.toReal p) / 2)
          ≤ Real.exp (K * (X (min q t) ω - X p ω)) + Real.exp (-K * (X (min q t) ω - X p ω)) := by
        refine (Real.exp_le_exp.mpr hle1).trans ?_
        obtain ⟨hlo, hhi⟩ := abs_le.mp (hK ω)
        rcases le_total 0 (X (min q t) ω - X p ω) with hΔ | hΔ
        · exact le_add_of_le_of_nonneg (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hhi hΔ))
            (Real.exp_nonneg _)
        · exact le_add_of_nonneg_of_le (Real.exp_nonneg _)
            (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_right hlo hΔ))
      calc |M p ω| * Real.exp (c ω * (X (min q t) ω - X p ω)
              - (c ω) ^ 2 * (NNReal.toReal (min q t) - NNReal.toReal p) / 2)
          ≤ |M p ω| * (Real.exp (K * (X (min q t) ω - X p ω))
              + Real.exp (-K * (X (min q t) ω - X p ω))) :=
            mul_le_mul_of_nonneg_left hGle (abs_nonneg _)
        _ = _ := by ring
  refine ⟨fun t ↦ (hM.1 t).mul (hG_mart.1 t), fun s t hst ↦ ?_⟩
  change P[fun ω ↦ M t ω * cellExp (X := X) p q c t ω | (𝓕 s : MeasurableSpace Ω)]
    =ᵐ[P] fun ω ↦ M s ω * cellExp (X := X) p q c s ω
  rcases le_total p s with hps | hsp
  · -- (I) `p ≤ s`: `M` frozen, pull out the `𝓕_s`-measurable `M_p`, `cellExp` martingale.
    rw [show (fun ω ↦ M t ω * cellExp (X := X) p q c t ω)
          = fun ω ↦ M p ω * cellExp (X := X) p q c t ω from
        funext fun ω ↦ by rw [hMfroz t ω (hps.trans hst)],
      show (fun ω ↦ M s ω * cellExp (X := X) p q c s ω)
          = fun ω ↦ M p ω * cellExp (X := X) p q c s ω from
        funext fun ω ↦ by rw [hMfroz s ω hps]]
    refine (condExp_mul_of_stronglyMeasurable_left (m := (𝓕 s : MeasurableSpace Ω))
      ((hM.1 p).mono (𝓕.mono hps)) (hMpG_int t) (hG_mart.integrable t)).trans ?_
    filter_upwards [hG_mart.2 s t hst] with ω hgw
    rw [Pi.mul_apply, hgw]
  · rcases le_total t p with htp | hpt
    · -- (II) `t ≤ p`: both cells are `1`, `M` martingale.
      rw [show (fun ω ↦ M t ω * cellExp (X := X) p q c t ω) = M t from
          funext fun ω ↦ by rw [cellExp_of_le_left hpq htp ω, mul_one],
        show (fun ω ↦ M s ω * cellExp (X := X) p q c s ω) = M s from
          funext fun ω ↦ by rw [cellExp_of_le_left hpq (hst.trans htp) ω, mul_one]]
      exact hM.2 s t hst
    · -- (III) `s ≤ p ≤ t`: tower through `𝓕_p`; inner pull-out gives `M_p` (cell at `p` is `1`).
      rw [show (fun ω ↦ M s ω * cellExp (X := X) p q c s ω) = M s from
          funext fun ω ↦ by rw [cellExp_of_le_left hpq hsp ω, mul_one],
        show (fun ω ↦ M t ω * cellExp (X := X) p q c t ω)
            = fun ω ↦ M p ω * cellExp (X := X) p q c t ω from
          funext fun ω ↦ by rw [hMfroz t ω hpt]]
      have hinner : P[(fun ω ↦ M p ω * cellExp (X := X) p q c t ω) |
          (𝓕 p : MeasurableSpace Ω)] =ᵐ[P] M p := by
        refine (condExp_mul_of_stronglyMeasurable_left (m := (𝓕 p : MeasurableSpace Ω)) (hM.1 p)
          (hMpG_int t) (hG_mart.integrable t)).trans ?_
        filter_upwards [hG_mart.2 p t hpt] with ω hgw
        rw [Pi.mul_apply, hgw, cellExp_of_le_left hpq (le_refl p) ω, mul_one]
      calc P[(fun ω ↦ M p ω * cellExp (X := X) p q c t ω) | (𝓕 s : MeasurableSpace Ω)]
          =ᵐ[P] P[P[(fun ω ↦ M p ω * cellExp (X := X) p q c t ω) |
              (𝓕 p : MeasurableSpace Ω)] | (𝓕 s : MeasurableSpace Ω)] :=
            (condExp_condExp_of_le (𝓕.mono hsp) (𝓕.le p)).symm
        _ =ᵐ[P] P[M p | (𝓕 s : MeasurableSpace Ω)] := condExp_congr_ae hinner
        _ =ᵐ[P] M s := hM.2 s p hsp

/-- **The running simple Doléans exponential** over the first `N` cells of a partition
`s : ℕ → ℝ≥0` with multipliers `d : ℕ → Ω → ℝ`: the product `∏_{i<N} cellExp (s i) (s (i+1))
(d i)`. This is the density process of the discrete/simple Girsanov change of measure. -/
noncomputable def simpleDoleansExp (s : ℕ → ℝ≥0) (d : ℕ → Ω → ℝ) : ℕ → ℝ≥0 → Ω → ℝ
  | 0, _, _ => 1
  | (n + 1), t, ω =>
    simpleDoleansExp s d n t ω * cellExp (X := X) (s n) (s (n + 1)) (d n) t ω

/-- The simple Doléans exponential over the first `N` cells is **frozen after `s N`**: past the
last partition point every cell factor is constant in time. -/
lemma simpleDoleansExp_frozen (s : ℕ → ℝ≥0) (hs : Monotone s) (d : ℕ → Ω → ℝ) :
    ∀ (N : ℕ) (u : ℝ≥0) (ω : Ω), s N ≤ u →
      simpleDoleansExp (X := X) s d N u ω = simpleDoleansExp (X := X) s d N (s N) ω := by
  intro N
  induction N with
  | zero => intro u ω _; rfl
  | succ n ih =>
    intro u ω hu
    have hsn : s n ≤ s (n + 1) := hs (Nat.le_succ n)
    change simpleDoleansExp (X := X) s d n u ω * cellExp (X := X) (s n) (s (n + 1)) (d n) u ω
        = simpleDoleansExp (X := X) s d n (s (n + 1)) ω
          * cellExp (X := X) (s n) (s (n + 1)) (d n) (s (n + 1)) ω
    rw [ih u ω (hsn.trans hu), ih (s (n + 1)) ω hsn,
      cellExp_of_ge_right hsn hu, cellExp_of_ge_right hsn (le_refl _)]

include hX in
/-- **The simple Doléans exponential is a `P`-martingale.** For a monotone partition
`s : ℕ → ℝ≥0` and uniformly bounded adapted multipliers `d` (`d i` is `𝓕_{s i}`-measurable),
the running product `simpleDoleansExp s d N` is a martingale w.r.t. `𝓕` — the density process of
the simple (piecewise-constant-adapted) Girsanov change of measure. Induction on `N` via
`mul_cellExp_isMartingale`, with the `simpleDoleansExp_frozen` invariant feeding each new cell. -/
theorem simpleDoleansExp_isMartingale (s : ℕ → ℝ≥0) (hs : Monotone s) (d : ℕ → Ω → ℝ)
    (hd : ∀ i, StronglyMeasurable[(𝓕 (s i) : MeasurableSpace Ω)] (d i)) {K : ℝ}
    (hd_bdd : ∀ i ω, |d i ω| ≤ K) (N : ℕ) :
    Martingale (fun t ω ↦ simpleDoleansExp (X := X) s d N t ω) 𝓕 P := by
  induction N with
  | zero => exact martingale_const 𝓕 P 1
  | succ n ih =>
    exact mul_cellExp_isMartingale (X := X) ih
      (fun u ω hu ↦ simpleDoleansExp_frozen (X := X) s hs d n u ω hu)
      (hs (Nat.le_succ n)) (hd n) (hd_bdd n)

end MathFin
