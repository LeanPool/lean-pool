/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye, Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.Rates.VasicekBondPrice
public import LeanPool.MathFin.Models.Rates.VasicekSDEGaussian

/-!
# Hull–White short rates: deterministic part, Gaussian law, affine bonds, calibration

The Hull–White model `dr_t = (θ(t) − κ·r_t) dt + σ·dB_t` with `κ > 0` and deterministic
`θ` (continuity hypotheses stated where the FTC needs them), obtained by generalizing the
proved Vasicek template of `MathFin/Models/Rates/VasicekBondPrice.lean`.

Scope, as in that template: the short rate and its time integral are carried in their
Wiener representations — `integratedRate` and `bondRate` are definitions. That
`integratedRate` solves the SDE above, and that `bondRate T = ∫₀ᵀ integratedRate s ds`
(the time-order swap), are the modelling bridges; neither is proved here. Everything below
is derived from those representations.

* **The deterministic part** — `deterministic` is the particular solution
  `α(t) = e^{−κt}·(r₀ + ∫₀ᵗ e^{κs}·θ(s) ds)` with `α(0) = r₀`. The ODE lemma
  `deterministic_solves_ODE` generalizes `vasicekDeterministic_solves_ODE`; constant `θ`
  reduces to Vasicek verbatim (`deterministic_const`); uniqueness of the ODE solution
  (`deterministic_eq_of_solves_ODE`) writes the deterministic part through any other
  solution `α` as `α(t) + (r₀ − α(0))·e^{−κt}` (`deterministic_eq_add_exp_of_solves_ODE`). It
  is the centre of the law of `r_t` (`integratedRate_hasLaw_gaussian`).
* **The short rate in Wiener representation** — `integratedRate` (= `deterministic` +
  `σ·`Wiener integral of the kernel `e^{−κ(t−u)}`) is Gaussian with the Vasicek variance
  `(σ²/2κ)·(1 − e^{−2κt})` — `θ` shifts means, never variances
  (`integratedRate_hasLaw_gaussian`).
* **The affine bond price** — the integrated rate reuses the Vasicek integrated kernel
  `vasicekIntegratedKernelLp` verbatim (integrating the diffusion kernel over
  `s ∈ [u, T]` is model-independent), so `bondPrice_eq` is the Wiener bond-price lemma
  `integral_exp_neg_add_mul_wienerIntegralLp` with variance `vasicekBondV` again; `bondA` gains
  the `θ`-forcing integral and `bondPrice_affine` gives the time-0 affine form
  `A(T)·e^{−B(T)·r₀}`, `A` independent of `r₀` and `B = vasicekBondB` reused verbatim.
  `P(t,T)` for `t > 0` is not formalized.
* **Constant forcing is Vasicek** — with `θ ≡ κθ_v` the integrated mean is Vasicek's
  `r₀B(T) + θ_v(T − B(T))` (`integratedMean_const`), so the integrated HW rate *is* the
  integrated Vasicek rate `vasicekIntegratedRate` at level `θ_v` (`bondRate_const`).
* **Calibration** — `theta` is the calibration formula
  `θ(t) = ∂_t f(0,t) + κ·f(0,t) + (σ²/2κ)·(1 − e^{−2κt})`; `calibAlpha_solves_ODE`
  verifies by differentiation that the closed form
  `β(t) = f(0,t) + (σ²/2κ²)·(1 − e^{−κt})²` solves the HW ODE under this `θ`, uniqueness
  (`deterministic_eq_of_solves_ODE`) makes it the calibrated deterministic part
  (`mean_eq_forward`; the expected short rate is `calibMean_eq_forward`), and the
  calibration integral lemma `∫₀ᵀ α = ∫₀ᵀ f0 + σ²V/2` (`calibIntegratedMean`, via the
  kernel reflection `var_eq_interval`) makes `reprices_curve` exact: for `f0 ∈ C¹`,
  `κ > 0` and the rate started at `r₀ = f(0,0)`,
  `𝔼[exp(−bondRate T)] = exp(−∫₀ᵀ f(0,s) ds)`.

Structural note: the `θ`-forcing integral lives on the triangle `0 ≤ u ≤ s ≤ t`; rather
than rewrite it over a rectangle for an interval-integral Fubini swap, it is proved by an
antiderivative (`beta_integral`: `G(s) =
(1/κ)·(∫₀ˢ θ − e^{−κs}·∫₀ˢ e^{κu}θ)` has `G' = e^{−κs}·I(s)`, `G(0) = 0`) plus a
pointwise expansion of `θ(s)·B(t−s)` (`integral_theta_B`) — no Fubini anywhere, only
pointwise congruences, linearity, and one `intervalIntegral.integral_comp_sub_left`
reflection.

## Main definitions

* `deterministic`: the Hull–White deterministic solution
  `α(t) = e^{−κt}·(r₀ + ∫₀ᵗ e^{κs} θ(s) ds)` with `α(0) = r₀`.
* `integratedRate`: the Hull–White short rate in its Wiener representation.
* `integratedMean`, `bondRate`: the deterministic part `∫₀ᵗ α(s) ds` of the integrated short rate,
  and the integrated short rate `∫₀ᵗ α + σ·∫₀ᵗ g(u) dB_u` in Wiener representation.
* `bondA`: the affine coefficient `A(T) = exp(−∫₀ᵀ θ(s)·B(T−s) ds + σ²·V(T)/2)`.
* `theta`: the calibrated drift `θ(t)`, given by the calibration formula.
* `calibAlpha`: the closed form `β(t) = f(0,t) + (σ²/2κ²)·(1 − e^{−κt})²`, the initial forward
  plus the convexity correction.

## Main results

* `deterministic_solves_ODE`, `deterministic_eq_of_solves_ODE`: for continuous `θ`, the
  deterministic part solves `α' = θ − κα`, and any everywhere-differentiable solution `α` of that
  ODE coincides with `deterministic θ κ (α 0)`.
* `integratedRate_hasLaw_gaussian`: for `κ > 0`, the integrated short rate at time `t` has the
  Gaussian law with mean `deterministic θ κ r₀ t` and the Vasicek variance.
* `bondPrice_eq`, `bondPrice_affine`: for `κ > 0`, `𝔼[exp(−bondRate T)]` equals
  `exp(−integratedMean T + σ²·vasicekBondV κ T/2)`, which for continuous `θ` is the affine form
  `bondA·exp(−B(T)·r₀)`.
* `integratedMean_const`, `bondRate_const`: for `κ ≠ 0` (respectively `κ > 0`), constant forcing
  `κθ` gives the Vasicek integrated mean (respectively the Vasicek integrated rate).
* `calibAlpha_solves_ODE`, `mean_eq_forward`: for `f0` of class `C¹` and `κ ≠ 0`, `calibAlpha`
  solves the Hull–White ODE under `theta f0 κ σ`, and the deterministic part started at
  `f0 0` equals `f0(t) + (σ²/2κ²)(1 − e^{−κt})²`.
* `calibMean_eq_forward`: for `κ > 0`, the expected short rate under `theta` equals
  `f0(t) + (σ²/2κ²)(1 − e^{−κt})²`.
* `calibIntegratedMean`: for `κ > 0`, the integrated mean under `theta` equals
  `∫₀ᵀ f0 + (σ²/2)·vasicekBondV κ T`.
* `reprices_curve`: for `f0` of class `C¹`, `κ > 0` and `r₀ = f0 0`,
  `𝔼[exp(−bondRate T)] = exp(−∫₀ᵀ f0)`.

## References

* [D. Brigo and F. Mercurio, *Interest Rate Models --- Theory and Practice*][BrigoMercurio2006],
  §3.3
* [J. Hull and A. White, *Pricing interest-rate-derivative securities*][HullWhite1990]

## Tags

Hull–White model, curve calibration, extended Vasicek, forward rate curve, mean reversion,
Gaussian short rate, affine bond price, MSC 91G30, MSC 60H10, JEL E43
-/

@[expose] public section

namespace MathFin.HullWhite

open MeasureTheory ProbabilityTheory Real Set
open scoped NNReal
open MathFin WienerIntegralL2

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ}

/-! ### The deterministic part -/

/-- **Hull–White deterministic (particular) solution** with `α(0) = r₀`:
`α(t) = e^{−κt}·(r₀ + ∫₀ᵗ e^{κs} θ(s) ds)`. For non-integrable `θ` the integral is
junk; every meaningful statement below states its hypotheses on `θ` explicitly. -/
noncomputable def deterministic (θ : ℝ → ℝ) (κ r₀ t : ℝ) : ℝ :=
  Real.exp (-(κ * t)) * (r₀ + ∫ s in (0 : ℝ)..t, Real.exp (κ * s) * θ s)

/-- **Initial condition**: `α(0) = r₀` (no hypotheses — the empty integral is 0). -/
lemma deterministic_at_zero (θ : ℝ → ℝ) (κ r₀ : ℝ) :
    deterministic θ κ r₀ 0 = r₀ := by
  simp [deterministic, intervalIntegral.integral_same]

/-- **The HW ODE lemma** (generalizes `vasicekDeterministic_solves_ODE`): with θ
continuous, the particular solution satisfies `α'(t) = θ(t) − κ·α(t)` at every
point. Proof: FTC (`integral_hasDerivAt_right`) for the integral term + product
rule; `e^{−κt}·e^{κt} = 1` collapses the forcing term. -/
theorem deterministic_solves_ODE (θ : ℝ → ℝ) (hθ : Continuous θ) (κ r₀ t : ℝ) :
    HasDerivAt (deterministic θ κ r₀) (θ t - κ * deterministic θ κ r₀ t) t := by
  have hfc : Continuous (fun s : ℝ ↦ Real.exp (κ * s) * θ s) := by fun_prop
  have hI : HasDerivAt (fun x : ℝ ↦ ∫ s in (0 : ℝ)..x, Real.exp (κ * s) * θ s)
      (Real.exp (κ * t) * θ t) t :=
    intervalIntegral.integral_hasDerivAt_right (hfc.intervalIntegrable 0 t)
      (hfc.stronglyMeasurableAtFilter volume (nhds t)) hfc.continuousAt
  have hexp1 : HasDerivAt (fun x : ℝ ↦ Real.exp (-(κ * x)))
      (Real.exp (-(κ * t)) * (-κ)) t := by
    have hk : HasDerivAt (fun x : ℝ ↦ κ * x) κ t := by
      simpa using (hasDerivAt_id t).const_mul κ
    exact hk.neg.exp
  have hprod := hexp1.mul (hI.const_add r₀)
  have hexpmul : Real.exp (-(κ * t)) * Real.exp (κ * t) = 1 := by
    rw [← Real.exp_add]; simp
  have hval : (θ t - κ * deterministic θ κ r₀ t)
      = Real.exp (-(κ * t)) * (-κ) * (r₀ + ∫ s in (0 : ℝ)..t, Real.exp (κ * s) * θ s)
        + Real.exp (-(κ * t)) * (Real.exp (κ * t) * θ t) := by
    have hsplit : Real.exp (-(κ * t)) * (Real.exp (κ * t) * θ t) = θ t := by
      rw [← mul_assoc, hexpmul, one_mul]
    simp only [deterministic, hsplit]
    ring
  rw [hval]
  exact hprod

/-- Scalar integral: `∫₀ᵗ e^{κs}·Θ ds = Θ·(e^{κt} − 1)/κ`. -/
lemma integral_exp_pos_const (Θ κ t : ℝ) (hκ : κ ≠ 0) :
    ∫ s in (0 : ℝ)..t, Real.exp (κ * s) * Θ = Θ * (Real.exp (κ * t) - 1) / κ := by
  have hF : ∀ s ∈ Set.uIcc (0 : ℝ) t,
      HasDerivAt (fun s : ℝ ↦ Θ * Real.exp (κ * s) / κ) (Real.exp (κ * s) * Θ) s := by
    intro s _
    have hk : HasDerivAt (fun s : ℝ ↦ κ * s) κ s := by
      simpa using (hasDerivAt_id s).const_mul κ
    have h := ((hk.exp).const_mul Θ).div_const κ
    have hval : (Θ * (Real.exp (κ * s) * κ)) / κ = Real.exp (κ * s) * Θ := by
      field_simp
    rw [hval] at h
    exact h
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF
    (by apply Continuous.intervalIntegrable; fun_prop)]
  simp only [mul_zero, Real.exp_zero, mul_one]
  field_simp

/-- **Constant θ reduces to Vasicek**: `deterministic (fun _ ↦ Θ) κ r₀ t =
vasicekDeterministic r₀ (Θ/κ) κ t` — the HW drift `Θ − κr` is Vasicek's
`κ(θ_v − r)` with `θ_v = Θ/κ`, so every proved Vasicek result transfers. -/
lemma deterministic_const (Θ κ r₀ t : ℝ) (hκ : κ ≠ 0) :
    deterministic (fun _ ↦ Θ) κ r₀ t = vasicekDeterministic r₀ (Θ / κ) κ t := by
  have hint : ∫ s in (0 : ℝ)..t, Real.exp (κ * s) * Θ
      = Θ * (Real.exp (κ * t) - 1) / κ := integral_exp_pos_const Θ κ t hκ
  have hexpmul : Real.exp (-(κ * t)) * Real.exp (κ * t) = 1 := by
    rw [← Real.exp_add]; simp
  simp only [deterministic, hint, vasicekDeterministic]
  field_simp [hexpmul]
  linear_combination Θ * hexpmul

/-- **Vasicek's closed form for constant θ**: `deterministic (fun _ ↦ Θ) κ r₀ t
= Θ/κ + (r₀ − Θ/κ)·e^{−κt}` — the mean-reversion solution to level `θ_v = Θ/κ`
in explicit form (reached through the bridge `deterministic_const`;
`vasicekDeterministic`'s definition body): constant HW forcing `Θ` is Vasicek
with long-run mean `Θ/κ` — *not* HW forcing `Θ/κ`, which would be Vasicek with
mean `Θ/κ²`. -/
theorem deterministic_const_closed_form (Θ κ r₀ t : ℝ) (hκ : κ ≠ 0) :
    deterministic (fun _ ↦ Θ) κ r₀ t = Θ / κ + (r₀ - Θ / κ) * Real.exp (-(κ * t)) := by
  rw [deterministic_const Θ κ r₀ t hκ]
  rfl

/-- **Mean reversion for constant θ**: the deterministic part tends to `Θ/κ`,
mirroring `vasicekDeterministic_tendsto_mean`. -/
theorem deterministic_const_tendsto (Θ κ r₀ : ℝ) (hκ : 0 < κ) :
    Filter.Tendsto (deterministic (fun _ ↦ Θ) κ r₀) Filter.atTop (nhds (Θ / κ)) := by
  have h : deterministic (fun _ ↦ Θ) κ r₀ = vasicekDeterministic r₀ (Θ / κ) κ := by
    funext t
    exact deterministic_const Θ κ r₀ t hκ.ne'
  rw [h]
  exact vasicekDeterministic_tendsto_mean r₀ (Θ / κ) κ hκ

/-- Linearity of the particular solution in the initial condition: raising the
initial rate by `a` shifts `α(t)` by `a·e^{−κt}` for every `t`. -/
lemma deterministic_add_exponential (θ : ℝ → ℝ) (κ r₀ a t : ℝ) :
    deterministic θ κ (r₀ + a) t
      = deterministic θ κ r₀ t + a * Real.exp (-(κ * t)) := by
  simp only [deterministic]
  ring

/-- **Uniqueness of the ODE solution**: any `α` satisfying `α'(s) = θ(s) − κ·α(s)`
at every point (θ continuous) with `α(0) = r₀` equals `deterministic θ κ r₀`.
Proof: `F(s) = e^{κs}(α(s) − α_det(s))` has `F' = 0` everywhere, hence `F ≡ 0`. -/
theorem deterministic_eq_of_solves_ODE (θ : ℝ → ℝ) (hθ : Continuous θ) (κ : ℝ)
    (α : ℝ → ℝ) (hα : ∀ s, HasDerivAt α (θ s - κ * α s) s) (t : ℝ) :
    deterministic θ κ (α 0) t = α t := by
  have hhwd : ∀ s : ℝ, HasDerivAt (deterministic θ κ (α 0))
      (θ s - κ * deterministic θ κ (α 0) s) s := fun s ↦
    deterministic_solves_ODE θ hθ κ (α 0) s
  have hgap : ∀ s : ℝ, HasDerivAt (fun x : ℝ ↦ α x - deterministic θ κ (α 0) x)
      (-(κ * (α s - deterministic θ κ (α 0) s))) s := by
    intro s
    have h := (hα s).sub (hhwd s)
    rw [show (θ s - κ * α s) - (θ s - κ * deterministic θ κ (α 0) s)
        = -(κ * (α s - deterministic θ κ (α 0) s)) from by ring] at h
    exact h
  have hF : ∀ s : ℝ, HasDerivAt
      (fun x : ℝ ↦ Real.exp (κ * x) * (α x - deterministic θ κ (α 0) x)) 0 s := by
    intro s
    have hk : HasDerivAt (fun x : ℝ ↦ κ * x) κ s := by
      simpa using (hasDerivAt_id s).const_mul κ
    have h := (hk.exp).mul (hgap s)
    rw [show Real.exp (κ * s) * κ * (α s - deterministic θ κ (α 0) s)
        + Real.exp (κ * s) * (-(κ * (α s - deterministic θ κ (α 0) s))) = 0 from by
      ring] at h
    exact h
  have hint : IntervalIntegrable (fun _ : ℝ ↦ (0 : ℝ)) volume 0 t := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hsub := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ ↦ hF s) hint
  rw [intervalIntegral.integral_const] at hsub
  simp only [sub_zero, smul_zero, mul_zero, Real.exp_zero, one_mul] at hsub
  have hF0 : α 0 - deterministic θ κ (α 0) 0 = 0 := by
    rw [deterministic_at_zero]; ring
  rw [hF0, sub_zero] at hsub
  have hgap : α t - deterministic θ κ (α 0) t = 0 := by
    refine mul_left_cancel₀ (Real.exp_ne_zero (κ * t)) ?_
    rw [mul_zero]
    exact hsub.symm
  exact (eq_of_sub_eq_zero hgap).symm

/-- **The deterministic part through any ODE solution**: with any `α` solving
`α' = θ − κα` pointwise (θ continuous), the deterministic part of the HW short rate is
`α(t) + (r₀ − α(0))·e^{−κt}` — the particular solution plus the exponentially decaying
initial gap. It is the centre of the law of `r_t` (`integratedRate_hasLaw_gaussian`);
the expectation itself is stated under calibration, `calibMean_eq_forward`. -/
theorem deterministic_eq_add_exp_of_solves_ODE (θ : ℝ → ℝ) (κ : ℝ) (α : ℝ → ℝ)
    (hα : ∀ s, HasDerivAt α (θ s - κ * α s) s) (hθ : Continuous θ) (r₀ t : ℝ) :
    deterministic θ κ r₀ t = α t + (r₀ - α 0) * Real.exp (-(κ * t)) := by
  have hsplit : α 0 + (r₀ - α 0) = r₀ := by ring
  rw [show r₀ = α 0 + (r₀ - α 0) from hsplit.symm, deterministic_add_exponential,
    deterministic_eq_of_solves_ODE θ hθ κ α hα]
  ring

/-! ### The short rate and its Gaussian law -/

/- The HW diffusion kernel `e^{−κ(t−u)}` — the deterministic integrand of the
short rate's Wiener part `σ∫₀ᵗ e^{−κ(t−u)} dB_u` — is the Vasicek kernel
`vasicekKernel` of `Models/Rates/VasicekSDEGaussian` verbatim, and is used through its
`L²` element `vasicekKernelLp` there; nothing kernel-specific is redefined here. -/

/-- **The HW short rate in Wiener representation** (the counterpart of the Vasicek
short rate of `VasicekSDEGaussian`), defined as `r_t = α(t) + σ·∫₀ᵗ e^{−κ(t−u)} dB_u`
with `α` the particular solution `deterministic θ κ r₀` and the diffusion kernel the
Vasicek `vasicekKernelLp` reused verbatim. That it solves the HW SDE is
the modelling bridge, not proved here. -/
noncomputable def integratedRate (hB : IsPreBrownianReal B μ) (θ : ℝ → ℝ)
    (κ σ r₀ : ℝ) (hκ : 0 < κ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  deterministic θ κ r₀ (t : ℝ)
    + σ * (wienerIntegralLp B hB t (vasicekKernelLp κ hκ.le t) ω)

/-- **The HW short rate is Gaussian**: `r_t ~ N(α(t), σ²(1 − e^{−2κt})/(2κ))` —
θ(t) shifted the mean and left the Vasicek variance untouched: the zero-mean Vasicek law
(`vasicekShortRate_hasLaw_gaussian` at `r₀ = θ = 0`) shifted by `α(t)`. -/
theorem integratedRate_hasLaw_gaussian (hB : IsPreBrownianReal B μ) (θ : ℝ → ℝ)
    (κ σ r₀ : ℝ) (hκ : 0 < κ) (t : ℝ≥0) :
    HasLaw (integratedRate hB θ κ σ r₀ hκ t)
      (gaussianReal (deterministic θ κ r₀ (t : ℝ))
        ((vasicekSDEVariance σ κ (t : ℝ)).toNNReal)) μ := by
  unfold integratedRate
  simpa only [vasicekSDEMean, zero_mul, zero_add, add_zero] using
    gaussianReal_const_add (vasicekShortRate_hasLaw_gaussian hB 0 0 σ hκ t)
      (deterministic θ κ r₀ (t : ℝ))

/-! ### The affine bond price -/

/-- The deterministic part `∫₀ᵗ α(s) ds` of the integrated HW short rate (`bondRate`). -/
noncomputable def integratedMean (θ : ℝ → ℝ) (κ r₀ t : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..t, deterministic θ κ r₀ s

/-- The Vasicek affine coefficient is the integrated diffusion kernel:
`∫₀ᵗ e^{−κs} ds = (1 − e^{−κt})/κ = vasicekBondB κ t` — the identity that makes
`B` carry over from Vasicek to HW verbatim. -/
lemma integral_exp_neg_eq_bondB (κ t : ℝ) (hκ : κ ≠ 0) :
    ∫ s in (0 : ℝ)..t, Real.exp (-(κ * s)) = vasicekBondB κ t := by
  have hF : ∀ s ∈ Set.uIcc (0 : ℝ) t,
      HasDerivAt (fun s : ℝ ↦ -Real.exp (-(κ * s)) / κ) (Real.exp (-(κ * s))) s := by
    intro s _
    have hk : HasDerivAt (fun s : ℝ ↦ κ * s) κ s := by
      simpa using (hasDerivAt_id s).const_mul κ
    have hexpneg : HasDerivAt (fun x : ℝ ↦ Real.exp (-(κ * x)))
        (Real.exp (-(κ * s)) * (-κ)) s := by
      simpa using hk.neg.exp
    have h := hexpneg.neg.div_const κ
    have hval : -((Real.exp (-(κ * s)) * -κ)) / κ = Real.exp (-(κ * s)) := by
      field_simp
    rw [hval] at h
    exact h
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF
    (by apply Continuous.intervalIntegrable; fun_prop)]
  simp only [mul_zero, neg_zero, Real.exp_zero]
  rw [vasicekBondB]
  field_simp
  ring

/-- **The forcing integral** (the antiderivative route; the integral lives on the
triangle `0 ≤ u ≤ s ≤ t`):
`∫₀ᵗ e^{−κs}·(∫₀ˢ e^{κu}θ(u) du) ds = (1/κ)·(∫₀ᵗ θ − e^{−κt}·∫₀ᵗ e^{κu}θ(u) du)`.
`G(s) = (1/κ)(∫₀ˢ θ − e^{−κs}·∫₀ˢ e^{κu}θ)` satisfies `G' = e^{−κs}·I(s)`,
`G(0) = 0`. -/
lemma beta_integral (θ : ℝ → ℝ) (hθ : Continuous θ) (κ t : ℝ) (hκ : κ ≠ 0) :
    ∫ s in (0 : ℝ)..t, Real.exp (-(κ * s)) * (∫ u in (0 : ℝ)..s, Real.exp (κ * u) * θ u)
      = (1 / κ) * ((∫ s in (0 : ℝ)..t, θ s)
          - Real.exp (-(κ * t)) * (∫ s in (0 : ℝ)..t, Real.exp (κ * s) * θ s)) := by
  have hI : ∀ s : ℝ, HasDerivAt (fun x : ℝ ↦ ∫ u in (0 : ℝ)..x, Real.exp (κ * u) * θ u)
      (Real.exp (κ * s) * θ s) s := by
    intro s
    have hfc : Continuous (fun u : ℝ ↦ Real.exp (κ * u) * θ u) := by fun_prop
    exact intervalIntegral.integral_hasDerivAt_right (hfc.intervalIntegrable 0 s)
      (hfc.stronglyMeasurableAtFilter volume (nhds s)) hfc.continuousAt
  have hD : ∀ s : ℝ, HasDerivAt (fun x : ℝ ↦ ∫ u in (0 : ℝ)..x, θ u) (θ s) s := by
    intro s
    exact intervalIntegral.integral_hasDerivAt_right (hθ.intervalIntegrable 0 s)
      (hθ.stronglyMeasurableAtFilter volume (nhds s)) hθ.continuousAt
  have hE : ∀ s : ℝ, HasDerivAt (fun x : ℝ ↦ Real.exp (-(κ * x)))
      (Real.exp (-(κ * s)) * (-κ)) s := by
    intro s
    have hk : HasDerivAt (fun x : ℝ ↦ κ * x) κ s := by
      simpa using (hasDerivAt_id s).const_mul κ
    exact hk.neg.exp
  have hG : ∀ s : ℝ, HasDerivAt
      (fun x : ℝ ↦ (1 / κ) * ((∫ u in (0 : ℝ)..x, θ u)
        - Real.exp (-(κ * x)) * (∫ u in (0 : ℝ)..x, Real.exp (κ * u) * θ u)))
      (Real.exp (-(κ * s)) * (∫ u in (0 : ℝ)..s, Real.exp (κ * u) * θ u)) s := by
    intro s
    have hexpmul : Real.exp (-(κ * s)) * Real.exp (κ * s) = 1 := by
      rw [← Real.exp_add]; simp
    have h := ((hD s).sub ((hE s).mul (hI s))).const_mul (1 / κ)
    rw [← mul_assoc (Real.exp (-(κ * s))) (Real.exp (κ * s)) (θ s), hexpmul, one_mul] at h
    have hval : (1 / κ) * (θ s
        - (Real.exp (-(κ * s)) * -κ * (∫ u in (0 : ℝ)..s, Real.exp (κ * u) * θ u) + θ s))
        = Real.exp (-(κ * s)) * (∫ u in (0 : ℝ)..s, Real.exp (κ * u) * θ u) := by
      field_simp
      ring
    rw [hval] at h
    exact h
  have hint : IntervalIntegrable
      (fun s : ℝ ↦ Real.exp (-(κ * s))
        * (∫ u in (0 : ℝ)..s, Real.exp (κ * u) * θ u)) volume 0 t := by
    have hfc : Continuous (fun u : ℝ ↦ Real.exp (κ * u) * θ u) := by fun_prop
    apply Continuous.intervalIntegrable
    exact (by fun_prop : Continuous (fun x : ℝ ↦ Real.exp (-(κ * x)))).mul
      (intervalIntegral.continuous_primitive (fun a b ↦ hfc.intervalIntegrable a b) 0)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ ↦ hG s) hint]
  have h0 : (1 / κ) * ((∫ u in (0 : ℝ)..0, θ u)
      - Real.exp (-(κ * 0)) * (∫ u in (0 : ℝ)..0, Real.exp (κ * u) * θ u)) = 0 := by
    simp [intervalIntegral.integral_same]
  rw [h0, sub_zero]

/-- The A-integral in split form: `∫₀ᵗ θ(s)·B(t−s) ds =
(1/κ)·(∫₀ᵗ θ − e^{−κt}·∫₀ᵗ e^{κs}θ(s) ds)` — pure pointwise algebra on
`B(τ) = (1 − e^{−κτ})/κ`, no Fubini. -/
lemma integral_theta_B (θ : ℝ → ℝ) (κ t : ℝ) (hθ : Continuous θ) (hκ : κ ≠ 0) :
    ∫ s in (0 : ℝ)..t, θ s * vasicekBondB κ (t - s)
      = (1 / κ) * ((∫ s in (0 : ℝ)..t, θ s)
          - Real.exp (-(κ * t)) * (∫ s in (0 : ℝ)..t, Real.exp (κ * s) * θ s)) := by
  have hpt : ∀ s : ℝ, θ s * vasicekBondB κ (t - s)
      = (1 / κ) * θ s - (1 / κ) * (Real.exp (-(κ * t)) * (Real.exp (κ * s) * θ s)) := by
    intro s
    rw [vasicekBondB]
    have hrw : Real.exp (-(κ * (t - s))) = Real.exp (-(κ * t)) * Real.exp (κ * s) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [hrw]
    field_simp
  rw [intervalIntegral.integral_congr
    (show EqOn (fun s : ℝ ↦ θ s * vasicekBondB κ (t - s))
      (fun s : ℝ ↦ (1 / κ) * θ s - (1 / κ) * (Real.exp (-(κ * t)) * (Real.exp (κ * s) * θ s)))
      (Set.uIcc (0 : ℝ) t) from fun s _ ↦ hpt s)]
  rw [intervalIntegral.integral_sub
    ((by fun_prop : Continuous (fun s : ℝ ↦ (1 / κ) * θ s)).intervalIntegrable 0 t)
      ((by fun_prop : Continuous (fun s : ℝ ↦ (1 / κ) * (Real.exp (-(κ * t))
      * (Real.exp (κ * s) * θ s)))).intervalIntegrable 0 t)]
  simp only [intervalIntegral.integral_const_mul]
  ring

/-- **Mean of the integrated HW rate in B-form**: `∫₀ᵗ α(s) ds = r₀·B(t) +
∫₀ᵗ θ(s)·B(t−s) ds` — the r₀-separation that makes A r₀-free (the affine content;
Vasicek's closed form `r₀·B + θ_v·(t − B)` is the constant-θ special case). -/
lemma integratedMean_eq (θ : ℝ → ℝ) (hθ : Continuous θ) (κ r₀ t : ℝ) (hκ : κ ≠ 0) :
    integratedMean θ κ r₀ t
      = r₀ * vasicekBondB κ t + ∫ s in (0 : ℝ)..t, θ s * vasicekBondB κ (t - s) := by
  have hsplit : ∀ s : ℝ, deterministic θ κ r₀ s
      = r₀ * Real.exp (-(κ * s))
        + Real.exp (-(κ * s)) * (∫ u in (0 : ℝ)..s, Real.exp (κ * u) * θ u) := by
    intro s
    simp only [deterministic]
    rw [mul_add, mul_comm r₀ (Real.exp (-(κ * s)))]
  have hbeta : ∫ s in (0 : ℝ)..t,
      Real.exp (-(κ * s)) * (∫ u in (0 : ℝ)..s, Real.exp (κ * u) * θ u)
      = ∫ s in (0 : ℝ)..t, θ s * vasicekBondB κ (t - s) := by
    rw [beta_integral θ hθ κ t hκ, integral_theta_B θ κ t hθ hκ]
  have hsplitint : ∫ x in (0 : ℝ)..t, deterministic θ κ r₀ x ∂volume
      = ∫ x in (0 : ℝ)..t, (r₀ * Real.exp (-(κ * x))
        + Real.exp (-(κ * x)) * (∫ u in (0 : ℝ)..x, Real.exp (κ * u) * θ u)) ∂volume :=
    intervalIntegral.integral_congr (fun x _ ↦ hsplit x)
  have hadd : ∫ x in (0 : ℝ)..t, (r₀ * Real.exp (-(κ * x))
        + Real.exp (-(κ * x)) * (∫ u in (0 : ℝ)..x, Real.exp (κ * u) * θ u)) ∂volume
      = ∫ x in (0 : ℝ)..t, r₀ * Real.exp (-(κ * x)) ∂volume
        + ∫ x in (0 : ℝ)..t, Real.exp (-(κ * x))
          * (∫ u in (0 : ℝ)..x, Real.exp (κ * u) * θ u) ∂volume := by
    refine intervalIntegral.integral_add ?_ ?_
    · exact (by fun_prop : Continuous
        (fun s : ℝ ↦ r₀ * Real.exp (-(κ * s)))).intervalIntegrable 0 t
    · have hfc : Continuous (fun u : ℝ ↦ Real.exp (κ * u) * θ u) := by fun_prop
      have hcont : Continuous (fun x : ℝ ↦ ∫ u in (0 : ℝ)..x, Real.exp (κ * u) * θ u) :=
        intervalIntegral.continuous_primitive (fun a b ↦ hfc.intervalIntegrable a b) 0
      exact ((by fun_prop : Continuous
        (fun x : ℝ ↦ Real.exp (-(κ * x)))).mul hcont).intervalIntegrable 0 t
  rw [integratedMean, hsplitint, hadd, intervalIntegral.integral_const_mul,
    integral_exp_neg_eq_bondB κ t hκ, hbeta]

/-- **The integrated HW short rate** in Wiener representation (mirror of
`vasicekIntegratedRate`), defined as `∫₀ᵗ α + σ·∫₀ᵗ g(u) dB_u` — the representation of
`∫₀ᵗ r_s ds` after the time-order swap, which is the modelling bridge — with `g` the
**Vasicek integrated kernel reused verbatim** (`vasicekIntegratedKernelLp`):
integrating the diffusion kernel `e^{−κ(s−u)}` over `s ∈ [u, T]` is
model-independent, so kernel, L²-element and variance all carry over. -/
noncomputable def bondRate (hB : IsPreBrownianReal B μ) (θ : ℝ → ℝ) (κ σ r₀ : ℝ)
    (hκ : 0 < κ) (T : ℝ≥0) (ω : Ω) : ℝ :=
  integratedMean θ κ r₀ (T : ℝ)
    + σ * (wienerIntegralLp B hB T (vasicekIntegratedKernelLp hκ T) ω)

/-- **The HW zero-coupon bond price** — the exponential-Gaussian moment:
`P(0,T) = 𝔼[exp(−bondRate T)] = exp(−∫₀ᵀ α + σ²·V(T)/2)` with `V = vasicekBondV`
the Vasicek variance, unchanged: the Wiener bond-price lemma
`integral_exp_neg_add_mul_wienerIntegralLp` at `m = ∫₀ᵀ α`, `c = σ` and the Vasicek integrated
kernel. -/
theorem bondPrice_eq (hB : IsPreBrownianReal B μ) (θ : ℝ → ℝ) (κ σ r₀ : ℝ)
    (hκ : 0 < κ) (T : ℝ≥0) :
    ∫ ω, Real.exp (-(bondRate hB θ κ σ r₀ hκ T ω)) ∂μ
      = Real.exp (-(integratedMean θ κ r₀ (T : ℝ))
          + σ ^ 2 * vasicekBondV κ (T : ℝ) / 2) :=
  (integral_exp_neg_add_mul_wienerIntegralLp hB T (integratedMean θ κ r₀ (T : ℝ)) σ
    (vasicekIntegratedKernelLp hκ T)).trans <| by rw [vasicekIntegratedKernelLp_integral_sq hκ T]

/-- **Constant forcing, integrated**: with `θ ≡ κ·θ_v` the integrated deterministic part is
Vasicek's `∫₀ᵀ α = r₀·B(T) + θ_v·(T − B(T))` (`κ ≠ 0`): `integratedMean_eq` plus the kernel mass
`∫₀ᵀ B(T − s) ds = (T − B(T))/κ` (`integral_vasicekIntegratedKernel`). -/
theorem integratedMean_const (r₀ θ : ℝ) {κ : ℝ} (hκ : κ ≠ 0) (T : ℝ) :
    integratedMean (fun _ ↦ κ * θ) κ r₀ T = vasicekIntegratedMean r₀ θ κ T := by
  have hmass : ∫ s in (0 : ℝ)..T, vasicekBondB κ (T - s) = (T - vasicekBondB κ T) / κ :=
    integral_vasicekIntegratedKernel κ T hκ
  rw [integratedMean_eq _ continuous_const κ r₀ T hκ, intervalIntegral.integral_const_mul, hmass,
    vasicekIntegratedMean]
  field_simp

omit [IsProbabilityMeasure μ] in
/-- **Hull–White with constant forcing is Vasicek**: with `θ ≡ κ·θ_v`, the integrated HW short
rate is the integrated Vasicek short rate at long-run level `θ_v`, as random variables (same
deterministic part by `integratedMean_const`, same Wiener part by construction). -/
theorem bondRate_const (hB : IsPreBrownianReal B μ) (r₀ θ σ : ℝ) {κ : ℝ} (hκ : 0 < κ)
    (T : ℝ≥0) :
    bondRate hB (fun _ ↦ κ * θ) κ σ r₀ hκ T = vasicekIntegratedRate hB r₀ θ σ hκ T := by
  funext ω
  rw [bondRate, vasicekIntegratedRate, integratedMean_const r₀ θ hκ.ne']

/-- The HW affine coefficient `A(T) = exp(−∫₀ᵀ θ(s)·B(T−s) ds + σ²·V(T)/2)` —
Vasicek's `vasicekBondA` with the constant-drift term `θ_v·(T − B(T))` replaced by
the θ-forcing integral. (`∫₀ᵀ B(T−s)² ds = vasicekBondV κ T`, so the variance
term is exactly `(σ²/2)·∫₀ᵀ B(τ)² dτ`, the standard Hull–White `A`.) -/
noncomputable def bondA (θ : ℝ → ℝ) (σ κ t : ℝ) : ℝ :=
  Real.exp (-(∫ s in (0 : ℝ)..t, θ s * vasicekBondB κ (t - s))
    + σ ^ 2 * vasicekBondV κ t / 2)

/-- **The time-0 affine form**: `P(0,T) = A(T)·exp(−B(T)·r₀)` with `B` the Vasicek
coefficient **verbatim** and `A` carrying the θ-forcing, independent of `r₀` (the exact
analogue of `vasicekBondPrice_affine`). `P(t,T)` for `t > 0` is not formalized. -/
theorem bondPrice_affine (hB : IsPreBrownianReal B μ) (θ : ℝ → ℝ) (κ σ r₀ : ℝ)
    (hθ : Continuous θ) (hκ : 0 < κ) (T : ℝ≥0) :
    ∫ ω, Real.exp (-(bondRate hB θ κ σ r₀ hκ T ω)) ∂μ
      = bondA θ σ κ (T : ℝ) * Real.exp (-(vasicekBondB κ (T : ℝ) * r₀)) := by
  rw [bondPrice_eq hB θ κ σ r₀ hκ T, bondA,
    integratedMean_eq θ hθ κ r₀ (T : ℝ) hκ.ne', ← Real.exp_add]
  congr 1
  ring

/-! ### Calibration — `θ` from the initial forward curve -/

/-- **The calibrated drift**, the calibration formula (justified by
`calibAlpha_solves_ODE` and `reprices_curve`):
`θ(t) = ∂_t f(0,t) + κ·f(0,t) + (σ²/2κ)·(1 − e^{−2κt})` — the initial
instantaneous forward curve's slope, plus mean reversion, plus the HJM convexity
correction. Defined with `deriv` (total, junk off-curve); every theorem below
binds `hf0 : ContDiff ℝ 1 f0`, which packages differentiability of `f0` and
continuity of `deriv f0` (`contDiff_one_iff_deriv`). -/
noncomputable def theta (f0 : ℝ → ℝ) (κ σ : ℝ) (t : ℝ) : ℝ :=
  deriv f0 t + κ * f0 t + (σ ^ 2 / (2 * κ)) * (1 - Real.exp (-(2 * κ * t)))

/-- The closed form `β(t) = f(0,t) + (σ²/2κ²)·(1 − e^{−κt})²` — the initial forward plus
the convexity correction. A definition: that it is the calibrated deterministic part is
`mean_eq_forward` (for `f0 ∈ C¹`, `κ ≠ 0`, `r₀ = f(0,0)`), and that it is the expected short
rate is `calibMean_eq_forward` (for `κ > 0`). -/
noncomputable def calibAlpha (f0 : ℝ → ℝ) (κ σ : ℝ) (t : ℝ) : ℝ :=
  f0 t + (σ ^ 2 / (2 * κ ^ 2)) * (1 - Real.exp (-(κ * t))) ^ 2

/-- `theta` is continuous for a `C¹` curve — `deriv f0` is continuous by
`contDiff_one_iff_deriv`. -/
lemma theta_continuous (f0 : ℝ → ℝ) (hf0 : ContDiff ℝ 1 f0) (κ σ : ℝ) :
    Continuous (theta f0 κ σ) := by
  obtain ⟨_, hdd⟩ := contDiff_one_iff_deriv.mp hf0
  exact (hdd.add (hf0.continuous.const_mul κ)).add
    (by fun_prop : Continuous fun t : ℝ ↦ (σ ^ 2 / (2 * κ)) * (1 - Real.exp (-(2 * κ * t))))

/-- **The calibrated β solves the HW ODE** (verified by differentiation): with `f0` a `C¹` curve,
`β(t) = f(0,t) + (σ²/2κ²)(1 − e^{−κt})²` satisfies
`β'(t) = θ(t) − κ·β(t)` pointwise for `θ = theta f0 κ σ`. Chain rule on β plus the
pointwise algebra `(1 − E²) − (1 − E)² = 2E(1 − E)` (`E = e^{−κt}`); this is what makes the
θ-formula a calibration (sufficient for exact repricing, `reprices_curve`; uniqueness of `θ` is
not proved). -/
theorem calibAlpha_solves_ODE (f0 : ℝ → ℝ) (hf0 : ContDiff ℝ 1 f0) (κ σ : ℝ)
    (hκ : κ ≠ 0) (t : ℝ) :
    HasDerivAt (calibAlpha f0 κ σ) (theta f0 κ σ t - κ * calibAlpha f0 κ σ t) t := by
  have hfd : HasDerivAt f0 (deriv f0 t) t := (hf0.differentiable_one t).hasDerivAt
  have hk : HasDerivAt (fun x : ℝ ↦ κ * x) κ t := by
    simpa using (hasDerivAt_id t).const_mul κ
  have hexp : HasDerivAt (fun x : ℝ ↦ Real.exp (-(κ * x)))
      (Real.exp (-(κ * t)) * (-κ)) t := hk.neg.exp
  have hsub : HasDerivAt (fun x : ℝ ↦ 1 - Real.exp (-(κ * x)))
      (κ * Real.exp (-(κ * t))) t := by
    have h0 := (hasDerivAt_const t 1).sub hexp
    rwa [show (0 : ℝ) - Real.exp (-(κ * t)) * (-κ)
        = κ * Real.exp (-(κ * t)) from by ring] at h0
  have hsq : HasDerivAt (fun x : ℝ ↦ (1 - Real.exp (-(κ * x))) ^ 2)
      (2 * (1 - Real.exp (-(κ * t))) * (κ * Real.exp (-(κ * t)))) t := by
    have h0 := hsub.mul hsub
    rw [show κ * Real.exp (-(κ * t)) * (1 - Real.exp (-(κ * t)))
          + (1 - Real.exp (-(κ * t))) * (κ * Real.exp (-(κ * t)))
          = 2 * (1 - Real.exp (-(κ * t))) * (κ * Real.exp (-(κ * t))) from by ring] at h0
    exact h0.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y ↦ pow_two _)
  have hcm : HasDerivAt
      (fun x : ℝ ↦ (σ ^ 2 / (2 * κ ^ 2)) * (1 - Real.exp (-(κ * x))) ^ 2)
      ((σ ^ 2 / (2 * κ ^ 2)) * (2 * (1 - Real.exp (-(κ * t)))
          * (κ * Real.exp (-(κ * t))))) t := hsq.const_mul (σ ^ 2 / (2 * κ ^ 2))
  have hE2 : Real.exp (-(2 * κ * t)) = Real.exp (-(κ * t)) ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hval : theta f0 κ σ t - κ * calibAlpha f0 κ σ t
      = deriv f0 t + (σ ^ 2 / (2 * κ ^ 2)) * (2 * (1 - Real.exp (-(κ * t)))
          * (κ * Real.exp (-(κ * t)))) := by
    simp only [theta, calibAlpha, hE2]
    field_simp
    ring
  rw [hval]
  exact hfd.add hcm

/-- **The calibrated deterministic part**: the HW particular solution driven by `theta`
and started at the initial forward `r₀ = f(0,0)` is exactly
`β(t) = f(0,t) + (σ²/2κ²)(1 − e^{−κt})²` — the initial forward plus the convexity
correction (`calibMean_eq_forward` turns it into the expected short rate). Route:
`calibAlpha_solves_ODE` (verified by differentiation) + ODE uniqueness
(`deterministic_eq_of_solves_ODE`; note
`β(0) = f(0,0)` automatically, since `(1 − e^{−κ·0})² = 0`). Only `κ ≠ 0` is
needed — the θ-formula divides by κ; no positivity enters the deterministic
identity. -/
theorem mean_eq_forward (f0 : ℝ → ℝ) (hf0 : ContDiff ℝ 1 f0) (κ σ : ℝ) (hκ : κ ≠ 0) (t : ℝ) :
    deterministic (theta f0 κ σ) κ (f0 0) t
      = f0 t + (σ ^ 2 / (2 * κ ^ 2)) * (1 - Real.exp (-(κ * t))) ^ 2 := by
  have h := deterministic_eq_of_solves_ODE (theta f0 κ σ)
    (theta_continuous f0 hf0 κ σ) κ (calibAlpha f0 κ σ)
    (fun s ↦ calibAlpha_solves_ODE f0 hf0 κ σ hκ s) t
  rwa [show calibAlpha f0 κ σ 0 = f0 0 from by simp [calibAlpha]] at h

/-- **The calibrated deterministic part, for `κ > 0`** (`mean_eq_forward`): the HW
particular solution driven by `theta` and
started at the initial forward `r₀ = f(0,0)` is exactly
`β(t) = f(0,t) + (σ²/2κ²)(1 − e^{−κt})²` — `calibAlpha_solves_ODE` + ODE
uniqueness (`deterministic_eq_of_solves_ODE`; note `β(0) = f(0,0)`
automatically, since `(1 − e^{−κ·0})² = 0`). -/
theorem calibMean (f0 : ℝ → ℝ) (hf0 : ContDiff ℝ 1 f0) (κ σ : ℝ) (hκ : 0 < κ) (t : ℝ) :
    deterministic (theta f0 κ σ) κ (f0 0) t
      = f0 t + (σ ^ 2 / (2 * κ ^ 2)) * (1 - Real.exp (-(κ * t))) ^ 2 :=
  mean_eq_forward f0 hf0 κ σ hκ.ne' t

/-- **The mean identity at the law level**: `𝔼[r_t] = f(0,t) +
(σ²/2κ²)(1 − e^{−κt})²` — the expected HW short rate under calibration is the
initial forward plus the convexity correction (the centred Gaussian part
contributes zero: `integratedRate_hasLaw_gaussian` +
`integral_id_gaussianReal`). -/
theorem calibMean_eq_forward (hB : IsPreBrownianReal B μ) (f0 : ℝ → ℝ)
    (hf0 : ContDiff ℝ 1 f0) (κ σ : ℝ) (hκ : 0 < κ) (t : ℝ≥0) :
    ∫ ω, integratedRate hB (theta f0 κ σ) κ σ (f0 0) hκ t ω ∂μ
      = f0 (t : ℝ) + (σ ^ 2 / (2 * κ ^ 2)) * (1 - Real.exp (-(κ * (t : ℝ)))) ^ 2 := by
  have hlaw := integratedRate_hasLaw_gaussian hB (theta f0 κ σ) κ σ (f0 0) hκ t
  rw [hlaw.integral_eq, integral_id_gaussianReal,
    calibMean f0 hf0 κ σ hκ (t : ℝ)]

/-- **The variance identity for calibration**: `V(T) = ∫₀ᵀ B(u)² du` in interval
form. Route: `vasicekIntegratedKernel_integral_sq` gives the `Ioc`-integral of
the integrated kernel `g(u) = B(T−u)`; `intervalIntegral.integral_of_le` moves to
interval form, the integrand is `vasicekBondB κ (T−u)` definitionally, and the
reflection `∫₀ᵀ φ(u) du = ∫₀ᵀ φ(T−u) du` (`integral_comp_sub_left`) lands on
`B(u)` — the L²-norm is symmetric under `u ↦ T−u`. -/
lemma var_eq_interval (κ : ℝ) (hκ : κ ≠ 0) (𝕋 : ℝ≥0) :
    vasicekBondV κ (𝕋 : ℝ) = ∫ u in (0 : ℝ)..(𝕋 : ℝ), (vasicekBondB κ u) ^ 2 := by
  have href : ∫ u in (0 : ℝ)..(𝕋 : ℝ), (vasicekBondB κ u) ^ 2
      = ∫ u in (0 : ℝ)..(𝕋 : ℝ), (vasicekBondB κ ((𝕋 : ℝ) - u)) ^ 2 := by
    rw [intervalIntegral.integral_comp_sub_left
      (f := fun u : ℝ ↦ (vasicekBondB κ u) ^ 2) (𝕋 : ℝ)]
    simp
  have h2 := vasicekIntegratedKernel_integral_sq hκ 𝕋
  have h3 : (∫ u in Set.Ioc (0 : ℝ) (𝕋 : ℝ),
      (vasicekIntegratedKernel κ (𝕋 : ℝ) u) ^ 2 ∂volume)
      = ∫ u in (0 : ℝ)..(𝕋 : ℝ), (vasicekIntegratedKernel κ (𝕋 : ℝ) u) ^ 2 ∂volume :=
    (intervalIntegral.integral_of_le 𝕋.prop).symm
  rw [← h2, h3, intervalIntegral.integral_congr
    (show EqOn (fun u : ℝ ↦ (vasicekIntegratedKernel κ (𝕋 : ℝ) u) ^ 2)
      (fun u : ℝ ↦ (vasicekBondB κ ((𝕋 : ℝ) - u)) ^ 2) (Set.uIcc (0 : ℝ) (𝕋 : ℝ))
      from fun u _ ↦ rfl)]
  exact href.symm

/-- The κ²-scaling bridge: `κ²·∫₀ᵀ B(u)² du = ∫₀ᵀ (1 − e^{−κu})² du` — pure
pointwise algebra on `B(u) = (1 − e^{−κu})/κ`. -/
private lemma calibVar_key (κ : ℝ) (hκ : κ ≠ 0) (𝕋 : ℝ≥0) :
    κ ^ 2 * (∫ s in (0 : ℝ)..(𝕋 : ℝ), (vasicekBondB κ s) ^ 2)
      = ∫ s in (0 : ℝ)..(𝕋 : ℝ), (1 - Real.exp (-(κ * s))) ^ 2 := by
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr
    (show EqOn (fun s : ℝ ↦ κ ^ 2 * (vasicekBondB κ s) ^ 2)
      (fun s : ℝ ↦ (1 - Real.exp (-(κ * s))) ^ 2) (Set.uIcc (0 : ℝ) (𝕋 : ℝ))
      from fun s _ ↦ ?_)
  change κ ^ 2 * ((1 - Real.exp (-(κ * s))) / κ) ^ 2 = (1 - Real.exp (-(κ * s))) ^ 2
  field_simp

/-- **The convexity-correction integral in isolation**:
`∫₀ᵀ (σ²/2κ²)(1 − e^{−κs})² ds = (σ²/2)·V(T)` — the mean-correction term of
`mean_eq_forward`, integrated, equals half the integrated-rate variance: the
exact quantity the Gaussian bond moment's `σ²V/2` cancels, which is why
`reprices_curve` is exact (`calibIntegratedMean` = `∫₀ᵀ f0` + this). -/
theorem calibCorrection_integral (κ σ : ℝ) (hκ : κ ≠ 0) (𝕋 : ℝ≥0) :
    ∫ s in (0 : ℝ)..(𝕋 : ℝ), (σ ^ 2 / (2 * κ ^ 2)) * (1 - Real.exp (-(κ * s))) ^ 2
      = σ ^ 2 / 2 * vasicekBondV κ (𝕋 : ℝ) := by
  rw [intervalIntegral.integral_const_mul (r := (σ ^ 2 / (2 * κ ^ 2)))
      (f := fun s : ℝ ↦ (1 - Real.exp (-(κ * s))) ^ 2),
    ← calibVar_key κ hκ 𝕋, ← var_eq_interval κ hκ 𝕋]
  field_simp

/-- **The calibrated integrated mean**: `∫₀ᵀ α(s) ds = ∫₀ᵀ f(0,s) ds +
(σ²/2)·V(T)` — the forward-discount integral plus half the integrated-rate
variance. This is the identity the repricing exactness lives on: the convexity
correction in the mean exactly offsets the `σ²V/2` in the Gaussian moment. -/
theorem calibIntegratedMean (f0 : ℝ → ℝ) (hf0 : ContDiff ℝ 1 f0) (κ σ : ℝ)
    (hκ : 0 < κ) (𝕋 : ℝ≥0) :
    integratedMean (theta f0 κ σ) κ (f0 0) (𝕋 : ℝ)
      = (∫ s in (0 : ℝ)..(𝕋 : ℝ), f0 s) + σ ^ 2 / 2 * vasicekBondV κ (𝕋 : ℝ) := by
  have hfa : IntervalIntegrable f0 volume (0 : ℝ) (𝕋 : ℝ) :=
    hf0.continuous.intervalIntegrable _ _
  have hgb : IntervalIntegrable (fun s : ℝ ↦ (σ ^ 2 / (2 * κ ^ 2))
      * (1 - Real.exp (-(κ * s))) ^ 2) volume (0 : ℝ) (𝕋 : ℝ) :=
    (by fun_prop : Continuous fun s : ℝ ↦ (σ ^ 2 / (2 * κ ^ 2))
      * (1 - Real.exp (-(κ * s))) ^ 2).intervalIntegrable _ _
  unfold integratedMean
  rw [intervalIntegral.integral_congr
    (show EqOn (fun s : ℝ ↦ deterministic (theta f0 κ σ) κ (f0 0) s)
      (fun s : ℝ ↦ f0 s + (σ ^ 2 / (2 * κ ^ 2)) * (1 - Real.exp (-(κ * s))) ^ 2)
      (Set.uIcc (0 : ℝ) (𝕋 : ℝ)) from fun s _ ↦ calibMean f0 hf0 κ σ hκ s),
    intervalIntegral.integral_add hfa hgb, calibCorrection_integral κ σ hκ.ne' 𝕋]

/-- **The repricing identity** (the headline): with `θ = theta f0 κ σ` and the short
rate started at `r₀ = f(0,0)` (`f0 ∈ C¹`, `κ > 0`), the HW model's time-0 bond curve
reprices the market curve read off the initial forwards:
`𝔼[exp(−bondRate T)] = exp(−∫₀ᵀ f(0,s) ds) = P^mkt(0,T)`.
Route: `bondPrice_eq` (the exponential-Gaussian moment) +
`calibIntegratedMean` (`∫₀ᵀ α = ∫₀ᵀ f0 + σ²V/2`) — the `σ²V/2` cancels. -/
theorem reprices_curve (hB : IsPreBrownianReal B μ) (f0 : ℝ → ℝ)
    (hf0 : ContDiff ℝ 1 f0) (κ σ : ℝ) (hκ : 0 < κ) (T : ℝ≥0) :
    ∫ ω, Real.exp (-(bondRate hB (theta f0 κ σ) κ σ (f0 0) hκ T ω)) ∂μ
      = Real.exp (-(∫ s in (0 : ℝ)..(T : ℝ), f0 s)) := by
  rw [bondPrice_eq hB (theta f0 κ σ) κ σ (f0 0) hκ T,
    calibIntegratedMean f0 hf0 κ σ hκ T]
  congr 1
  ring

end MathFin.HullWhite
