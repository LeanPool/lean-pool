/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.Jumps.JumpDiffusionProcess
public import LeanPool.MathFin.Probability.Laws.Esscher
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# The law at one date determines the drift, the Gaussian variance and the Lévy measure

When the jump laws' moment-generating functions are finite near `0`, the log-return law over a time
`τ > 0` of a jump-diffusion with drift `b`, volatility coefficient `σ`, jump rate `Λ` and jump law
`ν` (`jumpDiffusionIncrementLaw`) determines the drift `b`, the Gaussian variance `σ²` and the Lévy
measure `Λν` away from `0`. The sign of `σ` is not determined, since the Gaussian part is
symmetric, and the rate `Λ` and the jump law `ν` enter only through their product off `0`: jumps
of size `0` do not move the log-price. This is the uniqueness in the
Lévy–Khintchine representation for compound-Poisson jumps with exponential moments near `0`, read
off a single date. The full uniqueness needs no moment conditions.

* `jumpDiffusionExponent_eq_levy`: `κ(u) = bu + σ²u²/2 + ∫ (e^{ux} − 1) Π(dx)` wherever
  `∫ e^{ux} dν < ∞`, where `Π` is `Λν` restricted to `x ≠ 0`. The Laplace exponent sees the jumps
  only through `Π`.
* `mgf_id_secondDifferenceMeasure`: where `ν` has the exponential moments of orders `u ± s` and
  `u`, the second difference `κ(u + s) + κ(u − s) − 2κ(u)` is the moment-generating function at
  `u` of the finite measure `σ²s²·δ₀ + 2(cosh(sx) − 1)·Λν` (`secondDifferenceMeasure`). Its atom
  at `0` is the Gaussian part and off `0` it is the jumps, as in Kolmogorov's canonical measure
  `σ²δ₀ + x²Π(dx)`.
* `jumpDiffusionIncrementLaw_eq_iff`: for jump laws whose moment-generating functions are finite
  near `0`, two log-return laws at the same date `τ > 0` are equal iff their drifts agree, their
  Gaussian variances agree and their Lévy measures agree off `0`.

The proof reads `κ` off the law near `0` (`mgf_id_jumpDiffusionIncrementLaw`) and takes second
differences in `u`, which cancel the drift. Equal laws give second-difference measures with the
same moment-generating function near `0`, hence equal measures
(`measure_eq_of_mgf_id_eventuallyEq`).
Their atoms at `0` give `σ²`. Off `0`, dividing by `2(cosh(sx) − 1)`, which vanishes only at `0`,
gives `Π`. Then `κ` at one point gives `b`.

## Main definitions

* `coshKernel`: the second-difference kernel `2(cosh(sx) − 1)`, as a nonnegative real density.
* `secondDifferenceMeasure`: the measure `σ²s² · δ₀ + 2(cosh(sx) − 1) · Λν`, whose
  moment-generating function at `u` is the second difference of the Laplace exponent with
  step `s`.

## Main results

* `coshKernel_eq_zero_iff`: for `s ≠ 0` the kernel vanishes only at `0`.
* `jumpDiffusionExponent_eq_levy`: wherever `∫ e^{ux} dν < ∞`,
  `κ(u) = bu + σ²u²/2 + ∫ (e^{ux} − 1) dΠ`, with `Π` the measure `Λν` restricted to `x ≠ 0`.
* `mgf_id_secondDifferenceMeasure`: where `ν` has the exponential moments of orders `u + s`,
  `u − s` and `u`, `κ(u + s) + κ(u − s) − 2κ(u)` is the moment-generating function at `u` of
  `secondDifferenceMeasure σ s Λ ν`.
* `secondDifferenceMeasure_singleton_zero`: its atom at `0` is `σ²s²`.
* `restrict_compl_zero_secondDifferenceMeasure`: off `0` it is the kernel times the Lévy
  measure.
* `eventually_jumpDiffusionExponent_eq`: equal log-return laws at a date `τ > 0` have equal
  Laplace exponents near `0`, when the jump laws have exponential moments near `0`.
* `jumpDiffusionIncrementLaw_eq_iff`: for jump laws with moment-generating functions finite
  near `0` and `τ > 0`, two log-return laws agree iff the drifts agree, the Gaussian variances
  `σ²` agree and the Lévy measures `Λν` agree off `0`.

## References

* [Cont and Tankov, *Financial Modelling with Jump Processes*][ContTankov2004]
* [Sato, *Lévy Processes and Infinitely Divisible Distributions*][Sato1999]

## Tags

identifiability, Lévy measure, calibration from one date, moment generating function,
drift and variance recovery, MSC 60G51, MSC 91G20, MSC 62F10
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real Filter Set
open scoped NNReal ENNReal Topology

/-- The second-difference kernel `2(cosh(sx) − 1) = e^{sx} + e^{−sx} − 2`, as a density: the second
difference of `u ↦ e^{ux}` with step `s` is `e^{ux}` times it (`coshKernel_smul_exp`). -/
noncomputable def coshKernel (s x : ℝ) : ℝ≥0 := Real.toNNReal (2 * (Real.cosh (s * x) - 1))

lemma coe_coshKernel (s x : ℝ) : (coshKernel s x : ℝ) = 2 * (Real.cosh (s * x) - 1) :=
  Real.coe_toNNReal _ (by linarith [Real.one_le_cosh (s * x)])

lemma measurable_coshKernel (s : ℝ) : Measurable (coshKernel s) :=
  (by fun_prop : Measurable fun x ↦ 2 * (Real.cosh (s * x) - 1)).real_toNNReal

/-- For `s ≠ 0` the kernel vanishes only at `0`. -/
lemma coshKernel_eq_zero_iff {s : ℝ} (hs : s ≠ 0) {x : ℝ} : coshKernel s x = 0 ↔ x = 0 := by
  rw [coshKernel, Real.toNNReal_eq_zero]
  refine ⟨fun h ↦ Classical.byContradiction fun hx ↦ ?_, fun hx ↦ by simp [hx]⟩
  linarith [Real.one_lt_cosh.2 (mul_ne_zero hs hx)]

/-- The second difference of `u ↦ e^{ux}` with step `s`:
`2(cosh(sx) − 1)·e^{ux} = e^{(u+s)x} + e^{(u−s)x} − 2e^{ux}`. -/
lemma coshKernel_smul_exp (s u x : ℝ) :
    coshKernel s x • rexp (u * x)
      = rexp ((u + s) * x) + rexp ((u - s) * x) - 2 * rexp (u * x) := by
  rw [NNReal.smul_def, smul_eq_mul, coe_coshKernel, Real.cosh_eq,
    show (u + s) * x = u * x + s * x by ring, show (u - s) * x = u * x + -(s * x) by ring,
    Real.exp_add, Real.exp_add]
  ring

lemma integrable_coshKernel_smul_exp {ν : Measure ℝ} {s u : ℝ}
    (hp : Integrable (fun x ↦ rexp ((u + s) * x)) ν)
    (hm : Integrable (fun x ↦ rexp ((u - s) * x)) ν) (h0 : Integrable (fun x ↦ rexp (u * x)) ν) :
    Integrable (fun x ↦ coshKernel s x • rexp (u * x)) ν := by
  simp_rw [coshKernel_smul_exp]
  exact (hp.add hm).sub (h0.const_mul 2)

/-- **The kernel turns second differences of exponential moments into one integral**:
`∫ 2(cosh(sx) − 1)e^{ux} dν = ∫ e^{(u+s)x} dν + ∫ e^{(u−s)x} dν − 2∫ e^{ux} dν`. -/
lemma integral_coshKernel_smul_exp {ν : Measure ℝ} {s u : ℝ}
    (hp : Integrable (fun x ↦ rexp ((u + s) * x)) ν)
    (hm : Integrable (fun x ↦ rexp ((u - s) * x)) ν) (h0 : Integrable (fun x ↦ rexp (u * x)) ν) :
    ∫ x, coshKernel s x • rexp (u * x) ∂ν
      = ∫ x, rexp ((u + s) * x) ∂ν + ∫ x, rexp ((u - s) * x) ∂ν - 2 * ∫ x, rexp (u * x) ∂ν := by
  have hpm : Integrable (fun x ↦ rexp ((u + s) * x) + rexp ((u - s) * x)) ν := hp.add hm
  simp_rw [coshKernel_smul_exp]
  rw [integral_sub hpm (h0.const_mul 2), integral_add hp hm, integral_const_mul]

/-- The kernel measure `2(cosh(sx) − 1)·Λν` has the exponential moment of order `u` when `ν` has
those of orders `u + s`, `u − s` and `u`. -/
lemma integrable_exp_mul_withDensity_coshKernel (Λ : ℝ≥0) {ν : Measure ℝ} {s u : ℝ}
    (hp : Integrable (fun x ↦ rexp ((u + s) * x)) ν)
    (hm : Integrable (fun x ↦ rexp ((u - s) * x)) ν) (h0 : Integrable (fun x ↦ rexp (u * x)) ν) :
    Integrable (fun x ↦ rexp (u * x)) ((Λ • ν).withDensity fun x ↦ coshKernel s x) :=
  (integrable_withDensity_iff_integrable_smul (measurable_coshKernel s)).2
    (integrable_coshKernel_smul_exp hp hm h0).smul_measure_nnreal

/-- **The moment-generating function of the kernel measure** at `u` is `Λ` times the second
difference of the moment-generating function of `ν`, when `ν` has the exponential moments of
orders `u + s`, `u − s` and `u`. -/
lemma mgf_id_withDensity_coshKernel (Λ : ℝ≥0) {ν : Measure ℝ} {s u : ℝ}
    (hp : Integrable (fun x ↦ rexp ((u + s) * x)) ν)
    (hm : Integrable (fun x ↦ rexp ((u - s) * x)) ν) (h0 : Integrable (fun x ↦ rexp (u * x)) ν) :
    mgf id ((Λ • ν).withDensity fun x ↦ coshKernel s x) u
      = Λ * (∫ x, rexp ((u + s) * x) ∂ν + ∫ x, rexp ((u - s) * x) ∂ν
          - 2 * ∫ x, rexp (u * x) ∂ν) := by
  change ∫ x, rexp (u * x) ∂((Λ • ν).withDensity fun x ↦ coshKernel s x) = _
  rw [integral_withDensity_eq_integral_smul (measurable_coshKernel s),
    integral_smul_nnreal_measure, integral_coshKernel_smul_exp hp hm h0, NNReal.smul_def,
    smul_eq_mul]

/-- The kernel measure is finite when `ν` has the exponential moments of orders `s` and `−s`. -/
lemma isFiniteMeasure_withDensity_coshKernel (Λ : ℝ≥0) {ν : Measure ℝ} [IsFiniteMeasure ν]
    {s : ℝ} (hp : Integrable (fun x ↦ rexp (s * x)) ν)
    (hm : Integrable (fun x ↦ rexp (-s * x)) ν) :
    IsFiniteMeasure ((Λ • ν).withDensity fun x ↦ coshKernel s x) := by
  have h := integrable_exp_mul_withDensity_coshKernel Λ (u := 0) (s := s)
    (by simpa only [zero_add] using hp) (by simpa only [zero_sub] using hm)
    (by simpa only [zero_mul, Real.exp_zero] using integrable_const (1 : ℝ))
  simp only [zero_mul, Real.exp_zero] at h
  exact (integrable_const_iff.1 h).resolve_left one_ne_zero

/-- Off `0` the kernel is positive and finite, so dividing the kernel measure by it gives back the
measure restricted to `x ≠ 0`. -/
lemma restrict_compl_zero_eq_withDensity_inv {s : ℝ} (hs : s ≠ 0) (μ : Measure ℝ) :
    μ.restrict {0}ᶜ = ((μ.withDensity fun x ↦ coshKernel s x).restrict {0}ᶜ).withDensity
      fun x ↦ (coshKernel s x : ℝ≥0∞)⁻¹ := by
  rw [restrict_withDensity (measurableSet_singleton (0 : ℝ)).compl, withDensity_inv_same
    (measurable_coshKernel s).coe_nnreal_ennreal ?_ (ae_of_all _ fun _ ↦ ENNReal.coe_ne_top)]
  filter_upwards [ae_restrict_mem (measurableSet_singleton (0 : ℝ)).compl] with x hx
  exact ENNReal.coe_ne_zero.2 ((coshKernel_eq_zero_iff hs).not.2 (mem_compl_singleton_iff.1 hx))

/-- **The second-difference measure** `σ²s²·δ₀ + 2(cosh(sx) − 1)·Λν`. Its moment-generating
function at `u` is the second difference of the Laplace exponent with step `s`, where `ν` has the
exponential moments of orders `u ± s` and `u` (`mgf_id_secondDifferenceMeasure`). Its atom at `0`
is the Gaussian part `σ²s²` (`secondDifferenceMeasure_singleton_zero`), and off `0` it is the
kernel times the Lévy measure (`restrict_compl_zero_secondDifferenceMeasure`). -/
noncomputable def secondDifferenceMeasure (σ s : ℝ) (Λ : ℝ≥0) (ν : Measure ℝ) : Measure ℝ :=
  (σ ^ 2 * s ^ 2).toNNReal • Measure.dirac 0 + (Λ • ν).withDensity fun x ↦ coshKernel s x

/-- The second-difference measure is finite when `ν` has the exponential moments of orders `s` and
`−s`. -/
lemma isFiniteMeasure_secondDifferenceMeasure (σ : ℝ) (Λ : ℝ≥0) {ν : Measure ℝ}
    [IsFiniteMeasure ν] {s : ℝ} (hp : Integrable (fun x ↦ rexp (s * x)) ν)
    (hm : Integrable (fun x ↦ rexp (-s * x)) ν) :
    IsFiniteMeasure (secondDifferenceMeasure σ s Λ ν) := by
  have := isFiniteMeasure_withDensity_coshKernel Λ hp hm
  unfold secondDifferenceMeasure
  infer_instance

/-- The second-difference measure has the exponential moment of order `u` when `ν` has those of
orders `u + s`, `u − s` and `u`. -/
lemma integrable_exp_mul_secondDifferenceMeasure (σ : ℝ) (Λ : ℝ≥0) {ν : Measure ℝ} {s u : ℝ}
    (hp : Integrable (fun x ↦ rexp ((u + s) * x)) ν)
    (hm : Integrable (fun x ↦ rexp ((u - s) * x)) ν) (h0 : Integrable (fun x ↦ rexp (u * x)) ν) :
    Integrable (fun x ↦ rexp (u * x)) (secondDifferenceMeasure σ s Λ ν) :=
  (integrable_dirac (f := fun x : ℝ ↦ rexp (u * x)) (a := 0) eNorm_lt_top).smul_measure_nnreal
    |>.add_measure (integrable_exp_mul_withDensity_coshKernel Λ hp hm h0)

/-- **The second difference of the Laplace exponent is a moment-generating function**:
`κ(u + s) + κ(u − s) − 2κ(u) = σ²s² + Λ(m(u + s) + m(u − s) − 2m(u))`, the moment-generating
function at `u` of `σ²s²·δ₀ + 2(cosh(sx) − 1)·Λν`, when `ν` has the exponential moments of orders
`u + s`, `u − s` and `u`. The drift cancels. -/
lemma mgf_id_secondDifferenceMeasure (b σ : ℝ) (Λ : ℝ≥0) {ν : Measure ℝ} {s u : ℝ}
    (hp : Integrable (fun x ↦ rexp ((u + s) * x)) ν)
    (hm : Integrable (fun x ↦ rexp ((u - s) * x)) ν) (h0 : Integrable (fun x ↦ rexp (u * x)) ν) :
    mgf id (secondDifferenceMeasure σ s Λ ν) u
      = jumpDiffusionExponent b σ Λ ν (u + s) + jumpDiffusionExponent b σ Λ ν (u - s)
        - 2 * jumpDiffusionExponent b σ Λ ν u := by
  have hW : ∫ x, rexp (u * x) ∂((Λ • ν).withDensity fun x ↦ coshKernel s x)
      = Λ * (∫ x, rexp ((u + s) * x) ∂ν + ∫ x, rexp ((u - s) * x) ∂ν
          - 2 * ∫ x, rexp (u * x) ∂ν) :=
    mgf_id_withDensity_coshKernel Λ hp hm h0
  change ∫ x, rexp (u * x) ∂(secondDifferenceMeasure σ s Λ ν) = _
  rw [secondDifferenceMeasure, integral_add_measure
      (integrable_dirac (f := fun x : ℝ ↦ rexp (u * x)) (a := 0) eNorm_lt_top).smul_measure_nnreal
      (integrable_exp_mul_withDensity_coshKernel Λ hp hm h0),
    integral_smul_nnreal_measure, integral_dirac, hW, mul_zero, Real.exp_zero, NNReal.smul_def,
    smul_eq_mul, mul_one, Real.coe_toNNReal _ (by positivity)]
  simp only [jumpDiffusionExponent]
  ring

/-- **The atom of the second-difference measure at `0` is the Gaussian part** `σ²s²`: the kernel
vanishes at `0`. -/
lemma secondDifferenceMeasure_singleton_zero (σ s : ℝ) (Λ : ℝ≥0) (ν : Measure ℝ) :
    secondDifferenceMeasure σ s Λ ν {0} = ENNReal.ofReal (σ ^ 2 * s ^ 2) := by
  have hW : ((Λ • ν).withDensity fun x ↦ coshKernel s x) {0} = 0 := by
    rw [withDensity_apply_eq_zero (measurable_coshKernel s).coe_nnreal_ennreal]
    refine measure_mono_null (fun x ⟨hx0, hx1⟩ ↦ ?_) measure_empty
    rw [mem_singleton_iff.1 hx1] at hx0
    simp [coshKernel] at hx0
  rw [show ENNReal.ofReal (σ ^ 2 * s ^ 2) = ((σ ^ 2 * s ^ 2).toNNReal : ℝ≥0∞) from rfl,
    secondDifferenceMeasure, add_apply, hW, add_zero, Measure.coe_nnreal_smul_apply,
    Measure.dirac_apply_of_mem (mem_singleton (0 : ℝ)), mul_one]

/-- **Off `0` the second-difference measure is the kernel times the Lévy measure**: the atom
lives at `0`. -/
lemma restrict_compl_zero_secondDifferenceMeasure (σ s : ℝ) (Λ : ℝ≥0) (ν : Measure ℝ) :
    (secondDifferenceMeasure σ s Λ ν).restrict {0}ᶜ
      = ((Λ • ν).withDensity fun x ↦ coshKernel s x).restrict {0}ᶜ := by
  have hδ : (Measure.dirac (0 : ℝ)).restrict {0}ᶜ = 0 :=
    Measure.restrict_eq_zero.2 ((dirac_eq_zero_iff_notMem (measurableSet_singleton 0).compl).2
      (by simp))
  rw [secondDifferenceMeasure, Measure.restrict_add, Measure.restrict_smul, hδ, smul_zero,
    zero_add]

/-- **The Lévy–Khintchine form of the Laplace exponent**: wherever `∫ e^{ux} dν < ∞`,
`κ(u) = bu + σ²u²/2 + ∫ (e^{ux} − 1) Π(dx)`, where `Π` is the Lévy measure `Λν` restricted to
`x ≠ 0`. Jumps of size `0` contribute nothing. -/
lemma jumpDiffusionExponent_eq_levy (b σ : ℝ) (Λ : ℝ≥0) {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {u : ℝ} (hu : Integrable (fun x ↦ rexp (u * x)) ν) :
    jumpDiffusionExponent b σ Λ ν u
      = b * u + σ ^ 2 * u ^ 2 / 2 + ∫ x, (rexp (u * x) - 1) ∂((Λ • ν).restrict {0}ᶜ) := by
  have hf : Integrable (fun x ↦ rexp (u * x) - 1) (Λ • ν) :=
    (hu.sub (integrable_const 1)).smul_measure_nnreal
  have h0 : ∫ x in {0}, (rexp (u * x) - 1) ∂(Λ • ν) = 0 :=
    setIntegral_eq_zero_of_forall_eq_zero fun x hx ↦ by simp [mem_singleton_iff.1 hx]
  have h := integral_add_compl (measurableSet_singleton (0 : ℝ)) hf
  rw [h0, zero_add, integral_smul_nnreal_measure, integral_sub hu (integrable_const 1),
    integral_const, probReal_univ, one_smul, NNReal.smul_def, smul_eq_mul] at h
  rw [jumpDiffusionExponent, h]

/-- Equal log-return laws at a date `τ > 0` have equal Laplace exponents near `0`, where the jump
laws have exponential moments. -/
lemma eventually_jumpDiffusionExponent_eq {b₁ b₂ σ₁ σ₂ : ℝ} {Λ₁ Λ₂ : ℝ≥0} {ν₁ ν₂ : Measure ℝ}
    [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂]
    (h₁ : 0 ∈ interior (integrableExpSet id ν₁)) (h₂ : 0 ∈ interior (integrableExpSet id ν₂))
    {τ : ℝ≥0} (hτ : 0 < τ)
    (h : jumpDiffusionIncrementLaw b₁ σ₁ Λ₁ ν₁ τ = jumpDiffusionIncrementLaw b₂ σ₂ Λ₂ ν₂ τ) :
    ∀ᶠ u in 𝓝 (0 : ℝ),
      jumpDiffusionExponent b₁ σ₁ Λ₁ ν₁ u = jumpDiffusionExponent b₂ σ₂ Λ₂ ν₂ u := by
  filter_upwards [mem_interior_iff_mem_nhds.1 h₁, mem_interior_iff_mem_nhds.1 h₂] with u hu₁ hu₂
  have e : mgf id (jumpDiffusionIncrementLaw b₁ σ₁ Λ₁ ν₁ τ) u
      = mgf id (jumpDiffusionIncrementLaw b₂ σ₂ Λ₂ ν₂ τ) u := by rw [h]
  rw [mgf_id_jumpDiffusionIncrementLaw b₁ σ₁ Λ₁
      (hu₁ : Integrable (fun x ↦ rexp (u * x)) ν₁) τ,
    mgf_id_jumpDiffusionIncrementLaw b₂ σ₂ Λ₂ (hu₂ : Integrable (fun x ↦ rexp (u * x)) ν₂) τ,
    Real.exp_eq_exp] at e
  exact mul_right_cancel₀ (NNReal.coe_ne_zero.2 hτ.ne') e

/-- **The law at one date determines the drift, the Gaussian variance and the Lévy measure.**
For jump laws whose moment-generating functions are finite near `0`, two jump-diffusion log-return
laws at the same date `τ > 0` are equal iff their drifts agree, their Gaussian variances `σ²` agree
and their Lévy measures `Λν` agree off `0`. -/
theorem jumpDiffusionIncrementLaw_eq_iff {b₁ b₂ σ₁ σ₂ : ℝ} {Λ₁ Λ₂ : ℝ≥0} {ν₁ ν₂ : Measure ℝ}
    [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂]
    (h₁ : 0 ∈ interior (integrableExpSet id ν₁)) (h₂ : 0 ∈ interior (integrableExpSet id ν₂))
    {τ : ℝ≥0} (hτ : 0 < τ) :
    jumpDiffusionIncrementLaw b₁ σ₁ Λ₁ ν₁ τ = jumpDiffusionIncrementLaw b₂ σ₂ Λ₂ ν₂ τ ↔
      b₁ = b₂ ∧ σ₁ ^ 2 = σ₂ ^ 2 ∧ (Λ₁ • ν₁).restrict {0}ᶜ = (Λ₂ • ν₂).restrict {0}ᶜ := by
  -- near `0` both jump laws have exponential moments
  have hD₁ : ∀ᶠ u in 𝓝 (0 : ℝ), Integrable (fun x ↦ rexp (u * x)) ν₁ :=
    eventually_mem_set.2 (mem_interior_iff_mem_nhds.1 h₁)
  have hD₂ : ∀ᶠ u in 𝓝 (0 : ℝ), Integrable (fun x ↦ rexp (u * x)) ν₂ :=
    eventually_mem_set.2 (mem_interior_iff_mem_nhds.1 h₂)
  constructor
  · intro h
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1
      (hD₁.and (hD₂.and (eventually_jumpDiffusionExponent_eq h₁ h₂ hτ h)))
    have hin (y : ℝ) (hy₁ : -ε < y) (hy₂ : y < ε) := hball y (by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
      exact ⟨hy₁, hy₂⟩)
    have hs : ε / 2 ≠ 0 := (half_pos hε).ne'
    have := isFiniteMeasure_secondDifferenceMeasure σ₁ Λ₁ (s := ε / 2)
      (hin (ε / 2) (by linarith) (by linarith)).1 (hin (-(ε / 2)) (by linarith) (by linarith)).1
    have := isFiniteMeasure_secondDifferenceMeasure σ₂ Λ₂ (s := ε / 2)
      (hin (ε / 2) (by linarith) (by linarith)).2.1
      (hin (-(ε / 2)) (by linarith) (by linarith)).2.1
    -- the second-difference measures have the same moment-generating function on `(-ε/2, ε/2)`
    have hM : secondDifferenceMeasure σ₁ (ε / 2) Λ₁ ν₁
        = secondDifferenceMeasure σ₂ (ε / 2) Λ₂ ν₂ := by
      have hU : Metric.ball (0 : ℝ) (ε / 2) ∈ 𝓝 0 := Metric.ball_mem_nhds 0 (half_pos hε)
      refine measure_eq_of_mgf_id_eventuallyEq
        (mem_interior_iff_mem_nhds.2 (mem_of_superset hU fun u hu ↦ ?_))
        (eventually_of_mem hU fun u hu ↦ ?_)
      all_goals
        rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt] at hu
        obtain ⟨hu₁, hu₂⟩ := hu
      · exact integrable_exp_mul_secondDifferenceMeasure σ₁ Λ₁
          (hin (u + ε / 2) (by linarith) (by linarith)).1
          (hin (u - ε / 2) (by linarith) (by linarith)).1 (hin u (by linarith) (by linarith)).1
      · rw [mgf_id_secondDifferenceMeasure b₁ σ₁ Λ₁ (hin (u + ε / 2) (by linarith) (by linarith)).1
            (hin (u - ε / 2) (by linarith) (by linarith)).1 (hin u (by linarith) (by linarith)).1,
          mgf_id_secondDifferenceMeasure b₂ σ₂ Λ₂ (hin (u + ε / 2) (by linarith) (by linarith)).2.1
            (hin (u - ε / 2) (by linarith) (by linarith)).2.1
            (hin u (by linarith) (by linarith)).2.1,
          (hin (u + ε / 2) (by linarith) (by linarith)).2.2,
          (hin (u - ε / 2) (by linarith) (by linarith)).2.2,
          (hin u (by linarith) (by linarith)).2.2]
    -- their atoms at `0` give `σ²`
    have hσ : σ₁ ^ 2 = σ₂ ^ 2 := by
      have h0 : secondDifferenceMeasure σ₁ (ε / 2) Λ₁ ν₁ {0}
          = secondDifferenceMeasure σ₂ (ε / 2) Λ₂ ν₂ {0} := by rw [hM]
      rw [secondDifferenceMeasure_singleton_zero, secondDifferenceMeasure_singleton_zero,
        ENNReal.ofReal_eq_ofReal_iff (by positivity) (by positivity)] at h0
      exact mul_right_cancel₀ (pow_ne_zero 2 hs) h0
    -- off `0` they are the kernel times the Lévy measures, and dividing by the kernel gives those
    have hLevy : (Λ₁ • ν₁).restrict {0}ᶜ = (Λ₂ • ν₂).restrict {0}ᶜ := by
      rw [restrict_compl_zero_eq_withDensity_inv hs (Λ₁ • ν₁),
        restrict_compl_zero_eq_withDensity_inv hs (Λ₂ • ν₂),
        ← restrict_compl_zero_secondDifferenceMeasure σ₁ (ε / 2) Λ₁ ν₁,
        ← restrict_compl_zero_secondDifferenceMeasure σ₂ (ε / 2) Λ₂ ν₂, hM]
    -- and then `κ` gives the drift
    refine ⟨?_, hσ, hLevy⟩
    have e := (hin (ε / 2) (by linarith) (by linarith)).2.2
    rw [jumpDiffusionExponent_eq_levy b₁ σ₁ Λ₁ (hin (ε / 2) (by linarith) (by linarith)).1,
      jumpDiffusionExponent_eq_levy b₂ σ₂ Λ₂ (hin (ε / 2) (by linarith) (by linarith)).2.1,
      hLevy] at e
    have h2 : (b₁ - b₂) * (ε / 2) = 0 := by linear_combination e - (ε / 2) ^ 2 / 2 * hσ
    exact sub_eq_zero.1 ((mul_eq_zero.1 h2).resolve_right hs)
  · rintro ⟨hb, hσ, hLevy⟩
    refine measure_eq_of_mgf_id_eventuallyEq
      (zero_mem_interior_integrableExpSet_jumpDiffusionIncrementLaw _ _ _ h₁ τ)
      ((hD₁.and hD₂).mono fun u hu ↦ ?_)
    rw [mgf_id_jumpDiffusionIncrementLaw _ _ _ hu.1, mgf_id_jumpDiffusionIncrementLaw _ _ _ hu.2,
      jumpDiffusionExponent_eq_levy _ _ _ hu.1, jumpDiffusionExponent_eq_levy _ _ _ hu.2, hLevy, hb,
      hσ]

end MathFin
