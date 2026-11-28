/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Init
public import Mathlib.MeasureTheory.Function.L2Space

/-! # Multiplication by `f` as an isometry `L²(f²·ν) → L²(ν)`

Multiplying by a fixed measurable `f` carries the weighted space `L²(f²·ν)` isometrically
into `L²(ν)`:

  `∫ |f·ψ|² dν = ∫ |ψ|²·f² dν = ∫ |ψ|² d(f²·ν)`,

so `‖f·ψ‖_{L²(ν)} = ‖ψ‖_{L²(f²·ν)}`. This is the analytic content behind "the Itô integral
against `M = φ●B` is the Itô integral against `B` of `ψφ`": the bracket measure `d⟨M⟩ = φ²ds`
is the weight, and the chain rule is this isometry composed with `itoIntegralCLM`.

Mathlib carries only the `p = 1` case, `withDensitySMulLI`, where the density and the
multiplier coincide; at `p = 2` the multiplier is the *square root* of the density, which is
what makes the norm come out right. The general-`p` statement
`‖f·ψ‖_{L^p(ν)} = ‖ψ‖_{L^p(‖f‖ᵖ·ν)}` is the natural home for this and is an upstreaming
candidate; only `p = 2` is built here, since that is the only exponent the Itô tower uses.

## The well-definedness point

`Lp ℝ 2 (sqWeight ν f)` is a space of classes modulo `(f²·ν)`-null sets, which is **coarser**
than modulo `ν`-null sets: `{f = 0}` is `(f²·ν)`-null but in general not `ν`-null. So two
representatives of one class can disagree on a `ν`-non-null set, and the map `ψ ↦ f·ψ` is
still well defined — on `{f ≠ 0}` the representatives agree, and on `{f = 0}` both products
vanish. Each linearity proof below therefore ends in a case split on `f x = 0`, exactly as
Mathlib's `withDensitySMulLI` does. This is the step at which a naive attempt breaks.

## Main definitions

* `sqWeight`: the measure `f²·ν`, with density `‖f‖ₑ²` against `ν`.
* `mulLM`: multiplication by a measurable `f` as a linear map `L²(f²·ν) →ₗ[ℝ] L²(ν)`.
* `mulLI`: the same map as a linear isometry `L²(f²·ν) →ₗᵢ[ℝ] L²(ν)`; `coeFn_mulLI` gives
  `f·ψ` as its a.e. representative.

## Main results

* `lp_two_norm_sq` — `‖g‖² = ∫ (g a)² ∂ν` for `g : Lp ℝ 2 ν`.
* `lintegral_sqWeight` — the change-of-density identity for lower integrals.
* `eLpNorm_mul_eq` — the norm identity, for a measurable function.
* `integral_sqWeight`, `setIntegral_sqWeight` — the Bochner transfer, and its set form.
* `sqWeight_ae_ne_zero` — `f²·ν` is carried by `{f ≠ 0}`.
* `sqWeight_sqWeight` — **the weight composes**, `(f²·ν) weighted by g² = (fg)²·ν`; read as a
  bracket this is `d⟨ψ●M⟩ = ψ² d⟨M⟩`, and `coeFn_mulLI_mulLI` is its map-level form.
* `ae_of_sqWeight_of_ae_ne_zero` — a.e. statements transfer back when `f ≠ 0` a.e.
* `exists_mulLI_eq` — for `f ≠ 0` a.e. the multiplication isometry is **onto**: `ψ := u/f`.
* `memLp_mul` — `ψ ∈ L²(f²·ν)` implies `f·ψ ∈ L²(ν)`.
* `mulLM`, `mulLI` — the map as a linear map and as a `LinearIsometry`, with `coeFn_mulLM`
  the characterising a.e. identity.

## Tags

weighted L2 space, change of density, Itô integral chain rule, bracket measure,
multiplication isometry, MSC 60H05, MSC 28A25
-/

@[expose] public section

namespace MathFin

open MeasureTheory in
/-- **The real `L²` norm-square as an integral**: `‖g‖² = ∫ (g a)² ∂ν` for `g : Lp ℝ 2 ν`. The one
`L²`-norm bridge of the Brownian and jump towers (Itô isometry, Wiener integral, compensated Poisson
integral), stated once here. -/
lemma lp_two_norm_sq {α : Type*} {mα : MeasurableSpace α} {ν : Measure α} (g : Lp ℝ 2 ν) :
    ‖g‖ ^ 2 = ∫ a, (g a) ^ 2 ∂ν := by
  have h : inner ℝ g g = ‖g‖ ^ 2 := real_inner_self_eq_norm_sq g
  rw [L2.inner_def] at h
  rw [← h]
  refine integral_congr_ae ?_
  filter_upwards with a
  change (g a) * (g a) = (g a) ^ 2
  ring

namespace LpMulIsometry

open MeasureTheory Filter
open scoped ENNReal NNReal

variable {α : Type*} {m : MeasurableSpace α} {ν : Measure α} {f : α → ℝ}

/-- The measure `f²·ν`. For `f` the diffusion coefficient of an Itô integral this is the
bracket measure `d⟨M⟩ = f² ds ⊗ dμ`. -/
noncomputable def sqWeight (ν : Measure α) (f : α → ℝ) : Measure α :=
  ν.withDensity fun x ↦ ‖f x‖ₑ ^ 2

lemma measurable_sqDensity (hf : Measurable f) : Measurable fun x ↦ ‖f x‖ₑ ^ 2 :=
  hf.eNorm.pow_const 2

lemma sqDensity_ne_top (x : α) : ‖f x‖ₑ ^ 2 ≠ ⊤ := by
  simp [eNorm_ne_top]

/-- The density is nonzero exactly where `f` is, which is what turns an a.e. statement for
`sqWeight ν f` into one for `ν` restricted to `{f ≠ 0}`. -/
lemma sqDensity_ne_zero {x : α} (hx : f x ≠ 0) : ‖f x‖ₑ ^ 2 ≠ 0 :=
  pow_ne_zero 2 (by simpa using hx)

/-- **Change of density for lower integrals.** Integrating against `f²·ν` is integrating
against `ν` with the integrand scaled by `‖f‖ₑ²`. -/
lemma lintegral_sqWeight (hf : Measurable f) (g : α → ℝ≥0∞) :
    ∫⁻ x, g x ∂(sqWeight ν f) = ∫⁻ x, ‖f x‖ₑ ^ 2 * g x ∂ν := by
  rw [sqWeight, lintegral_withDensity_eq_lintegral_mul_non_measurable _
    (measurable_sqDensity hf) (Eventually.of_forall fun x ↦ (sqDensity_ne_top x).lt_top)]
  rfl

/-- The weight only sees `f` up to a `ν`-null set. -/
lemma sqWeight_congr_ae {g : α → ℝ} (h : f =ᵐ[ν] g) : sqWeight ν f = sqWeight ν g := by
  rw [sqWeight, sqWeight]
  exact withDensity_congr_ae (by filter_upwards [h] with x hx; rw [hx])

/-- **The weight composes**: weighting by `g` on top of a weighting by `f` is weighting by the
product. Densities multiply, and `‖fg‖ₑ² = ‖f‖ₑ²‖g‖ₑ²`.

This is the associativity of the chain rule. Reading `sqWeight` as a bracket, it says
`d⟨ψ●M⟩ = ψ² d⟨M⟩`: an Itô integral against an Itô integral is again one, with the brackets
composing the way the integrands do. -/
lemma sqWeight_sqWeight (hf : Measurable f) {g : α → ℝ} (hg : Measurable g) :
    sqWeight (sqWeight ν f) g = sqWeight ν (fun x ↦ f x * g x) := by
  have hdens : (fun x ↦ ‖f x * g x‖ₑ ^ 2)
      = (fun x ↦ ‖f x‖ₑ ^ 2) * (fun x ↦ ‖g x‖ₑ ^ 2) := by
    funext x
    simp [eNorm_mul, mul_pow]
  simp only [sqWeight, hdens]
  exact (withDensity_mul ν (measurable_sqDensity hf) (measurable_sqDensity hg)).symm

/-- **The norm identity.** `‖f·g‖_{L²(ν)} = ‖g‖_{L²(f²·ν)}`, for a measurable `g` — no
integrability is needed, both sides being lower integrals. -/
lemma eLpNorm_mul_eq (hf : Measurable f) {g : α → ℝ} (hg : Measurable g) :
    eLpNorm (fun x ↦ f x * g x) 2 ν = eLpNorm g 2 (sqWeight ν f) := by
  have hfg : AEStronglyMeasurable (fun x ↦ f x * g x) ν := (hf.mul hg).aestronglyMeasurable
  rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal (by norm_num) (by norm_num) hfg,
    eLpNorm_eq_lintegral_rpow_eNorm_toReal (by norm_num) (by norm_num) hg.aestronglyMeasurable,
    lintegral_sqWeight hf]
  congr 1
  refine lintegral_congr fun x ↦ ?_
  rw [eNorm_mul, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ (2:ℝ≥0∞).toReal)]
  congr 1
  rw [show ((2 : ℝ≥0∞).toReal) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]

/-- `(‖r‖ₑ²).toReal = r²` — the real form of the density, used to turn a `withDensity`
transfer into an honest multiplication by `f²`. -/
lemma enorm_sq_toReal (r : ℝ) : (‖r‖ₑ ^ 2).toReal = r ^ 2 := by
  rw [ENNReal.toReal_pow, Real.eNorm_eq_ofReal_abs, ENNReal.toReal_ofReal (abs_nonneg r),
    sq_abs]

/-- **Bochner transfer.** Integrating `u` against `f²·ν` is integrating `f²·u` against `ν`. -/
lemma integral_sqWeight (hf : Measurable f) (u : α → ℝ) :
    ∫ x, u x ∂(sqWeight ν f) = ∫ x, f x ^ 2 * u x ∂ν := by
  rw [sqWeight, integral_withDensity_eq_integral_toReal_smul (measurable_sqDensity hf)
    (Eventually.of_forall fun x ↦ (sqDensity_ne_top x).lt_top)]
  exact integral_congr_ae (Eventually.of_forall fun x ↦ by
    simp only [smul_eq_mul, enorm_sq_toReal])

/-- The set-integral form of `integral_sqWeight`. -/
lemma setIntegral_sqWeight (hf : Measurable f) {R : Set α} (hR : MeasurableSet R) (u : α → ℝ) :
    ∫ x in R, u x ∂(sqWeight ν f) = ∫ x in R, f x ^ 2 * u x ∂ν := by
  rw [sqWeight, restrict_withDensity hR,
    integral_withDensity_eq_integral_toReal_smul (measurable_sqDensity hf)
      (Eventually.of_forall fun x ↦ (sqDensity_ne_top x).lt_top)]
  exact integral_congr_ae (Eventually.of_forall fun x ↦ by
    simp only [smul_eq_mul, enorm_sq_toReal])

/-- `f²·ν` is carried by `{f ≠ 0}`: the weight kills the rest. This is what turns "`f²·g = 0`
`ν`-a.e." into "`g = 0` a.e. for the weighted measure". -/
lemma sqWeight_ae_ne_zero (hf : Measurable f) : ∀ᵐ x ∂(sqWeight ν f), f x ≠ 0 := by
  rw [sqWeight, ae_withDensity_iff (measurable_sqDensity hf)]
  filter_upwards with x hx hfx
  exact hx (by simp [hfx])

/-- `ψ ∈ L²(f²·ν)` implies `f·ψ ∈ L²(ν)`. The measurability is not transported across the
measures — an `Lp` element carries a genuinely `StronglyMeasurable` representative
(`Lp.stronglyMeasurable`), so it is measurable for every measure at once. -/
lemma memLp_mul (hf : Measurable f) (ψ : Lp ℝ 2 (sqWeight ν f)) :
    MemLp (fun x ↦ f x * ψ x) 2 ν :=
  (eLpNorm_mul_eq hf (Lp.stronglyMeasurable ψ).measurable).trans_lt (Lp.eLpNorm_lt_top ψ)

/-- When `f ≠ 0` a.e., an a.e. statement for the weighted measure transfers back to `ν`. The
two measures are then equivalent: `f²·ν ≪ ν` always, and the density is a.e. nonzero. -/
lemma ae_of_sqWeight_of_ae_ne_zero (hf : Measurable f) (hf0 : ∀ᵐ x ∂ν, f x ≠ 0)
    {p : α → Prop} (h : ∀ᵐ x ∂(sqWeight ν f), p x) : ∀ᵐ x ∂ν, p x := by
  rw [sqWeight, ae_withDensity_iff (measurable_sqDensity hf)] at h
  filter_upwards [h, hf0] with x hx hx0
  exact hx (sqDensity_ne_zero hx0)

/-- **Multiplication by `f` as a linear map** `L²(f²·ν) →ₗ[ℝ] L²(ν)`. -/
noncomputable def mulLM (ν : Measure α) (hf : Measurable f) :
    Lp ℝ 2 (sqWeight ν f) →ₗ[ℝ] Lp ℝ 2 ν where
  toFun ψ := (memLp_mul hf ψ).toLp _
  map_add' ψ₁ ψ₂ := by
    refine Lp.ext ?_
    filter_upwards [(ae_withDensity_iff (measurable_sqDensity hf)).1 (Lp.coeFn_add ψ₁ ψ₂),
      (memLp_mul hf (ψ₁ + ψ₂)).coeFn_toLp,
      Lp.coeFn_add ((memLp_mul hf ψ₁).toLp _) ((memLp_mul hf ψ₂).toLp _),
      (memLp_mul hf ψ₁).coeFn_toLp, (memLp_mul hf ψ₂).coeFn_toLp] with x hadd h h' h₁ h₂
    rw [h, h', Pi.add_apply, h₁, h₂]
    rcases eq_or_ne (f x) 0 with hx | hx
    · simp [hx]
    · rw [hadd (sqDensity_ne_zero hx), Pi.add_apply, mul_add]
  map_smul' r ψ := by
    refine Lp.ext ?_
    filter_upwards [(ae_withDensity_iff (measurable_sqDensity hf)).1 (Lp.coeFn_smul r ψ),
      (memLp_mul hf (r • ψ)).coeFn_toLp,
      Lp.coeFn_smul r ((memLp_mul hf ψ).toLp _), (memLp_mul hf ψ).coeFn_toLp] with x hs h h' h₁
    rw [RingHom.id_apply, h, h', Pi.smul_apply, h₁]
    rcases eq_or_ne (f x) 0 with hx | hx
    · simp [hx]
    · rw [hs (sqDensity_ne_zero hx), Pi.smul_apply, smul_eq_mul, smul_eq_mul]
      ring

/-- **The characterising a.e. identity** — without it the map is opaque. -/
lemma coeFn_mulLM (ν : Measure α) (hf : Measurable f) (ψ : Lp ℝ 2 (sqWeight ν f)) :
    ⇑(mulLM ν hf ψ) =ᵐ[ν] fun x ↦ f x * ψ x :=
  (memLp_mul hf ψ).coeFn_toLp

/-- **Multiplication by `f`, bundled as an isometry** `L²(f²·ν) →ₗᵢ[ℝ] L²(ν)`. -/
noncomputable def mulLI (ν : Measure α) (hf : Measurable f) :
    Lp ℝ 2 (sqWeight ν f) →ₗᵢ[ℝ] Lp ℝ 2 ν where
  toLinearMap := mulLM ν hf
  norm_map' ψ := by
    rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (coeFn_mulLM ν hf ψ),
      eLpNorm_mul_eq hf (Lp.stronglyMeasurable ψ).measurable]

/-- `coeFn_mulLM` for the bundled isometry. -/
lemma coeFn_mulLI (ν : Measure α) (hf : Measurable f) (ψ : Lp ℝ 2 (sqWeight ν f)) :
    ⇑(mulLI ν hf ψ) =ᵐ[ν] fun x ↦ f x * ψ x :=
  coeFn_mulLM ν hf ψ

/-- **Multiplying twice is multiplying by the product.** The composite
`L²(g²f²·ν) → L²(f²·ν) → L²(ν)` sends `χ` to `f·(g·χ)`.

The inner identity holds only `(f²·ν)`-a.e., which is strictly weaker than `ν`-a.e., so it does
not transfer — but it does not need to: off `{f ≠ 0}` the outer multiplication kills both sides.
Same case split as the well-definedness argument, for the same reason. -/
lemma coeFn_mulLI_mulLI (ν : Measure α) (hf : Measurable f) {g : α → ℝ} (hg : Measurable g)
    (χ : Lp ℝ 2 (sqWeight (sqWeight ν f) g)) :
    ⇑(mulLI ν hf (mulLI (sqWeight ν f) hg χ)) =ᵐ[ν] fun x ↦ f x * (g x * χ x) := by
  -- term mode, not `rw`: the measure is `sqWeight ν f`, which is `ν.withDensity …` only up to
  -- unfolding, and `rw` matches syntactically. Elaboration unifies up to defeq and succeeds.
  have h2 : ∀ᵐ x ∂ν, ‖f x‖ₑ ^ 2 ≠ 0 →
      (mulLI (sqWeight ν f) hg χ : α → ℝ) x = g x * (χ : α → ℝ) x :=
    (ae_withDensity_iff (measurable_sqDensity hf)).1 (coeFn_mulLI (sqWeight ν f) hg χ)
  filter_upwards [coeFn_mulLI ν hf (mulLI (sqWeight ν f) hg χ), h2] with x hx1 hx2
  rw [hx1]
  rcases eq_or_ne (f x) 0 with h0 | h0
  · simp [h0]
  · rw [hx2 (sqDensity_ne_zero h0)]

/-- **Multiplication by `f` is onto when `f ≠ 0` a.e.** The preimage of `u` is `u/f`, which
lands in the weighted space precisely because the weight cancels the division:
`∫|u/f|² f² dν = ∫|u|² dν`. This is what turns a hedge against `B` into a holding in a price
with volatility `f`. -/
theorem exists_mulLI_eq (hf : Measurable f) (hf0 : ∀ᵐ x ∂ν, f x ≠ 0) (u : Lp ℝ 2 ν) :
    ∃ ψ : Lp ℝ 2 (sqWeight ν f), mulLI ν hf ψ = u := by
  have hcancel : (fun x ↦ f x * ((u : α → ℝ) x / f x)) =ᵐ[ν] ⇑u := by
    filter_upwards [hf0] with x hx
    field_simp
  have hquot : MemLp (fun x ↦ (u : α → ℝ) x / f x) 2 (sqWeight ν f) := by
    have hmeas : Measurable fun x ↦ (u : α → ℝ) x / f x :=
      (Lp.stronglyMeasurable u).measurable.div hf
    rw [memLp_iff, ← eLpNorm_mul_eq hf hmeas, eLpNorm_congr_ae hcancel]
    exact Lp.eLpNorm_lt_top u
  refine ⟨hquot.toLp _, Lp.ext ?_⟩
  have hcoe : ∀ᵐ x ∂ν, (hquot.toLp _ : α → ℝ) x = (u : α → ℝ) x / f x :=
    ae_of_sqWeight_of_ae_ne_zero hf hf0 hquot.coeFn_toLp
  filter_upwards [coeFn_mulLI ν hf (hquot.toLp _), hcoe, hf0] with x h1 h2 hx
  rw [h1, h2]
  field_simp

end LpMulIsometry
end MathFin
