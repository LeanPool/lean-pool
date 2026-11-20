/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Analysis.TransverseLocalizedNorm
public import LeanPool.FastDynamo.Global.HorizontalTransportSkewness

/-!
# The weighted energy estimate for the background operator

This module proves `eq:background-coercivity`, the
analytic core of `prop:background-resolvent`, for the
**two-component** horizontal operator `A^bg_{ε,n} = horizontalInductionOperator u ε K` of
`eq:background-operator`, together with its two
immediate consequences: injectivity of the pencil `z - A^bg` and the a-priori bound
`‖h‖ + √ε‖∇_⊥h‖ ≤ C‖(z - A^bg)h‖` (`eq:bg-resolvent`).

Notation local to this module: `w = (u^bg_n)_⊥`, `a = (u^bg_n)_3` and `k_n = 2πK_n` (the paper
writes these expressions out).

Everything is stated for an arbitrary real periodic `W^{1,∞}` velocity `u`, an arbitrary
scalar multiplier `β` and an arbitrary measurable "core" set `S`, with the paper's
coefficient estimates as explicit hypotheses:

* `|β_n| ≤ 1` and a bound on `ε‖∇β_n‖_∞²` — `eq:background-multiplier-bounds`;
* the pointwise phase bound `β_n(Im ζ + τ(s_n - 1)) ≥ (τc_q²/2)1_S - M²/(2τ)` merged with the
  local axial multiplier, i.e. `eq:background-phase-positive` together with the
  second half of `eq:background-local-coefficients`;
* `|β_n w| ≤ C√ε 1_S` and `|∇_⊥ w| ≤ C 1_S` — `eq:background-local-coefficients`.

`Global/TorusBackgroundVelocity.lean` and `Global/TorusBackgroundMultiplier.lean` discharge
those hypotheses for the concrete placed velocity and multiplier.

The weighted test field is used **only** as an a-priori estimate at
`H²`, so no Lax–Milgram, no `H¹` form domain and no periodic elliptic regularity is needed.
As in the paper, the resolvent itself is obtained downstream from injectivity plus Fredholm
index zero (`lem:torus-sector-basic`), here the compact-base Fredholm package
`Operator/HorizontalSectorBasic.pencilFredholmIndexZeroOn_horizontalInductionOperator`.

## Relation to the proof in the paper

The paper splits the pairing as `Re⟨(z - A^bg)h, (1 + iβ_n)h⟩ = I₁ + I₂ + I₃ + I₄`
(`eq:background-testing`).  The Lean proof splits the same pairing into the five terms of
`horizontalInductionPencil_apply_eq`: the diffusion term gives `I₁`; the zeroth-order and axial
multipliers together give `I₂` plus the local axial multiplier of `I₄`; the transport term gives
`I₃` (its unweighted part has zero real part because `Div_⊥ w = 0`); the stretching term is the
rest of `I₄`.  The Lean constants are explicit (`C₀ = C₀' + 2C_w² + 4C_s`, see below).

*Deviation in `I₁` (argument-level).*  The paper bounds the defect of the diffusion term by
`∫ |∇_⊥β_n| |h| |∇_⊥h|`.  The Lean subtracts instead the `L²` Cauchy–Schwarz majorant
`Σ_j ‖(∂_j β)h‖₂ ‖∂_j h‖₂` of the exact defect
(`re_inner_weightedTransverseState_neg_laplacian_ge`, `Analysis/TransverseWeightedDiffusion.lean`)
and absorbs it by Young into `(1/4)‖∇_⊥h‖₂² + Σ_j ‖∂_j β‖_∞² ‖h‖₂²`.  Accordingly the square of the
paper's `√ε‖∇_⊥β_n‖_∞` is the Lean's `ε · gradSupNormSq β = ε Σ_j ‖∂_j β‖_∞²`; the lower bound
`I₁ ≥ (3ε/4)‖∇_⊥h‖₂² - C δ₊ d(K₀)² ‖h‖₂²` has the paper's form.

## Contents

1. support-localised Hölder bounds, phrased through `l2MeasurableSetRestriction`;
2. the localised zeroth-order bound, which merges `re_inner_weightedTransverseState_smul`
   with `re_inner_weightedTransverseState_axialMultiplier`;
3. `eq:background-coercivity` itself;
4. injectivity of `z - A^bg` and `eq:bg-resolvent`.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory
open scoped ENNReal

/-! The support-localised norm `‖1_S h‖₂` of `eq:background-local-coefficients` and
its four Hölder bounds are generic; they live in `Analysis/TransverseLocalizedNorm.lean`. -/

/-! ## The localised zeroth-order bound

This merges `re_inner_weightedTransverseState_smul` (which produces
`Re ζ + ε k_n² + β_n(Im ζ - τ)`) with `re_inner_weightedTransverseState_axialMultiplier`
(which produces `+ β_n k_n a`, i.e. `+ β_n τ s_n` plus the local axial multiplier, since
`k_n (u^ax)_3 = τ s_n`) into the integrand `[Re ζ + ε k_n² + β_n(Im ζ + τ(s_n - 1))]` of `I₂`
in `eq:background-testing` together with the local axial multiplier of `I₄`, and then
integrates the pointwise phase inequality `eq:background-phase-positive` against `|h|²`. -/

section Zeroth

variable {ι : Type*} [Fintype ι]

/-- The real part of an `L²` pairing is the integral of the pointwise real parts. -/
private theorem re_inner_eq_integral' (f g : TransverseVecL2 ι) :
    (inner ℂ f g : ℂ).re =
      ∫ x, (inner ℂ (f x) (g x) : ℂ).re ∂transverseMeasure := by
  rw [MeasureTheory.L2.inner_def]
  have h := integral_re (L2.integrable_inner (𝕜 := ℂ) f g)
  simp only [RCLike.re_to_complex] at h
  exact h.symm

/-- Pointwise form of the pairing of two scalar multiples of the same field. -/
private theorem re_inner_smul_smul_point (c d : ℂ) (v : EuclideanSpace ℂ ι) :
    (inner ℂ (c • v) (d • v) : ℂ).re = ((starRingEnd ℂ) c * d).re * ‖v‖ ^ 2 := by
  have h : (inner ℂ v v : ℂ) = ((‖v‖ : ℝ) : ℂ) ^ 2 := inner_self_eq_norm_sq_to_K v
  rw [inner_smul_left, inner_smul_right, h, ← Complex.ofReal_pow, ← mul_assoc,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- **The paired multiplier as an integral**: `Re ⟨a f, b f⟩ = ∫ Re(conj a · b) |f|²`. -/
theorem re_inner_scalarVectorMulTransverseVec_pair_eq_integral
    (a b : TransverseScalarLInf) (f : TransverseVecL2 ι) :
    (inner ℂ (scalarVectorMulTransverseVec ι a f)
        (scalarVectorMulTransverseVec ι b f)).re =
      ∫ x, ((starRingEnd ℂ) (a x) * b x).re * ‖f x‖ ^ 2 ∂transverseMeasure := by
  rw [re_inner_eq_integral']
  refine integral_congr_ae ?_
  filter_upwards [scalarVectorMulTransverseVec_coe_ae a f,
    scalarVectorMulTransverseVec_coe_ae b f] with x ha hb
  rw [ha, hb]
  exact re_inner_smul_smul_point (a x) (b x) _

/-- The integrand of the paired multiplier is integrable. -/
theorem integrable_re_scalarVectorMulTransverseVec_pair
    (a b : TransverseScalarLInf) (f : TransverseVecL2 ι) :
    Integrable (fun x ↦ ((starRingEnd ℂ) (a x) * b x).re * ‖f x‖ ^ 2)
      transverseMeasure := by
  refine ((L2.integrable_inner (𝕜 := ℂ) (scalarVectorMulTransverseVec ι a f)
    (scalarVectorMulTransverseVec ι b f)).re).congr ?_
  filter_upwards [scalarVectorMulTransverseVec_coe_ae a f,
    scalarVectorMulTransverseVec_coe_ae b f] with x ha hb
  rw [ha, hb]
  exact re_inner_smul_smul_point (a x) (b x) _

/--
**The localised zeroth-order estimate**, `eq:background-phase-positive`
integrated against `|h|²`.  For a real `L∞` axial
coefficient `a`, a real shift `t = Im z` and a real wavenumber `k = k_n`, the pointwise bound
`c₁ 1_S - c₂ ≤ β (t + k a)` gives

`c₁ ∫_S |f|² - c₂ ‖f‖₂² ≤ t Re ⟨βf, f⟩ + k Re ⟨βf, af⟩`.
-/
theorem re_zerothOrder_localized_ge
    (β : TransverseScalarW1Inf) {a : TransverseScalarLInf}
    (ha : IsRealTransverseScalarLInf a) (t k : ℝ)
    {S : Set TransverseTorus} (hS : MeasurableSet S) {c₁ c₂ : ℝ}
    (hphase : ∀ᵐ x ∂transverseMeasure,
      S.indicator (fun _ ↦ c₁) x - c₂ ≤ (β.value x).re * (t + k * (a x).re))
    (f : TransverseVecL2 ι) :
    c₁ * transverseLocalizedNorm S hS f ^ 2 - c₂ * ‖f‖ ^ 2 ≤
      t * (inner ℂ (scalarVectorMulTransverseVec ι β.value f) f).re +
        k * (inner ℂ (scalarVectorMulTransverseVec ι β.value f)
              (scalarVectorMulTransverseVec ι a f)).re := by
  have hsq := integrable_sq_norm_transverseVecL2 f
  have hg1 := integrable_re_scalarVectorMulTransverseVec β.value f
  have hg2 := integrable_re_scalarVectorMulTransverseVec_pair β.value a f
  have hgint : Integrable
      (fun x ↦ S.indicator (fun y ↦ c₁ * ‖f y‖ ^ 2) x - c₂ * ‖f x‖ ^ 2)
      transverseMeasure :=
    ((hsq.const_mul c₁).indicator hS).sub (hsq.const_mul c₂)
  have hpoint : ∀ᵐ x ∂transverseMeasure,
      S.indicator (fun y ↦ c₁ * ‖f y‖ ^ 2) x - c₂ * ‖f x‖ ^ 2 ≤
        t * ((β.value x).re * ‖f x‖ ^ 2) +
          k * (((starRingEnd ℂ) (β.value x) * a x).re * ‖f x‖ ^ 2) := by
    filter_upwards [hphase, ha] with x hx hax
    have haim : (a x).im = 0 := by
      have := congrArg Complex.im hax
      simp only [Complex.conj_im] at this
      linarith
    have hpair : ((starRingEnd ℂ) (β.value x) * a x).re =
        (β.value x).re * (a x).re := by
      simp [Complex.mul_re, haim]
    have hsplit : S.indicator (fun y ↦ c₁ * ‖f y‖ ^ 2) x =
        S.indicator (fun _ ↦ c₁) x * ‖f x‖ ^ 2 := by
      by_cases hxS : x ∈ S
      · rw [Set.indicator_of_mem hxS, Set.indicator_of_mem hxS]
      · rw [Set.indicator_of_notMem hxS, Set.indicator_of_notMem hxS, zero_mul]
    rw [hsplit, hpair, ← sub_mul]
    have hweighted := mul_le_mul_of_nonneg_right hx (sq_nonneg ‖f x‖)
    nlinarith only [hweighted]
  have hmain := integral_mono_ae hgint ((hg1.const_mul t).add (hg2.const_mul k)) hpoint
  simp only [Pi.add_apply] at hmain
  rw [integral_sub ((hsq.const_mul c₁).indicator hS) (hsq.const_mul c₂),
    integral_indicator hS, integral_const_mul, integral_const_mul,
    ← sq_norm_transverseVecL2_eq_integral,
    integral_add (hg1.const_mul t) (hg2.const_mul k),
    integral_const_mul, integral_const_mul,
    ← re_inner_scalarVectorMulTransverseVec_self_eq_integral,
    ← re_inner_scalarVectorMulTransverseVec_pair_eq_integral] at hmain
  rw [transverseLocalizedNorm_sq]
  exact hmain

end Zeroth

/-! ## `eq:background-coercivity` -/

section Coercivity

variable {ι : Type*} [Fintype ι]

/-- The localised norm of the weighted test field is at most twice that of the field. -/
theorem transverseLocalizedNorm_weightedTransverseState_le
    {S : Set TransverseTorus} (hS : MeasurableSet S)
    (β : TransverseScalarW1Inf) (hβ : ‖β.value‖ ≤ 1) (h : TransverseVecH2 ι) :
    transverseLocalizedNorm S hS (weightedTransverseState β h) ≤
      2 * transverseLocalizedNorm S hS (transverseH2Embedding h) := by
  have hcomm := l2MeasurableSetRestriction_scalarVectorMulTransverseVec (ι := ι)
    S hS β.value (transverseH2Embedding h)
  have key : ‖l2MeasurableSetRestriction (E := EuclideanSpace ℂ ι) transverseMeasure S hS
      (weightedTransverseState β h)‖ ≤
      2 * ‖l2MeasurableSetRestriction (E := EuclideanSpace ℂ ι) transverseMeasure S hS
        (transverseH2Embedding h)‖ := by
    rw [weightedTransverseState, map_add, map_smul, hcomm]
    refine le_trans (norm_add_le _ _) ?_
    have h1 : ‖Complex.I • scalarVectorMulTransverseVec ι β.value
        (l2MeasurableSetRestriction (E := EuclideanSpace ℂ ι) transverseMeasure S hS
          (transverseH2Embedding h))‖ ≤
        ‖l2MeasurableSetRestriction (E := EuclideanSpace ℂ ι) transverseMeasure S hS
          (transverseH2Embedding h)‖ := by
      rw [norm_smul, Complex.norm_I, one_mul]
      refine le_trans (norm_scalarVectorMulTransverseVec_apply_le _ _) ?_
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hβ (norm_nonneg
          (l2MeasurableSetRestriction (E := EuclideanSpace ℂ ι) transverseMeasure S hS
            (transverseH2Embedding h)))
    linarith only [h1]
  exact key

/-- A vector coefficient dominated by `C 1_S` produces an output supported in `S`. -/
theorem vectorScalarMulTransverseVec_ae_zero_off
    {S : Set TransverseTorus} {A : TransverseVecLInf ι} {C : ℝ}
    (hA : ∀ᵐ x ∂transverseMeasure, ‖A x‖ ≤ S.indicator (fun _ ↦ C) x)
    (g : TransverseScalarL2) :
    ∀ᵐ x ∂transverseMeasure, x ∉ S →
      (vectorScalarMulTransverseVec ι A g :
        TransverseTorus → EuclideanSpace ℂ ι) x = 0 := by
  have hcoe : (vectorScalarMulTransverseVec ι A g :
      TransverseTorus → EuclideanSpace ℂ ι) =ᵐ[transverseMeasure]
      fun x ↦ (g : TransverseTorus → ℂ) x •
        (A : TransverseTorus → EuclideanSpace ℂ ι) x :=
    vectorScalarMulL2_coe_ae transverseMeasure A g
  filter_upwards [hA, hcoe] with x hx hcx hxS
  rw [hcx, Set.indicator_of_notMem hxS] at *
  have h0 : A x = 0 := norm_le_zero_iff.mp hx
  rw [h0, smul_zero]

end Coercivity

/-- The transverse transport term of `A_{ε,K}` in the shape consumed by the weighted
splitting lemma of `Analysis/TransverseWeightedLeibniz.lean`. -/
theorem horizontalInductionTransport_eq_transverseCoefficientTransport
    (u : TransverseRealW1Inf) (h : TransverseC2H2) :
    horizontalInductionTransport u h =
      transverseCoefficientTransport
        (fun j ↦ transverseW1InfComplexValueCoordLInf j.castSucc u) h := by
  rw [horizontalInductionTransport_apply]
  rfl

/--
The pencil `z - A^bg_{ε,n}` written as the five terms of `𝔞_z` (the form the paper pairs
with `(1 + iβ_n)h` in `eq:background-testing`): the zeroth-order multiplier `z + ε k_n²`, the
diffusion `ε(-Δ_⊥)`, the transport `w·∇_⊥`, the axial multiplier `+ i k_n a` and the
stretching `-(h·∇_⊥)w`.
-/
theorem horizontalInductionPencil_apply_eq
    (u : TransverseRealW1Inf) (ε : ℝ) (K : ℤ) (z : ℂ) (h : TransverseC2H2) :
    (horizontalInductionOperator u ε K).pencil z h =
      ((z + ((ε * (2 * Real.pi * (K : ℝ)) ^ 2 : ℝ) : ℂ)) • transverseH2Embedding h +
          (ε : ℂ) • (-transverseVecLaplacianFromH2 (Fin 2) h) +
          horizontalInductionTransport u h +
          (((2 * Real.pi * (K : ℝ) : ℝ) : ℂ) * Complex.I) •
            scalarVectorMulTransverseVec (Fin 2)
              (transverseW1InfComplexValueCoordLInf 2 u)
              (transverseH2Embedding h)) -
        horizontalInductionStretching u h := by
  have hop : (horizontalInductionOperator u ε K).pencil z h =
      z • transverseH2Embedding h - horizontalInductionAction u ε K h := rfl
  have hax : axialMultiplier K = (((2 * Real.pi * (K : ℝ) : ℝ)) : ℂ) * Complex.I := by
    rw [axialMultiplier]
    push_cast
    ring
  have hc : ((ε * (2 * Real.pi * (K : ℝ)) ^ 2 : ℝ) : ℂ) =
      (ε : ℂ) * (2 * Real.pi * K : ℂ) ^ 2 := by
    push_cast
    ring
  rw [hop, horizontalInductionAction]
  simp only [add_apply, sub_apply, smul_apply, horizontalInductionDiffusion_apply,
    horizontalInductionAxialTransport_apply]
  rw [hax, hc]
  have e1 : (ε : ℂ) • (transverseVecLaplacianFromH2 (Fin 2) h -
      (2 * Real.pi * K : ℂ) ^ 2 • transverseH2Embedding h) =
      -((ε : ℂ) • (-transverseVecLaplacianFromH2 (Fin 2) h)) -
        ((ε : ℂ) * (2 * Real.pi * K : ℂ) ^ 2) • transverseH2Embedding h := by
    rw [smul_sub, smul_smul, smul_neg, neg_neg]
  have e2 : (z + (ε : ℂ) * (2 * Real.pi * K : ℂ) ^ 2) • transverseH2Embedding h =
      z • transverseH2Embedding h +
        ((ε : ℂ) * (2 * Real.pi * K : ℂ) ^ 2) • transverseH2Embedding h :=
    add_smul _ _ _
  rw [e1, e2]
  abel

/-- Pure scalar form of the Young absorption of the transport term
(the estimate of `I₃` in the proof of `prop:background-resolvent`): with `q = √ε`, `C = C_w`,
`m = ‖1_S h‖₂` and `x, y` the two derivative norms, `C q m (x + y) ≤ (ε/4)(x² + y²) + 2C²m²`. -/
private theorem young_transport_absorption {ε q x y m C : ℝ} (hq : q ^ 2 = ε) :
    C * q * m * x + C * q * m * y ≤
      ε / 4 * (x ^ 2 + y ^ 2) + 2 * C ^ 2 * m ^ 2 := by
  subst hq
  nlinarith [sq_nonneg (q * x / 2 - C * m), sq_nonneg (q * y / 2 - C * m)]

/-- Pure scalar form of the stretching absorption
(the stretching part of `I₄` in the proof of `prop:background-resolvent`): a pairing bounded
by `M b` with `M ≤ 2m` and `b ≤ C m` is bounded by `2C m²`. -/
private theorem stretching_absorption {a b m M C : ℝ} (h1 : a ≤ M * b)
    (h2 : b ≤ C * m) (h3 : M ≤ 2 * m) (hb : 0 ≤ b) (hm : 0 ≤ m) :
    a ≤ 2 * C * m ^ 2 := by
  calc a ≤ M * b := h1
    _ ≤ 2 * m * (C * m) := mul_le_mul h3 h2 hb (by linarith)
    _ = 2 * C * m ^ 2 := by ring

/--
**`eq:background-coercivity`** on two components.

For a real periodic `W^{1,∞}` velocity `u` with vanishing transverse weak divergence, a scalar
multiplier `β` with `|β| ≤ 1`, and a measurable set `S` (the union `𝒞_n` of the nonselected
cores) carrying the three coefficient estimates

* `hphase`  — `eq:background-phase-positive` merged with the local axial multiplier
  bound of `eq:background-local-coefficients`: the bracket
  `β_n(Im z + k_n a)` is at least `c₁ 1_S - c₂` pointwise,
* `hw`      — `|w_j| |β_n| ≤ C_w √ε 1_S` (first line of `eq:background-local-coefficients`),
* `hgrad`   — `|(∂_j u)_⊥| ≤ C_s 1_S` (second line of `eq:background-local-coefficients`),

the weighted test field `(1 + iβ)h` satisfies

`Re 𝔞_z(h,(1+iβ)h) ≥ (ε/2)‖∇_⊥h‖² + (Re z + εk_n² - c₂ - ε‖∇β‖_∞²)‖h‖²`
`  + (c₁ - 2C_w² - 4C_s)∫_S|h|²`.

Compared with the paper, `c₁ = τ c_q²/2 - C₀'`, `c₂ = M²/(2τ)`,
`C₀ = 2C_w² + 4C_s + C₀'` and `C₁ δ₊ d(K₀)² = ε‖∇β‖_∞²`; all of `C_w`, `C_s` and `C₀` are
`τ`-free because `s_n` is, so the order "`τ` first, then `K₀`" is non-circular.
-/
theorem re_inner_weightedTransverseState_horizontalInductionPencil_ge
    (β : TransverseScalarW1Inf) (hβ : ‖β.value‖ ≤ 1)
    (u : TransverseRealW1Inf) (hu : IsTransverseDivergenceFree u)
    {ε : ℝ} (hε : 0 < ε) (K : ℤ) (z : ℂ)
    {S : Set TransverseTorus} (hS : MeasurableSet S)
    {c₁ c₂ Cw Cs : ℝ} (hCw : 0 ≤ Cw) (hCs : 0 ≤ Cs)
    (hphase : ∀ᵐ x ∂transverseMeasure,
      S.indicator (fun _ ↦ c₁) x - c₂ ≤
        (β.value x).re *
          (z.im + 2 * Real.pi * (K : ℝ) *
            ((transverseW1InfComplexValueCoordLInf 2 u) x).re))
    (hw : ∀ j : Fin 2, ∀ᵐ x ∂transverseMeasure,
      ‖(transverseW1InfComplexValueCoordLInf j.castSucc u) x‖ * ‖β.value x‖ ≤
        S.indicator (fun _ ↦ Cw * Real.sqrt ε) x)
    (hgrad : ∀ j : Fin 2, ∀ᵐ x ∂transverseMeasure,
      ‖(transverseW1InfHorizontalDerivLInf j u) x‖ ≤ S.indicator (fun _ ↦ Cs) x)
    (h : TransverseC2H2) :
    ε / 2 * transverseGradientEnergy h +
          (z.re + ε * (2 * Real.pi * (K : ℝ)) ^ 2 - c₂ - ε * β.gradSupNormSq) *
            ‖transverseH2Embedding h‖ ^ 2 +
          (c₁ - 2 * Cw ^ 2 - 4 * Cs) *
            transverseLocalizedNorm S hS (transverseH2Embedding h) ^ 2 ≤
      (inner ℂ (weightedTransverseState β h)
        ((horizontalInductionOperator u ε K).pencil z h)).re := by
  have hureal := transverseW1InfComplexValueCoordLInf_isReal u 2
  -- the zeroth-order bracket
  have hT0 := re_inner_weightedTransverseState_smul β h
    (z + ((ε * (2 * Real.pi * (K : ℝ)) ^ 2 : ℝ) : ℂ))
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    add_zero] at hT0
  have hT3 := re_inner_weightedTransverseState_axialMultiplier β hureal
    (2 * Real.pi * (K : ℝ)) h
  have hzero := re_zerothOrder_localized_ge β hureal z.im (2 * Real.pi * (K : ℝ))
    hS hphase (transverseH2Embedding h)
  -- the diffusion term
  have hlap := re_inner_weightedTransverseState_neg_laplacian_ge_young β h
  have hT1 : (inner ℂ (weightedTransverseState β h)
      ((ε : ℂ) • (-transverseVecLaplacianFromH2 (Fin 2) h))).re =
      ε * (inner ℂ (weightedTransverseState β h)
        (-transverseVecLaplacianFromH2 (Fin 2) h)).re := by
    rw [inner_smul_right]
    simp [Complex.mul_re]
  have hT1' : ε * (3 / 4 * transverseGradientEnergy h -
      β.gradSupNormSq * ‖transverseH2Embedding h‖ ^ 2) ≤
      ε * (inner ℂ (weightedTransverseState β h)
        (-transverseVecLaplacianFromH2 (Fin 2) h)).re :=
    mul_le_mul_of_nonneg_left hlap hε.le
  -- the transport term
  have htr0 : (inner ℂ (transverseH2Embedding h)
      (transverseCoefficientTransport
        (fun j ↦ transverseW1InfComplexValueCoordLInf j.castSucc u) h)).re = 0 := by
    rw [← horizontalInductionTransport_eq_transverseCoefficientTransport]
    exact re_inner_horizontalInductionTransport_eq_zero u hu h
  have hsplit := re_inner_weightedTransverseState_transport_eq β
    (fun j ↦ transverseW1InfComplexValueCoordLInf j.castSucc u) h
  rw [htr0, zero_add] at hsplit
  have htrb := abs_re_inner_weightedPart_transport_le β
    (fun j ↦ transverseW1InfComplexValueCoordLInf_isReal u j.castSucc) h
  rw [Fin.sum_univ_two] at htrb
  have hwb : ∀ j : Fin 2,
      ‖scalarVectorMulTransverseVec (Fin 2)
        (transverseW1InfComplexValueCoordLInf j.castSucc u)
        (scalarVectorMulTransverseVec (Fin 2) β.value (transverseH2Embedding h))‖ ≤
        Cw * Real.sqrt ε *
          transverseLocalizedNorm S hS (transverseH2Embedding h) :=
    fun j ↦ norm_scalarVectorMulTransverseVec_comp_le_of_ae_indicator hS
      (mul_nonneg hCw (Real.sqrt_nonneg ε)) (hw j) (transverseH2Embedding h)
  -- the stretching term
  have hst : ∀ j : Fin 2,
      |(inner ℂ (weightedTransverseState β h)
        (vectorScalarMulTransverseC2 (transverseW1InfHorizontalDerivLInf j u)
          (transverseCoordL2 j (transverseH2Embedding h)))).re| ≤
        2 * Cs * transverseLocalizedNorm S hS (transverseH2Embedding h) ^ 2 := by
    intro j
    have hzero' := vectorScalarMulTransverseVec_ae_zero_off (hgrad j)
      (transverseCoordL2 j (transverseH2Embedding h))
    have h1 := abs_re_inner_le_localized hS (weightedTransverseState β h) hzero'
    have h2 := norm_vectorScalarMulTransverseVec_coord_le_of_ae_indicator hS hCs
      (hgrad j) j (transverseH2Embedding h)
    have h3 := transverseLocalizedNorm_weightedTransverseState_le hS β hβ h
    have h4 := transverseLocalizedNorm_nonneg S hS (transverseH2Embedding h)
    have h6 := norm_nonneg (vectorScalarMulTransverseVec (Fin 2)
      (transverseW1InfHorizontalDerivLInf j u)
      (transverseCoordL2 j (transverseH2Embedding h)))
    exact stretching_absorption h1 h2 h3 h6 h4
  -- Young absorption of the transport term
  have hE : transverseGradientEnergy h =
      ‖transverseVecDerivFromH2 (Fin 2) 0 h‖ ^ 2 +
        ‖transverseVecDerivFromH2 (Fin 2) 1 h‖ ^ 2 := by
    rw [transverseGradientEnergy, Fin.sum_univ_two]
  have hyoung : Cw * Real.sqrt ε *
        transverseLocalizedNorm S hS (transverseH2Embedding h) *
          ‖transverseVecDerivFromH2 (Fin 2) 0 h‖ +
      Cw * Real.sqrt ε *
        transverseLocalizedNorm S hS (transverseH2Embedding h) *
          ‖transverseVecDerivFromH2 (Fin 2) 1 h‖ ≤
      ε / 4 * transverseGradientEnergy h +
        2 * Cw ^ 2 *
          transverseLocalizedNorm S hS (transverseH2Embedding h) ^ 2 := by
    rw [hE]
    exact young_transport_absorption (Real.sq_sqrt hε.le)
  have htrans : -(ε / 4 * transverseGradientEnergy h +
      2 * Cw ^ 2 * transverseLocalizedNorm S hS (transverseH2Embedding h) ^ 2) ≤
      (inner ℂ (weightedTransverseState β h)
        (transverseCoefficientTransport
          (fun j ↦ transverseW1InfComplexValueCoordLInf j.castSucc u) h)).re := by
    rw [hsplit]
    have hmono : ‖transverseVecDerivFromH2 (Fin 2) 0 h‖ ≥ 0 := norm_nonneg _
    have hmono' : ‖transverseVecDerivFromH2 (Fin 2) 1 h‖ ≥ 0 := norm_nonneg _
    have hb0 := mul_le_mul_of_nonneg_right (hwb 0) hmono
    have hb1 := mul_le_mul_of_nonneg_right (hwb 1) hmono'
    have habs := neg_abs_le
      ((inner ℂ (Complex.I • scalarVectorMulTransverseVec (Fin 2) β.value
        (transverseH2Embedding h))
        (transverseCoefficientTransport
          (fun j ↦ transverseW1InfComplexValueCoordLInf j.castSucc u) h)).re)
    linarith only [htrb, hyoung, hb0, hb1, habs]
  -- assembly
  rw [horizontalInductionPencil_apply_eq,
    horizontalInductionTransport_eq_transverseCoefficientTransport,
    horizontalInductionStretching_apply, Fin.sum_univ_two]
  simp only [inner_sub_right, inner_add_right, Complex.sub_re, Complex.add_re]
  have hst0 := neg_abs_le ((inner ℂ (weightedTransverseState β h)
    (vectorScalarMulTransverseC2 (transverseW1InfHorizontalDerivLInf 0 u)
      (transverseCoordL2 0 (transverseH2Embedding h)))).re)
  have hst1 := neg_abs_le ((inner ℂ (weightedTransverseState β h)
    (vectorScalarMulTransverseC2 (transverseW1InfHorizontalDerivLInf 1 u)
      (transverseCoordL2 1 (transverseH2Embedding h)))).re)
  have hstb0 := le_abs_self ((inner ℂ (weightedTransverseState β h)
    (vectorScalarMulTransverseC2 (transverseW1InfHorizontalDerivLInf 0 u)
      (transverseCoordL2 0 (transverseH2Embedding h)))).re)
  have hstb1 := le_abs_self ((inner ℂ (weightedTransverseState β h)
    (vectorScalarMulTransverseC2 (transverseW1InfHorizontalDerivLInf 1 u)
      (transverseCoordL2 1 (transverseH2Embedding h)))).re)
  linarith only [hT0, hT3, hzero, hT1, hT1', htrans, hst 0, hst 1, hst0, hst1,
    hstb0, hstb1]

/-! ## Injectivity and the a-priori bound `eq:bg-resolvent` -/

/--
The hypotheses of `eq:background-coercivity` at one
spectral parameter, bundled.  `growth` is the paper's `g_* - M²/(2τ) - C₁δ₊d(K₀)²`
after the choices `eq:axial-separation-choice` and `eq:background-diffusion-small`;
`core_nonneg` is `τ c_q²/2 ≥ C₀`, implied by the second half `τ c_q²/2 ≥ C₀ + 1` of
`eq:axial-separation-choice`.

`Global/GlobalParameterChoice.lean` assembles the parameter chain `q → τ → K₀` that produces
such a datum uniformly in `n`, `δ ∈ I` and `z ∈ 𝒢_τ`; this module only has to exhibit the
fields.
-/
structure BackgroundCoercivity (β : TransverseScalarW1Inf) (u : TransverseRealW1Inf)
    (ε : ℝ) (K : ℤ) (z : ℂ) (S : Set TransverseTorus) where
  /-- The union of the nonselected cores is measurable. -/
  measurable : MeasurableSet S
  /-- The diffusivity is positive. -/
  eps_pos : 0 < ε
  /-- `|β_n| ≤ 1` (`eq:background-multiplier-bounds`). -/
  norm_value_le_one : ‖β.value‖ ≤ 1
  /-- `Div_⊥ u^bg = 0` (used before `eq:background-testing`). -/
  divergenceFree : IsTransverseDivergenceFree u
  /-- `τ c_q²/2 - C₀'`, the localised gain of `eq:background-phase-positive`. -/
  phaseFloor : ℝ
  /-- `M²/(2τ)`, the global loss of `eq:background-phase-positive`. -/
  phaseDefect : ℝ
  /-- `C_w` of `|β_n w| ≤ C_w √ε 1_S` (`eq:background-local-coefficients`). -/
  transportConstant : ℝ
  /-- `C_s` of `|∇_⊥ w| ≤ C_s 1_S` (`eq:background-local-coefficients`). -/
  stretchingConstant : ℝ
  /-- The transport constant is nonnegative. -/
  transportConstant_nonneg : 0 ≤ transportConstant
  /-- The stretching constant is nonnegative. -/
  stretchingConstant_nonneg : 0 ≤ stretchingConstant
  /-- The pointwise phase bound, `eq:background-phase-positive` merged with the
  local axial multiplier of `eq:background-local-coefficients`. -/
  phase : ∀ᵐ x ∂transverseMeasure,
    S.indicator (fun _ ↦ phaseFloor) x - phaseDefect ≤
      (β.value x).re *
        (z.im + 2 * Real.pi * (K : ℝ) *
          ((transverseW1InfComplexValueCoordLInf 2 u) x).re)
  /-- The transport coefficient bound of `eq:background-local-coefficients`. -/
  transport : ∀ j : Fin 2, ∀ᵐ x ∂transverseMeasure,
    ‖(transverseW1InfComplexValueCoordLInf j.castSucc u) x‖ * ‖β.value x‖ ≤
      S.indicator (fun _ ↦ transportConstant * Real.sqrt ε) x
  /-- The stretching coefficient bound of `eq:background-local-coefficients`. -/
  stretching : ∀ j : Fin 2, ∀ᵐ x ∂transverseMeasure,
    ‖(transverseW1InfHorizontalDerivLInf j u) x‖ ≤
      S.indicator (fun _ ↦ stretchingConstant) x
  /-- `τ c_q²/2 ≥ C₀`, implied by the second half of `eq:axial-separation-choice`. -/
  core_nonneg :
    0 ≤ phaseFloor - 2 * transportConstant ^ 2 - 4 * stretchingConstant
  /-- The retained growth rate `g_* - M²/(2τ) - C₁δ₊d(K₀)²`. -/
  growth : ℝ
  /-- The retained growth rate is positive (`eq:axial-separation-choice`,
  `eq:background-diffusion-small`). -/
  growth_pos : 0 < growth
  /-- The retained growth rate is dominated by the coercivity coefficient. -/
  growth_le :
    growth ≤ z.re + ε * (2 * Real.pi * (K : ℝ)) ^ 2 - phaseDefect -
      ε * β.gradSupNormSq

namespace BackgroundCoercivity

variable {β : TransverseScalarW1Inf} {u : TransverseRealW1Inf} {ε : ℝ} {K : ℤ}
  {z : ℂ} {S : Set TransverseTorus}

/-- `eq:background-coercivity` with the localised term discarded:
`Re 𝔞_z(h,(1+iβ)h) ≥ (ε/2)‖∇_⊥h‖² + g‖h‖²`. -/
theorem re_inner_pencil_ge (D : BackgroundCoercivity β u ε K z S)
    (h : TransverseC2H2) :
    ε / 2 * transverseGradientEnergy h +
        D.growth * ‖transverseH2Embedding h‖ ^ 2 ≤
      (inner ℂ (weightedTransverseState β h)
        ((horizontalInductionOperator u ε K).pencil z h)).re := by
  have hmain := re_inner_weightedTransverseState_horizontalInductionPencil_ge β
    D.norm_value_le_one u D.divergenceFree D.eps_pos K z D.measurable
    D.transportConstant_nonneg D.stretchingConstant_nonneg D.phase D.transport
    D.stretching h
  have h1 : D.growth * ‖transverseH2Embedding h‖ ^ 2 ≤
      (z.re + ε * (2 * Real.pi * (K : ℝ)) ^ 2 - D.phaseDefect -
        ε * β.gradSupNormSq) * ‖transverseH2Embedding h‖ ^ 2 :=
    mul_le_mul_of_nonneg_right D.growth_le (sq_nonneg _)
  have h2 : 0 ≤ (D.phaseFloor - 2 * D.transportConstant ^ 2 -
      4 * D.stretchingConstant) *
      transverseLocalizedNorm S D.measurable (transverseH2Embedding h) ^ 2 :=
    mul_nonneg D.core_nonneg (sq_nonneg _)
  linarith

/-- The weighted test field costs at most `√2‖h‖₂` (the `√2` bound at the end of the proof
of `prop:background-resolvent`). -/
theorem re_inner_pencil_le (D : BackgroundCoercivity β u ε K z S)
    (h : TransverseC2H2) :
    (inner ℂ (weightedTransverseState β h)
        ((horizontalInductionOperator u ε K).pencil z h)).re ≤
      Real.sqrt 2 * ‖transverseH2Embedding h‖ *
        ‖(horizontalInductionOperator u ε K).pencil z h‖ :=
  le_trans (le_abs_self _)
    (abs_re_inner_weightedTransverseState_le β D.norm_value_le_one h _)

/-- **The `L²` half of `eq:bg-resolvent`**:
`g‖h‖₂ ≤ √2‖(z - A^bg)h‖₂`. -/
theorem growth_mul_norm_le (D : BackgroundCoercivity β u ε K z S)
    (h : TransverseC2H2) :
    D.growth * ‖transverseH2Embedding h‖ ≤
      Real.sqrt 2 * ‖(horizontalInductionOperator u ε K).pencil z h‖ := by
  have hge := D.re_inner_pencil_ge h
  have hle := D.re_inner_pencil_le h
  have hE := mul_nonneg (div_nonneg D.eps_pos.le (by norm_num : 0 ≤ (2 : ℝ)))
    (transverseGradientEnergy_nonneg h)
  have hkey : D.growth * ‖transverseH2Embedding h‖ ^ 2 ≤
      Real.sqrt 2 * ‖transverseH2Embedding h‖ *
        ‖(horizontalInductionOperator u ε K).pencil z h‖ := by
    linarith only [hge, hle, hE]
  rcases eq_or_lt_of_le (norm_nonneg (transverseH2Embedding h)) with hN | hN
  · rw [← hN, mul_zero]
    positivity
  · rw [pow_two, ← mul_assoc, mul_right_comm (Real.sqrt 2)] at hkey
    exact le_of_mul_le_mul_right hkey hN

/-- **The gradient half of `eq:bg-resolvent`**: `g ε‖∇_⊥h‖₂² ≤ 4‖(z - A^bg)h‖₂²`. -/
theorem growth_mul_eps_gradientEnergy_le (D : BackgroundCoercivity β u ε K z S)
    (h : TransverseC2H2) :
    D.growth * (ε * transverseGradientEnergy h) ≤
      4 * ‖(horizontalInductionOperator u ε K).pencil z h‖ ^ 2 := by
  have hge := D.re_inner_pencil_ge h
  have hle := D.re_inner_pencil_le h
  have hgn := D.growth_mul_norm_le h
  have hmul : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hf := norm_nonneg ((horizontalInductionOperator u ε K).pencil z h)
  have hgN2 : 0 ≤ D.growth * ‖transverseH2Embedding h‖ ^ 2 :=
    mul_nonneg D.growth_pos.le (sq_nonneg _)
  have hE1 : ε * transverseGradientEnergy h ≤
      2 * (Real.sqrt 2 * ‖transverseH2Embedding h‖ *
        ‖(horizontalInductionOperator u ε K).pencil z h‖) := by
    linarith
  have hE2 : D.growth * (ε * transverseGradientEnergy h) ≤
      D.growth * (2 * (Real.sqrt 2 * ‖transverseH2Embedding h‖ *
        ‖(horizontalInductionOperator u ε K).pencil z h‖)) :=
    mul_le_mul_of_nonneg_left hE1 D.growth_pos.le
  have hE4 : 2 * Real.sqrt 2 *
        ‖(horizontalInductionOperator u ε K).pencil z h‖ *
          (D.growth * ‖transverseH2Embedding h‖) ≤
      2 * Real.sqrt 2 * ‖(horizontalInductionOperator u ε K).pencil z h‖ *
        (Real.sqrt 2 * ‖(horizontalInductionOperator u ε K).pencil z h‖) :=
    mul_le_mul_of_nonneg_left hgn (by positivity)
  nlinarith [hE2, hE4, hmul]

/-- The constant of `eq:bg-resolvent` in terms
of the retained growth rate `g`: `‖h‖₂ + √ε‖∇_⊥h‖₂ ≤ (√2/g + 2/√g)‖f‖₂`. -/
def backgroundResolventConstant (g : ℝ) : ℝ := Real.sqrt 2 / g + 2 / Real.sqrt g

/-- **`eq:bg-resolvent`**:
`‖h‖₂ + √ε‖∇_⊥h‖₂ ≤ C‖(z - A^bg_{ε,n})h‖₂` with the explicit constant
`C = √2/g + 2/√g`, which depends on no parameter other than the retained growth rate. -/
theorem norm_add_sqrt_eps_gradientEnergy_le
    (D : BackgroundCoercivity β u ε K z S) (h : TransverseC2H2) :
    ‖transverseH2Embedding h‖ +
        Real.sqrt (ε * transverseGradientEnergy h) ≤
      backgroundResolventConstant D.growth *
        ‖(horizontalInductionOperator u ε K).pencil z h‖ := by
  have hg := D.growth_pos
  have hf := norm_nonneg ((horizontalInductionOperator u ε K).pencil z h)
  have h1 : ‖transverseH2Embedding h‖ ≤
      Real.sqrt 2 / D.growth *
        ‖(horizontalInductionOperator u ε K).pencil z h‖ := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hg]
    rw [mul_comm _ D.growth]
    exact D.growth_mul_norm_le h
  have h2 : Real.sqrt (ε * transverseGradientEnergy h) ≤
      2 / Real.sqrt D.growth *
        ‖(horizontalInductionOperator u ε K).pencil z h‖ := by
    have hsg : 0 < Real.sqrt D.growth := Real.sqrt_pos.mpr hg
    rw [div_mul_eq_mul_div, le_div_iff₀ hsg]
    have hprod : Real.sqrt D.growth * Real.sqrt (ε * transverseGradientEnergy h) =
        Real.sqrt (D.growth * (ε * transverseGradientEnergy h)) :=
      (Real.sqrt_mul hg.le _).symm
    rw [mul_comm (Real.sqrt (ε * transverseGradientEnergy h)) (Real.sqrt D.growth),
      hprod]
    have hbound := D.growth_mul_eps_gradientEnergy_le h
    have hsq : D.growth * (ε * transverseGradientEnergy h) ≤
        (2 * ‖(horizontalInductionOperator u ε K).pencil z h‖) ^ 2 := by
      simpa only [mul_pow, show (2 : ℝ) ^ 2 = 4 by norm_num] using hbound
    calc Real.sqrt (D.growth * (ε * transverseGradientEnergy h)) ≤
          Real.sqrt ((2 * ‖(horizontalInductionOperator u ε K).pencil z h‖) ^ 2) :=
          Real.sqrt_le_sqrt hsq
      _ = 2 * ‖(horizontalInductionOperator u ε K).pencil z h‖ :=
          Real.sqrt_sq (by positivity)
  rw [backgroundResolventConstant, add_mul]
  exact add_le_add h1 h2

/-- Coercivity forces the kernel of the pencil to be trivial. -/
theorem eq_zero_of_pencil_eq_zero (D : BackgroundCoercivity β u ε K z S)
    {h : TransverseC2H2}
    (hh : (horizontalInductionOperator u ε K).pencil z h = 0) : h = 0 := by
  have hbound := D.growth_mul_norm_le h
  rw [hh, norm_zero, mul_zero] at hbound
  have hzero : ‖transverseH2Embedding h‖ = 0 := by
    refine le_antisymm (le_of_not_gt ?_) (norm_nonneg _)
    intro hnorm
    exact (not_lt_of_ge hbound) (mul_pos D.growth_pos hnorm)
  have : transverseH2Embedding h = 0 := norm_eq_zero.mp hzero
  exact transverseH2Embedding_injective (by rw [this, map_zero])

/--
**Injectivity of `z - A^bg_{ε,n}` on `𝒢_τ`**, the first of the two consequences of
`eq:background-coercivity` under the parameter choices `eq:axial-separation-choice`
and `eq:background-diffusion-small`.

This is exactly the hypothesis of
`DomainOperator.hasResolventAt_of_compactStateResolvent_of_pencil_injective`
(`Operator/CompactBaseInjectiveResolvent.lean`), whose other hypothesis — a base point with
compact state resolvent — is
`exists_positiveReal_compactStateResolvent_horizontalInductionOperator` of
`Operator/HorizontalSectorBasic.lean`.
The two are assembled over `z ∈ 𝒢_τ` through
`Operator/PointwiseResolvent.hasResolventOnOfPointwiseTwoSidedInverses` in
`Global/TorusBackgroundResolvent.lean`.
-/
theorem pencil_injective (D : BackgroundCoercivity β u ε K z S) :
    Function.Injective ((horizontalInductionOperator u ε K).pencil z) := by
  intro a b hab
  have h0 : (horizontalInductionOperator u ε K).pencil z (a - b) = 0 := by
    rw [map_sub, hab, sub_self]
  exact sub_eq_zero.mp (D.eq_zero_of_pencil_eq_zero h0)

end BackgroundCoercivity

end

end FastDynamo
