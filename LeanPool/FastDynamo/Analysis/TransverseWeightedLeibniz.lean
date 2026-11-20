/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Analysis.TransverseWeightedDiffusion

/-!
# The weighted form `a_z(h, (1 + i beta)h)`: the remaining terms and the §6 bridges

`Analysis/TransverseWeightedDiffusion.lean` proves the weighted diffusion inequality of the
estimate of `I₁` in the proof of `prop:background-resolvent` and its Young absorption.  This
module continues it with everything else the §6 assembly of `prop:background-resolvent`
reads off the weighted form `a_z(h, (1 + i beta_n)h)`:

* the zeroth-order, axial-multiplier and stretching terms;
* the transport term, whose weighted part is the only one that does not cancel;
* the three bridges: an a.e. pointwise lower bound on a real `L∞` coefficient integrates to a
  lower bound on `Re <a f, f>` (localised by an indicator, this is
  `eq:background-phase-positive` in integrated form), `‖h‖₂ ≤ ‖(1 + i beta)h‖₂`,
  and an a.e. pointwise bound on an `L∞` class bounds its norm.

Conventions, the fibre-genericity and the scalar multiplier type are those of the base module.
The docstrings abbreviate `k_n = 2πK_n`, `w = (u_n^bg)_⊥`, `a = (u_n^bg)_3` and
`𝔞_z(h, φ) = ⟨(z - A^bg_{ε,n})h, φ⟩`; the paper writes these out in full.
The two `example`s at the end exhibit the two fibres the formalisation uses: `iota = Fin 2` for
§6's `L²(T²;ℂ²)` and `iota = Fin 3` for the reduced induction operator.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory
open scoped ENNReal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Companion facts for the remaining terms of `𝔞_z(h,(1+iβ)h)` -/

omit [DecidableEq ι] in
/-- The zeroth-order term.  For `z ∈ ℂ`,
`Re ⟨(1 + iβ)h, z h⟩ = (Re z) ‖h‖₂² + (Im z) ∫ β |h|²`.
With `z = ζ - iτ` and the diffusion shift `ε k_n²` this is the bracket
`[Re ζ + ε k_n² + β_n(Im ζ - τ)]`, since `Im z = Im ζ - τ`.  The remaining
`+ τ s_n` that completes the paper's `β_n(Im ζ + τ(s_n - 1))`
(the zeroth-order term `I₂` of `eq:background-testing`) comes from the axial multiplier;
see `re_inner_weightedTransverseState_axialMultiplier`. -/
theorem re_inner_weightedTransverseState_smul (β : TransverseScalarW1Inf)
    (h : TransverseVecH2 ι) (z : ℂ) :
    (inner ℂ (weightedTransverseState β h)
        (z • transverseH2Embedding h)).re =
      z.re * ‖transverseH2Embedding h‖ ^ 2 +
        z.im * (inner ℂ (scalarVectorMulTransverseVec ι β.value
          (transverseH2Embedding h)) (transverseH2Embedding h)).re := by
  have hreal := im_inner_scalarVectorMulTransverse_self_eq_zero β.value_isReal
    (transverseH2Embedding h)
  rw [weightedTransverseState]
  simp only [inner_add_left, inner_smul_left, inner_smul_right, Complex.conj_I]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im, re_inner_self,
    im_inner_self, hreal]
  ring

omit [DecidableEq ι] in
/-- **The axial multiplier term, operator orientation.**  For a real `L∞` axial
coefficient `a` and a real wavenumber `k`,

`Re ⟨(1 + iβ)h, (-ik) a h⟩ = -k ∫ β a |h|²`.

This is the sign carried by the *operator* `A^bg_{ε,n}`, whose axial term is
`-i k_n a h` (`eq:background-operator`).  At `k := k_n` it therefore produces
`-k_n ∫ β_n a |h|²`, i.e. the contribution `-τ s_n` to the phase bracket — the **opposite** of what
`eq:background-phase-positive` needs.  §6 tests the *shifted* form
`𝔞_z(h, φ) = ⟨(z - A^bg)h, φ⟩`, whose axial term is `+i k_n ⟨ah, φ⟩`
(`eq:background-testing`); use
`re_inner_weightedTransverseState_axialMultiplier` for that orientation, or
equivalently apply the present lemma with `k := -k_n`. -/
theorem re_inner_weightedTransverseState_axialMultiplierOperator
    (β : TransverseScalarW1Inf) {a : TransverseScalarLInf}
    (ha : IsRealTransverseScalarLInf a) (k : ℝ) (h : TransverseVecH2 ι) :
    (inner ℂ (weightedTransverseState β h)
        ((-(k : ℂ) * Complex.I) •
          scalarVectorMulTransverseVec ι a (transverseH2Embedding h))).re =
      -k * (inner ℂ (scalarVectorMulTransverseVec ι β.value
          (transverseH2Embedding h))
        (scalarVectorMulTransverseVec ι a (transverseH2Embedding h))).re := by
  have haxial : (inner ℂ (transverseH2Embedding h)
      (scalarVectorMulTransverseVec ι a (transverseH2Embedding h))).im = 0 :=
    im_inner_self_scalarVectorMulTransverse_eq_zero ha (transverseH2Embedding h)
  rw [weightedTransverseState]
  simp only [inner_add_left, inner_smul_left, inner_smul_right, Complex.conj_I]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, haxial]
  ring

omit [DecidableEq ι] in
/-- **The axial multiplier term, `𝔞_z` orientation** — the one §6 uses.
For a real `L∞` axial coefficient `a` and a real wavenumber `k`,

`Re ⟨(1 + iβ)h, (+ik) a h⟩ = +k ∫ β a |h|²`.

The operator `A^bg_{ε,n}` carries `-i k_n a h` (`eq:background-operator`), so the shifted
form `𝔞_z(h, φ) = ⟨(z - A^bg)h, φ⟩` carries `+i k_n ⟨ah, φ⟩`
(`eq:background-testing`).  With the axial normalisation
`k_n a^{ax} = τ s_n` — forced by `k_n ℓ_m = N r_m`
(the relation `2πK_nℓ_m = 2πr_m` before `eq:background-local-coefficients`) — the conclusion at
`k := k_n` is `+ τ ∫ β_n s_n |h|²`, which is exactly the `+ τ s_n` of the phase bracket
`β_n(Im ζ + τ(s_n - 1))` of `eq:background-phase-positive`; the matching `- τ` is supplied by
`re_inner_weightedTransverseState_smul` through `Im z = Im ζ - τ`. -/
theorem re_inner_weightedTransverseState_axialMultiplier
    (β : TransverseScalarW1Inf) {a : TransverseScalarLInf}
    (ha : IsRealTransverseScalarLInf a) (k : ℝ) (h : TransverseVecH2 ι) :
    (inner ℂ (weightedTransverseState β h)
        (((k : ℂ) * Complex.I) •
          scalarVectorMulTransverseVec ι a (transverseH2Embedding h))).re =
      k * (inner ℂ (scalarVectorMulTransverseVec ι β.value
          (transverseH2Embedding h))
        (scalarVectorMulTransverseVec ι a (transverseH2Embedding h))).re := by
  have hmain :=
    re_inner_weightedTransverseState_axialMultiplierOperator β ha (-k) h
  have hcast : (-((-k : ℝ) : ℂ) * Complex.I) = (k : ℂ) * Complex.I := by
    push_cast
    ring
  rw [hcast] at hmain
  rw [hmain]
  ring

omit [DecidableEq ι] in
/-- The squared norm of the weighted test field:
`‖(1 + iβ)h‖₂² = ‖h‖₂² + ‖β h‖₂²`. -/
theorem norm_weightedTransverseState_sq (β : TransverseScalarW1Inf)
    (h : TransverseVecH2 ι) :
    ‖weightedTransverseState β h‖ ^ 2 =
      ‖transverseH2Embedding h‖ ^ 2 +
        ‖scalarVectorMulTransverseVec ι β.value (transverseH2Embedding h)‖ ^ 2 := by
  have h1 := im_inner_self_scalarVectorMulTransverse_eq_zero β.value_isReal
    (transverseH2Embedding h)
  have h2 := im_inner_scalarVectorMulTransverse_self_eq_zero β.value_isReal
    (transverseH2Embedding h)
  rw [← re_inner_self, weightedTransverseState]
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    Complex.conj_I]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im, re_inner_self,
    im_inner_self, h1, h2]
  ring

omit [DecidableEq ι] in
/-- `|1 + iβ| ≤ √2` whenever `|β| ≤ 1`, in the `L²` form
`‖(1 + iβ)h‖₂ ≤ √2 ‖h‖₂`.  This is the factor `√2` in the a-priori estimate
`√2 ‖f‖₂ ‖h‖₂ ≥ Re 𝔞_z(h,(1+iβ_n)h)` at the end of the proof of
`prop:background-resolvent`. -/
theorem norm_weightedTransverseState_le (β : TransverseScalarW1Inf)
    (hβ : ‖β.value‖ ≤ 1) (h : TransverseVecH2 ι) :
    ‖weightedTransverseState β h‖ ≤
      Real.sqrt 2 * ‖transverseH2Embedding h‖ := by
  have hsq := norm_weightedTransverseState_sq β h
  have hmul : ‖scalarVectorMulTransverseVec ι β.value (transverseH2Embedding h)‖ ≤
      ‖transverseH2Embedding h‖ := by
    refine le_trans (norm_scalarVectorMulTransverseVec_apply_le _ _) ?_
    nlinarith [norm_nonneg (transverseH2Embedding h), norm_nonneg β.value, hβ]
  have hbound : ‖weightedTransverseState β h‖ ^ 2 ≤
      (Real.sqrt 2 * ‖transverseH2Embedding h‖) ^ 2 := by
    have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    rw [mul_pow, h2, hsq]
    nlinarith [hmul, norm_nonneg
      (scalarVectorMulTransverseVec ι β.value (transverseH2Embedding h)),
      norm_nonneg (transverseH2Embedding h)]
  have hrhs : 0 ≤ Real.sqrt 2 * ‖transverseH2Embedding h‖ :=
    mul_nonneg (Real.sqrt_nonneg 2) (norm_nonneg _)
  nlinarith [hbound, norm_nonneg (weightedTransverseState β h), hrhs]

omit [DecidableEq ι] in
/-- **Generic bound for every lower-order term.**  Testing any `L²` field `S`
against the weighted test field costs at most `√2 ‖h‖₂ ‖S‖₂`.  Applied to the
stretching output `S = (h·∇_⊥)w` together with the support-restricted
multiplier bounds of `Global/TorusLocalCoreMeasurability.lean`, this gives
`|Re ⟨(h·∇_⊥)w, (1 + iβ)h⟩| ≤ √2 ‖∇_⊥ w‖_∞ ∫_{supp ∇w} |h|²`, the bound quoted
for `I₄` after `eq:background-local-coefficients`. -/
theorem abs_re_inner_weightedTransverseState_le (β : TransverseScalarW1Inf)
    (hβ : ‖β.value‖ ≤ 1) (h : TransverseVecH2 ι) (S : TransverseVecL2 ι) :
    |(inner ℂ (weightedTransverseState β h) S).re| ≤
      Real.sqrt 2 * ‖transverseH2Embedding h‖ * ‖S‖ := by
  refine le_trans (Complex.abs_re_le_norm _) ?_
  refine le_trans (norm_inner_le_norm _ _) ?_
  exact mul_le_mul_of_nonneg_right
    (norm_weightedTransverseState_le β hβ h) (norm_nonneg _)

/-! ## The transport term -/

/-- The transverse transport output `Σ_j a_j ∂_j h` for a family of scalar `L∞`
coefficients.  With `a_j = w_j` the horizontal components of the background
velocity this is the paper's `(u_n^bg)_⊥·∇_⊥ h`. -/
def transverseCoefficientTransport (a : Fin 2 → TransverseScalarLInf)
    (h : TransverseVecH2 ι) : TransverseVecL2 ι :=
  ∑ j : Fin 2, scalarVectorMulTransverseVec ι (a j) (transverseVecDerivFromH2 ι j h)

/-- **Splitting of the weighted transport term.**  The unweighted half
`Re ⟨h, w·∇_⊥ h⟩` vanishes for a divergence-free `w ∈ W^{1,∞}`; that is
`Global/ReducedInductionEnergyIdentity.re_inner_reducedInductionTransport_eq_zero`
and is reused unchanged.  Only the weighted half has to be estimated. -/
theorem re_inner_weightedTransverseState_transport_eq
    (β : TransverseScalarW1Inf) (a : Fin 2 → TransverseScalarLInf)
    (h : TransverseVecH2 ι) :
    (inner ℂ (weightedTransverseState β h)
        (transverseCoefficientTransport a h)).re =
      (inner ℂ (transverseH2Embedding h)
          (transverseCoefficientTransport a h)).re +
        (inner ℂ (Complex.I • scalarVectorMulTransverseVec ι β.value
          (transverseH2Embedding h))
            (transverseCoefficientTransport a h)).re := by
  rw [weightedTransverseState, inner_add_left, Complex.add_re]

/-- **The weighted transport estimate.**  For real `L∞` coefficients `a_j`,

`|Re ⟨iβh, Σ_j a_j ∂_j h⟩| ≤ Σ_j ‖a_j β h‖₂ ‖∂_j h‖₂`,

which is the Cauchy–Schwarz form of the paper's
`∫ |β_n w| |h| |∇_⊥ h|` (the estimate of `I₃`).
The background layer combines it
with `|β_n w| ≤ C √ε 1_{𝒞_n}` from `eq:background-local-coefficients` and one
more Young inequality to reach `(ε/4)‖∇h‖² + C ∫_{𝒞_n}|h|²`. -/
theorem abs_re_inner_weightedPart_transport_le (β : TransverseScalarW1Inf)
    {a : Fin 2 → TransverseScalarLInf}
    (ha : ∀ j, IsRealTransverseScalarLInf (a j)) (h : TransverseVecH2 ι) :
    |(inner ℂ (Complex.I • scalarVectorMulTransverseVec ι β.value
        (transverseH2Embedding h))
          (transverseCoefficientTransport a h)).re| ≤
      ∑ j : Fin 2,
        ‖scalarVectorMulTransverseVec ι (a j)
            (scalarVectorMulTransverseVec ι β.value (transverseH2Embedding h))‖ *
          ‖transverseVecDerivFromH2 ι j h‖ := by
  have hterm : ∀ j : Fin 2,
      inner ℂ (Complex.I • scalarVectorMulTransverseVec ι β.value
          (transverseH2Embedding h))
        (scalarVectorMulTransverseVec ι (a j) (transverseVecDerivFromH2 ι j h)) =
      (-Complex.I) *
        inner ℂ (scalarVectorMulTransverseVec ι (a j)
            (scalarVectorMulTransverseVec ι β.value (transverseH2Embedding h)))
          (transverseVecDerivFromH2 ι j h) := by
    intro j
    rw [inner_smul_left,
      inner_scalarVectorMulTransverse_real_selfAdjoint (ha j)]
    simp [Complex.conj_I]
  rw [transverseCoefficientTransport, inner_sum]
  rw [Finset.sum_congr rfl (fun j _ ↦ hterm j)]
  rw [Complex.re_sum]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  apply Finset.sum_le_sum
  intro j hj
  refine le_trans (Complex.abs_re_le_norm _) ?_
  rw [norm_mul]
  simp only [norm_neg, Complex.norm_I, one_mul]
  exact norm_inner_le_norm _ _

/-! ## Bridges for the §6 assembly

`eq:background-phase-positive` is an almost
everywhere *pointwise* lower bound for the real scalar coefficient
`β_n(Im ζ + τ(s_n - 1))`, while §6 uses its *integrated* form

`∫ β_n(Im ζ + τ(s_n - 1))|h|² ≥ (τ c_q²/2) ∫_{𝒞_n}|h|² - (M²/2τ) ‖h‖₂²`

(inside the lower bound for `I₂`).  The declarations below supply
that passage, the reverse inequality `‖h‖₂ ≤ ‖(1 + iβ)h‖₂` behind
`|1 + iβ_n| ≥ 1`, and the pointwise-to-`L∞`
bridge that turns the pointwise `|β_n| ≤ 1` of
`eq:background-multiplier-bounds` into the
hypothesis `‖β.value‖ ≤ 1` used by `norm_weightedTransverseState_le`.
-/

omit [DecidableEq ι] in
/-- The self-pairing of a vector of the fibre is its squared norm. -/
private theorem re_inner_self_point (v : EuclideanSpace ℂ ι) :
    (inner ℂ v v : ℂ).re = ‖v‖ ^ 2 := by
  have h : (inner ℂ v v : ℂ) = ((‖v‖ : ℝ) : ℂ) ^ 2 :=
    inner_self_eq_norm_sq_to_K v
  rw [h, ← Complex.ofReal_pow, Complex.ofReal_re]

omit [DecidableEq ι] in
/-- The real part of a scalar multiple of the self-pairing, at one point of the
fibre: `Re ⟨c v, v⟩ = (Re c) ‖v‖²`. -/
private theorem re_inner_smul_self_point (c : ℂ) (v : EuclideanSpace ℂ ι) :
    (inner ℂ (c • v) v : ℂ).re = c.re * ‖v‖ ^ 2 := by
  have h : (inner ℂ v v : ℂ) = ((‖v‖ : ℝ) : ℂ) ^ 2 :=
    inner_self_eq_norm_sq_to_K v
  rw [inner_smul_left, h, ← Complex.ofReal_pow, Complex.mul_re, Complex.conj_re,
    Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

omit [DecidableEq ι] in
/-- The real part of an `L²` pairing is the integral of the pointwise real
parts. -/
private theorem re_inner_eq_integral (f g : TransverseVecL2 ι) :
    (inner ℂ f g : ℂ).re =
      ∫ x, (inner ℂ (f x) (g x) : ℂ).re ∂transverseMeasure := by
  rw [MeasureTheory.L2.inner_def]
  have h := integral_re (L2.integrable_inner (𝕜 := ℂ) f g)
  simp only [RCLike.re_to_complex] at h
  exact h.symm

omit [DecidableEq ι] in
/-- **Parseval in physical space**: `‖f‖₂² = ∫ |f|²`. -/
theorem sq_norm_transverseVecL2_eq_integral (f : TransverseVecL2 ι) :
    ‖f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂transverseMeasure := by
  rw [← re_inner_self f, re_inner_eq_integral f f]
  refine integral_congr_ae ?_
  filter_upwards with x
  exact re_inner_self_point _

omit [DecidableEq ι] in
/-- The pointwise squared norm of an `L²` field is integrable. -/
theorem integrable_sq_norm_transverseVecL2 (f : TransverseVecL2 ι) :
    Integrable (fun x ↦ ‖f x‖ ^ 2) transverseMeasure := by
  refine ((L2.integrable_inner (𝕜 := ℂ) f f).re).congr ?_
  filter_upwards with x
  exact re_inner_self_point _

omit [DecidableEq ι] in
/-- **The multiplier pairing as an integral**: for any essentially bounded
scalar coefficient `a`, `Re ⟨a f, f⟩ = ∫ (Re a) |f|²`.  Reality of `a` is not
needed: only its real part enters. -/
theorem re_inner_scalarVectorMulTransverseVec_self_eq_integral
    (a : TransverseScalarLInf) (f : TransverseVecL2 ι) :
    (inner ℂ (scalarVectorMulTransverseVec ι a f) f).re =
      ∫ x, (a x).re * ‖f x‖ ^ 2 ∂transverseMeasure := by
  rw [re_inner_eq_integral]
  refine integral_congr_ae ?_
  filter_upwards [scalarVectorMulTransverseVec_coe_ae a f] with x hx
  rw [hx]
  exact re_inner_smul_self_point (a x) _

omit [DecidableEq ι] in
/-- The integrand of the multiplier pairing is integrable. -/
theorem integrable_re_scalarVectorMulTransverseVec (a : TransverseScalarLInf)
    (f : TransverseVecL2 ι) :
    Integrable (fun x ↦ (a x).re * ‖f x‖ ^ 2) transverseMeasure := by
  refine ((L2.integrable_inner (𝕜 := ℂ)
    (scalarVectorMulTransverseVec ι a f) f).re).congr ?_
  filter_upwards [scalarVectorMulTransverseVec_coe_ae a f] with x hx
  rw [hx]
  exact re_inner_smul_self_point (a x) _

omit [DecidableEq ι] in
/-- **`|1 + iβ| ≥ 1`**, in the `L²` form `‖h‖₂ ≤ ‖(1 + iβ)h‖₂`.  The paper does not state
this bound (the end of the proof of `prop:background-resolvent` uses only `|β_n| ≤ 1`); it is
the companion of the upper bound `norm_weightedTransverseState_le`. -/
theorem norm_le_norm_weightedTransverseState (β : TransverseScalarW1Inf)
    (h : TransverseVecH2 ι) :
    ‖transverseH2Embedding h‖ ≤ ‖weightedTransverseState β h‖ := by
  have hsq := norm_weightedTransverseState_sq β h
  have hnn : (0 : ℝ) ≤ ‖scalarVectorMulTransverseVec ι β.value
      (transverseH2Embedding h)‖ ^ 2 := sq_nonneg _
  nlinarith [hsq, hnn, norm_nonneg (transverseH2Embedding h),
    norm_nonneg (weightedTransverseState β h)]

/-- **Pointwise to `L∞` norm.**  An almost everywhere pointwise bound on a
transverse scalar `L∞` class bounds its norm by the same constant.  This is how
the pointwise `|β_n| = |F(s_n)| ≤ 1` of `eq:background-multiplier-bounds`
becomes the hypothesis `‖β.value‖ ≤ 1`. -/
theorem norm_transverseScalarLInf_le_of_ae_bound (a : TransverseScalarLInf)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ᵐ x ∂transverseMeasure, ‖a x‖ ≤ C) : ‖a‖ ≤ C := by
  rw [Lp.norm_def, eLpNorm_exponent_top (Lp.aestronglyMeasurable a)]
  exact ENNReal.toReal_le_of_le_ofReal hC
    (eLpNormEssSup_le_of_ae_bound hbound)

/-- The pointwise form of `|β_n| ≤ 1`, in the shape consumed by
`norm_weightedTransverseState_le`. -/
theorem TransverseScalarW1Inf.norm_value_le_one_of_ae_bound
    (β : TransverseScalarW1Inf)
    (hβ : ∀ᵐ x ∂transverseMeasure, ‖β.value x‖ ≤ 1) : ‖β.value‖ ≤ 1 :=
  norm_transverseScalarLInf_le_of_ae_bound β.value zero_le_one hβ

/-- The pointwise form of the gradient bound of
`eq:background-multiplier-bounds`: an a.e.
bound `|∂_j β| ≤ C` on both components gives `‖∇β‖_∞² ≤ 2C²` in the
`gradSupNormSq` reading. -/
theorem TransverseScalarW1Inf.gradSupNormSq_le_of_ae_bound
    (β : TransverseScalarW1Inf) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ j : Fin 2, ∀ᵐ x ∂transverseMeasure, ‖(β.grad j) x‖ ≤ C) :
    β.gradSupNormSq ≤ 2 * C ^ 2 := by
  have hj : ∀ j : Fin 2, ‖β.grad j‖ ^ 2 ≤ C ^ 2 := by
    intro j
    have h := norm_transverseScalarLInf_le_of_ae_bound (β.grad j) hC (hb j)
    nlinarith [norm_nonneg (β.grad j), h]
  rw [TransverseScalarW1Inf.gradSupNormSq, Fin.sum_univ_two]
  nlinarith [hj 0, hj 1]

/-! ## The two fibres used by the formalisation -/

/-- §6 works on `L²(T²;ℂ²)` (`eq:background-operator`): the coercive estimate at the
two-component fibre. -/
example (β : TransverseScalarW1Inf) (h : TransverseC2H2) :
    3 / 4 * transverseGradientEnergy h -
        β.gradSupNormSq * ‖transverseH2Embedding h‖ ^ 2 ≤
      (inner ℂ (weightedTransverseState β h)
        (-transverseVecLaplacianFromH2 (Fin 2) h)).re :=
  re_inner_weightedTransverseState_neg_laplacian_ge_young β h

/-- The same estimate at the three-component fibre of the reduced induction
operator. -/
example (β : TransverseScalarW1Inf) (h : TransverseC3H2) :
    3 / 4 * transverseGradientEnergy h -
        β.gradSupNormSq * ‖transverseH2Embedding h‖ ^ 2 ≤
      (inner ℂ (weightedTransverseState β h)
        (-transverseLaplacianFromH2 h)).re :=
  re_inner_weightedTransverseState_neg_laplacian_ge_young β h

end

end FastDynamo
