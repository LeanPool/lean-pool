/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.RecentDefectCongruenceBound

/-!
# High-contrast homogenization: Entry.Response.Kernel.EtaKernelBound

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The η-kernel bound

This is the η-kernel of the diagonal weak-norm estimate (`p.response.transfer`): for each depth
`n` and index `w`, the two-sided normalized recent defect satisfies `∫ ‖D_{n,w}‖² ≤ K_n η^{2/Q}`
once the two-sided smallness hypothesis `∫ respAllScaleAbs^Q dP ≤ Cm η` is supplied together with
its measurability and integrability. This file discharges both premises from `RawOutput`,
`RespCalibrated` and `RespSourceSmall` alone, so that the two corollaries below need no further
analytic input.
-/

section
open HCPolySupport.HighContrast (CoeffSpace)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator
open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ}

/-- **The η-kernel** (paper `p.response.transfer`).  For each depth `n` and index `w`, the
two-sided normalized recent defect is square-integrable with
`∫ ‖D_{n,w}‖^2 ≤ K_n η^{2/Q}`.

The smallness hypothesis is the TWO-SIDED `∫ respAllScaleAbs ^ Q ∂P ≤ Cm * η`, not the
one-sided `respAllScaleMax` one.  The conclusion `K n * η ^ (2/Q)` and every other binder are
unchanged.  The η-kernel obstruction shows that the one-sided hypothesis implies the conclusion
for NO constant sequence `K`; the paper routes this step through the two-sided fluctuation
history, not through `M` (`p.response.transfer`).  The two-sided premise is carried by an `L²`
quantity and is discharged through `blockOpNorm (normalizedFluctuation …)`.

The lower side needs a pathwise lower Loewner bound.  The deterministic block-algebra
identities `swapConj_lowerRight` / `schurSigma_le_corrected` / `meanPenalty` concern a single
symmetric positive definite `E`; they mention neither the sample `a` nor the cell, so they
cannot produce that bound.  The route is:

* `D_{n,w} = (N_{n,w} - I) - (N_0 - I)` with `N = normalizedBlock(·, E_t)`, using
  `normalizedBlock_blockSub` and `adaptedCellAtCenter_zero`;
* both summands are bounded by `respAllScaleAbs` through `le_csSup` (weights `3^{ρn}` and `1`),
  so `‖D_{n,w}‖ ≤ (3^{ρn} + 1) · respAllScaleAbs a` -- this is the step the one-sided carrier
  could not supply;
* the recentred field `a_∓` and the normalizer `Ehat^∓ = blockCongr (respG F) E_t` are the
  SAME congruence of the `E_t`-picture (`coarseBlockMatrix_respCoeffMinus_at` /
  `_respCoeffPlus_at` below), and a congruence applied to both the block
  and its normalizer leaves the normalized block orthogonally similar, hence leaves
  `blockOpNorm` unchanged;
* Jensen on the probability measure with `Q ≥ 2` then gives
  `∫ D^2 ≤ (3^{ρn}+1)^2 (Cm η)^{2/Q}`, i.e. `K n := (3^{ρn}+1)^2 · Cm^{2/Q} > 0`.

Conjunct 1 (measurability) is `aestronglyMeasurable_recentDefectBlock_minus/plus` above,
carrier-independent.  Conjunct 2 is the same pointwise bound.

All three conjuncts, both signs.  `K n :=
(3 ^ (Quenched.contrastRho γ * n) + 1) ^ 2 * Cm ^ (2/Q)`, positive.  The chain above:

* `blockSpecBound_le_blockOpNorm` -- `blockSpecBound N ≤ blockOpNorm N` UNCONDITIONALLY, so
  the new hypothesis implies the old one and no `respAllScaleMax` consumer is lost;
* `blockOpNorm_sub_id_le_specBound_add_two` and `pathwise_envelope_abs` -- the
  two-sided defining set is a.e. `BddAbove`, the `respAllScaleAbs` analogue;
* `weighted_blockOpNorm_le_respAllScaleAbs` -- the `le_csSup` step;
* `blockOpNorm_normalizedBlock_sub_le` -- the split `(N_{n,w} - I) - (N_0 - I)` in the
  `E_t`-picture, which is where BOTH sides are needed and where the one-sided carrier fails;
* `blockOpNorm_normalizedBlock_blockCongr_le` -- congruence invariance:
  `U = matSqrt E · G · matSqrt (Gᵀ E G)⁻¹` has `Uᵀ U = 1`, so applying the same `blockCongr` to
  a block and to its normalizer leaves the normalized block orthogonally similar;
* `blockCongr_posDef` (with `isUnit_respG` / `isUnit_respGPlus`) -- positive
  definiteness of `Ehat^∓`, discharged, not assumed;
* `recentDefect_le_respAllScaleAbs_minus` / `_plus` -- THE η-KERNEL POINTWISE BOUND,
  `recentDefect ≤ (3 ^ (ρ n) + 1) · respAllScaleAbs a` a.e., uniformly in `n` and `w`;
* `respAllScaleAbs_measurable`, `respAllScaleAbs_nonneg`,
  `integral_sq_le_rpow` (Jensen, `∫ f ^ 2 ≤ (∫ f ^ Q) ^ (2/Q)` on a probability measure) and
  `conjuncts_of_pointwise` -- integrability (conjunct 2) and the exponent (conjunct 3).

Conjunct 1 is `aestronglyMeasurable_recentDefectBlock_minus` / `_plus`, carrier-independent.
-/
theorem integral_recentDefect_sq_le_minus (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1) (S : SelectionData) (hS : S.Selects d γ) (Cc Cm : ℝ)
    (hCc : 0 < Cc) (hCm : 0 < Cm) :
    ∃ K : ℕ → ℝ, (∀ n, 0 < K n) ∧
      ∀ (ε σ Cglob Cprof Csrc Bresp : ℝ) (H : ℕ) (P : Measure (CoeffSpace d)) (E : BlockMat d)
        (Ψ : ℝ → ℝ) (Kg : ℝ) (Src : CoeffSpace d → ℝ) (B : ℝ) (jStar : ℕ) (F : BlockMat d)
        (s t : ℤ),
        RawOutput d γ S ε σ Cglob Cprof Csrc H Bresp P E Ψ Kg Src B jStar F s t →
        RespCalibrated Cc P jStar F s t →
        ∀ η : ℝ, η ∈ Set.Ioo (0 : ℝ) (1 / 2) →
          Integrable (fun a => respAllScaleAbs P γ jStar F t a ^ bigQ d γ) P →
          ∫ a, respAllScaleAbs P γ jStar F t a ^ bigQ d γ ∂P ≤ Cm * η →
          ∀ (n : ℕ) (w : Fin d → ℤ), w ∈ triadicIndexBox d n →
            AEStronglyMeasurable (fun a =>
              recentDefectBlock (respGrid jStar F) t n w (respEhatMinus P jStar F t)
                (respCoeffMinus F a)) P ∧
            Integrable (fun a =>
              recentDefect (respGrid jStar F) t n w (respEhatMinus P jStar F t)
                (respCoeffMinus F a) ^ 2) P ∧
            ∫ a, recentDefect (respGrid jStar F) t n w (respEhatMinus P jStar F t)
                (respCoeffMinus F a) ^ 2 ∂P ≤ K n * η ^ ((2 : ℝ) / (bigQ d γ : ℝ)) := by
  let : NeZero d := ⟨by omega⟩
  -- `hS`/`hCc` are carried by the statement (which is unchanged apart from the two-sided
  -- smallness hypothesis) but are not needed by this route; named here so the unused-variable
  -- linter does not force a rename of the binders.
  have _hS_unused := hS
  have _hCc_unused := hCc
  refine ⟨fun n => ((3 : ℝ) ^ (Quenched.contrastRho γ * (n : ℝ)) + 1) ^ 2 *
      Cm ^ ((2 : ℝ) / (bigQ d γ : ℝ)), fun n => ?_, ?_⟩
  · change (0 : ℝ) < ((3 : ℝ) ^ (Quenched.contrastRho γ * (n : ℝ)) + 1) ^ 2 * Cm ^ ((2 : ℝ) /
    (bigQ d γ : ℝ))
    have h1 : (0 : ℝ) < (3 : ℝ) ^ (Quenched.contrastRho γ * (n : ℝ)) := Real.rpow_pos_of_pos (by
      norm_num) _
    have h2 : (0 : ℝ) < Cm ^ ((2 : ℝ) / (bigQ d γ : ℝ)) := Real.rpow_pos_of_pos hCm _
    exact mul_pos (pow_pos (by linarith only [h1]) 2) h2
  · intro ε σ Cglob Cprof Csrc Bresp H P E Ψ Kg Src B jStar F s t raw _hcal η hη hAint hAle n w hw
    have := raw.prob
    have hm : (explicitCanonicalMetric F).PosDef := Geometry.explicitCanonicalMetric_posDef
      raw.symm raw.pos
    have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid raw.hj hm
    have hQ2 : 2 ≤ bigQ d γ := bigQ_two_le d γ hγ
    have hmeas1 := aestronglyMeasurable_recentDefectBlock_minus hq P t n w (respEhatMinus P
      jStar F t) F
    have hg0 : ∀ a : CoeffSpace d, 0 ≤ recentDefect (respGrid jStar F) t n w
        (respEhatMinus P jStar F t) (respCoeffMinus F a) := fun a => norm_nonneg _
    have hgmeas : AEStronglyMeasurable (fun a : CoeffSpace d =>
        recentDefect (respGrid jStar F) t n w (respEhatMinus P jStar F t)
          (respCoeffMinus F a) ^ 2) P := by
      have hsq : (fun a : CoeffSpace d => recentDefect (respGrid jStar F) t n w
            (respEhatMinus P jStar F t) (respCoeffMinus F a) ^ 2)
          = fun a : CoeffSpace d => ‖recentDefectBlock (respGrid jStar F) t n w
              (respEhatMinus P jStar F t) (respCoeffMinus F a)‖ *
            ‖recentDefectBlock (respGrid jStar F) t n w
              (respEhatMinus P jStar F t) (respCoeffMinus F a)‖ := by
        funext a
        rw [recentDefect]
        ring
      rw [hsq]
      exact hmeas1.norm.mul hmeas1.norm
    have hAmeas : AEStronglyMeasurable (fun a : CoeffSpace d =>
        respAllScaleAbs P γ jStar F t a ^ 2) P :=
      ((respAllScaleAbs_measurable P γ jStar F hq t).pow_const 2).aestronglyMeasurable
    have hbd := recentDefect_le_respAllScaleAbs_minus hd γ hγ P E Ψ Kg Src
      raw.stat raw.ell jStar raw.hj F hm t
    have hbound : ∀ᵐ a ∂P, recentDefect (respGrid jStar F) t n w
        (respEhatMinus P jStar F t) (respCoeffMinus F a)
        ≤ ((3 : ℝ) ^ (Quenched.contrastRho γ * (n : ℝ)) + 1) * respAllScaleAbs P γ jStar F t a := by
      filter_upwards [hbd] with a ha using ha n w hw
    have hc : (0 : ℝ) ≤ (3 : ℝ) ^ (Quenched.contrastRho γ * (n : ℝ)) + 1 := by
      have := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) (Quenched.contrastRho γ * (n : ℝ))
      linarith only [this]
    obtain ⟨hint, hle⟩ := conjuncts_of_pointwise P (bigQ d γ) hQ2 Cm η hCm hη.1 _ _
      (respAllScaleAbs_nonneg P γ jStar F t) hg0 hgmeas hAmeas _ hc hbound hAint hAle
    exact ⟨hmeas1, hint, hle⟩

/-- **The η-kernel, plus sign.** -/
theorem integral_recentDefect_sq_le_plus (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1) (S : SelectionData) (hS : S.Selects d γ) (Cc Cm : ℝ)
    (hCc : 0 < Cc) (hCm : 0 < Cm) :
    ∃ K : ℕ → ℝ, (∀ n, 0 < K n) ∧
      ∀ (ε σ Cglob Cprof Csrc Bresp : ℝ) (H : ℕ) (P : Measure (CoeffSpace d)) (E : BlockMat d)
        (Ψ : ℝ → ℝ) (Kg : ℝ) (Src : CoeffSpace d → ℝ) (B : ℝ) (jStar : ℕ) (F : BlockMat d)
        (s t : ℤ),
        RawOutput d γ S ε σ Cglob Cprof Csrc H Bresp P E Ψ Kg Src B jStar F s t →
        RespCalibrated Cc P jStar F s t →
        ∀ η : ℝ, η ∈ Set.Ioo (0 : ℝ) (1 / 2) →
          Integrable (fun a => respAllScaleAbs P γ jStar F t a ^ bigQ d γ) P →
          ∫ a, respAllScaleAbs P γ jStar F t a ^ bigQ d γ ∂P ≤ Cm * η →
          ∀ (n : ℕ) (w : Fin d → ℤ), w ∈ triadicIndexBox d n →
            AEStronglyMeasurable (fun a =>
              recentDefectBlock (respGrid jStar F) t n w (respEhatPlus P jStar F t)
                (respCoeffPlus F a)) P ∧
            Integrable (fun a =>
              recentDefect (respGrid jStar F) t n w (respEhatPlus P jStar F t)
                (respCoeffPlus F a) ^ 2) P ∧
            ∫ a, recentDefect (respGrid jStar F) t n w (respEhatPlus P jStar F t)
                (respCoeffPlus F a) ^ 2 ∂P ≤ K n * η ^ ((2 : ℝ) / (bigQ d γ : ℝ)) := by
  let : NeZero d := ⟨by omega⟩
  -- `hS`/`hCc` are carried by the statement (which is unchanged apart from the two-sided
  -- smallness hypothesis) but are not needed by this route; named here so the unused-variable
  -- linter does not force a rename of the binders.
  have _hS_unused := hS
  have _hCc_unused := hCc
  refine ⟨fun n => ((3 : ℝ) ^ (Quenched.contrastRho γ * (n : ℝ)) + 1) ^ 2 *
      Cm ^ ((2 : ℝ) / (bigQ d γ : ℝ)), fun n => ?_, ?_⟩
  · change (0 : ℝ) < ((3 : ℝ) ^ (Quenched.contrastRho γ * (n : ℝ)) + 1) ^ 2 * Cm ^ ((2 : ℝ) /
    (bigQ d γ : ℝ))
    have h1 : (0 : ℝ) < (3 : ℝ) ^ (Quenched.contrastRho γ * (n : ℝ)) := Real.rpow_pos_of_pos (by
      norm_num) _
    have h2 : (0 : ℝ) < Cm ^ ((2 : ℝ) / (bigQ d γ : ℝ)) := Real.rpow_pos_of_pos hCm _
    exact mul_pos (pow_pos (by linarith only [h1]) 2) h2
  · intro ε σ Cglob Cprof Csrc Bresp H P E Ψ Kg Src B jStar F s t raw _hcal η hη hAint hAle n w hw
    have := raw.prob
    have hm : (explicitCanonicalMetric F).PosDef := Geometry.explicitCanonicalMetric_posDef
      raw.symm raw.pos
    have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid raw.hj hm
    have hQ2 : 2 ≤ bigQ d γ := bigQ_two_le d γ hγ
    have hmeas1 := aestronglyMeasurable_recentDefectBlock_plus hq P t n w (respEhatPlus P jStar
      F t) F
    have hg0 : ∀ a : CoeffSpace d, 0 ≤ recentDefect (respGrid jStar F) t n w
        (respEhatPlus P jStar F t) (respCoeffPlus F a) := fun a => norm_nonneg _
    have hgmeas : AEStronglyMeasurable (fun a : CoeffSpace d =>
        recentDefect (respGrid jStar F) t n w (respEhatPlus P jStar F t)
          (respCoeffPlus F a) ^ 2) P := by
      have hsq : (fun a : CoeffSpace d => recentDefect (respGrid jStar F) t n w
            (respEhatPlus P jStar F t) (respCoeffPlus F a) ^ 2)
          = fun a : CoeffSpace d => ‖recentDefectBlock (respGrid jStar F) t n w
              (respEhatPlus P jStar F t) (respCoeffPlus F a)‖ *
            ‖recentDefectBlock (respGrid jStar F) t n w
              (respEhatPlus P jStar F t) (respCoeffPlus F a)‖ := by
        funext a
        rw [recentDefect]
        ring
      rw [hsq]
      exact hmeas1.norm.mul hmeas1.norm
    have hAmeas : AEStronglyMeasurable (fun a : CoeffSpace d =>
        respAllScaleAbs P γ jStar F t a ^ 2) P :=
      ((respAllScaleAbs_measurable P γ jStar F hq t).pow_const 2).aestronglyMeasurable
    have hbd := recentDefect_le_respAllScaleAbs_plus hd γ hγ P E Ψ Kg Src
      raw.stat raw.ell jStar raw.hj F hm t
    have hbound : ∀ᵐ a ∂P, recentDefect (respGrid jStar F) t n w
        (respEhatPlus P jStar F t) (respCoeffPlus F a)
        ≤ ((3 : ℝ) ^ (Quenched.contrastRho γ * (n : ℝ)) + 1) * respAllScaleAbs P γ jStar F t a := by
      filter_upwards [hbd] with a ha using ha n w hw
    have hc : (0 : ℝ) ≤ (3 : ℝ) ^ (Quenched.contrastRho γ * (n : ℝ)) + 1 := by
      have := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) (Quenched.contrastRho γ * (n : ℝ))
      linarith only [this]
    obtain ⟨hint, hle⟩ := conjuncts_of_pointwise P (bigQ d γ) hQ2 Cm η hCm hη.1 _ _
      (respAllScaleAbs_nonneg P γ jStar F t) hg0 hgmeas hAmeas _ hc hbound hAint hAle
    exact ⟨hmeas1, hint, hle⟩

/-! ### The η-kernel twins reduced to the source hypotheses

Both premises of the twins above -- `Integrable (fun a => respAllScaleAbs ^ Q) P` and
`∫ respAllScaleAbs ^ Q ∂P ≤ Cm η` -- are supplied by
`respAllScaleAbs_aestronglyMeasurable_integrable` (above) and `response_allscale_abs`
.  The two corollaries below discharge both premises and leave
only `RawOutput`, `RespCalibrated`, `RespSourceSmall` and the profile smallness
`Cprof σ^{(1-γ)/8} ≤ η` -- exactly the premises the assembly already supplies to
`response_allscale_abs` and `response_source_smallness` (`AdaptedResponseAssembly.lean`).  They show
that the wiring closes: `Cm` is no longer a free constant of the twins but the `C` produced
by `response_allscale_abs`, and the two `Csrc`s are
reconciled by the tree's `max` idiom, as `AdaptedResponseAssembly.lean` does. -/

/-- `RawOutput` is antitone in the source threshold constant `Csrc`.  Same statement as the
`private` `rawOutput_le_csrc` (`AdaptedResponseAssembly.lean`), which is downstream of this
file. -/
private theorem RawOutput.mono_csrc {γ : ℝ} {S : SelectionData}
    {ε σ Cglob Cprof Csrc Csrc' : ℝ} {H : ℕ} {Bresp : ℝ} {P : Measure (CoeffSpace d)}
    {E : BlockMat d} {Ψ : ℝ → ℝ} {Kg : ℝ} {Src : CoeffSpace d → ℝ} {B : ℝ} {jStar : ℕ}
    {F : BlockMat d} {s t : ℤ}
    (raw : RawOutput d γ S ε σ Cglob Cprof Csrc H Bresp P E Ψ Kg Src B jStar F s t)
    (h : Csrc' ≤ Csrc) :
    RawOutput d γ S ε σ Cglob Cprof Csrc' H Bresp P E Ψ Kg Src B jStar F s t := by
  refine ⟨raw.prob, raw.stat, raw.unit, raw.ell, raw.hB, raw.hj, ?_, raw.symm, raw.pos, raw.hst,
    raw.ht, raw.hs_lo, raw.ht_hi, raw.cube, raw.calib_lo, raw.calib_hi, raw.det, raw.prof,
    raw.ecc⟩
  have hK : 1 < Kg := raw.ell.one_lt_growthWitness
  have hlog : 0 ≤ Real.logb 3 (2 * Kg) :=
    Real.logb_nonneg (by norm_num) (by linarith only [hK])
  refine le_trans (Int.ceil_mono ?_) raw.hsrc
  have := mul_le_mul_of_nonneg_right h hlog
  linarith only [this]

/-- **The η-kernel wired, minus sign.**  The conclusion of `integral_recentDefect_sq_le_minus`
with both
`respAllScaleAbs` premises discharged from `RawOutput` by `response_allscale_abs`
and `respAllScaleAbs_aestronglyMeasurable_integrable`. -/
theorem integral_recentDefect_sq_le_of_rawOutput_minus (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1) (S : SelectionData) (hS : S.Selects d γ) (Cc : ℝ)
    (hCc : 0 < Cc) (Cs : ℝ) (hCs : 0 < Cs) :
    ∃ Csrc : ℝ, 0 < Csrc ∧ ∃ K : ℕ → ℝ, (∀ n, 0 < K n) ∧
      ∀ (ε σ : ℝ), ε ∈ Set.Ioc (0 : ℝ) S.eps0 → σ ∈ Set.Ioc (0 : ℝ) ε →
        ∀ (Cglob Cprof Bresp : ℝ), 0 ≤ Cglob →
          ∀ (H : ℕ) (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (Kg : ℝ)
            (Src : CoeffSpace d → ℝ) (B : ℝ) (jStar : ℕ) (F : BlockMat d) (s t : ℤ),
            RawOutput d γ S ε σ Cglob Cprof Csrc H Bresp P E Ψ Kg Src B jStar F s t →
            RespCalibrated Cc P jStar F s t →
            ∀ η : ℝ, η ∈ Set.Ioo (0 : ℝ) (1 / 2) →
              Cprof * σ ^ ((1 - γ) / 8) ≤ η →
              RespSourceSmall d γ Cs η E F jStar s t →
              ∀ (n : ℕ) (w : Fin d → ℤ), w ∈ triadicIndexBox d n →
                AEStronglyMeasurable (fun a =>
                  recentDefectBlock (respGrid jStar F) t n w (respEhatMinus P jStar F t)
                    (respCoeffMinus F a)) P ∧
                Integrable (fun a =>
                  recentDefect (respGrid jStar F) t n w (respEhatMinus P jStar F t)
                    (respCoeffMinus F a) ^ 2) P ∧
                ∫ a, recentDefect (respGrid jStar F) t n w (respEhatMinus P jStar F t)
                    (respCoeffMinus F a) ^ 2 ∂P ≤ K n * η ^ ((2 : ℝ) / (bigQ d γ : ℝ)) := by
  obtain ⟨CsrcA, hCsrcA, Cm, hCm, hA⟩ := response_allscale_abs d hd γ hγ S hS Cs hCs
  obtain ⟨CsrcI, hCsrcI, hI⟩ :=
    respAllScaleAbs_aestronglyMeasurable_integrable d hd γ hγ S hS
  obtain ⟨K, hK, htwin⟩ := integral_recentDefect_sq_le_minus d hd γ hγ S hS Cc Cm hCc hCm
  refine ⟨max CsrcA CsrcI, lt_max_of_lt_left hCsrcA, K, hK, ?_⟩
  intro ε σ hε hσ Cglob Cprof Bresp hCglob H P E Ψ Kg Src B jStar F s t raw hcal η hη hprof hsrc
  have hrawA := RawOutput.mono_csrc raw (le_max_left CsrcA CsrcI)
  have hrawI := RawOutput.mono_csrc raw (le_max_right CsrcA CsrcI)
  have hint := (hI ε σ hε hσ Cglob Cprof Bresp hCglob H P E Ψ Kg Src B jStar F s t hrawI).2
  have hle := hA ε σ hε hσ Cglob Cprof Bresp hCglob H P E Ψ Kg Src B jStar F s t hrawA η hη
    hprof hsrc
  exact htwin ε σ Cglob Cprof (max CsrcA CsrcI) Bresp H P E Ψ Kg Src B jStar F s t raw hcal η hη
    hint hle

/-- **The η-kernel wired, plus sign.**  The plus twin of
`integral_recentDefect_sq_le_of_rawOutput_minus`. -/
theorem integral_recentDefect_sq_le_of_rawOutput_plus (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1) (S : SelectionData) (hS : S.Selects d γ) (Cc : ℝ)
    (hCc : 0 < Cc) (Cs : ℝ) (hCs : 0 < Cs) :
    ∃ Csrc : ℝ, 0 < Csrc ∧ ∃ K : ℕ → ℝ, (∀ n, 0 < K n) ∧
      ∀ (ε σ : ℝ), ε ∈ Set.Ioc (0 : ℝ) S.eps0 → σ ∈ Set.Ioc (0 : ℝ) ε →
        ∀ (Cglob Cprof Bresp : ℝ), 0 ≤ Cglob →
          ∀ (H : ℕ) (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (Kg : ℝ)
            (Src : CoeffSpace d → ℝ) (B : ℝ) (jStar : ℕ) (F : BlockMat d) (s t : ℤ),
            RawOutput d γ S ε σ Cglob Cprof Csrc H Bresp P E Ψ Kg Src B jStar F s t →
            RespCalibrated Cc P jStar F s t →
            ∀ η : ℝ, η ∈ Set.Ioo (0 : ℝ) (1 / 2) →
              Cprof * σ ^ ((1 - γ) / 8) ≤ η →
              RespSourceSmall d γ Cs η E F jStar s t →
              ∀ (n : ℕ) (w : Fin d → ℤ), w ∈ triadicIndexBox d n →
                AEStronglyMeasurable (fun a =>
                  recentDefectBlock (respGrid jStar F) t n w (respEhatPlus P jStar F t)
                    (respCoeffPlus F a)) P ∧
                Integrable (fun a =>
                  recentDefect (respGrid jStar F) t n w (respEhatPlus P jStar F t)
                    (respCoeffPlus F a) ^ 2) P ∧
                ∫ a, recentDefect (respGrid jStar F) t n w (respEhatPlus P jStar F t)
                    (respCoeffPlus F a) ^ 2 ∂P ≤ K n * η ^ ((2 : ℝ) / (bigQ d γ : ℝ)) := by
  obtain ⟨CsrcA, hCsrcA, Cm, hCm, hA⟩ := response_allscale_abs d hd γ hγ S hS Cs hCs
  obtain ⟨CsrcI, hCsrcI, hI⟩ :=
    respAllScaleAbs_aestronglyMeasurable_integrable d hd γ hγ S hS
  obtain ⟨K, hK, htwin⟩ := integral_recentDefect_sq_le_plus d hd γ hγ S hS Cc Cm hCc hCm
  refine ⟨max CsrcA CsrcI, lt_max_of_lt_left hCsrcA, K, hK, ?_⟩
  intro ε σ hε hσ Cglob Cprof Bresp hCglob H P E Ψ Kg Src B jStar F s t raw hcal η hη hprof hsrc
  have hrawA := RawOutput.mono_csrc raw (le_max_left CsrcA CsrcI)
  have hrawI := RawOutput.mono_csrc raw (le_max_right CsrcA CsrcI)
  have hint := (hI ε σ hε hσ Cglob Cprof Bresp hCglob H P E Ψ Kg Src B jStar F s t hrawI).2
  have hle := hA ε σ hε hσ Cglob Cprof Bresp hCglob H P E Ψ Kg Src B jStar F s t hrawA η hη
    hprof hsrc
  exact htwin ε σ Cglob Cprof (max CsrcA CsrcI) Bresp H P E Ψ Kg Src B jStar F s t raw hcal η hη
    hint hle

/-! ### Local helper for the squared recent sums -/

/-- Helper: on a probability measure, an `L²` bound gives the matching `L¹` bound.
Elementary (Young `2cg ≤ g² + c²`), no Jensen/Hölder needed. -/
private theorem integral_le_of_sq_le {α : Type*} [MeasurableSpace α] (P : Measure α)
    [IsProbabilityMeasure P] (g : α → ℝ) (hg : Integrable g P)
    (hg2 : Integrable (fun a => g a ^ 2) P) (c : ℝ) (hc : 0 < c)
    (h : ∫ a, g a ^ 2 ∂P ≤ c ^ 2) : ∫ a, g a ∂P ≤ c := by
  have h2c : (0 : ℝ) < 2 * c := by linarith only [hc]
  have hmaj : Integrable (fun a => (g a ^ 2 + c ^ 2) / (2 * c)) P :=
    (hg2.add (integrable_const _)).div_const _
  have hstep : ∫ a, g a ∂P ≤ ∫ a, (g a ^ 2 + c ^ 2) / (2 * c) ∂P := by
    refine integral_mono hg hmaj fun a => ?_
    rw [le_div_iff₀ h2c]
    nlinarith only [sq_nonneg (g a - c)]
  have hval : ∫ a, (g a ^ 2 + c ^ 2) / (2 * c) ∂P = (∫ a, g a ^ 2 ∂P + c ^ 2) / (2 * c) := by
    rw [integral_div, integral_add hg2 (integrable_const _)]
    simp
  rw [hval, le_div_iff₀ h2c] at hstep
  have hsq : ∫ a, g a ^ 2 ∂P ≤ c ^ 2 := h
  nlinarith only [hstep, hsq, h2c]

/-- Exponent conversion for the probability-measure square-sum estimate. -/
private theorem etaExponentBounds (Q : ℕ) (hQ : 1 ≤ Q) (η : ℝ)
    (hη : η ∈ Set.Ioo (0 : ℝ) (1 / 2)) :
    0 < (Q : ℝ) ∧ 0 < η ^ ((1 : ℝ) / (Q : ℝ)) ∧
      (η ^ ((1 : ℝ) / (Q : ℝ))) ^ 2 = η ^ ((2 : ℝ) / (Q : ℝ)) ∧
      η ^ ((2 : ℝ) / (Q : ℝ)) ≤ η ^ ((1 : ℝ) / (Q : ℝ)) := by
  have hQ0 : (0 : ℝ) < (Q : ℝ) := by
    have : 0 < Q := lt_of_lt_of_le Nat.zero_lt_one hQ
    exact_mod_cast this
  have hη0 : (0 : ℝ) < η := hη.1
  have hη1 : η < 1 := lt_trans hη.2 (by norm_num)
  have hZpos : (0 : ℝ) < η ^ ((1 : ℝ) / (Q : ℝ)) := Real.rpow_pos_of_pos hη0 _
  have hZsq : (η ^ ((1 : ℝ) / (Q : ℝ))) ^ 2 = η ^ ((2 : ℝ) / (Q : ℝ)) := by
    rw [← Real.rpow_natCast (η ^ ((1 : ℝ) / (Q : ℝ))) 2, ← Real.rpow_mul hη0.le]
    congr 1
    push_cast
    ring
  have h12 : (1 : ℝ) / (Q : ℝ) ≤ (2 : ℝ) / (Q : ℝ) := by
    have hsplit : (2 : ℝ) / (Q : ℝ) = (1 : ℝ) / (Q : ℝ) + (1 : ℝ) / (Q : ℝ) := by ring
    have hpos : (0 : ℝ) ≤ (1 : ℝ) / (Q : ℝ) := by positivity
    linarith only [hsplit, hpos, hQ0]
  have hηmono : η ^ ((2 : ℝ) / (Q : ℝ)) ≤ η ^ ((1 : ℝ) / (Q : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_ge hη0 hη1.le h12
  exact ⟨hQ0, hZpos, hZsq, hηmono⟩

/-- Finite-window assembly of the cell and averaged recent-defect bounds. -/
private theorem weakSums_squared_integrable_of_scale_bounds (rho : ℝ) (K : ℕ → ℝ)
    (Q : ℕ) (hQ : 1 ≤ Q) (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (q : Mat d) (t : ℤ) (H : ℕ) (E : BlockMat d) (b : CoeffSpace d → CoeffField d)
    (η : ℝ) (hη : η ∈ Set.Ioo (0 : ℝ) (1 / 2))
    (hCellMeas : ∀ n, n ≤ H → AEStronglyMeasurable
      (fun a => weakCellDefect q t n E (b a)) P)
    (hCellInt : ∀ n, n ≤ H → Integrable
      (fun a => weakCellDefect q t n E (b a) ^ 2) P)
    (hCellBound : ∀ n, n ≤ H →
      ∫ a, weakCellDefect q t n E (b a) ^ 2 ∂P ≤ K n * η ^ ((2 : ℝ) / (Q : ℝ)))
    (hAverageMeas : ∀ n, n ≤ H → AEStronglyMeasurable
      (fun a => (((triadicIndexBox d n).card : ℝ)⁻¹ *
        ‖∑ w ∈ triadicIndexBox d n, recentDefectBlock q t n w E (b a)‖)) P)
    (hAverageInt : ∀ n, n ≤ H → Integrable
      (fun a => (((triadicIndexBox d n).card : ℝ)⁻¹ *
        ‖∑ w ∈ triadicIndexBox d n, recentDefectBlock q t n w E (b a)‖)) P)
    (hAverageBound : ∀ n, n ≤ H →
      ∫ a, (((triadicIndexBox d n).card : ℝ)⁻¹ *
        ‖∑ w ∈ triadicIndexBox d n, recentDefectBlock q t n w E (b a)‖) ∂P
        ≤ Real.sqrt (K n) * η ^ ((1 : ℝ) / (Q : ℝ))) :
    Integrable (fun a => (weakCellSum q t H E (b a) +
      weakAverageSum q t H rho E (b a)) ^ 2) P ∧
      ∫ a, (weakCellSum q t H E (b a) + weakAverageSum q t H rho E (b a)) ^ 2 ∂P ≤
        (2 * ((H : ℝ) + 1) * ∑ n ∈ Finset.range (H + 1),
          (((3 : ℝ) ^ (-((n : ℝ) / 2))) ^ 2 * K n +
            ((3 : ℝ) ^ (-((1 / 2 : ℝ) - rho / 2) * (n : ℝ))) ^ 2 * Real.sqrt (K n)) + 1) *
          η ^ ((1 : ℝ) / (Q : ℝ)) := by
  have := ‹IsProbabilityMeasure P›
  set NB : ℕ → ℝ := fun n => ((triadicIndexBox d n).card : ℝ)
  set BB : ℕ → (Fin d → ℤ) → CoeffSpace d →
      Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) ℝ :=
    fun n w a => recentDefectBlock q t n w E (b a)
  have hNBpos : ∀ n, 0 < NB n := by
    intro n
    simp only [NB]
    rw [card_triadicIndexBox]
    positivity
  obtain ⟨_, hZpos, _, hηmono⟩ := etaExponentBounds Q hQ η hη
  have hcd_meas := hCellMeas
  have hcd_int2 := hCellInt
  have hcd_bd := hCellBound
  have hav_meas := hAverageMeas
  have hav_int := hAverageInt
  have hav_bd := hAverageBound
  have hcs_eq : ∀ a, weakCellSum q t H E (b a)
      = ∑ n ∈ Finset.range (H + 1),
          (3 : ℝ) ^ (-((n : ℝ) / 2)) * weakCellDefect q t n E (b a) := fun _ => rfl
  have hav_eq : ∀ n a, Real.sqrt ‖toFullBlockMat (weakAverageDefect q t n E (b a))‖
      = Real.sqrt ((NB n)⁻¹ * ‖∑ w ∈ triadicIndexBox d n, BB n w a‖) := by
    intro n a
    have hinv : (0 : ℝ) ≤ (((triadicIndexBox d n).card : ℝ))⁻¹ := by positivity
    simp only [NB, BB, weakAverageDefect, recentDefectBlock, toFullBlockMat_ofFullBlockMat,
      norm_smul, Real.norm_eq_abs, abs_of_nonneg hinv]
  have has_eq : ∀ a, weakAverageSum q t H rho E (b a)
      = ∑ n ∈ Finset.range (H + 1), (3 : ℝ) ^ (-((1 / 2 : ℝ) - rho / 2) * (n : ℝ))
          * Real.sqrt ((NB n)⁻¹ * ‖∑ w ∈ triadicIndexBox d n, BB n w a‖) := by
    intro a
    simp only [weakAverageSum]
    exact Finset.sum_congr rfl fun n _ => by rw [hav_eq n a]
  have hrangele : ∀ n ∈ Finset.range (H + 1), n ≤ H := fun n hn =>
    Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
  set maj : CoeffSpace d → ℝ := fun a => 2 * ((H : ℝ) + 1) *
      ∑ n ∈ Finset.range (H + 1),
        (((3 : ℝ) ^ (-((n : ℝ) / 2))) ^ 2 * weakCellDefect q t n E (b a) ^ 2
          + ((3 : ℝ) ^ (-((1 / 2 : ℝ) - rho / 2) * (n : ℝ))) ^ 2
              * ((NB n)⁻¹ * ‖∑ w ∈ triadicIndexBox d n, BB n w a‖)) with hmajdef
  have hmaj_int : Integrable maj P := by
    rw [hmajdef]
    refine Integrable.const_mul ?_ _
    refine integrable_finsetSum _ fun n hn => ?_
    exact (Integrable.const_mul (hcd_int2 n (hrangele n hn)) _).add
      (Integrable.const_mul (hav_int n (hrangele n hn)) _)
  have hpt : ∀ a, (weakCellSum q t H E (b a) + weakAverageSum q t H rho E (b a)) ^ 2 ≤ maj a := by
    intro a
    have hA : weakCellSum q t H E (b a) ^ 2
        ≤ ((H : ℝ) + 1) * ∑ n ∈ Finset.range (H + 1),
            ((3 : ℝ) ^ (-((n : ℝ) / 2))) ^ 2 * weakCellDefect q t n E (b a) ^ 2 := by
      rw [hcs_eq]
      have h := _root_.sq_sum_le_card_mul_sum_sq (s := Finset.range (H + 1))
        (f := fun n => (3 : ℝ) ^ (-((n : ℝ) / 2)) * weakCellDefect q t n E (b a))
      simpa [Finset.card_range, mul_pow] using h
    have hB : weakAverageSum q t H rho E (b a) ^ 2
        ≤ ((H : ℝ) + 1) * ∑ n ∈ Finset.range (H + 1),
            ((3 : ℝ) ^ (-((1 / 2 : ℝ) - rho / 2) * (n : ℝ))) ^ 2
              * ((NB n)⁻¹ * ‖∑ w ∈ triadicIndexBox d n, BB n w a‖) := by
      rw [has_eq]
      have h := _root_.sq_sum_le_card_mul_sum_sq (s := Finset.range (H + 1))
        (f := fun n => (3 : ℝ) ^ (-((1 / 2 : ℝ) - rho / 2) * (n : ℝ))
          * Real.sqrt ((NB n)⁻¹ * ‖∑ w ∈ triadicIndexBox d n, BB n w a‖))
      refine h.trans_eq ?_
      rw [Finset.card_range]
      push_cast
      refine congrArg _ (Finset.sum_congr rfl fun n _ => ?_)
      rw [mul_pow, Real.sq_sqrt (mul_nonneg (inv_nonneg.2 (hNBpos n).le) (norm_nonneg _))]
    have hmaj_eq : maj a
        = 2 * (((H : ℝ) + 1) * ∑ n ∈ Finset.range (H + 1),
            ((3 : ℝ) ^ (-((n : ℝ) / 2))) ^ 2 * weakCellDefect q t n E (b a) ^ 2)
          + 2 * (((H : ℝ) + 1) * ∑ n ∈ Finset.range (H + 1),
            ((3 : ℝ) ^ (-((1 / 2 : ℝ) - rho / 2) * (n : ℝ))) ^ 2
              * ((NB n)⁻¹ * ‖∑ w ∈ triadicIndexBox d n, BB n w a‖)) := by
      rw [hmajdef]
      simp only [Finset.sum_add_distrib]
      ring
    have hsq : (weakCellSum q t H E (b a) + weakAverageSum q t H rho E (b a)) ^ 2
        ≤ 2 * weakCellSum q t H E (b a) ^ 2 + 2 * weakAverageSum q t H rho E (b a) ^ 2 := by
      nlinarith only [sq_nonneg (weakCellSum q t H E (b a) - weakAverageSum q t H rho E (b a))]
    rw [hmaj_eq]
    linarith only [hsq, hA, hB]
  have hf_meas : AEStronglyMeasurable
      (fun a => (weakCellSum q t H E (b a) + weakAverageSum q t H rho E (b a)) ^ 2) P := by
    have h1 : AEStronglyMeasurable (fun a => weakCellSum q t H E (b a)) P := by
      simp only [hcs_eq]
      exact Finset.aestronglyMeasurable_fun_sum _ fun n hn =>
        AEStronglyMeasurable.const_mul (hcd_meas n (hrangele n hn)) _
    have h2 : AEStronglyMeasurable (fun a => weakAverageSum q t H rho E (b a)) P := by
      simp only [has_eq]
      refine Finset.aestronglyMeasurable_fun_sum _ fun n hn => ?_
      exact AEStronglyMeasurable.const_mul
        (Real.continuous_sqrt.comp_aestronglyMeasurable (hav_meas n (hrangele n hn))) _
    exact (h1.add h2).pow 2
  have hint_f : Integrable
      (fun a => (weakCellSum q t H E (b a) + weakAverageSum q t H rho E (b a)) ^ 2) P := by
    refine Integrable.mono hmaj_int hf_meas ?_
    filter_upwards with a
    have h0 : (0 : ℝ) ≤ (weakCellSum q t H E (b a) + weakAverageSum q t H rho E (b a)) ^ 2 :=
      sq_nonneg _
    have h1 : 0 ≤ maj a := le_trans h0 (hpt a)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h0, abs_of_nonneg h1]
    exact hpt a
  refine ⟨hint_f, ?_⟩
  have hmaj_val : ∫ a, maj a ∂P = 2 * ((H : ℝ) + 1) *
      ∑ n ∈ Finset.range (H + 1),
        (((3 : ℝ) ^ (-((n : ℝ) / 2))) ^ 2 * ∫ a, weakCellDefect q t n E (b a) ^ 2 ∂P
          + ((3 : ℝ) ^ (-((1 / 2 : ℝ) - rho / 2) * (n : ℝ))) ^ 2
              * ∫ a, (NB n)⁻¹ * ‖∑ w ∈ triadicIndexBox d n, BB n w a‖ ∂P) := by
    rw [hmajdef, integral_const_mul,
      integral_finsetSum (Finset.range (H + 1))
        (f := fun n a => ((3 : ℝ) ^ (-((n : ℝ) / 2))) ^ 2 * weakCellDefect q t n E (b a) ^ 2
          + ((3 : ℝ) ^ (-((1 / 2 : ℝ) - rho / 2) * (n : ℝ))) ^ 2
              * ((NB n)⁻¹ * ‖∑ w ∈ triadicIndexBox d n, BB n w a‖))
        (fun n hn => (Integrable.const_mul (hcd_int2 n (hrangele n hn)) _).add
          (Integrable.const_mul (hav_int n (hrangele n hn)) _))]
    congr 1
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [integral_add (Integrable.const_mul (hcd_int2 n (hrangele n hn)) _)
      (Integrable.const_mul (hav_int n (hrangele n hn)) _), integral_const_mul, integral_const_mul]
  have hterm : ∀ n ∈ Finset.range (H + 1),
      ((3 : ℝ) ^ (-((n : ℝ) / 2))) ^ 2 * ∫ a, weakCellDefect q t n E (b a) ^ 2 ∂P
        + ((3 : ℝ) ^ (-((1 / 2 : ℝ) - rho / 2) * (n : ℝ))) ^ 2
            * ∫ a, (NB n)⁻¹ * ‖∑ w ∈ triadicIndexBox d n, BB n w a‖ ∂P
      ≤ (((3 : ℝ) ^ (-((n : ℝ) / 2))) ^ 2 * K n
          + ((3 : ℝ) ^ (-((1 / 2 : ℝ) - rho / 2) * (n : ℝ))) ^ 2 * Real.sqrt (K n))
        * η ^ ((1 : ℝ) / (Q : ℝ)) := by
    intro n hn
    have hn' := hrangele n hn
    have hKn : 0 ≤ K n := by
      have hz : 0 < η ^ ((2 : ℝ) / (Q : ℝ)) := Real.rpow_pos_of_pos hη.1 _
      exact nonneg_of_mul_nonneg_left
        ((integral_nonneg fun a => sq_nonneg (weakCellDefect q t n E (b a))).trans
          (hcd_bd n hn')) hz
    have t1 : ∫ a, weakCellDefect q t n E (b a) ^ 2 ∂P ≤ K n * η ^ ((1 : ℝ) / (Q : ℝ)) :=
      le_trans (hcd_bd n hn') (mul_le_mul_of_nonneg_left hηmono hKn)
    have t2 : ∫ a, (NB n)⁻¹ * ‖∑ w ∈ triadicIndexBox d n, BB n w a‖ ∂P
        ≤ Real.sqrt (K n) * η ^ ((1 : ℝ) / (Q : ℝ)) := hav_bd n hn'
    have hA := mul_le_mul_of_nonneg_left t1 (sq_nonneg ((3 : ℝ) ^ (-((n : ℝ) / 2))))
    have hB := mul_le_mul_of_nonneg_left t2
      (sq_nonneg ((3 : ℝ) ^ (-((1 / 2 : ℝ) - rho / 2) * (n : ℝ))))
    nlinarith only [hA, hB]
  calc ∫ a, (weakCellSum q t H E (b a) + weakAverageSum q t H rho E (b a)) ^ 2 ∂P
      ≤ ∫ a, maj a ∂P := integral_mono hint_f hmaj_int hpt
    _ = 2 * ((H : ℝ) + 1) * ∑ n ∈ Finset.range (H + 1),
          (((3 : ℝ) ^ (-((n : ℝ) / 2))) ^ 2 * ∫ a, weakCellDefect q t n E (b a) ^ 2 ∂P
            + ((3 : ℝ) ^ (-((1 / 2 : ℝ) - rho / 2) * (n : ℝ))) ^ 2
                * ∫ a, (NB n)⁻¹ * ‖∑ w ∈ triadicIndexBox d n, BB n w a‖ ∂P) := hmaj_val
    _ ≤ 2 * ((H : ℝ) + 1) * ∑ n ∈ Finset.range (H + 1),
          ((((3 : ℝ) ^ (-((n : ℝ) / 2))) ^ 2 * K n
            + ((3 : ℝ) ^ (-((1 / 2 : ℝ) - rho / 2) * (n : ℝ))) ^ 2 * Real.sqrt (K n))
            * η ^ ((1 : ℝ) / (Q : ℝ))) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) (by positivity)
    _ = (2 * ((H : ℝ) + 1) * ∑ n ∈ Finset.range (H + 1),
          (((3 : ℝ) ^ (-((n : ℝ) / 2))) ^ 2 * K n
            + ((3 : ℝ) ^ (-((1 / 2 : ℝ) - rho / 2) * (n : ℝ))) ^ 2 * Real.sqrt (K n)))
          * η ^ ((1 : ℝ) / (Q : ℝ)) := by
        rw [← Finset.sum_mul]
        ring
    _ ≤ (2 * ((H : ℝ) + 1) * ∑ n ∈ Finset.range (H + 1),
          (((3 : ℝ) ^ (-((n : ℝ) / 2))) ^ 2 * K n
            + ((3 : ℝ) ^ (-((1 / 2 : ℝ) - rho / 2) * (n : ℝ))) ^ 2 * Real.sqrt (K n)) + 1)
          * η ^ ((1 : ℝ) / (Q : ℝ)) := by
        nlinarith only [hZpos]

/-- **Bookkeeping from the η-kernel to the squared recent sums** (`p.response.transfer`, finite
window
`n ≤ H`): `(S_cell + S_av)^2 ≤ 2S_cell^2 + 2S_av^2`; Cauchy–Schwarz on the finite sums;
`S_cell`: `∫ weakCellDefect^2 = avg_w ∫ ‖D_{n,w}‖^2 ≤ K_n η^{2/Q} ≤ K_n η^{1/Q}` (`η < 1`);
`S_av`: `‖avg_w D‖ ≤ avg_w ‖D‖ ≤ (avg_w ‖D‖^2)^{1/2}` (`ofFullBlockMat`/`toFullBlockMat` inverse,
norm of a mean) and `∫ √f ≤ (∫ f)^{1/2}` on a probability measure, giving `√K_n η^{1/Q}`.
`D H = 2(H+1) ∑_{n ≤ H} (K n + √(K n)) + 1` works. -/
theorem integral_weakSums_sq_le (rho : ℝ) (hrho : 0 ≤ rho) (K : ℕ → ℝ) (hK : ∀ n, 0 < K n)
    (Q : ℕ) (hQ : 1 ≤ Q) :
    ∃ D : ℕ → ℝ, (∀ H, 0 < D H) ∧
      ∀ (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (q : Mat d) (t : ℤ) (H : ℕ)
        (E : BlockMat d) (b : CoeffSpace d → CoeffField d) (η : ℝ),
        η ∈ Set.Ioo (0 : ℝ) (1 / 2) →
        (∀ n, n ≤ H → ∀ w ∈ triadicIndexBox d n,
          AEStronglyMeasurable (fun a => recentDefectBlock q t n w E (b a)) P ∧
          Integrable (fun a => recentDefect q t n w E (b a) ^ 2) P ∧
          ∫ a, recentDefect q t n w E (b a) ^ 2 ∂P ≤ K n * η ^ ((2 : ℝ) / (Q : ℝ))) →
        Integrable (fun a => (weakCellSum q t H E (b a) + weakAverageSum q t H rho E (b a)) ^ 2) P ∧
        ∫ a, (weakCellSum q t H E (b a) + weakAverageSum q t H rho E (b a)) ^ 2 ∂P ≤
          D H * η ^ ((1 : ℝ) / (Q : ℝ)) := by
  classical
  have _hrho : (0 : ℝ) ≤ rho := hrho
  refine ⟨fun H => 2 * ((H : ℝ) + 1) * ∑ n ∈ Finset.range (H + 1),
      (((3 : ℝ) ^ (-((n : ℝ) / 2))) ^ 2 * K n +
        ((3 : ℝ) ^ (-((1 / 2 : ℝ) - rho / 2) * (n : ℝ))) ^ 2 * Real.sqrt (K n)) + 1, ?_, ?_⟩
  · intro H
    have hs : (0 : ℝ) ≤ ∑ n ∈ Finset.range (H + 1),
        (((3 : ℝ) ^ (-((n : ℝ) / 2))) ^ 2 * K n +
          ((3 : ℝ) ^ (-((1 / 2 : ℝ) - rho / 2) * (n : ℝ))) ^ 2 * Real.sqrt (K n)) := by
      exact Finset.sum_nonneg fun n _ =>
        add_nonneg (mul_nonneg (sq_nonneg _) (hK n).le)
          (mul_nonneg (sq_nonneg _) (Real.sqrt_nonneg _))
    have hf : (0 : ℝ) ≤ 2 * ((H : ℝ) + 1) := by positivity
    have := mul_nonneg hf hs
    linarith only [this]
  · intro P _inst q t H E b η hη hbound
    set NB : ℕ → ℝ := fun n => ((triadicIndexBox d n).card : ℝ) with hNB
    set BB : ℕ → (Fin d → ℤ) → CoeffSpace d →
        Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) ℝ :=
      fun n w a => recentDefectBlock q t n w E (b a) with hBB
    set DD : ℕ → (Fin d → ℤ) → CoeffSpace d → ℝ :=
      fun n w a => recentDefect q t n w E (b a) with hDD
    have hNBpos : ∀ n, 0 < NB n := by
      intro n
      change (0 : ℝ) < ((triadicIndexBox d n).card : ℝ)
      rw [card_triadicIndexBox]
      positivity
    have hDDeq : ∀ n w a, DD n w a = ‖BB n w a‖ := fun _ _ _ => rfl
    have hDDnn : ∀ n w a, 0 ≤ DD n w a := fun _ _ _ => norm_nonneg _
    have hmeas : ∀ n, n ≤ H → ∀ w ∈ triadicIndexBox d n,
        AEStronglyMeasurable (fun a => BB n w a) P := by
      intro n hn w hw
      exact (hbound n hn w hw).1
    have hint2 : ∀ n, n ≤ H → ∀ w ∈ triadicIndexBox d n,
        Integrable (fun a => DD n w a ^ 2) P := by
      intro n hn w hw
      exact (hbound n hn w hw).2.1
    have hbd2 : ∀ n, n ≤ H → ∀ w ∈ triadicIndexBox d n,
        ∫ a, DD n w a ^ 2 ∂P ≤ K n * η ^ ((2 : ℝ) / (Q : ℝ)) := by
      intro n hn w hw
      exact (hbound n hn w hw).2.2
    have hDmeas : ∀ n, n ≤ H → ∀ w ∈ triadicIndexBox d n,
        AEStronglyMeasurable (fun a => DD n w a) P :=
      fun n hn w hw => (hmeas n hn w hw).norm
    have hDint : ∀ n, n ≤ H → ∀ w ∈ triadicIndexBox d n,
        Integrable (fun a => DD n w a) P := by
      intro n hn w hw
      exact ((memLp_two_iff_integrable_sq (hDmeas n hn w hw)).2
        (hint2 n hn w hw)).integrable (by norm_num)
    obtain ⟨hQ0, hZpos, hZsq, hηmono⟩ := etaExponentBounds Q hQ η hη
    -- ## the recent-cell defect
    have hcd_eq : ∀ n a, weakCellDefect q t n E (b a)
        = Real.sqrt ((NB n)⁻¹ * ∑ w ∈ triadicIndexBox d n, DD n w a ^ 2) := by
      intro n a
      simp only [hNB, hDD, weakCellDefect, recentDefect, recentDefectBlock]
    have hcd_sq : ∀ n a, weakCellDefect q t n E (b a) ^ 2
        = (NB n)⁻¹ * ∑ w ∈ triadicIndexBox d n, DD n w a ^ 2 := by
      intro n a
      rw [hcd_eq]
      exact Real.sq_sqrt (mul_nonneg (inv_nonneg.2 (hNBpos n).le)
        (Finset.sum_nonneg fun w _ => sq_nonneg _))
    have hcd_meas : ∀ n, n ≤ H →
        AEStronglyMeasurable (fun a => weakCellDefect q t n E (b a)) P := by
      intro n hn
      have h1 : AEStronglyMeasurable
          (fun a => (NB n)⁻¹ * ∑ w ∈ triadicIndexBox d n, DD n w a ^ 2) P :=
        AEStronglyMeasurable.const_mul
          (Finset.aestronglyMeasurable_fun_sum _ fun w hw => (hDmeas n hn w hw).pow 2) _
      simpa only [hcd_eq] using Real.continuous_sqrt.comp_aestronglyMeasurable h1
    have hcd_int2 : ∀ n, n ≤ H → Integrable (fun a => weakCellDefect q t n E (b a) ^ 2) P := by
      intro n hn
      have h1 : Integrable (fun a => (NB n)⁻¹ * ∑ w ∈ triadicIndexBox d n, DD n w a ^ 2) P :=
        Integrable.const_mul (integrable_finsetSum _ fun w hw => hint2 n hn w hw) _
      exact h1.congr (Filter.Eventually.of_forall fun a => (hcd_sq n a).symm)
    have hcd_bd : ∀ n, n ≤ H →
        ∫ a, weakCellDefect q t n E (b a) ^ 2 ∂P ≤ K n * η ^ ((2 : ℝ) / (Q : ℝ)) := by
      intro n hn
      have heq : ∫ a, weakCellDefect q t n E (b a) ^ 2 ∂P
          = (NB n)⁻¹ * ∑ w ∈ triadicIndexBox d n, ∫ a, DD n w a ^ 2 ∂P := by
        simp only [hcd_sq]
        rw [integral_const_mul, integral_finsetSum _ fun w hw => hint2 n hn w hw]
      rw [heq]
      have hsum : ∑ w ∈ triadicIndexBox d n, ∫ a, DD n w a ^ 2 ∂P
          ≤ NB n * (K n * η ^ ((2 : ℝ) / (Q : ℝ))) := by
        have h := Finset.sum_le_sum fun w hw => hbd2 n hn w hw
        simpa [hNB, Finset.sum_const, nsmul_eq_mul] using h
      calc (NB n)⁻¹ * ∑ w ∈ triadicIndexBox d n, ∫ a, DD n w a ^ 2 ∂P
          ≤ (NB n)⁻¹ * (NB n * (K n * η ^ ((2 : ℝ) / (Q : ℝ)))) :=
            mul_le_mul_of_nonneg_left hsum (inv_nonneg.2 (hNBpos n).le)
        _ = K n * η ^ ((2 : ℝ) / (Q : ℝ)) := by
            have hne : NB n ≠ 0 := (hNBpos n).ne'
            field_simp
    -- ## the recent averaged defect
    have hav_eq : ∀ n a, Real.sqrt ‖toFullBlockMat (weakAverageDefect q t n E (b a))‖
        = Real.sqrt ((NB n)⁻¹ * ‖∑ w ∈ triadicIndexBox d n, BB n w a‖) := by
      intro n a
      have hinv : (0 : ℝ) ≤ (((triadicIndexBox d n).card : ℝ))⁻¹ := by positivity
      simp only [hNB, hBB, weakAverageDefect, recentDefectBlock, toFullBlockMat_ofFullBlockMat,
        norm_smul, Real.norm_eq_abs, abs_of_nonneg hinv]
    have hav_le : ∀ n a, (NB n)⁻¹ * ‖∑ w ∈ triadicIndexBox d n, BB n w a‖
        ≤ (NB n)⁻¹ * ∑ w ∈ triadicIndexBox d n, DD n w a := by
      intro n a
      refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 (hNBpos n).le)
      exact (norm_sum_le _ _).trans_eq (by simp only [hDDeq])
    have hav_meas : ∀ n, n ≤ H →
        AEStronglyMeasurable (fun a => (NB n)⁻¹ * ‖∑ w ∈ triadicIndexBox d n, BB n w a‖) P := by
      intro n hn
      have h1 : AEStronglyMeasurable (fun a => ∑ w ∈ triadicIndexBox d n, BB n w a) P :=
        Finset.aestronglyMeasurable_fun_sum _ fun w hw => hmeas n hn w hw
      exact AEStronglyMeasurable.const_mul h1.norm _
    have hav_int : ∀ n, n ≤ H →
        Integrable (fun a => (NB n)⁻¹ * ‖∑ w ∈ triadicIndexBox d n, BB n w a‖) P := by
      intro n hn
      refine Integrable.mono
        (Integrable.const_mul (integrable_finsetSum _ fun w hw => hDint n hn w hw) (NB n)⁻¹)
        (hav_meas n hn) ?_
      filter_upwards with a
      have hnn : 0 ≤ (NB n)⁻¹ * ∑ w ∈ triadicIndexBox d n, DD n w a :=
        mul_nonneg (inv_nonneg.2 (hNBpos n).le) (Finset.sum_nonneg fun w _ => hDDnn n w a)
      have hnn2 : 0 ≤ (NB n)⁻¹ * ‖∑ w ∈ triadicIndexBox d n, BB n w a‖ :=
        mul_nonneg (inv_nonneg.2 (hNBpos n).le) (norm_nonneg _)
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hnn2, abs_of_nonneg hnn]
      exact hav_le n a
    have hav_bd : ∀ n, n ≤ H →
        ∫ a, (NB n)⁻¹ * ‖∑ w ∈ triadicIndexBox d n, BB n w a‖ ∂P
          ≤ Real.sqrt (K n) * η ^ ((1 : ℝ) / (Q : ℝ)) := by
      intro n hn
      have hc : 0 < Real.sqrt (K n) * η ^ ((1 : ℝ) / (Q : ℝ)) :=
        mul_pos (Real.sqrt_pos.2 (hK n)) hZpos
      have hcsq : (Real.sqrt (K n) * η ^ ((1 : ℝ) / (Q : ℝ))) ^ 2 = K n * η ^ ((2 : ℝ) / (Q : ℝ))
        := by
        rw [mul_pow, Real.sq_sqrt (hK n).le, hZsq]
      have hDbd : ∀ w ∈ triadicIndexBox d n,
          ∫ a, DD n w a ∂P ≤ Real.sqrt (K n) * η ^ ((1 : ℝ) / (Q : ℝ)) := by
        intro w hw
        refine integral_le_of_sq_le P (fun a => DD n w a) (hDint n hn w hw)
          (hint2 n hn w hw) _ hc ?_
        rw [hcsq]
        exact hbd2 n hn w hw
      calc ∫ a, (NB n)⁻¹ * ‖∑ w ∈ triadicIndexBox d n, BB n w a‖ ∂P
          ≤ ∫ a, (NB n)⁻¹ * ∑ w ∈ triadicIndexBox d n, DD n w a ∂P :=
            integral_mono (hav_int n hn)
              (Integrable.const_mul (integrable_finsetSum _ fun w hw => hDint n hn w hw) _)
              (fun a => hav_le n a)
        _ = (NB n)⁻¹ * ∑ w ∈ triadicIndexBox d n, ∫ a, DD n w a ∂P := by
            rw [integral_const_mul, integral_finsetSum _ fun w hw => hDint n hn w hw]
        _ ≤ (NB n)⁻¹ * (NB n * (Real.sqrt (K n) * η ^ ((1 : ℝ) / (Q : ℝ)))) := by
            refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 (hNBpos n).le)
            have h := Finset.sum_le_sum hDbd
            simpa [hNB, Finset.sum_const, nsmul_eq_mul] using h
        _ = Real.sqrt (K n) * η ^ ((1 : ℝ) / (Q : ℝ)) := by
            have hne : NB n ≠ 0 := (hNBpos n).ne'
            field_simp
    exact weakSums_squared_integrable_of_scale_bounds rho K Q hQ P q t H E b η hη
      hcd_meas hcd_int2 hcd_bd hav_meas hav_int hav_bd

end

end HCPolySupport.HighContrast.Multiscale
end
