/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.DepthZeroEnergyExtraction

/-!
# High-contrast homogenization: Entry.Response.Kernel.RecentCellDefectBound

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Measurability and the recent-cell defect bound

Under `RawOutput`, the all-scale maximum `respAllScaleMax` - a countable supremum over
coarse-block quantities, each measurable through the integrable-coarse-block fields of
`RawOutput` - is `AEStronglyMeasurable` and `L^Q`-integrable (`p.response.transfer`). Because
`respAllScaleMax` is built from the one-sided spectral positive part and so majorizes the
recent-cell defect only from above, a bound at the sharp exponent `η^{2/Q}` cannot follow from it
alone; this file records that obstruction and develops the two-sided quantity `respAllScaleAbs`
in its place, together with the measurability of the recent-defect block for both signs and the
resulting one-sided bound `‖normalizedBlock‖ ≤ (weight) · respAllScaleAbs` the genuine two-sided
estimate is built from.
-/

section
open HCPolySupport.HighContrast (CoeffSpace aspectRatio)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator
open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ}
/-- **Measurability and `L^Q`-integrability of `M` under `RawOutput`**.  NOTE: the
hypothesis `∫ M^Q ∂P ≤ C_m η` is a Bochner integral with no integrability side condition, so this
is genuinely needed to use it (else the integral is the junk `0`).  `M` is an `sSup` over the
countable family `(n, z)`, each term measurable in `a` through the coarse blocks (`RawOutput`
integrable-coarse-block fields); the bound comes from a.e. ellipticity.

FIRST CONJUNCT: proved by
`respAllScaleMax_measurable` above — the countable-`sSup` route, with `blockSpecBound` shown
continuous by an attained-infimum/Lipschitz argument that needs no semidefiniteness of its
(indefinite) argument `normalizedBlock A E_t − I`.

SECOND CONJUNCT: not derivable from the statement's previous binder set, in which `Csrc` was
universally quantified: every route to an integrable majorant for `M^Q` goes through the
deep scales `k < j_*`, and the only tools for those are
`Source.source_multiplier_and_adapted_bound` (`AdaptedBound.lean`) and
`Annealed.adaptedMean_refBlock_normalization` (`ReferenceNormalization.lean`), each of which
*produces* a positive `Csrc_i` and demands the threshold `⌈Csrc_i · logb 3 (2 K)⌉ ≤ j_*`.
`RawOutput.hsrc` supplies that threshold only for the `Csrc` of the binder, which under a `∀`
may be zero or negative, and `RawOutput.hj` gives only `2d ≤ 3^{j_*}`.  Three premises are
therefore carried, each of them forced and each of them already carried by the all-scale
maximum bound, whose machinery this proof reuses:

* `Csrc` is **produced** (`∃ Csrc, 0 < Csrc ∧ …`) rather than taken, exactly as
  `Source.source_multiplier` and every other Source consumer in the tree produces it.  The
  assembly consuming this statement reconciles its `Csrc` with that of the all-scale maximum
  bound and with those of the other estimates it combines by the tree's own `max`-ing idiom
  (`HCPoly/Entry/OneGridPropagation.lean`).
* `ε ∈ Ioc 0 S.eps0` and `σ ∈ Ioc 0 ε`: `SelectionData.one_le_B0` holds only on
  that range, and without it `respAllScale_window`'s `j_* < t` — needed even on the fluctuation
  side — is unavailable.
* `0 ≤ Cglob`: needed to drop the first summand of `raw.hsrc` when specialising
  it to the source threshold.

The strengthened statement's satisfiability is exhibited inside the proof itself —
the `∃ Csrc` witness is `max Csrc₁ Csrc₂ > 0`, and the source-smallness pair is chosen here as
`Cs := 1`, `η := (1 + Y)^Q`, so that the `RespSourceSmall` inequality holds **by construction**
(`Y ≤ 1 + Y`).  No `RespSourceSmall` premise and no `η ∈ Ioo 0 (1/2)` premise is added:
integrability, unlike the quantitative bound `∫ M^Q ≤ C η`, does not care about the constant.  No
new
constraint is placed on `SelectionData` or on `Selects`, so no separate selection-satisfiability
obligation arises.

The helpers this proof needs are public declarations of
`HCPoly/Entry/Response/Core/EnergyDefectBound.lean` (`respAllScale_window`) and of
`HCPoly/Entry/Response/Core/PathwiseFluctuationBound.lean` (`add3_pow_le` and `pathwise_bound_max`),
with no statement and no proof changed.  `fluctuation_term_le_max` and `source_term_le_max` stay
`private` in `HCPoly/Entry/Response/Core/PathwiseFluctuationBound.lean`; `scale_index_le` and
`respAllScaleMax_le_of_forall` are public in `HCPoly/Entry/Response/Core/EnergyDefectBound.lean`.
`respAllScaleMax_nonneg` is public in
`HCPoly/Entry/Response/Kernel/DepthZeroEnergyExtraction.lean`, which this file imports, and it is
the one used here. -/
theorem respAllScaleMax_aestronglyMeasurable_integrable (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1) (S : SelectionData) (_hS : S.Selects d γ) :
    ∃ Csrc : ℝ, 0 < Csrc ∧
      ∀ (ε σ : ℝ), ε ∈ Set.Ioc (0 : ℝ) S.eps0 → σ ∈ Set.Ioc (0 : ℝ) ε →
        ∀ (Cglob Cprof Bresp : ℝ), 0 ≤ Cglob →
          ∀ (H : ℕ) (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (Kg : ℝ)
            (Src : CoeffSpace d → ℝ) (B : ℝ) (jStar : ℕ) (F : BlockMat d) (s t : ℤ),
            RawOutput d γ S ε σ Cglob Cprof Csrc H Bresp P E Ψ Kg Src B jStar F s t →
            AEStronglyMeasurable (respAllScaleMax P γ jStar F t) P ∧
              Integrable (fun a => respAllScaleMax P γ jStar F t a ^ bigQ d γ) P := by
  obtain ⟨Csrc₁, C₀, hCsrc₁, hC₀, hsrcm⟩ :=
    Source.source_multiplier_and_adapted_bound d hd γ hγ
  obtain ⟨Csrc₂, Cn, hCsrc₂, hCn, hrefn⟩ :=
    Annealed.adaptedMean_refBlock_normalization d hd γ hγ
  refine ⟨max Csrc₁ Csrc₂, lt_max_of_lt_left hCsrc₁, ?_⟩
  intro ε σ hε hσ Cglob Cprof Bresp hCglob H P E Ψ Kg Src B jStar F s t raw
  let : NeZero d := ⟨by omega⟩
  have := raw.prob
  have hm : (explicitCanonicalMetric F).PosDef := Geometry.explicitCanonicalMetric_posDef raw.symm raw.pos
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid raw.hj hm
  have hMmeas : Measurable (respAllScaleMax P γ jStar F t) :=
    respAllScaleMax_measurable P γ jStar F hq t
  refine ⟨hMmeas.aestronglyMeasurable, ?_⟩
  have hQ2 : 2 ≤ bigQ d γ := bigQ_two_le d γ hγ
  have hQ0 : bigQ d γ ≠ 0 := by omega
  have hwin := respAllScale_window d hd γ S ε σ Cglob Cprof (max Csrc₁ Csrc₂) Bresp H P E Ψ Kg
    Src B jStar F s t hε hσ raw
  have hjt : (jStar : ℤ) ≤ t := le_of_lt hwin.2
  have hB0 : (1 : ℝ) ≤ S.B0 ε σ := S.one_le_B0 ε σ hε hσ
  have hB : (1 : ℝ) ≤ B := hB0.trans ((le_max_left _ _).trans raw.hB)
  have hA1 : (1 : ℝ) ≤ aspectRatio E := HCPolySupport.HighContrast.one_le_aspectRatio_of_coarseEllipticityDagger raw.ell
  have hlog : (1 : ℝ) ≤ Real.logb 3 (2 + aspectRatio E) := by
    have hl3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
    have h2 : Real.log 3 ≤ Real.log (2 + aspectRatio E) :=
      Real.log_le_log (by norm_num) (by linarith only [hA1])
    rw [Real.logb, le_div_iff₀ hl3]
    linarith only [h2]
  have hlogK : (0 : ℝ) ≤ Real.logb 3 (2 * Kg) :=
    Real.logb_nonneg (by norm_num) (by linarith only [raw.ell.one_lt_growthWitness])
  have hthr : ∀ c : ℝ, c ≤ max Csrc₁ Csrc₂ → ⌈c * Real.logb 3 (2 * Kg)⌉ ≤ (jStar : ℤ) := by
    intro c hc
    refine le_trans (Int.ceil_mono ?_) raw.hsrc
    have h1 : c * Real.logb 3 (2 * Kg) ≤ max Csrc₁ Csrc₂ * Real.logb 3 (2 * Kg) :=
      mul_le_mul_of_nonneg_right hc hlogK
    have h2 : (0 : ℝ) ≤ Cglob * (B + 1) * Real.logb 3 (2 + aspectRatio E) :=
      mul_nonneg (mul_nonneg hCglob (by linarith only [hB])) (by linarith only [hlog])
    linarith only [h1, h2]
  obtain ⟨ell, X, hell, hXm, hform, hmin, hlp, hXint, hXmom, hXnorm, hpath⟩ :=
    hsrcm P E Ψ Kg Src raw.stat raw.ell jStar raw.hj (hthr Csrc₁ (le_max_left _ _))
  have hnormt := (hrefn P E Ψ Kg Src raw.stat raw.ell jStar raw.hj
    (hthr Csrc₂ (le_max_right _ _)) (explicitCanonicalMetric F) hm t hjt raw.cube).2
  have hX0 : ∀ a, (0 : ℝ) < X a := fun a => by rw [hform]; positivity
  obtain ⟨hfint, -⟩ := oneGrid_fluctuation_integrable_dominate d hd γ P E Ψ Kg Src raw.stat
    raw.ell jStar raw.hj (explicitCanonicalMetric F) hm t
  set F0 : CoeffSpace d → ℝ := fun a => ⨆ j ∈ Set.Icc (jStar : ℤ) t,
    (3 : ℝ) ^ (-(bigQ d γ : ℝ) * rhoMax d γ * ((t : ℝ) - (j : ℝ))) *
      ⨆ z ∈ adaptedLatticeAtScale (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) j ∩
          HighContrast.adaptedCell (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) t,
        blockOpNorm (normalizedFluctuation P (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F))
          j t z a) ^ bigQ d γ with hF0def
  have hF00 : ∀ a, (0 : ℝ) ≤ F0 a := fun a =>
    Real.iSup_nonneg fun j => Real.iSup_nonneg fun _ =>
      mul_nonneg (Real.rpow_nonneg (by norm_num) _)
        (Real.iSup_nonneg fun z => Real.iSup_nonneg fun _ => pow_nonneg (norm_nonneg _) _)
  have hDr0 : (0 : ℝ) ≤ determinantDrift P γ
      (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) jStar t :=
    determinantDrift_nonneg d hd γ P E Ψ Kg Src raw.prob raw.stat raw.unit raw.ell
      jStar raw.hj (explicitCanonicalMetric F) hm t
  -- The choice of the source-smallness pair `(Cs, η)`: only positivity and the one inequality
  -- of `pathwise_bound_max` are needed, so take `Cs = 1` and `η = (1 + Y)^Q`.
  -- This is the explicit witness making the strengthened statement satisfiable.
  set Y : ℝ := aspectRatio E * (‖explicitCanonicalMetric F‖ * ‖(explicitCanonicalMetric F)⁻¹‖) *
    (3 : ℝ) ^ (-(rhoMax d γ * ((t : ℝ) - (jStar : ℝ)))) with hYdef
  have hPi : (0 : ℝ) < aspectRatio E := (Annealed.aspectRatio_pos_and_three_le raw.ell).1
  have hY0 : (0 : ℝ) ≤ Y := by
    rw [hYdef]; positivity
  set η : ℝ := (1 + Y) ^ bigQ d γ with hηdef
  have hη : (0 : ℝ) < η := by rw [hηdef]; exact pow_pos (by linarith only [hY0]) _
  have hηroot : η ^ ((1 : ℝ) / (bigQ d γ : ℝ)) = 1 + Y := by
    rw [hηdef, one_div]
    exact Real.pow_rpow_inv_natCast (by linarith only [hY0]) hQ0
  have hsrcsmall : (1 : ℝ) * aspectRatio E * (‖explicitCanonicalMetric F‖ * ‖(explicitCanonicalMetric F)⁻¹‖) *
      (3 : ℝ) ^ (-(rhoMax d γ * ((t : ℝ) - (jStar : ℝ)))) ≤
      η ^ ((1 : ℝ) / (bigQ d γ : ℝ)) := by
    rw [hηroot, one_mul, ← hYdef]
    linarith only []
  set Kw : ℝ := C₀ * Cn / 1 with hKwdef
  have hKw : (0 : ℝ) < Kw := by rw [hKwdef]; positivity
  have hkey : ∀ᵐ a ∂P, respAllScaleMax P γ jStar F t a ^ bigQ d γ ≤
      (3 : ℝ) ^ bigQ d γ * (F0 a +
        (determinantDrift P γ (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) jStar t) ^
          bigQ d γ + (Kw * (1 + Y)) ^ bigQ d γ * X a ^ bigQ d γ) := by
    filter_upwards [hpath] with a ha
    have hu0 : (0 : ℝ) ≤ F0 a ^ ((bigQ d γ : ℝ)⁻¹) := Real.rpow_nonneg (hF00 a) _
    have hw0 : (0 : ℝ) ≤ Kw * η ^ ((1 : ℝ) / (bigQ d γ : ℝ)) * X a :=
      mul_nonneg (mul_nonneg hKw.le (Real.rpow_nonneg hη.le _)) (hX0 a).le
    have hMle : respAllScaleMax P γ jStar F t a ≤
        F0 a ^ ((bigQ d γ : ℝ)⁻¹) +
          determinantDrift P γ (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) jStar t +
          Kw * η ^ ((1 : ℝ) / (bigQ d γ : ℝ)) * X a :=
      pathwise_bound_max d hd γ hγ P E Ψ Kg Src raw.stat raw.unit raw.ell jStar raw.hj F hm
        t hjt raw.cube C₀ Cn 1 η hC₀ hCn one_pos hη X a (hX0 a) ha.2 hnormt hsrcsmall
    calc respAllScaleMax P γ jStar F t a ^ bigQ d γ
        ≤ (F0 a ^ ((bigQ d γ : ℝ)⁻¹) +
            determinantDrift P γ (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) jStar t +
            Kw * η ^ ((1 : ℝ) / (bigQ d γ : ℝ)) * X a) ^ bigQ d γ :=
          pow_le_pow_left₀ (respAllScaleMax_nonneg P γ jStar F t a) hMle _
      _ ≤ (3 : ℝ) ^ bigQ d γ * ((F0 a ^ ((bigQ d γ : ℝ)⁻¹)) ^ bigQ d γ +
            (determinantDrift P γ (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F))
              jStar t) ^ bigQ d γ +
            (Kw * η ^ ((1 : ℝ) / (bigQ d γ : ℝ)) * X a) ^ bigQ d γ) :=
          add3_pow_le _ _ _ _ hu0 hDr0 hw0
      _ = (3 : ℝ) ^ bigQ d γ * (F0 a +
            (determinantDrift P γ (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F))
              jStar t) ^ bigQ d γ + (Kw * (1 + Y)) ^ bigQ d γ * X a ^ bigQ d γ) := by
          rw [Real.rpow_inv_natCast_pow (hF00 a) hQ0, hηroot, mul_pow]
  have hi1 : Integrable (fun a => F0 a +
      (determinantDrift P γ (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) jStar t) ^
        bigQ d γ) P := hfint.add (integrable_const _)
  have hi2 : Integrable (fun a => (Kw * (1 + Y)) ^ bigQ d γ * X a ^ bigQ d γ) P :=
    hXint.const_mul _
  have hgint : Integrable (fun a => (3 : ℝ) ^ bigQ d γ * (F0 a +
      (determinantDrift P γ (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) jStar t) ^
        bigQ d γ + (Kw * (1 + Y)) ^ bigQ d γ * X a ^ bigQ d γ)) P :=
    (hi1.add hi2).const_mul _
  refine hgint.mono' ((hMmeas.pow_const _).aestronglyMeasurable) ?_
  filter_upwards [hkey] with a ha
  rw [Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg (respAllScaleMax_nonneg P γ jStar F t a) _)]
  exact ha

end

end HCPolySupport.HighContrast.Multiscale
end

section
open HCPolySupport.HighContrast.CG

open HCPolySupport.HighContrast (CoeffSpace adaptedCellCenter blockScale blockSub coarseBlock
  isSymmetricBlockMat_coarseBlockMatrix matSqrt matSqrt_spec normalizedBlock)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator
open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ}

/-! ## The recent-cell differences (`p.response.transfer`) -/

/-! ### The η-kernel's hypothesis is one-sided.

`respAllScaleMax` is built from `blockSpecBound`, i.e. from the *spectral positive part*
`|(E_t^{-1/2}A_k(z)E_t^{-1/2} - I)_+|` of the paper (`p.response.transfer`).  It
therefore majorizes the recent-cell defect only from ABOVE.  The conclusion of the η-kernel asks for
`∫ ‖D_{n,w}‖^2 ≤ K_n η^{2/Q}` from `∫ M^Q ≤ C_m η` alone; the theorem below shows that this
implication is FALSE, and that the reachable exponent from a one-sided majorant is `η^{1/Q}`,
not `η^{2/Q}`.

The paper does not claim otherwise: at `p.response.transfer` the recent cell differences
`V_{k,t}(z) - V_t + (P_{k,t} - I)` are bounded in `L^2` by `C_H η^{1/Q}` using **the fluctuation
history** (two-sided, `fluctuationHistory`) for the first two terms and **the mean history**
(`meanPenalty_Q(P_{k,t}) ≤ 3^{α(t-1-k)}η`) for the third.  Neither carrier is present in the
hypotheses of `integral_recentDefect_sq_le_minus/plus`. -/

/-! ### Local helpers for the η-kernel

These close the FIRST conjunct (`AEStronglyMeasurable`) of both η-kernel twins, and are
independent of the `η` exponent.

`isOpenBoundedConvexDomain_adaptedCellAtCenter` and `volume_adaptedCellAtCenter_toReal_pos`
are `private` in `DiagonalDefectCarriers.lean`), which IS in this
file's import closure.  The two proofs are three lines each over public CoarseGraining lemmas,
so they are restated here with citations. -/

/-- `HasQuadraticMu` on every ALIGNED adapted cell. -/
theorem hasQuadraticMu_adaptedCellAtCenter [NeZero d] (q : Mat d) (hq : IsUnit q) (j : ℤ)
    (w : Fin d → ℤ) (a : CoeffSpace d) :
    HasQuadraticMu (adaptedCellAtCenter q j w) (⇑a.1 : CoeffField d) := by
  obtain ⟨lam, Lam, f, _, _, hEll, hae⟩ :=
    Annealed.exists_elliptic_representative_adapted q hq j (adaptedCellCenter q j w) a
  have hConv : IsOpenBoundedConvexDomain (adaptedCellAtCenter q j w) :=
    isOpenBoundedConvexDomain_adaptedCellAtCenter q hq j w
  let : IsFiniteMeasure (volumeMeasureOn (adaptedCellAtCenter q j w)) :=
    hConv.isFiniteMeasure_restrict_volume
  have hvol : 0 < (volume (adaptedCellAtCenter q j w)).toReal :=
    volume_adaptedCellAtCenter_toReal_pos q hq j w
  obtain ⟨R, ⟨compat⟩⟩ :=
    exists_recovery_compatibility_of_isOpenBoundedConvexDomain hConv hEll hvol
  obtain ⟨Qm, hQm⟩ := R.hasQuadraticMuOfIsEllipticFieldOn hEll hvol compat
  exact ⟨Qm, fun Pv => by rw [Mu_congr_of_ae_eq (ae_restrict_of_ae hae) Pv]; exact hQm Pv⟩

/-! ### the η-kernel measurability layer -/

/-- Entrywise measurability is preserved by a fixed two-sided matrix product. -/
theorem measurable_mul_mul {Ω : Type*} [MeasurableSpace Ω] (L R : FullBlockMat d)
    (X : Ω → FullBlockMat d) (hX : ∀ ζ δ, Measurable fun ω => X ω ζ δ) (α β : BlockCoord d) :
    Measurable fun ω => (L * X ω * R) α β := by
  have hrw : (fun ω => (L * X ω * R) α β)
      = fun ω => ∑ δ : BlockCoord d, (∑ ζ : BlockCoord d, L α ζ * X ω ζ δ) * R δ β := by
    funext ω
    rw [Matrix.mul_apply]
    exact Finset.sum_congr rfl fun δ _ => by rw [Matrix.mul_apply]
  rw [hrw]
  exact Finset.measurable_sum _ fun δ _ =>
    (Finset.measurable_sum _ fun ζ _ => (hX ζ δ).const_mul _).mul_const _

/-- The congruence bridge on an ALIGNED adapted cell, minus sign. -/
theorem coarseBlockMatrix_respCoeffMinus_at [NeZero d] {q : Mat d} (hq : IsUnit q) (j : ℤ)
    (w : Fin d → ℤ) (F : BlockMat d) (a : CoeffSpace d) :
    coarseBlockMatrix (adaptedCellAtCenter q j w) (respCoeffMinus F a)
      = blockCongr (respG F) (coarseBlock (adaptedCellAtCenter q j w) a) :=
  coarseBlockMatrix_sub_skew_eq_blockCongr (respg_isSkew F)
    (hasQuadraticMu_adaptedCellAtCenter q hq j w a)

/-- Entrywise measurability of the recentred coarse block on an aligned cell, minus sign. -/
theorem measurable_coarseBlockMatrix_minus [NeZero d] {q : Mat d} (hq : IsUnit q)
    (j : ℤ) (w : Fin d → ℤ) (F : BlockMat d) (α β : BlockCoord d) :
    Measurable fun a : CoeffSpace d =>
      toFullBlockMat (coarseBlockMatrix (adaptedCellAtCenter q j w) (respCoeffMinus F a)) α β := by
  have hrw : (fun a : CoeffSpace d =>
      toFullBlockMat (coarseBlockMatrix (adaptedCellAtCenter q j w) (respCoeffMinus F a)) α β)
      = fun a : CoeffSpace d =>
        ((toFullBlockMat (respG F))ᵀ * toFullBlockMat (coarseBlock (adaptedCellAtCenter q j w) a) *
          toFullBlockMat (respG F)) α β := by
    funext a
    rw [coarseBlockMatrix_respCoeffMinus_at hq j w F a, blockCongr,
      toFullBlockMat_ofFullBlockMat]
  rw [hrw]
  exact measurable_mul_mul _ _ _ (fun ζ δ => measurable_coarseBlock_entry hq j w ζ δ) α β

/-- **The measurability conjunct of the η-kernel (minus).** -/
theorem aestronglyMeasurable_recentDefectBlock_minus [NeZero d] {q : Mat d} (hq : IsUnit q)
    (P : Measure (CoeffSpace d)) (t : ℤ) (n : ℕ) (w : Fin d → ℤ) (E F : BlockMat d) :
    AEStronglyMeasurable (fun a : CoeffSpace d =>
      recentDefectBlock q t n w E (respCoeffMinus F a)) P := by
  refine Measurable.aestronglyMeasurable ?_
  refine Measurable.of_eval fun α => Measurable.of_eval fun β => ?_
  have hcell : HighContrast.adaptedCell q t = adaptedCellAtCenter q t 0 := (adaptedCellAtCenter_zero q t).symm
  have hrw : (fun a : CoeffSpace d => recentDefectBlock q t n w E (respCoeffMinus F a) α β)
      = fun a : CoeffSpace d =>
        (matSqrt ((toFullBlockMat E)⁻¹) *
          (fun a' : CoeffSpace d =>
            toFullBlockMat (blockSub
              (coarseBlockMatrix (adaptedCellAtCenter q (t - (n : ℤ)) w) (respCoeffMinus F a'))
              (coarseBlockMatrix (adaptedCellAtCenter q t 0) (respCoeffMinus F a')))) a *
          matSqrt ((toFullBlockMat E)⁻¹)) α β := by
    funext a
    rw [recentDefectBlock, normalizedBlock, toFullBlockMat_ofFullBlockMat, hcell]
  rw [hrw]
  refine measurable_mul_mul _ _ _ (fun ζ δ => ?_) α β
  simp only [Recurrence.toFullBlockMat_blockSub_apply]
  exact (measurable_coarseBlockMatrix_minus hq (t - (n : ℤ)) w F ζ δ).sub
    (measurable_coarseBlockMatrix_minus hq t 0 F ζ δ)

/-- `G_+ = (shear by g) ∘ D`, the adjoint congruence of the plus recentring. -/
@[expose]
def respGPlus (F : BlockMat d) : BlockMat d :=
  ofFullBlockMat (toFullBlockMat (respG F) * toFullBlockMat (blockD d))

/-- The congruence bridge on an ALIGNED adapted cell, plus sign. -/
theorem coarseBlockMatrix_respCoeffPlus_at [NeZero d] {q : Mat d} (hq : IsUnit q) (j : ℤ)
    (w : Fin d → ℤ) (F : BlockMat d) (a : CoeffSpace d) :
    coarseBlockMatrix (adaptedCellAtCenter q j w) (respCoeffPlus F a)
      = blockCongr (respGPlus F) (coarseBlock (adaptedCellAtCenter q j w) a) := by
  have hgnskew : matTranspose (-(respg F)) = -(-(respg F)) := by
    have hT : matTranspose (-(respg F)) = -matTranspose (respg F) := by
      simp only [matTranspose, Matrix.transpose_neg]
    rw [hT, respg_isSkew F]
  have h1 : respCoeffPlus F a
      = fun y => (adjointCoeffField (⇑a.1 : CoeffField d)) y - (-(respg F)) := by
    funext y
    simp only [respCoeffPlus, adjointCoeffField, sub_neg_eq_add]
  have h2 := coarseBlockMatrix_sub_skew_eq_blockCongr (U := adaptedCellAtCenter q j w)
    (a := adjointCoeffField (⇑a.1 : CoeffField d)) hgnskew
    (hasQuadraticMu_adjointCoeffField (hasQuadraticMu_adaptedCellAtCenter q hq j w a))
  have h3 : coarseBlockMatrix (adaptedCellAtCenter q j w) (adjointCoeffField (⇑a.1 : CoeffField d))
      = blockCongr (blockD d) (coarseBlock (adaptedCellAtCenter q j w) a) := by
    rw [coarseBlockMatrix_adjointCoeffField_of_exists
      (exists_coarseBlockMatrix_of_hasQuadraticMu
        (hasQuadraticMu_adaptedCellAtCenter q hq j w a)), ← blockCongr_blockD]
    rfl
  rw [h1, h2, h3, blockCongr_blockCongr, respGPlus]
  exact congrArg (fun M => blockCongr M (coarseBlock (adaptedCellAtCenter q j w) a))
    (congrArg ofFullBlockMat (blockD_mul_shear_neg (respg F)))

/-- Entrywise measurability of the recentred coarse block on an aligned cell, plus sign. -/
theorem measurable_coarseBlockMatrix_plus [NeZero d] {q : Mat d} (hq : IsUnit q)
    (j : ℤ) (w : Fin d → ℤ) (F : BlockMat d) (α β : BlockCoord d) :
    Measurable fun a : CoeffSpace d =>
      toFullBlockMat (coarseBlockMatrix (adaptedCellAtCenter q j w) (respCoeffPlus F a)) α β := by
  have hrw : (fun a : CoeffSpace d =>
      toFullBlockMat (coarseBlockMatrix (adaptedCellAtCenter q j w) (respCoeffPlus F a)) α β)
      = fun a : CoeffSpace d =>
        ((toFullBlockMat (respGPlus F))ᵀ *
          toFullBlockMat (coarseBlock (adaptedCellAtCenter q j w) a) *
          toFullBlockMat (respGPlus F)) α β := by
    funext a
    rw [coarseBlockMatrix_respCoeffPlus_at hq j w F a, blockCongr,
      toFullBlockMat_ofFullBlockMat]
  rw [hrw]
  exact measurable_mul_mul _ _ _ (fun ζ δ => measurable_coarseBlock_entry hq j w ζ δ) α β

/-- **The measurability conjunct of the η-kernel (plus).** -/
theorem aestronglyMeasurable_recentDefectBlock_plus [NeZero d] {q : Mat d} (hq : IsUnit q)
    (P : Measure (CoeffSpace d)) (t : ℤ) (n : ℕ) (w : Fin d → ℤ) (E F : BlockMat d) :
    AEStronglyMeasurable (fun a : CoeffSpace d =>
      recentDefectBlock q t n w E (respCoeffPlus F a)) P := by
  refine Measurable.aestronglyMeasurable ?_
  refine Measurable.of_eval fun α => Measurable.of_eval fun β => ?_
  have hcell : HighContrast.adaptedCell q t = adaptedCellAtCenter q t 0 := (adaptedCellAtCenter_zero q t).symm
  have hrw : (fun a : CoeffSpace d => recentDefectBlock q t n w E (respCoeffPlus F a) α β)
      = fun a : CoeffSpace d =>
        (matSqrt ((toFullBlockMat E)⁻¹) *
          (fun a' : CoeffSpace d =>
            toFullBlockMat (blockSub
              (coarseBlockMatrix (adaptedCellAtCenter q (t - (n : ℤ)) w) (respCoeffPlus F a'))
              (coarseBlockMatrix (adaptedCellAtCenter q t 0) (respCoeffPlus F a')))) a *
          matSqrt ((toFullBlockMat E)⁻¹)) α β := by
    funext a
    rw [recentDefectBlock, normalizedBlock, toFullBlockMat_ofFullBlockMat, hcell]
  rw [hrw]
  refine measurable_mul_mul _ _ _ (fun ζ δ => ?_) α β
  simp only [Recurrence.toFullBlockMat_blockSub_apply]
  exact (measurable_coarseBlockMatrix_plus hq (t - (n : ℤ)) w F ζ δ).sub
    (measurable_coarseBlockMatrix_plus hq t 0 F ζ δ)

/-! ### The two-sided carrier

The ONE-SIDED hypothesis `∫ respAllScaleMax ^ Q ∂P ≤ Cm * η` cannot imply the η-kernel's conclusion
`∫ ‖D_{n,w}‖ ^ 2 ≤ K n * η ^ (2/Q)` for ANY constant sequence `K`.  The conclusion is unchanged,
and the hypothesis carrier is replaced by its two-sided twin `respAllScaleAbs`
(`ResponseBlockObjects.lean`), which is `respAllScaleMax` with `blockSpecBound` (the spectral
positive
part) replaced by `blockOpNorm`; the premise's route already runs through the TWO-SIDED
`blockOpNorm (normalizedFluctuation …)`.

The lemmas below are the comparison layer that keeps every EXISTING `respAllScaleMax` consumer
(`coarseBlock_le_one_add_respAllScaleMax` among them) available under the new hypothesis:
`respAllScaleMax ≤ respAllScaleAbs` pointwise. -/

/-- `v ⬝ᵥ (N *ᵥ v) ≤ ‖N‖ (v ⬝ᵥ v)` for an ARBITRARY square matrix -- no positivity. -/
private theorem dotProduct_mulVec_le_opNorm_mul_dotProduct_self {n : Type*} [Fintype n] [DecidableEq n]
    (N : Matrix n n ℝ) (v : n → ℝ) : v ⬝ᵥ (N *ᵥ v) ≤ ‖N‖ * (v ⬝ᵥ v) := by
  have hsq := vecSq_mulVec_le N v
  have hvv : (0 : ℝ) ≤ v ⬝ᵥ v := dotProduct_self_nonneg v
  rcases eq_or_lt_of_le (norm_nonneg N) with h0 | hpos
  · have hN : N = 0 := norm_eq_zero.mp h0.symm
    subst hN
    simp
  · have hexp : (0 : ℝ) ≤ (‖N‖ • v - N *ᵥ v) ⬝ᵥ (‖N‖ • v - N *ᵥ v) :=
      dotProduct_self_nonneg _
    have hexpand : (‖N‖ • v - N *ᵥ v) ⬝ᵥ (‖N‖ • v - N *ᵥ v) =
        ‖N‖ * ‖N‖ * (v ⬝ᵥ v) - 2 * ‖N‖ * (v ⬝ᵥ (N *ᵥ v)) + (N *ᵥ v) ⬝ᵥ (N *ᵥ v) := by
      simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul,
        smul_eq_mul, dotProduct_comm (N *ᵥ v) v]
      ring
    rw [hexpand] at hexp
    rw [pow_two] at hsq
    have h2rX : (0 : ℝ) ≤ 2 * ‖N‖ * (‖N‖ * (v ⬝ᵥ v) - v ⬝ᵥ (N *ᵥ v)) := by
      linarith only [hexp, hsq]
    have hpos2 : (0 : ℝ) < 2 * ‖N‖ := by linarith only [hpos]
    have hX : (0 : ℝ) ≤ ‖N‖ * (v ⬝ᵥ v) - v ⬝ᵥ (N *ᵥ v) :=
      (mul_nonneg_iff_of_pos_left hpos2).mp h2rX
    linarith only [hX]

/-- The Loewner envelope of an ARBITRARY doubled block by its operator norm.  This is the step
that does NOT need positive semidefiniteness, and it is what makes `blockSpecBound ≤ blockOpNorm`
unconditional. -/
private theorem blockMatLoewnerLE_blockScale_blockOpNorm_self (N : BlockMat d) :
    BlockMatLoewnerLE N (blockScale (blockOpNorm N) (Book.Ch02.blockIdentity d)) := by
  intro X
  have h := dotProduct_mulVec_le_opNorm_mul_dotProduct_self (toFullBlockMat N) (toFullBlockVec X)
  have hL : blockVecDot X (blockMatVecMul N X) =
      toFullBlockVec X ⬝ᵥ (toFullBlockMat N *ᵥ toFullBlockVec X) := by
    rw [← dotProduct_toFullBlockVec, toFullBlockVec_blockMatVecMul]
  have hB : blockOpNorm N = ‖toFullBlockMat N‖ := rfl
  rw [hL, qform_blockScale_smul, qform_identity, hB]
  linarith only [h]

/-- `‖I‖ ≤ 1` for the doubled identity in the `L²` operator norm (the `d = 0` case is the
zero space, where the norm is `0`). -/
private theorem norm_one_le : ‖(1 : FullBlockMat d)‖ ≤ 1 := by
  rcases isEmpty_or_nonempty (BlockCoord d) with hi | hi
  · let := hi
    have he : (1 : FullBlockMat d) = 0 := Subsingleton.elim _ _
    rw [he, norm_zero]; norm_num
  · exact le_of_eq CStarRing.norm_one

/-- The defining set of `blockSpecBound` is bounded below by `0`. -/
private theorem blockSpecBound_le (N : BlockMat d) (c : ℝ) (hc : 0 ≤ c)
    (h : BlockMatLoewnerLE N (blockScale c (Book.Ch02.blockIdentity d))) :
    blockSpecBound N ≤ c := by
  refine csInf_le ⟨0, ?_⟩ ⟨hc, h⟩
  rintro y ⟨hy0, -⟩
  exact hy0

/-- **The comparison, termwise, UNCONDITIONAL.**  `blockSpecBound N ≤ blockOpNorm N` for
every doubled block: `blockSpecBound N = sInf {c ≥ 0 | N ≼ c I}` and `‖N‖` is a member of that
set by `blockMatLoewnerLE_blockScale_blockOpNorm_self`.  This is the inequality that makes
`respAllScaleAbs`
(`ResponseBlockObjects.lean`) a genuine strengthening of `respAllScaleMax`, so every existing
`respAllScaleMax` consumer -- in particular
`coarseBlock_le_one_add_respAllScaleMax` -- remains available. -/
theorem blockSpecBound_le_blockOpNorm (N : BlockMat d) :
    blockSpecBound N ≤ blockOpNorm N :=
  blockSpecBound_le N _ (by rw [blockOpNorm]; exact norm_nonneg _)
    (blockMatLoewnerLE_blockScale_blockOpNorm_self N)

/-- A normalized block of a positive semidefinite block is positive semidefinite. -/
theorem normalizedBlock_posSemidef_of_posSemidef_of_posDef {A R : BlockMat d}
    (hA : (toFullBlockMat A).PosSemidef) (hR : (toFullBlockMat R).PosDef) :
    (toFullBlockMat (normalizedBlock A R)).PosSemidef := by
  have hs : (matSqrt (toFullBlockMat R)⁻¹).IsHermitian :=
    (Multiscale.matSqrt_inv_posDef_full hR).isHermitian
  have hp := hA.conjTranspose_mul_mul_same (matSqrt (toFullBlockMat R)⁻¹)
  rw [hs.eq] at hp
  rw [normalizedBlock, toFullBlockMat_ofFullBlockMat]
  exact hp

/-- A Loewner bound against `c I` is a bound on the full quadratic form at EVERY vector, not
merely at the vectors of the form `toFullBlockVec X`: `toFullBlockVec` is a bijection
(`toFullBlockVec_ofFullBlockVec`). -/
private theorem dot_le_of_loewner_le_scale_identity {N : BlockMat d} {c : ℝ}
    (h : BlockMatLoewnerLE N (blockScale c (Book.Ch02.blockIdentity d)))
    (v : FullBlockVec d) : v ⬝ᵥ (toFullBlockMat N *ᵥ v) ≤ c * (v ⬝ᵥ v) := by
  have hX := h (ofFullBlockVec v)
  rw [qform_blockScale_smul, qform_identity] at hX
  have hL : blockVecDot (ofFullBlockVec v) (blockMatVecMul N (ofFullBlockVec v)) =
      toFullBlockVec (ofFullBlockVec v) ⬝ᵥ
        (toFullBlockMat N *ᵥ toFullBlockVec (ofFullBlockVec v)) := by
    rw [← dotProduct_toFullBlockVec, toFullBlockVec_blockMatVecMul]
  rw [hL, toFullBlockVec_ofFullBlockVec] at hX
  linarith only [hX]

/-- On a positive semidefinite block a Loewner bound `N ≼ c I` bounds the operator norm.
This is the converse of `blockMatLoewnerLE_blockScale_blockOpNorm_self`, and it is the ONLY place
where
positive semidefiniteness is genuinely needed. -/
private theorem blockOpNorm_le_of_loewner {N : BlockMat d}
    (hN : (toFullBlockMat N).PosSemidef) {c : ℝ} (hc : 0 ≤ c)
    (h : BlockMatLoewnerLE N (blockScale c (Book.Ch02.blockIdentity d))) :
    blockOpNorm N ≤ c :=
  opNorm_le_of_psd_dot_le hN hc (dot_le_of_loewner_le_scale_identity h)

/-- **The reverse comparison on a PSD block**: the two-sided operator norm of `N - I` exceeds
its spectral positive part by at most `2`.  `N ≼ (1 + s) I` with `s = blockSpecBound (N - I)`
by `le_one_add_specBound`, hence `‖N‖ ≤ 1 + s` by `blockOpNorm_le_of_loewner`, hence
`‖N - I‖ ≤ ‖N‖ + ‖I‖ ≤ s + 2`.

This is what turns the EXISTING one-sided envelope `pathwise_envelope` into an envelope
for the two-sided carrier `respAllScaleAbs`, i.e. it discharges the `BddAbove` side condition
of `respAllScaleMax_le_respAllScaleAbs` and of the `le_csSup` step the η-kernel needs. -/
theorem blockOpNorm_sub_id_le_specBound_add_two (N : BlockMat d)
    (hN : (toFullBlockMat N).PosSemidef) :
    blockOpNorm (blockSub N (Book.Ch02.blockIdentity d))
      ≤ blockSpecBound (blockSub N (Book.Ch02.blockIdentity d)) + 2 := by
  set s : ℝ := blockSpecBound (blockSub N (Book.Ch02.blockIdentity d)) with hs
  have hs0 : 0 ≤ s := blockSpecBound_nonneg _
  have hNle : blockOpNorm N ≤ 1 + s := by
    refine blockOpNorm_le_of_loewner hN (by linarith only [hs0]) ?_
    exact le_one_add_specBound N
      (blockOpNorm (blockSub N (Book.Ch02.blockIdentity d))) s
      (by rw [blockOpNorm]; exact norm_nonneg _)
      (blockMatLoewnerLE_blockScale_blockOpNorm_self _) le_rfl
  have hsub : toFullBlockMat (blockSub N (Book.Ch02.blockIdentity d)) =
      toFullBlockMat N - (1 : FullBlockMat d) := by
    rw [toFullBlockMat_blockSub, toFullBlockMat_blockIdentity]
  have htri : ‖toFullBlockMat N - (1 : FullBlockMat d)‖ ≤
      ‖toFullBlockMat N‖ + ‖(1 : FullBlockMat d)‖ := norm_sub_le _ _
  have h1 := norm_one_le (d := d)
  have hB : blockOpNorm N = ‖toFullBlockMat N‖ := rfl
  rw [blockOpNorm, hsub]
  rw [hB] at hNle
  linarith only [htri, h1, hNle]

/-- **`respAllScaleMax ≤ respAllScaleAbs` pointwise.**

One side condition, genuine:

* `hbdd` -- `BddAbove` of the defining set of `respAllScaleAbs`.  `Real.sSup` takes the junk
  value `0` on an unbounded set, so WITHOUT this the inequality is false; the existing
  `respAllScaleMax` lemmas carry exactly the same side condition (`le_csSup hbdd` in
  `coarseBlock_le_one_add_respAllScaleMax`, whose `hbdd` comes from
  `pathwise_envelope`).  Stated, not assumed away. -/
theorem respAllScaleMax_le_respAllScaleAbs (P : Measure (CoeffSpace d)) (γ : ℝ)
    (jStar : ℕ) (F : BlockMat d) (t : ℤ) (a : CoeffSpace d)
    (hbdd : BddAbove {y : ℝ | ∃ n : ℕ, ∃ z ∈ triadicIndexBox d n, y =
      (3 : ℝ) ^ (-(Quenched.contrastRho γ * (n : ℝ))) *
        blockOpNorm (blockSub
          (normalizedBlock (coarseBlock (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z) a)
            (respMean P jStar F t)) (Book.Ch02.blockIdentity d))}) :
    respAllScaleMax P γ jStar F t a ≤ respAllScaleAbs P γ jStar F t a := by
  rw [respAllScaleMax]
  refine Real.sSup_le ?_ ?_
  · rintro y ⟨n, z, hz, rfl⟩
    refine le_trans ?_ (le_csSup hbdd ⟨n, z, hz, rfl⟩)
    exact mul_le_mul_of_nonneg_left (blockSpecBound_le_blockOpNorm _)
      (Real.rpow_nonneg (by norm_num) _)
  · rw [respAllScaleAbs]
    refine Real.sSup_nonneg ?_
    rintro y ⟨n, z, hz, rfl⟩
    exact mul_nonneg (Real.rpow_nonneg (by norm_num) _) (by rw [blockOpNorm]; exact norm_nonneg _)

/-- The coarse block of an ALIGNED adapted cell is positive semidefinite.  The `w`-general
form of `Annealed.coarseBlock_adaptedCell_posSemidef` (`ParentChildRecurrence.lean`, stated only
for `w = 0`); `adaptedCellAtCenter q j w` is by definition `adaptedCellTranslate q j
(adaptedCellCenter q j w)` (`HCPoly/Entry/Setup/AdaptedGridCells.lean`), which is exactly what
`Annealed.blockPosDef_coarseBlock_adapted` (`AdaptedDomainLocality.lean`) takes. -/
theorem coarseBlock_adaptedCellAtCenter_posSemidef_of_isUnit [NeZero d] (q : Mat d) (hq : IsUnit q)
    (j : ℤ) (w : Fin d → ℤ) (a : CoeffSpace d) :
    (toFullBlockMat (coarseBlock (adaptedCellAtCenter q j w) a)).PosSemidef := by
  have hsymm : IsSymmetricBlockMat (coarseBlock (adaptedCellAtCenter q j w) a) :=
    isSymmetricBlockMat_coarseBlockMatrix (adaptedCellAtCenter q j w) (⇑a.1)
  have hpos : Book.Ch02.BlockPosDef (coarseBlock (adaptedCellAtCenter q j w) a) :=
    Annealed.blockPosDef_coarseBlock_adapted q hq j (adaptedCellCenter q j w) a
  exact (posDef_toFullBlockMat hsymm hpos).posSemidef

/-- `‖U‖ ≤ 1` for a matrix with `Uᵀ U = 1`, through the C⋆-identity `‖UᵀU‖ = ‖U‖²`
(`CStarRing.norm_star_mul_self`, `star = ᵀ` over `ℝ`), as in
`HCPoly/Entry/Annealed/ParentChildRecurrence.lean`. -/
private theorem norm_le_one_of_transpose_mul_self
    (U : FullBlockMat d) (h : Uᵀ * U = 1) : ‖U‖ ≤ 1 := by
  have hsq : ‖Uᵀ * U‖ = ‖U‖ * ‖U‖ := by
    have hst := CStarRing.norm_star_mul_self (x := U)
    rwa [show (star U : FullBlockMat d) = Uᵀ from rfl] at hst
  rw [h] at hsq
  have h1 := norm_one_le (d := d)
  nlinarith only [hsq, h1, sq_nonneg (‖U‖ - 1)]

/-- **Congruence invariance of the normalized operator norm.**  Applying the SAME congruence
`blockCongr G` to a block AND to its normalizer leaves the normalized block orthogonally
similar, so its operator norm does not increase:

`U := matSqrt E * G * matSqrt (Gᵀ E G)⁻¹` satisfies `Uᵀ U = 1` and
`normalizedBlock (blockCongr G Z) (blockCongr G E) = Uᵀ · normalizedBlock Z E · U`.

This is the step that carries `weighted_blockOpNorm_le_respAllScaleAbs` from the
`E_t`-picture of `respAllScaleAbs` to the `Ehat^∓`-picture of `recentDefect`: recall
`respEhatMinus = blockCongr (respG F) (respMean …)` (`ResponseBlockObjects.lean`) and that
`coarseBlockMatrix_respCoeffMinus_at` puts the numerator in the matching `blockCongr`
form. -/
theorem blockOpNorm_normalizedBlock_blockCongr_le (G Z E : BlockMat d)
    (hE : (toFullBlockMat E).PosDef)
    (hC : (toFullBlockMat (blockCongr G E)).PosDef) :
    blockOpNorm (normalizedBlock (blockCongr G Z) (blockCongr G E))
      ≤ blockOpNorm (normalizedBlock Z E) := by
  set Ef : FullBlockMat d := toFullBlockMat E with hEf
  set Gf : FullBlockMat d := toFullBlockMat G with hGf
  set Zf : FullBlockMat d := toFullBlockMat Z with hZf
  set Cf : FullBlockMat d := toFullBlockMat (blockCongr G E) with hCfd
  have hCeq : Cf = Gfᵀ * Ef * Gf := by
    rw [hCfd, blockCongr, toFullBlockMat_ofFullBlockMat]
  set S : FullBlockMat d := matSqrt Cf⁻¹ with hSd
  set T : FullBlockMat d := matSqrt Ef⁻¹ with hTd
  set R : FullBlockMat d := matSqrt Ef with hRd
  set U : FullBlockMat d := R * Gf * S with hUd
  have hSsym : Sᵀ = S := transpose_eq_of_psd (matSqrt_inv_posDef_full hC).posSemidef
  have hRsym : Rᵀ = R := transpose_eq_of_psd (matSqrt_spec hE.posSemidef).1
  have hRR : R * R = Ef := (matSqrt_spec hE.posSemidef).2
  have hRT : R * T = 1 := HCPolySupport.HighContrast.matSqrt_mul_matSqrt_inv hE
  have hTR : T * R = 1 := HCPolySupport.HighContrast.matSqrt_inv_mul_matSqrt hE
  have hUU : Uᵀ * U = 1 := by
    rw [hUd, Matrix.transpose_mul, Matrix.transpose_mul, hSsym, hRsym]
    calc S * (Gfᵀ * R) * (R * Gf * S) = S * (Gfᵀ * (R * R) * Gf) * S := by noncomm_ring
      _ = S * Cf * S := by rw [hRR, ← hCeq]
      _ = 1 := matSqrt_inv_conj hC
  have hUUt : U * Uᵀ = 1 := _root_.mul_eq_one_comm.mp hUU
  have hUn : ‖U‖ ≤ 1 := norm_le_one_of_transpose_mul_self U hUU
  have hUtn : ‖Uᵀ‖ ≤ 1 := by
    refine norm_le_one_of_transpose_mul_self Uᵀ ?_
    rw [Matrix.transpose_transpose]
    exact hUUt
  have hlhs : toFullBlockMat (normalizedBlock (blockCongr G Z) (blockCongr G E)) =
      S * (Gfᵀ * Zf * Gf) * S := by
    rw [normalizedBlock, toFullBlockMat_ofFullBlockMat, ← hCfd, ← hSd, blockCongr,
      toFullBlockMat_ofFullBlockMat]
  have hrhs : toFullBlockMat (normalizedBlock Z E) = T * Zf * T := by
    rw [normalizedBlock, toFullBlockMat_ofFullBlockMat, ← hEf, ← hTd]
  have hsim : Uᵀ * (T * Zf * T) * U = S * (Gfᵀ * Zf * Gf) * S := by
    rw [hUd, Matrix.transpose_mul, Matrix.transpose_mul, hSsym, hRsym]
    calc S * (Gfᵀ * R) * (T * Zf * T) * (R * Gf * S)
        = S * Gfᵀ * (R * T) * Zf * (T * R) * Gf * S := by noncomm_ring
      _ = S * (Gfᵀ * Zf * Gf) * S := by
            rw [hRT, hTR]; noncomm_ring
  rw [blockOpNorm, blockOpNorm, hlhs, hrhs, ← hsim]
  have hb1 : ‖Uᵀ * (T * Zf * T) * U‖ ≤ ‖Uᵀ * (T * Zf * T)‖ * ‖U‖ := norm_mul_le _ _
  have hb2 : ‖Uᵀ * (T * Zf * T)‖ ≤ ‖Uᵀ‖ * ‖T * Zf * T‖ := norm_mul_le _ _
  have hM0 : (0 : ℝ) ≤ ‖T * Zf * T‖ := norm_nonneg _
  have hU0 : (0 : ℝ) ≤ ‖U‖ := norm_nonneg _
  have hUt0 : (0 : ℝ) ≤ ‖Uᵀ‖ := norm_nonneg _
  have hP0 : (0 : ℝ) ≤ ‖Uᵀ * (T * Zf * T)‖ := norm_nonneg _
  calc ‖Uᵀ * (T * Zf * T) * U‖
      ≤ ‖Uᵀ * (T * Zf * T)‖ * ‖U‖ := hb1
    _ ≤ (‖Uᵀ‖ * ‖T * Zf * T‖) * ‖U‖ := by
          exact mul_le_mul_of_nonneg_right hb2 hU0
    _ ≤ (1 * ‖T * Zf * T‖) * 1 := by
          exact mul_le_mul (mul_le_mul_of_nonneg_right hUtn hM0) hUn hU0 (by rw [one_mul]; exact hM0)
    _ = ‖T * Zf * T‖ := by rw [one_mul, mul_one]

/-- **The `respAllScaleAbs` envelope.**  The two-sided defining set is a.e. bounded above, by
`C + 2` where `C` is the constant of the ONE-SIDED `pathwise_envelope`: the weights
`3 ^ (-(ρ n))` are at most `1`, and `blockOpNorm_sub_id_le_specBound_add_two` costs `2`.

This is the `respAllScaleAbs` analogue of `pathwise_envelope`, and it is
what lets `le_csSup` be applied to `respAllScaleAbs` -- so the junk value `0` of `Real.sSup` on
an unbounded set is excluded, exactly as for `respAllScaleMax`. -/
theorem pathwise_envelope_abs (hd : 2 ≤ d) (γ : ℝ)
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (E : BlockMat d) (Ψ : ℝ → ℝ) (Kg : ℝ) (Src : CoeffSpace d → ℝ)
    (hstat : IsStationaryLaw P) (hdag : CoarseEllipticityDagger P γ E Ψ Kg Src)
    (jStar : ℕ) (hj : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (t : ℤ) :
    ∀ᵐ a ∂P, BddAbove {y : ℝ | ∃ n : ℕ, ∃ z ∈ triadicIndexBox d n, y =
      (3 : ℝ) ^ (-(Quenched.contrastRho γ * (n : ℝ))) *
        blockOpNorm (blockSub
          (normalizedBlock (coarseBlock (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z) a)
            (respMean P jStar F t)) (Book.Ch02.blockIdentity d))} := by
  have hγ := hdag.g_mem
  let : NeZero d := ⟨by omega⟩
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hj hm
  have hEt : (toFullBlockMat (respMean P jStar F t)).PosDef :=
    Annealed.adaptedMean_posDef d hd P γ E Ψ Kg Src hstat hdag jStar hj (explicitCanonicalMetric F) hm t
  filter_upwards [pathwise_envelope hd γ P E Ψ Kg Src hstat hdag jStar hj F hm t]
    with a ha
  obtain ⟨C, hC0, -, hterms⟩ := ha
  refine ⟨C + 2, ?_⟩
  rintro y ⟨n, z, hz, rfl⟩
  have hw1 : (3 : ℝ) ^ (-(Quenched.contrastRho γ * (n : ℝ))) ≤ 1 := by
    refine Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) ?_
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hρ : 0 ≤ Quenched.contrastRho γ := by rw [Quenched.contrastRho]; linarith only [hγ.1]
    linarith only [mul_nonneg hρ hn0]
  have hw0 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(Quenched.contrastRho γ * (n : ℝ))) :=
    Real.rpow_nonneg (by norm_num) _
  have hpsd := normalizedBlock_posSemidef_of_posSemidef_of_posDef
    (coarseBlock_adaptedCellAtCenter_posSemidef_of_isUnit (respGrid jStar F) hq (t - (n : ℤ)) z a) hEt
  have hkey := blockOpNorm_sub_id_le_specBound_add_two _ hpsd
  have hspec := hterms n z hz
  have hs0 : (0 : ℝ) ≤ blockSpecBound (blockSub
      (normalizedBlock (coarseBlock (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z) a)
        (respMean P jStar F t)) (Book.Ch02.blockIdentity d)) :=
    blockSpecBound_nonneg _
  calc (3 : ℝ) ^ (-(Quenched.contrastRho γ * (n : ℝ))) *
        blockOpNorm (blockSub
          (normalizedBlock (coarseBlock (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z) a)
            (respMean P jStar F t)) (Book.Ch02.blockIdentity d))
      ≤ (3 : ℝ) ^ (-(Quenched.contrastRho γ * (n : ℝ))) *
          (blockSpecBound (blockSub
            (normalizedBlock (coarseBlock (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z) a)
              (respMean P jStar F t)) (Book.Ch02.blockIdentity d)) + 2) :=
        mul_le_mul_of_nonneg_left hkey hw0
    _ = (3 : ℝ) ^ (-(Quenched.contrastRho γ * (n : ℝ))) *
          blockSpecBound (blockSub
            (normalizedBlock (coarseBlock (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z) a)
              (respMean P jStar F t)) (Book.Ch02.blockIdentity d)) +
          (3 : ℝ) ^ (-(Quenched.contrastRho γ * (n : ℝ))) * 2 := by rw [mul_add]
    _ ≤ C + 2 := by linarith only [hspec, hw1]

/-- **The `le_csSup` step for the two-sided carrier.**  Every weighted term of the defining set
of `respAllScaleAbs` is at most `respAllScaleAbs` itself, a.e.  This is the pathwise input the
η-kernel needs on BOTH sides, and the exact analogue of the `le_csSup hbdd hmem` step of
`coarseBlock_le_one_add_respAllScaleMax`. -/
theorem weighted_blockOpNorm_le_respAllScaleAbs (hd : 2 ≤ d) (γ : ℝ)
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (E : BlockMat d) (Ψ : ℝ → ℝ) (Kg : ℝ) (Src : CoeffSpace d → ℝ)
    (hstat : IsStationaryLaw P) (hdag : CoarseEllipticityDagger P γ E Ψ Kg Src)
    (jStar : ℕ) (hj : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (t : ℤ) :
    ∀ᵐ a ∂P, ∀ (n : ℕ), ∀ z ∈ triadicIndexBox d n,
      (3 : ℝ) ^ (-(Quenched.contrastRho γ * (n : ℝ))) *
        blockOpNorm (blockSub
          (normalizedBlock (coarseBlock (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z) a)
            (respMean P jStar F t)) (Book.Ch02.blockIdentity d))
        ≤ respAllScaleAbs P γ jStar F t a := by
  filter_upwards [pathwise_envelope_abs hd γ P E Ψ Kg Src hstat hdag jStar hj F hm t]
    with a hbdd
  intro n z hz
  exact le_csSup hbdd ⟨n, z, hz, rfl⟩

end

end HCPolySupport.HighContrast.Multiscale
end
