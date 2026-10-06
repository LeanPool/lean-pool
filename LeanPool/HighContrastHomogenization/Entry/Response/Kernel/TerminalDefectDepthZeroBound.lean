/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.EtaKernelBound
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# High-contrast homogenization: Entry.Response.Kernel.TerminalDefectDepthZeroBound

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The depth-zero bound on the terminal defect

This file proves the two-sided depth-`0` bound on the normalized terminal defect of the
recentred and adjoint coarse blocks against their own annealed blocks, and composes it with the
analytic core of the recentring bound to obtain the estimate
`integral_respRecentre_sq_le_minus/_plus` (`p.response.transfer`): the correction from the
random cell average to the annealed centre, integrated over the coefficient law via
`response_allscale_abs` and the integrability of `respAllScaleAbs`. A short leaf of purely
real-number identities and inequalities - squares of scaled square roots, the reciprocal bound
on `1 - 3^{-1/2}`, and the rewriting of `η^{1/(2Q)}` powers - is carried alongside it for reuse
when the weak-norm estimate is finally assembled.
-/

section
open HCPolySupport.HighContrast (CoeffSpace blockSub coarseBlock normalizedBlock)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator
open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ}

/-! ## The random-to-annealed recentring (`p.response.transfer`) -/

/-! ### The recentring layer.

The two twins below rest on the observation that the available `respAllScaleMax` controls
only the spectral positive part.

This is not a gap in the proof but a defect of the STATEMENT: the recentring vector `c_a =
M_0^{1/2} R (A_t(a) − Ehat_t^-) x^-` needs a bound on the SIGNED difference, which the one-sided
`respAllScaleMax` provably cannot give (the one-sided hypothesis is too weak for this bound, for
every constant).  Accordingly the two carrier premises of both twins are restated on the two-sided
`respAllScaleAbs`, exactly as for the earlier twins.  The restatement is free of new obligations:
`response_allscale_abs` produces the moment bound and
`respAllScaleAbs_aestronglyMeasurable_integrable` the integrability, and
`integral_recentDefect_sq_le_of_rawOutput_minus`/`_plus` are the compiled proof that they compose
from `RawOutput` alone.

The analytic core is the comparison `profilePrimalCenterVariance_le_variance` through
`centered_metric_quadratic_le`; it lives in `RandomToAnnealedRecentring.lean`, imported above.
What remains
here is the three steps that need the earlier layer: the depth-`0` comparison with
`respAllScaleAbs`, measurability, and Jensen. -/

/-- **The depth-`0` two-sided bound, minus sign.**  The normalized terminal defect of the
RECENTRED coarse block against its own annealed block is at most `respAllScaleAbs`, a.e.

This is the `n = 0` instance of the earlier layer: the congruence `respG F` relates the
`Ehat^-`-picture to the `E_t`-picture without increasing the normalized operator norm
(`blockOpNorm_normalizedBlock_blockCongr_le`), `normalizedBlock` is linear
(`normalizedBlock_blockSub`) and normalizes `E_t` to the identity
(`normalizedBlock_self_of_posDef`), and the depth-`0` member of the defining set of
`respAllScaleAbs` carries the weight `3 ^ 0 = 1`. -/
private theorem normalizedDefect_le_respAllScaleAbs_minus (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1)
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (E : BlockMat d) (Ψ : ℝ → ℝ) (Kg : ℝ) (Src : CoeffSpace d → ℝ)
    (hstat : IsStationaryLaw P) (hdag : CoarseEllipticityDagger P γ E Ψ Kg Src)
    (jStar : ℕ) (hj : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (t : ℤ) :
    ∀ᵐ a ∂P, blockOpNorm (normalizedBlock
        (blockSub (coarseBlockMatrix (respCell jStar F t) (respCoeffMinus F a))
          (respEhatMinus P jStar F t)) (respEhatMinus P jStar F t))
      ≤ respAllScaleAbs P γ jStar F t a := by
  let : NeZero d := ⟨by omega⟩
  have _hγ := hγ
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hj hm
  have hEt : (toFullBlockMat (respMean P jStar F t)).PosDef :=
    Annealed.adaptedMean_posDef d hd P γ E Ψ Kg Src hstat hdag jStar hj (explicitCanonicalMetric F) hm t
  have hEhat : (toFullBlockMat (respEhatMinus P jStar F t)).PosDef :=
    respEhatMinus_posDef hd γ P E Ψ Kg Src hstat hdag jStar hj F hm t
  filter_upwards
    [weighted_blockOpNorm_le_respAllScaleAbs hd γ P E Ψ Kg Src hstat hdag jStar hj F hm t]
    with a hkey
  have h0 := hkey 0 0 (zero_mem_triadicIndexBox 0)
  simp only [Nat.cast_zero, mul_zero, neg_zero, Real.rpow_zero, one_mul, sub_zero] at h0
  rw [adaptedCellAtCenter_zero] at h0
  have hEhd : respEhatMinus P jStar F t = blockCongr (respG F) (respMean P jStar F t) := rfl
  have hAeq : coarseBlockMatrix (respCell jStar F t) (respCoeffMinus F a)
      = blockCongr (respG F) (coarseBlock (respCell jStar F t) a) := by
    have hx := coarseBlockMatrix_respCoeffMinus_at hq t 0 F a
    rwa [adaptedCellAtCenter_zero] at hx
  have hsub : blockSub (coarseBlockMatrix (respCell jStar F t) (respCoeffMinus F a))
      (respEhatMinus P jStar F t)
      = blockCongr (respG F)
          (blockSub (coarseBlock (respCell jStar F t) a) (respMean P jStar F t)) := by
    rw [hAeq, hEhd, ← blockCongr_blockSub]
  have hcongr := blockOpNorm_normalizedBlock_blockCongr_le (respG F)
    (blockSub (coarseBlock (respCell jStar F t) a) (respMean P jStar F t))
    (respMean P jStar F t) hEt (hEhd ▸ hEhat)
  have hsplit : normalizedBlock
      (blockSub (coarseBlock (respCell jStar F t) a) (respMean P jStar F t))
      (respMean P jStar F t)
      = blockSub (normalizedBlock (coarseBlock (respCell jStar F t) a) (respMean P jStar F t))
          (Book.Ch02.blockIdentity d) := by
    rw [Annealed.normalizedBlock_blockSub, normalizedBlock_self_of_posDef _ hEt]
  rw [hsub, hEhd]
  refine le_trans hcongr ?_
  rw [hsplit]
  exact h0

/-- **The depth-`0` two-sided bound, plus sign.** -/
private theorem normalizedDefect_le_respAllScaleAbs_plus (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1)
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (E : BlockMat d) (Ψ : ℝ → ℝ) (Kg : ℝ) (Src : CoeffSpace d → ℝ)
    (hstat : IsStationaryLaw P) (hdag : CoarseEllipticityDagger P γ E Ψ Kg Src)
    (jStar : ℕ) (hj : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (t : ℤ) :
    ∀ᵐ a ∂P, blockOpNorm (normalizedBlock
        (blockSub (coarseBlockMatrix (respCell jStar F t) (respCoeffPlus F a))
          (respEhatPlus P jStar F t)) (respEhatPlus P jStar F t))
      ≤ respAllScaleAbs P γ jStar F t a := by
  let : NeZero d := ⟨by omega⟩
  have _hγ := hγ
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hj hm
  have hEt : (toFullBlockMat (respMean P jStar F t)).PosDef :=
    Annealed.adaptedMean_posDef d hd P γ E Ψ Kg Src hstat hdag jStar hj (explicitCanonicalMetric F) hm t
  have hEhat : (toFullBlockMat (respEhatPlus P jStar F t)).PosDef :=
    respEhatPlus_posDef hd γ P E Ψ Kg Src hstat hdag jStar hj F hm t
  filter_upwards
    [weighted_blockOpNorm_le_respAllScaleAbs hd γ P E Ψ Kg Src hstat hdag jStar hj F hm t]
    with a hkey
  have h0 := hkey 0 0 (zero_mem_triadicIndexBox 0)
  simp only [Nat.cast_zero, mul_zero, neg_zero, Real.rpow_zero, one_mul, sub_zero] at h0
  rw [adaptedCellAtCenter_zero] at h0
  have hEhd := respEhatPlus_eq_blockCongr P jStar F t
  have hAeq : coarseBlockMatrix (respCell jStar F t) (respCoeffPlus F a)
      = blockCongr (respGPlus F) (coarseBlock (respCell jStar F t) a) := by
    have hx := coarseBlockMatrix_respCoeffPlus_at hq t 0 F a
    rwa [adaptedCellAtCenter_zero] at hx
  have hsub : blockSub (coarseBlockMatrix (respCell jStar F t) (respCoeffPlus F a))
      (respEhatPlus P jStar F t)
      = blockCongr (respGPlus F)
          (blockSub (coarseBlock (respCell jStar F t) a) (respMean P jStar F t)) := by
    rw [hAeq, hEhd, ← blockCongr_blockSub]
  have hcongr := blockOpNorm_normalizedBlock_blockCongr_le (respGPlus F)
    (blockSub (coarseBlock (respCell jStar F t) a) (respMean P jStar F t))
    (respMean P jStar F t) hEt (hEhd ▸ hEhat)
  have hsplit : normalizedBlock
      (blockSub (coarseBlock (respCell jStar F t) a) (respMean P jStar F t))
      (respMean P jStar F t)
      = blockSub (normalizedBlock (coarseBlock (respCell jStar F t) a) (respMean P jStar F t))
          (Book.Ch02.blockIdentity d) := by
    rw [Annealed.normalizedBlock_blockSub, normalizedBlock_self_of_posDef _ hEt]
  rw [hsub, hEhd]
  refine le_trans hcongr ?_
  rw [hsplit]
  exact h0

/-- **Measurability of the recentring length.**  After the mean identity the optimizer family
`u` has disappeared from `|c_a|²`, which is then a polynomial in the entries of the pathwise
coarse block; that is what makes the first conjunct provable at all, since the statement
quantifies over an ARBITRARY family of maximizers with no measurability assumption. -/
private theorem measurable_recentre_sq {Ω : Type*} [MeasurableSpace Ω]
    (F Ehat : BlockMat d) (x : BlockVec d) (A : Ω → BlockMat d)
    (hA : ∀ ζ δ, Measurable fun ω => toFullBlockMat (A ω) ζ δ) :
    Measurable fun ω =>
      blockVecDot
        (blockMatVecMul (blockSqrt (respM0 F))
          (blockResponseMean (A ω) x - blockResponseMean Ehat x))
        (blockMatVecMul (blockSqrt (respM0 F))
          (blockResponseMean (A ω) x - blockResponseMean Ehat x)) := by
  set S : FullBlockMat d :=
    toFullBlockMat (blockSqrt (respM0 F)) * toFullBlockMat (blockSwap d) with hS
  have hflat : ∀ ω, toFullBlockVec (blockMatVecMul (blockSqrt (respM0 F))
      (blockResponseMean (A ω) x - blockResponseMean Ehat x))
      = (S * (toFullBlockMat (A ω) - toFullBlockMat Ehat)) *ᵥ toFullBlockVec x := by
    intro ω
    rw [blockResponseMean_sub_blockResponseMean, toFullBlockVec_blockMatVecMul,
      toFullBlockVec_blockMatVecMul, toFullBlockVec_blockMatVecMul,
      toFullBlockMat_blockSub, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hS,
      Matrix.mul_assoc]
  have hrw : (fun ω => blockVecDot
      (blockMatVecMul (blockSqrt (respM0 F))
        (blockResponseMean (A ω) x - blockResponseMean Ehat x))
      (blockMatVecMul (blockSqrt (respM0 F))
        (blockResponseMean (A ω) x - blockResponseMean Ehat x)))
      = fun ω => ∑ α : BlockCoord d,
          ((S * (toFullBlockMat (A ω) - toFullBlockMat Ehat)) *ᵥ toFullBlockVec x) α *
          ((S * (toFullBlockMat (A ω) - toFullBlockMat Ehat)) *ᵥ toFullBlockVec x) α := by
    funext ω
    rw [← dotProduct_toFullBlockVec, hflat ω]
    rfl
  rw [hrw]
  refine Finset.measurable_sum _ fun α _ => ?_
  have hM : ∀ β : BlockCoord d, Measurable fun ω =>
      (S * (toFullBlockMat (A ω) - toFullBlockMat Ehat)) α β := by
    intro β
    have hx := measurable_mul_mul S 1
      (fun ω => toFullBlockMat (A ω) - toFullBlockMat Ehat)
      (fun ζ δ => (hA ζ δ).sub measurable_const) α β
    simpa using hx
  have hentry : Measurable fun ω =>
      ((S * (toFullBlockMat (A ω) - toFullBlockMat Ehat)) *ᵥ toFullBlockVec x) α := by
    have hxr : (fun ω => ((S * (toFullBlockMat (A ω) - toFullBlockMat Ehat)) *ᵥ
        toFullBlockVec x) α)
        = fun ω => ∑ β : BlockCoord d,
            (S * (toFullBlockMat (A ω) - toFullBlockMat Ehat)) α β * toFullBlockVec x β := rfl
    rw [hxr]
    exact Finset.measurable_sum _ fun β _ => (hM β).mul_const _
  exact hentry.mul hentry

/-- **From the pathwise recentring bound to conjuncts 1 and 2.**  The recentring analogue of
`conjuncts_of_pointwise` above: the majorant is `c · A²` rather than `(c · A)²`, because the
recentring bound is already stated on the SQUARE. -/
private theorem conjuncts_of_pointwise_sq (P : Measure (CoeffSpace d))
    [IsProbabilityMeasure P] (Q : ℕ) (hQ : 2 ≤ Q) (Cm η : ℝ) (hCm : 0 < Cm) (hη : 0 < η)
    (f A : CoeffSpace d → ℝ) (hA0 : ∀ a, 0 ≤ A a) (hf0 : ∀ a, 0 ≤ f a)
    (hfmeas : AEStronglyMeasurable f P)
    (hAmeas : AEStronglyMeasurable (fun a => A a ^ 2) P)
    (c : ℝ) (hc : 0 ≤ c) (hbound : ∀ᵐ a ∂P, f a ≤ c * A a ^ 2)
    (hAint : Integrable (fun a => A a ^ Q) P) (hAle : ∫ a, A a ^ Q ∂P ≤ Cm * η) :
    Integrable f P ∧
      ∫ a, f a ∂P ≤ c * (Cm ^ ((2 : ℝ) / (Q : ℝ)) * η ^ ((2 : ℝ) / (Q : ℝ))) := by
  have hsq_le : ∀ a, A a ^ 2 ≤ 1 + A a ^ Q := by
    intro a
    rcases le_or_gt (A a) 1 with h | h
    · have h2 : A a ^ 2 ≤ 1 := by nlinarith only [h, hA0 a]
      have hQnn : (0 : ℝ) ≤ A a ^ Q := pow_nonneg (hA0 a) _
      linarith only [h2, hQnn]
    · have h2 : A a ^ 2 ≤ A a ^ Q := pow_le_pow_right₀ h.le hQ
      have hQnn : (0 : ℝ) ≤ A a ^ Q := pow_nonneg (hA0 a) _
      linarith only [h2, hQnn]
  have hA2 : Integrable (fun a => A a ^ 2) P := by
    refine Integrable.mono' ((integrable_const (1 : ℝ)).add hAint) hAmeas ?_
    filter_upwards with a
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hA0 a) 2)]
    exact hsq_le a
  have hfint : Integrable f P := by
    refine Integrable.mono' (hA2.const_mul c) hfmeas ?_
    filter_upwards [hbound] with a ha
    rw [Real.norm_eq_abs, abs_of_nonneg (hf0 a)]
    exact ha
  refine ⟨hfint, ?_⟩
  have hstep1 : ∫ a, f a ∂P ≤ c * ∫ a, A a ^ 2 ∂P := by
    have hx := integral_mono_ae hfint (hA2.const_mul c) hbound
    rwa [integral_const_mul] at hx
  have hstep2 : ∫ a, A a ^ 2 ∂P ≤ (∫ a, A a ^ Q ∂P) ^ ((2 : ℝ) / (Q : ℝ)) :=
    integral_sq_le_rpow P Q hQ A hA0 hA2 hAint
  have hQ0 : (0 : ℝ) < (Q : ℝ) := by
    have : (0 : ℕ) < Q := by omega
    exact_mod_cast this
  have hexp : (0 : ℝ) ≤ (2 : ℝ) / (Q : ℝ) := le_of_lt (div_pos (by norm_num) hQ0)
  have hInn : (0 : ℝ) ≤ ∫ a, A a ^ Q ∂P := integral_nonneg fun a => pow_nonneg (hA0 a) _
  have hstep3 : (∫ a, A a ^ Q ∂P) ^ ((2 : ℝ) / (Q : ℝ)) ≤ (Cm * η) ^ ((2 : ℝ) / (Q : ℝ)) :=
    Real.rpow_le_rpow hInn hAle hexp
  have hstep4 : (Cm * η) ^ ((2 : ℝ) / (Q : ℝ)) =
      Cm ^ ((2 : ℝ) / (Q : ℝ)) * η ^ ((2 : ℝ) / (Q : ℝ)) := Real.mul_rpow hCm.le hη.le
  calc ∫ a, f a ∂P ≤ c * ∫ a, A a ^ 2 ∂P := hstep1
    _ ≤ c * ((Cm * η) ^ ((2 : ℝ) / (Q : ℝ))) :=
        mul_le_mul_of_nonneg_left (le_trans hstep2 hstep3) hc
    _ = c * (Cm ^ ((2 : ℝ) / (Q : ℝ)) * η ^ ((2 : ℝ) / (Q : ℝ))) := by rw [hstep4]

/-- `0 ≤ |X|²` for the doubled dot product. -/
private theorem blockVecDot_self_nonneg (X : BlockVec d) : 0 ≤ blockVecDot X X := by
  rw [← dotProduct_toFullBlockVec]
  exact dotProduct_self_nonneg _

/-- `0 ≤ x · Ehat x` for a positive semidefinite doubled block. -/
private theorem qform_nonneg {Ehat : BlockMat d}
    (hE : (toFullBlockMat Ehat).PosSemidef) (x : BlockVec d) :
    0 ≤ blockVecDot x (blockMatVecMul Ehat x) := by
  have hx := hE.dotProduct_mulVec_nonneg (toFullBlockVec x)
  rw [← dotProduct_toFullBlockVec, toFullBlockVec_blockMatVecMul]
  simpa using hx

/-- **The recentring estimate, minus sign.** `⟨X_a⟩_{U_t} = blockResponseMean (A^b_t(a)) x^-` and
`Y^- = blockResponseMean (Ehat_t^-) x^- = ∫ ⟨X_a⟩_{U_t} dP` (`integral_blockResponseMean`;
its integrability binders come from `RawOutput`), so
`c_a = M_0^{1/2} R (A^b_t(a) - Ehat_t^-) x^-` and `|c_a| ≤ K_0 ·
‖Ehat^{-1/2}(A_t(a)-Ehat)Ehat^{-1/2}‖ · L^-`
(`‖M_0^{1/2} R Ehat^{1/2}‖^2 = K_0^2` since `R = blockSwap` and `S M_0^{1/2} = M_0^{-1/2} S`);
the two-sided difference at depth `0` is bounded as in the earlier layer by `M(a)` (+
swap-conjugate lower side),
and `∫ M^2 ≤ (∫ M^Q)^{2/Q}`. -/
theorem integral_respRecentre_sq_le_minus (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1) (S : SelectionData) (hS : S.Selects d γ) (Cc Cm : ℝ)
    (hCc : 0 < Cc) (hCm : 0 < Cm) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (ε σ Cglob Cprof Csrc Bresp : ℝ) (H : ℕ) (P : Measure (CoeffSpace d)) (E : BlockMat d)
        (Ψ : ℝ → ℝ) (Kg : ℝ) (Src : CoeffSpace d → ℝ) (B : ℝ) (jStar : ℕ) (F : BlockMat d)
        (s t : ℤ),
        RawOutput d γ S ε σ Cglob Cprof Csrc H Bresp P E Ψ Kg Src B jStar F s t →
        RespCalibrated Cc P jStar F s t →
        ∀ η : ℝ, η ∈ Set.Ioo (0 : ℝ) (1 / 2) →
          Integrable (fun a => respAllScaleAbs P γ jStar F t a ^ bigQ d γ) P →
          ∫ a, respAllScaleAbs P γ jStar F t a ^ bigQ d γ ∂P ≤ Cm * η →
          ∀ e : Vec d, vecDot e e = 1 →
            ∀ (u : (a : CoeffSpace d) → AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t)),
              (∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
                (respqMinus P jStar F t e) (respCoeffMinus F a) (u a)) →
              Integrable (fun a => blockVecDot (respRecentreMinus P jStar F t e a (u a))
                (respRecentreMinus P jStar F t e a (u a))) P ∧
              ∫ a, blockVecDot (respRecentreMinus P jStar F t e a (u a))
                  (respRecentreMinus P jStar F t e a (u a)) ∂P ≤
                C * (respK0SqMinus P jStar F t * respLsqMinus P jStar F t e) *
                  η ^ ((2 : ℝ) / (bigQ d γ : ℝ)) := by
  let : NeZero d := ⟨by omega⟩
  -- `hS`/`hCc` are carried by the statement but are not needed by this route; named here so the
  -- unused-variable linter does not force a rename of the binders.
  have _hS_unused := hS
  have _hCc_unused := hCc
  refine ⟨Cm ^ ((2 : ℝ) / (bigQ d γ : ℝ)), Real.rpow_pos_of_pos hCm _, ?_⟩
  intro ε σ Cglob Cprof Csrc Bresp H P E Ψ Kg Src B jStar F s t raw _hcal η hη hAint hAle e _he u hu
  have := raw.prob
  have hm : (explicitCanonicalMetric F).PosDef := Geometry.explicitCanonicalMetric_posDef raw.symm raw.pos
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid raw.hj hm
  have hEhat : (toFullBlockMat (respEhatMinus P jStar F t)).PosDef :=
    respEhatMinus_posDef hd γ P E Ψ Kg Src raw.stat raw.ell jStar raw.hj F hm t
  have hQ2 : 2 ≤ bigQ d γ := bigQ_two_le d γ hγ
  -- The mean identity eliminates the optimizer family `u` from `c_a`, which is what makes
  -- conjunct 1 provable.
  have hcell : ∀ a : CoeffSpace d,
      cellAverage (respCell jStar F t) (optimizerField (respCoeffMinus F a) (u a))
        = blockResponseMean (coarseBlockMatrix (respCell jStar F t) (respCoeffMinus F a))
            (respxMinus P jStar F t e) := fun a =>
    cellAverage_optimizerField_respCoeffMinus_eq (respGrid jStar F) hq t F a
      (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (u a) (hu a)
  have hfeq : (fun a : CoeffSpace d => blockVecDot (respRecentreMinus P jStar F t e a (u a))
        (respRecentreMinus P jStar F t e a (u a)))
      = fun a : CoeffSpace d => blockVecDot
          (blockMatVecMul (blockSqrt (respM0 F))
            (blockResponseMean (coarseBlockMatrix (respCell jStar F t) (respCoeffMinus F a))
                (respxMinus P jStar F t e)
              - blockResponseMean (respEhatMinus P jStar F t) (respxMinus P jStar F t e)))
          (blockMatVecMul (blockSqrt (respM0 F))
            (blockResponseMean (coarseBlockMatrix (respCell jStar F t) (respCoeffMinus F a))
                (respxMinus P jStar F t e)
              - blockResponseMean (respEhatMinus P jStar F t) (respxMinus P jStar F t e))) := by
    funext a
    simp only [respRecentreMinus, respYMinus, hcell a]
  have hmeas : AEStronglyMeasurable (fun a : CoeffSpace d =>
      blockVecDot (respRecentreMinus P jStar F t e a (u a))
        (respRecentreMinus P jStar F t e a (u a))) P := by
    refine Measurable.aestronglyMeasurable ?_
    rw [hfeq]
    refine measurable_recentre_sq F (respEhatMinus P jStar F t) (respxMinus P jStar F t e)
      (fun a => coarseBlockMatrix (respCell jStar F t) (respCoeffMinus F a)) ?_
    intro ζ δ
    have hx := measurable_coarseBlockMatrix_minus hq t 0 F ζ δ
    rwa [adaptedCellAtCenter_zero] at hx
  have hK0 : (0 : ℝ) ≤ respK0SqMinus P jStar F t := blockSpecBound_nonneg _
  have hL0 : (0 : ℝ) ≤ respLsqMinus P jStar F t e :=
    qform_nonneg hEhat.posSemidef (respxMinus P jStar F t e)
  have hbound : ∀ᵐ a ∂P, blockVecDot (respRecentreMinus P jStar F t e a (u a))
      (respRecentreMinus P jStar F t e a (u a))
      ≤ (respK0SqMinus P jStar F t * respLsqMinus P jStar F t e) *
          respAllScaleAbs P γ jStar F t a ^ 2 := by
    filter_upwards [normalizedDefect_le_respAllScaleAbs_minus hd γ hγ P E Ψ Kg Src
      raw.stat raw.ell jStar raw.hj F hm t] with a ha
    have hpt := recentre_sq_le_minus P jStar F t e hq hm hEhat a (u a) (hu a)
    have hn0 : (0 : ℝ) ≤ blockOpNorm (normalizedBlock
        (blockSub (coarseBlockMatrix (respCell jStar F t) (respCoeffMinus F a))
          (respEhatMinus P jStar F t)) (respEhatMinus P jStar F t)) := by
      rw [blockOpNorm]; exact norm_nonneg _
    have hA0 : (0 : ℝ) ≤ respAllScaleAbs P γ jStar F t a :=
      respAllScaleAbs_nonneg P γ jStar F t a
    have hKL : respK0SqMinus P jStar F t = blockSpecBound
        (normalizedBlock (respEhatMinus P jStar F t) (respM0 F)) := rfl
    rw [hKL] at hK0 ⊢
    refine le_trans hpt ?_
    set NN : ℝ := blockOpNorm (normalizedBlock
        (blockSub (coarseBlockMatrix (respCell jStar F t) (respCoeffMinus F a))
          (respEhatMinus P jStar F t)) (respEhatMinus P jStar F t)) with _hNN
    set KK : ℝ := blockSpecBound (normalizedBlock (respEhatMinus P jStar F t) (respM0 F)) with _hKK
    set LL : ℝ := respLsqMinus P jStar F t e with _hLL
    set AA : ℝ := respAllScaleAbs P γ jStar F t a with _hAA
    have hsq : NN ^ 2 ≤ AA ^ 2 := by nlinarith only [ha, hn0, hA0, _hNN, _hAA]
    have hfin := mul_le_mul_of_nonneg_left hsq (mul_nonneg hK0 hL0)
    linarith only [hfin]
  obtain ⟨hint, hle⟩ := conjuncts_of_pointwise_sq P (bigQ d γ) hQ2 Cm η hCm hη.1 _ _
    (respAllScaleAbs_nonneg P γ jStar F t)
    (fun a => blockVecDot_self_nonneg _) hmeas
    (((respAllScaleAbs_measurable P γ jStar F hq t).pow_const 2).aestronglyMeasurable)
    _ (mul_nonneg hK0 hL0) hbound hAint hAle
  refine ⟨hint, ?_⟩
  calc ∫ a, blockVecDot (respRecentreMinus P jStar F t e a (u a))
        (respRecentreMinus P jStar F t e a (u a)) ∂P
      ≤ (respK0SqMinus P jStar F t * respLsqMinus P jStar F t e) *
          (Cm ^ ((2 : ℝ) / (bigQ d γ : ℝ)) * η ^ ((2 : ℝ) / (bigQ d γ : ℝ))) := hle
    _ = Cm ^ ((2 : ℝ) / (bigQ d γ : ℝ)) *
          (respK0SqMinus P jStar F t * respLsqMinus P jStar F t e) *
          η ^ ((2 : ℝ) / (bigQ d γ : ℝ)) := by ring

/-- **The recentring estimate, plus sign.** -/
theorem integral_respRecentre_sq_le_plus (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1) (S : SelectionData) (hS : S.Selects d γ) (Cc Cm : ℝ)
    (hCc : 0 < Cc) (hCm : 0 < Cm) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (ε σ Cglob Cprof Csrc Bresp : ℝ) (H : ℕ) (P : Measure (CoeffSpace d)) (E : BlockMat d)
        (Ψ : ℝ → ℝ) (Kg : ℝ) (Src : CoeffSpace d → ℝ) (B : ℝ) (jStar : ℕ) (F : BlockMat d)
        (s t : ℤ),
        RawOutput d γ S ε σ Cglob Cprof Csrc H Bresp P E Ψ Kg Src B jStar F s t →
        RespCalibrated Cc P jStar F s t →
        ∀ η : ℝ, η ∈ Set.Ioo (0 : ℝ) (1 / 2) →
          Integrable (fun a => respAllScaleAbs P γ jStar F t a ^ bigQ d γ) P →
          ∫ a, respAllScaleAbs P γ jStar F t a ^ bigQ d γ ∂P ≤ Cm * η →
          ∀ e : Vec d, vecDot e e = 1 →
            ∀ (u : (a : CoeffSpace d) → AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t)),
              (∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
                (respqPlus P jStar F t e) (respCoeffPlus F a) (u a)) →
              Integrable (fun a => blockVecDot (respRecentrePlus P jStar F t e a (u a))
                (respRecentrePlus P jStar F t e a (u a))) P ∧
              ∫ a, blockVecDot (respRecentrePlus P jStar F t e a (u a))
                  (respRecentrePlus P jStar F t e a (u a)) ∂P ≤
                C * (respK0SqPlus P jStar F t * respLsqPlus P jStar F t e) *
                  η ^ ((2 : ℝ) / (bigQ d γ : ℝ)) := by
  let : NeZero d := ⟨by omega⟩
  -- `hS`/`hCc` are carried by the statement but are not needed by this route; named here so the
  -- unused-variable linter does not force a rename of the binders.
  have _hS_unused := hS
  have _hCc_unused := hCc
  refine ⟨Cm ^ ((2 : ℝ) / (bigQ d γ : ℝ)), Real.rpow_pos_of_pos hCm _, ?_⟩
  intro ε σ Cglob Cprof Csrc Bresp H P E Ψ Kg Src B jStar F s t raw _hcal η hη hAint hAle e _he u hu
  have := raw.prob
  have hm : (explicitCanonicalMetric F).PosDef := Geometry.explicitCanonicalMetric_posDef raw.symm raw.pos
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid raw.hj hm
  have hEhat : (toFullBlockMat (respEhatPlus P jStar F t)).PosDef :=
    respEhatPlus_posDef hd γ P E Ψ Kg Src raw.stat raw.ell jStar raw.hj F hm t
  have hQ2 : 2 ≤ bigQ d γ := bigQ_two_le d γ hγ
  -- The mean identity eliminates the optimizer family `u` from `c_a`, which is what makes
  -- conjunct 1 provable.
  have hcell : ∀ a : CoeffSpace d,
      cellAverage (respCell jStar F t) (optimizerField (respCoeffPlus F a) (u a))
        = blockResponseMean (coarseBlockMatrix (respCell jStar F t) (respCoeffPlus F a))
            (respxPlus P jStar F t e) := fun a =>
    cellAverage_optimizerField_respCoeffPlus_eq (respGrid jStar F) hq t F a
      (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (u a) (hu a)
  have hfeq : (fun a : CoeffSpace d => blockVecDot (respRecentrePlus P jStar F t e a (u a))
        (respRecentrePlus P jStar F t e a (u a)))
      = fun a : CoeffSpace d => blockVecDot
          (blockMatVecMul (blockSqrt (respM0 F))
            (blockResponseMean (coarseBlockMatrix (respCell jStar F t) (respCoeffPlus F a))
                (respxPlus P jStar F t e)
              - blockResponseMean (respEhatPlus P jStar F t) (respxPlus P jStar F t e)))
          (blockMatVecMul (blockSqrt (respM0 F))
            (blockResponseMean (coarseBlockMatrix (respCell jStar F t) (respCoeffPlus F a))
                (respxPlus P jStar F t e)
              - blockResponseMean (respEhatPlus P jStar F t) (respxPlus P jStar F t e))) := by
    funext a
    simp only [respRecentrePlus, respYPlus, hcell a]
  have hmeas : AEStronglyMeasurable (fun a : CoeffSpace d =>
      blockVecDot (respRecentrePlus P jStar F t e a (u a))
        (respRecentrePlus P jStar F t e a (u a))) P := by
    refine Measurable.aestronglyMeasurable ?_
    rw [hfeq]
    refine measurable_recentre_sq F (respEhatPlus P jStar F t) (respxPlus P jStar F t e)
      (fun a => coarseBlockMatrix (respCell jStar F t) (respCoeffPlus F a)) ?_
    intro ζ δ
    have hx := measurable_coarseBlockMatrix_plus hq t 0 F ζ δ
    rwa [adaptedCellAtCenter_zero] at hx
  have hK0 : (0 : ℝ) ≤ respK0SqPlus P jStar F t := blockSpecBound_nonneg _
  have hL0 : (0 : ℝ) ≤ respLsqPlus P jStar F t e :=
    qform_nonneg hEhat.posSemidef (respxPlus P jStar F t e)
  have hbound : ∀ᵐ a ∂P, blockVecDot (respRecentrePlus P jStar F t e a (u a))
      (respRecentrePlus P jStar F t e a (u a))
      ≤ (respK0SqPlus P jStar F t * respLsqPlus P jStar F t e) *
          respAllScaleAbs P γ jStar F t a ^ 2 := by
    filter_upwards [normalizedDefect_le_respAllScaleAbs_plus hd γ hγ P E Ψ Kg Src
      raw.stat raw.ell jStar raw.hj F hm t] with a ha
    have hpt := recentre_sq_le_plus P jStar F t e hq hm hEhat a (u a) (hu a)
    have hn0 : (0 : ℝ) ≤ blockOpNorm (normalizedBlock
        (blockSub (coarseBlockMatrix (respCell jStar F t) (respCoeffPlus F a))
          (respEhatPlus P jStar F t)) (respEhatPlus P jStar F t)) := by
      rw [blockOpNorm]; exact norm_nonneg _
    have hA0 : (0 : ℝ) ≤ respAllScaleAbs P γ jStar F t a :=
      respAllScaleAbs_nonneg P γ jStar F t a
    have hKL : respK0SqPlus P jStar F t = blockSpecBound
        (normalizedBlock (respEhatPlus P jStar F t) (respM0 F)) := rfl
    rw [hKL] at hK0 ⊢
    refine le_trans hpt ?_
    set NN : ℝ := blockOpNorm (normalizedBlock
        (blockSub (coarseBlockMatrix (respCell jStar F t) (respCoeffPlus F a))
          (respEhatPlus P jStar F t)) (respEhatPlus P jStar F t)) with _hNN
    set KK : ℝ := blockSpecBound (normalizedBlock (respEhatPlus P jStar F t) (respM0 F)) with _hKK
    set LL : ℝ := respLsqPlus P jStar F t e with _hLL
    set AA : ℝ := respAllScaleAbs P γ jStar F t a with _hAA
    have hsq : NN ^ 2 ≤ AA ^ 2 := by nlinarith only [ha, hn0, hA0, _hNN, _hAA]
    have hfin := mul_le_mul_of_nonneg_left hsq (mul_nonneg hK0 hL0)
    linarith only [hfin]
  obtain ⟨hint, hle⟩ := conjuncts_of_pointwise_sq P (bigQ d γ) hQ2 Cm η hCm hη.1 _ _
    (respAllScaleAbs_nonneg P γ jStar F t)
    (fun a => blockVecDot_self_nonneg _) hmeas
    (((respAllScaleAbs_measurable P γ jStar F hq t).pow_const 2).aestronglyMeasurable)
    _ (mul_nonneg hK0 hL0) hbound hAint hAle
  refine ⟨hint, ?_⟩
  calc ∫ a, blockVecDot (respRecentrePlus P jStar F t e a (u a))
        (respRecentrePlus P jStar F t e a (u a)) ∂P
      ≤ (respK0SqPlus P jStar F t * respLsqPlus P jStar F t e) *
          (Cm ^ ((2 : ℝ) / (bigQ d γ : ℝ)) * η ^ ((2 : ℝ) / (bigQ d γ : ℝ))) := hle
    _ = Cm ^ ((2 : ℝ) / (bigQ d γ : ℝ)) *
          (respK0SqPlus P jStar F t * respLsqPlus P jStar F t e) *
          η ^ ((2 : ℝ) / (bigQ d γ : ℝ)) := by ring

/-! ## The constant chain `K_0 L^± ≤ C κ_s^{1/2}` (`p.response.transfer`) -/

/-! ### The two scale-selection premises.

Can `κ_t ≤ C κ_s` and `1 ≤ κ` be derived from what `RawOutput` / `RespCalibrated` ALREADY state?
Yes, with one caveat.  Both facts are already proved, with `C = 1`, by
`response_imbalance_comparison`
(`HCPoly/Entry/Response/Core/ResponseImbalanceComparison.lean`, sorry-free, in the import closure of
this file through `LoadMeanIdentity`):
  `1 ≤ κ_t ∧ κ_t ≤ κ_s ∧ κ_s ≤ r² κ_t ∧ 1 ≤ r ∧ r < exp(d σ)`.
CAVEAT: `response_imbalance_comparison` carries two premises that this statement -- and the
statement in `WeakEstimateAssembly.lean` --
do NOT carry: `hε : ε ∈ Set.Ioc 0 S.eps0` and `hσ : σ ∈ Set.Ioc 0 ε`.  They are needed because
without them `S.one_le_B0` is unavailable, so `1 ≤ B` fails, so `raw.hs_lo` does not give
`j_* < s`, so `Annealed.adaptedMean_antitone` (`HCPoly/Entry/Annealed/AnnealedBlockOrder.lean`,
which needs
`(jStar : ℤ) ≤ j ≤ k`) does not give `E_t ≤ E_s`, which is what `canonicalImbalance_mono`
 consumes for `κ_t ≤ κ_s`.  `1 ≤ κ_t` alone does NOT need them.
So the missing inequality is NOT one of `RespCalibrated`: it is a premise gap at the
statement.

`respKappa_persistence_of_raw` below is that derivation, compiled.  `respK0Sq_mul_Lsq_le_arith`,
`respLsq_bounds_of_energyDefect`, `respK0Sq_nonneg` and
`respK0Sq_mul_Lsq_le_kappa_of_calibration_step` are the compiled constant chain on top of it:
with the single remaining routine matrix step `K_0² ≤ C_c √κ_t` they close the chain with the
explicit constant `C = 2 C_c (1 + C_e)`. -/

/-- **The persistence inequality (a)**, compiled.  `1 ≤ κ_t` and `κ_t ≤ κ_s` from `RawOutput`
alone, ONCE the two
scale-selection premises `hε`, `hσ` of `response_imbalance_comparison` are available.  A pure
re-export of the first two
conjuncts of `response_imbalance_comparison`; it records, in compiled
form, exactly which premises the inequality turns on. -/
theorem respKappa_persistence_of_raw (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1) (S : SelectionData) (hS : S.Selects d γ)
    (ε σ : ℝ) (hε : ε ∈ Set.Ioc (0 : ℝ) S.eps0) (hσ : σ ∈ Set.Ioc (0 : ℝ) ε)
    (Cglob Cprof Csrc Bresp : ℝ) (H : ℕ) (P : Measure (CoeffSpace d)) (E : BlockMat d)
    (Ψ : ℝ → ℝ) (Kg : ℝ) (Src : CoeffSpace d → ℝ) (B : ℝ) (jStar : ℕ) (F : BlockMat d)
    (s t : ℤ)
    (raw : RawOutput d γ S ε σ Cglob Cprof Csrc H Bresp P E Ψ Kg Src B jStar F s t) :
    1 ≤ respKappa P jStar F t ∧ respKappa P jStar F t ≤ respKappa P jStar F s := by
  obtain ⟨h1, h2, -⟩ :=
    response_imbalance_comparison d hd γ hγ S hS ε σ hε hσ Cglob Cprof Csrc Bresp H P E Ψ Kg
      Src B jStar F s t raw
  exact ⟨h1, h2⟩

/-- **The constant chain as pure real arithmetic**: `K_0² ≤ C_c √κ_t`,
`L² ≤ 2 + 2 C_e √κ_s` and `1 ≤ κ_t ≤ κ_s` give `K_0² L² ≤ 2 C_c (1 + C_e) κ_s`.  The step that
consumes `1 ≤ κ_s` is `√κ_s ≤ κ_s`. -/
theorem respK0Sq_mul_Lsq_le_arith {Cc Ce k0sq lsq kt ks : ℝ} (hCc : 0 < Cc) (_hCe : 0 < Ce)
    (hkt1 : 1 ≤ kt) (hkts : kt ≤ ks) (_hk0nn : 0 ≤ k0sq)
    (hk0 : k0sq ≤ Cc * Real.sqrt kt) (hlnn : 0 ≤ lsq)
    (hl : lsq ≤ 2 + 2 * Ce * Real.sqrt ks) :
    k0sq * lsq ≤ (2 * Cc + 2 * Cc * Ce) * ks := by
  have hks1 : (1 : ℝ) ≤ ks := le_trans hkt1 hkts
  have hksnn : (0 : ℝ) ≤ ks := le_trans zero_le_one hks1
  have hrnn : (0 : ℝ) ≤ Real.sqrt ks := Real.sqrt_nonneg _
  have hrsq : Real.sqrt ks ^ 2 = ks := Real.sq_sqrt hksnn
  have hr1 : (1 : ℝ) ≤ Real.sqrt ks := by nlinarith only [hrsq, hrnn, hks1]
  have hst : Real.sqrt kt ≤ Real.sqrt ks := Real.sqrt_le_sqrt hkts
  have hk0' : k0sq ≤ Cc * Real.sqrt ks := le_trans hk0 (mul_le_mul_of_nonneg_left hst hCc.le)
  have h1 : k0sq * lsq ≤ Cc * Real.sqrt ks * (2 + 2 * Ce * Real.sqrt ks) :=
    mul_le_mul hk0' hl hlnn (mul_nonneg hCc.le hrnn)
  have key : ∀ r : ℝ, 0 ≤ r → 1 ≤ r →
      Cc * r * (2 + 2 * Ce * r) ≤ (2 * Cc + 2 * Cc * Ce) * r ^ 2 := by
    intro r hr0 hr1'
    nlinarith only [mul_nonneg (mul_nonneg hCc.le hr0) (sub_nonneg.mpr hr1')]
  have h2 := key (Real.sqrt ks) hrnn hr1
  rw [hrsq] at h2
  linarith only [h1, h2]

/-- **The `L²` side of the constant chain**, compiled.  `RespEnergyDefect` alone gives both `0 ≤
(L^±)²` (in
fact `2 ≤ (L^±)²`) and `(L^±)² ≤ 2 + 2 C_e √κ_s`, through `(L^±)² = 2(E[J^±] + 1)` and
`0 ≤ E[J^±] ≤ C_e √κ_s`.  No extra premise is needed. -/
theorem respLsq_bounds_of_energyDefect (Ce : ℝ) (P : Measure (CoeffSpace d)) (jStar : ℕ)
    (F : BlockMat d) (s t : ℤ) (e : Vec d) (hE : RespEnergyDefect Ce P jStar F s t e) :
    0 ≤ respLsqMinus P jStar F t e ∧ 0 ≤ respLsqPlus P jStar F t e ∧
      respLsqMinus P jStar F t e ≤ 2 + 2 * Ce * Real.sqrt (respKappa P jStar F s) ∧
      respLsqPlus P jStar F t e ≤ 2 + 2 * Ce * Real.sqrt (respKappa P jStar F s) := by
  obtain ⟨hm0, hp0, hmEq, hpEq, hmLe, hpLe, -⟩ := hE
  exact ⟨by linarith only [hm0, hmEq], by linarith only [hp0, hpEq],
    by linarith only [hmEq, hmLe], by linarith only [hpEq, hpLe]⟩

/-- **The constant chain: `0 ≤ K_0^±`.**  `blockSpecBound` is an `sInf` over a set of nonnegative
reals, so it
is nonnegative whether or not that infimum is attained. -/
theorem respK0Sq_nonneg (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d) (t : ℤ) :
    0 ≤ respK0SqMinus P jStar F t ∧ 0 ≤ respK0SqPlus P jStar F t :=
  ⟨Real.sInf_nonneg (fun _ hx => hx.1), Real.sInf_nonneg (fun _ hx => hx.1)⟩

/-- **The constant chain, conditional witness.**  The two inequalities, with the explicit constant
`C = 2 C_c (1 + C_e)`, from exactly two things beyond `RawOutput`/`RespEnergyDefect`:
* the two scale-selection premises `hε`, `hσ` that this statement and the statement in
`WeakEstimateAssembly.lean` do not
  carry, and
* the single remaining routine matrix step `K_0^± ≤ C_c √κ_t` (hypotheses `hKm`, `hKp`), which is
  `RespCalibrated`'s `Ehat_t^± ≤ C_c √κ_t M_0` normalized by `M_0` and read off by `csInf_le`:
  `normalizedBlock_le_scale` followed by
  `blockSpecBound_le_of_loewner` -- both currently `private`, hence
  restated rather than cited here.

This shows that the chain closes, with a concrete constant, as soon as `hε`/`hσ` are restored; no
new inequality has to be added to `RespCalibrated`. -/
theorem respK0Sq_mul_Lsq_le_kappa_of_calibration_step (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1) (S : SelectionData) (hS : S.Selects d γ) (Cc Ce : ℝ)
    (hCc : 0 < Cc) (hCe : 0 < Ce) :
    ∀ (ε σ Cglob Cprof Csrc Bresp : ℝ) (H : ℕ) (P : Measure (CoeffSpace d)) (E : BlockMat d)
      (Ψ : ℝ → ℝ) (Kg : ℝ) (Src : CoeffSpace d → ℝ) (B : ℝ) (jStar : ℕ) (F : BlockMat d)
      (s t : ℤ),
      ε ∈ Set.Ioc (0 : ℝ) S.eps0 → σ ∈ Set.Ioc (0 : ℝ) ε →
      RawOutput d γ S ε σ Cglob Cprof Csrc H Bresp P E Ψ Kg Src B jStar F s t →
      ∀ e : Vec d,
        RespEnergyDefect Ce P jStar F s t e →
        respK0SqMinus P jStar F t ≤ Cc * Real.sqrt (respKappa P jStar F t) →
        respK0SqPlus P jStar F t ≤ Cc * Real.sqrt (respKappa P jStar F t) →
        respK0SqMinus P jStar F t * respLsqMinus P jStar F t e ≤
            (2 * Cc + 2 * Cc * Ce) * respKappa P jStar F s ∧
          respK0SqPlus P jStar F t * respLsqPlus P jStar F t e ≤
            (2 * Cc + 2 * Cc * Ce) * respKappa P jStar F s := by
  intro ε σ Cglob Cprof Csrc Bresp H P E Ψ Kg Src B jStar F s t hε hσ raw e hED hKm hKp
  obtain ⟨hk1, hks⟩ :=
    respKappa_persistence_of_raw d hd γ hγ S hS ε σ hε hσ Cglob Cprof Csrc Bresp H P E Ψ Kg Src
      B jStar F s t raw
  obtain ⟨hLm0, hLp0, hLm, hLp⟩ := respLsq_bounds_of_energyDefect Ce P jStar F s t e hED
  obtain ⟨hKm0, hKp0⟩ := respK0Sq_nonneg P jStar F t
  exact ⟨respK0Sq_mul_Lsq_le_arith hCc hCe hk1 hks hKm0 hKm hLm0 hLm,
    respK0Sq_mul_Lsq_le_arith hCc hCe hk1 hks hKp0 hKp hLp0 hLp⟩

/-- **The constant chain**. `K_0^2 ≤ C_c √κ_t` (`RespCalibrated`, `Ehat_t^± ≤ C_c √κ_t M_0`, via
`blockSpecBound` of the normalized block), `(L^±)^2 = 2(respEJ± + 1) ≤ 2 + 2C_e √κ_s`
(`RespEnergyDefect`), alternatively `(L^±)^2 ≤ C_c √κ_t · C_l √κ_s` (`RespLoadMean`).  Closing
to `C κ_s` needs `κ ≥ 1` (`canonicalImbalance` is the operator norm of a block whose product with
its swap-inverse is `I`, so `≥ 1`) and `κ_t ≤ C κ_s` from `RawOutput` (persistence,
`adaptedMean_persistence` EccentricityScaleDecay:134 + `adaptedMean_antitone`, `t = s + H`).  If
`κ_t ≤ C κ_s` is NOT derivable from `RawOutput`, then the paper's `K_0 ≤ C κ_s^{1/4}`
(`p.response.transfer`) would be a statement-level gap.

The two premises `hε`, `hσ` are binders of this theorem; the matrix step is
`normalizedBlock_le_scale` followed by `blockSpecBound_le_of_loewner`, and the constant is
`C = 2 C_c (1 + C_e)`, exactly as (b) below predicts.  A residual gap remains: the statement
(`WeakEstimateAssembly.lean`) and the route assembly `response_weak_estimate_of_route` still do not
carry `hε`/`hσ`, so the consumer of this theorem cannot discharge them.  The points
below record the derivation.
(a) `1 ≤ κ_t` and `κ_t ≤ κ_s` ARE derivable, with `C = 1`, from `RawOutput` alone -- they are
  conjuncts 1 and 2 of `response_imbalance_comparison`
  (`HCPoly/Entry/Response/Core/ResponseImbalanceComparison.lean`,
  sorry-free) -- BUT only once the two scale-selection premises `hε : ε ∈ Set.Ioc 0 S.eps0` and
    `hσ : σ ∈ Set.Ioc 0 ε` are available.  This statement and the statement
    (`WeakEstimateAssembly.lean`) do not carry them.  See the note above this section and the
  compiled `respKappa_persistence_of_raw`.
(b) NO new inequality has to be added to `RespCalibrated`.  With `hε`/`hσ` restored, the chain
  closes with the explicit constant `C = 2 C_c (1 + C_e)`; that is the compiled
    `respK0Sq_mul_Lsq_le_kappa_of_calibration_step` above, whose only further input is the routine
  matrix step `K_0^± ≤ C_c √κ_t` already contained in `RespCalibrated`.
(c) The residual gap is therefore a PREMISE gap at the statement; it cannot be repaired inside
  this file, because its statement is fixed. -/
theorem respK0Sq_mul_Lsq_le_kappa (d : ℕ) (hd : 2 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1)
    (S : SelectionData) (hS : S.Selects d γ) (Cc Ce Cl : ℝ) (hCc : 0 < Cc) (hCe : 0 < Ce)
    (_hCl : 0 < Cl) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (ε σ Cglob Cprof Csrc Bresp : ℝ) (H : ℕ) (P : Measure (CoeffSpace d)) (E : BlockMat d)
        (Ψ : ℝ → ℝ) (Kg : ℝ) (Src : CoeffSpace d → ℝ) (B : ℝ) (jStar : ℕ) (F : BlockMat d)
        (s t : ℤ),
        ε ∈ Set.Ioc (0 : ℝ) S.eps0 → σ ∈ Set.Ioc (0 : ℝ) ε →
        RawOutput d γ S ε σ Cglob Cprof Csrc H Bresp P E Ψ Kg Src B jStar F s t →
        RespCalibrated Cc P jStar F s t →
        ∀ e : Vec d, vecDot e e = 1 →
          RespEnergyDefect Ce P jStar F s t e →
          RespLoadMean Cl P jStar F s t e →
          0 ≤ respK0SqMinus P jStar F t ∧ 0 ≤ respLsqMinus P jStar F t e ∧
          0 ≤ respK0SqPlus P jStar F t ∧ 0 ≤ respLsqPlus P jStar F t e ∧
          respK0SqMinus P jStar F t * respLsqMinus P jStar F t e ≤ C * respKappa P jStar F s ∧
          respK0SqPlus P jStar F t * respLsqPlus P jStar F t e ≤ C * respKappa P jStar F s := by
  refine ⟨2 * Cc + 2 * Cc * Ce, by nlinarith only [hCc, hCe], ?_⟩
  intro ε σ Cglob Cprof Csrc Bresp H P E Ψ Kg Src B jStar F s t hε hσ raw hcal e _he hED _hLM
  let : NeZero d := ⟨by omega⟩
  -- `M_0 = diag(m, m^{-1})` is positive definite: `m = m(F)` is, by `raw.symm` and `raw.pos`.
  have hm : (explicitCanonicalMetric F).PosDef := Geometry.explicitCanonicalMetric_posDef raw.symm raw.pos
  have hM0 : (toFullBlockMat (respM0 F)).PosDef := respM0_full_posDef hm
  have hcnn : 0 ≤ Cc * Real.sqrt (respKappa P jStar F t) :=
    mul_nonneg hCc.le (Real.sqrt_nonneg _)
  obtain ⟨-, -, hcalm, hcalp, -, -⟩ := hcal
  -- The routine matrix step `K_0^± ≤ C_c √κ_t`: normalize the `RespCalibrated` upper sandwich
  -- by `M_0` and read the `sInf` off with `csInf_le`.
  have hKm : respK0SqMinus P jStar F t ≤ Cc * Real.sqrt (respKappa P jStar F t) :=
    blockSpecBound_le_of_loewner _ _ hcnn
      (normalizedBlock_le_scale _ _ hM0 _ hcalm)
  have hKp : respK0SqPlus P jStar F t ≤ Cc * Real.sqrt (respKappa P jStar F t) :=
    blockSpecBound_le_of_loewner _ _ hcnn
      (normalizedBlock_le_scale _ _ hM0 _ hcalp)
  obtain ⟨hKm0, hKp0⟩ := respK0Sq_nonneg P jStar F t
  obtain ⟨hLm0, hLp0, -, -⟩ := respLsq_bounds_of_energyDefect Ce P jStar F s t e hED
  obtain ⟨hprodm, hprodp⟩ :=
    respK0Sq_mul_Lsq_le_kappa_of_calibration_step d hd γ hγ S hS Cc Ce hCc hCe
      ε σ Cglob Cprof Csrc Bresp H P E Ψ Kg Src B jStar F s t hε hσ raw e hED hKm hKp
  exact ⟨hKm0, hLm0, hKp0, hLp0, hprodm, hprodp⟩

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## Real arithmetic for the weak-estimate assembly

This leaf module collects the purely real identities and inequalities that are used when
the weak-norm estimate is assembled from its pieces.  Nothing here mentions a measure, a
matrix, a block or a function space: every statement is an identity or an inequality
between real numbers.
-/

namespace HCPolySupport.HighContrast.Multiscale

noncomputable section

/-- `(3 ^ (-(t / 2))) ^ 2 = 3 ^ (-t)` for the real power. -/
theorem rpow_half_sq (t : ℝ) : ((3 : ℝ) ^ (-(t / 2))) ^ 2 = (3 : ℝ) ^ (-t) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3),
    show -(t / 2) * ((2 : ℕ) : ℝ) = -t by ring]

/-- Square of a product of two square roots:
`(c * √x * √y * s) ^ 2 = c ^ 2 * (x * y) * s ^ 2`. -/
theorem sqrt_mul_sq (c x y s : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (c * Real.sqrt x * Real.sqrt y * s) ^ 2 = c ^ 2 * (x * y) * s ^ 2 := by
  rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hx, Real.sq_sqrt hy]
  ring

/-- Square of a scaled square root: `(c * √v) ^ 2 = c ^ 2 * v`. -/
theorem scaled_sqrt_sq (c v : ℝ) (hv : 0 ≤ v) : (c * Real.sqrt v) ^ 2 = c ^ 2 * v := by
  rw [mul_pow, Real.sq_sqrt hv]

/-- `3 ^ (-(1 / 2)) < 1`, hence `0 < 1 - 3 ^ (-(1 / 2))`. -/
theorem one_sub_rpow_pos : (0 : ℝ) < 1 - (3 : ℝ) ^ (-(1 / 2 : ℝ)) :=
  sub_pos.mpr <| Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)

/-- `(η ^ (1 / (2 * Q))) ^ 2 = η ^ (1 / Q)` for `η ≥ 0` and `Q > 0`. -/
theorem rpow_sq_eq (η : ℝ) (hη : 0 ≤ η) (Q : ℝ) (hQ : 0 < Q) :
    (η ^ ((1 : ℝ) / (2 * Q))) ^ 2 = η ^ ((1 : ℝ) / Q) := by
  have hQne : Q ≠ 0 := ne_of_gt hQ
  have h2Qne : (2 : ℝ) * Q ≠ 0 := mul_ne_zero (by norm_num) hQne
  have hexp : (1 : ℝ) / (2 * Q) * ((2 : ℕ) : ℝ) = 1 / Q := by
    field_simp [hQne, h2Qne]
    ring
  rw [← Real.rpow_natCast, ← Real.rpow_mul hη, hexp]

/-- For `0 < η ≤ 1` the exponent map is antitone, so `η ^ (2 / Q) ≤ η ^ (1 / Q)`. -/
theorem rpow_two_le_one (η : ℝ) (hη0 : 0 < η) (hη1 : η ≤ 1) (Q : ℝ) (hQ : 0 < Q) :
    η ^ ((2 : ℝ) / Q) ≤ η ^ ((1 : ℝ) / Q) :=
  Real.rpow_le_rpow_of_exponent_ge hη0 hη1
    (div_le_div_of_nonneg_right (by norm_num : (1 : ℝ) ≤ 2) hQ.le)

/-- Final constant bookkeeping for the weak estimate.  If `X ≤ (A * z ^ 2 + B * θ ^ 2) * κ`
and all of `A`, `B`, `θ`, `z`, `κ` are nonnegative, then
`X ≤ (√(B + 1) * (θ + √(A + 1) * z) * √κ) ^ 2`. -/
theorem constant_arith (A B θ z κ X : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hθ : 0 ≤ θ)
    (hz : 0 ≤ z) (hκ : 0 ≤ κ) (hX : X ≤ (A * z ^ 2 + B * θ ^ 2) * κ) :
    X ≤ (Real.sqrt (B + 1) * (θ + Real.sqrt (A + 1) * z) * Real.sqrt κ) ^ 2 := by
  have hB1 : (0 : ℝ) ≤ B + 1 := by linarith only [hB]
  have hA1 : (0 : ℝ) ≤ A + 1 := by linarith only [hA]
  have hsB : (Real.sqrt (B + 1)) ^ 2 = B + 1 := Real.sq_sqrt hB1
  have hsA : (Real.sqrt (A + 1)) ^ 2 = A + 1 := Real.sq_sqrt hA1
  have hsk : (Real.sqrt κ) ^ 2 = κ := Real.sq_sqrt hκ
  have hsAs : (0 : ℝ) ≤ Real.sqrt (A + 1) := Real.sqrt_nonneg _
  have hcross : (0 : ℝ) ≤ 2 * (B + 1) * θ * (Real.sqrt (A + 1) * z) := by
    have h : (0 : ℝ) ≤ (B + 1) * θ * (Real.sqrt (A + 1) * z) :=
      mul_nonneg (mul_nonneg hB1 hθ) (mul_nonneg hsAs hz)
    nlinarith only [h]
  have hBA : (0 : ℝ) ≤ B * A * z ^ 2 := mul_nonneg (mul_nonneg hB hA) (sq_nonneg z)
  have hBz : (0 : ℝ) ≤ B * z ^ 2 := mul_nonneg hB (sq_nonneg z)
  have hkey : A * z ^ 2 + B * θ ^ 2 ≤ (B + 1) * (θ + Real.sqrt (A + 1) * z) ^ 2 := by
    nlinarith only [hsA, hcross, hBA, hBz, sq_nonneg θ, sq_nonneg z]
  have hmain : (A * z ^ 2 + B * θ ^ 2) * κ
      ≤ ((B + 1) * (θ + Real.sqrt (A + 1) * z) ^ 2) * κ :=
    mul_le_mul_of_nonneg_right hkey hκ
  calc
    X ≤ (A * z ^ 2 + B * θ ^ 2) * κ := hX
    _ ≤ ((B + 1) * (θ + Real.sqrt (A + 1) * z) ^ 2) * κ := hmain
    _ = (Real.sqrt (B + 1) * (θ + Real.sqrt (A + 1) * z) * Real.sqrt κ) ^ 2 := by
          rw [mul_pow, mul_pow, hsB, hsk]

end

end HCPolySupport.HighContrast.Multiscale
end
