/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Base.BaseCaseAllScaleError
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Base.BaseCaseMStarStarError
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Base.InductionStart

/-!
# MultiscaleBaseBranch

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Provider: the frozen multiscale display on the base-case plateau

## THIS — what this module is NOT

This module is **NOT** the `m <= mStar M` branch of the frozen root, and it
**closes no branch of** `p.multiscale.estimate`.  The chartered complementary
branch of the sibling
`Provider.MultiscaleEstimate.multiscale_estimate_of_mStarStar`
(`MultiscaleEstimate/MultiscaleAbsorption.lean`, whose carried premise is
`mStarStar M < m` since the re-gate, option (i)) is now the range `m <=
mStarStar M` — exactly the range proved here.  What is proved here is the
frozen root's body on the strictly smaller range

```text
    m <= mStarStar M
```

(the BASE landmark, `e.mstarstar`), which is where the `m**`-gated base-case
error public consumed below
(`Provider.Base.exists_baseCaseMStarStarErrorConst`) reaches.  That is NOT the
maximal range of the base-case surface: the landmark-free all-scale public
(`Provider.Base.cutoffHomogenizationError_isOneSidedOrlicz_allScale`, the input
of section 3) supports the frozen display on the strictly larger range
`3^{cgamma m} <~ c(d) nu cgamma cstar^{-1} 2^{Cms}`, which reaches strictly
past `mStarStar M` — but, by the same arithmetic recorded in "Why the range
stops at `m**`" below, still falls strictly short of `mStar M`.  The complement
`mStarStar M < m <= mStar M` is **not** covered here; it is covered from the
other side, by re-gating `l.shom.continuity` and its downstream chain at
`mstarstar`, so that the sibling branch covers that band and this module's
range is exactly its complement.  The arithmetic reason why the base-case
surface cannot reach past `m**` is recorded in full in the section "Why the
range stops at `m**`" below.

## What is delivered

`multiscale_estimate_of_le_mStarStar` is the frozen root's statement body
(`Frozen/Section3/MultiscaleEstimate.lean`, between) **verbatim, binder for
binder and amplitude spelling for amplitude spelling**, with ONE premise
inserted:

```text
    m <= mStarStar M ->
```

immediately before `inductionState M (m - 1) E` — the same slot in which the
sibling inserts its `mStarStar M < m`.  Everything else is unchanged: the same
`exists Cms`, the same window `cstar^{-1} eps^{-Cms} <= E`, the same smallness
`cgamma <= (E^{-1})^{10}`, the same `s in [8 cgamma, 1]`, ONE `(Y, Z)` pair
serving the main conjunct AND the refinement clause, and the two amplitudes

```text
    Cms E s^{-1} sqrt(eps cgamma)   and   Cms eps (s^{-1})^2 exp(-E^{-3} cgamma^{-1}) .
```

**Two of the frozen root's binders are carried unconsumed.**
Both are carried because the frozen body's binder list is immutable — deleting
either would produce a different, strictly stronger theorem that no longer fits
the root — but neither is used by the proof:

* the induction state `Algsuperdiff.Frozen.Section3.inductionState M (m - 1) E`
  (the base-case error surface is unconditional in the state), and
* the smallness premise `cgamma <= (E^{-1})^{10}`, which occurs exactly once in
  this file, at the `intro` of section 2's proof, and is consumed by nothing.

Both are therefore introduced under underscored names (`_hS`, `_hgammaE`); the
proof is machine-verified to compile verbatim with both binders deleted from
the statement.  That is a strength, not a gap: the display is proved from
strictly less than the root offers, on both counts.

## The route (for the display of section 2)

Three proved publics and one arithmetic comparison; no analysis is re-proved.
Section 3's own input is named in its docstring.

1. `Provider.Base.exists_baseCaseMStarStarErrorConst` — the corrected
   `m <= m**` base-case error tail: a one-sided `Gamma_2` bound (no
   deterministic shift) at the amplitude
   `C . cstarPlus^{-1/2} . cgamma^{1/2} . sqrt(baseLoss d s)` on the
   literal source range `0 < s < 1`.
2. `Provider.Base.isOneSidedOrlicz_cutoffHomogenizationError_of_le`
   — the `s = 1` endpoint of the frozen root's
   closed window `[8 cgamma, 1]`, reached WITHOUT evaluating `baseLoss` at `1`:
   the bound is read at the interior scale `min s (1/2)` and transported up by
   the proved a.e. antitonicity of the observable in `s`
   (`Provider.ErrorComparison.cutoffHomogenizationError_ae_antitone`,
   `e.mathcalE.monotone.ordered`).  The cost is the factor `(min s (1/2))^{-1}
   <= 2 s^{-1}`.
3. `Provider.Scales.sqrt_baseLoss_le` (`Scales/BaseLoss.lean`) and
   `Provider.Base.sqrt_cstar_le_sqrt_cstarPlus` (`Base/InductionStart.lean`,
   `cstar <= c+` from `d cstar <= c+` and `d >= 2`) and
   `Provider.Disorder.cstar_le_three_halves` — the three scalar comparisons.
4. The amplitude comparison (section 1 below).  Writing `K := sqrt (1 + 6 d log
   3)` for the base-loss constant, the delivered constant is `Cms = max 4 (4
   K)`, chosen before every model and scale parameter.

The witnesses are `(Y, Z) = (mathcal E, 0)`: the second lane is not used at all
on this range, so `Z` is identically zero and its `Gamma_{1/2}` tail is
vacuous.  The refinement clause is discharged unconditionally from the same
`Gamma_2` component (its `s <= Cms eps` hypothesis is consumed by nothing),
which is what makes one `(Y, Z)` pair serve both conjuncts.

## Why the range stops at `m**`

Both halves of the deterministic bridge behind the base case
(`Provider.Base.ae_cutoffHomogenizationError_sq_le_cutoffPlateauAmplitude_add_mass`)
are governed by the SAME all-scale core

```text
    nu^{-1} cgamma^{-1/2} 3^{cgamma m}
```

(`Provider.Base.sqrt_cutoffPlateauAmplitude_le_allScale`,
`sqrt_cutoffMassTailScale_le_allScale`), so the best `Gamma_2` amplitude the
base-case surface can produce at scale `m` is `C(d). nu^{-1} cgamma^{-1/2}
3^{cgamma m}. sqrt(baseLoss d s)`.

```text
    m <= mStarStar M :  <= C(d) cstarPlus^{-1/2} cgamma^{1/2}   (the gamma^3 threshold)
    m <= mStar M     :  <= C(d) cstarPlus^{-1/2}                (the gamma^1 threshold)
```

(`Provider.Base.CutoffBaseTailArithmetic`, `allScaleCore_le_mStarStar` and
`allScaleCore_le_mStar`).

```text
    Cms E s^{-1} sqrt(eps cgamma) >= Cms cstar^{-1} cgamma^{1/2} s^{-1}
```

(because `cstar^{-1} eps^{-Cms} <= E` forces `E sqrt(eps) >= cstar^{-1}`), and
`sqrt(baseLoss d s) <= K s^{-1}`.  Hence the comparison needed at scale `m` is

```text
    nu^{-1} cgamma^{-1/2} 3^{cgamma m}  <~  cstar^{-1} cgamma^{1/2} ,
```

i.e. a `cgamma^2` threshold `3^{2 cgamma m} <~ nu^2 cgamma^2 cstar^{-2}`.  The
`m**` threshold (`cgamma^3`) is stronger and clears it — that is this file.  The
`m*` threshold (`cgamma^1`) does NOT: at `m = mStar M` the base-case amplitude
is `cgamma`-free while the frozen target still carries `cgamma^{1/2}`, and
`cgamma` is unbounded below relative to `cstar` (the model constrains only `0 <
cgamma <= 1/4`, `0 < cstar <= 3/2`, and the root's own window constrains
`cgamma` from ABOVE only).  So the gap is a genuine factor `sqrt(cstar / cgamma)
-> infinity`, not a slack loss: no choice of `Cms` closes it, and the plateau
layer cannot reach the range `mStarStar M < m <= mStar M` at all.

**Which step carries the "no choice of `Cms`" conclusion.**  NOT the lower
bound just displayed: the window's own endpoint `eps <= 1/2` makes that lower
bound itself grow like `2^{Cms}` (from `E sqrt(eps) >= cstar^{-1} eps^{-Cms +
1/2} >= cstar^{-1} 2^{Cms - 1/2}`), so a larger `Cms` does inflate the target
and the lower-bound computation alone does not close the question.

```text
    E sqrt(eps cgamma) <= cgamma^{2/5}
```

— in full, `(E sqrt(eps cgamma))^{10} = E^{10} eps^5 cgamma^5 <= E^{10}
cgamma^5 <= cgamma^{-1} cgamma^5 = cgamma^4`, the last step by `cgamma <=
(E^{-1})^{10}`.  Section 3's docstring records the `eps`-free case `E
sqrt(cgamma) <= cgamma^{2/5}` of the same bound.  The ceiling tends to `0` with
`cgamma`, whereas the `m*` collapse above leaves the base-case amplitude
bounded below by a `cgamma`-free, `eps`-free constant.  Ceiling against floor is
the whole argument; the `Cms`-monotone lower bound is only its motivation.
This also subsumes the earlier negative finding about
`Provider.Base.exists_baseCaseMStarErrorConst` (its deterministic shift `2`):
the obstruction is not the shift, it is the amplitude.  In shift-free form: on
the whole range `m <= mStar M` the base-case surface gives a one-sided
`Gamma_2` bound with no deterministic shift and no `cgamma` factor, and that is
the best it gives.

## The situation in the source

* `p.base.case` itself splits exactly here: its `m <= mstarstar` consequence
  `e.basecase.homogenization` is `E <= O_{Gamma_2}(C cstar^{-1/2}
  cgamma^{1/2})` — with the `cgamma^{1/2}` — while its `m <= mstar` consequence
  `e.basecase.diffusivity` is only `E <= 2 + O_{Gamma_2}(C cstar^{-1/2})` —
  shift `2`, no `cgamma`.  The proposition's own final clause starts the
  induction at `mstarstar`, not at `mstar`: "`S(mstarstar, C cstar^{-1/2})` is
  valid" (again).
* The printed proof of `p.multiscale.estimate` never mentions either landmark;
  the gate `m_0 in (mstar, infinity)` is inherited from its ingredients
  (`l.shom.continuity`, `p.propagate.diffusivity.lower. bound`,
  `l.approximate.recurrence.formula`, `p.bfA.multiscalebound`).  NOTE:
  `p.cg.ellipticity.bounds` itself is NOT landmark-gated — its statement
  (label, hypotheses) assumes only `m in Z`, `E in [1,infinity)` and the
  validity of `S(m-1,E)`.  What sits is the landmark binder `m - 1 >= mstar` of
  the interior proposition `p.bfA.multiscalebound` (label), from which
  `p.cg.ellipticity.bounds` is then deduced.
* The only printed small-`m` device in the whole chain is for
  `p.cg.ellipticity.bounds`: "the statement of the proposition is immediate for
  `m <= mstar`".  It works there because that display's leading term is a
  deterministic constant `C`, which is exactly what the shift `2` of
  `e.basecase.diffusivity` supplies.  It cannot be transplanted to
  `e.complete.wrapping`, which has no deterministic term at all.

So the range `mStarStar M < m <= mStar M` is open in the source as printed.
The correction is on the other side: `l.shom.continuity`'s printed
`m0 in (mstar, infty) cap Z` becomes `m0 in (mstarstar, infty) cap Z`, its
proof extended below `mstar` by the two printed devices, and the upstream
integration re-gated the same way.  The analysis above is therefore a record of
what the base-case surface reaches; the band is closed by the re-gated sibling,
not from this side.
-/

namespace Algsuperdiff.Section3.Provider.MultiscaleEstimate

open _root_.MeasureTheory
open _root_.HCPolySupport

noncomputable section

variable {d : ℕ}

/-! ## 1. The two scalar gates of the window -/

/-- The root's window `cstar^{-1} eps^{-Cms} <= E` forces `E sqrt(eps)` above
`cstar^{-1}`, for every exponent `Cms >= 1/2`: the loss `sqrt(eps) <= 1` is
paid by the window's own `eps^{-Cms}`. -/
private theorem cstar_inv_le_mul_sqrt {cstarInv epsilon Cms Eval : ℝ}
    (hcstarInv : 0 ≤ cstarInv) (heps0 : 0 < epsilon) (heps1 : epsilon ≤ 1)
    (hCms : (1 : ℝ) / 2 ≤ Cms)
    (hwin : cstarInv * epsilon ^ (-Cms) ≤ Eval) :
    cstarInv ≤ Eval * Real.sqrt epsilon := by
  have hone : (1 : ℝ) ≤ epsilon ^ (-Cms) * Real.sqrt epsilon := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add heps0]
    exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos heps0 heps1 (by linarith)
  have hstep : cstarInv * (epsilon ^ (-Cms) * Real.sqrt epsilon) ≤
      Eval * Real.sqrt epsilon := by
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right hwin (Real.sqrt_nonneg _)
  calc cstarInv = cstarInv * 1 := (mul_one _).symm
    _ ≤ cstarInv * (epsilon ^ (-Cms) * Real.sqrt epsilon) :=
        mul_le_mul_of_nonneg_left hone hcstarInv
    _ ≤ Eval * Real.sqrt epsilon := hstep

/-- The same gate for the refinement clause, where the loss is the full
`eps <= 1` rather than `sqrt(eps)`; it needs `Cms >= 1`. -/
private theorem cstar_inv_le_mul_self {cstarInv epsilon Cms Eval : ℝ}
    (hcstarInv : 0 ≤ cstarInv) (heps0 : 0 < epsilon) (heps1 : epsilon ≤ 1)
    (hCms : (1 : ℝ) ≤ Cms)
    (hwin : cstarInv * epsilon ^ (-Cms) ≤ Eval) :
    cstarInv ≤ Eval * epsilon := by
  have hone : (1 : ℝ) ≤ epsilon ^ (-Cms) * epsilon := by
    nth_rewrite 2 [show epsilon = epsilon ^ (1 : ℝ) from (Real.rpow_one epsilon).symm]
    rw [← Real.rpow_add heps0]
    exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos heps0 heps1 (by linarith)
  have hstep : cstarInv * (epsilon ^ (-Cms) * epsilon) ≤ Eval * epsilon := by
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right hwin heps0.le
  calc cstarInv = cstarInv * 1 := (mul_one _).symm
    _ ≤ cstarInv * (epsilon ^ (-Cms) * epsilon) :=
        mul_le_mul_of_nonneg_left hone hcstarInv
    _ ≤ Eval * epsilon := hstep

/-- The interior scale `min s (1/2)` costs only the factor `2` in `s^{-1}`. -/
private theorem inv_min_half_le {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    (min s (1 / 2))⁻¹ ≤ 2 * s⁻¹ := by
  have hu0 : (0 : ℝ) < min s (1 / 2) := lt_min hs (by norm_num)
  have hhalf : s / 2 ≤ min s (1 / 2) := le_min (by linarith) (by linarith)
  calc (min s (1 / 2))⁻¹ ≤ (s / 2)⁻¹ := by
        rw [inv_le_inv₀ hu0 (by linarith : (0 : ℝ) < s / 2)]
        exact hhalf
    _ = 2 * s⁻¹ := by
        rw [div_eq_mul_inv, mul_inv, inv_inv]
        ring

/-! ## 2. The display on the base-case plateau -/

/-- **The frozen `p.multiscale.estimate` body on the range `m <= mStarStar M`.**

This is `Algsuperdiff.Frozen.Section3.multiscale_estimate`'s statement body
verbatim with the single premise `m <= mStarStar M` inserted immediately before
the induction state.  It is NOT the chartered `m <= mStar M` branch; see the
module header, whose section "Why the range stops at `m**`" records why the
range `mStarStar M < m <= mStar M` is unreachable from the base-case surface.

The proof reads the corrected `m <= m**` base-case tail at the interior scale
`min s (1/2)`, transports it to the closed endpoint `s = 1` by the proved a.e.
antitonicity, and compares amplitudes: the base amplitude `C2 cstarPlus^{-1/2}
cgamma^{1/2} sqrt(baseLoss d (min s (1/2)))` is at most `2 K cstar^{-1/2}
cgamma^{1/2} s^{-1}`, while the two frozen targets are at least `Cms cstar^{-1}
cgamma^{1/2} s^{-1}` by the window gate; with `sqrt(cstar) <= 2` the choice
`Cms = max 4 (4 K)` clears both. -/
theorem multiscale_estimate_of_le_mStarStar (d : ℕ) :
    ∃ Cms : ℝ, 0 < Cms ∧
      ∀ (M : ABKModel d) (m : ℤ)
        (E : {E : ℝ // 1 ≤ E}),
        m ≤ mStarStar M →
        Algsuperdiff.Frozen.Section3.inductionState M (m - 1) E →
        ∀ epsilon : ℝ, epsilon ∈ Set.Ioc 0 (1 / 2) →
          (Disorder.cstar M)⁻¹ * epsilon ^ (-Cms) ≤ (E : ℝ) →
          M.gamma ≤ ((E : ℝ)⁻¹) ^ 10 →
          ∀ s : ℝ, ∀ hsWindow : s ∈ Set.Icc (8 * M.gamma) 1,
            ∃ Y Z : Cutoff.CutoffSample d → ℝ,
              Probability.IsTwoTermBigOWithWitnesses
                  (Cutoff.cutoffSampleLaw M).toMeasure
                  (HCPolySupport.IndependentSums.gammaSigma 2)
                  (HCPolySupport.IndependentSums.gammaSigma (1 / 2))
                  (Observable.cutoffHomogenizationError M m
                    ⟨s,
                      (mul_pos (by norm_num : (0 : ℝ) < 8)
                        M.shellPrefix.gamma_pos).trans_le hsWindow.1⟩)
                  Y Z
                  (Cms * (E : ℝ) * s⁻¹ *
                    Real.sqrt (epsilon * M.gamma))
                  (Cms * epsilon * (s⁻¹) ^ 2 *
                    Real.exp
                      (-(((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹))) ∧
                (s ≤ Cms * epsilon →
                  HCPolySupport.IndependentSums.IsBigOWith
                    (Cutoff.cutoffSampleLaw M).toMeasure
                    (HCPolySupport.IndependentSums.gammaSigma 2)
                    Y
                    (Cms * epsilon * (E : ℝ) * s⁻¹ *
                      Real.sqrt M.gamma)) := by
  obtain ⟨C2, hC2pos, hbase⟩ := Provider.Base.exists_baseCaseMStarStarErrorConst d
  have hKpos : (0 : ℝ) < Real.sqrt (1 + 6 * (d : ℝ) * Real.log 3) := by
    refine Real.sqrt_pos_of_pos ?_
    have h : (0 : ℝ) ≤ 6 * (d : ℝ) * Real.log 3 :=
      mul_nonneg (by positivity) (Real.log_nonneg (by norm_num))
    linarith
  refine ⟨max 4 (4 * C2 * Real.sqrt (1 + 6 * (d : ℝ) * Real.log 3)),
    lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
  intro M m E hm _hS epsilon hepsilon hwin _hgammaE s hsWindow
  set K : ℝ := Real.sqrt (1 + 6 * (d : ℝ) * Real.log 3) with hKdef
  set Cms : ℝ := max 4 (4 * C2 * K) with hCmsdef
  have hCms4 : (4 : ℝ) ≤ Cms := le_max_left _ _
  have hCmsK : 4 * C2 * K ≤ Cms := le_max_right _ _
  have hCms0 : (0 : ℝ) < Cms := lt_of_lt_of_le (by norm_num) hCms4
  have hgam : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hs0 : (0 : ℝ) < s :=
    (mul_pos (by norm_num : (0 : ℝ) < 8) hgam).trans_le hsWindow.1
  have hs1 : s ≤ 1 := hsWindow.2
  have hsinv : (0 : ℝ) < s⁻¹ := inv_pos.mpr hs0
  have heps0 : (0 : ℝ) < epsilon := hepsilon.1
  have heps1 : epsilon ≤ 1 := by linarith [hepsilon.2]
  have hEpos : (0 : ℝ) < (E : ℝ) := lt_of_lt_of_le zero_lt_one E.2
  have hcstar : (0 : ℝ) < Disorder.cstar M := (Disorder.cstar_characterization M).1
  have hsqcs : (0 : ℝ) < Real.sqrt (Disorder.cstar M) := Real.sqrt_pos.mpr hcstar
  have hgamsqrt : (0 : ℝ) ≤ Real.sqrt M.gamma := Real.sqrt_nonneg _
  -- the interior scale of the base-case range
  have hu0 : (0 : ℝ) < min s (1 / 2) := lt_min hs0 (by norm_num)
  have hu1 : min s (1 / 2) < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  -- the base-case tail at the interior scale, transported to the closed endpoint
  have htransport := Provider.Base.isOneSidedOrlicz_cutoffHomogenizationError_of_le
    M m hu0 (min_le_left s (1 / 2))
    (hbase M m hm ⟨min s (1 / 2), ⟨hu0, hu1⟩⟩)
  obtain ⟨-, hApos, hXmeas, htail⟩ := htransport
  -- the amplitude comparison
  have hlossle : Real.sqrt (baseLoss d ⟨min s (1 / 2), ⟨hu0, hu1⟩⟩) ≤ K * (2 * s⁻¹) := by
    refine le_trans (Provider.Scales.sqrt_baseLoss_le d ⟨min s (1 / 2), ⟨hu0, hu1⟩⟩) ?_
    exact mul_le_mul_of_nonneg_left (inv_min_half_le hs0 hs1) hKpos.le
  have hcpinv : (Real.sqrt (Disorder.cstarPlus M))⁻¹ ≤
      (Real.sqrt (Disorder.cstar M))⁻¹ := by
    rw [inv_le_inv₀ (Real.sqrt_pos.mpr (Disorder.cstarPlus_pos M)) hsqcs]
    exact Provider.Base.sqrt_cstar_le_sqrt_cstarPlus M
  have hsqcsle : Real.sqrt (Disorder.cstar M) ≤ 2 := by
    have h := Real.sqrt_le_sqrt
      (show Disorder.cstar M ≤ 2 ^ 2 by
        linarith [Provider.Disorder.cstar_le_three_halves M])
    rwa [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)] at h
  have hhalfinv : (2 : ℝ)⁻¹ ≤ (Real.sqrt (Disorder.cstar M))⁻¹ := by
    rw [inv_le_inv₀ (by norm_num : (0 : ℝ) < 2) hsqcs]
    exact hsqcsle
  have hcsinv : (Real.sqrt (Disorder.cstar M))⁻¹ * (Real.sqrt (Disorder.cstar M))⁻¹ =
      (Disorder.cstar M)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt hcstar.le]
  -- the common core estimate: the base amplitude against `2 K cstar^{-1/2} sqrt(cgamma) s^{-1}`
  have hcore : C2 * (Real.sqrt (Disorder.cstarPlus M))⁻¹ * Real.sqrt M.gamma *
      Real.sqrt (baseLoss d ⟨min s (1 / 2), ⟨hu0, hu1⟩⟩) ≤
      2 * C2 * K * ((Real.sqrt (Disorder.cstar M))⁻¹ * Real.sqrt M.gamma * s⁻¹) := by
    have h1 : C2 * (Real.sqrt (Disorder.cstarPlus M))⁻¹ * Real.sqrt M.gamma ≤
        C2 * (Real.sqrt (Disorder.cstar M))⁻¹ * Real.sqrt M.gamma :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hcpinv hC2pos.le) hgamsqrt
    have h0 : (0 : ℝ) ≤ C2 * (Real.sqrt (Disorder.cstarPlus M))⁻¹ * Real.sqrt M.gamma := by
      positivity
    calc C2 * (Real.sqrt (Disorder.cstarPlus M))⁻¹ * Real.sqrt M.gamma *
          Real.sqrt (baseLoss d ⟨min s (1 / 2), ⟨hu0, hu1⟩⟩)
        ≤ C2 * (Real.sqrt (Disorder.cstarPlus M))⁻¹ * Real.sqrt M.gamma * (K * (2 * s⁻¹)) :=
          mul_le_mul_of_nonneg_left hlossle h0
      _ ≤ C2 * (Real.sqrt (Disorder.cstar M))⁻¹ * Real.sqrt M.gamma * (K * (2 * s⁻¹)) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = 2 * C2 * K * ((Real.sqrt (Disorder.cstar M))⁻¹ * Real.sqrt M.gamma * s⁻¹) := by
          ring
  -- the window gate, in the two forms the two conjuncts need
  have hgate1 : (Disorder.cstar M)⁻¹ ≤ (E : ℝ) * Real.sqrt epsilon :=
    cstar_inv_le_mul_sqrt (inv_nonneg.mpr hcstar.le) heps0 heps1 (by linarith) hwin
  have hgate2 : (Disorder.cstar M)⁻¹ ≤ (E : ℝ) * epsilon :=
    cstar_inv_le_mul_self (inv_nonneg.mpr hcstar.le) heps0 heps1 (by linarith) hwin
  -- the square-root gate: the core constant against `Cms cstar^{-1}`
  have hAcore : 2 * C2 * K * (Real.sqrt (Disorder.cstar M))⁻¹ ≤
      Cms * (Disorder.cstar M)⁻¹ := by
    have hinv0 : (0 : ℝ) ≤ (Real.sqrt (Disorder.cstar M))⁻¹ := inv_nonneg.mpr hsqcs.le
    have h1 : 2 * C2 * K * (Real.sqrt (Disorder.cstar M))⁻¹ ≤
        Cms * (2 : ℝ)⁻¹ * (Real.sqrt (Disorder.cstar M))⁻¹ :=
      mul_le_mul_of_nonneg_right (by linarith [hCmsK]) hinv0
    have h2 : Cms * (2 : ℝ)⁻¹ * (Real.sqrt (Disorder.cstar M))⁻¹ ≤
        Cms * (Real.sqrt (Disorder.cstar M))⁻¹ * (Real.sqrt (Disorder.cstar M))⁻¹ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hhalfinv hCms0.le) hinv0
    have h3 : Cms * (Real.sqrt (Disorder.cstar M))⁻¹ *
        (Real.sqrt (Disorder.cstar M))⁻¹ = Cms * (Disorder.cstar M)⁻¹ := by
      rw [mul_assoc, hcsinv]
    linarith [h1, h2, h3.le, h3.ge]
  have hpos : (0 : ℝ) ≤ Real.sqrt M.gamma * s⁻¹ := by positivity
  -- the two amplitude comparisons
  have hmain : C2 * (Real.sqrt (Disorder.cstarPlus M))⁻¹ * Real.sqrt M.gamma *
      Real.sqrt (baseLoss d ⟨min s (1 / 2), ⟨hu0, hu1⟩⟩) ≤
      Cms * (E : ℝ) * s⁻¹ * Real.sqrt (epsilon * M.gamma) := by
    refine le_trans hcore ?_
    calc 2 * C2 * K * ((Real.sqrt (Disorder.cstar M))⁻¹ * Real.sqrt M.gamma * s⁻¹)
        = 2 * C2 * K * (Real.sqrt (Disorder.cstar M))⁻¹ *
            (Real.sqrt M.gamma * s⁻¹) := by ring
      _ ≤ Cms * (Disorder.cstar M)⁻¹ * (Real.sqrt M.gamma * s⁻¹) :=
          mul_le_mul_of_nonneg_right hAcore hpos
      _ ≤ Cms * ((E : ℝ) * Real.sqrt epsilon) * (Real.sqrt M.gamma * s⁻¹) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hgate1 hCms0.le) hpos
      _ = Cms * (E : ℝ) * s⁻¹ * (Real.sqrt epsilon * Real.sqrt M.gamma) := by ring
      _ = Cms * (E : ℝ) * s⁻¹ * Real.sqrt (epsilon * M.gamma) := by
          rw [Real.sqrt_mul heps0.le]
  have hrefine : C2 * (Real.sqrt (Disorder.cstarPlus M))⁻¹ * Real.sqrt M.gamma *
      Real.sqrt (baseLoss d ⟨min s (1 / 2), ⟨hu0, hu1⟩⟩) ≤
      Cms * epsilon * (E : ℝ) * s⁻¹ * Real.sqrt M.gamma := by
    refine le_trans hcore ?_
    calc 2 * C2 * K * ((Real.sqrt (Disorder.cstar M))⁻¹ * Real.sqrt M.gamma * s⁻¹)
        = 2 * C2 * K * (Real.sqrt (Disorder.cstar M))⁻¹ *
            (Real.sqrt M.gamma * s⁻¹) := by ring
      _ ≤ Cms * (Disorder.cstar M)⁻¹ * (Real.sqrt M.gamma * s⁻¹) :=
          mul_le_mul_of_nonneg_right hAcore hpos
      _ ≤ Cms * ((E : ℝ) * epsilon) * (Real.sqrt M.gamma * s⁻¹) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hgate2 hCms0.le) hpos
      _ = Cms * epsilon * (E : ℝ) * s⁻¹ * Real.sqrt M.gamma := by ring
  -- the two frozen amplitudes are positive
  have hK1 : (0 : ℝ) < Cms * (E : ℝ) * s⁻¹ * Real.sqrt (epsilon * M.gamma) :=
    lt_of_lt_of_le hApos hmain
  have hK2 : (0 : ℝ) < Cms * epsilon * (s⁻¹) ^ 2 *
      Real.exp (-(((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹)) := by positivity
  exact ⟨Observable.cutoffHomogenizationError M m
      ⟨s, (mul_pos (by norm_num : (0 : ℝ) < 8) M.shellPrefix.gamma_pos).trans_le hsWindow.1⟩,
    fun _ => 0,
    ⟨Probability.isAdmissibleTail_gammaSigma (by norm_num : (0 : ℝ) < 2),
      Probability.isAdmissibleTail_gammaSigma (by norm_num : (0 : ℝ) < 1 / 2),
      hK1, hK2, hXmeas, hXmeas, measurable_const, fun _ => by simp,
      htail.mono_scale hmain,
      Provider.Tail.isBigOWith_gammaSigma_const hK2.le hK2.le⟩,
    fun _ => htail.mono_scale hrefine⟩

end

end Algsuperdiff.Section3.Provider.MultiscaleEstimate
