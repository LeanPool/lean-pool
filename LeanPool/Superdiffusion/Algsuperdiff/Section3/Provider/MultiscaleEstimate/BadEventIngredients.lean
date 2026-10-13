/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.Section3.CoarseEllipticityBounds
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.BadEvents.BadEventMultiscaleConsumption
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Localization.ShomContinuity
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.ConclusionSeam3Closure
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.MultiscaleEstimate.BadEventCeiling
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Orlicz.TwoTermCalculus
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Tail.TailAssembly

/-!
# BadEventIngredients

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Provider: the two ingredient displays of the bad-event sum

Three displays are delivered:

1. `e.mathcalE.crude.bound` — the crude deterministic-plus-tails bound on
   `mathcal E^2_{s/4,infty,2}(cu_m; a_m, shom)`;
2. `e.badevent.indicator.propagate` — in the S form required, at `rho` free
   (hence at `rho = s/d`, which refutes the printed `rho = s/2d`);
3. the averaged-indicator display — by Markov plus the deterministic `[0,1]`
   ceiling, at the amplitude `C d s^{-1} cstar^{-1} 3^{5h} cgamma`.

Displays 2 and 3 are *independent* consumers of the same per-site probability
input: display 3 does **not** route through display 2.  It never forms the
indicator's `Gamma_rho` bound at all; it averages the per-site *measures* and
applies the ceiling engine of `BadEventCeiling.lean` directly.

This is a *provider endpoint only*.  It is not a source node, not a frozen
declaration, and it does not close `p.multiscale.estimate` or any part of it.

## 1. The crude bound and the gauge index

The consumed inputs are exactly two, both proved:

* the `q = 2` face of `l.mathcal.E.to.Lambdas`,
  `Provider.Tail.sq_cutoffHomogenizationError_le`, which gives
  `mathcal E^2 <= 2 Lambda shom^{-1} + 2 lambda^{-1} shom` almost surely at a
  free comparator scale; and
* the frozen `p.cg.ellipticity.bounds`
  (`Frozen.Section3.coarse_ellipticity_bounds`), consumed at `sigma = 1/7` (this
  is the unique `sigma` at which the endpoints' printed indices
  `Gamma_{(1-sigma)/3}` and `Gamma_{(1-sigma)/2}` become the crude route's
  `Gamma_{2/7}` and `Gamma_{3/7}`), `q = 2`, and its own `s`-slot pinned at
  `s/4`.

**Gauge index.**  `p.cg.ellipticity.bounds` normalizes both payloads at
`shom_{m-1}`, while the printed display reads them at `shom_m`: this is
exactly.  Both readings are provided:

* It is retained as **supporting A only**: it bounds a *different observable*,
  namely `Observable.cutoffHomogenizationErrorAtComparatorScale M m (m-1)` (the
  error normalized at `shom_{m-1}`), whereas every printed step of
  `p.multiscale.estimate` reads `Observable.cutoffHomogenizationError M m` (=
  the same observable at comparator scale `m`).  It therefore appears in no
  printed step and closes no fraction of any display; it is kept because it is
  certified, harmless, and the honest record of what the frozen ellipticity
  statement gives before any gauge conversion;
* `exists_crude_bound` is the display at the printed comparator scale `m`, at
  the cost of the two-sided running-diffusivity sandwich `shom_{m-1} <= 4
  shom_m` and `shom_m <= 4 . 3^{cgamma} shom_{m-1}` (ABK26).

* the binder `inductionState M m E` is at the multiscale root — the `m`-th
  error conjunct of the state at index `m` is the root's own conclusion, so no
  consumer at the root can supply it;
* the true statement is narrower: it is the two proved lemmas
  `Provider.Multiscale.sigmaBar_le_four_mul_sigmaBar` and
  `..._le_four_mul_rpow_mul_sigmaBar` that require the state at a scale `>= m`.
  The clause-direction reason was mis-stated as well: the frozen
  `inductionState M m0 E` quantifies both of its clauses over `m <= m0`, so
  what a conversion at the pair `(m-1, m)` needs is the *larger* scale inside
  the range; `l.shom.continuity` supplies exactly that at `m0 := m`, from a
  state at `m - 1`, because its own proof runs the recurrence up to `m0`.

Consuming `l.shom.continuity` at `m0 := m`, `m := m`, `n := m - 1` reads its
conjunct 2 (`shom_{m-1} shom_m^{-1} <= 4`) and its conjunct 3 (`shom_m <= 4.
3^{cgamma (m-n)} shom_{m-1}`, here at `m - n = 1`).  The complementary branch
is now `m <= mStarStar M`, which is where
`Provider.Base.exists_baseCaseMStarStarErrorConst` reaches.

**Constants.**  `l.shom.continuity` is an `exists C` statement, so
`exists_crude_bound` exports *two* dimensional constants: `Ccg`, the constant
of `p.cg.ellipticity.bounds` in which the display's own amplitudes are written,
and `Cshom`, the constant of `l.shom.continuity` appearing only in the
`E`-gate.  Each is obtained once, and neither is composed with the other.

**The `s`-window.**  The frozen ellipticity statement's `s`-slot carries the
window `s/4 in [cgamma/2 + exp(-Ccg^{-1} E^{-2} cgamma^{-1}), 1]`.  The chain
is `exp(7 Ccg) <= E` (the seam gate at `sigma = 1/7`) `=> 4 Ccg^2 <= E` `=> 2
Ccg <= sqrt E`; the fifth-root gate `E <= cgamma^{-1/5}` gives
`sqrt(cgamma^{-1}) >= E^2 sqrt E >= 2 Ccg E^2`, and `log x <= 2 sqrt x` turns
this into `log(cgamma^{-1}) <= Ccg^{-1} E^{-2} cgamma^{-1}`, i.e.
`exp(-Ccg^{-1} E^{-2} cgamma^{-1}) <= cgamma`; and `8 cgamma <= s` gives `s/4 -
cgamma/2 >= 3 cgamma/2 >= cgamma`.

At `sigma = 2/7` this is `(1 + log 2)^{7/2} < 6.4`.  `gammaTriangleConst` and
`gammaGrowthConst` are never invoked.

## 2. The split indicator display and the averaged-indicator display

The proved bad-event probability is a **sum of two** exponentials, and the
already-applied multiscale-parameter form
`Provider.BadEvents.exists_measureReal_compl_goodLocalEventAt_le_of_multiscaleParameters`
delivers it with all gates discharged:

```
P[ not Q(l, l-h, z) ]
  <= exp( - c cstar cgamma^{-1} 3^{-5h} ) + exp( - exp( c E^{-2} cgamma^{-1} ) ) .
```

The averaged-indicator display is proved by the engine of
`BadEventCeiling.lean` (Markov plus the deterministic `[0,1]` ceiling on the
normalized sum), never by the Orlicz triangle inequality and that module's
header.  The grid `3^l Zd cap cu_m` enters only as an arbitrary nonempty
`Finset (Vec d)`: the per-site bound is uniform in `z`, and the mean of an
average is the average of the means, so no grid cardinality and no union bound
occurs.

## 3. Consumer fit: the `[0,1]` ceiling, never an Orlicz product

The fourth term of `e.local.bad.events.summed` multiplies the crude
bound of display 1 against the bad-event max factor built from display 3,

```
    W  =  max_l 3^{-s(m-l)/2} ( avsum_z 1_{not Q(l,l-h,z)} )^{s/d} .
```

The `Gamma_1 x Gamma_1` lane fails separately, on amplitude.

The mechanism is `W`'s own pointwise `[0,1]` ceiling, exported by the sibling
as `weightedIndicatorAverage_rpow_mem_Icc` (and its base
`indicatorAverage_mem_Icc`): at `0 <= W <= 1` and `Y >= 0` one has `Y . W <= Y`
pointwise, so the `Gamma_1` lane and the `Gamma_{2/7}` lane of
`exists_crude_bound` pass through the product **unchanged**, at their printed
amplitudes and indices, and only the deterministic shift consumes `W`'s own
`Gamma_1` smallness.  The output is exactly the printed `Gamma_1 + Gamma_{2/7}`
shape of `e.local.bad.events.summed`.

The `Y >= 0` in that pointwise step is not free, and the two lanes pass through
at unchanged amplitude only **after** the free witness clamp
`Provider.Tail.isBigOWith_max_zero` (`Provider/Tail/TailSqrt.lean`) has replaced
each of the display's two Orlicz witnesses by `max 0 (.)` at the *same* scale:
the witnesses of `IsDeterministicShiftTwoTermOneSidedOrlicz` are only known to
be measurable and dominating, never nonnegative.  `ceiling_product` below
performs exactly that clamp and exports the finished composition, so the
consumer of `e.local.bad.events.summed` does not re-derive it.

## The scale gate on `m` (-bin statement change)

The landmark premise carried by every endpoint below is `mStarStar M < m`,
**not** the printed `m0 in (mstar, infty) cap Z` that it inherits from
`l.shom.continuity`.  Nothing else moved: the premise is forwarded verbatim to
`Provider.Localization.shom_continuity`, no proof step here consumes it, and no
frozen statement changes.

## Main results

*
`isDeterministicShiftTwoTermOneSidedOrlicz_of_ae_le`
* `Algsuperdiff.Section3.Provider.MultiscaleEstimate.quarter_pos_of_eight_gamma_le`
* `Algsuperdiff.Section3.Provider.MultiscaleEstimate.quarter_mem_crude_window`
* `Algsuperdiff.Section3.Provider.MultiscaleEstimate.exists_crude_bound`
* `Algsuperdiff.Section3.Provider.MultiscaleEstimate.exists_badEvent_indicatorAverage_rpow`
*
`Algsuperdiff.Section3.Provider.MultiscaleEstimate.exists_badEvent_indicatorAverage_rpow_at_s_div_d`

## In-repo consumed set

`Frozen.Section3.coarse_ellipticity_bounds`,
`Frozen.Section3.goodLocalEventAt`, `Frozen.Section3.inductionState`,
`Section3.mStar`, `Section3.lowerEllipticityProfile`,
`Provider.Localization.shom_continuity`,
`Provider.Tail.sq_cutoffHomogenizationError_le`,
`Provider.Tail.isBigOWith_of_ae_eq`, `Provider.Tail.isBigOWith_max_zero`,
`Provider.Tail.lowerEllipticityProfile_exponentTwo`,
`Provider.Tail.pow_five_le_inv_of_le_rpow`, `Provider.Tail.exponentTwo`,
`Provider.BadEvents.exists_measureReal_compl_goodLocalEventAt_le_of_multiscaleParameters`,
`Provider.BadEvents.scaleGapPos` (+ `_of_le`),
`Provider.BadEvents.measurableSet_goodLocalEvent`,
`Provider.Multiscale.isBigOWith_gammaSigma_add`,
`Provider.Orlicz.isBigOWith_gammaSigma_mono_exponent`,
`Provider.Orlicz.cstar_pos`, `Provider.Orlicz.sigmaBar_pos`,
`Observable.cutoffUpperEllipticity_nonneg`,
`Observable.cutoffLowerEllipticityInv_nonneg`,
`Observable.cutoffHomogenizationError` (+ its measurability),
`Observable.measurable_cutoffHomogenizationErrorAtComparatorScale`,
`Annealed.sigmaBar`, `Disorder.cstar`, `Cutoff.cutoffSampleLaw`,
`Cutoff.measurable_translateCutoffSample`, and from the sibling
`BadEventCeiling.lean` the items
`isBigOWith_gammaSigma_indicator_of_two_exp`,
`indicatorAverage_rpow_isBigOWith_gammaOne_of_two_exp` and
`weightedIndicatorAverage_rpow_mem_Icc`.

`Provider.Multiscale.sigmaBar_le_four_mul_sigmaBar` and
`Provider.Multiscale.sigmaBar_le_four_mul_rpow_mul_sigmaBar` are **no longer
consumed**: they carry the circular `inductionState`-at-`m` binder, and the
gauge conversions now come from `l.shom.continuity`.

## References

* ABK26: `e.mathcalE.crude.bound`, `e.badevent.indicator.propagate`, the
  averaged display, `e.bound.Lambdas.by.Es`, `p.cg.ellipticity.bounds`,
  `e.bad.event.Q.estimate`, `e.param.conditions.in.main`, `e.indc.O.sigma`,
  `e.Gamma.sigma.triangle`, `e.multGammasig`.
-/

namespace Algsuperdiff.Section3.Provider.MultiscaleEstimate

open _root_.MeasureTheory
open _root_.HCPolySupport
open _root_.HCPolySupport.IndependentSums
open _root_.Algsuperdiff.Section3.Cutoff
open _root_.Algsuperdiff.Section3.Provider.Tail

noncomputable section

variable {d : ℕ}

/-! ## 1. The null-set modification of a two-term display -/

section Transfer

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **The null-set modification.**  The source's additive notation `X <= b +
O_{Psi_1}(A_1) + O_{Psi_2}(A_2)` is carried by
`IsDeterministicShiftTwoTermOneSidedOrlicz`, whose domination clause is
*pointwise*; the `q = 2` face of `l.mathcal.E.to.Lambdas` delivers its
inequality only *almost surely*, because the cutoff observables are identified
with their literals off a null set.  Replacing the first witness by `X - b - Z`
on the null set removes the mismatch at no cost: the modified witness is almost
everywhere equal to the original, and the proved
`Provider.Tail.isBigOWith_of_ae_eq` (`Provider/Tail/TailSqrt.lean`) transports
the tail.

This is *not* `Provider.Tail.isTwoTermBigOWith_of_ae_le`
(`Provider/Tail/TailSqrt.lean`), which makes the same modification for
`Probability.IsTwoTermBigOWith`; the carrier here is
`Probability.IsDeterministicShiftTwoTermOneSidedOrlicz`, whose domination
clause carries the deterministic shift `b` that the source's additive notation
needs. -/
theorem isDeterministicShiftTwoTermOneSidedOrlicz_of_ae_le
    {X Y Z : Ω → ℝ} {b A₁ A₂ sigma₁ sigma₂ : ℝ}
    (hs₁ : 0 < sigma₁) (hs₂ : 0 < sigma₂) (hA₁ : 0 < A₁) (hA₂ : 0 < A₂)
    (hXm : Measurable X) (hYm : Measurable Y) (hZm : Measurable Z)
    (hY : IsBigOWith μ (gammaSigma sigma₁) Y A₁)
    (hZ : IsBigOWith μ (gammaSigma sigma₂) Z A₂)
    (hae : ∀ᵐ omega ∂μ, X omega ≤ b + Y omega + Z omega) :
    Probability.IsDeterministicShiftTwoTermOneSidedOrlicz μ (gammaSigma sigma₁)
      (gammaSigma sigma₂) X b A₁ A₂ := by
  classical
  set S : Set Ω := {omega | X omega ≤ b + Y omega + Z omega} with hSdef
  have hSmeas : MeasurableSet S :=
    measurableSet_le hXm ((measurable_const.add hYm).add hZm)
  set Y' : Ω → ℝ := S.piecewise Y (fun omega => X omega - b - Z omega) with hY'def
  have hY'meas : Measurable Y' :=
    Measurable.piecewise hSmeas hYm ((hXm.sub measurable_const).sub hZm)
  have hY'eq : Y' =ᵐ[μ] Y := by
    filter_upwards [hae] with omega homega
    exact Set.piecewise_eq_of_mem _ _ _ homega
  have hdom : ∀ omega, X omega ≤ b + Y' omega + Z omega := by
    intro omega
    by_cases homega : omega ∈ S
    · rw [hY'def, Set.piecewise_eq_of_mem _ _ _ homega]
      exact homega
    · rw [hY'def, Set.piecewise_eq_of_notMem _ _ _ homega]
      exact le_of_eq (by ring)
  exact Probability.deterministicShiftTwoTermOneSidedOrlicz_iff_exists.2
    ⟨Y', Z, Probability.isAdmissibleTail_gammaSigma hs₁,
      Probability.isAdmissibleTail_gammaSigma hs₂, hA₁, hA₂, hXm, hY'meas, hZm,
      hdom, Provider.Tail.isBigOWith_of_ae_eq hY'eq.symm hY, hZ⟩

end Transfer

/-! ## 2. The gauge index -/

/-- Nothing model-specific happens here; the source content is entirely in
`l.shom.continuity`, which the three consumers below supply.

The three consumers are the two named conversion lemmas and `exists_crude_bound`.
`exists_crude_bound` obtains `l.shom.continuity` itself rather than consuming
the two lemmas, because each of them is existential in its own copy of the
constant and Lean cannot see that the three copies coincide; routing all three
through this core keeps the mathematics in one place and the constant count at
two. -/
private theorem gauge_pair_of_shom (M : ABKModel d) (m : ℤ)
    (hratio : (Annealed.sigmaBar M (m - 1) : ℝ) * ((Annealed.sigmaBar M m : ℝ))⁻¹ ≤ 4)
    (hgrowth : (Annealed.sigmaBar M m : ℝ) ≤
      4 * (3 : ℝ) ^ (M.gamma * ((m : ℝ) - ((m - 1 : ℤ) : ℝ))) *
        (Annealed.sigmaBar M (m - 1) : ℝ)) :
    (Annealed.sigmaBar M (m - 1) : ℝ) ≤ 4 * (Annealed.sigmaBar M m : ℝ) ∧
      (Annealed.sigmaBar M m : ℝ) ≤
        4 * (3 : ℝ) ^ M.gamma * (Annealed.sigmaBar M (m - 1) : ℝ) := by
  have hposm : (0 : ℝ) < (Annealed.sigmaBar M m : ℝ) :=
    Provider.Orlicz.sigmaBar_pos M m
  refine ⟨?_, ?_⟩
  · rw [← div_eq_mul_inv, div_le_iff₀ hposm] at hratio
    linarith
  · have hexp : M.gamma * ((m : ℝ) - ((m - 1 : ℤ) : ℝ)) = M.gamma := by
      push_cast
      ring
    rwa [hexp] at hgrowth

/-! ## 4. The window bridge: the printed `8 cgamma <= s <= 1` implies the
frozen ellipticity window -/

/-- The pinned scale `s/4` is positive on the printed window `8 cgamma <= s`. -/
theorem quarter_pos_of_eight_gamma_le {gamma s : ℝ} (hgamma : 0 < gamma)
    (hs : 8 * gamma ≤ s) : (0 : ℝ) < s / 4 := by linarith

/-- **The window bridge.**  On the *printed* window `8 cgamma <= s <= 1` of
`e.mathcalE.crude.bound`, and under the `E`-gates the frozen
`p.cg.ellipticity.bounds` already carries at `sigma = 1/7`, the pinned scale
`s/4` lies in the frozen statement's own window

```
    s/4  in  [ cgamma/2 + exp(-Ccg^{-1} E^{-2} cgamma^{-1}) ,  1 ] .
```

The chain, all of it elementary:

* `exp(7 Ccg) <= E` and `exp(x) >= 1 + x` give
  `E >= (1 + 7Ccg/2)^2 >= (7Ccg/2)^2 >= 4 Ccg^2`, i.e. `sqrt E >= 2 Ccg`;
* `E <= cgamma^{-1/5}` gives `E^5 <= cgamma^{-1}`, hence
  `sqrt(cgamma^{-1}) >= sqrt(E^5) = E^2 sqrt E >= 2 Ccg E^2`;
* `log x <= 2 sqrt x` (from `log y <= y - 1` at `y = sqrt x`) then gives
  `log(cgamma^{-1}) <= 2 sqrt(cgamma^{-1}) <= Ccg^{-1} E^{-2} cgamma^{-1}`,
  i.e. `exp(-Ccg^{-1} E^{-2} cgamma^{-1}) <= cgamma`;
* finally `8 cgamma <= s` gives `s/4 - cgamma/2 >= 2 cgamma - cgamma/2 >= cgamma`.

So the crude-bound publics need no window binder: they take the printed `8
cgamma <= s <= 1`.

**The fifth-root gate is not an extra demand.**  `hEgamma : E <= cgamma^{-1/5}`
is *implied* by two binders the multiscale root already carries, namely
`cgamma <= (E^{-1})^{10}` and `1 <= E`: from the first,
`cgamma^{-1/5} >= ((E^{-1})^{10})^{-1/5} = E^2`, and `E^2 >= E` at `E >= 1`.  It
is kept as an explicit binder anyway, because the frozen
`p.cg.ellipticity.bounds` statement carries it in exactly this shape and the
consumers pass it through verbatim; the point of the note is that no consumer
acquires a new obligation by supplying it. -/
theorem quarter_mem_crude_window {Ccg E gamma s : ℝ}
    (hCcg : 0 < Ccg) (hE : 1 ≤ E)
    (hCE : Real.exp (Ccg / (1 / 7)) ≤ E)
    (hEgamma : E ≤ gamma ^ (-(1 / 5 : ℝ)))
    (hgamma : 0 < gamma) (hs8 : 8 * gamma ≤ s) (hs1 : s ≤ 1) :
    s / 4 ∈ Set.Icc
      (gamma / 2 + Real.exp (-(Ccg⁻¹ * (E⁻¹) ^ 2 * gamma⁻¹))) 1 := by
  have hE0 : (0 : ℝ) < E := lt_of_lt_of_le zero_lt_one hE
  have hginv : (0 : ℝ) < gamma⁻¹ := inv_pos.2 hgamma
  -- Step 1: the seam gate in the shape `exp(7 Ccg) <= E`.
  have hrw : Ccg / (1 / 7 : ℝ) = 7 * Ccg := by ring
  rw [hrw] at hCE
  -- Step 2: `4 Ccg^2 <= E`, from `exp x >= 1 + x` squared.
  have hxpos : (0 : ℝ) ≤ 7 * Ccg / 2 := by positivity
  have hx : 7 * Ccg / 2 ≤ Real.exp (7 * Ccg / 2) := by
    linarith [Real.add_one_le_exp (7 * Ccg / 2)]
  have hxx : (7 * Ccg / 2) * (7 * Ccg / 2) ≤
      Real.exp (7 * Ccg / 2) * Real.exp (7 * Ccg / 2) :=
    mul_le_mul hx hx hxpos (Real.exp_pos _).le
  have hexpsq : Real.exp (7 * Ccg / 2) * Real.exp (7 * Ccg / 2) = Real.exp (7 * Ccg) := by
    rw [← Real.exp_add]
    ring_nf
  have h4 : 4 * Ccg ^ 2 ≤ E := by nlinarith [hxx, hexpsq, hCE]
  -- Step 3: `2 Ccg <= sqrt E`.
  have hsqrtE : 2 * Ccg ≤ Real.sqrt E := by
    have hmono : Real.sqrt ((2 * Ccg) ^ 2) ≤ Real.sqrt E :=
      Real.sqrt_le_sqrt (by nlinarith [h4])
    rwa [Real.sqrt_sq (by positivity)] at hmono
  -- Step 4: `E^5 <= gamma⁻¹` — the proved polynomial form of the fifth-root
  -- gate, `Provider.Tail.pow_five_le_inv_of_le_rpow`.
  have hE5 : E ^ (5 : ℕ) ≤ gamma⁻¹ :=
    Provider.Tail.pow_five_le_inv_of_le_rpow hE0.le hgamma hEgamma
  -- Step 5: `2 Ccg E^2 <= sqrt (gamma⁻¹)`.
  have hsplit : Real.sqrt (E ^ (5 : ℕ)) = E ^ (2 : ℕ) * Real.sqrt E := by
    have hid : E ^ (5 : ℕ) = (E ^ (2 : ℕ)) ^ 2 * E := by ring
    rw [hid, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  have hmono5 : Real.sqrt (E ^ (5 : ℕ)) ≤ Real.sqrt gamma⁻¹ := Real.sqrt_le_sqrt hE5
  have hstep : E ^ (2 : ℕ) * (2 * Ccg) ≤ E ^ (2 : ℕ) * Real.sqrt E :=
    mul_le_mul_of_nonneg_left hsqrtE (by positivity)
  have hkey : 2 * Ccg * E ^ (2 : ℕ) ≤ Real.sqrt gamma⁻¹ := by
    rw [hsplit] at hmono5
    nlinarith [hstep, hmono5]
  -- Step 6: `log (gamma⁻¹) <= 2 sqrt (gamma⁻¹)`.
  have hsp : 0 < Real.sqrt gamma⁻¹ := Real.sqrt_pos.2 hginv
  have hlogsq : Real.log gamma⁻¹ = 2 * Real.log (Real.sqrt gamma⁻¹) := by
    conv_lhs => rw [← Real.sq_sqrt hginv.le]
    rw [Real.log_pow]
    norm_num
  have hlogle : Real.log gamma⁻¹ ≤ 2 * Real.sqrt gamma⁻¹ := by
    have := Real.log_le_sub_one_of_pos hsp
    linarith [hlogsq]
  -- Step 7: `log (gamma⁻¹) <= Ccg⁻¹ E⁻² gamma⁻¹`.
  have hCE2 : (0 : ℝ) < Ccg * E ^ (2 : ℕ) := by positivity
  have hTid : (Ccg⁻¹ * (E⁻¹) ^ 2 * gamma⁻¹) * (Ccg * E ^ (2 : ℕ)) = gamma⁻¹ := by
    field_simp
  have hsqsq : Real.sqrt gamma⁻¹ * Real.sqrt gamma⁻¹ = gamma⁻¹ :=
    Real.mul_self_sqrt hginv.le
  have hT : Real.log gamma⁻¹ ≤ Ccg⁻¹ * (E⁻¹) ^ 2 * gamma⁻¹ := by
    have hmul := mul_le_mul_of_nonneg_right hkey hsp.le
    have h2 : 2 * Real.sqrt gamma⁻¹ * (Ccg * E ^ (2 : ℕ)) ≤ gamma⁻¹ := by
      nlinarith [hmul, hsqsq]
    have h3 : 2 * Real.sqrt gamma⁻¹ ≤ Ccg⁻¹ * (E⁻¹) ^ 2 * gamma⁻¹ :=
      le_of_mul_le_mul_right (by linarith [hTid, h2]) hCE2
    linarith [hlogle, h3]
  -- Step 8: `exp(-(Ccg⁻¹ E⁻² gamma⁻¹)) <= gamma`.
  have hexpT : Real.exp (-(Ccg⁻¹ * (E⁻¹) ^ 2 * gamma⁻¹)) ≤ gamma := by
    have hlg : Real.log gamma⁻¹ = -Real.log gamma := Real.log_inv gamma
    have hle : -(Ccg⁻¹ * (E⁻¹) ^ 2 * gamma⁻¹) ≤ Real.log gamma := by
      linarith [hT, hlg]
    calc Real.exp (-(Ccg⁻¹ * (E⁻¹) ^ 2 * gamma⁻¹))
        ≤ Real.exp (Real.log gamma) := Real.exp_le_exp.2 hle
      _ = gamma := Real.exp_log hgamma
  -- Step 9: the window.
  exact Set.mem_Icc.2 ⟨by linarith, by linarith⟩

/-! ## 5. `e.mathcalE.crude.bound` -/

section Crude

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **The assembly core of `e.mathcalE.crude.bound`.**

Given the almost-sure two-summand face
`X <= cU . Uf + cL . Lfam L` of `e.bound.Lambdas.by.Es`, the two-term upper
payload of `p.cg.ellipticity.bounds` and its lower-family payload, this
produces the source's three-term display

```
X  <=  (cU bU + cL bL)  +  O_{Gamma_1}(cU AU1)  +  O_{Gamma_sigma}(K (cU AU2 + cL AL)) ,
K = (1 + log 2)^{1/sigma} .
```

The two rare lanes are merged after the free exponent downgrades
`Gamma_{sigmaU} ⊆ Gamma_sigma` and `Gamma_{sigmaL} ⊆ Gamma_sigma`, by the cheap
proved binary add; `gammaTriangleConst` is not used. -/
private theorem crude_core [IsFiniteMeasure μ]
    {X Uf : Ω → ℝ} {Lfam : ℤ → Ω → ℝ} {L0 L : ℤ}
    {bU AU1 AU2 bL AL cU cL sigma sigmaU sigmaL : ℝ}
    (hsigma : 0 < sigma) (hsU : sigma ≤ sigmaU) (hsL : sigma ≤ sigmaL)
    (hcU : 0 < cU) (hcL : 0 < cL) (hL0 : L0 ≤ L) (hXm : Measurable X)
    (hupper : Probability.IsDeterministicShiftTwoTermOneSidedOrlicz μ
      (gammaSigma 1) (gammaSigma sigmaU) Uf bU AU1 AU2)
    (hlower : Probability.IsLowerIntegerFamilyOrlicz μ (gammaSigma sigmaL)
      Lfam L0 bL AL)
    (hae : ∀ᵐ omega ∂μ, X omega ≤ cU * Uf omega + cL * Lfam L omega) :
    Probability.IsDeterministicShiftTwoTermOneSidedOrlicz μ (gammaSigma 1)
      (gammaSigma sigma) X (cU * bU + cL * bL) (cU * AU1)
      ((1 + Real.log 2) ^ sigma⁻¹ * (cU * AU2 + cL * AL)) := by
  obtain ⟨Y₁, Z₁, -, -, hAU1, hAU2, -, hY₁m, hZ₁m, hUdom, hY₁t, hZ₁t⟩ :=
    Probability.deterministicShiftTwoTermOneSidedOrlicz_iff_exists.1 hupper
  obtain ⟨W, hW⟩ := hlower
  have hYt : IsBigOWith μ (gammaSigma 1) (fun omega => cU * Y₁ omega) (cU * AU1) :=
    IsBigOWith.const_mul hcU.le hY₁t
  have hZt : IsBigOWith μ (gammaSigma sigma)
      (fun omega => cU * Z₁ omega + cL * W omega)
      ((1 + Real.log 2) ^ sigma⁻¹ * (cU * AU2 + cL * AL)) :=
    Provider.Multiscale.isBigOWith_gammaSigma_add hsigma
      (Provider.Orlicz.isBigOWith_gammaSigma_mono_exponent hsU
        (IsBigOWith.const_mul hcU.le hZ₁t))
      (Provider.Orlicz.isBigOWith_gammaSigma_mono_exponent hsL
        (IsBigOWith.const_mul hcL.le hW.tail))
  have hAL : 0 < AL := hW.scale_pos
  have hlog2 : (0 : ℝ) < 1 + Real.log 2 := by
    have hpos := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    linarith
  refine isDeterministicShiftTwoTermOneSidedOrlicz_of_ae_le one_pos hsigma
    (by positivity) (mul_pos (Real.rpow_pos_of_pos hlog2 _) (by positivity))
    hXm (hY₁m.const_mul cU)
    ((hZ₁m.const_mul cU).add (hW.measurable_witness.const_mul cL)) hYt hZt ?_
  filter_upwards [hae] with omega homega
  have hU := hUdom omega
  have hL := hW.dominates omega L hL0
  simp only [Pi.add_apply]
  nlinarith [mul_le_mul_of_nonneg_left hU hcU.le,
    mul_le_mul_of_nonneg_left hL hcL.le]

end Crude

/-- **`e.mathcalE.crude.bound` at the printed gauge `shom_m`.**

Identical to `exists_crude_bound_at_predecessor_gauge` except that the
comparator scale is the printed `m`, at the cost of the two gauge conversions
(factor `4` on the upper lane, factor `4 . 3^{cgamma}` on the lower lane).

The earlier reading of this theorem under `inductionState M m E` is **withdrawn
as circular at the root**; see the module header.

Two dimensional constants are exported: `Ccg` from `p.cg.ellipticity.bounds`,
in which the display's amplitudes are written, and `Cshom` from
`l.shom.continuity`, which appears only in the `E`-gate.  They are obtained
once each and never composed.

The `<= 4 Ccg` reading of the deterministic part belongs to the predecessor
gauge only; here the deterministic part is
`8 Ccg + 8 . 3^{cgamma} . lowerEllipticityProfile Ccg cgamma (s/4) 2`. -/
theorem exists_crude_bound (d : ℕ) :
    ∃ Ccg Cshom : ℝ, 0 < Ccg ∧ 0 < Cshom ∧
      ∀ (M : ABKModel d) (m : ℤ) (E : {E : ℝ // 1 ≤ E}),
        Algsuperdiff.Frozen.Section3.inductionState M (m - 1) E →
        mStarStar M < m →
        max (Real.exp (Ccg / (1 / 7))) (Disorder.cstar M)⁻¹ ≤ (E : ℝ) →
        Cshom * (Disorder.cstar M)⁻¹ ≤ (E : ℝ) →
        (E : ℝ) ≤ M.gamma ^ (-(1 / 5 : ℝ)) →
        M.gamma ≤ ((E : ℝ)⁻¹) ^ 10 →
        ∀ s : ℝ, ∀ hs8 : 8 * M.gamma ≤ s, s ≤ 1 →
          Probability.IsDeterministicShiftTwoTermOneSidedOrlicz
            (Cutoff.cutoffSampleLaw M).toMeasure
            (gammaSigma 1) (gammaSigma (2 / 7))
            (fun omega =>
              Observable.cutoffHomogenizationError M m
                  ⟨s / 4,
                    quarter_pos_of_eight_gamma_le M.shellPrefix.gamma_pos hs8⟩
                  omega ^ 2)
            (8 * Ccg +
              8 * (3 : ℝ) ^ M.gamma *
                lowerEllipticityProfile Ccg M.gamma (s / 4) exponentTwo)
            (8 * (Ccg * (Disorder.cstar M)⁻¹ * (s / 4) * M.gamma *
              (2 * (s / 4) - M.gamma)⁻¹ ^ 3))
            ((1 + Real.log 2) ^ ((2 : ℝ) / 7)⁻¹ *
              (8 * Real.exp (-(Ccg⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹)) +
                8 * (3 : ℝ) ^ M.gamma *
                  Real.exp (-(Ccg⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹)))) := by
  obtain ⟨Ccg, hCcgPos, hcg⟩ := Algsuperdiff.Frozen.Section3.coarse_ellipticity_bounds d
  obtain ⟨Cshom, hCshomPos, hshom⟩ := Provider.Localization.shom_continuity d
  refine ⟨Ccg, Cshom, hCcgPos, hCshomPos, ?_⟩
  intro M m E hS hmStar hE hEshom hEgamma hgammaE s hs8 hs1
  have hgamma : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hs4 : (0 : ℝ) < s / 4 := quarter_pos_of_eight_gamma_le hgamma hs8
  have hsWindow : s / 4 ∈ Set.Icc
      (M.gamma / 2 + Real.exp (-(Ccg⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹))) 1 :=
    quarter_mem_crude_window hCcgPos E.2 (le_trans (le_max_left _ _) hE) hEgamma
      hgamma hs8 hs1
  obtain ⟨hlower, hupper⟩ :=
    hcg M m E hS (1 / 7) (by norm_num) hE hEgamma exponentTwo (s / 4) hsWindow
  have hthree : (0 : ℝ) < (3 : ℝ) ^ M.gamma := Real.rpow_pos_of_pos (by norm_num) _
  refine crude_core (sigma := 2 / 7) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num : (0 : ℝ) < 8) (by positivity)
    (show m - 1 ≤ m by omega)
    (((Observable.measurable_cutoffHomogenizationError M m
      ⟨s / 4, hs4⟩).pow_const 2)) hupper hlower ?_
  -- the gauge conversion of the two lanes, from `l.shom.continuity`
  obtain ⟨-, hratio, hgrowthShom, -, -⟩ :=
    hshom M m E hmStar hS hEshom hgammaE m (m - 1) (by omega) le_rfl
  obtain ⟨hpredLe, hLe⟩ := gauge_pair_of_shom M m hratio hgrowthShom
  have hposm : (0 : ℝ) < (Annealed.sigmaBar M m : ℝ) := Provider.Orlicz.sigmaBar_pos M m
  have hposp : (0 : ℝ) < (Annealed.sigmaBar M (m - 1) : ℝ) :=
    Provider.Orlicz.sigmaBar_pos M (m - 1)
  have hinvLe : ((Annealed.sigmaBar M m : ℝ))⁻¹ ≤
      4 * ((Annealed.sigmaBar M (m - 1) : ℝ))⁻¹ := by
    rw [inv_le_iff_one_le_mul₀ hposm]
    have hstep := mul_le_mul_of_nonneg_left hpredLe (inv_pos.2 hposp).le
    rw [inv_mul_cancel₀ (ne_of_gt hposp)] at hstep
    nlinarith [hstep, hposm, inv_pos.2 hposp]
  filter_upwards [Provider.Tail.sq_cutoffHomogenizationError_le M m m hs4]
    with omega homega
  have hUnn := Observable.cutoffUpperEllipticity_nonneg M m m (s / 4) hs4 exponentTwo omega
  have hLnn :=
    Observable.cutoffLowerEllipticityInv_nonneg M m m (s / 4) hs4 exponentTwo omega
  have hUstep := mul_le_mul_of_nonneg_left hinvLe hUnn
  have hLstep := mul_le_mul_of_nonneg_left hLe hLnn
  change Observable.cutoffHomogenizationErrorAtComparatorScale M m m
      ⟨s / 4, hs4⟩ omega ^ 2 ≤ _ at homega
  simp only [Observable.cutoffHomogenizationError]
  nlinarith [homega, hUstep, hLstep]

/-! ## 6. `e.badevent.indicator.propagate`, in the split form -/

section BadEvent

/-- The scale gap of the multiscale bad event, in the direction the
oscillation rate uses. -/
private theorem scaleGapPos_down (l : ℤ) (h : ℕ) :
    Provider.BadEvents.scaleGapPos (l - (h : ℤ)) l = (h : ℝ) := by
  rw [Provider.BadEvents.scaleGapPos_of_le (show l - (h : ℤ) ≤ l by omega)]
  push_cast
  ring

/-- The scale gap of the multiscale bad event, in the opposite direction: the
coarse scale is below the fine one, so the reversed gap vanishes. -/
private theorem scaleGapPos_up (l : ℤ) (h : ℕ) :
    Provider.BadEvents.scaleGapPos l (l - (h : ℤ)) = 0 := by
  rw [Provider.BadEvents.scaleGapPos]
  refine max_eq_right ?_
  have : (0 : ℝ) ≤ (h : ℝ) := Nat.cast_nonneg h
  push_cast
  linarith

/-- The oscillation rate of the multiscale bad event, evaluated. -/
private theorem oscRate_eq {M : ABKModel d} (c : ℝ) (l : ℤ) (h : ℕ) :
    c * Disorder.cstar M * M.gamma⁻¹ *
        (3 : ℝ) ^ (-5 * Provider.BadEvents.scaleGapPos (l - (h : ℤ)) l) *
        (3 : ℝ) ^ Provider.BadEvents.scaleGapPos l (l - (h : ℤ)) =
      c * Disorder.cstar M * M.gamma⁻¹ * ((3 : ℝ) ^ (5 * (h : ℝ)))⁻¹ := by
  rw [scaleGapPos_down, scaleGapPos_up, Real.rpow_zero, mul_one,
    show (-5 : ℝ) * (h : ℝ) = -(5 * (h : ℝ)) by ring,
    Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3)]

/-- The reciprocal of the oscillation rate, in the printed shape. -/
private theorem four_div_oscRate {M : ABKModel d} {c : ℝ} (hc : 0 < c) (h : ℕ) :
    4 / (c * Disorder.cstar M * M.gamma⁻¹ * ((3 : ℝ) ^ (5 * (h : ℝ)))⁻¹) =
      4 * c⁻¹ * (Disorder.cstar M)⁻¹ * (3 : ℝ) ^ (5 * (h : ℝ)) * M.gamma := by
  have hcstar : 0 < Disorder.cstar M := Provider.Orlicz.cstar_pos M
  have hgamma : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hthree : (0 : ℝ) < (3 : ℝ) ^ (5 * (h : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  field_simp

/-- The reciprocal of the doubly-exponential rate, in the printed shape. -/
private theorem four_div_exp (x : ℝ) :
    4 / Real.exp x = 4 * Real.exp (-x) := by
  rw [Real.exp_neg, div_eq_mul_inv]

/-- The multiscale bad event is measurable. -/
private theorem measurableSet_compl_goodLocalEventAt (M : ABKModel d) (Ccg : ℝ)
    (m n : ℤ) (z : Vec d) :
    MeasurableSet
      (Algsuperdiff.Frozen.Section3.goodLocalEventAt M Ccg m n z)ᶜ :=
  (((Cutoff.measurable_translateCutoffSample z)
    (Provider.BadEvents.measurableSet_goodLocalEvent M Ccg (originCube d m) n))).compl

/-- **The averaged-indicator display, by Markov plus the `[0,1]` ceiling.**

For every nonempty finite set `F` of base points and every `rho ∈ (0,2]`,

```
( avsum_{z in F} 1_{not Q(l,l-h,z)} )^rho
   <= O_{Gamma_1}( 4 rho^{-1} ( 4 c^{-1} cstar^{-1} 3^{5h} cgamma
                                + 4 exp(-c E^{-2} cgamma^{-1}) ) ) .
```

: the printed *"crude application of the triangle inequality"* does not produce
this display (the countable `Gamma_sigma` triangle costs a further `1 + |log
s|`, which the display's own `eps^{-C}` cannot absorb).  The mechanism is
Markov's inequality plus the deterministic `[0,1]` ceiling on the normalized
sum, and the printed `rho^{-1}` is the join constant between the two branches.
The finite index set is arbitrary — in the manuscript it is `3^l Zd cap cu_m` —
and no cardinality factor appears, because means average rather than add. -/
theorem exists_badEvent_indicatorAverage_rpow (d : ℕ) :
    ∃ Ccg c : ℝ, 1 ≤ Ccg ∧ 0 < c ∧
      ∀ H : ℝ, 0 ≤ H → ∃ C : ℝ, 1 ≤ C ∧
        ∀ (M : ABKModel d) (m0 : ℤ) (E : {E : ℝ // 1 ≤ E})
          (epsilon : ℝ) (h : ℕ) (l : ℤ),
          Algsuperdiff.Frozen.Section3.inductionState M (m0 - 1) E →
          epsilon ∈ Set.Ioc 0 (1 / 2) →
          (h : ℝ) ≤ H * |Real.log epsilon| + 1 →
          (Disorder.cstar M)⁻¹ * epsilon ^ (-C) ≤ (E : ℝ) →
          M.gamma ≤ ((E : ℝ)⁻¹) ^ 10 →
          l - (h : ℤ) ≤ m0 - 1 →
          ∀ rho : ℝ, 0 < rho → rho ≤ 2 →
          ∀ F : Finset (Vec d), F.Nonempty →
            IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure (gammaSigma 1)
              (fun omega =>
                ((F.card : ℝ)⁻¹ * ∑ z ∈ F,
                  (Algsuperdiff.Frozen.Section3.goodLocalEventAt
                    M (2 * Ccg) l (l - (h : ℤ)) z)ᶜ.indicator
                      (fun _ => (1 : ℝ)) omega) ^ rho)
              (4 * rho⁻¹ *
                (4 * c⁻¹ * (Disorder.cstar M)⁻¹ * (3 : ℝ) ^ (5 * (h : ℝ)) *
                    M.gamma +
                  4 * Real.exp (-(c * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹)))) := by
  obtain ⟨Ccg, c, hCcg, hc, hbad⟩ :=
    Provider.BadEvents.exists_measureReal_compl_goodLocalEventAt_le_of_multiscaleParameters d
  refine ⟨Ccg, c, hCcg, hc, ?_⟩
  intro H hH
  obtain ⟨C, hC, hbadC⟩ := hbad H hH
  refine ⟨C, hC, ?_⟩
  intro M m0 E epsilon h l hS hepsilon hh hscale hgammaE hn rho hrho hrho2 F hF
  have hcstar : 0 < Disorder.cstar M := Provider.Orlicz.cstar_pos M
  have hgamma : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hthree : (0 : ℝ) < (3 : ℝ) ^ (5 * (h : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hosc : (0 : ℝ) <
      c * Disorder.cstar M * M.gamma⁻¹ * ((3 : ℝ) ^ (5 * (h : ℝ)))⁻¹ := by positivity
  have hrare : (0 : ℝ) < Real.exp (c * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹) := Real.exp_pos _
  have hmain := indicatorAverage_rpow_isBigOWith_gammaOne_of_two_exp
    (μ := (Cutoff.cutoffSampleLaw M).toMeasure) (F := F) hF
    (B := fun z : Vec d =>
      (Algsuperdiff.Frozen.Section3.goodLocalEventAt
        M (2 * Ccg) l (l - (h : ℤ)) z)ᶜ)
    (fun z _ => measurableSet_compl_goodLocalEventAt M (2 * Ccg) l (l - (h : ℤ)) z)
    hrho hrho2 hosc hrare ?_
  · rwa [four_div_oscRate hc h, four_div_exp] at hmain
  · intro z _
    have hmeasure := hbadC M m0 E epsilon h l hS hepsilon hh hscale hgammaE hn z
    rwa [oscRate_eq c l h] at hmeasure

/-- **The averaged-indicator display at the corrected exponent `rho = s/d`.**

```
( avsum_{z in F} 1_{not Q(l,l-h,z)} )^{s/d}
   <= O_{Gamma_1}( 16 d s^{-1} ( c^{-1} cstar^{-1} 3^{5h} cgamma
                                 + exp(-c E^{-2} cgamma^{-1}) ) ) .
```

The admissibility `s/d <= 2` is automatic on the source window `s <= 1` because
`2 <= d`. -/
theorem exists_badEvent_indicatorAverage_rpow_at_s_div_d (d : ℕ) :
    ∃ Ccg c : ℝ, 1 ≤ Ccg ∧ 0 < c ∧
      ∀ H : ℝ, 0 ≤ H → ∃ C : ℝ, 1 ≤ C ∧
        ∀ (M : ABKModel d) (m0 : ℤ) (E : {E : ℝ // 1 ≤ E})
          (epsilon : ℝ) (h : ℕ) (l : ℤ),
          Algsuperdiff.Frozen.Section3.inductionState M (m0 - 1) E →
          epsilon ∈ Set.Ioc 0 (1 / 2) →
          (h : ℝ) ≤ H * |Real.log epsilon| + 1 →
          (Disorder.cstar M)⁻¹ * epsilon ^ (-C) ≤ (E : ℝ) →
          M.gamma ≤ ((E : ℝ)⁻¹) ^ 10 →
          l - (h : ℤ) ≤ m0 - 1 →
          ∀ s : ℝ, 0 < s → s ≤ 1 →
          ∀ F : Finset (Vec d), F.Nonempty →
            IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure (gammaSigma 1)
              (fun omega =>
                ((F.card : ℝ)⁻¹ * ∑ z ∈ F,
                  (Algsuperdiff.Frozen.Section3.goodLocalEventAt
                    M (2 * Ccg) l (l - (h : ℤ)) z)ᶜ.indicator
                      (fun _ => (1 : ℝ)) omega) ^ (s / (d : ℝ)))
              (16 * (d : ℝ) * s⁻¹ *
                (c⁻¹ * (Disorder.cstar M)⁻¹ * (3 : ℝ) ^ (5 * (h : ℝ)) * M.gamma +
                  Real.exp (-(c * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹)))) := by
  obtain ⟨Ccg, c, hCcg, hc, hbad⟩ := exists_badEvent_indicatorAverage_rpow d
  refine ⟨Ccg, c, hCcg, hc, ?_⟩
  intro H hH
  obtain ⟨C, hC, hbadC⟩ := hbad H hH
  refine ⟨C, hC, ?_⟩
  intro M m0 E epsilon h l hS hepsilon hh hscale hgammaE hn s hs hs1 F hF
  have hd : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast M.shellPrefix.dimension
  have hdpos : (0 : ℝ) < (d : ℝ) := by linarith
  have hrho : 0 < s / (d : ℝ) := by positivity
  have hrho2 : s / (d : ℝ) ≤ 2 := by
    rw [div_le_iff₀ hdpos]
    linarith
  have hmain := hbadC M m0 E epsilon h l hS hepsilon hh hscale hgammaE hn
    (s / (d : ℝ)) hrho hrho2 F hF
  have hamp : 4 * (s / (d : ℝ))⁻¹ *
      (4 * c⁻¹ * (Disorder.cstar M)⁻¹ * (3 : ℝ) ^ (5 * (h : ℝ)) * M.gamma +
        4 * Real.exp (-(c * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹))) =
      16 * (d : ℝ) * s⁻¹ *
        (c⁻¹ * (Disorder.cstar M)⁻¹ * (3 : ℝ) ^ (5 * (h : ℝ)) * M.gamma +
          Real.exp (-(c * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹))) := by
    field_simp
    ring
  rwa [hamp] at hmain

end BadEvent

end

end Algsuperdiff.Section3.Provider.MultiscaleEstimate
