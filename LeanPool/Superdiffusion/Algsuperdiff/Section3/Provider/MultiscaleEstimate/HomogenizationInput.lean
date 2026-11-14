/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.Section3.HomogenizationStep
public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.Section3.InductionState
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Localization.ResponseTransport
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Orlicz.CommonEventAggregation
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Stream.IncrementTranslation

/-!
# HomogenizationInput

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

open _root_.Algsuperdiff.Section3.Provider.Homogenization
  (isCommonEventTwoTermBigOWith_of_ae_forall_exists_le)
open _root_.Algsuperdiff.Section3.Provider.Localization
  (ae_forall_descendant_responseJ_cutoffFamily_eq_cutoffResponseJ_translate)

/-!
# Provider: the per-cube homogenization input of `p.multiscale.estimate`

The proof of ABK26's Proposition `p.multiscale.estimate` reduces, through
`l.localization.mathcalE`, to three displays.  The first of them is
`e.what.homogenization.gives`,

```
s * sum_{l = -infty}^{m} 3^{-s(m-l)}
     ( avsum_{z in 3^l Z^d cap cu_m}
         max_{|e| = 1} J(z + cu_l, shom_{l-h}^{-1/2} e, shom_{l-h}^{1/2} e; a_{l-h})^{d/s}
     )^{s/d}
  <= O_{Gamma_1}(C s^{-1} eps E^2 cgamma) + O_{Gamma_{1/4}}(C eps exp(-E^{-3} cgamma^{-1})) ,
```

and the manuscript proves it in one sentence: *"an immediate consequence of
Proposition `p.homogenization.step`, the triangle inequality
`e.Gamma.sigma.triangle` and the fact that `s >= 8 cgamma`, provided that `h:=
C |log eps|` for `C` large enough"*.

This module is the **per-cube half** of that sentence: for **one** scale `l`
and **one** grid point `z` it applies the
`Algsuperdiff.Frozen.Section3.homogenization_step` at cube scale `l` and at
`eps' := eps^2`, and it moves the conclusion from the origin cube `cu_l`, the
only cube the Section 3 observable reads, to the translated cube `z + cu_l`
that the localization display carries.

* the `l`-sum, the `avsum_z` volume average and the two `Gamma_sigma` triangle
  aggregations that turn the per-cube bounds into the display above;

## The `eps^2` route (development decision D2)

Two consequences are visible in this module.

1. **The lanes are the printed ones, a fortiori.**  At `eps' = eps^2` the root
   emits `O_{Gamma_1}(eps^2 E^2 cgamma) + O_{Gamma_{1/4}}(eps^2 exp(-2 E^{-3}
   cgamma^{-1}))`.  Since `eps <= 1/2`, both amplitudes are below the printed
   `eps`-linear ones, so the printed display is obtained with a surplus half
   power of `eps` in hand.
2. **The `s <= Cms * eps` witness clause of the frozen `multiscale_estimate`
   becomes free.**  That surplus is exactly what the buckle's square root turns
   into the refined `Gamma_2` amplitude: `sqrt (eps^2 E^2 cgamma) = eps E sqrt
   cgamma`, which is the clause's own amplitude at `Cms = 1`, `s = 1`, and
   therefore below `Cms eps E s^{-1} sqrt cgamma` for every `s <= 1` --- no `s
   <= Cms * eps` guard is used anywhere.

## The `Gamma`-lane structure

Both lanes are emitted **exactly** as the frozen root emits them: the typical
lane at `Gamma_1` and the rare lane at `Gamma_{1/4}`.  No index is lowered and
no lane is weakened anywhere below.  This matters downstream: records that the
multiscale buckle's rare budget is **pinned** at `Gamma_{1/4}` by this very
display and that the Orlicz index can only ever be lowered, so an index loss
introduced here would be unrecoverable.

## The translation seam

`Observable.cutoffResponseJ M l L e` reads the **origin** cube `cu_l` only ---
there is no translate parameter in the observable --- while the localization
display carries `z + cu_l` on both sides.  The bridge is the proved unit-D
transport `Provider/Localization/ResponseTransport.lean`, whose almost-sure
endpoint identifies the demanded `Book.Ch02.responseJ` at an arbitrary
descendant `R = z + cu_l` with the observable read at the translated sample
`translateCutoffSample (triadicCubeShift R) omega`.  Two things are added here
and nothing else:

* section 5, the transport of a **common-event** two-term bound along that same
  translation (the proved translation layer carries the one-term `IsBigOWith`
  and the two-term `IsTwoTermBigOWith` cases, not the common-event one, whose
  almost-sure domination clause has to be pulled back along the
  measure-preserving translation);
* section 8, the passage from the root's **unit** directions `|e| = 1` --- the
  quantifier of the printed display --- to the loading ball `|v|^2 <= 2` in
  which `Provider/Localization/Breakdown.lean` and `ResponseTransport`'s
  consumption interface state the two breakdown legs.  This is the quadratic
  homogeneity of `J`, at the price of the factor `2` that the ball costs; it is
  a deterministic identity and commits to no amplitude.

No gap was found in the transport lane: every identity this module needed was
either already public there or is the CoarseGraining quadraticity theorem
`Book.Ch02.responseJ_smul`.

## References

* ABK26, `e.what.homogenization.gives`, and its proof sentence.
* ABK26, `p.homogenization.step` (the frozen `homogenization_step`).
* ABK26, `e.mathcal.E.breakdown` (the legs at `z + cu_l`).
-/

namespace Algsuperdiff.Section3.Provider.MultiscaleEstimate

-- `_root_` is load-bearing throughout: `Algsuperdiff.Section3.Provider.Homogenization`
-- is a live sibling namespace and is in this file's import closure, so a bare
-- `open Homogenization` would resolve to it rather than to the CoarseGraining root namespace.
open _root_.MeasureTheory
open _root_.HCPolySupport
open _root_.HCPolySupport.IndependentSums
open _root_.Algsuperdiff.Section3.Cutoff

noncomputable section



variable {d : ℕ}

/-! ## 1. The homogenization constant -/

/-- The homogenization constant of the `p.homogenization.step`: the existential
witness of `Algsuperdiff.Frozen.Section3.homogenization_step`, which depends on
the dimension alone. -/
def homogenizationStepConst (d : ℕ) : ℝ :=
  (Algsuperdiff.Frozen.Section3.homogenization_step d).choose

/-- The homogenization constant is at least one, by the frozen statement. -/
theorem one_le_homogenizationStepConst (d : ℕ) : 1 ≤ homogenizationStepConst d :=
  (Algsuperdiff.Frozen.Section3.homogenization_step d).choose_spec.1

/-- The homogenization constant is positive. -/
theorem homogenizationStepConst_pos (d : ℕ) : 0 < homogenizationStepConst d :=
  lt_of_lt_of_le zero_lt_one (one_le_homogenizationStepConst d)

/-- **The homogenization step, at the named constant.**  This is the frozen
`homogenization_step` with its existential witness replaced by
`homogenizationStepConst d`; it is a restatement, binder for binder, and proves
nothing new.  Every later declaration in this file goes through it, so the
frozen root is applied exactly once. -/
theorem homogenizationStep_spec (d : ℕ) (M : ABKModel d) (m : ℤ)
    (E : {E : ℝ // 1 ≤ E})
    (hE : 15 * (Disorder.cstar M)⁻¹ ≤ (E : ℝ))
    (hgammaE : M.gamma ≤ ((E : ℝ)⁻¹) ^ 10)
    (hstate : ∀ k : ℤ, k ≤ m - 1 →
      ∀ s : ℝ, ∀ hsWindow : s ∈ Set.Icc (8 * M.gamma) 1,
        Probability.IsTwoTermBigOWith
          (cutoffSampleLaw M).toMeasure
          (gammaSigma 2) (gammaSigma (1 / 2))
          (Observable.cutoffHomogenizationError M k
            ⟨s,
              (mul_pos (by norm_num : (0 : ℝ) < 8)
                M.shellPrefix.gamma_pos).trans_le hsWindow.1⟩)
          ((E : ℝ) * s⁻¹ * Real.sqrt M.gamma)
          ((s⁻¹) ^ 2 * Real.exp (-(((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹))))
    (epsilon : ℝ) (hepsilon : epsilon ∈ Set.Ioc (0 : ℝ) (1 / 2))
    (hgate : M.gamma ≤ (homogenizationStepConst d)⁻¹ * ((E : ℝ)⁻¹) ^ 2 * epsilon) :
    Probability.IsCommonEventTwoTermBigOWith
      (cutoffSampleLaw M).toMeasure (gammaSigma 1) (gammaSigma (1 / 4))
      (fun i : {p : ℤ × {e : Vec d // Book.Ch02.vecNorm e = 1} //
          (p.1 : ℝ) ≤ (m : ℝ) - homogenizationStepConst d * |Real.log epsilon|} =>
        Observable.cutoffResponseJ M m i.1.1 i.1.2.1)
      (epsilon * (E : ℝ) ^ 2 * M.gamma)
      (epsilon * Real.exp (-(2 * ((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹))) :=
  (Algsuperdiff.Frozen.Section3.homogenization_step d).choose_spec.2 M m E hE hgammaE
    hstate epsilon hepsilon hgate

/-! ## 2. The `eps^2` substitution

The root's own window premise and its corridor are the only two places where
`eps'` occurs syntactically, and both survive the substitution `eps' := eps^2`
free of charge: the window because `eps <= 1/2` forces `eps^2 <= 1/4`, and the
corridor because `|log (eps^2)| = 2 |log eps|`, which is the cost
`h |-> 2 Chom |log eps|` that decision D2 records. -/

/-- The `eps^2` route stays inside the frozen window `Ioc 0 (1/2)`: it is the
`eps`-window premise of the root, discharged at no cost. -/
theorem sq_mem_Ioc_of_mem_Ioc {epsilon : ℝ}
    (hepsilon : epsilon ∈ Set.Ioc (0 : ℝ) (1 / 2)) :
    epsilon ^ 2 ∈ Set.Ioc (0 : ℝ) (1 / 2) :=
  ⟨pow_pos hepsilon.1 2, by nlinarith [hepsilon.1, hepsilon.2]⟩

/-- The corridor budget of the `eps^2` route is twice the printed one. -/
theorem abs_log_sq (epsilon : ℝ) :
    |Real.log (epsilon ^ 2)| = 2 * |Real.log epsilon| := by
  rw [Real.log_pow, abs_mul]
  norm_num

/-- The corridor of the root, read at `eps^2`, is the corridor at the doubled
budget `2 * Chom * |log eps|`. -/
theorem corridor_sq (l : ℤ) (Chom epsilon : ℝ) :
    (l : ℝ) - Chom * |Real.log (epsilon ^ 2)| =
      (l : ℝ) - 2 * Chom * |Real.log epsilon| := by
  rw [abs_log_sq]
  ring

/-! ## 3. The preceding-error premise at a lower cube scale

The root's third premise is verbatim the second conjunct of the frozen
`inductionState`, at `m0 := m - 1`.  Applying the root at a cube scale `l <= m`
asks for it at `l - 1`, which is a *restriction* of the same clause; no premise
is added and none is strengthened. -/

/-- **Premise inheritance.**  The preceding-error clause the root demands at cube
scale `l` is the second conjunct of the induction state `inductionState M m0 E`
whenever `l - 1 <= m0` --- in particular at `m0 = m - 1` for every `l <= m`,
which is the situation of `p.multiscale.estimate`'s own binder. -/
theorem precedingError_of_inductionState {M : ABKModel d} {m0 l : ℤ}
    {E : {E : ℝ // 1 ≤ E}} (hl : l - 1 ≤ m0)
    (hS : Algsuperdiff.Frozen.Section3.inductionState M m0 E) :
    ∀ k : ℤ, k ≤ l - 1 →
      ∀ s : ℝ, ∀ hsWindow : s ∈ Set.Icc (8 * M.gamma) 1,
        Probability.IsTwoTermBigOWith
          (cutoffSampleLaw M).toMeasure
          (gammaSigma 2) (gammaSigma (1 / 2))
          (Observable.cutoffHomogenizationError M k
            ⟨s,
              (mul_pos (by norm_num : (0 : ℝ) < 8)
                M.shellPrefix.gamma_pos).trans_le hsWindow.1⟩)
          ((E : ℝ) * s⁻¹ * Real.sqrt M.gamma)
          ((s⁻¹) ^ 2 * Real.exp (-(((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹))) :=
  fun k hk => hS.2 k (hk.trans hl)

/-! ## 4. The per-cube input at the origin cube -/

/-- **The per-cube homogenization input, at the origin cube of scale `l`.**  The
`p.homogenization.step` applied at cube scale `l` and at `eps' := eps^2`: one
pair of measurable envelopes dominates, on **one** event of probability one,
the response `J(cu_l, sigmaBar_L^{-1/2} e, sigmaBar_L^{1/2} e; a_L)`
simultaneously for every coefficient-cutoff scale `L` in the corridor `L <= l -
2 Chom |log eps|` and every unit direction `e`, at the two amplitudes

```
Gamma_1     :  eps^2 E^2 cgamma ,
Gamma_{1/4} :  eps^2 exp(-2 E^{-3} cgamma^{-1}) .
```

Both are the frozen root's own amplitudes at `eps' = eps^2`; both lanes carry
the frozen root's own Orlicz indices.  Since `eps <= 1/2`, both are below the
`eps`-linear amplitudes the display `e.what.homogenization.gives` prints, so the
printed lanes follow a fortiori and the surplus half power of `eps` is the one
decision D2 spends on the `Gamma_2` refinement. -/
theorem isCommonEventTwoTermBigOWith_cutoffResponseJ_epsSq
    (M : ABKModel d) (l : ℤ) (E : {E : ℝ // 1 ≤ E})
    (hE : 15 * (Disorder.cstar M)⁻¹ ≤ (E : ℝ))
    (hgammaE : M.gamma ≤ ((E : ℝ)⁻¹) ^ 10)
    (hstate : ∀ k : ℤ, k ≤ l - 1 →
      ∀ s : ℝ, ∀ hsWindow : s ∈ Set.Icc (8 * M.gamma) 1,
        Probability.IsTwoTermBigOWith
          (cutoffSampleLaw M).toMeasure
          (gammaSigma 2) (gammaSigma (1 / 2))
          (Observable.cutoffHomogenizationError M k
            ⟨s,
              (mul_pos (by norm_num : (0 : ℝ) < 8)
                M.shellPrefix.gamma_pos).trans_le hsWindow.1⟩)
          ((E : ℝ) * s⁻¹ * Real.sqrt M.gamma)
          ((s⁻¹) ^ 2 * Real.exp (-(((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹))))
    (epsilon : ℝ) (hepsilon : epsilon ∈ Set.Ioc (0 : ℝ) (1 / 2))
    (hgate : M.gamma ≤ (homogenizationStepConst d)⁻¹ * ((E : ℝ)⁻¹) ^ 2 * epsilon ^ 2) :
    Probability.IsCommonEventTwoTermBigOWith
      (cutoffSampleLaw M).toMeasure (gammaSigma 1) (gammaSigma (1 / 4))
      (fun i : {p : ℤ × {e : Vec d // Book.Ch02.vecNorm e = 1} //
          (p.1 : ℝ) ≤ (l : ℝ) - 2 * homogenizationStepConst d * |Real.log epsilon|} =>
        Observable.cutoffResponseJ M l i.1.1 i.1.2.1)
      (epsilon ^ 2 * (E : ℝ) ^ 2 * M.gamma)
      (epsilon ^ 2 * Real.exp (-(2 * ((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹))) := by
  refine
    isCommonEventTwoTermBigOWith_of_ae_forall_exists_le
      (homogenizationStep_spec d M l E hE hgammaE hstate (epsilon ^ 2)
        (sq_mem_Ioc_of_mem_Ioc hepsilon) hgate)
      (fun i => Observable.measurable_cutoffResponseJ M l i.1.1 i.1.2.1) ?_
  refine Filter.Eventually.of_forall (fun _ i => ?_)
  exact ⟨⟨i.1, by rw [corridor_sq]; exact i.2⟩, le_rfl⟩

/-! ## 5. Translation of a common-event two-term bound -/

/-- **The common-event carrier is translation invariant.**  A two-term
weak-Orlicz bound with one common domination event for an indexed family of
observables of the cutoff sample holds verbatim --- same envelopes up to the
translation, same Orlicz profiles, same amplitudes --- for the family read at
every real translate of the sample.

The two tail lanes are moved by the proved
`Stream.isBigOWith_comp_translateCutoffSample`; the only new step is the common
domination event, which is pulled back along the measure-preserving
translation, so the index quantifier stays inside one event and no intersection
over the index is taken.  The single probabilistic input is the `J1`
stationarity of the model, consumed as the fact
`map_translateCutoffSample_cutoffSampleLaw` and never as a hypothesis. -/
theorem isCommonEventTwoTermBigOWith_comp_translateCutoffSample {I : Type*}
    (M : ABKModel d) (z : Vec d) {Psi1 Psi2 : ℝ → ℝ}
    {X : I → CutoffSample d → ℝ} {A1 A2 : ℝ}
    (h : Probability.IsCommonEventTwoTermBigOWith
      (cutoffSampleLaw M).toMeasure Psi1 Psi2 X A1 A2) :
    Probability.IsCommonEventTwoTermBigOWith
      (cutoffSampleLaw M).toMeasure Psi1 Psi2
      (fun i omega => X i (translateCutoffSample z omega)) A1 A2 := by
  obtain ⟨Y, Z, hPsi1, hPsi2, hA1, hA2, hXm, hYm, hZm, hdom, hYt, hZt⟩ := h
  have hmp : MeasurePreserving (translateCutoffSample (d := d) z)
      (cutoffSampleLaw M).toMeasure (cutoffSampleLaw M).toMeasure :=
    ⟨measurable_translateCutoffSample z, map_translateCutoffSample_cutoffSampleLaw M z⟩
  exact ⟨fun omega => Y (translateCutoffSample z omega),
    fun omega => Z (translateCutoffSample z omega), hPsi1, hPsi2, hA1, hA2,
    fun i => (hXm i).comp (measurable_translateCutoffSample z),
    hYm.comp (measurable_translateCutoffSample z),
    hZm.comp (measurable_translateCutoffSample z),
    hmp.quasiMeasurePreserving.ae hdom,
    _root_.Algsuperdiff.Section3.Provider.Stream.isBigOWith_comp_translateCutoffSample
      M z hYm hYt,
    _root_.Algsuperdiff.Section3.Provider.Stream.isBigOWith_comp_translateCutoffSample
      M z hZm hZt⟩

/-! ## 6. The per-cube input at the translated cube -/

/-- **The per-cube homogenization input, transported.**  The statement of
`isCommonEventTwoTermBigOWith_cutoffResponseJ_epsSq` for the observable read at
the translated sample.  Instantiated at `z := triadicCubeShift R` this is the
input at the grid cube `R = z + cu_l`, which is the carrier the localization
display uses; the translation is the Lean carrier device forced by the fact that
`Observable.cutoffResponseJ` reads the origin cube only, and it changes neither
amplitude nor Orlicz index. -/
theorem isCommonEventTwoTermBigOWith_cutoffResponseJ_translate_epsSq
    (M : ABKModel d) (l : ℤ) (z : Vec d) (E : {E : ℝ // 1 ≤ E})
    (hE : 15 * (Disorder.cstar M)⁻¹ ≤ (E : ℝ))
    (hgammaE : M.gamma ≤ ((E : ℝ)⁻¹) ^ 10)
    (hstate : ∀ k : ℤ, k ≤ l - 1 →
      ∀ s : ℝ, ∀ hsWindow : s ∈ Set.Icc (8 * M.gamma) 1,
        Probability.IsTwoTermBigOWith
          (cutoffSampleLaw M).toMeasure
          (gammaSigma 2) (gammaSigma (1 / 2))
          (Observable.cutoffHomogenizationError M k
            ⟨s,
              (mul_pos (by norm_num : (0 : ℝ) < 8)
                M.shellPrefix.gamma_pos).trans_le hsWindow.1⟩)
          ((E : ℝ) * s⁻¹ * Real.sqrt M.gamma)
          ((s⁻¹) ^ 2 * Real.exp (-(((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹))))
    (epsilon : ℝ) (hepsilon : epsilon ∈ Set.Ioc (0 : ℝ) (1 / 2))
    (hgate : M.gamma ≤ (homogenizationStepConst d)⁻¹ * ((E : ℝ)⁻¹) ^ 2 * epsilon ^ 2) :
    Probability.IsCommonEventTwoTermBigOWith
      (cutoffSampleLaw M).toMeasure (gammaSigma 1) (gammaSigma (1 / 4))
      (fun (i : {p : ℤ × {e : Vec d // Book.Ch02.vecNorm e = 1} //
            (p.1 : ℝ) ≤ (l : ℝ) - 2 * homogenizationStepConst d * |Real.log epsilon|})
          (omega : CutoffSample d) =>
        Observable.cutoffResponseJ M l i.1.1 i.1.2.1 (translateCutoffSample z omega))
      (epsilon ^ 2 * (E : ℝ) ^ 2 * M.gamma)
      (epsilon ^ 2 * Real.exp (-(2 * ((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹))) :=
  isCommonEventTwoTermBigOWith_comp_translateCutoffSample M z
    (isCommonEventTwoTermBigOWith_cutoffResponseJ_epsSq M l E hE hgammaE hstate epsilon
      hepsilon hgate)

/-! ## 7. The literal per-`(l, z)` response of the printed display -/

/-- **The homogenization input at the printed carrier.**  For a grid cube
`R = z + cu_l` of the printed tiling `3^l Z^d cap cu_m`, one pair of measurable
envelopes with the two frozen tails dominates, on one event of probability one,
the manuscript's own quantity

```
J(z + cu_l, sigmaBar_L^{-1/2} e, sigmaBar_L^{1/2} e; a_L)
```

simultaneously for every coefficient-cutoff scale `L` in the corridor and every
unit direction `e`.  This is `e.what.homogenization.gives` before the `avsum_z`
average and the `l`-sum, at `eps' := eps^2`.

The envelopes are stated as an explicit `∃ Y Z` rather than through
`IsCommonEventTwoTermBigOWith` on purpose: the literal `Book.Ch02.responseJ` of
the cutoff family is *not* known to be measurable --- that is exactly why
Section 3 carries the measurable representative `Observable.cutoffResponseJ`
--- so the common-event carrier, which demands measurability of every member,
is not available at this spelling.  The almost-sure identification of the two
spellings is the proved unit-D endpoint, consumed here.

That concession is about the *family*, not about the envelopes: `Measurable Y`
and `Measurable Z` are carried as the first two conjuncts of the conclusion,
because `Y` and `Z` are existentially bound here and could not be recovered by
any consumer afterwards, while every consumer needs them --- the frozen
`IsTwoTermBigOWithWitnesses` demands `Measurable Y` and `Measurable Z`
(`Section3/Probability/TwoTermOrlicz.lean`), and so does every proved
`Gamma_sigma` triangle engine that this display exists to feed
(`Provider/Orlicz/TwoTermCalculus.lean`, `Provider/Orlicz/TsumTriangle.lean`).
They cost nothing: they are two of the fields of the common-event datum this
proof already destructures. -/
theorem exists_envelope_responseJ_descendant_epsSq
    (M : ABKModel d) {m l : ℤ} (hlm : l ≤ m) {R : TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d m) l)
    (E : {E : ℝ // 1 ≤ E})
    (hE : 15 * (Disorder.cstar M)⁻¹ ≤ (E : ℝ))
    (hgammaE : M.gamma ≤ ((E : ℝ)⁻¹) ^ 10)
    (hstate : ∀ k : ℤ, k ≤ l - 1 →
      ∀ s : ℝ, ∀ hsWindow : s ∈ Set.Icc (8 * M.gamma) 1,
        Probability.IsTwoTermBigOWith
          (cutoffSampleLaw M).toMeasure
          (gammaSigma 2) (gammaSigma (1 / 2))
          (Observable.cutoffHomogenizationError M k
            ⟨s,
              (mul_pos (by norm_num : (0 : ℝ) < 8)
                M.shellPrefix.gamma_pos).trans_le hsWindow.1⟩)
          ((E : ℝ) * s⁻¹ * Real.sqrt M.gamma)
          ((s⁻¹) ^ 2 * Real.exp (-(((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹))))
    (epsilon : ℝ) (hepsilon : epsilon ∈ Set.Ioc (0 : ℝ) (1 / 2))
    (hgate : M.gamma ≤ (homogenizationStepConst d)⁻¹ * ((E : ℝ)⁻¹) ^ 2 * epsilon ^ 2) :
    ∃ Y Z : CutoffSample d → ℝ,
      Measurable Y ∧ Measurable Z ∧
      IsBigOWith (cutoffSampleLaw M).toMeasure (gammaSigma 1) Y
          (epsilon ^ 2 * (E : ℝ) ^ 2 * M.gamma) ∧
        IsBigOWith (cutoffSampleLaw M).toMeasure (gammaSigma (1 / 4)) Z
            (epsilon ^ 2 * Real.exp (-(2 * ((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹))) ∧
          ∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure,
            ∀ L : ℤ,
              (L : ℝ) ≤ (l : ℝ) - 2 * homogenizationStepConst d * |Real.log epsilon| →
                ∀ e : Vec d, Book.Ch02.vecNorm e = 1 →
                  Book.Ch02.responseJ (Book.Ch02.cubeDomain R)
                      ((coefficientCutoffTriadicCoeffFamily M L omega).coeffOn R)
                      (Observable.inverseSqrtLoad (Annealed.sigmaBar M L) e)
                      (Observable.sqrtLoad (Annealed.sigmaBar M L) e) ≤
                    Y omega + Z omega := by
  let : NeZero d := _root_.Algsuperdiff.Section3.Provider.Localization.neZero_of_abkModel M
  obtain ⟨Y, Z, -, -, -, -, -, hYm, hZm, hdom, hYt, hZt⟩ :=
    isCommonEventTwoTermBigOWith_cutoffResponseJ_translate_epsSq M l (triadicCubeShift R) E
      hE hgammaE hstate epsilon hepsilon hgate
  refine ⟨Y, Z, hYm, hZm, hYt, hZt, ?_⟩
  filter_upwards [hdom,
    ae_forall_descendant_responseJ_cutoffFamily_eq_cutoffResponseJ_translate
      M hlm] with omega hdomega hidomega
  intro L hL e he
  rw [hidomega R hR L e]
  exact hdomega ⟨(L, ⟨e, he⟩), hL⟩

/-- The form of `exists_envelope_responseJ_descendant_epsSq` whose premises are
literally the binders of the frozen `multiscale_estimate`: the preceding-error
clause is supplied by that theorem's own induction state
`inductionState M (m-1) E`, restricted from `m - 1` to `l - 1`. -/
theorem exists_envelope_responseJ_descendant_of_inductionState
    (M : ABKModel d) {m l : ℤ} (hlm : l ≤ m) {R : TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d m) l)
    (E : {E : ℝ // 1 ≤ E})
    (hE : 15 * (Disorder.cstar M)⁻¹ ≤ (E : ℝ))
    (hgammaE : M.gamma ≤ ((E : ℝ)⁻¹) ^ 10)
    (hS : Algsuperdiff.Frozen.Section3.inductionState M (m - 1) E)
    (epsilon : ℝ) (hepsilon : epsilon ∈ Set.Ioc (0 : ℝ) (1 / 2))
    (hgate : M.gamma ≤ (homogenizationStepConst d)⁻¹ * ((E : ℝ)⁻¹) ^ 2 * epsilon ^ 2) :
    ∃ Y Z : CutoffSample d → ℝ,
      Measurable Y ∧ Measurable Z ∧
      IsBigOWith (cutoffSampleLaw M).toMeasure (gammaSigma 1) Y
          (epsilon ^ 2 * (E : ℝ) ^ 2 * M.gamma) ∧
        IsBigOWith (cutoffSampleLaw M).toMeasure (gammaSigma (1 / 4)) Z
            (epsilon ^ 2 * Real.exp (-(2 * ((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹))) ∧
          ∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure,
            ∀ L : ℤ,
              (L : ℝ) ≤ (l : ℝ) - 2 * homogenizationStepConst d * |Real.log epsilon| →
                ∀ e : Vec d, Book.Ch02.vecNorm e = 1 →
                  Book.Ch02.responseJ (Book.Ch02.cubeDomain R)
                      ((coefficientCutoffTriadicCoeffFamily M L omega).coeffOn R)
                      (Observable.inverseSqrtLoad (Annealed.sigmaBar M L) e)
                      (Observable.sqrtLoad (Annealed.sigmaBar M L) e) ≤
                    Y omega + Z omega :=
  exists_envelope_responseJ_descendant_epsSq M hlm hR E hE hgammaE
    (precedingError_of_inductionState (by omega) hS) epsilon hepsilon hgate

/-! ## 8. From unit directions to the loading ball of the localization legs

The printed display and the frozen root quantify over unit directions `|e| = 1`;
`Provider/Localization/Breakdown.lean` and `ResponseTransport`'s consumption
interface state the two breakdown legs over the loading ball `|v|^2 <= 2`, the
frame vectors `e_1 -+ e_2` of the paired families.  The passage between the two
is the quadratic homogeneity of `J`, at the price of the factor `2` the ball
costs.  Both lemmas are deterministic: no measure, no amplitude and no Orlicz
datum appears. -/

/-- **Quadratic homogeneity of the response in the loading direction.**  The two
comparator loads are linear in the direction, so `J` is quadratic in it. -/
theorem responseJ_load_smul {U : Book.Ch02.Domain d} (a : Book.Ch02.CoeffOn U)
    (sigma : Observable.PositiveScalar) (c : ℝ) (v : Vec d) :
    Book.Ch02.responseJ U a (Observable.inverseSqrtLoad sigma (c • v))
        (Observable.sqrtLoad sigma (c • v)) =
      c ^ 2 * Book.Ch02.responseJ U a (Observable.inverseSqrtLoad sigma v)
        (Observable.sqrtLoad sigma v) := by
  have h1 : Observable.inverseSqrtLoad sigma (c • v) =
      c • Observable.inverseSqrtLoad sigma v := smul_comm _ _ _
  have h2 : Observable.sqrtLoad sigma (c • v) = c • Observable.sqrtLoad sigma v :=
    smul_comm _ _ _
  rw [h1, h2, Book.Ch02.responseJ_smul]

/-- **The seam to the localization legs.**  A bound on the response over the
unit sphere --- the quantifier of `e.what.homogenization.gives` and of the frozen
homogenization step --- bounds it over the loading ball `|v|^2 <= 2` of the
breakdown legs, at the cost of the factor `2`.

The per-cube bound is the hypothesis of the statement, not a premise of the
module: nothing here asserts that such a bound holds. -/
theorem responseJ_le_two_mul_of_forall_unit {U : Book.Ch02.Domain d}
    (a : Book.Ch02.CoeffOn U) (sigma : Observable.PositiveScalar) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ e : Vec d, Book.Ch02.vecNorm e = 1 →
      Book.Ch02.responseJ U a (Observable.inverseSqrtLoad sigma e)
        (Observable.sqrtLoad sigma e) ≤ c)
    {v : Vec d} (hv : vecNormSq v ≤ 2) :
    Book.Ch02.responseJ U a (Observable.inverseSqrtLoad sigma v)
      (Observable.sqrtLoad sigma v) ≤ 2 * c := by
  rcases eq_or_ne v 0 with rfl | hv0
  · have hzero : Book.Ch02.responseJ U a (Observable.inverseSqrtLoad sigma 0)
        (Observable.sqrtLoad sigma 0) = 0 := by
      have hsmul := responseJ_load_smul a sigma 0 0
      simpa using hsmul
    rw [hzero]
    linarith
  · have hnsq : Book.Ch02.vecNorm v ^ 2 = vecNormSq v := Book.Ch02.vecNorm_sq_eq_vecNormSq v
    have hnnonneg : 0 ≤ Book.Ch02.vecNorm v := Book.Ch02.vecNorm_nonneg v
    have hnpos : 0 < Book.Ch02.vecNorm v := by
      rcases hnnonneg.lt_or_eq with hlt | heq
      · exact hlt
      · exact absurd (vecNormSq_eq_zero (by rw [← hnsq, ← heq]; ring)) hv0
    have hunit : Book.Ch02.vecNorm ((Book.Ch02.vecNorm v)⁻¹ • v) = 1 := by
      have hsq : Book.Ch02.vecNorm ((Book.Ch02.vecNorm v)⁻¹ • v) ^ 2 = 1 := by
        rw [Book.Ch02.vecNorm_sq_eq_vecNormSq, vecNormSq_smul, ← hnsq]
        field_simp
      nlinarith [Book.Ch02.vecNorm_nonneg ((Book.Ch02.vecNorm v)⁻¹ • v)]
    have hsplit : v = Book.Ch02.vecNorm v • ((Book.Ch02.vecNorm v)⁻¹ • v) := by
      rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hnpos), one_smul]
    calc Book.Ch02.responseJ U a (Observable.inverseSqrtLoad sigma v)
          (Observable.sqrtLoad sigma v)
        = Book.Ch02.vecNorm v ^ 2 *
            Book.Ch02.responseJ U a
              (Observable.inverseSqrtLoad sigma ((Book.Ch02.vecNorm v)⁻¹ • v))
              (Observable.sqrtLoad sigma ((Book.Ch02.vecNorm v)⁻¹ • v)) := by
            conv_lhs => rw [hsplit]
            rw [responseJ_load_smul]
      _ ≤ Book.Ch02.vecNorm v ^ 2 * c :=
          mul_le_mul_of_nonneg_left (h _ hunit) (sq_nonneg _)
      _ ≤ 2 * c := by
          have hle : Book.Ch02.vecNorm v ^ 2 ≤ 2 := by rw [hnsq]; exact hv
          nlinarith

end

end Algsuperdiff.Section3.Provider.MultiscaleEstimate
