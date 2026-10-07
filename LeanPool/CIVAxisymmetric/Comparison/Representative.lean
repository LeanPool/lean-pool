/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Comparison.EnergyInequality2
public import LeanPool.CIVAxisymmetric.Comparison.MollifiedEquation
public import Mathlib.Analysis.Calculus.BumpFunction.Basic
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# The representative lemma: an a.e. fundamental theorem of calculus, unconditional in `x`

`CIV/Comparison/EnergyInequality2.lean` proves the distributional fundamental theorem of
calculus `eq_add_intervalIntegral_of_pairing_eq`: a function `f` continuous on an open,
order-connected `I`, paired against every smooth compactly supported test function the same way
a locally integrable `h` is, equals a primitive of `h` throughout `I`. Applying that
theorem to `f = mollifySlice m ε q (x, ·)` — the shape `mollified_equation` supplies the pairing
for — needs two extra facts at the fixed spatial point `x`: continuity of the slice in time
(`hCont`), and local integrability in time of the right side of `eq:aniso:comparison:mollified`
(`hLoc`). Neither follows from the hypotheses of the comparison lemma
(`IsAdmissibleDrift`, `IsLocallyBoundedOn`, `IsDistributionalDriftDiffusion`): a two-function
counterexample differing only on the null slice `Vec m × {0}` gives mollified slices at `τ = 0`
that differ, so `hCont` is a genuine restriction on the chosen representative of `q`, not a
consequence of those hypotheses.

This file dispenses with both hypotheses by weakening the *conclusion* from "holds everywhere on
`I`" to "holds for a.e. `τ₁, τ₂ ∈ I`" wherever they are needed:

* `ae_ae_sub_eq_intervalIntegral_of_pairing_eq` is the a.e. weakening of
  `eq_add_intervalIntegral_of_pairing_eq`: `hfc : ContinuousOn f I` is replaced by
  `hfLoc : LocallyIntegrableOn f I volume`, and the conclusion becomes the *difference* identity
  `f τ₂ - f τ₁ = ∫ s in τ₁..τ₂, h s`, holding for a.e. `τ₁ ∈ I` and (the same null set) a.e.
  `τ₂ ∈ I`. Continuity enters the proof of the everywhere version only to promote the
  a.e.-constant conclusion of the abstract du Bois-Reymond argument
  (`ae_eq_zero_of_integral_contDiff_smul_eq_zero`) to an everywhere statement, and to supply
  integrability side conditions; dropping the promotion and re-deriving the side conditions from
  local integrability removes the need for it. Working with the *difference* rather than an
  absolute primitive additionally removes the unknown integration constant: it cancels between
  any two points where the a.e. identity holds.

* `locallyIntegrableOn_mollifySlice` and `locallyIntegrableOn_mollifiedRHS` supply the two local
  integrability facts the a.e. lemma needs, **unconditionally in `x`**, directly from the
  hypotheses `hB`, `hq`, `heq`, `hε` of the comparison lemma, with no `hCont`/`hLoc` hypothesis.
  The second is the substantial one: it repeats, at a smooth bump function centred at each point
  of `I`, exactly the integrability computation already carried out inside the proof of
  `mollified_equation` for whichever single test function that theorem is handed.

* `mollifySlice_ae_ae_sub_eq_intervalIntegral` combines the three: for every `x`, a.e. `τ₁ ∈ I`
  and a.e. `τ₂ ∈ I`, `mollifySlice m ε q (x, τ₂) - mollifySlice m ε q (x, τ₁)` equals the
  interval integral of the right side of `eq:aniso:comparison:mollified`. Compared with
  `CIV.mollifySlice_eq_add_intervalIntegral`, the same conclusion (as a difference, a.e. rather
  than everywhere) follows from `hB`, `hq`, `heq`, `hε` alone.

## Scope

The identity is proved for each fixed `x`, and the exceptional null set of pairs `(τ₁, τ₂)` may
depend on `x`. The joint statement, almost everywhere on `Vec m × I × I`, is
`CIV.mollifySlice_sub_eq_intervalIntegral_ae_prod`; the comparison proof uses it to choose a
reference time (`CIV.ae_isReferenceTime_mollifySlice`).
-/

public section

open MeasureTheory Set Filter Topology
open CKN

noncomputable section
namespace CIV

/-! ## Part 0: local helpers -/

/-- The product of a function locally integrable on an open `I` with a continuous, compactly
supported function whose support lies in `I` is integrable, with no continuity hypothesis on the
first factor. This is the local-integrability replacement for
`EnergyInequality2.integrable_mul_of_continuousOn_hasCompactSupport`. -/
theorem integrable_mul_of_locallyIntegrableOn_hasCompactSupport {I : Set ℝ}
    {f ψ : ℝ → ℝ} (hf : LocallyIntegrableOn f I volume) (hψ : Continuous ψ)
    (hψc : HasCompactSupport ψ) (hψI : tsupport ψ ⊆ I) :
    Integrable (fun τ => f τ * ψ τ) volume := by
  have hK : IsCompact (tsupport ψ) := hψc
  have hKm : MeasurableSet (tsupport ψ) := (isClosed_tsupport ψ).measurableSet
  have hfK : IntegrableOn f (tsupport ψ) volume := hf.integrableOn_compact_subset hψI hK
  have hmulK : IntegrableOn (fun τ => f τ * ψ τ) (tsupport ψ) volume :=
    hfK.mul_continuousOn_of_subset hψ.continuousOn hKm hK (Subset.refl _)
  have hzero : ∀ τ, τ ∉ tsupport ψ → f τ * ψ τ = 0 := fun τ hτ => by
    rw [image_eq_zero_of_notMem_tsupport hτ, mul_zero]
  have hind : Integrable ((tsupport ψ).indicator (fun τ => f τ * ψ τ)) volume :=
    (integrable_indicator_iff hKm).mpr hmulK
  have hfun : (tsupport ψ).indicator (fun τ => f τ * ψ τ) = fun τ => f τ * ψ τ := by
    funext τ
    by_cases hτ : τ ∈ tsupport ψ
    · rw [Set.indicator_of_mem hτ]
    · rw [Set.indicator_of_notMem hτ, hzero τ hτ]
  rwa [hfun] at hind

/-- A smooth, compactly supported bump function centred at a point of an open set `I`, with
support inside `I` and equal to `1` on a smaller closed ball around the centre. -/
theorem exists_bump_eq_one_near_of_isOpen {I : Set ℝ} (hI : IsOpen I) {τ₀ : ℝ} (hτ₀ : τ₀ ∈ I) :
    ∃ χ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ I ∧
      ∃ r : ℝ, 0 < r ∧ ∀ τ ∈ Metric.closedBall τ₀ r, χ τ = 1 := by
  obtain ⟨r', hr', hballI⟩ := Metric.mem_nhds_iff.mp (hI.mem_nhds hτ₀)
  set r : ℝ := r' / 2 with hrdef
  have hrpos : 0 < r := by positivity
  set bump : ContDiffBump τ₀ := ⟨r / 2, r, by positivity, by linarith only [hrpos]⟩ with hbumpdef
  have hcbsub : Metric.closedBall τ₀ r ⊆ Metric.ball τ₀ r' :=
    Metric.closedBall_subset_ball (by rw [hrdef]; linarith only [hr'])
  refine ⟨bump, bump.contDiff, bump.hasCompactSupport, ?_, r / 2, by positivity,
    fun τ hτ => bump.one_of_mem_closedBall hτ⟩
  rw [bump.tsupport_eq]
  exact hcbsub.trans hballI

/-- If `f` multiplied by a bump function `χ` equal to `1` on `closedBall τ₀ r` is integrable,
then `f` alone is integrable on that ball. -/
theorem integrableOn_closedBall_of_integrable_mul_bump {f χ : ℝ → ℝ} {τ₀ r : ℝ}
    (hone : ∀ τ ∈ Metric.closedBall τ₀ r, χ τ = 1)
    (hint : Integrable (fun τ => f τ * χ τ) volume) :
    IntegrableOn f (Metric.closedBall τ₀ r) volume := by
  have hcong : (fun τ => f τ * χ τ) =ᵐ[volume.restrict (Metric.closedBall τ₀ r)] f :=
    (ae_restrict_iff' measurableSet_closedBall).mpr
      (Filter.Eventually.of_forall fun τ hτ => by simp only [hone τ hτ, mul_one])
  exact hint.restrict.congr hcong

/-! ## Part 1: the a.e. distributional fundamental theorem of calculus -/

/-- The a.e. weakening of `eq_add_intervalIntegral_of_pairing_eq`: replacing continuity of `f`
on `I` by mere local integrability, and reading off the *difference* `f τ₂ - f τ₁` instead of an
absolute primitive (which removes the unknown integration constant, since it cancels), the same
pairing hypothesis gives the fundamental-theorem-of-calculus identity for a.e. `τ₁ ∈ I` and a.e.
`τ₂ ∈ I`. -/
theorem ae_ae_sub_eq_intervalIntegral_of_pairing_eq
    {I : Set ℝ} (hI : IsOpen I) (hIoc : I.OrdConnected) {f h : ℝ → ℝ}
    (hfLoc : LocallyIntegrableOn f I volume) (hh : LocallyIntegrableOn h I volume)
    (hDist : ∀ χ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ → HasCompactSupport χ → tsupport χ ⊆ I →
      ∫ τ, f τ * (-(deriv χ τ)) = ∫ τ, χ τ * h τ)
    {τ₀ : ℝ} (hτ₀ : τ₀ ∈ I) :
    ∀ᵐ τ₁ ∂(volume.restrict I), ∀ᵐ τ₂ ∂(volume.restrict I),
      f τ₂ - f τ₁ = ∫ s in τ₁..τ₂, h s := by
  set F : ℝ → ℝ := fun τ' => f τ₀ + ∫ s in τ₀..τ', h s with hFdef
  have hFcont : ContinuousOn F I :=
    continuousOn_const.add (continuousOn_primitive_of_isOpen hI hIoc hτ₀ hh)
  have hFLoc : LocallyIntegrableOn F I volume := hFcont.locallyIntegrableOn hI.measurableSet
  have hfFLoc : LocallyIntegrableOn (fun τ' => f τ' - F τ') I volume := hfLoc.sub hFLoc
  -- a fixed reference bump `β` at `τ₀`, compactly supported inside `I`, with `∫ β = 1`
  obtain ⟨r', hr', hballI⟩ := Metric.mem_nhds_iff.mp (hI.mem_nhds hτ₀)
  set r : ℝ := r' / 2 with hrdef
  have hrpos : 0 < r := by positivity
  have hcbsub : Metric.closedBall τ₀ r ⊆ Metric.ball τ₀ r' :=
    Metric.closedBall_subset_ball (by rw [hrdef]; linarith only [hr'])
  have hclosedballI : Metric.closedBall τ₀ r ⊆ I := hcbsub.trans hballI
  set bump : ContDiffBump τ₀ := ⟨r / 2, r, by positivity, by linarith only [hrpos]⟩ with hbumpdef
  set β : ℝ → ℝ := bump.normed volume with hβdef
  have hβcontdiff : ContDiff ℝ (⊤ : ℕ∞) β := bump.contDiff_normed
  have hβcs : HasCompactSupport β := bump.hasCompactSupport_normed
  have hβsupp : tsupport β = Metric.closedBall τ₀ bump.rOut := bump.tsupport_normed_eq
  have hβI : tsupport β ⊆ I := by rw [hβsupp]; exact hclosedballI
  have hβint : ∫ x, β x = 1 := bump.integral_normed
  set c : ℝ := ∫ τ', (f τ' - F τ') * β τ' with hcdef
  -- the pairing of `f - F` against a general test function reduces to `c` times its integral
  have hpairing : ∀ ρ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ρ → HasCompactSupport ρ → tsupport ρ ⊆ I →
      ∫ τ', (f τ' - F τ') * ρ τ' = c * ∫ τ', ρ τ' := by
    intro ρ hρ hρc hρI
    set ψ : ℝ → ℝ := ρ - (fun y => (∫ x, ρ x) * β y) with hψdef
    have hψcd : ContDiff ℝ (⊤ : ℕ∞) ψ := hρ.sub (contDiff_const.mul hβcontdiff)
    have hcβcs : HasCompactSupport (fun y => (∫ x, ρ x) * β y) := hβcs.mul_left
    have hψcs : HasCompactSupport ψ := hρc.sub hcβcs
    have hcβI : tsupport (fun y => (∫ x, ρ x) * β y) ⊆ I :=
      tsupport_subset_of_eq_zero_of_notMem (isClosed_tsupport β)
        (fun y hy => by rw [image_eq_zero_of_notMem_tsupport hy, mul_zero]) |>.trans hβI
    have hψI : tsupport ψ ⊆ I := (tsupport_sub_subset ρ _).trans (union_subset hρI hcβI)
    have hψmean : ∫ τ', ψ τ' = 0 := by
      have hint1 : Integrable ρ volume := hρ.continuous.integrable_of_hasCompactSupport hρc
      have hint2 : Integrable (fun y => (∫ x, ρ x) * β y) volume :=
        (hβcontdiff.continuous.integrable_of_hasCompactSupport hβcs).const_mul _
      rw [hψdef, Pi.sub_def, MeasureTheory.integral_sub hint1 hint2,
        MeasureTheory.integral_const_mul, hβint, mul_one, sub_self]
    obtain ⟨χ, hχ, hχc, hχI, hχderiv⟩ :=
      exists_contDiff_hasCompactSupport_deriv_eq_neg_of_integral_eq_zero hI hIoc hψcd hψcs hψI
        hψmean
    have hEq1 : ∫ τ', f τ' * ψ τ' = ∫ τ', χ τ' * h τ' := by
      have hd := hDist χ hχ hχc hχI
      rw [hχderiv] at hd
      simpa only [Pi.neg_apply, neg_neg] using hd
    have hEq2 : ∫ τ', F τ' * ψ τ' = ∫ τ', χ τ' * h τ' := by
      have hstep :=
        integral_primitive_mul_deriv_eq_integral_mul_of_isOpen (f τ₀) hI hIoc hτ₀ hh hχ hχc hχI
      rw [hχderiv] at hstep
      simp only [Pi.neg_apply, neg_neg] at hstep
      rw [hFdef]
      exact hstep
    have hfψ_int : Integrable (fun τ' => f τ' * ψ τ') volume :=
      integrable_mul_of_locallyIntegrableOn_hasCompactSupport hfLoc hψcd.continuous hψcs hψI
    have hFψ_int : Integrable (fun τ' => F τ' * ψ τ') volume :=
      integrable_mul_of_locallyIntegrableOn_hasCompactSupport hFLoc hψcd.continuous hψcs hψI
    have hdiff : ∫ τ', (f τ' - F τ') * ψ τ' = 0 := by
      have heq : (fun τ' => (f τ' - F τ') * ψ τ') = (fun τ' => f τ' * ψ τ' - F τ' * ψ τ') := by
        funext τ'; ring
      rw [heq, MeasureTheory.integral_sub hfψ_int hFψ_int, hEq1, hEq2, sub_self]
    have hfFρ_int : Integrable (fun τ' => (f τ' - F τ') * ρ τ') volume :=
      integrable_mul_of_locallyIntegrableOn_hasCompactSupport hfFLoc hρ.continuous hρc hρI
    have hfFβ_int : Integrable (fun τ' => (f τ' - F τ') * β τ') volume :=
      integrable_mul_of_locallyIntegrableOn_hasCompactSupport hfFLoc hβcontdiff.continuous hβcs
        hβI
    have hexpand : ∫ τ', (f τ' - F τ') * ψ τ'
        = (∫ τ', (f τ' - F τ') * ρ τ') - (∫ x, ρ x) * ∫ τ', (f τ' - F τ') * β τ' := by
      have heq2 : (fun τ' => (f τ' - F τ') * ψ τ')
          = (fun τ' => (f τ' - F τ') * ρ τ' - (∫ x, ρ x) * ((f τ' - F τ') * β τ')) := by
        funext τ'
        rw [hψdef]
        simp only [Pi.sub_apply]
        ring
      rw [heq2, MeasureTheory.integral_sub hfFρ_int (hfFβ_int.const_mul _),
        MeasureTheory.integral_const_mul]
    rw [hexpand, ← hcdef, sub_eq_zero] at hdiff
    rw [hdiff]
    ring
  -- the same pairing, shifted by the constant `c`, vanishes for every test function
  have hgpairing : ∀ ρ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ρ → HasCompactSupport ρ → tsupport ρ ⊆ I →
      ∫ τ', ((f τ' - F τ') - c) * ρ τ' = 0 := by
    intro ρ hρ hρc hρI
    have hbase := hpairing ρ hρ hρc hρI
    have hfFρ_int : Integrable (fun τ' => (f τ' - F τ') * ρ τ') volume :=
      integrable_mul_of_locallyIntegrableOn_hasCompactSupport hfFLoc hρ.continuous hρc hρI
    have hcρ_int : Integrable (fun τ' => c * ρ τ') volume :=
      (hρ.continuous.integrable_of_hasCompactSupport hρc).const_mul _
    have heq : (fun τ' => ((f τ' - F τ') - c) * ρ τ')
        = (fun τ' => (f τ' - F τ') * ρ τ' - c * ρ τ') := by funext τ'; ring
    rw [heq, MeasureTheory.integral_sub hfFρ_int hcρ_int, MeasureTheory.integral_const_mul, hbase]
    ring
  have hgloc : LocallyIntegrableOn (fun τ' => (f τ' - F τ') - c) I volume :=
    hfFLoc.sub (locallyIntegrableOn_const c)
  have hgae : ∀ᵐ x ∂volume, x ∈ I → (f x - F x) - c = 0 := by
    apply IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero hI hgloc
    intro ρ hρ hρc hρI
    have hg := hgpairing ρ hρ hρc hρI
    simp only [smul_eq_mul]
    calc ∫ x, ρ x * (f x - F x - c) = ∫ x, (f x - F x - c) * ρ x :=
          MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _)
      _ = 0 := hg
  have hgae' : (fun τ' => (f τ' - F τ') - c) =ᵐ[volume.restrict I] 0 :=
    (ae_restrict_iff' hI.measurableSet).mpr
      (by filter_upwards [hgae] with x hx hxmem; exact hx hxmem)
  -- from here: no continuity, only the a.e. statement above
  have hgood2 : ∀ᵐ τ' ∂(volume.restrict I), f τ' = (f τ₀ + c) + ∫ s in τ₀..τ', h s := by
    filter_upwards [hgae'] with τ' hτ'
    simp only [Pi.zero_apply, hFdef] at hτ'
    linarith only [hτ']
  have hmemI : ∀ᵐ τ ∂(volume.restrict I), τ ∈ I := ae_restrict_mem hI.measurableSet
  filter_upwards [hgood2, hmemI] with τ₁ hτ1 hτ1mem
  filter_upwards [hgood2, hmemI] with τ₂ hτ2 hτ2mem
  have hUIcc1 : uIcc τ₀ τ₁ ⊆ I := hIoc.uIcc_subset hτ₀ hτ1mem
  have hUIcc2 : uIcc τ₀ τ₂ ⊆ I := hIoc.uIcc_subset hτ₀ hτ2mem
  have hInt1 : IntervalIntegrable h volume τ₀ τ₁ :=
    intervalIntegrable_iff.mpr
      ((hh.integrableOn_compact_subset hUIcc1 isCompact_uIcc).mono_set uIoc_subset_uIcc)
  have hInt2 : IntervalIntegrable h volume τ₀ τ₂ :=
    intervalIntegrable_iff.mpr
      ((hh.integrableOn_compact_subset hUIcc2 isCompact_uIcc).mono_set uIoc_subset_uIcc)
  have hChasles : (∫ s in τ₀..τ₂, h s) - ∫ s in τ₀..τ₁, h s = ∫ s in τ₁..τ₂, h s :=
    intervalIntegral.integral_interval_sub_left hInt2 hInt1
  rw [hτ1, hτ2]
  linarith only [hChasles]

/-! ## Part 2: local integrability of the mollified slice, unconditional in `x` -/

/-- The mollified slice `mollifySlice m ε q (x, ·)` is locally integrable in time on `I`, for
**every** spatial point `x`, from `hq : IsLocallyBoundedOn` alone. -/
theorem locallyIntegrableOn_mollifySlice {m : ℕ} {ε : ℝ} (hε : 0 < ε) (x : Vec m) {I : Set ℝ}
    (hI : IsOpen I) {q : Vec m × ℝ → ℝ} (hq : IsLocallyBoundedOn m I q) :
    LocallyIntegrableOn (fun τ => mollifySlice m ε q (x, τ)) I volume := by
  intro τ₀ hτ₀
  obtain ⟨χ, hχ, hχc, hχI, r, hr, hone⟩ := exists_bump_eq_one_near_of_isOpen hI hτ₀
  have hint : Integrable (fun τ => mollifySlice m ε q (x, τ) * χ τ) volume :=
    integrable_mollifySlice_mul hε x hq hχ hχc hχI
  exact ⟨Metric.closedBall τ₀ r, mem_nhdsWithin_of_mem_nhds (Metric.closedBall_mem_nhds τ₀ hr),
    integrableOn_closedBall_of_integrable_mul_bump hone hint⟩

/-! ## Part 3: local integrability of the mollified right side, unconditional in `x` -/

/-- For every spatial point `x`, the right side of `eq:aniso:comparison:mollified` is locally
integrable in time on `I`, directly from the hypotheses `hB`, `hq`, `heq` of the comparison
lemma, with no `hLoc` hypothesis. The proof repeats, at a
bump function centred at each point of `I`, exactly the integrability computation the proof of
`mollified_equation` performs for whichever single test function that theorem is handed. -/
theorem locallyIntegrableOn_mollifiedRHS {m d : ℕ} {ε : ℝ} (hε : 0 < ε) (x : Vec m) {I : Set ℝ}
    (hI : IsOpen I) {B : Vec m × ℝ → Vec m} {divB q : Vec m × ℝ → ℝ}
    (hB : IsAdmissibleDrift m I B divB) (hq : IsLocallyBoundedOn m I q)
    (heq : IsDistributionalDriftDiffusion m d I B divB q) :
    LocallyIntegrableOn (fun τ => partialLaplacian m d (mollifySlice m ε q) (x, τ)
        - gradPair m (mollifySlice m ε q) (x, τ) (B (x, τ))
        + diPernaLionsCommutator m ε (fun y => B (y, τ)) (fun y => divB (y, τ))
            (fun y => q (y, τ)) x) I volume := by
  intro τ₀ hτ₀
  obtain ⟨χ, hχ, hχc, hχI, r, hr, hone⟩ := exists_bump_eq_one_near_of_isOpen hI hτ₀
  have hχd : Differentiable ℝ χ := hχ.differentiable (by simp)
  have hφ : mollifierTest m ε x χ ∈ testFunctions m I :=
    mollifierTest_mem_testFunctions hε x hχ hχc hχI
  have hJm : MeasurableSet (tsupport χ) := (isClosed_tsupport χ).measurableSet
  obtain ⟨M, -, hMae⟩ := hq.ae_slice_bound hχc hχI
  obtain ⟨Λ, hΛae⟩ := hB.ae_slice hχc hχI
  have hBm : ∀ τ : ℝ, Measurable fun y : Vec m => B (y, τ) := fun τ =>
    hB.1.comp measurable_prodMk_right
  have hdm : ∀ τ : ℝ, Measurable fun y : Vec m => divB (y, τ) := fun τ =>
    hB.2.1.comp measurable_prodMk_right
  have hqmAll : ∀ᵐ τ ∂(volume : Measure ℝ), τ ∈ I →
      AEStronglyMeasurable (fun y : Vec m => q (y, τ)) volume :=
    (ae_restrict_iff' hI.measurableSet).mp hq.ae_slice_measurable
  have hMall : ∀ᵐ τ ∂(volume : Measure ℝ), τ ∈ tsupport χ → ∀ᵐ y : Vec m, |q (y, τ)| ≤ M :=
    (ae_restrict_iff' hJm).mp hMae
  have hΛall : ∀ᵐ τ ∂(volume : Measure ℝ), τ ∈ tsupport χ →
      ((∀ y, ‖B (y, τ)‖ ≤ (Λ : ℝ)) ∧ LipschitzWith Λ (fun y => B (y, τ)) ∧
        (∀ y, |divB (y, τ)| ≤ (Λ : ℝ))) := (ae_restrict_iff' hJm).mp hΛae
  have hgood : ∀ᵐ τ ∂(volume : Measure ℝ),
      (∫ y : Vec m, q (y, τ) * (-(timeDeriv m (mollifierTest m ε x χ) (y, τ))
          - gradPair m (mollifierTest m ε x χ) (y, τ) (B (y, τ))
          - divB (y, τ) * mollifierTest m ε x χ (y, τ)
          - partialLaplacian m d (mollifierTest m ε x χ) (y, τ)))
        = mollifySlice m ε q (x, τ) * (-(deriv χ τ))
          - χ τ * (partialLaplacian m d (mollifySlice m ε q) (x, τ)
              - gradPair m (mollifySlice m ε q) (x, τ) (B (x, τ))
              + diPernaLionsCommutator m ε (fun y => B (y, τ)) (fun y => divB (y, τ))
                  (fun y => q (y, τ)) x) := by
    filter_upwards [hqmAll, hMall, hΛall] with τ h1 h2 h3
    by_cases hτ : τ ∈ tsupport χ
    · exact integral_slice_testedIntegrand d hε x hχd (h1 (hχI hτ)) (h2 hτ) (hBm τ) (hdm τ)
        (h3 hτ).1 (h3 hτ).2.2
    · have hχ0 : χ τ = 0 := image_eq_zero_of_notMem_tsupport hτ
      have hdχ0 : deriv χ τ = 0 := deriv_of_notMem_tsupport hτ
      have hz : ∀ y : Vec m, q (y, τ) * (-(timeDeriv m (mollifierTest m ε x χ) (y, τ))
          - gradPair m (mollifierTest m ε x χ) (y, τ) (B (y, τ))
          - divB (y, τ) * mollifierTest m ε x χ (y, τ)
          - partialLaplacian m d (mollifierTest m ε x χ) (y, τ)) = 0 := by
        intro y
        rw [timeDeriv_mollifierTest ε x hχd, gradPair_mollifierTest ε x χ,
          partialLaplacian_mollifierTest d ε x χ, mollifierTest_apply, hχ0, hdχ0]
        ring
      rw [integral_congr_ae (g := fun _ : Vec m => (0 : ℝ))
        (Filter.Eventually.of_forall hz), hχ0, hdχ0]
      simp
  have hzero := integral_integral_testedIntegrand d heq hφ
  have hprod := integrable_testedIntegrand d heq hφ
  have hvol : (volume : Measure (Vec m × ℝ))
      = (volume : Measure (Vec m)).prod (volume : Measure ℝ) := Measure.volume_eq_prod _ _
  have hprod' : Integrable (fun z : Vec m × ℝ => q z *
      (-(timeDeriv m (mollifierTest m ε x χ) z)
        - gradPair m (mollifierTest m ε x χ) z (B z)
        - divB z * mollifierTest m ε x χ z
        - partialLaplacian m d (mollifierTest m ε x χ) z))
      ((volume : Measure (Vec m)).prod (volume : Measure ℝ)) := by rwa [hvol] at hprod
  have hAint : Integrable (fun τ : ℝ => ∫ y : Vec m,
      q (y, τ) * (-(timeDeriv m (mollifierTest m ε x χ) (y, τ))
        - gradPair m (mollifierTest m ε x χ) (y, τ) (B (y, τ))
        - divB (y, τ) * mollifierTest m ε x χ (y, τ)
        - partialLaplacian m d (mollifierTest m ε x χ) (y, τ))) volume :=
    hprod'.integral_prod_right
  have hdχc : HasCompactSupport (fun τ : ℝ => -(deriv χ τ)) := by
    have h : HasCompactSupport (-(deriv χ)) := (hχc.deriv).neg
    exact h
  have hdχI : tsupport (fun τ : ℝ => -(deriv χ τ)) ⊆ I := by
    have h : tsupport (-(deriv χ)) ⊆ I :=
      (tsupport_neg (deriv χ)) ▸ tsupport_deriv_subset.trans hχI
    exact h
  have hLint : Integrable (fun τ : ℝ => mollifySlice m ε q (x, τ) * (-(deriv χ τ))) volume :=
    integrable_mollifySlice_mul hε x hq (hχ.deriv'.neg) hdχc hdχI
  have hRint : Integrable (fun τ : ℝ => χ τ *
      (partialLaplacian m d (mollifySlice m ε q) (x, τ)
        - gradPair m (mollifySlice m ε q) (x, τ) (B (x, τ))
        + diPernaLionsCommutator m ε (fun y => B (y, τ)) (fun y => divB (y, τ))
            (fun y => q (y, τ)) x)) volume := by
    refine (hLint.sub hAint).congr ?_
    filter_upwards [hgood] with τ hτ
    simp only [Pi.sub_apply]
    linarith only [hτ]
  have hRint' : Integrable (fun τ : ℝ => (partialLaplacian m d (mollifySlice m ε q) (x, τ)
      - gradPair m (mollifySlice m ε q) (x, τ) (B (x, τ))
      + diPernaLionsCommutator m ε (fun y => B (y, τ)) (fun y => divB (y, τ))
          (fun y => q (y, τ)) x) * χ τ) volume := by
    refine hRint.congr (Filter.Eventually.of_forall fun τ => ?_)
    exact mul_comm _ _
  exact ⟨Metric.closedBall τ₀ r, mem_nhdsWithin_of_mem_nhds (Metric.closedBall_mem_nhds τ₀ hr),
    integrableOn_closedBall_of_integrable_mul_bump hone hRint'⟩

/-! ## Part 4: the representative lemma -/

/-- **The representative lemma.** For every spatial point `x` and a.e. `τ₁, τ₂ ∈ I`, the
mollified slice's change between `τ₁` and `τ₂` equals the interval integral of the right side of
`eq:aniso:comparison:mollified`. This is the conclusion of
`CIV.mollifySlice_eq_add_intervalIntegral` without its hypotheses `hCont`/`hLoc`, as an a.e.
difference identity following from the hypotheses `hB`, `hq`, `heq`, `hε` of the comparison
lemma alone. -/
theorem mollifySlice_ae_ae_sub_eq_intervalIntegral {m d : ℕ} {I : Set ℝ} (hI : IsOpen I)
    (hIoc : I.OrdConnected) {B : Vec m × ℝ → Vec m} {divB q : Vec m × ℝ → ℝ}
    (hB : IsAdmissibleDrift m I B divB) (hq : IsLocallyBoundedOn m I q)
    (heq : IsDistributionalDriftDiffusion m d I B divB q) {ε : ℝ} (hε : 0 < ε) (x : Vec m)
    {τ₀ : ℝ} (hτ₀ : τ₀ ∈ I) :
    ∀ᵐ τ₁ ∂(volume.restrict I), ∀ᵐ τ₂ ∂(volume.restrict I),
      mollifySlice m ε q (x, τ₂) - mollifySlice m ε q (x, τ₁)
        = ∫ s in τ₁..τ₂, (partialLaplacian m d (mollifySlice m ε q) (x, s)
            - gradPair m (mollifySlice m ε q) (x, s) (B (x, s))
            + diPernaLionsCommutator m ε (fun y => B (y, s)) (fun y => divB (y, s))
                (fun y => q (y, s)) x) := by
  refine ae_ae_sub_eq_intervalIntegral_of_pairing_eq hI hIoc
    (locallyIntegrableOn_mollifySlice hε x hI hq)
    (locallyIntegrableOn_mollifiedRHS hε x hI hB hq heq) ?_ hτ₀
  intro χ hχ hχc hχI
  exact mollified_equation m d I hI B divB q hB hq heq hε x χ hχ hχc hχI

end CIV
