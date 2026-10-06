/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# The distributional fundamental theorem of calculus, and the comparison energy inequality

`CIV.Comparison.EnergyInequality` proves the two easy pieces of the Grönwall step of
`lem:aniso:comparison` — the support/integrability facts about `comparisonEnergy` and the
integral-form Grönwall inequality itself — with the integrated energy inequality
`eq:aniso:comparison:positive:energy` as a hypothesis (`hineq` of
`comparisonEnergy_le_exp_mul_integral_sq`). That integrated inequality is obtained from the
mollified equation `eq:aniso:comparison:mollified` (`mollified_equation`) in three stages:
(1) upgrading the time-tested identity `mollified_equation` delivers into the
fundamental-theorem-of-calculus statement that the mollified slice *is* the primitive of the right
side of `eq:aniso:comparison:mollified`; (2) a Green identity and energy computation testing that
identity against `(q_ε - Ψ_σ)_+`, which is only Lipschitz; (3) passing to the limit in a
regularization parameter. This module proves stage (1) completely, in the generality needed to feed
`mollified_equation`'s exact conclusion shape.

## Main result

`eq_add_intervalIntegral_of_pairing_eq`: if `f` is continuous on an open, order connected `I`,
`h` is locally integrable on `I`, and `f` obeys the tested identity `∫ f (-χ') = ∫ χ h` for every
`χ` that is `ContDiff ℝ (⊤ : ℕ∞)`, compactly supported, with support in `I` — the shape
`mollified_equation` delivers with `f τ = q_ε(x, τ)` and `h` the right side of
`eq:aniso:comparison:mollified` at a fixed `x` — then `f` is literally the primitive of `h`:
`f τ = f τ₀ + ∫ s in τ₀..τ, h s` for every `τ₀, τ ∈ I`.

The proof decomposes an arbitrary smooth compactly supported test function `ρ` against a fixed
reference bump `β` (`∫ β = 1`, built from `ContDiffBump`) into a mean-zero part and a multiple of
`β`. The mean-zero part is the negative derivative of a compactly supported primitive
(`exists_contDiff_hasCompactSupport_deriv_eq_neg_of_integral_eq_zero`), so the hypothesis applies
to it directly; the primitive `F` of `h` obeys the same tested identity against that same `χ`
(`integral_primitive_mul_deriv_eq_integral_mul_of_isOpen`), proved through the integration by parts
already in Mathlib for `AbsolutelyContinuousOnInterval` functions together with the interval form
of the Lebesgue differentiation theorem (`IntervalIntegrable.ae_hasDerivAt_integral`) — not a hand
Fubini argument. Comparing the two identities and testing again against `β` pins `f - F` to a
constant on `I` via `ae_eq_zero_of_integral_contDiff_smul_eq_zero`, and evaluating at `τ₀` shows
that constant is `0`.

## Use

`eq_add_intervalIntegral_of_pairing_eq` is applied to `mollified_equation` in
`CIV.mollifySlice_eq_add_intervalIntegral`, which takes continuity in time of the mollified slice
and local integrability of the mollified right side as explicit hypotheses.
`CIV.ae_ae_sub_eq_intervalIntegral_of_pairing_eq` is the almost-everywhere version without the
continuity hypothesis; it gives `CIV.mollifySlice_ae_ae_sub_eq_intervalIntegral` from the
hypotheses of the comparison lemma alone.

For stages (2)-(3), note that the natural closed form for the Kato regularization,
`Φ_κ(g) = (g + √(g² + κ²)) / 2 − κ/2`, does **not** tend to `0` as `g → -∞`: it tends to `-κ/2`.
Once `v_ε = (q_ε - Ψ_σ)_+` is compactly supported and `Φ_κ` is applied to `q_ε - Ψ_σ` directly
(which is unbounded below away from the support of `v_ε`), the energy `∫ Φ_κ(q_ε - Ψ_σ)²` over all
of `Vec m` is **not finite** for a fixed `κ > 0`, since the integrand tends to the nonzero constant
`κ²/4` at spatial infinity while `Vec m` has infinite measure. `CIV.Comparison.EnergyInequality3`
therefore applies a `κ`-independent spatial truncation (`CIV.mollifierCutoff`) before the Kato
step.
-/

public section

open MeasureTheory Set Filter Topology

noncomputable section
namespace CIV

/-- A nonempty compact set of reals lies in the closed interval spanned by its own least and
greatest elements. -/
theorem exists_Icc_subset_of_isCompact {s : Set ℝ} (hs : IsCompact s) (hne : s.Nonempty) :
    ∃ p ∈ s, ∃ q ∈ s, s ⊆ Icc p q := by
  obtain ⟨p, hp, hpmin⟩ := hs.exists_isMinOn hne continuousOn_id
  obtain ⟨q, hq, hqmax⟩ := hs.exists_isMaxOn hne continuousOn_id
  exact ⟨p, hp, q, hq, fun x hx => ⟨hpmin hx, hqmax hx⟩⟩

/-- A point of an open set has a strictly smaller neighbour still inside the set. -/
theorem exists_lt_mem_of_isOpen {I : Set ℝ} (hI : IsOpen I) {p : ℝ} (hp : p ∈ I) :
    ∃ p' < p, p' ∈ I := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hI.mem_nhds hp)
  refine ⟨p - ε / 2, by linarith only [hε], hball ?_⟩
  rw [Metric.mem_ball, Real.dist_eq, show p - ε / 2 - p = -(ε / 2) by ring, abs_neg,
    abs_of_pos (by linarith only [hε])]
  linarith only [hε]

/-- A point of an open set has a strictly larger neighbour still inside the set. -/
theorem exists_gt_mem_of_isOpen {I : Set ℝ} (hI : IsOpen I) {q : ℝ} (hq : q ∈ I) :
    ∃ q' > q, q' ∈ I := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hI.mem_nhds hq)
  refine ⟨q + ε / 2, by linarith only [hε], hball ?_⟩
  rw [Metric.mem_ball, Real.dist_eq, show q + ε / 2 - q = ε / 2 by ring,
    abs_of_pos (by linarith only [hε])]
  linarith only [hε]

/-- A function vanishing off a closed set has its topological support inside that set. -/
theorem tsupport_subset_of_eq_zero_of_notMem {f : ℝ → ℝ} {K : Set ℝ} (hK : IsClosed K)
    (hf : ∀ x ∉ K, f x = 0) : tsupport f ⊆ K := by
  have hsupp : Function.support f ⊆ K := fun x hx => by
    by_contra hxK
    exact hx (hf x hxK)
  calc tsupport f = closure (Function.support f) := rfl
    _ ⊆ closure K := closure_mono hsupp
    _ = K := hK.closure_eq

/-- A smooth, mean-zero, compactly supported function with support inside an open, order
connected `I` is the negative derivative of a smooth compactly supported function with support
still inside `I`. -/
theorem exists_contDiff_hasCompactSupport_deriv_eq_neg_of_integral_eq_zero
    {I : Set ℝ} (hI : IsOpen I) (hIoc : I.OrdConnected) {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) (hψI : tsupport ψ ⊆ I)
    (hmean : ∫ τ, ψ τ = 0) :
    ∃ χ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ I ∧
      deriv χ = -ψ := by
  rcases (tsupport ψ).eq_empty_or_nonempty with hempty | hne
  · have hψ0 : ψ = 0 :=
      Function.support_eq_empty_iff.mp (subset_empty_iff.mp (hempty ▸ subset_tsupport ψ))
    refine ⟨fun _ => 0, contDiff_const, ?_, ?_, ?_⟩
    · exact HasCompactSupport.intro isCompact_empty (fun x _ => rfl)
    · simp
    · funext τ; simp [hψ0]
  · obtain ⟨p, hp, q, hq, hpq⟩ := exists_Icc_subset_of_isCompact hψc hne
    have hpleq : p ≤ q := (hpq hp).2
    have hpI : p ∈ I := hψI hp
    have hqI : q ∈ I := hψI hq
    obtain ⟨p', hp'lt, hp'I⟩ := exists_lt_mem_of_isOpen hI hpI
    obtain ⟨q', hq'gt, hq'I⟩ := exists_gt_mem_of_isOpen hI hqI
    have hIccI : Icc p' q' ⊆ I := hIoc.out hp'I hq'I
    set χ : ℝ → ℝ := fun τ => -(∫ x in p..τ, ψ x) with hχdef
    have hcont : Continuous ψ := hψ.continuous
    have hderiv : ∀ τ, HasDerivAt χ (-(ψ τ)) τ :=
      fun τ => (hcont.integral_hasStrictDerivAt p τ).hasDerivAt.neg
    have hdiff : Differentiable ℝ χ := fun τ => (hderiv τ).differentiableAt
    have hderiveq : deriv χ = -ψ := funext fun τ => (hderiv τ).deriv
    have hzero : ∀ τ ∉ Icc p' q', χ τ = 0 := by
      intro τ hτ
      simp only [Set.mem_Icc, not_and_or, not_le] at hτ
      rcases hτ with hlt | hgt
      · -- τ < p' < p: ψ vanishes on the whole of `Ico τ p`
        have htp : τ ≤ p := (hlt.trans hp'lt).le
        have hEqOn : Set.EqOn ψ 0 (Ico τ p) := by
          intro x hx
          apply image_eq_zero_of_notMem_tsupport
          intro hxs
          have hxpq := hpq hxs
          exact absurd hxpq.1 (not_le.mpr hx.2)
        have hzint : (∫ x in τ..p, ψ x) = 0 := by
          rw [intervalIntegral.integral_of_le htp,
            (setIntegral_congr_set (Ico_ae_eq_Ioc (a := τ) (b := p))).symm,
            setIntegral_congr_fun measurableSet_Ico hEqOn]
          simp
        have : (∫ x in p..τ, ψ x) = 0 := by
          rw [intervalIntegral.integral_symm, hzint, neg_zero]
        simp [hχdef, this]
      · -- τ > q' > q ≥ p: `Icc p τ` engulfs all of `tsupport ψ`
        have hqτ : q ≤ τ := hq'gt.le.trans hgt.le
        have hpτ : p ≤ τ := hpleq.trans hqτ
        have hvanish : ∀ x, x ∉ Icc p τ → ψ x = 0 := by
          intro x hx
          apply image_eq_zero_of_notMem_tsupport
          intro hxs
          exact hx (Icc_subset_Icc_right hqτ (hpq hxs))
        have hzint : (∫ x in p..τ, ψ x) = 0 := by
          rw [intervalIntegral.integral_of_le hpτ,
            setIntegral_congr_set (Ioc_ae_eq_Icc (a := p) (b := τ)),
            setIntegral_eq_integral_of_forall_compl_eq_zero hvanish, hmean]
        simp [hχdef, hzint]
    have htsupp : tsupport χ ⊆ Icc p' q' :=
      tsupport_subset_of_eq_zero_of_notMem isClosed_Icc hzero
    refine ⟨χ, contDiff_infty_iff_deriv.mpr ⟨hdiff, by rw [hderiveq]; exact hψ.neg⟩,
      IsCompact.of_isClosed_subset (isCompact_Icc (a := p') (b := q')) (isClosed_tsupport χ)
        htsupp,
      htsupp.trans hIccI, hderiveq⟩

/-- The primitive of an interval-integrable `h` obeys the same test-function pairing against a
smooth `χ` vanishing at the two ends of `a..b` as `h` itself does against `χ`: this is the
"integration by parts against the primitive" step of the distributional fundamental theorem of
calculus. -/
theorem integral_primitive_mul_deriv_eq_integral_mul
    (f0 : ℝ) {a b τ₀ : ℝ} (hab : a ≤ b) (hτ₀ : τ₀ ∈ Icc a b) {h : ℝ → ℝ}
    (hh : IntervalIntegrable h volume a b)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχab : tsupport χ ⊆ Ioo a b) :
    ∫ τ in a..b, (f0 + ∫ s in τ₀..τ, h s) * (-(deriv χ τ)) = ∫ τ in a..b, χ τ * h τ := by
  set G : ℝ → ℝ := fun τ => ∫ s in τ₀..τ, h s with hGdef
  set F : ℝ → ℝ := fun τ => f0 + G τ with hFdef
  have huIcc : uIcc a b = Icc a b := uIcc_of_le hab
  have hτ₀' : τ₀ ∈ uIcc a b := by rwa [huIcc]
  have hGac : AbsolutelyContinuousOnInterval G a b :=
    hh.absolutelyContinuousOnInterval_intervalIntegral hτ₀'
  have hconstAC : AbsolutelyContinuousOnInterval (fun _ : ℝ => f0) a b := by
    have hLip : LipschitzOnWith 0 (fun _ : ℝ => f0) (uIcc a b) := fun x _ y _ => by simp
    exact hLip.absolutelyContinuousOnInterval
  have hFac : AbsolutelyContinuousOnInterval F a b := hconstAC.add hGac
  have hderivFG : deriv F = deriv G := deriv_const_add' f0
  have hχdiff : ∀ x, DifferentiableAt ℝ χ x := fun x => hχ.differentiable (by simp) x
  have hχderivc : Continuous (deriv χ) := hχ.continuous_deriv (by simp)
  obtain ⟨C, hC⟩ := IsCompact.exists_bound_of_continuousOn (isCompact_Icc (a := a) (b := b))
    hχderivc.continuousOn
  have hχLip : LipschitzOnWith C.toNNReal χ (uIcc a b) := by
    rw [huIcc]
    refine (convex_Icc a b).lipschitzOnWith_of_nnnorm_deriv_le (fun x _ => hχdiff x) ?_
    intro x hx
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal']
    exact le_trans (hC x hx) (le_max_left _ _)
  have hχac : AbsolutelyContinuousOnInterval χ a b := hχLip.absolutelyContinuousOnInterval
  have hIBP := AbsolutelyContinuousOnInterval.integral_mul_deriv_eq_deriv_mul hχac hFac
  have hχa : χ a = 0 := image_eq_zero_of_notMem_tsupport (fun hcon => lt_irrefl a (hχab hcon).1)
  have hχb : χ b = 0 := image_eq_zero_of_notMem_tsupport (fun hcon => lt_irrefl b (hχab hcon).2)
  rw [hχa, hχb, zero_mul, zero_mul, sub_zero, zero_sub] at hIBP
  have hderivGh : ∀ᵐ x, x ∈ uIcc a b → deriv G x = h x := by
    filter_upwards [hh.ae_hasDerivAt_integral] with x hx
    intro hxmem
    exact (hx hxmem τ₀ hτ₀').deriv
  have hcongr : ∫ x in a..b, χ x * deriv F x = ∫ x in a..b, χ x * h x := by
    apply intervalIntegral.integral_congr_ae
    rw [hderivFG]
    filter_upwards [hderivGh] with x hx hxmem
    rw [hx (Set.uIoc_subset_uIcc hxmem)]
  rw [hcongr] at hIBP
  calc ∫ τ in a..b, F τ * (-(deriv χ τ))
      = ∫ τ in a..b, -(deriv χ τ * F τ) := by
        apply intervalIntegral.integral_congr; intro x _; ring
    _ = -∫ τ in a..b, deriv χ τ * F τ := intervalIntegral.integral_neg
    _ = ∫ τ in a..b, χ τ * h τ := hIBP.symm

/-- A function vanishing off a set integrates the same way over that set (as an interval
integral) as it does over the whole line, once the set is `Icc a b`. -/
theorem intervalIntegral_eq_integral_of_forall_compl_eq_zero {a b : ℝ} (hab : a ≤ b)
    {g : ℝ → ℝ} (hg : ∀ x ∉ Icc a b, g x = 0) : ∫ τ in a..b, g τ = ∫ τ, g τ := by
  rw [intervalIntegral.integral_of_le hab, setIntegral_congr_set (Ioc_ae_eq_Icc (a := a) (b := b)),
    setIntegral_eq_integral_of_forall_compl_eq_zero hg]

/-- The full-line form of `integral_primitive_mul_deriv_eq_integral_mul`: for `h` locally
integrable on an open, order connected `I` and `χ` a smooth compactly supported test function
with support in `I`, the primitive of `h` based at `τ₀ ∈ I` pairs with `-χ'` exactly as `h`
pairs with `χ`. -/
theorem integral_primitive_mul_deriv_eq_integral_mul_of_isOpen
    (f0 : ℝ) {I : Set ℝ} (hI : IsOpen I) (hIoc : I.OrdConnected) {τ₀ : ℝ} (hτ₀ : τ₀ ∈ I)
    {h : ℝ → ℝ} (hh : LocallyIntegrableOn h I volume)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχc : HasCompactSupport χ) (hχI : tsupport χ ⊆ I) :
    ∫ τ, (f0 + ∫ s in τ₀..τ, h s) * (-(deriv χ τ)) = ∫ τ, χ τ * h τ := by
  rcases (tsupport χ).eq_empty_or_nonempty with hempty | hne
  · have hχ0 : χ = 0 :=
      Function.support_eq_empty_iff.mp (subset_empty_iff.mp (hempty ▸ subset_tsupport χ))
    simp [hχ0]
  · obtain ⟨p, hp, q, hq, hpq⟩ := exists_Icc_subset_of_isCompact hχc hne
    set a₀ := min p τ₀ with ha₀def
    set b₀ := max q τ₀ with hb₀def
    have hpI : p ∈ I := hχI hp
    have hqI : q ∈ I := hχI hq
    have ha₀I : a₀ ∈ I := by
      rcases le_total p τ₀ with hle | hle
      · rw [ha₀def, min_eq_left hle]; exact hpI
      · rw [ha₀def, min_eq_right hle]; exact hτ₀
    have hb₀I : b₀ ∈ I := by
      rcases le_total q τ₀ with hle | hle
      · rw [hb₀def, max_eq_right hle]; exact hτ₀
      · rw [hb₀def, max_eq_left hle]; exact hqI
    obtain ⟨a, halt, haI⟩ := exists_lt_mem_of_isOpen hI ha₀I
    obtain ⟨b, hbgt, hbI⟩ := exists_gt_mem_of_isOpen hI hb₀I
    have habI : Icc a b ⊆ I := hIoc.out haI hbI
    have ha₀b₀ : a₀ ≤ b₀ := le_trans (min_le_right p τ₀) (le_max_right q τ₀)
    have hab : a ≤ b := ((halt.trans_le ha₀b₀).trans hbgt).le
    have hχab : tsupport χ ⊆ Ioo a b := by
      intro x hx
      have hpqx := hpq hx
      exact ⟨lt_of_lt_of_le halt (le_trans (min_le_left p τ₀) hpqx.1),
        lt_of_le_of_lt (le_trans hpqx.2 (le_max_left q τ₀)) hbgt⟩
    have hτ₀ab : τ₀ ∈ Icc a b :=
      ⟨(halt.trans_le (min_le_right p τ₀)).le, ((le_max_right q τ₀).trans_lt hbgt).le⟩
    have hhIcc : IntegrableOn h (Icc a b) volume := hh.integrableOn_compact_subset habI
      isCompact_Icc
    have hhInterval : IntervalIntegrable h volume a b :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr hhIcc
    have hstep := integral_primitive_mul_deriv_eq_integral_mul f0 hab hτ₀ab hhInterval hχ hχab
    have hderivvanish : ∀ x ∉ Icc a b, deriv χ x = 0 := fun x hx =>
      deriv_of_notMem_tsupport (fun hxs => hx (Ioo_subset_Icc_self (hχab hxs)))
    have hχvanish : ∀ x ∉ Icc a b, χ x = 0 := fun x hx =>
      image_eq_zero_of_notMem_tsupport (fun hxs => hx (Ioo_subset_Icc_self (hχab hxs)))
    rw [intervalIntegral_eq_integral_of_forall_compl_eq_zero hab
        (fun x hx => by rw [hderivvanish x hx]; ring),
      intervalIntegral_eq_integral_of_forall_compl_eq_zero hab
        (fun x hx => by rw [hχvanish x hx]; ring)] at hstep
    exact hstep

/-- Two points of an open, order connected set lie strictly inside a closed interval still
contained in the set. -/
theorem exists_Icc_subset_isOpen_of_mem_mem {I : Set ℝ} (hI : IsOpen I) (hIoc : I.OrdConnected)
    {x y : ℝ} (hx : x ∈ I) (hy : y ∈ I) :
    ∃ a b, a < x ∧ a < y ∧ x < b ∧ y < b ∧ Icc a b ⊆ I := by
  have ha₀I : min x y ∈ I := by
    rcases le_total x y with hle | hle
    · rwa [min_eq_left hle]
    · rwa [min_eq_right hle]
  have hb₀I : max x y ∈ I := by
    rcases le_total x y with hle | hle
    · rwa [max_eq_right hle]
    · rwa [max_eq_left hle]
  obtain ⟨a, halt, haI⟩ := exists_lt_mem_of_isOpen hI ha₀I
  obtain ⟨b, hbgt, hbI⟩ := exists_gt_mem_of_isOpen hI hb₀I
  exact ⟨a, b, lt_of_lt_of_le halt (min_le_left x y), lt_of_lt_of_le halt (min_le_right x y),
    lt_of_le_of_lt (le_max_left x y) hbgt, lt_of_le_of_lt (le_max_right x y) hbgt,
    hIoc.out haI hbI⟩

/-- The primitive `τ ↦ ∫ s in τ₀..τ, h s` of a function locally integrable on an open, order
connected `I` is continuous on `I`. -/
theorem continuousOn_primitive_of_isOpen {I : Set ℝ} (hI : IsOpen I) (hIoc : I.OrdConnected)
    {τ₀ : ℝ} (hτ₀ : τ₀ ∈ I) {h : ℝ → ℝ} (hh : LocallyIntegrableOn h I volume) :
    ContinuousOn (fun τ => ∫ s in τ₀..τ, h s) I := by
  intro τ hτ
  obtain ⟨a, b, halt, halt', hgt, hgt', habI⟩ :=
    exists_Icc_subset_isOpen_of_mem_mem hI hIoc hτ₀ hτ
  have hab : a ≤ b := (halt.trans hgt).le
  have hτ₀ab : τ₀ ∈ Icc a b := ⟨halt.le, hgt.le⟩
  have hτab : τ ∈ Ioo a b := ⟨halt', hgt'⟩
  have hτIccab : τ ∈ Icc a b := Ioo_subset_Icc_self hτab
  have hhIcc : IntegrableOn h (Icc a b) volume := hh.integrableOn_compact_subset habI isCompact_Icc
  have hhInterval : IntervalIntegrable h volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr hhIcc
  have hcont := intervalIntegral.continuousOn_primitive_interval' hhInterval
    (by rw [uIcc_of_le hab]; exact hτ₀ab)
  rw [uIcc_of_le hab] at hcont
  have hnbhd : Icc a b ∈ 𝓝 τ :=
    mem_nhds_iff.mpr ⟨Ioo a b, Ioo_subset_Icc_self, isOpen_Ioo, hτab⟩
  exact ((hcont τ hτIccab).continuousAt hnbhd).continuousWithinAt

/-- The product of a function continuous on an open `I` with a globally continuous function whose
support lies in `I` is continuous, once extended by zero. -/
theorem continuous_mul_of_continuousOn_hasCompactSupport {I : Set ℝ} (hI : IsOpen I)
    {k ψ : ℝ → ℝ} (hk : ContinuousOn k I) (hψ : Continuous ψ) (hψI : tsupport ψ ⊆ I) :
    Continuous (fun x => k x * ψ x) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x ∈ tsupport ψ
  · have hxI : x ∈ I := hψI hx
    have hkAt : ContinuousAt k x := (hk x hxI).continuousAt (hI.mem_nhds hxI)
    exact hkAt.mul hψ.continuousAt
  · have hopen : IsOpen (tsupport ψ)ᶜ := (isClosed_tsupport ψ).isOpen_compl
    have hzero : (fun y => k y * ψ y) =ᶠ[nhds x] (fun _ => (0 : ℝ)) := by
      filter_upwards [hopen.mem_nhds hx] with y hy
      rw [image_eq_zero_of_notMem_tsupport hy, mul_zero]
    exact hzero.continuousAt

/-- The product of a function continuous on an open `I` with a smooth compactly supported
function whose support lies in `I` is integrable. -/
theorem integrable_mul_of_continuousOn_hasCompactSupport {I : Set ℝ} (hI : IsOpen I)
    {k ψ : ℝ → ℝ} (hk : ContinuousOn k I) (hψ : Continuous ψ) (hψcs : HasCompactSupport ψ)
    (hψI : tsupport ψ ⊆ I) : Integrable (fun x => k x * ψ x) volume := by
  have hcont : Continuous (fun x => k x * ψ x) :=
    continuous_mul_of_continuousOn_hasCompactSupport hI hk hψ hψI
  have hcs : HasCompactSupport (fun x => k x * ψ x) :=
    HasCompactSupport.intro hψcs (fun x hx => by
      rw [image_eq_zero_of_notMem_tsupport hx, mul_zero])
  exact hcont.integrable_of_hasCompactSupport hcs

/-- A function vanishing off the topological support of another has that support inside it,
once the ambient set is closed. -/
theorem tsupport_sub_subset (f g : ℝ → ℝ) : tsupport (f - g) ⊆ tsupport f ∪ tsupport g := by
  apply tsupport_subset_of_eq_zero_of_notMem ((isClosed_tsupport f).union (isClosed_tsupport g))
  intro x hx
  simp only [Set.mem_union, not_or] at hx
  rw [Pi.sub_apply, image_eq_zero_of_notMem_tsupport hx.1, image_eq_zero_of_notMem_tsupport hx.2,
    sub_zero]

/-- The distributional fundamental theorem of calculus: if `f` is continuous on an open, order
connected `I`, `h` is locally integrable on `I`, and `f` obeys the tested identity
`∫ f (-χ') = ∫ χ h` for every smooth compactly supported `χ` with support in `I` (the shape
`mollified_equation` delivers), then `f` is literally the primitive of `h` based at any
`τ₀ ∈ I`, throughout `I`. -/
theorem eq_add_intervalIntegral_of_pairing_eq
    {I : Set ℝ} (hI : IsOpen I) (hIoc : I.OrdConnected) {f h : ℝ → ℝ}
    (hfc : ContinuousOn f I) (hh : LocallyIntegrableOn h I volume)
    (hDist : ∀ χ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ → HasCompactSupport χ → tsupport χ ⊆ I →
      ∫ τ, f τ * (-(deriv χ τ)) = ∫ τ, χ τ * h τ)
    {τ₀ : ℝ} (hτ₀ : τ₀ ∈ I) {τ : ℝ} (hτ : τ ∈ I) :
    f τ = f τ₀ + ∫ s in τ₀..τ, h s := by
  set F : ℝ → ℝ := fun τ' => f τ₀ + ∫ s in τ₀..τ', h s with hFdef
  have hFcont : ContinuousOn F I :=
    continuousOn_const.add (continuousOn_primitive_of_isOpen hI hIoc hτ₀ hh)
  have hfFcont : ContinuousOn (f - F) I := hfc.sub hFcont
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
        MeasureTheory.integral_const_mul,
        hβint, mul_one, sub_self]
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
      integrable_mul_of_continuousOn_hasCompactSupport hI hfc hψcd.continuous hψcs hψI
    have hFψ_int : Integrable (fun τ' => F τ' * ψ τ') volume :=
      integrable_mul_of_continuousOn_hasCompactSupport hI hFcont hψcd.continuous hψcs hψI
    have hdiff : ∫ τ', (f τ' - F τ') * ψ τ' = 0 := by
      have heq : (fun τ' => (f τ' - F τ') * ψ τ') = (fun τ' => f τ' * ψ τ' - F τ' * ψ τ') := by
        funext τ'; ring
      rw [heq, MeasureTheory.integral_sub hfψ_int hFψ_int, hEq1, hEq2, sub_self]
    have hfFρ_int : Integrable (fun τ' => (f τ' - F τ') * ρ τ') volume :=
      integrable_mul_of_continuousOn_hasCompactSupport hI hfFcont hρ.continuous hρc hρI
    have hfFβ_int : Integrable (fun τ' => (f τ' - F τ') * β τ') volume :=
      integrable_mul_of_continuousOn_hasCompactSupport hI hfFcont hβcontdiff.continuous hβcs hβI
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
      integrable_mul_of_continuousOn_hasCompactSupport hI hfFcont hρ.continuous hρc hρI
    have hcρ_int : Integrable (fun τ' => c * ρ τ') volume :=
      (hρ.continuous.integrable_of_hasCompactSupport hρc).const_mul _
    have heq : (fun τ' => ((f τ' - F τ') - c) * ρ τ')
        = (fun τ' => (f τ' - F τ') * ρ τ' - c * ρ τ') := by funext τ'; ring
    rw [heq, MeasureTheory.integral_sub hfFρ_int hcρ_int, MeasureTheory.integral_const_mul, hbase]
    ring
  have hgcont : ContinuousOn (fun τ' => (f τ' - F τ') - c) I := hfFcont.sub continuousOn_const
  have hgloc : LocallyIntegrableOn (fun τ' => (f τ' - F τ') - c) I volume :=
    hgcont.locallyIntegrableOn hI.measurableSet
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
  have heqon : Set.EqOn (fun τ' => (f τ' - F τ') - c) 0 I :=
    MeasureTheory.Measure.eqOn_open_of_ae_eq hgae' hI hgcont continuousOn_const
  have hFτ₀ : F τ₀ = f τ₀ := by rw [hFdef]; simp
  have hc0 : c = 0 := by
    have hzero := heqon hτ₀
    simp only [Pi.zero_apply] at hzero
    linarith only [hzero, hFτ₀]
  have hfinal := heqon hτ
  simp only [Pi.zero_apply, hc0, sub_zero] at hfinal
  have hfF : f τ = F τ := by linarith only [hfinal]
  rw [hfF, hFdef]

end CIV
