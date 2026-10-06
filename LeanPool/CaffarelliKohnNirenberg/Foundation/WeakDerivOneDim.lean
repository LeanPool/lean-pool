/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# One-dimensional weak derivatives

These results identify locally integrable functions from their distributional
time derivatives on an open interval.
-/

public section

open MeasureTheory Set Function Filter
open scoped Topology

noncomputable section

namespace CKN

/-- A compact smooth test supported in an open interval. -/
@[expose]
def IsIntervalTest (U : Set ℝ) (φ : ℝ → ℝ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ U

/-- The distributional derivative of f on U is represented by g. -/
@[expose]
def HasWeakDerivOn (U : Set ℝ) (f g : ℝ → ℝ) : Prop :=
  ∀ φ : ℝ → ℝ, IsIntervalTest U φ →
    (∫ x in U, f x * deriv φ x) = -(∫ x in U, g x * φ x)

private theorem contDiff_intervalPrimitive {ψ : ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (a : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => ∫ t in a..x, ψ t) := by
  rw [contDiff_infty_iff_deriv]
  refine ⟨intervalIntegral.differentiable_integral_of_continuous hψ.continuous, ?_⟩
  have hderiv : deriv (fun x => ∫ t in a..x, ψ t) = ψ := by
    funext x
    exact Continuous.deriv_integral ψ hψ.continuous a x
  rw [hderiv]
  exact hψ

private theorem zeroMeanPrimitive_isIntervalTest {a b : ℝ} (hab : a < b)
    {ψ : ℝ → ℝ} (hψ : IsIntervalTest (Ioo a b) ψ)
    (hmean : ∫ x, ψ x = 0) :
    IsIntervalTest (Ioo a b) (fun x => ∫ t in a..x, ψ t) ∧
      (∀ x, deriv (fun y => ∫ t in a..y, ψ t) x = ψ x) := by
  rcases hψ with ⟨hψsmooth, hψcompact, hψsupp⟩
  obtain ⟨q, haq, hqb⟩ := exists_between hab
  let K := tsupport ψ ∪ {q}
  have hKcompact : IsCompact K := hψcompact.isCompact.union isCompact_singleton
  have hKne : K.Nonempty := ⟨q, Or.inr rfl⟩
  have hKsub : K ⊆ Ioo a b := by
    intro x hx
    rcases hx with hx | hx
    · exact hψsupp hx
    · simp only [mem_singleton_iff] at hx
      subst x
      exact ⟨haq, hqb⟩
  obtain ⟨m, hmK, hmmin⟩ := hKcompact.exists_isMinOn hKne continuousOn_id
  obtain ⟨n, hnK, hnmax⟩ := hKcompact.exists_isMaxOn hKne continuousOn_id
  have ham : a < m := (hKsub hmK).1
  have hnb : n < b := (hKsub hnK).2
  have hsupport : Function.support ψ ⊆ Ioc a b := by
    intro x hx
    have hxK : x ∈ K := Or.inl (subset_tsupport ψ hx)
    have hmx : m ≤ x := hmmin hxK
    have hxn : x ≤ n := hnmax hxK
    exact ⟨lt_of_lt_of_le ham hmx, le_of_lt (lt_of_le_of_lt hxn hnb)⟩
  have hψint : Integrable ψ volume :=
    hψsmooth.continuous.integrable_of_hasCompactSupport hψcompact
  have habint : ∫ t in a..b, ψ t = 0 := by
    rw [intervalIntegral.integral_eq_integral_of_support_subset hsupport]
    exact hmean
  let P : ℝ → ℝ := fun x => ∫ t in a..x, ψ t
  have hPleft (x : ℝ) (hx : x ≤ m) : P x = 0 := by
    dsimp [P]
    have hne : ∀ᵐ s ∂volume, s ≠ m := by
      simp [ae_iff, measure_singleton]
    have hzero : ∀ᵐ s ∂volume, s ∈ uIoc a x → ψ s = 0 := by
      filter_upwards [hne] with s hsm hs
      have hsle : s ≤ m := by
        simp only [uIoc, mem_Ioc] at hs
        exact hs.2.trans (max_le (le_of_lt ham) hx)
      have hslt : s < m := lt_of_le_of_ne hsle hsm
      have hsnot : s ∉ tsupport ψ := by
        intro hss
        have hmle : m ≤ s := hmmin (Or.inl hss)
        exact (not_lt_of_ge hmle) hslt
      by_contra hneψ
      have hsupp : s ∈ Function.support ψ := Function.mem_support.mpr hneψ
      exact hsnot (subset_tsupport ψ hsupp)
    rw [intervalIntegral.integral_congr_ae hzero]
    simp
  have htail (x : ℝ) (hx : n ≤ x) : ∫ t in n..x, ψ t = 0 := by
    have hzero : ∀ᵐ s ∂volume, s ∈ uIoc n x → ψ s = 0 := by
      filter_upwards with s hs
      have hsn : n < s := by
        have hs' : s ∈ Ioc n x := by simpa [uIoc, hx] using hs
        exact hs'.1
      have hsnot : s ∉ tsupport ψ := by
        intro hss
        have hle : s ≤ n := hnmax (Or.inl hss)
        exact (not_lt_of_ge hle) hsn
      by_contra hneψ
      have hsupp : s ∈ Function.support ψ := Function.mem_support.mpr hneψ
      exact hsnot (subset_tsupport ψ hsupp)
    rw [intervalIntegral.integral_congr_ae hzero]
    simp
  have hPan : ∫ t in a..n, ψ t = 0 := by
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (hψsmooth.continuous.intervalIntegrable (μ := volume) a n)
      (hψsmooth.continuous.intervalIntegrable (μ := volume) n b)
    rw [htail b (le_of_lt hnb), add_zero] at hsplit
    calc
      ∫ t in a..n, ψ t = ∫ t in a..b, ψ t := hsplit
      _ = 0 := habint
  have hPright (x : ℝ) (hx : n ≤ x) : P x = 0 := by
    dsimp [P]
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (hψsmooth.continuous.intervalIntegrable (μ := volume) a n)
      (hψsmooth.continuous.intervalIntegrable (μ := volume) n x)
    rw [htail x hx, add_zero] at hsplit
    rw [← hsplit, hPan]
  have hPzero : ∀ x ∉ Icc m n, P x = 0 := by
    intro x hx
    rcases not_and_or.mp hx with hxm | hxn
    · exact hPleft x (le_of_lt (not_le.mp hxm))
    · exact hPright x (le_of_lt (not_le.mp hxn))
  have hPcompact : HasCompactSupport P :=
    HasCompactSupport.intro isCompact_Icc hPzero
  have hPsupport : tsupport P ⊆ Icc m n := by
    apply closure_minimal
    · intro x hx
      have hp : P x ≠ 0 := Function.mem_support.mp hx
      by_contra hx'
      exact hp (hPzero x hx')
    · exact isClosed_Icc
  have hPsupportU : tsupport P ⊆ Ioo a b := by
    intro x hx
    have hxmn := hPsupport hx
    exact ⟨lt_of_lt_of_le ham hxmn.1, lt_of_le_of_lt hxmn.2 hnb⟩
  have hPdiff : ContDiff ℝ (⊤ : ℕ∞) P := contDiff_intervalPrimitive hψsmooth a
  have hPderiv : ∀ x, deriv P x = ψ x := by
    intro x
    exact Continuous.deriv_integral ψ hψsmooth.continuous a x
  refine ⟨?_, ?_⟩
  · change IsIntervalTest (Ioo a b) P
    exact ⟨hPdiff, hPcompact, hPsupportU⟩
  · intro x
    exact hPderiv x

private theorem eq_zero_of_not_mem_tsupport {f : ℝ → ℝ} {x : ℝ}
    (hx : x ∉ tsupport f) : f x = 0 := by
  by_contra hne
  exact hx (subset_tsupport f (Function.mem_support.mpr hne))

private theorem integrableOn_mul_intervalTest {U : Set ℝ} {f : ℝ → ℝ}
    (hf : LocallyIntegrableOn f U volume) {φ : ℝ → ℝ}
    (hφ : IsIntervalTest U φ) : IntegrableOn (fun x => φ x * f x) U volume := by
  rcases hφ with ⟨hφsmooth, hφcompact, hφsupport⟩
  let K := tsupport φ
  have hKcompact : IsCompact K := hφcompact.isCompact
  have hfK : IntegrableOn f K volume := hf.integrableOn_compact_subset hφsupport hKcompact
  have hprodK : IntegrableOn (fun x => φ x * f x) K volume := by
    simpa only [smul_eq_mul, mul_comm] using
      hfK.smul_continuousOn hφsmooth.continuous.continuousOn hKcompact
  have hprodSupport : Function.support (fun x => φ x * f x) ⊆ K := by
    intro x hx
    have hφne : φ x ≠ 0 := by
      intro hφzero
      apply hx
      simp [hφzero]
    exact subset_tsupport φ (Function.mem_support.mpr hφne)
  exact ((integrableOn_iff_integrable_of_support_subset hprodSupport).mp hprodK).integrableOn

private theorem setIntegral_eq_full_of_test {U : Set ℝ} {f : ℝ → ℝ}
    {φ : ℝ → ℝ} (hφ : IsIntervalTest U φ) :
    (∫ x in U, φ x * f x) = ∫ x, φ x * f x := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  have hφzero : φ x = 0 := eq_zero_of_not_mem_tsupport (fun hs => hx (hφ.2.2 hs))
  simp [hφzero]

/-- A locally integrable function with zero distributional derivative
is constant almost everywhere. -/
theorem exists_ae_eq_const_of_weakDeriv_zero {a b : ℝ} (hab : a < b)
    {F : ℝ → ℝ} (hF : LocallyIntegrableOn F (Ioo a b) volume)
    (hweak : HasWeakDerivOn (Ioo a b) F (fun _ => 0)) :
    ∃ C : ℝ, ∀ᵐ x ∂volume, x ∈ Ioo a b → F x = C := by
  obtain ⟨q, haq, hqb⟩ := exists_between hab
  obtain ⟨ρ, hρsupp, hρcompact, hρsmooth, hρrange, hρq⟩ :=
    exists_contDiff_tsupport_subset (n := ⊤) (isOpen_Ioo.mem_nhds ⟨haq, hqb⟩)
  have hρnonneg : ∀ x, 0 ≤ ρ x := fun x => (hρrange ⟨x, rfl⟩).1
  have hρpos : 0 < ∫ x, ρ x := by
    apply hρsmooth.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
      hρcompact hρnonneg
    rw [hρq]
    exact one_ne_zero
  have hρint : Integrable ρ volume :=
    hρsmooth.continuous.integrable_of_hasCompactSupport hρcompact
  let C : ℝ := (∫ x, ρ x * F x) / (∫ x, ρ x)
  have htestIdentity :
      ∀ φ : ℝ → ℝ, IsIntervalTest (Ioo a b) φ →
        (∫ x, φ x * F x) = C * (∫ x, φ x) := by
    intro φ hφ
    rcases hφ with ⟨hφsmooth, hφcompact, hφsupp⟩
    have hφint : Integrable φ volume :=
      hφsmooth.continuous.integrable_of_hasCompactSupport hφcompact
    let k : ℝ := (∫ x, φ x) / (∫ x, ρ x)
    let ψ : ℝ → ℝ := fun x => φ x - k * ρ x
    have hscaledCompact : HasCompactSupport (fun x => k * ρ x) :=
      HasCompactSupport.intro hρcompact.isCompact fun x hx => by
        rw [eq_zero_of_not_mem_tsupport hx]
        simp
    have hscaledSupport : tsupport (fun x => k * ρ x) ⊆ Ioo a b := by
      have hscaledT : tsupport (fun x => k * ρ x) ⊆ tsupport ρ := by
        apply closure_minimal ?_ isClosed_closure
        intro x hx
        have hkρ : k * ρ x ≠ 0 := Function.mem_support.mp hx
        have hρ : ρ x ≠ 0 := by
          intro hzero
          apply hkρ
          simp [hzero]
        exact subset_tsupport ρ (Function.mem_support.mpr hρ)
      exact hscaledT.trans hρsupp
    have hψtest : IsIntervalTest (Ioo a b) ψ := by
      refine ⟨hφsmooth.sub (contDiff_const.mul hρsmooth), hφcompact.sub hscaledCompact, ?_⟩
      change tsupport (fun x => φ x - k * ρ x) ⊆ Ioo a b
      exact (tsupport_sub φ (fun x => k * ρ x)).trans (union_subset hφsupp hscaledSupport)
    have hscaledInt : Integrable (fun x => k * ρ x) volume := hρint.const_mul k
    have hmean : ∫ x, ψ x = 0 := by
      dsimp [ψ]
      rw [integral_sub hφint hscaledInt, integral_const_mul]
      dsimp [k]
      field_simp [ne_of_gt hρpos]
      ring
    have hprim := zeroMeanPrimitive_isIntervalTest hab hψtest hmean
    rcases hprim with ⟨hPtest, hPderiv⟩
    let P : ℝ → ℝ := fun x => ∫ t in a..x, ψ t
    have hweakP := hweak P hPtest
    have hPzero : ∫ x in Ioo a b, F x * ψ x = 0 := by
      have hweakP' : ∫ x in Ioo a b, F x * deriv P x = 0 := by
        simpa [HasWeakDerivOn] using hweakP
      calc
        ∫ x in Ioo a b, F x * ψ x = ∫ x in Ioo a b, F x * deriv P x := by
          apply integral_congr_ae
          filter_upwards with x
          rw [hPderiv x]
        _ = 0 := hweakP'
    have hPfull : ∫ x, ψ x * F x = 0 := by
      have hset := setIntegral_eq_full_of_test hψtest (f := F)
      rw [← hset]
      simpa [mul_comm] using hPzero
    have hφFintOn := integrableOn_mul_intervalTest hF
      ⟨hφsmooth, hφcompact, hφsupp⟩
    have hρFintOn := integrableOn_mul_intervalTest hF
      ⟨hρsmooth, hρcompact, hρsupp⟩
    have hψFintOn := integrableOn_mul_intervalTest hF hψtest
    have hsetLinear : (∫ x in Ioo a b, φ x * F x) -
        k * (∫ x in Ioo a b, ρ x * F x) = 0 := by
      have hsplit : (∫ x in Ioo a b, φ x * F x) -
          (∫ x in Ioo a b, k * (ρ x * F x)) =
            ∫ x in Ioo a b, ψ x * F x := by
        calc
          (∫ x in Ioo a b, φ x * F x) -
              (∫ x in Ioo a b, k * (ρ x * F x)) =
                ∫ x in Ioo a b, (φ x * F x - k * (ρ x * F x)) :=
            (integral_sub hφFintOn (hρFintOn.const_mul k)).symm
          _ = ∫ x in Ioo a b, ψ x * F x := by
            apply integral_congr_ae
            filter_upwards with x
            dsimp [ψ]
            ring
      rw [integral_const_mul] at hsplit
      have hPset : ∫ x in Ioo a b, ψ x * F x = 0 := by
        calc
          ∫ x in Ioo a b, ψ x * F x = ∫ x in Ioo a b, F x * ψ x := by
            apply integral_congr_ae
            filter_upwards with x
            ring
          _ = 0 := hPzero
      rw [hPset] at hsplit
      exact hsplit
    have hφset := setIntegral_eq_full_of_test ⟨hφsmooth, hφcompact, hφsupp⟩ (f := F)
    have hρset := setIntegral_eq_full_of_test
      ⟨hρsmooth, hρcompact, hρsupp⟩ (f := F)
    have hfullLinear : (∫ x, φ x * F x) -
        k * (∫ x, ρ x * F x) = 0 := by
      simpa [hφset, hρset] using hsetLinear
    have hfullEq : (∫ x, φ x * F x) = k * (∫ x, ρ x * F x) :=
      sub_eq_zero.mp hfullLinear
    dsimp [C]
    rw [hfullEq]
    dsimp [k]
    field_simp [ne_of_gt hρpos]
  have hFminus : ∀ φ : ℝ → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b →
      (∫ x, φ x • (F x - C)) = 0 := by
    intro φ hφsmooth hφcompact hφsupp
    have htest : IsIntervalTest (Ioo a b) φ := ⟨hφsmooth, hφcompact, hφsupp⟩
    have hφint : Integrable φ volume :=
      hφsmooth.continuous.integrable_of_hasCompactSupport hφcompact
    have hφFintOn := integrableOn_mul_intervalTest hF htest
    have hφFsupport : Function.support (fun x => φ x * F x) ⊆ Ioo a b := by
      intro x hx
      have hφne : φ x ≠ 0 := by
        intro hzero
        apply hx
        simp [hzero]
      exact hφsupp (subset_tsupport φ (Function.mem_support.mpr hφne))
    have hφFint : Integrable (fun x => φ x * F x) volume :=
      (integrableOn_iff_integrable_of_support_subset hφFsupport).mp hφFintOn
    have hφCint : Integrable (fun x => φ x * C) volume := by
      simpa [mul_comm] using hφint.const_mul C
    have hidentity := htestIdentity φ htest
    rw [show (fun x => φ x • (F x - C)) =
        (fun x => φ x * F x - φ x * C) by
          funext x
          simp only [smul_eq_mul]
          ring,
      integral_sub hφFint hφCint, integral_mul_const] 
    rw [hidentity]
    ring
  have hzero := isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (hF.sub (locallyIntegrableOn_const C)) hFminus
  refine ⟨C, ?_⟩
  filter_upwards [hzero] with x hx
  intro hxU
  exact sub_eq_zero.mp (hx hxU)

private theorem intervalPrimitive_continuousOn {a b t₀ : ℝ}
    (ht₀ : t₀ ∈ Ioo a b) {g : ℝ → ℝ}
    (hg : LocallyIntegrableOn g (Ioo a b) volume) :
    ContinuousOn (fun x => ∫ s in t₀..x, g s) (Ioo a b) := by
  intro x hx
  obtain ⟨c, hac, hcl⟩ := exists_between (lt_min hx.1 ht₀.1)
  obtain ⟨d, hrd, hdb⟩ := exists_between (max_lt hx.2 ht₀.2)
  have hcd : c ≤ d := le_trans (le_of_lt (lt_of_lt_of_le hcl (min_le_left _ _)))
    (le_of_lt (lt_of_le_of_lt (le_max_left _ _) hrd))
  have hIccSub : Icc c d ⊆ Ioo a b := by
    intro y hy
    exact ⟨lt_of_lt_of_le hac hy.1, lt_of_le_of_lt hy.2 hdb⟩
  have hIccInt : IntegrableOn g (Icc c d) volume :=
    hg.integrableOn_compact_subset hIccSub isCompact_Icc
  have hgInt : IntervalIntegrable g volume c d := by
    apply intervalIntegrable_iff.mpr
    exact hIccInt.mono_set (uIoc_subset_uIcc.trans (by simp [uIcc_of_le hcd]))
  have ht₀cc : t₀ ∈ uIcc c d := by
    rw [uIcc_of_le hcd]
    exact ⟨le_of_lt (lt_of_lt_of_le hcl (min_le_right _ _)),
      le_of_lt (lt_of_le_of_lt (le_max_right _ _) hrd)⟩
  have hGac := hgInt.absolutelyContinuousOnInterval_intervalIntegral ht₀cc
  have hxc : c < x := lt_of_lt_of_le hcl (min_le_left _ _)
  have hxd : x < d := lt_of_le_of_lt (le_max_left _ _) hrd
  have hGcont : ContinuousOn (fun y => ∫ s in t₀..y, g s) (Icc c d) := by
    simpa [uIcc_of_le hcd] using hGac.continuousOn
  exact (hGcont.continuousAt (Icc_mem_nhds hxc hxd)).continuousWithinAt

private theorem intervalPrimitive_hasWeakDerivOn {a b t₀ : ℝ} (hab : a < b)
    (ht₀ : t₀ ∈ Ioo a b) {g : ℝ → ℝ}
    (hg : LocallyIntegrableOn g (Ioo a b) volume) :
    HasWeakDerivOn (Ioo a b) (fun x => ∫ s in t₀..x, g s) g := by
  let G : ℝ → ℝ := fun x => ∫ s in t₀..x, g s
  have hGcont : ContinuousOn G (Ioo a b) := intervalPrimitive_continuousOn ht₀ hg
  have hGlocal : LocallyIntegrableOn G (Ioo a b) volume :=
    hGcont.locallyIntegrableOn isOpen_Ioo.measurableSet
  intro φ hφ
  rcases hφ with ⟨hφsmooth, hφcompact, hφsupp⟩
  obtain ⟨q, haq, hqb⟩ := exists_between hab
  let K := tsupport φ ∪ {q} ∪ {t₀}
  have hKcompact : IsCompact K :=
    (hφcompact.isCompact.union isCompact_singleton).union isCompact_singleton
  have hKne : K.Nonempty := ⟨q, Or.inl (Or.inr rfl)⟩
  have hKsub : K ⊆ Ioo a b := by
    intro x hx
    rcases hx with hx | hx
    · rcases hx with hx | hx
      · exact hφsupp hx
      · simp only [mem_singleton_iff] at hx
        subst x
        exact ⟨haq, hqb⟩
    · simp only [mem_singleton_iff] at hx
      subst x
      exact ht₀
  obtain ⟨m, hmK, hmmin⟩ := hKcompact.exists_isMinOn hKne continuousOn_id
  obtain ⟨n, hnK, hnmax⟩ := hKcompact.exists_isMaxOn hKne continuousOn_id
  have ham : a < m := (hKsub hmK).1
  have hnb : n < b := (hKsub hnK).2
  obtain ⟨c, hac, hcm⟩ := exists_between ham
  obtain ⟨d, hnd, hdb⟩ := exists_between hnb
  have hmn : m ≤ n := hmmin hnK
  have hcd : c ≤ d := le_of_lt (lt_trans hcm (lt_of_le_of_lt hmn hnd))
  have hIccSub : Icc c d ⊆ Ioo a b := by
    intro x hx
    exact ⟨lt_of_lt_of_le hac hx.1, lt_of_le_of_lt hx.2 hdb⟩
  have hgIcc : IntegrableOn g (Icc c d) volume :=
    hg.integrableOn_compact_subset hIccSub isCompact_Icc
  have hgInt : IntervalIntegrable g volume c d := by
    apply intervalIntegrable_iff.mpr
    exact hgIcc.mono_set (uIoc_subset_uIcc.trans (by simp [uIcc_of_le hcd]))
  have ht₀cc : t₀ ∈ uIcc c d := by
    rw [uIcc_of_le hcd]
    exact ⟨le_of_lt (lt_of_lt_of_le hcm (hmmin (Or.inr rfl))),
      le_of_lt (lt_of_le_of_lt (hnmax (Or.inr rfl)) hnd)⟩
  have hGac := hgInt.absolutelyContinuousOnInterval_intervalIntegral ht₀cc
  have hφac : AbsolutelyContinuousOnInterval φ c d := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    exact hφsmooth.contDiffOn.of_le (by simp)
  have hφc : φ c = 0 := by
    apply eq_zero_of_not_mem_tsupport
    intro hc
    exact (not_le_of_gt hcm) (hmmin (Or.inl (Or.inl hc)))
  have hφd : φ d = 0 := by
    apply eq_zero_of_not_mem_tsupport
    intro hd
    exact (not_le_of_gt hnd) (hnmax (Or.inl (Or.inl hd)))
  have hGderivAE : ∀ᵐ x ∂volume, x ∈ uIcc c d → deriv G x = g x := by
    filter_upwards [hgInt.ae_hasDerivAt_integral] with x hx hxcc
    have hder := hx hxcc t₀ ht₀cc
    simpa [G] using hder.deriv
  have hGderivInterval :
      ∫ x in c..d, deriv G x * φ x = ∫ x in c..d, g x * φ x := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hGderivAE] with x hx hxoc
    rw [hx (uIoc_subset_uIcc hxoc)]
  have hIbP := hGac.integral_mul_deriv_eq_deriv_mul hφac
  have hIbP' : ∫ x in c..d, G x * deriv φ x = -(∫ x in c..d, g x * φ x) := by
    rw [hφd, hφc, hGderivInterval] at hIbP
    simpa using hIbP
  have hderivTest : IsIntervalTest (Ioo a b) (deriv φ) := by
    exact ⟨(contDiff_infty_iff_deriv.mp hφsmooth).2, hφcompact.deriv,
      (tsupport_deriv_subset (f := φ)).trans hφsupp⟩
  have hGderivOn := integrableOn_mul_intervalTest hGlocal hderivTest
  have hgφOn := integrableOn_mul_intervalTest hg ⟨hφsmooth, hφcompact, hφsupp⟩
  have hGset := setIntegral_eq_full_of_test hderivTest (f := G)
  have hgφset := setIntegral_eq_full_of_test ⟨hφsmooth, hφcompact, hφsupp⟩ (f := g)
  have hGfull : (∫ x, G x * deriv φ x) = ∫ x in c..d, G x * deriv φ x := by
    symm
    apply intervalIntegral.integral_eq_integral_of_support_subset
    intro x hx
    have hderivNe : deriv φ x ≠ 0 := by
      intro hz
      apply hx
      simp [hz]
    have hxφ : x ∈ tsupport φ := (tsupport_deriv_subset (f := φ))
      (subset_tsupport (deriv φ) (Function.mem_support.mpr hderivNe))
    have hxK : x ∈ K := Or.inl (Or.inl hxφ)
    have hmx : m ≤ x := hmmin hxK
    have hxn : x ≤ n := hnmax hxK
    exact ⟨lt_of_lt_of_le hcm hmx, le_of_lt (lt_of_le_of_lt hxn hnd)⟩
  have hgφfull : (∫ x, g x * φ x) = ∫ x in c..d, g x * φ x := by
    symm
    apply intervalIntegral.integral_eq_integral_of_support_subset
    intro x hx
    have hφNe : φ x ≠ 0 := by
      intro hz
      apply hx
      simp [hz]
    have hxφ : x ∈ tsupport φ := subset_tsupport φ (Function.mem_support.mpr hφNe)
    have hxK : x ∈ K := Or.inl (Or.inl hxφ)
    have hmx : m ≤ x := hmmin hxK
    have hxn : x ≤ n := hnmax hxK
    exact ⟨lt_of_lt_of_le hcm hmx, le_of_lt (lt_of_le_of_lt hxn hnd)⟩
  calc
    ∫ x in Ioo a b, G x * deriv φ x = ∫ x, G x * deriv φ x := by
      simpa [mul_comm] using setIntegral_eq_full_of_test hderivTest (f := G)
    _ = ∫ x in c..d, G x * deriv φ x := hGfull
    _ = -(∫ x in c..d, g x * φ x) := hIbP'
    _ = -(∫ x, g x * φ x) := by rw [hgφfull]
    _ = -(∫ x in Ioo a b, g x * φ x) := by
      have hsetOrder : (∫ x in Ioo a b, g x * φ x) = ∫ x, g x * φ x := by
        calc
          (∫ x in Ioo a b, g x * φ x) = ∫ x in Ioo a b, φ x * g x := by
            apply integral_congr_ae
            filter_upwards with x
            ring
          _ = ∫ x, φ x * g x := hgφset
          _ = ∫ x, g x * φ x := by
            apply integral_congr_ae
            filter_upwards with x
            ring
      rw [← hsetOrder]

/-- A locally integrable weak derivative determines the function up to a constant. -/
theorem exists_ae_eq_const_add_intervalIntegral_of_weakDeriv {a b t₀ : ℝ} (hab : a < b)
    (ht₀ : t₀ ∈ Ioo a b) {f g : ℝ → ℝ}
    (hf : LocallyIntegrableOn f (Ioo a b) volume)
    (hg : LocallyIntegrableOn g (Ioo a b) volume)
    (hweak : HasWeakDerivOn (Ioo a b) f g) :
    ∃ C : ℝ, ∀ᵐ x ∂volume, x ∈ Ioo a b →
      f x = C + ∫ s in t₀..x, g s := by
  let G : ℝ → ℝ := fun x => ∫ s in t₀..x, g s
  have hGweak := intervalPrimitive_hasWeakDerivOn hab ht₀ hg
  have hGloc : LocallyIntegrableOn G (Ioo a b) volume :=
    (intervalPrimitive_continuousOn ht₀ hg).locallyIntegrableOn isOpen_Ioo.measurableSet
  have hHloc : LocallyIntegrableOn (fun x => f x - G x) (Ioo a b) volume := hf.sub hGloc
  have hHweak : HasWeakDerivOn (Ioo a b) (fun x => f x - G x) (fun _ => 0) := by
    intro φ hφ
    rcases hφ with ⟨hφsmooth, hφcompact, hφsupp⟩
    have hφderiv : IsIntervalTest (Ioo a b) (deriv φ) := by
      exact ⟨(contDiff_infty_iff_deriv.mp hφsmooth).2, hφcompact.deriv,
        (tsupport_deriv_subset (f := φ)).trans hφsupp⟩
    have hfderivOn := integrableOn_mul_intervalTest hf hφderiv
    have hGderivOn := integrableOn_mul_intervalTest hGloc hφderiv
    have hfderivOn' : IntegrableOn (fun x => f x * deriv φ x) (Ioo a b) volume := by
      simpa [mul_comm] using hfderivOn
    have hGderivOn' : IntegrableOn (fun x => G x * deriv φ x) (Ioo a b) volume := by
      simpa [mul_comm] using hGderivOn
    have hfw := hweak φ ⟨hφsmooth, hφcompact, hφsupp⟩
    have hGw := hGweak φ ⟨hφsmooth, hφcompact, hφsupp⟩
    have hGw' : (∫ x in Ioo a b, G x * deriv φ x) =
        -(∫ x in Ioo a b, g x * φ x) := by
      simpa [G] using hGw
    have hzero : (∫ x in Ioo a b, (f x - G x) * deriv φ x) = 0 := by
      calc
        (∫ x in Ioo a b, (f x - G x) * deriv φ x) =
            (∫ x in Ioo a b, f x * deriv φ x) -
              (∫ x in Ioo a b, G x * deriv φ x) := by
          calc
            (∫ x in Ioo a b, (f x - G x) * deriv φ x) =
                ∫ x in Ioo a b, (f x * deriv φ x - G x * deriv φ x) := by
              apply integral_congr_ae
              filter_upwards with x
              ring
            _ = (∫ x in Ioo a b, f x * deriv φ x) -
                (∫ x in Ioo a b, G x * deriv φ x) :=
              integral_sub hfderivOn' hGderivOn'
        _ = 0 := by rw [hfw, hGw']; ring
    simpa [HasWeakDerivOn] using hzero
  obtain ⟨C, hC⟩ := exists_ae_eq_const_of_weakDeriv_zero hab hHloc hHweak
  refine ⟨C, ?_⟩
  filter_upwards [hC] with x hx
  intro hxU
  have hEq : f x - G x = C := hx hxU
  change f x = C + G x
  linear_combination hEq

/-- Continuity upgrades the weak-derivative representation to every point. -/
theorem eq_const_add_intervalIntegral_of_continuous_weakDeriv {a b t₀ : ℝ} (hab : a < b)
    (ht₀ : t₀ ∈ Ioo a b) {f g : ℝ → ℝ}
    (hf : LocallyIntegrableOn f (Ioo a b) volume)
    (hg : LocallyIntegrableOn g (Ioo a b) volume)
    (hweak : HasWeakDerivOn (Ioo a b) f g)
    (hfcont : ContinuousOn f (Ioo a b)) :
    ∃ C : ℝ, ∀ x ∈ Ioo a b, f x = C + ∫ s in t₀..x, g s := by
  obtain ⟨C, hC⟩ := exists_ae_eq_const_add_intervalIntegral_of_weakDeriv hab ht₀ hf hg hweak
  let G : ℝ → ℝ := fun x => C + ∫ s in t₀..x, g s
  have hGcont : ContinuousOn G (Ioo a b) :=
    continuousOn_const.add (intervalPrimitive_continuousOn ht₀ hg)
  have hEq : (fun x => f x) =ᵐ[volume.restrict (Ioo a b)] G := by
    filter_upwards [ae_restrict_of_ae hC,
      ae_restrict_mem isOpen_Ioo.measurableSet] with x hx hxU
    exact hx hxU
  have hEqOn := MeasureTheory.Measure.eqOn_open_of_ae_eq hEq isOpen_Ioo hfcont hGcont
  refine ⟨C, ?_⟩
  intro x hx
  exact hEqOn hx

/-- The zero initial trace gives the one-dimensional small-time energy bound. -/
theorem abs_sq_le_time_integral_sq_of_continuous_weakDeriv {τ : ℝ} (hτ : 0 < τ)
    {f g : ℝ → ℝ} (hfcont : ContinuousOn f (Ico 0 τ)) (hfzero : f 0 = 0)
    (hgL2 : MemLp g 2 (volume.restrict (Ioo 0 τ)))
    (hweak : HasWeakDerivOn (Ioo 0 τ) f g) :
    ∀ t, 0 < t → t < τ → |f t| ^ 2 ≤ t * ∫ s in 0..t, |g s| ^ 2 := by
  let U := Ioo (0 : ℝ) τ
  let t₀ := τ / 2
  have ht₀pos : 0 < t₀ := by dsimp [t₀]; linarith only [hτ]
  have ht₀τ : t₀ < τ := by dsimp [t₀]; linarith only [hτ]
  have ht₀U : t₀ ∈ U := ⟨ht₀pos, ht₀τ⟩
  have hfLoc : LocallyIntegrableOn f U volume :=
    (hfcont.mono Ioo_subset_Ico_self).locallyIntegrableOn isOpen_Ioo.measurableSet
  have hgLoc : LocallyIntegrableOn g U volume :=
    locallyIntegrableOn_of_locallyIntegrable_restrict
      (hgL2.locallyIntegrable (by norm_num : (1 : ENNReal) ≤ (2 : ENNReal)))
  obtain ⟨C, hRep⟩ := eq_const_add_intervalIntegral_of_continuous_weakDeriv
    hτ ht₀U hfLoc hgLoc hweak (hfcont.mono Ioo_subset_Ico_self)
  let gExt := U.indicator g
  have hgExtLp : MemLp gExt 2 volume := by
    rw [memLp_indicator_iff_restrict isOpen_Ioo.measurableSet]
    exact hgL2
  have hgExtInt : Integrable gExt volume := by
    have hgIntU : IntegrableOn g U volume :=
      MeasureTheory.MemLp.integrable (by norm_num : (1 : ENNReal) ≤ (2 : ENNReal)) hgL2
    simpa [gExt, U] using hgIntU.integrable_indicator isOpen_Ioo.measurableSet
  let J : ℝ → ℝ := fun t => ∫ s in 0..t, gExt s
  have hgExtInterval : IntervalIntegrable gExt volume (-1) 1 := by
    apply intervalIntegrable_iff.mpr
    exact hgExtInt.integrableOn.mono_set (fun _ _ => trivial)
  have hJac := hgExtInterval.absolutelyContinuousOnInterval_intervalIntegral
    (c := 0) (by simp [uIcc])
  have hJcontOn : ContinuousOn J (Icc (-1) 1) := by
    simpa [J, uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hJac.continuousOn
  have hJcontAt : ContinuousAt J 0 :=
    hJcontOn.continuousAt (Icc_mem_nhds (by norm_num) (by norm_num))
  have hJzero : J 0 = 0 := by simp [J]
  have hgIntU : IntegrableOn g U volume := by
    exact MeasureTheory.MemLp.integrable (by norm_num : (1 : ENNReal) ≤ (2 : ENNReal)) hgL2
  have hIntT₀zero : IntervalIntegrable g volume t₀ 0 := by
    apply intervalIntegrable_iff.mpr
    apply hgIntU.mono_set
    intro s hs
    have hs' : s ∈ Ioc 0 t₀ := by simpa [uIoc, le_of_lt ht₀pos] using hs
    exact ⟨hs'.1, lt_of_le_of_lt hs'.2 ht₀τ⟩
  have hIntZeroT (t : ℝ) (ht : 0 < t) (htτ : t < τ) :
      IntervalIntegrable g volume 0 t := by
    apply intervalIntegrable_iff.mpr
    apply hgIntU.mono_set
    intro s hs
    have hs' : s ∈ Ioc 0 t := by simpa [uIoc, ht.le] using hs
    exact ⟨hs'.1, lt_of_le_of_lt hs'.2 htτ⟩
  have hJ_eq_g (t : ℝ) (ht : 0 < t) (htτ : t < τ) :
      (∫ s in 0..t, g s) = J t := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards with s hs
    have hs' : s ∈ Ioc 0 t := by simpa [uIoc, ht.le] using hs
    have hsU : s ∈ U := ⟨hs'.1, lt_of_le_of_lt hs'.2 htτ⟩
    simp [gExt, U, hsU]
  let C₀ := C + ∫ s in t₀..0, g s
  have hpoint (t : ℝ) (ht : 0 < t) (htτ : t < τ) : f t = C₀ + J t := by
    have hrt := hRep t ⟨ht, htτ⟩
    have hsplit := intervalIntegral.integral_add_adjacent_intervals hIntT₀zero
      (hIntZeroT t ht htτ)
    have hsplit' : (∫ s in t₀..t, g s) =
        (∫ s in t₀..0, g s) + (∫ s in 0..t, g s) := by
      simpa using hsplit.symm
    calc
      f t = C + ∫ s in t₀..t, g s := hrt
      _ = C + ((∫ s in t₀..0, g s) + (∫ s in 0..t, g s)) :=
        congrArg (fun z : ℝ => C + z) hsplit'
      _ = (C + (∫ s in t₀..0, g s)) + (∫ s in 0..t, g s) := by
        abel
      _ = C₀ + J t := by
        dsimp [C₀]
        rw [hJ_eq_g t ht htτ]
  let H := fun t => f t - J t
  let V := Ioi (0 : ℝ) ∩ Iio τ
  have hVeq : 𝓝[V] 0 = 𝓝[Ioi (0 : ℝ)] 0 := by
    exact nhdsWithin_inter_of_mem'
      (mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hτ))
  have hHcont : ContinuousWithinAt H (Ico 0 τ) 0 := by
    dsimp [H]
    exact (hfcont 0 ⟨le_rfl, hτ⟩).sub hJcontAt.continuousWithinAt
  have hfilterle : 𝓝[Ioi (0 : ℝ)] 0 ≤ 𝓝[Ico 0 τ] 0 := by
    rw [← hVeq]
    exact nhdsWithin_mono 0 (by
      intro t ht
      exact ⟨le_of_lt ht.1, ht.2⟩)
  have hHlimit := hHcont.tendsto.mono_left hfilterle
  have hHconst : ∀ᶠ t in 𝓝[Ioi (0 : ℝ)] 0, H t = C₀ := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hτ)] with t ht httau
    have hpt := hpoint t ht httau
    dsimp [H]
    linear_combination hpt
  have hHlimitConst := hHlimit.congr' hHconst
  have hH0 : H 0 = 0 := by simp [H, hJzero, hfzero]
  have hC₀ : C₀ = 0 := by
    have hlim := tendsto_nhds_unique hHlimitConst tendsto_const_nhds
    rw [hH0] at hlim
    exact hlim.symm
  intro t ht htτ
  have hrepr : f t = ∫ s in 0..t, g s := by
    have hrepr' := hpoint t ht htτ
    rw [hC₀, ← hJ_eq_g t ht htτ] at hrepr'
    simpa using hrepr'
  have hholder (t : ℝ) (ht : 0 < t) :
      (∫ s in 0..t, |gExt s|) ≤
        Real.sqrt (∫ s in 0..t, |gExt s| ^ 2) * Real.sqrt t := by
    let μ := volume.restrict (Ioc 0 t)
    have hgμ : MemLp gExt (ENNReal.ofReal (2 : ℝ)) μ := by
      simpa using hgExtLp.mono_measure Measure.restrict_le_self
    have h1 : MemLp (fun _ : ℝ => (1 : ℝ))
        (ENNReal.ofReal (2 : ℝ)) μ := by
      simpa using (memLp_const 1 :
        MemLp (fun _ : ℝ => (1 : ℝ)) 2 μ)
    have hcs := integral_mul_norm_le_Lp_mul_Lq
      (Real.holderConjugate_iff.mpr
        (show 1 < (2 : ℝ) ∧ (2 : ℝ)⁻¹ + (2 : ℝ)⁻¹ = 1 by norm_num)) hgμ h1
    simpa [μ, intervalIntegral.integral_of_le ht.le, Real.norm_eq_abs,
      Real.sqrt_eq_rpow, sq_abs, max_eq_left ht.le] using hcs
  have hholdert := hholder t ht
  have hnorm : |∫ s in 0..t, gExt s| ≤ ∫ s in 0..t, |gExt s| := by
    simpa [Real.norm_eq_abs] using
      (intervalIntegral.norm_integral_le_integral_norm (E := ℝ) (f := gExt) (μ := volume) ht.le)
  have hA : 0 ≤ ∫ s in 0..t, |gExt s| ^ 2 :=
    intervalIntegral.integral_nonneg ht.le (fun _ _ => sq_nonneg _)
  have hsqrtA : 0 ≤ Real.sqrt (∫ s in 0..t, |gExt s| ^ 2) :=
    Real.sqrt_nonneg _
  have hsqrtt : 0 ≤ Real.sqrt t := Real.sqrt_nonneg _
  have hroot : |∫ s in 0..t, gExt s| ^ 2 ≤
      (Real.sqrt (∫ s in 0..t, |gExt s| ^ 2) * Real.sqrt t) ^ 2 :=
    (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hsqrtA hsqrtt)).2
      (le_trans hnorm hholdert)
  have hExtBound : |∫ s in 0..t, gExt s| ^ 2 ≤
      t * ∫ s in 0..t, |gExt s| ^ 2 := by
    calc
      |∫ s in 0..t, gExt s| ^ 2 ≤
          (Real.sqrt (∫ s in 0..t, |gExt s| ^ 2) * Real.sqrt t) ^ 2 := hroot
      _ = t * ∫ s in 0..t, |gExt s| ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hA, Real.sq_sqrt ht.le]
        ring
  have hSqEq : (∫ s in 0..t, |gExt s| ^ 2) =
      ∫ s in 0..t, |g s| ^ 2 := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards with s hs
    have hs' : s ∈ Ioc 0 t := by simpa [uIoc, ht.le] using hs
    have hsU : s ∈ U := ⟨hs'.1, lt_of_le_of_lt hs'.2 htτ⟩
    simp [gExt, U, hsU]
  calc
    |f t| ^ 2 = |∫ s in 0..t, g s| ^ 2 := by rw [hrepr]
    _ = |∫ s in 0..t, gExt s| ^ 2 := by rw [hJ_eq_g t ht htτ]
    _ ≤ t * ∫ s in 0..t, |gExt s| ^ 2 := hExtBound
    _ = t * ∫ s in 0..t, |g s| ^ 2 := by rw [hSqEq]

end CKN
