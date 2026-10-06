/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.CarlemanSobolevSupport
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Global weak derivatives of zero extensions

Compact support inside the product domain allows the weak integration-by-parts
identities to extend to the ambient space (`lem:carleman-sobolev` of the Escauriaza–Seregin–Šverák manuscript).
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN

private theorem exists_spaceTime_smooth_cutoff
    {U K : Set (Vec3 × ℝ)} (hU : IsOpen U) (hK : IsCompact K)
    (hKU : K ⊆ U) :
    ∃ χ : Vec3 × ℝ → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ U ∧
        (∀ x ∈ K, χ x = 1) ∧
        ∃ V : Set (Vec3 × ℝ), IsOpen V ∧ K ⊆ V ∧ EqOn χ 1 V := by
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_cthickening_subset_open hU hKU
  let O : Set (Vec3 × ℝ) := Metric.thickening δ K
  have hOopen : IsOpen O := by exact Metric.isOpen_thickening
  have hKO : K ⊆ O := by
    intro x hx
    change x ∈ Metric.thickening δ K
    rw [Metric.mem_thickening_iff]
    exact ⟨x, hx, by simp [hδ]⟩
  have hclosure : IsCompact (closure O) := by
    apply hK.cthickening.of_isClosed_subset isClosed_closure
    · exact Metric.closure_thickening_subset_cthickening δ K
  obtain ⟨f, hf_support, hf_smooth, hf_range⟩ :=
    hOopen.exists_contDiff_support_eq (n := ⊤)
  have hf_compact : HasCompactSupport f := by
    change IsCompact (tsupport f)
    change IsCompact (closure (Function.support f))
    rw [hf_support]
    exact hclosure
  have hf_positive : ∀ x ∈ K, 0 < f x := by
    intro x hx
    have hxO : x ∈ O := hKO hx
    have hfx : f x ≠ 0 := by
      intro hzero
      have : x ∉ Function.support f := by simpa [Function.mem_support] using hzero
      exact this (by simpa [hf_support] using hxO)
    have hnonneg : 0 ≤ f x := (hf_range (Set.mem_range_self x)).1
    exact lt_of_le_of_ne hnonneg (Ne.symm hfx)
  obtain ⟨m, hmpos, hmK⟩ := hK.exists_forall_le' hf_smooth.continuous.continuousOn
    (a := 0) hf_positive
  let c : ℝ := m / 2
  have hc : 0 < c := by dsimp [c]; positivity
  let χ : Vec3 × ℝ → ℝ := fun x => Real.smoothTransition (f x / c)
  have hχsmooth : ContDiff ℝ (⊤ : ℕ∞) χ := by
    exact Real.smoothTransition.contDiff.comp (hf_smooth.div_const c)
  have hχsupp : Function.support χ ⊆ tsupport f := by
    intro x hx
    by_contra hx'
    have hfx : f x = 0 := by
      by_contra hne
      exact hx' (subset_tsupport f (Function.mem_support.mpr hne))
    have hχx : χ x = 0 := by simp [χ, hfx]
    exact (Function.mem_support.mp hx) hχx
  have hχcompact : HasCompactSupport χ := by
    apply HasCompactSupport.of_support_subset_isCompact hclosure
    exact hχsupp.trans (by
      intro x hx
      change x ∈ closure (Function.support f) at hx
      simpa only [hf_support] using hx)
  have htsuppfU : tsupport f ⊆ U := by
    change closure (Function.support f) ⊆ U
    rw [hf_support]
    exact (Metric.closure_thickening_subset_cthickening δ K).trans hδU
  have hχtsupp : tsupport χ ⊆ U := by
    calc
      tsupport χ = closure (Function.support χ) := rfl
      _ ⊆ closure (tsupport f) := closure_mono hχsupp
      _ = tsupport f := (closure_eq_iff_isClosed.mpr (isClosed_tsupport f))
      _ ⊆ U := htsuppfU
  have hχone : ∀ x ∈ K, χ x = 1 := by
    intro x hx
    have hmx : m ≤ f x := hmK x hx
    have hratio : 1 ≤ f x / c := by
      apply (le_div_iff₀ hc).2
      dsimp [c]
      nlinarith only [hmx, hmpos]
    exact Real.smoothTransition.one_of_one_le hratio
  let V : Set (Vec3 × ℝ) := {x | c < f x}
  have hVopen : IsOpen V := by
    exact isOpen_lt continuous_const hf_smooth.continuous
  have hKV : K ⊆ V := by
    intro x hx
    change c < f x
    have hmx := hmK x hx
    dsimp [c]
    linarith only [hmx, hmpos]
  have hχV : EqOn χ 1 V := by
    intro x hx
    have hx' : c < f x := hx
    have hratio : 1 ≤ f x / c := (le_div_iff₀ hc).2 (by linarith only [hx'])
    exact Real.smoothTransition.one_of_one_le hratio
  exact ⟨χ, hχsmooth, hχcompact, hχtsupp, hχone, V, hVopen, hKV, hχV⟩

private theorem weakIdentity_zeroExtend
    {U K : Set (Vec3 × ℝ)} (hUopen : IsOpen U)
    (hUmeas : MeasurableSet U) (hK : IsCompact K) (hKU : K ⊆ U)
    {u g : Vec3 × ℝ → ℝ} {v : Vec3 × ℝ}
    (hweak : ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ →
      HasCompactSupport ψ → tsupport ψ ⊆ U →
      (∫ y in U, u y * (fderiv ℝ ψ y) v ∂(volume : Measure (Vec3 × ℝ))) =
        -∫ y in U, g y * ψ y ∂(volume : Measure (Vec3 × ℝ)))
    (hu0 : ∀ᵐ y ∂(volume : Measure (Vec3 × ℝ)),
      y ∈ U → y ∉ K → u y = 0)
    (hg0 : ∀ᵐ y ∂(volume : Measure (Vec3 × ℝ)),
      y ∈ U → y ∉ K → g y = 0)
    {φ : Vec3 × ℝ → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφc : HasCompactSupport φ) :
    (∫ y, zeroExtendField U u y * (fderiv ℝ φ y) v
        ∂(volume : Measure (Vec3 × ℝ))) =
      -∫ y, zeroExtendField U g y * φ y ∂(volume : Measure (Vec3 × ℝ)) := by
  obtain ⟨χ, hχ, hχc, hχU, hχK, V, hVopen, hKV, hχV⟩ :=
    exists_spaceTime_smooth_cutoff hUopen hK hKU
  let ψ : Vec3 × ℝ → ℝ := fun y => χ y * φ y
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ := hχ.mul hφ
  have hψc : HasCompactSupport ψ := hφc.mul_left
  have hψU : tsupport ψ ⊆ U :=
    tsupport_mul_subset_left.trans hχU
  have hweakψ := hweak ψ hψ hψc hψU
  have hproduct (y : Vec3 × ℝ) (hyK : y ∈ K) :
      (fderiv ℝ ψ y) v = (fderiv ℝ φ y) v := by
    have hχfd : HasFDerivAt χ (0 : (Vec3 × ℝ) →L[ℝ] ℝ) y := by
      have hneighborhood : χ =ᶠ[𝓝 y] fun _ => (1 : ℝ) := by
        filter_upwards [hVopen.mem_nhds (hKV hyK)] with z hz
        exact hχV hz
      exact (hasFDerivAt_const (1 : ℝ) y).congr_of_eventuallyEq hneighborhood
    have hφfd : HasFDerivAt φ (fderiv ℝ φ y) y :=
      (hφ.differentiable (by simp) y).hasFDerivAt
    have hprod := hχfd.mul hφfd
    have hfd : fderiv ℝ ψ y = fderiv ℝ φ y := by
      change fderiv ℝ (χ * φ) y = fderiv ℝ φ y
      simpa [hχK y hyK] using hprod.fderiv
    exact congrArg (fun L : (Vec3 × ℝ) →L[ℝ] ℝ => L v) hfd
  have hleftAE : ∀ᵐ y ∂(volume : Measure (Vec3 × ℝ)), y ∈ U →
      u y * (fderiv ℝ ψ y) v = u y * (fderiv ℝ φ y) v := by
    filter_upwards [hu0] with y hy0
    intro hyU
    by_cases hyK : y ∈ K
    · rw [hproduct y hyK]
    · rw [hy0 hyU hyK]
      simp
  have hrightAE : ∀ᵐ y ∂(volume : Measure (Vec3 × ℝ)), y ∈ U →
      g y * ψ y = g y * φ y := by
    filter_upwards [hg0] with y hy0
    intro hyU
    by_cases hyK : y ∈ K
    · simp [ψ, hχK y hyK]
    · rw [hy0 hyU hyK]
      simp
  have hleft :
      (∫ y in U, u y * (fderiv ℝ ψ y) v ∂(volume : Measure (Vec3 × ℝ))) =
        ∫ y in U, u y * (fderiv ℝ φ y) v ∂(volume : Measure (Vec3 × ℝ)) := by
    apply integral_congr_ae
    filter_upwards [hleftAE.filter_mono ae_restrict_le, ae_restrict_mem hUmeas]
      with y hy hyU
    exact hy hyU
  have hright :
      (∫ y in U, g y * ψ y ∂(volume : Measure (Vec3 × ℝ))) =
        ∫ y in U, g y * φ y ∂(volume : Measure (Vec3 × ℝ)) := by
    apply integral_congr_ae
    filter_upwards [hrightAE.filter_mono ae_restrict_le, ae_restrict_mem hUmeas]
      with y hy hyU
    exact hy hyU
  have hglobalLeft :
      (∫ y, zeroExtendField U u y * (fderiv ℝ φ y) v
          ∂(volume : Measure (Vec3 × ℝ))) =
        ∫ y in U, u y * (fderiv ℝ φ y) v ∂(volume : Measure (Vec3 × ℝ)) := by
    have heq : (fun y => zeroExtendField U u y * (fderiv ℝ φ y) v) =
        U.indicator (fun y => u y * (fderiv ℝ φ y) v) := by
      funext y
      by_cases hy : y ∈ U <;> simp [zeroExtendField, hy]
    rw [heq, integral_indicator hUmeas]
  have hglobalRight :
      (∫ y, zeroExtendField U g y * φ y ∂(volume : Measure (Vec3 × ℝ))) =
        ∫ y in U, g y * φ y ∂(volume : Measure (Vec3 × ℝ)) := by
    have heq : (fun y => zeroExtendField U g y * φ y) =
        U.indicator (fun y => g y * φ y) := by
      funext y
      by_cases hy : y ∈ U <;> simp [zeroExtendField, hy]
    rw [heq, integral_indicator hUmeas]
  calc
    (∫ y, zeroExtendField U u y * (fderiv ℝ φ y) v
        ∂(volume : Measure (Vec3 × ℝ)))
      = ∫ y in U, u y * (fderiv ℝ φ y) v
          ∂(volume : Measure (Vec3 × ℝ)) := hglobalLeft
    _ = ∫ y in U, u y * (fderiv ℝ ψ y) v
          ∂(volume : Measure (Vec3 × ℝ)) := hleft.symm
    _ = -∫ y in U, g y * ψ y ∂(volume : Measure (Vec3 × ℝ)) := hweakψ
    _ = -∫ y in U, g y * φ y ∂(volume : Measure (Vec3 × ℝ)) := by rw [hright]
    _ = -∫ y, zeroExtendField U g y * φ y
          ∂(volume : Measure (Vec3 × ℝ)) := by rw [hglobalRight]

/-- The zero extensions of a compactly supported space-time field and its weak data satisfy
the corresponding global weak integration-by-parts identities (`lem:carleman-sobolev`, ESS). -/
theorem spaceTimeZeroExtensions_weak_derivatives
    {Ω : Set Vec3} {I : Set ℝ} (hΩ : IsOpen Ω) (hI : IsOpen I)
    {w : ParabolicPoint → Vec3}
    {Dw : ParabolicPoint → Fin 3 → Vec3}
    {D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3}
    {Dtw : ParabolicPoint → Vec3}
    (hderiv : HasSpaceTimeWeakDerivs Ω I w Dw D2w Dtw)
    (hcompact : HasCompactSupport w)
    (htsupport : tsupport w ⊆ spaceTimeSet Ω I) :
    (∀ i j : Fin 3, ∀ φ : Vec3 × ℝ → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      (∫ y, zeroExtendField (Ω ×ˢ I)
        (fun q : Vec3 × ℝ => w (parabolicHomeomorph.symm q) i) y *
        (fderiv ℝ φ y) (basisVec j, 0) ∂(volume : Measure (Vec3 × ℝ))) =
        -∫ y, zeroExtendField (Ω ×ˢ I)
          (fun q : Vec3 × ℝ => Dw (parabolicHomeomorph.symm q) i j) y * φ y
          ∂(volume : Measure (Vec3 × ℝ))) ∧
    (∀ i j k : Fin 3, ∀ φ : Vec3 × ℝ → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      (∫ y, zeroExtendField (Ω ×ˢ I)
        (fun q : Vec3 × ℝ => Dw (parabolicHomeomorph.symm q) i j) y *
        (fderiv ℝ φ y) (basisVec k, 0) ∂(volume : Measure (Vec3 × ℝ))) =
        -∫ y, zeroExtendField (Ω ×ˢ I)
          (fun q : Vec3 × ℝ => D2w (parabolicHomeomorph.symm q) i j k) y * φ y
          ∂(volume : Measure (Vec3 × ℝ))) ∧
    (∀ i : Fin 3, ∀ φ : Vec3 × ℝ → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      (∫ y, zeroExtendField (Ω ×ˢ I)
        (fun q : Vec3 × ℝ => w (parabolicHomeomorph.symm q) i) y *
        (fderiv ℝ φ y) (0, 1) ∂(volume : Measure (Vec3 × ℝ))) =
        -∫ y, zeroExtendField (Ω ×ˢ I)
          (fun q : Vec3 × ℝ => Dtw (parabolicHomeomorph.symm q) i) y * φ y
          ∂(volume : Measure (Vec3 × ℝ))) := by
  let U : Set (Vec3 × ℝ) := Ω ×ˢ I
  let K : Set (Vec3 × ℝ) := parabolicHomeomorph '' tsupport w
  have hUopen : IsOpen U := hΩ.prod hI
  have hUmeas : MeasurableSet U := hUopen.measurableSet
  have hKcompact : IsCompact K := parabolicHomeomorph.isCompact_image.mpr hcompact.isCompact
  have hKU : K ⊆ U := by
    rintro y ⟨p, hp, rfl⟩
    exact htsupport hp
  have hzero := spaceTimeWeakDerivs_ae_zero_off_tsupport
    hΩ hI hderiv hcompact htsupport
  refine ⟨?_, ?_, ?_⟩
  · intro i j φ hφ hφc
    exact weakIdentity_zeroExtend hUopen hUmeas hKcompact hKU
      (fun ψ hψ hψc hψU => weak_spatial_identity_product hΩ hI hderiv hψ hψc hψU i j)
      (field_component_ae_zero_off_support (Ω := Ω) (I := I) (w := w) i)
      (hzero.1 i j) hφ hφc
  · intro i j k φ hφ hφc
    exact weakIdentity_zeroExtend hUopen hUmeas hKcompact hKU
      (fun ψ hψ hψc hψU => weak_spatialSecond_identity_product hΩ hI hderiv hψ hψc hψU i j k)
      (hzero.1 i j) (hzero.2.1 i j k) hφ hφc
  · intro i φ hφ hφc
    exact weakIdentity_zeroExtend hUopen hUmeas hKcompact hKU
      (fun ψ hψ hψc hψU => weak_time_identity_product hΩ hI hderiv hψ hψc hψU i)
      (field_component_ae_zero_off_support (Ω := Ω) (I := I) (w := w) i)
      (hzero.2.2 i) hφ hφc


end CKN
