/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.CarlemanSobolevLimit
public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.CarlemanSobolevApprox
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpatialGradient
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-!
# Density passage for compactly supported Carleman fields

Smooth weighted estimates pass to compactly supported fields with space-time weak derivatives
(`lem:carleman-sobolev`).
-/

public section


open MeasureTheory Set Filter
open scoped ENNReal Pointwise
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

private structure CarlemanMollificationSequenceState
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {K : Set X}
    {mass gradient residual : ℕ → X → ℝ}
    {massLimit gradientLimit residualLimit : X → ℝ} (c : ℝ) where
  leftLimit : Tendsto (fun n => (∫ x in K, mass n x ∂μ) +
    (∫ x in K, gradient n x ∂μ)) atTop
    (nhds ((∫ x in K, massLimit x ∂μ) + (∫ x in K, gradientLimit x ∂μ)))
  rightLimit : Tendsto (fun n => ∫ x in K, residual n x ∂μ) atTop
    (nhds (∫ x in K, residualLimit x ∂μ))
  eventualInequality : ∀ᶠ n in atTop,
    (∫ x in K, mass n x ∂μ) + (∫ x in K, gradient n x ∂μ) ≤
      c * (∫ x in K, residual n x ∂μ)

private structure WeightedWeakIntegralIdentifications
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (K : Set X)
    (σ τ ρ : X → ℝ) (W W0 : X → Fin 3 → ℝ)
    (G G0 : X → Fin 3 → Fin 3 → ℝ) (R R0 : X → Fin 3 → ℝ) where
  massAE : (fun z => σ z * vec3EuclideanNorm (W z) ^ 2) =ᵐ[μ.restrict K]
    (fun z => σ z * ∑ i, W0 z i ^ 2)
  gradientAE : (fun z => τ z * ∑ i, ∑ j, G z i j ^ 2) =ᵐ[μ.restrict K]
    (fun z => τ z * ∑ ij : Fin 3 × Fin 3, G0 z ij.1 ij.2 ^ 2)
  residualAE : (fun z => ρ z * vec3EuclideanNorm (R z) ^ 2) =ᵐ[μ.restrict K]
    (fun z => ρ z * ∑ i, R0 z i ^ 2)
  massIntegral : (∫ z in K, σ z * vec3EuclideanNorm (W z) ^ 2 ∂μ) =
    ∫ z in K, σ z * ∑ i, W0 z i ^ 2 ∂μ
  gradientIntegral : (∫ z in K, τ z * ∑ i, ∑ j, G z i j ^ 2 ∂μ) =
    ∫ z in K, τ z * ∑ ij : Fin 3 × Fin 3, G0 z ij.1 ij.2 ^ 2 ∂μ
  residualIntegral : (∫ z in K, ρ z * vec3EuclideanNorm (R z) ^ 2 ∂μ) =
    ∫ z in K, ρ z * ∑ i, R0 z i ^ 2 ∂μ

private structure WeakCarlemanIntegralPackage
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (U K : Set X)
    (σ τ ρ : X → ℝ) (W : X → Fin 3 → ℝ) (W0 : X → Fin 3 → ℝ)
    (G G0 : X → Fin 3 → Fin 3 → ℝ) (R R0 : X → Fin 3 → ℝ) where
  massIntegrable : Integrable (fun z => σ z * ∑ i, W0 z i ^ 2) (μ.restrict K)
  gradientIntegrable : Integrable
    (fun z => τ z * ∑ ij : Fin 3 × Fin 3, G0 z ij.1 ij.2 ^ 2) (μ.restrict K)
  massAE : (fun z => σ z * vec3EuclideanNorm (W z) ^ 2) =ᵐ[μ.restrict K]
    (fun z => σ z * ∑ i, W0 z i ^ 2)
  gradientAE : (fun z => τ z * ∑ i, ∑ j, G z i j ^ 2) =ᵐ[μ.restrict K]
    (fun z => τ z * ∑ ij : Fin 3 × Fin 3, G0 z ij.1 ij.2 ^ 2)
  massZeroOff : ∀ᵐ z ∂μ, z ∈ U → z ∉ K → σ z * vec3EuclideanNorm (W z) ^ 2 = 0
  gradientZeroOff : ∀ᵐ z ∂μ, z ∈ U → z ∉ K →
    τ z * ∑ i, ∑ j, G z i j ^ 2 = 0
  residualZeroOff : ∀ᵐ z ∂μ, z ∈ U → z ∉ K →
    ρ z * vec3EuclideanNorm (R z) ^ 2 = 0
  massTarget : (∫ z in K, σ z * vec3EuclideanNorm (W z) ^ 2 ∂μ) =
    ∫ z in K, σ z * ∑ i, W0 z i ^ 2 ∂μ
  gradientTarget : (∫ z in K, τ z * ∑ i, ∑ j, G z i j ^ 2 ∂μ) =
    ∫ z in K, τ z * ∑ ij : Fin 3 × Fin 3, G0 z ij.1 ij.2 ^ 2 ∂μ
  residualTarget : (∫ z in U, ρ z * vec3EuclideanNorm (R z) ^ 2 ∂μ) =
    ∫ z in K, ρ z * ∑ i, R0 z i ^ 2 ∂μ

private structure CompactWeightBounds
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [OpensMeasurableSpace X]
    (μ : Measure X) (K : Set X)
    (ρ σ τ : X → ℝ) where
  rhoBound : ℝ
  sigmaBound : ℝ
  tauBound : ℝ
  rhoNonneg : 0 ≤ rhoBound
  sigmaNonneg : 0 ≤ sigmaBound
  tauNonneg : 0 ≤ tauBound
  rhoAesm : AEStronglyMeasurable ρ (μ.restrict K)
  sigmaAesm : AEStronglyMeasurable σ (μ.restrict K)
  tauAesm : AEStronglyMeasurable τ (μ.restrict K)
  rhoBoundAE : ∀ᵐ z ∂(μ.restrict K), ‖ρ z‖ ≤ rhoBound
  sigmaBoundAE : ∀ᵐ z ∂(μ.restrict K), ‖σ z‖ ≤ sigmaBound
  tauBoundAE : ∀ᵐ z ∂(μ.restrict K), ‖τ z‖ ≤ tauBound

private def compactWeightBounds_of_continuous
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [OpensMeasurableSpace X]
    {μ : Measure X} {K : Set X}
    (hKcompact : IsCompact K) (hKmeas : MeasurableSet K)
    {ρ σ τ : X → ℝ}
    (hρcont : ContinuousOn ρ K) (hσcont : ContinuousOn σ K)
    (hτcont : ContinuousOn τ K) : CompactWeightBounds μ K ρ σ τ := by
  have hρbound := hKcompact.exists_bound_of_continuousOn hρcont
  have hσbound := hKcompact.exists_bound_of_continuousOn hσcont
  have hτbound := hKcompact.exists_bound_of_continuousOn hτcont
  let Cρ : ℝ := max hρbound.choose 0
  let Cσ : ℝ := max hσbound.choose 0
  let Cτ : ℝ := max hτbound.choose 0
  refine ⟨Cρ, Cσ, Cτ, le_max_right _ _, le_max_right _ _, le_max_right _ _,
    hρcont.aestronglyMeasurable hKmeas, hσcont.aestronglyMeasurable hKmeas,
    hτcont.aestronglyMeasurable hKmeas, ?_, ?_, ?_⟩
  · filter_upwards [ae_restrict_mem hKmeas] with z hz
    exact (hρbound.choose_spec z hz).trans (le_max_left _ _)
  · filter_upwards [ae_restrict_mem hKmeas] with z hz
    exact (hσbound.choose_spec z hz).trans (le_max_left _ _)
  · filter_upwards [ae_restrict_mem hKmeas] with z hz
    exact (hτbound.choose_spec z hz).trans (le_max_left _ _)

/-- A compactly supported space-time weak field inherits any weighted smooth Carleman inequality
whose coefficients are continuous on the product domain and bounded on compact subsets
(`lem:carleman-sobolev`). -/
private structure CarlemanMollificationSetup
    {Ω : Set Vec3} {I : Set ℝ} (hΩ : IsOpen Ω) (hI : IsOpen I)
    {w : ParabolicPoint → Vec3} {Dw : ParabolicPoint → Fin 3 → Vec3}
    {D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3}
    {Dtw : ParabolicPoint → Vec3}
    (hderiv : HasSpaceTimeWeakDerivs Ω I w Dw D2w Dtw)
    (hcompact : HasCompactSupport w)
    (htsupport : tsupport w ⊆ spaceTimeSet Ω I)
    (hL2 : (∫⁻ z in spaceTimeSet Ω I,
      ‖w z‖ₑ ^ (2 : ℝ) + ‖Dw z‖ₑ ^ (2 : ℝ) +
        ‖D2w z‖ₑ ^ (2 : ℝ) + ‖Dtw z‖ₑ ^ (2 : ℝ)) < ⊤) where
  radius : ℝ
  radiusPos : 0 < radius
  thickeningSubset :
    Metric.cthickening radius (parabolicHomeomorph '' tsupport w) ⊆ Ω ×ˢ I
  thickenedSupport : Set (Vec3 × ℝ)
  thickenedSupportEq : thickenedSupport =
    Metric.closedBall 0 (radius / 4) + (parabolicHomeomorph '' tsupport w)
  supportCompact : IsCompact (parabolicHomeomorph '' tsupport w)
  supportSubset : parabolicHomeomorph '' tsupport w ⊆ Ω ×ˢ I
  thickenedSupportCompact : IsCompact thickenedSupport
  thickenedSupportSubset : thickenedSupport ⊆ Ω ×ˢ I
  thickenedSupportMeas : MeasurableSet thickenedSupport
  delta : ℕ → ℝ
  deltaTendsto : Tendsto delta atTop (nhds 0)
  deltaPos : ∀ n, 0 < delta n
  deltaTests : ∀ n, spaceTimeMollifyPi
    (fun z => w (parabolicHomeomorph.symm z)) (delta n) (deltaPos n) ∈
      spaceTimeTestFunction (V := Vec3) Ω I
  deltaSmall : ∀ᶠ n in atTop, 4 * delta n ≤ radius / 2
  l2Data : MemLp (zeroExtendField (Ω ×ˢ I)
      (fun z : Vec3 × ℝ => w (parabolicHomeomorph.symm z)))
        (2 : ℝ≥0∞) (volume : Measure (Vec3 × ℝ)) ∧
    MemLp (zeroExtendField (Ω ×ˢ I)
      (fun z : Vec3 × ℝ => fun i j => Dw (parabolicHomeomorph.symm z) i j))
        (2 : ℝ≥0∞) (volume : Measure (Vec3 × ℝ)) ∧
    MemLp (zeroExtendField (Ω ×ˢ I)
      (fun z : Vec3 × ℝ => fun i j k => D2w (parabolicHomeomorph.symm z) i j k))
        (2 : ℝ≥0∞) (volume : Measure (Vec3 × ℝ)) ∧
    MemLp (zeroExtendField (Ω ×ˢ I)
      (fun z : Vec3 × ℝ => fun i => Dtw (parabolicHomeomorph.symm z) i))
        (2 : ℝ≥0∞) (volume : Measure (Vec3 × ℝ))
  weakZero : (∀ i j, ∀ᵐ z ∂(volume : Measure (Vec3 × ℝ)),
      z ∈ Ω ×ˢ I → z ∉ parabolicHomeomorph '' tsupport w →
        Dw (parabolicHomeomorph.symm z) i j = 0) ∧
    (∀ i j k, ∀ᵐ z ∂(volume : Measure (Vec3 × ℝ)),
      z ∈ Ω ×ˢ I → z ∉ parabolicHomeomorph '' tsupport w →
        D2w (parabolicHomeomorph.symm z) i j k = 0) ∧
    (∀ i, ∀ᵐ z ∂(volume : Measure (Vec3 × ℝ)),
      z ∈ Ω ×ˢ I → z ∉ parabolicHomeomorph '' tsupport w →
        Dtw (parabolicHomeomorph.symm z) i = 0)
  supportSubsetThickened : parabolicHomeomorph '' tsupport w ⊆ thickenedSupport
  pulledFieldSupport : tsupport (fun z => w (parabolicHomeomorph.symm z)) ⊆
    parabolicHomeomorph '' tsupport w
  pulledFieldRawSupport : tsupport (fun z => w (parabolicHomeomorph.symm z)) ⊆
    Ω ×ˢ I
  pulledFieldRawEq : zeroExtendField (Ω ×ˢ I)
      (fun z => w (parabolicHomeomorph.symm z)) =
        fun z => w (parabolicHomeomorph.symm z)
  pulledFieldMemLp : MemLp
    (fun z : Vec3 × ℝ => w (parabolicHomeomorph.symm z))
    (2 : ℝ≥0∞) (volume : Measure (Vec3 × ℝ))
  pulledFieldLocallyIntegrable : ∀ i : Fin 3,
    LocallyIntegrable (fun z : Vec3 × ℝ => w (parabolicHomeomorph.symm z) i)
      (volume : Measure (Vec3 × ℝ))
  pulledFieldCompactSupport : HasCompactSupport
    (fun z : Vec3 × ℝ => w (parabolicHomeomorph.symm z))

private def carlemanMollificationSetup_of_compactSupport
    {Ω : Set Vec3} {I : Set ℝ} (hΩ : IsOpen Ω) (hI : IsOpen I)
    {w : ParabolicPoint → Vec3} {Dw : ParabolicPoint → Fin 3 → Vec3}
    {D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3}
    {Dtw : ParabolicPoint → Vec3}
    (hderiv : HasSpaceTimeWeakDerivs Ω I w Dw D2w Dtw)
    (hcompact : HasCompactSupport w)
    (htsupport : tsupport w ⊆ spaceTimeSet Ω I)
    (hL2 : (∫⁻ z in spaceTimeSet Ω I,
      ‖w z‖ₑ ^ (2 : ℝ) + ‖Dw z‖ₑ ^ (2 : ℝ) +
        ‖D2w z‖ₑ ^ (2 : ℝ) + ‖Dtw z‖ₑ ^ (2 : ℝ)) < ⊤) :
    CarlemanMollificationSetup hΩ hI hderiv hcompact htsupport hL2 := by
  let U : Set (Vec3 × ℝ) := Ω ×ˢ I
  let K : Set (Vec3 × ℝ) := parabolicHomeomorph '' tsupport w
  let W : Vec3 × ℝ → Vec3 := fun z => w (parabolicHomeomorph.symm z)
  have hUopen : IsOpen U := by exact hΩ.prod hI
  have hKcompact : IsCompact K := parabolicHomeomorph.isCompact_image.mpr hcompact.isCompact
  have hKU : K ⊆ U := by
    rintro z ⟨p, hp, rfl⟩
    exact htsupport hp
  let hradius := hKcompact.exists_cthickening_subset_open hUopen hKU
  let r := Classical.choose hradius
  have hr : 0 < r := (Classical.choose_spec hradius).1
  have hthick : Metric.cthickening r K ⊆ U := (Classical.choose_spec hradius).2
  let K' : Set (Vec3 × ℝ) := Metric.closedBall 0 (r / 4) + K
  have hK'compact : IsCompact K' :=
    (isCompact_closedBall (0 : Vec3 × ℝ) (r / 4)).add hKcompact
  have hK'U : K' ⊆ U := by
    rintro z ⟨u, hu, v, hv, rfl⟩
    apply hthick
    apply Metric.mem_cthickening_of_dist_le (u + v) v r K hv
    have huv : dist (u + v) v ≤ r / 4 := by
      rw [dist_eq_norm]
      simpa using hu
    exact huv.trans (by nlinarith only [hr])
  have hK'meas : MeasurableSet K' := hK'compact.measurableSet
  have hL2data := zeroExtend_spaceTimeData_memLp hΩ hI hderiv hL2
  have hWtsupportK : tsupport W ⊆ K := by
    have hsupport : Function.support W ⊆ K := by
      intro z hz
      have hne : w (parabolicHomeomorph.symm z) ≠ 0 := by
        simpa [W, Function.mem_support] using hz
      exact ⟨parabolicHomeomorph.symm z,
        subset_tsupport w (Function.mem_support.mpr hne),
        parabolicHomeomorph.apply_symm_apply z⟩
    exact closure_minimal hsupport hKcompact.isClosed
  have hWrawSupport : tsupport W ⊆ U := hWtsupportK.trans hKU
  have hWrawEq : zeroExtendField U W = W := zeroExtend_eq_of_tsupport_subset U W hWrawSupport
  have hWmem : MemLp W (2 : ℝ≥0∞) (volume : Measure (Vec3 × ℝ)) := by
    rw [← hWrawEq]
    exact hL2data.1
  have hWloc : ∀ i : Fin 3,
      LocallyIntegrable (fun z : Vec3 × ℝ => W z i) (volume : Measure (Vec3 × ℝ)) := by
    intro i
    exact (memLp_pi_component hWmem i).locallyIntegrable (by norm_num)
  have hWcompact : HasCompactSupport W := product_field_hasCompactSupport hcompact
  let hsequence :=
    exists_spaceTimeMollifyPi_testSequence hΩ hI hWcompact hWrawSupport hWloc
  let δ := Classical.choose hsequence
  have hδtend : Tendsto δ atTop (nhds 0) := (Classical.choose_spec hsequence).1
  have hδtests : ∀ n, 0 < δ n ∧ ∀ hδ, spaceTimeMollifyPi W (δ n) hδ ∈
      spaceTimeTestFunction (V := Vec3) Ω I := (Classical.choose_spec hsequence).2
  have hδpos : ∀ n, 0 < δ n := fun n => (hδtests n).1
  have hδsmall : ∀ᶠ n in atTop, 4 * δ n ≤ r / 2 := by
    have hev : ∀ᶠ n in atTop, δ n < r / 8 :=
      hδtend.eventually (gt_mem_nhds (by positivity))
    filter_upwards [hev] with n hn
    nlinarith only [hn]
  have hweakZero := spaceTimeWeakDerivs_ae_zero_off_tsupport
    hΩ hI hderiv hcompact htsupport
  have hr4 : 0 ≤ r / 4 := by positivity
  have hzeroBall : (0 : Vec3 × ℝ) ∈ Metric.closedBall 0 (r / 4) :=
    Metric.mem_closedBall.mpr (by rw [dist_self]; exact hr4)
  have hKsubK' : K ⊆ K' := by
    intro z hz
    exact ⟨0, hzeroBall, z, hz, by simp⟩
  exact {
    radius := r
    radiusPos := hr
    thickeningSubset := hthick
    thickenedSupport := K'
    thickenedSupportEq := rfl
    supportCompact := hKcompact
    supportSubset := hKU
    thickenedSupportCompact := hK'compact
    thickenedSupportSubset := hK'U
    thickenedSupportMeas := hK'meas
    delta := δ
    deltaTendsto := hδtend
    deltaPos := hδpos
    deltaTests := by
      intro n
      simpa [W] using (hδtests n).2 (hδpos n)
    deltaSmall := hδsmall
    l2Data := by simpa [U, W] using hL2data
    weakZero := by simpa [U, K] using hweakZero
    supportSubsetThickened := hKsubK'
    pulledFieldSupport := by simpa [W, K] using hWtsupportK
    pulledFieldRawSupport := by simpa [W, U] using hWrawSupport
    pulledFieldRawEq := by simpa [W, U] using hWrawEq
    pulledFieldMemLp := hWmem
    pulledFieldLocallyIntegrable := by simpa [W] using hWloc
    pulledFieldCompactSupport := by simpa [W] using hWcompact }

private structure CarlemanMollifiedFamilyState
    (U K' : Set (Vec3 × ℝ))
    (W0 : Vec3 × ℝ → Vec3)
    (G0 : Vec3 × ℝ → Fin 3 → Fin 3 → ℝ)
    (H0 : Vec3 × ℝ → Fin 3 → Fin 3 → Fin 3 → ℝ)
    (T0 : Vec3 × ℝ → Fin 3 → ℝ)
    (δ : ℕ → ℝ) (hδpos : ∀ n, 0 < δ n)
    (hδtend : Tendsto δ atTop (nhds 0))
    (hWmem : MemLp W0 (2 : ℝ≥0∞) (volume : Measure (Vec3 × ℝ)))
    (hGmem : MemLp G0 (2 : ℝ≥0∞) (volume : Measure (Vec3 × ℝ)))
    (hHmem : MemLp H0 (2 : ℝ≥0∞) (volume : Measure (Vec3 × ℝ)))
    (hTmem : MemLp T0 (2 : ℝ≥0∞) (volume : Measure (Vec3 × ℝ))) where
  residual : Vec3 × ℝ → Fin 3 → ℝ
  residualZeroExtend : Vec3 × ℝ → Fin 3 → ℝ
  Wseq : ℕ → Vec3 × ℝ → Fin 3 → ℝ
  WseqMollify : ∀ n z i, Wseq n z i =
    spaceTimeMollify (fun q => W0 q i) (δ n) (hδpos n) z
  Gseq : ℕ → Vec3 × ℝ → Fin 3 × Fin 3 → ℝ
  GseqMollify : ∀ n z i j, Gseq n z (i, j) =
    spaceTimeMollify (fun q => G0 q i j) (δ n) (hδpos n) z
  Rseq : ℕ → Vec3 × ℝ → Fin 3 → ℝ
  RseqMollify : ∀ n z i, Rseq n z i =
    spaceTimeMollify (fun q => residualZeroExtend q i) (δ n) (hδpos n) z
  Wcomponent : ∀ i, MemLp (fun z => W0 z i) (2 : ℝ≥0∞) (volume : Measure (Vec3 × ℝ))
  Gcomponent : ∀ i j, MemLp (fun z => G0 z i j) (2 : ℝ≥0∞) (volume : Measure (Vec3 × ℝ))
  Hcomponent : ∀ i j k, MemLp (fun z => H0 z i j k) (2 : ℝ≥0∞) (volume : Measure (Vec3 × ℝ))
  Tcomponent : ∀ i, MemLp (fun z => T0 z i) (2 : ℝ≥0∞) (volume : Measure (Vec3 × ℝ))
  residualSource : ∀ i, (fun z => residualZeroExtend z i) =
    (fun z => T0 z i + ∑ j, H0 z i j j)
  residualComponent : ∀ i, MemLp (fun z => residualZeroExtend z i)
    (2 : ℝ≥0∞) (volume : Measure (Vec3 × ℝ))
  residualMollify : ∀ n i,
    spaceTimeMollify (fun z => residualZeroExtend z i) (δ n) (hδpos n) =
      fun z => spaceTimeMollify (fun q => T0 q i) (δ n) (hδpos n) z +
        ∑ j, spaceTimeMollify (fun q => H0 q i j j) (δ n) (hδpos n) z
  Wconv : ∀ i, Tendsto (fun n => eLpNorm
    (fun z => spaceTimeMollify (fun q => W0 q i) (δ n) (hδpos n) z - W0 z i) 2
    ((volume : Measure (Vec3 × ℝ)).restrict K')) atTop (nhds 0)
  Gconv : ∀ i j, Tendsto (fun n => eLpNorm
    (fun z => spaceTimeMollify (fun q => G0 q i j) (δ n) (hδpos n) z - G0 z i j) 2
    ((volume : Measure (Vec3 × ℝ)).restrict K')) atTop (nhds 0)
  Rconv : ∀ i, Tendsto (fun n => eLpNorm
    (fun z => spaceTimeMollify (fun q => residualZeroExtend q i) (δ n) (hδpos n) z -
      residualZeroExtend z i) 2 ((volume : Measure (Vec3 × ℝ)).restrict K')) atTop (nhds 0)
  WseqMem : ∀ n i, MemLp (fun z => Wseq n z i) (2 : ℝ≥0∞)
    ((volume : Measure (Vec3 × ℝ)).restrict K')
  GseqMem : ∀ n ij, MemLp (fun z => Gseq n z ij) (2 : ℝ≥0∞)
    ((volume : Measure (Vec3 × ℝ)).restrict K')
  RseqMem : ∀ n i, MemLp (fun z => Rseq n z i) (2 : ℝ≥0∞)
    ((volume : Measure (Vec3 × ℝ)).restrict K')

private theorem mollifiedFamily_l2_state
    {ι : Type*} {f : ι → Vec3 × ℝ → ℝ}
    (hf : ∀ i, MemLp (f i) (2 : ℝ≥0∞) (volume : Measure (Vec3 × ℝ)))
    {δ : ℕ → ℝ} (hδtend : Tendsto δ atTop (nhds 0))
    (hδpos : ∀ n, 0 < δ n) (K : Set (Vec3 × ℝ)) :
    (∀ i, Tendsto (fun n => eLpNorm
      (fun z => spaceTimeMollify (f i) (δ n) (hδpos n) z - f i z) 2
      ((volume : Measure (Vec3 × ℝ)).restrict K)) atTop (nhds 0)) ∧
    (∀ n i, MemLp (fun z => spaceTimeMollify (f i) (δ n) (hδpos n) z)
      (2 : ℝ≥0∞) ((volume : Measure (Vec3 × ℝ)).restrict K)) := by
  constructor
  · intro i
    exact tendsto_mollify_l2_restrict (hf i) hδtend hδpos K
  · intro n i
    exact (spaceTimeMollify_memLp_of_memLp (hδpos n) (hf i)).restrict K

private theorem mollifiedResidualOperator_state
    {R0 : Vec3 × ℝ → Fin 3 → ℝ}
    {T0 : Vec3 × ℝ → Fin 3 → ℝ}
    {H0 : Vec3 × ℝ → Fin 3 → Fin 3 → Fin 3 → ℝ}
    (hRsource : ∀ i, (fun z : Vec3 × ℝ => R0 z i) =
      (fun z => T0 z i + ∑ j, H0 z i j j))
    (hTcomponent : ∀ i, MemLp (fun z : Vec3 × ℝ => T0 z i) (2 : ℝ≥0∞)
      (volume : Measure (Vec3 × ℝ)))
    (hHcomponent : ∀ i j k, MemLp (fun z : Vec3 × ℝ => H0 z i j k)
      (2 : ℝ≥0∞) (volume : Measure (Vec3 × ℝ)))
    (δ : ℕ → ℝ) (hδpos : ∀ n, 0 < δ n) :
    (∀ i, MemLp (fun z : Vec3 × ℝ => R0 z i) (2 : ℝ≥0∞)
      (volume : Measure (Vec3 × ℝ))) ∧
    (∀ n i, spaceTimeMollify (fun z : Vec3 × ℝ => R0 z i) (δ n) (hδpos n) =
      fun z => spaceTimeMollify (fun q => T0 q i) (δ n) (hδpos n) z +
        ∑ j, spaceTimeMollify (fun q => H0 q i j j) (δ n) (hδpos n) z) := by
  constructor
  · intro i
    have hdiag : MemLp (fun z : Vec3 × ℝ => ∑ j, H0 z i j j)
        (2 : ℝ≥0∞) (volume : Measure (Vec3 × ℝ)) := by
      simpa only [Finset.univ_eq_attach] using
        memLp_finsetSum (Finset.univ : Finset (Fin 3)) (by
          intro j hj
          exact hHcomponent i j j)
    rw [hRsource i]
    exact (hTcomponent i).add hdiag
  · intro n i
    calc
      spaceTimeMollify (fun z : Vec3 × ℝ => R0 z i) (δ n) (hδpos n) =
          spaceTimeMollify (fun z => T0 z i + ∑ j, H0 z i j j)
            (δ n) (hδpos n) := by rw [hRsource i]
      _ = spaceTimeMollify (fun z => T0 z i) (δ n) (hδpos n) +
          spaceTimeMollify (fun z => ∑ j, H0 z i j j) (δ n) (hδpos n) := by
        change spaceTimeMollify
          ((fun z => T0 z i) + (fun z => ∑ j, H0 z i j j))
          (δ n) (hδpos n) = _
        have hdiag : MemLp (fun z : Vec3 × ℝ => ∑ j, H0 z i j j)
            (2 : ℝ≥0∞) (volume : Measure (Vec3 × ℝ)) := by
          simpa only [Finset.univ_eq_attach] using
            memLp_finsetSum (Finset.univ : Finset (Fin 3)) (by
              intro j hj
              exact hHcomponent i j j)
        exact spaceTimeMollify_add_of_memLp (hδpos n) (hTcomponent i) hdiag
      _ = _ := by
        rw [spaceTimeMollify_finset_sum (hδpos n) (by
          intro j hj
          exact hHcomponent i j j)]
        funext z
        rfl


private def carlemanMollifiedFamilyState_of_l2
    (U K' : Set (Vec3 × ℝ))
    (W0 : Vec3 × ℝ → Vec3)
    (G0 : Vec3 × ℝ → Fin 3 → Fin 3 → ℝ)
    (H0 : Vec3 × ℝ → Fin 3 → Fin 3 → Fin 3 → ℝ)
    (T0 : Vec3 × ℝ → Fin 3 → ℝ)
    (δ : ℕ → ℝ) (hδpos : ∀ n, 0 < δ n)
    (hδtend : Tendsto δ atTop (nhds 0))
    (hWmem : MemLp W0 (2 : ℝ≥0∞) (volume : Measure (Vec3 × ℝ)))
    (hGmem : MemLp G0 (2 : ℝ≥0∞) (volume : Measure (Vec3 × ℝ)))
    (hHmem : MemLp H0 (2 : ℝ≥0∞) (volume : Measure (Vec3 × ℝ)))
    (hTmem : MemLp T0 (2 : ℝ≥0∞) (volume : Measure (Vec3 × ℝ)))
    (hTzero : ∀ z i, z ∉ U → T0 z i = 0)
    (hHzero : ∀ z i j k, z ∉ U → H0 z i j k = 0) :
    CarlemanMollifiedFamilyState U K' W0 G0 H0 T0 δ hδpos hδtend
      hWmem hGmem hHmem hTmem := by
  have hWcomponent (i : Fin 3) := memLp_pi_component hWmem i
  have hGcomponent (i j : Fin 3) := memLp_pi_component (memLp_pi_component hGmem i) j
  have hHcomponent (i j k : Fin 3) :=
    memLp_pi_component (memLp_pi_component (memLp_pi_component hHmem i) j) k
  have hTcomponent (i : Fin 3) := memLp_pi_component hTmem i
  let R : Vec3 × ℝ → Fin 3 → ℝ := fun z i => T0 z i + ∑ j, H0 z i j j
  let R0 : Vec3 × ℝ → Fin 3 → ℝ := zeroExtendField U R
  have hRsource (i : Fin 3) :
      (fun z : Vec3 × ℝ => R0 z i) =
        (fun z => T0 z i + ∑ j, H0 z i j j) := by
    funext z
    by_cases hz : z ∈ U
    · simp [R0, R, zeroExtendField, hz]
    · simp [R0, R, zeroExtendField, hz, hTzero z i hz, hHzero z i]
  have hResidualOperator := mollifiedResidualOperator_state
    (fun i => hRsource i) (fun i => hTcomponent i)
    (fun i j k => hHcomponent i j k) δ hδpos
  let Wseq : ℕ → Vec3 × ℝ → Fin 3 → ℝ := fun n z i =>
    spaceTimeMollify (fun q => W0 q i) (δ n) (hδpos n) z
  let Gseq : ℕ → Vec3 × ℝ → Fin 3 × Fin 3 → ℝ := fun n z ij =>
    spaceTimeMollify (fun q => G0 q ij.1 ij.2) (δ n) (hδpos n) z
  let Rseq : ℕ → Vec3 × ℝ → Fin 3 → ℝ := fun n z i =>
    spaceTimeMollify (fun q => R0 q i) (δ n) (hδpos n) z
  have hWfamily := mollifiedFamily_l2_state (fun i => hWcomponent i)
    hδtend hδpos K'
  have hGfamily := mollifiedFamily_l2_state
    (fun ij : Fin 3 × Fin 3 => hGcomponent ij.1 ij.2) hδtend hδpos K'
  have hRfamily := mollifiedFamily_l2_state
    (fun i => hResidualOperator.1 i) hδtend hδpos K'
  exact {
    residual := R
    residualZeroExtend := R0
    Wseq := Wseq
    WseqMollify := by intro n z i; rfl
    Gseq := Gseq
    GseqMollify := by intro n z i j; rfl
    Rseq := Rseq
    RseqMollify := by intro n z i; rfl
    Wcomponent := hWcomponent
    Gcomponent := hGcomponent
    Hcomponent := hHcomponent
    Tcomponent := hTcomponent
    residualSource := hRsource
    residualComponent := hResidualOperator.1
    residualMollify := hResidualOperator.2
    Wconv := by intro i; simpa [Wseq] using hWfamily.1 i
    Gconv := by intro i j; simpa [Gseq] using hGfamily.1 (i, j)
    Rconv := by intro i; simpa [Rseq] using hRfamily.1 i
    WseqMem := by intro n i; simpa [Wseq] using hWfamily.2 n i
    GseqMem := by intro n ij; simpa [Gseq] using hGfamily.2 n ij
    RseqMem := by intro n i; simpa [Rseq] using hRfamily.2 n i }



private theorem compact_support_restrict_smooth_estimate
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {U K : Set X}
    (hUmeas : MeasurableSet U) (hKmeas : MeasurableSet K) (hKsubU : K ⊆ U)
    {left right : X → ℝ} {c : ℝ}
    (hsmooth : (∫ x in U, left x ∂μ) ≤ c * (∫ x in U, right x ∂μ))
    (hleftOff : ∀ᵐ x ∂μ, x ∈ U → x ∉ K → left x = 0)
    (hrightOff : ∀ᵐ x ∂μ, x ∈ U → x ∉ K → right x = 0) :
    (∫ x in K, left x ∂μ) ≤ c * (∫ x in K, right x ∂μ) := by
  have hleftDomain := setIntegral_eq_of_zero_off hUmeas hKmeas hKsubU hleftOff
  have hrightDomain := setIntegral_eq_of_zero_off hUmeas hKmeas hKsubU hrightOff
  rw [hleftDomain, hrightDomain] at hsmooth
  exact hsmooth


private theorem smoothMollification_compact_integral_state
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {U K : Set X}
    (hUmeas : MeasurableSet U) (hKmeas : MeasurableSet K) (hKsubU : K ⊆ U)
    {smoothLeft smoothRight mass gradient residual : ℕ → X → ℝ}
    {good : ℕ → Prop} {c : ℝ}
    (hmassInt : ∀ n, Integrable (mass n) (μ.restrict K))
    (hgradientInt : ∀ n, Integrable (gradient n) (μ.restrict K))
    (hpoint : ∀ n, good n → ∀ z ∈ K,
      smoothLeft n z = mass n z + gradient n z ∧
      smoothRight n z = residual n z)
    (hleftOff : ∀ n, good n → ∀ᵐ z ∂μ, z ∈ U → z ∉ K → smoothLeft n z = 0)
    (hrightOff : ∀ n, good n → ∀ᵐ z ∂μ, z ∈ U → z ∉ K → smoothRight n z = 0)
    (hSmooth : ∀ n, good n →
      (∫ z in U, smoothLeft n z ∂μ) ≤ c * (∫ z in U, smoothRight n z ∂μ)) :
    (∀ n, good n →
      (∫ z in K, smoothLeft n z ∂μ) =
        (∫ z in K, mass n z ∂μ) + (∫ z in K, gradient n z ∂μ)) ∧
    (∀ n, good n →
      (∫ z in K, smoothRight n z ∂μ) = ∫ z in K, residual n z ∂μ) ∧
    (∀ n, good n →
      (∫ z in K, smoothLeft n z ∂μ) ≤ c * (∫ z in K, smoothRight n z ∂μ)) := by
  have hleftK : ∀ n, good n →
      (∫ z in K, smoothLeft n z ∂μ) =
        (∫ z in K, mass n z ∂μ) + (∫ z in K, gradient n z ∂μ) := by
    intro n hn
    calc
      (∫ z in K, smoothLeft n z ∂μ) = ∫ z in K, mass n z + gradient n z ∂μ := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem hKmeas] with z hz
        exact (hpoint n hn z hz).1
      _ = (∫ z in K, mass n z ∂μ) + (∫ z in K, gradient n z ∂μ) :=
        integral_add (hmassInt n) (hgradientInt n)
  have hrightK : ∀ n, good n →
      (∫ z in K, smoothRight n z ∂μ) = ∫ z in K, residual n z ∂μ := by
    intro n hn
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hKmeas] with z hz
    exact (hpoint n hn z hz).2
  have hcompact : ∀ n, good n →
      (∫ z in K, smoothLeft n z ∂μ) ≤ c * (∫ z in K, smoothRight n z ∂μ) := by
    intro n hn
    have hsmooth := hSmooth n hn
    exact compact_support_restrict_smooth_estimate hUmeas hKmeas hKsubU
      hsmooth (hleftOff n hn) (hrightOff n hn)
  exact ⟨hleftK, hrightK, hcompact⟩


private theorem weightedCarleman_approximation_package
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {K : Set X}
    {mass gradient residual smoothLeft smoothRight : ℕ → X → ℝ}
    {massLimit gradientLimit residualLimit : X → ℝ} {c : ℝ}
    (hMassLimit : Tendsto (fun n => ∫ x in K, mass n x ∂μ) atTop
      (nhds (∫ x in K, massLimit x ∂μ)))
    (hGradientLimit : Tendsto (fun n => ∫ x in K, gradient n x ∂μ) atTop
      (nhds (∫ x in K, gradientLimit x ∂μ)))
    (hResidualLimit : Tendsto (fun n => ∫ x in K, residual n x ∂μ) atTop
      (nhds (∫ x in K, residualLimit x ∂μ)))
    {good : ℕ → Prop}
    (hgood : ∀ᶠ n in atTop, good n)
    (hleft : ∀ n, good n →
      (∫ x in K, smoothLeft n x ∂μ) =
        (∫ x in K, mass n x ∂μ) + (∫ x in K, gradient n x ∂μ))
    (hright : ∀ n, good n →
      (∫ x in K, smoothRight n x ∂μ) = ∫ x in K, residual n x ∂μ)
    (hsmooth : ∀ n, good n →
      (∫ x in K, smoothLeft n x ∂μ) ≤ c * (∫ x in K, smoothRight n x ∂μ)) :
    Tendsto (fun n => (∫ x in K, mass n x ∂μ) + (∫ x in K, gradient n x ∂μ))
        atTop (nhds ((∫ x in K, massLimit x ∂μ) +
          (∫ x in K, gradientLimit x ∂μ))) ∧
      Tendsto (fun n => ∫ x in K, residual n x ∂μ) atTop
        (nhds (∫ x in K, residualLimit x ∂μ)) ∧
      ∀ᶠ n in atTop,
        (∫ x in K, mass n x ∂μ) + (∫ x in K, gradient n x ∂μ) ≤
          c * (∫ x in K, residual n x ∂μ) := by
  have hleftLimit := hMassLimit.add hGradientLimit
  have hseq : ∀ᶠ n in atTop,
      (∫ x in K, mass n x ∂μ) + (∫ x in K, gradient n x ∂μ) ≤
        c * (∫ x in K, residual n x ∂μ) := by
    filter_upwards [hgood] with n hn
    have h := hsmooth n hn
    rw [hleft n hn, hright n hn] at h
    exact h
  exact ⟨hleftLimit, hResidualLimit, hseq⟩


private theorem carlemanMollification_limit_state
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {U K : Set X}
    (hUmeas : MeasurableSet U) (hKmeas : MeasurableSet K) (hKsubU : K ⊆ U)
    {mass gradient residual smoothLeft smoothRight : ℕ → X → ℝ}
    {massLimit gradientLimit residualLimit : X → ℝ} {c : ℝ}
    {good : ℕ → Prop}
    (hpoint : ∀ n, good n → ∀ z ∈ K,
      smoothLeft n z = mass n z + gradient n z ∧
      smoothRight n z = residual n z)
    (hleftOff : ∀ n, good n → ∀ᵐ z ∂μ,
      z ∈ U → z ∉ K → smoothLeft n z = 0)
    (hrightOff : ∀ n, good n → ∀ᵐ z ∂μ,
      z ∈ U → z ∉ K → smoothRight n z = 0)
    (hSmooth : ∀ n, good n →
      (∫ z in U, smoothLeft n z ∂μ) ≤ c * (∫ z in U, smoothRight n z ∂μ))
    (hMassLimit : Tendsto (fun n => ∫ z in K, mass n z ∂μ) atTop
      (nhds (∫ z in K, massLimit z ∂μ)))
    (hGradientLimit : Tendsto (fun n => ∫ z in K, gradient n z ∂μ) atTop
      (nhds (∫ z in K, gradientLimit z ∂μ)))
    (hResidualLimit : Tendsto (fun n => ∫ z in K, residual n z ∂μ) atTop
      (nhds (∫ z in K, residualLimit z ∂μ)))
    (hgood : ∀ᶠ n in atTop, good n)
    (hmassInt : ∀ n, Integrable (mass n) (μ.restrict K))
    (hgradientInt : ∀ n, Integrable (gradient n) (μ.restrict K)) :
    Tendsto (fun n => (∫ z in K, mass n z ∂μ) +
      ∫ z in K, gradient n z ∂μ) atTop
      (nhds ((∫ z in K, massLimit z ∂μ) + (∫ z in K, gradientLimit z ∂μ))) ∧
    Tendsto (fun n => ∫ z in K, residual n z ∂μ) atTop
      (nhds (∫ z in K, residualLimit z ∂μ)) ∧
    CarlemanMollificationSequenceState (μ := μ) (K := K) (mass := mass)
      (gradient := gradient) (residual := residual) (massLimit := massLimit)
      (gradientLimit := gradientLimit) (residualLimit := residualLimit) c := by
  obtain ⟨hleft, hright, hsmooth⟩ := smoothMollification_compact_integral_state
    hUmeas hKmeas hKsubU hmassInt hgradientInt hpoint hleftOff hrightOff hSmooth
  have hstate := weightedCarleman_approximation_package hMassLimit hGradientLimit
    hResidualLimit hgood hleft hright hsmooth
  exact ⟨hstate.1, hstate.2.1, ⟨hstate.1, hstate.2.1, hstate.2.2⟩⟩


private theorem spaceTimeMollify_tsupport_subset_closedBall_add
    {f : Vec3 × ℝ → ℝ} {K : Set (Vec3 × ℝ)} {δ r : ℝ}
    (hδ : 0 < δ) (hδle : δ ≤ r / 4) (hKcompact : IsCompact K)
    (hsupport : tsupport f ⊆ K) :
    tsupport (spaceTimeMollify f δ hδ) ⊆
      Metric.closedBall 0 (r / 4) + K := by
  have hsupport' : Function.support (spaceTimeMollify f δ hδ) ⊆
      Metric.ball 0 δ + Function.support f :=
    spaceTimeMollify_support_subset (f := f) hδ
  have hsum : Function.support (spaceTimeMollify f δ hδ) ⊆
      Metric.closedBall 0 (r / 4) + K := by
    intro z hz
    rcases hsupport' hz with ⟨u, hu, v, hv, rfl⟩
    refine ⟨u, ?_, v, ?_, rfl⟩
    · rw [Metric.mem_closedBall]
      exact (Metric.mem_ball.mp hu).le.trans hδle
    · exact hsupport (subset_tsupport _ hv)
  exact closure_minimal hsum
    ((isCompact_closedBall (0 : Vec3 × ℝ) (r / 4)).add hKcompact).isClosed

private theorem mollified_test_derivatives_zero_off
    {W : Vec3 × ℝ → Vec3} {K K' : Set (Vec3 × ℝ)}
    (hWsupport : ∀ i : Fin 3, tsupport (fun z : Vec3 × ℝ => W z i) ⊆ K)
    (hKcompact : IsCompact K) {r : ℝ} (δ : ℕ → ℝ)
    (hδpos : ∀ n, 0 < δ n)
    (hK' : K' = Metric.closedBall 0 (r / 4) + K) :
    (∀ n i (_hn : 4 * δ n ≤ r / 2) {z}, z ∉ K' →
      spaceTimeMollifyPi W (δ n) (hδpos n) z i = 0) ∧
    (∀ n i j (_hn : 4 * δ n ≤ r / 2) {z}, z ∉ K' →
      spatialPartial (fun q : ParabolicPoint =>
        spaceTimeMollifyPi W (δ n) (hδpos n) q i) j z = 0) ∧
    (∀ n i j k (_hn : 4 * δ n ≤ r / 2) {z}, z ∉ K' →
      spatialSecondPartial (fun q : ParabolicPoint =>
        spaceTimeMollifyPi W (δ n) (hδpos n) q i) j k z = 0) ∧
    (∀ n i (_hn : 4 * δ n ≤ r / 2) {z}, z ∉ K' →
      timePartial (fun q : ParabolicPoint =>
        spaceTimeMollifyPi W (δ n) (hδpos n) q i) z = 0) := by
  have hVsupport (n : ℕ) (i : Fin 3) (hn : 4 * δ n ≤ r / 2) :
      tsupport (fun z : Vec3 × ℝ =>
        spaceTimeMollifyPi W (δ n) (hδpos n) z i) ⊆ K' := by
    have hn' : 8 * δ n ≤ r := by nlinarith only [hn]
    have hδle : δ n ≤ r / 4 := by nlinarith only [hn', hδpos n]
    have hcomponent : tsupport (fun z : Vec3 × ℝ => W z i) ⊆ K := hWsupport i
    simpa [hK', spaceTimeMollifyPi] using spaceTimeMollify_tsupport_subset_closedBall_add
      (f := fun z => W z i) (K := K) (hδpos n) hδle hKcompact hcomponent
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n i hn z hz
    exact value_eq_zero_of_tsupport_subset (hVsupport n i hn) hz
  · intro n i j hn z hz
    have hsupp : tsupport (fun z : Vec3 × ℝ =>
        spatialPartial (fun q : ParabolicPoint =>
          spaceTimeMollifyPi W (δ n) (hδpos n) q i) j z) ⊆ K' :=
      (spatialPartial_tsupport_subset_product
        (f := fun z => spaceTimeMollifyPi W (δ n) (hδpos n) z i) j).trans
        (hVsupport n i hn)
    exact value_eq_zero_of_tsupport_subset hsupp hz
  · intro n i j k hn z hz
    have hsupp : tsupport (fun z : Vec3 × ℝ =>
        spatialSecondPartial (fun q : ParabolicPoint =>
          spaceTimeMollifyPi W (δ n) (hδpos n) q i) j k z) ⊆ K' :=
      (spatialSecondPartial_tsupport_subset_product
        (f := fun z => spaceTimeMollifyPi W (δ n) (hδpos n) z i) j k).trans
        (hVsupport n i hn)
    exact value_eq_zero_of_tsupport_subset hsupp hz
  · intro n i hn z hz
    have hsupp : tsupport (fun z : Vec3 × ℝ =>
        timePartial (fun q : ParabolicPoint =>
          spaceTimeMollifyPi W (δ n) (hδpos n) q i) z) ⊆ K' :=
      (timePartial_tsupport_subset_product
        (f := fun z => spaceTimeMollifyPi W (δ n) (hδpos n) z i)).trans
        (hVsupport n i hn)
    exact value_eq_zero_of_tsupport_subset hsupp hz


private theorem carlemanMollifiedPointwise_decomposition
    {V : (Vec3 × ℝ) → Vec3} {Wseq : Fin 3 → ℝ}
    {Gseq : Fin 3 × Fin 3 → ℝ} {Rseq : Fin 3 → ℝ}
    (σ τ ρ : Vec3 × ℝ → ℝ) (z : Vec3 × ℝ)
    (hV : ∀ i, V z i = Wseq i)
    (hG : ∀ i j, spatialPartial (fun q : ParabolicPoint => V q i) j z = Gseq (i, j))
    (hR : ∀ i, timePartial (fun q : ParabolicPoint => V q i) z +
      ∑ j, spatialSecondPartial (fun q : ParabolicPoint => V q i) j j z = Rseq i) :
    σ z * vec3EuclideanNorm (V z) ^ 2 +
        τ z * spatialGradientSq V (spatialGradient V) z =
      σ z * ∑ i, Wseq i ^ 2 + τ z * ∑ ij : Fin 3 × Fin 3, Gseq ij ^ 2 ∧
    ρ z * vec3EuclideanNorm (fun i =>
      timePartial (fun q : ParabolicPoint => V q i) z +
        ∑ j, spatialSecondPartial (fun q : ParabolicPoint => V q i) j j z) ^ 2 =
      ρ z * ∑ i, Rseq i ^ 2 := by
  have hmass : vec3EuclideanNorm (V z) ^ 2 = ∑ i, Wseq i ^ 2 := by
    rw [vec3EuclideanNorm_sq]
    apply Finset.sum_congr rfl
    intro i hi
    simp [hV i]
  have hgrad : spatialGradientSq V (spatialGradient V) z =
      ∑ ij : Fin 3 × Fin 3, Gseq ij ^ 2 := by
    calc
      spatialGradientSq V (spatialGradient V) z =
          ∑ i, ∑ j, spatialPartial (fun q : ParabolicPoint => V q i) j z ^ 2 := rfl
      _ = ∑ ij : Fin 3 × Fin 3, Gseq ij ^ 2 := by
        rw [fin3_double_sum_eq_product]
        apply Finset.sum_congr rfl
        rintro ⟨i, j⟩ hij
        rw [hG i j]
  constructor
  · rw [hmass, hgrad]
  · rw [vec3EuclideanNorm_sq]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [hR i]


private theorem mollifiedCarlemanIntegrands_zero_off
    {good : ℕ → Prop} {Vseq : ℕ → Vec3 × ℝ → Vec3}
    {U K : Set (Vec3 × ℝ)} {μ : Measure (Vec3 × ℝ)}
    {σ τ ρ : Vec3 × ℝ → ℝ}
    (hVzero : ∀ n i, good n → ∀ {z}, z ∉ K → Vseq n z i = 0)
    (hSpatialZero : ∀ n i j, good n → ∀ {z}, z ∉ K →
      spatialPartial (fun q : ParabolicPoint => Vseq n q i) j z = 0)
    (hSecondZero : ∀ n i j k, good n → ∀ {z}, z ∉ K →
      spatialSecondPartial (fun q : ParabolicPoint => Vseq n q i) j k z = 0)
    (hTimeZero : ∀ n i, good n → ∀ {z}, z ∉ K →
      timePartial (fun q : ParabolicPoint => Vseq n q i) z = 0) :
    (∀ n, good n → ∀ᵐ z ∂μ, z ∈ U → z ∉ K →
      σ z * vec3EuclideanNorm (Vseq n z) ^ 2 +
        τ z * spatialGradientSq (Vseq n) (spatialGradient (Vseq n)) z = 0) ∧
    (∀ n, good n → ∀ᵐ z ∂μ, z ∈ U → z ∉ K →
      ρ z * vec3EuclideanNorm (fun i =>
        timePartial (fun q : ParabolicPoint => Vseq n q i) z +
          ∑ j, spatialSecondPartial (fun q : ParabolicPoint => Vseq n q i) j j z) ^ 2 = 0) := by
  constructor
  · intro n hn
    filter_upwards [] with z
    intro hzU hzK
    have hv : Vseq n z = 0 := funext fun i => hVzero n i hn hzK
    have hgrad : spatialGradientSq (Vseq n) (spatialGradient (Vseq n)) z = 0 := by
      unfold spatialGradientSq spatialGradient
      apply Finset.sum_eq_zero
      intro i hi
      apply Finset.sum_eq_zero
      intro j hj
      simp [hSpatialZero n i j hn hzK]
    rw [hv, hgrad]
    simp [vec3EuclideanNorm]
  · intro n hn
    filter_upwards [] with z
    intro hzU hzK
    have hop : (fun i : Fin 3 =>
        timePartial (fun q : ParabolicPoint => Vseq n q i) z +
          ∑ j, spatialSecondPartial (fun q : ParabolicPoint => Vseq n q i) j j z) = 0 := by
      funext i
      rw [hTimeZero n i hn hzK]
      have hsum : (∑ j, spatialSecondPartial
          (fun q : ParabolicPoint => Vseq n q i) j j z) = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        exact hSecondZero n i j j hn hzK
      rw [hsum]
      simp
    rw [hop]
    simp [vec3EuclideanNorm]


private theorem carlemanWeightedMollificationState
    {Ω : Set Vec3} {I : Set ℝ} {U K' : Set (Vec3 × ℝ)}
    (hUmeas : MeasurableSet U) (hK'meas : MeasurableSet K') (hK'U : K' ⊆ U)
    (r : ℝ) (δ : ℕ → ℝ) (hδpos : ∀ n, 0 < δ n)
    (hδtend : Tendsto δ atTop (nhds 0))
    (hδsmall : ∀ᶠ n in atTop, 4 * δ n ≤ r / 2)
    {W : Vec3 × ℝ → Vec3} {W0 : Vec3 × ℝ → Vec3}
    {G0 : Vec3 × ℝ → Fin 3 → Fin 3 → ℝ}
    {H0 : Vec3 × ℝ → Fin 3 → Fin 3 → Fin 3 → ℝ}
    {T0 : Vec3 × ℝ → Fin 3 → ℝ}
    (hWmem : MemLp W0 (2 : ℝ≥0∞) (volume : Measure (Vec3 × ℝ)))
    (hGmem : MemLp G0 (2 : ℝ≥0∞) (volume : Measure (Vec3 × ℝ)))
    (hHmem : MemLp H0 (2 : ℝ≥0∞) (volume : Measure (Vec3 × ℝ)))
    (hTmem : MemLp T0 (2 : ℝ≥0∞) (volume : Measure (Vec3 × ℝ)))
    (family : CarlemanMollifiedFamilyState U K' W0 G0 H0 T0 δ hδpos hδtend
      hWmem hGmem hHmem hTmem)
    {σ τ ρ : Vec3 × ℝ → ℝ} (bounds : CompactWeightBounds volume K' ρ σ τ)
    (Vseq : ℕ → Vec3 × ℝ → Vec3)
    (hVseq : ∀ n z i, Vseq n z i =
      spaceTimeMollify (fun q => W q i) (δ n) (hδpos n) z)
    (hW0eq : W0 = W)
    (hδtests : ∀ n, 4 * δ n ≤ r / 2 →
      Vseq n ∈ spaceTimeTestFunction (V := Vec3) Ω I)
    (hBridge : ∀ n, 4 * δ n ≤ r / 2 → ∀ z, z ∈ K' →
      (∀ i j, spatialPartial (fun q : ParabolicPoint => Vseq n q i) j z =
        family.Gseq n z (i, j)) ∧
      (∀ i j k, spatialSecondPartial (fun q : ParabolicPoint => Vseq n q i) j k z =
        spaceTimeMollify (fun q => H0 q i j k) (δ n) (hδpos n) z) ∧
      ∀ i, timePartial (fun q : ParabolicPoint => Vseq n q i) z =
        spaceTimeMollify (fun q => T0 q i) (δ n) (hδpos n) z)
    (hOperator : ∀ n, 4 * δ n ≤ r / 2 → ∀ z, z ∈ K' → ∀ i,
      (timePartial (fun q : ParabolicPoint => Vseq n q i) z +
        Finset.univ.sum (fun j : Fin 3 =>
          spatialSecondPartial (fun q : ParabolicPoint => Vseq n q i) j j z)) =
          family.Rseq n z i)
    (hVzero : ∀ n i, 4 * δ n ≤ r / 2 → ∀ {z}, z ∉ K' → Vseq n z i = 0)
    (hSpatialZero : ∀ n i j, 4 * δ n ≤ r / 2 → ∀ {z}, z ∉ K' →
      spatialPartial (fun q : ParabolicPoint => Vseq n q i) j z = 0)
    (hSecondZero : ∀ n i j k, 4 * δ n ≤ r / 2 → ∀ {z}, z ∉ K' →
      spatialSecondPartial (fun q : ParabolicPoint => Vseq n q i) j k z = 0)
    (hTimeZero : ∀ n i, 4 * δ n ≤ r / 2 → ∀ {z}, z ∉ K' →
      timePartial (fun q : ParabolicPoint => Vseq n q i) z = 0)
    {c : ℝ}
    (hSmooth : ∀ v : Vec3 × ℝ → Vec3,
      v ∈ spaceTimeTestFunction (V := Vec3) Ω I →
      (∫ z in U, σ z * vec3EuclideanNorm (v z) ^ 2 +
        τ z * spatialGradientSq v (spatialGradient v) z ∂volume) ≤
      c * (∫ z in U, ρ z * vec3EuclideanNorm (fun i =>
        timePartial (fun y => v y i) z +
          ∑ j, spatialSecondPartial (fun y => v y i) j j z) ^ 2 ∂volume)) :
    CarlemanMollificationSequenceState (μ := volume) (K := K')
      (mass := fun n z => σ z * ∑ i, family.Wseq n z i ^ 2)
      (gradient := fun n z => τ z * ∑ ij : Fin 3 × Fin 3, family.Gseq n z ij ^ 2)
      (residual := fun n z => ρ z * ∑ i, family.Rseq n z i ^ 2)
      (massLimit := fun z => σ z * ∑ i, W0 z i ^ 2)
      (gradientLimit := fun z => τ z * ∑ ij : Fin 3 × Fin 3, G0 z ij.1 ij.2 ^ 2)
      (residualLimit := fun z => ρ z * ∑ i, family.residualZeroExtend z i ^ 2) c := by
  let smoothLeft n z := σ z * vec3EuclideanNorm (Vseq n z) ^ 2 +
    τ z * spatialGradientSq (Vseq n) (spatialGradient (Vseq n)) z
  let smoothRight n z := ρ z * vec3EuclideanNorm (fun i =>
    timePartial (fun y => Vseq n y i) z +
      ∑ j, spatialSecondPartial (fun y => Vseq n y i) j j z) ^ 2
  let mass n z := σ z * ∑ i, family.Wseq n z i ^ 2
  let gradient n z := τ z * ∑ ij : Fin 3 × Fin 3, family.Gseq n z ij ^ 2
  let residual n z := ρ z * ∑ i, family.Rseq n z i ^ 2
  have hMassLimit := weightedPiSq_tendsto bounds.sigmaNonneg bounds.sigmaAesm
    bounds.sigmaBoundAE (fun i => (family.Wcomponent i).restrict K')
    (fun n i => family.WseqMem n i)
    (fun i => by simpa only [family.WseqMollify] using family.Wconv i)
  have hGradientLimit := weightedPiSq_tendsto bounds.tauNonneg bounds.tauAesm
    bounds.tauBoundAE (fun ij => (family.Gcomponent ij.1 ij.2).restrict K')
    (fun n ij => family.GseqMem n ij)
    (by rintro ⟨i, j⟩; simpa only [family.GseqMollify] using family.Gconv i j)
  have hResidualLimit := weightedPiSq_tendsto bounds.rhoNonneg bounds.rhoAesm
    bounds.rhoBoundAE (fun i => (family.residualComponent i).restrict K')
    (fun n i => family.RseqMem n i)
    (fun i => by simpa only [family.RseqMollify] using family.Rconv i)
  have hPoint n (hn : 4 * δ n ≤ r / 2) z (hz : z ∈ K') := by
    have hb := hBridge n hn z hz
    have hp := carlemanMollifiedPointwise_decomposition
      (σ := σ) (τ := τ) (ρ := ρ) (V := Vseq n)
      (Wseq := fun i => family.Wseq n z i) (Gseq := fun ij => family.Gseq n z ij)
      (Rseq := fun i => family.Rseq n z i) z
      (fun i => by
        rw [hVseq n z i, family.WseqMollify n z i, hW0eq])
      (fun i j => hb.1 i j)
      (fun i => hOperator n hn z hz i)
    simpa only [smoothLeft, smoothRight, mass, gradient, residual] using hp
  have hLeftZero := mollifiedCarlemanIntegrands_zero_off
    (μ := volume) (Vseq := Vseq) (U := U) (K := K') (σ := σ) (τ := τ) (ρ := ρ)
    hVzero hSpatialZero hSecondZero hTimeZero
  have hMassInt n : Integrable (mass n) ((volume : Measure (Vec3 × ℝ)).restrict K') :=
    weightedPiSq_integrable bounds.sigmaAesm bounds.sigmaBoundAE
      (fun i => family.WseqMem n i)
  have hGradientInt n : Integrable (gradient n) ((volume : Measure (Vec3 × ℝ)).restrict K') :=
    weightedPiSq_integrable bounds.tauAesm bounds.tauBoundAE
      (fun ij => family.GseqMem n ij)
  have hstate := carlemanMollification_limit_state
    (μ := volume) (U := U) (K := K') hUmeas hK'meas hK'U
    (mass := mass) (gradient := gradient) (residual := residual)
    (smoothLeft := smoothLeft) (smoothRight := smoothRight)
    (massLimit := fun z => σ z * ∑ i, W0 z i ^ 2)
    (gradientLimit := fun z => τ z * ∑ ij : Fin 3 × Fin 3, G0 z ij.1 ij.2 ^ 2)
    (residualLimit := fun z => ρ z * ∑ i, family.residualZeroExtend z i ^ 2) (c := c)
    (good := fun n => 4 * δ n ≤ r / 2) hPoint hLeftZero.1 hLeftZero.2
    (by intro n hn
        simpa [smoothLeft, smoothRight] using hSmooth (Vseq n) (hδtests n hn))
    hMassLimit hGradientLimit hResidualLimit hδsmall hMassInt hGradientInt
  exact hstate.2.2


private theorem mollifiedResidualOperator_eq
    (δ : ℕ → ℝ) (hδpos : ∀ n, 0 < δ n) (r : ℝ) (K' : Set (Vec3 × ℝ))
    {Vseq : ℕ → Vec3 × ℝ → Vec3} {T0 : Vec3 × ℝ → Fin 3 → ℝ}
    {H0 : Vec3 × ℝ → Fin 3 → Fin 3 → Fin 3 → ℝ}
    {Rseq : ℕ → Vec3 × ℝ → Fin 3 → ℝ}
    (hBridge : ∀ n, 4 * δ n ≤ r / 2 → ∀ z, z ∈ K' →
      (∀ i j k, spatialSecondPartial (fun q : ParabolicPoint => Vseq n q i) j k z =
        spaceTimeMollify (fun q => H0 q i j k) (δ n) (hδpos n) z) ∧
      ∀ i, timePartial (fun q : ParabolicPoint => Vseq n q i) z =
        spaceTimeMollify (fun q => T0 q i) (δ n) (hδpos n) z)
    (hResidual : ∀ n i z,
      spaceTimeMollify (fun q => T0 q i) (δ n) (hδpos n) z +
        Finset.univ.sum (fun j : Fin 3 =>
          spaceTimeMollify (fun q => H0 q i j j) (δ n) (hδpos n) z) =
          Rseq n z i) :
    ∀ n, 4 * δ n ≤ r / 2 → ∀ z, z ∈ K' → ∀ i,
      (timePartial (fun q : ParabolicPoint => Vseq n q i) z +
        Finset.univ.sum (fun j : Fin 3 =>
          spatialSecondPartial (fun q : ParabolicPoint => Vseq n q i) j j z)) =
          Rseq n z i := by
  intro n hn z hz i
  have hb := hBridge n hn z hz
  rw [hb.2 i]
  have hsum : (∑ j, spatialSecondPartial
      (fun q : ParabolicPoint => Vseq n q i) j j z) =
      ∑ j, spaceTimeMollify (fun q => H0 q i j j) (δ n) (hδpos n) z := by
    apply Finset.sum_congr rfl
    intro j hj
    exact hb.1 i j j
  rw [hsum]
  exact hResidual n i z


private theorem mollifiedSpaceTimeDerivativeBridge
    {U : Set (Vec3 × ℝ)} {w : ParabolicPoint → Vec3}
    {Dw : ParabolicPoint → Fin 3 → Vec3}
    {D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3}
    {Dtw : ParabolicPoint → Vec3}
    {G0 : Vec3 × ℝ → Fin 3 → Fin 3 → ℝ}
    {H0 : Vec3 × ℝ → Fin 3 → Fin 3 → Fin 3 → ℝ}
    {T0 : Vec3 × ℝ → Fin 3 → ℝ}
    {δ : ℝ} (hδ : 0 < δ) (z : Vec3 × ℝ)
    (hraw : (∀ i j : Fin 3,
        spatialPartial (fun q : ParabolicPoint =>
          spaceTimeMollify (fun y : Vec3 × ℝ => w (parabolicHomeomorph.symm y) i)
            δ hδ q) j z =
          spaceTimeMollify (zeroExtendField U
            (fun y : Vec3 × ℝ => Dw (parabolicHomeomorph.symm y) i j)) δ hδ z) ∧
      (∀ i j k : Fin 3,
        spatialSecondPartial (fun q : ParabolicPoint =>
          spaceTimeMollify (fun y : Vec3 × ℝ => w (parabolicHomeomorph.symm y) i)
            δ hδ q) j k z =
          spaceTimeMollify (zeroExtendField U
            (fun y : Vec3 × ℝ => D2w (parabolicHomeomorph.symm y) i j k)) δ hδ z) ∧
      (∀ i : Fin 3,
        timePartial (fun q : ParabolicPoint =>
          spaceTimeMollify (fun y : Vec3 × ℝ => w (parabolicHomeomorph.symm y) i)
            δ hδ q) z =
          spaceTimeMollify (zeroExtendField U
            (fun y : Vec3 × ℝ => Dtw (parabolicHomeomorph.symm y) i)) δ hδ z))
    (hG0comp : ∀ i j : Fin 3,
      (fun q : Vec3 × ℝ => G0 q i j) =
        zeroExtendField U (fun y : Vec3 × ℝ => Dw (parabolicHomeomorph.symm y) i j))
    (hH0comp : ∀ i j k : Fin 3,
      (fun q : Vec3 × ℝ => H0 q i j k) =
        zeroExtendField U (fun y : Vec3 × ℝ => D2w (parabolicHomeomorph.symm y) i j k))
    (hT0comp : ∀ i : Fin 3,
      (fun q : Vec3 × ℝ => T0 q i) =
        zeroExtendField U (fun y : Vec3 × ℝ => Dtw (parabolicHomeomorph.symm y) i)) :
    (∀ i j : Fin 3,
      spatialPartial (fun q : ParabolicPoint =>
        spaceTimeMollify (fun y : Vec3 × ℝ => w (parabolicHomeomorph.symm y) i)
          δ hδ q) j z = spaceTimeMollify (fun q => G0 q i j) δ hδ z) ∧
    (∀ i j k : Fin 3,
      spatialSecondPartial (fun q : ParabolicPoint =>
        spaceTimeMollify (fun y : Vec3 × ℝ => w (parabolicHomeomorph.symm y) i)
          δ hδ q) j k z = spaceTimeMollify (fun q => H0 q i j k) δ hδ z) ∧
    (∀ i : Fin 3,
      timePartial (fun q : ParabolicPoint =>
        spaceTimeMollify (fun y : Vec3 × ℝ => w (parabolicHomeomorph.symm y) i)
          δ hδ q) z = spaceTimeMollify (fun q => T0 q i) δ hδ z) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    rw [hG0comp i j]
    exact hraw.1 i j
  · intro i j k
    rw [hH0comp i j k]
    exact hraw.2.1 i j k
  · intro i
    rw [hT0comp i]
    exact hraw.2.2 i


private theorem carlemanMollifiedDerivativeBridgeOnK'
    {Ω : Set Vec3} {I : Set ℝ} (hΩ : IsOpen Ω) (hI : IsOpen I)
    {w : ParabolicPoint → Vec3} {Dw : ParabolicPoint → Fin 3 → Vec3}
    {D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3}
    {Dtw : ParabolicPoint → Vec3}
    (hderiv : HasSpaceTimeWeakDerivs Ω I w Dw D2w Dtw)
    (htsupport : tsupport w ⊆ spaceTimeSet Ω I) (r : ℝ)
    (hr : 0 < r)
    (hthick : Metric.cthickening r (parabolicHomeomorph '' tsupport w) ⊆ Ω ×ˢ I)
    (U : Set (Vec3 × ℝ)) (hUeq : U = Ω ×ˢ I)
    (G0 : Vec3 × ℝ → Fin 3 → Fin 3 → ℝ)
    (H0 : Vec3 × ℝ → Fin 3 → Fin 3 → Fin 3 → ℝ)
    (T0 : Vec3 × ℝ → Fin 3 → ℝ)
    (hG0comp : ∀ i j : Fin 3,
      (fun q : Vec3 × ℝ => G0 q i j) =
        zeroExtendField U (fun y => Dw (parabolicHomeomorph.symm y) i j))
    (hH0comp : ∀ i j k : Fin 3,
      (fun q : Vec3 × ℝ => H0 q i j k) =
        zeroExtendField U (fun y => D2w (parabolicHomeomorph.symm y) i j k))
    (hT0comp : ∀ i : Fin 3,
      (fun q : Vec3 × ℝ => T0 q i) =
        zeroExtendField U (fun y => Dtw (parabolicHomeomorph.symm y) i))
    (δ : ℕ → ℝ) (hδpos : ∀ n, 0 < δ n)
    (K' : Set (Vec3 × ℝ))
    (hK'eq : K' = Metric.closedBall 0 (r / 4) +
      (parabolicHomeomorph '' tsupport w))
    (n : ℕ) (hn : 4 * δ n ≤ r / 2) (z : Vec3 × ℝ) (hz : z ∈ K') :
    (∀ i j : Fin 3,
      spatialPartial (fun q : ParabolicPoint =>
        spaceTimeMollifyPi (fun q => w (parabolicHomeomorph.symm q))
          (δ n) (hδpos n) q i) j z =
        spaceTimeMollify (fun q => G0 q i j) (δ n) (hδpos n) z) ∧
    (∀ i j k : Fin 3,
      spatialSecondPartial (fun q : ParabolicPoint =>
        spaceTimeMollifyPi (fun q => w (parabolicHomeomorph.symm q))
          (δ n) (hδpos n) q i) j k z =
        spaceTimeMollify (fun q => H0 q i j k) (δ n) (hδpos n) z) ∧
    (∀ i : Fin 3,
      timePartial (fun q : ParabolicPoint =>
        spaceTimeMollifyPi (fun q => w (parabolicHomeomorph.symm q))
          (δ n) (hδpos n) q i) z =
        spaceTimeMollify (fun q => T0 q i) (δ n) (hδpos n) z) := by
  have hz' : z ∈ Metric.closedBall (0 : Vec3 × ℝ) (r / 4) +
      (parabolicHomeomorph '' tsupport w) := by simpa only [hK'eq] using hz
  have hrawRaw := spaceTimeMollify_compactSupport_weakDerivs
    hΩ hI hderiv htsupport hr hthick (hδpos n) hn hz'
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    change spatialPartial (fun q : ParabolicPoint =>
      spaceTimeMollify (fun y => w (parabolicHomeomorph.symm y) i)
        (δ n) (hδpos n) q) j z =
      spaceTimeMollify (fun q => G0 q i j) (δ n) (hδpos n) z
    rw [hG0comp i j]
    simpa [hUeq] using hrawRaw.1 i j
  · intro i j k
    change spatialSecondPartial (fun q : ParabolicPoint =>
      spaceTimeMollify (fun y => w (parabolicHomeomorph.symm y) i)
        (δ n) (hδpos n) q) j k z =
      spaceTimeMollify (fun q => H0 q i j k) (δ n) (hδpos n) z
    rw [hH0comp i j k]
    simpa [hUeq] using hrawRaw.2.1 i j k
  · intro i
    change timePartial (fun q : ParabolicPoint =>
      spaceTimeMollify (fun y => w (parabolicHomeomorph.symm y) i)
        (δ n) (hδpos n) q) z =
      spaceTimeMollify (fun q => T0 q i) (δ n) (hδpos n) z
    rw [hT0comp i]
    simpa [hUeq] using hrawRaw.2.2 i



private theorem weakDerivativeData_zero_off_superset
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {U K K' : Set X}
    {G : X → Fin 3 → Fin 3 → ℝ} {H : X → Fin 3 → Fin 3 → Fin 3 → ℝ}
    {T : X → Fin 3 → ℝ} (hKsub : K ⊆ K')
    (hGzero : ∀ i j, ∀ᵐ z ∂μ, z ∈ U → z ∉ K → G z i j = 0)
    (hHzero : ∀ i j k, ∀ᵐ z ∂μ, z ∈ U → z ∉ K → H z i j k = 0)
    (hTzero : ∀ i, ∀ᵐ z ∂μ, z ∈ U → z ∉ K → T z i = 0) :
    (∀ᵐ z ∂μ, ∀ i j, z ∈ U → z ∉ K' → G z i j = 0) ∧
    (∀ᵐ z ∂μ, ∀ i j k, z ∈ U → z ∉ K' → H z i j k = 0) ∧
    (∀ᵐ z ∂μ, ∀ i, z ∈ U → z ∉ K' → T z i = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · apply ae_all_iff.mpr
    intro i
    apply ae_all_iff.mpr
    intro j
    filter_upwards [hGzero i j] with z hz
    intro hzU hzK'
    exact hz hzU (fun hzK => hzK' (hKsub hzK))
  · apply ae_all_iff.mpr
    intro i
    apply ae_all_iff.mpr
    intro j
    apply ae_all_iff.mpr
    intro k
    filter_upwards [hHzero i j k] with z hz
    intro hzU hzK'
    exact hz hzU (fun hzK => hzK' (hKsub hzK))
  · apply ae_all_iff.mpr
    intro i
    filter_upwards [hTzero i] with z hz
    intro hzU hzK'
    exact hz hzU (fun hzK => hzK' (hKsub hzK))


private theorem spaceTimeWeakDerivativeData_zero_off_support
    {Ω : Set Vec3} {I : Set ℝ} {w : ParabolicPoint → Vec3}
    {Dw : ParabolicPoint → Fin 3 → Vec3}
    {D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3} {Dtw : ParabolicPoint → Vec3}
    (hΩ : IsOpen Ω) (hI : IsOpen I)
    (hderiv : HasSpaceTimeWeakDerivs Ω I w Dw D2w Dtw)
    (hcompact : HasCompactSupport w) (htsupport : tsupport w ⊆ spaceTimeSet Ω I)
    {U K : Set (Vec3 × ℝ)} (hU : U = Ω ×ˢ I)
    (hK : K = parabolicHomeomorph '' tsupport w)
    {G : Vec3 × ℝ → Fin 3 → Fin 3 → ℝ}
    {H : Vec3 × ℝ → Fin 3 → Fin 3 → Fin 3 → ℝ}
    {T : Vec3 × ℝ → Fin 3 → ℝ}
    (hG : ∀ z i j, G z i j = Dw (parabolicHomeomorph.symm z) i j)
    (hH : ∀ z i j k, H z i j k = D2w (parabolicHomeomorph.symm z) i j k)
    (hT : ∀ z i, T z i = Dtw (parabolicHomeomorph.symm z) i) :
    (∀ i j, ∀ᵐ z ∂(volume : Measure (Vec3 × ℝ)),
      z ∈ U → z ∉ K → G z i j = 0) ∧
    (∀ i j k, ∀ᵐ z ∂(volume : Measure (Vec3 × ℝ)),
      z ∈ U → z ∉ K → H z i j k = 0) ∧
    (∀ i, ∀ᵐ z ∂(volume : Measure (Vec3 × ℝ)),
      z ∈ U → z ∉ K → T z i = 0) := by
  have hraw := spaceTimeWeakDerivs_ae_zero_off_tsupport hΩ hI hderiv hcompact htsupport
  refine ⟨?_, ⟨?_, ?_⟩⟩
  · intro i j
    filter_upwards [hraw.1 i j] with z hz
    intro hzU hzK
    rw [hG z i j]
    exact hz (by simpa [hU] using hzU) (by simpa [hK] using hzK)
  · intro i j k
    filter_upwards [hraw.2.1 i j k] with z hz
    intro hzU hzK
    rw [hH z i j k]
    exact hz (by simpa [hU] using hzU) (by simpa [hK] using hzK)
  · intro i
    filter_upwards [hraw.2.2 i] with z hz
    intro hzU hzK
    rw [hT z i]
    exact hz (by simpa [hU] using hzU) (by simpa [hK] using hzK)

private theorem weightedDerivativeIntegrands_zero_off
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {U K : Set X} {τ ρ : X → ℝ}
    {G : X → Fin 3 → Fin 3 → ℝ} {T : X → Fin 3 → ℝ}
    {H : X → Fin 3 → Fin 3 → Fin 3 → ℝ}
    (hGzero : ∀ᵐ z ∂μ, ∀ i j : Fin 3, z ∈ U → z ∉ K → G z i j = 0)
    (hTzero : ∀ᵐ z ∂μ, ∀ i : Fin 3, z ∈ U → z ∉ K → T z i = 0)
    (hHzero : ∀ᵐ z ∂μ, ∀ i j k : Fin 3, z ∈ U → z ∉ K → H z i j k = 0) :
    (∀ᵐ z ∂μ, z ∈ U → z ∉ K → τ z * ∑ i, ∑ j, G z i j ^ 2 = 0) ∧
    (∀ᵐ z ∂μ, z ∈ U → z ∉ K →
      ρ z * vec3EuclideanNorm (fun i => T z i + ∑ j, H z i j j) ^ 2 = 0) := by
  constructor
  · filter_upwards [hGzero] with z hg
    intro hzU hzK
    have hsum : (∑ i, ∑ j, G z i j ^ 2) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      apply Finset.sum_eq_zero
      intro j hj
      rw [hg i j hzU hzK]
      simp
    rw [hsum]
    simp
  · filter_upwards [hTzero, hHzero] with z ht hh
    intro hzU hzK
    have hraw (i : Fin 3) : T z i + ∑ j, H z i j j = 0 := by
      have hsum : (∑ j, H z i j j) = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        exact hh i j j hzU hzK
      rw [ht i hzU hzK, hsum]
      simp
    have hvec : (fun i : Fin 3 => T z i + ∑ j, H z i j j) = 0 := funext hraw
    rw [hvec]
    simp [vec3EuclideanNorm]


private theorem weightedWeakIntegrals_identify
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {K : Set X}
    (hKmeas : MeasurableSet K) {σ τ ρ : X → ℝ}
    {W W0 : X → Fin 3 → ℝ} {G G0 : X → Fin 3 → Fin 3 → ℝ}
    {R R0 : X → Fin 3 → ℝ}
    (hW : ∀ z ∈ K, ∀ i, W0 z i = W z i)
    (hG : ∀ z ∈ K, ∀ i j, G0 z i j = G z i j)
    (hR : ∀ z ∈ K, ∀ i, R0 z i = R z i) :
    WeightedWeakIntegralIdentifications μ K σ τ ρ W W0 G G0 R R0 := by
  have hMassAE : (fun z => σ z * vec3EuclideanNorm (W z) ^ 2) =ᵐ[μ.restrict K]
      (fun z => σ z * ∑ i, W0 z i ^ 2) := by
    filter_upwards [ae_restrict_mem hKmeas] with z hz
    rw [vec3EuclideanNorm_sq]
    simp [hW z hz]
  have hGradientAE : (fun z => τ z * ∑ i, ∑ j, G z i j ^ 2) =ᵐ[μ.restrict K]
      (fun z => τ z * ∑ ij : Fin 3 × Fin 3, G0 z ij.1 ij.2 ^ 2) := by
    filter_upwards [ae_restrict_mem hKmeas] with z hz
    calc
      τ z * ∑ i, ∑ j, G z i j ^ 2 = τ z * ∑ i, ∑ j, G0 z i j ^ 2 := by
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        rw [← hG z hz i j]
      _ = τ z * ∑ ij : Fin 3 × Fin 3, G0 z ij.1 ij.2 ^ 2 := by
        rw [fin3_double_sum_eq_product]
  have hResidualAE : (fun z => ρ z * vec3EuclideanNorm (R z) ^ 2) =ᵐ[μ.restrict K]
      (fun z => ρ z * ∑ i, R0 z i ^ 2) := by
    filter_upwards [ae_restrict_mem hKmeas] with z hz
    rw [vec3EuclideanNorm_sq]
    simp [hR z hz]
  exact ⟨hMassAE, hGradientAE, hResidualAE,
    integral_congr_ae hMassAE, integral_congr_ae hGradientAE,
    integral_congr_ae hResidualAE⟩


private theorem carleman_integral_bound_passes_to_limit
    {left right : ℕ → ℝ} {leftLimit rightLimit c : ℝ}
    (hleft : Tendsto left atTop (nhds leftLimit))
    (hright : Tendsto right atTop (nhds rightLimit))
    (hbound : ∀ᶠ n in atTop, left n ≤ c * right n) :
    leftLimit ≤ c * rightLimit :=
  le_of_tendsto_of_tendsto hleft (hright.const_mul c) hbound


private theorem weakCarleman_limit_integral_passage
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {U K : Set X}
    (hUmeas : MeasurableSet U) (hKmeas : MeasurableSet K) (hKsubU : K ⊆ U)
    {weakMass weakGradient weakResidual massTarget gradientTarget residualTarget : X → ℝ}
    {c : ℝ}
    (hmassAE : weakMass =ᵐ[μ.restrict K] massTarget)
    (hgradientAE : weakGradient =ᵐ[μ.restrict K] gradientTarget)
    (hmassInt : Integrable massTarget (μ.restrict K))
    (hgradientInt : Integrable gradientTarget (μ.restrict K))
    (hmassZero : ∀ᵐ z ∂μ, z ∈ U → z ∉ K → weakMass z = 0)
    (hgradientZero : ∀ᵐ z ∂μ, z ∈ U → z ∉ K → weakGradient z = 0)
    (hmassTarget : (∫ z in K, weakMass z ∂μ) = ∫ z in K, massTarget z ∂μ)
    (hgradientTarget : (∫ z in K, weakGradient z ∂μ) =
      ∫ z in K, gradientTarget z ∂μ)
    (hresidualTarget : (∫ z in U, weakResidual z ∂μ) =
      ∫ z in K, residualTarget z ∂μ)
    (hlimit : (∫ z in K, massTarget z ∂μ) +
      (∫ z in K, gradientTarget z ∂μ) ≤ c * (∫ z in K, residualTarget z ∂μ)) :
    (∫ z in U, weakMass z + weakGradient z ∂μ) ≤
      c * (∫ z in U, weakResidual z ∂μ) := by
  have hmassInt' : Integrable weakMass (μ.restrict K) := hmassInt.congr hmassAE.symm
  have hgradientInt' : Integrable weakGradient (μ.restrict K) :=
    hgradientInt.congr hgradientAE.symm
  have hleftZero : ∀ᵐ z ∂μ, z ∈ U → z ∉ K → weakMass z + weakGradient z = 0 := by
    filter_upwards [hmassZero, hgradientZero] with z hm hg
    intro hzU hzK
    rw [hm hzU hzK, hg hzU hzK]
    ring
  have hleft : (∫ z in U, weakMass z + weakGradient z ∂μ) =
      (∫ z in K, weakMass z ∂μ) + (∫ z in K, weakGradient z ∂μ) := by
    rw [setIntegral_eq_of_zero_off hUmeas hKmeas hKsubU hleftZero]
    exact integral_add hmassInt' hgradientInt'
  calc
    (∫ z in U, weakMass z + weakGradient z ∂μ) =
        (∫ z in K, weakMass z ∂μ) + (∫ z in K, weakGradient z ∂μ) := hleft
    _ = (∫ z in K, massTarget z ∂μ) + (∫ z in K, gradientTarget z ∂μ) := by
      rw [hmassTarget, hgradientTarget]
    _ ≤ c * (∫ z in K, residualTarget z ∂μ) := hlimit
    _ = c * (∫ z in U, weakResidual z ∂μ) :=
      congrArg (fun x : ℝ => c * x) hresidualTarget.symm


private theorem weakCarlemanIntegralPackage_passes_to_limit
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {U K : Set X}
    (hUmeas : MeasurableSet U) (hKmeas : MeasurableSet K) (hKsubU : K ⊆ U)
    {σ τ ρ : X → ℝ} {W : X → Fin 3 → ℝ} {W0 : X → Fin 3 → ℝ}
    {G G0 : X → Fin 3 → Fin 3 → ℝ} {R R0 : X → Fin 3 → ℝ} {c : ℝ}
    (package : WeakCarlemanIntegralPackage μ U K σ τ ρ W W0 G G0 R R0)
    (hlimit : (∫ z in K, σ z * ∑ i, W0 z i ^ 2 ∂μ) +
      ∫ z in K, τ z * ∑ ij : Fin 3 × Fin 3, G0 z ij.1 ij.2 ^ 2 ∂μ ≤
      c * (∫ z in K, ρ z * ∑ i, R0 z i ^ 2 ∂μ)) :
    (∫ z in U, σ z * vec3EuclideanNorm (W z) ^ 2 +
      τ z * ∑ i, ∑ j, G z i j ^ 2 ∂μ) ≤
      c * (∫ z in U, ρ z * vec3EuclideanNorm (R z) ^ 2 ∂μ) := by
  exact weakCarleman_limit_integral_passage hUmeas hKmeas hKsubU
    (weakMass := fun z => σ z * vec3EuclideanNorm (W z) ^ 2)
    (weakGradient := fun z => τ z * ∑ i, ∑ j, G z i j ^ 2)
    (weakResidual := fun z => ρ z * vec3EuclideanNorm (R z) ^ 2)
    (massTarget := fun z => σ z * ∑ i, W0 z i ^ 2)
    (gradientTarget := fun z => τ z * ∑ ij : Fin 3 × Fin 3, G0 z ij.1 ij.2 ^ 2)
    (residualTarget := fun z => ρ z * ∑ i, R0 z i ^ 2) (c := c)
    package.massAE package.gradientAE package.massIntegrable package.gradientIntegrable
    package.massZeroOff package.gradientZeroOff
    package.massTarget package.gradientTarget package.residualTarget hlimit


private theorem weakCarlemanIntegralPackage_of_components
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X] {μ : Measure X} {U Kbase K : Set X}
    (hUmeas : MeasurableSet U) (hKmeas : MeasurableSet K) (hKsubU : K ⊆ U)
    (hKbaseSub : Kbase ⊆ K) {σ τ ρ : X → ℝ}
    {W : X → Fin 3 → ℝ} {W0 : X → Fin 3 → ℝ}
    {G : X → Fin 3 → Fin 3 → ℝ} {G0 : X → Fin 3 → Fin 3 → ℝ}
    {H : X → Fin 3 → Fin 3 → Fin 3 → ℝ} {T : X → Fin 3 → ℝ}
    {R R0 : X → Fin 3 → ℝ}
    {Cσ Cτ : ℝ}
    (hWsupport : ∀ i, tsupport (fun z => W z i) ⊆ Kbase)
    (hGzero : ∀ᵐ z ∂μ, ∀ i j, z ∈ U → z ∉ K → G z i j = 0)
    (hTzero : ∀ᵐ z ∂μ, ∀ i, z ∈ U → z ∉ K → T z i = 0)
    (hHzero : ∀ᵐ z ∂μ, ∀ i j k, z ∈ U → z ∉ K → H z i j k = 0)
    (hσaesm : AEStronglyMeasurable σ (μ.restrict K))
    (hσbound : ∀ᵐ z ∂(μ.restrict K), ‖σ z‖ ≤ Cσ)
    (hτaesm : AEStronglyMeasurable τ (μ.restrict K))
    (hτbound : ∀ᵐ z ∂(μ.restrict K), ‖τ z‖ ≤ Cτ)
    (hWcomponent : ∀ i, MemLp (fun z => W0 z i) (2 : ℝ≥0∞) μ)
    (hGcomponent : ∀ i j, MemLp (fun z => G0 z i j) (2 : ℝ≥0∞) μ)
    (hWpoint : ∀ z ∈ K, ∀ i, W0 z i = W z i)
    (hGpoint : ∀ z ∈ K, ∀ i j, G0 z i j = G z i j)
    (hRpoint : ∀ z ∈ K, ∀ i, R0 z i = R z i)
    (hRdef : ∀ z i, R z i = T z i + ∑ j, H z i j j) :
    WeakCarlemanIntegralPackage μ U K σ τ ρ W W0 G G0 R R0 := by
  have hmassInt := weightedPiSq_integrable hσaesm hσbound
    (fun i => (hWcomponent i).restrict K)
  have hgradientInt := weightedPiSq_integrable hτaesm hτbound
    (fun (ij : Fin 3 × Fin 3) => (hGcomponent ij.1 ij.2).restrict K)
  have hmassZero : ∀ᵐ z ∂μ, z ∈ U → z ∉ K →
      σ z * vec3EuclideanNorm (W z) ^ 2 = 0 := by
    filter_upwards [] with z
    intro hzU hzK
    have hzBase : z ∉ Kbase := fun hz => hzK (hKbaseSub hz)
    have hWz : W z = 0 := funext fun i => by
      have hnot : z ∉ Function.support (fun q : X => W q i) := fun hz =>
        hzBase (hWsupport i (subset_tsupport _ hz))
      simpa [Function.mem_support] using hnot
    rw [hWz]
    simp [vec3EuclideanNorm]
  have hderivZero := weightedDerivativeIntegrands_zero_off (τ := τ) (ρ := ρ)
    hGzero hTzero hHzero
  have hIds := weightedWeakIntegrals_identify (μ := μ) (K := K)
    (σ := σ) (τ := τ) (ρ := ρ)
    hKmeas hWpoint hGpoint hRpoint
  have hresidualZero : ∀ᵐ z ∂μ, z ∈ U → z ∉ K →
      ρ z * vec3EuclideanNorm (R z) ^ 2 = 0 := by
    simpa only [← hRdef] using hderivZero.2
  have hresidualTarget : (∫ z in U, ρ z * vec3EuclideanNorm (R z) ^ 2 ∂μ) =
      ∫ z in K, ρ z * ∑ i, R0 z i ^ 2 ∂μ := by
    rw [setIntegral_eq_of_zero_off hUmeas hKmeas hKsubU hresidualZero]
    exact hIds.residualIntegral
  refine ⟨hmassInt, hgradientInt, hIds.massAE, hIds.gradientAE,
    hmassZero, ?_, hresidualZero, hIds.massIntegral, hIds.gradientIntegral,
    hresidualTarget⟩
  simpa using hderivZero.1


theorem compactlySupportedSpaceTimeCarleman_of_smooth
    {Ω : Set Vec3} {I : Set ℝ} (hΩ : IsOpen Ω) (hI : IsOpen I)
    {w : ParabolicPoint → Vec3}
    {Dw : ParabolicPoint → Fin 3 → Vec3}
    {D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3}
    {Dtw : ParabolicPoint → Vec3}
    (hderiv : HasSpaceTimeWeakDerivs Ω I w Dw D2w Dtw)
    (hcompact : HasCompactSupport w)
    (htsupport : tsupport w ⊆ spaceTimeSet Ω I)
    (hL2 : (∫⁻ z in spaceTimeSet Ω I,
      ‖w z‖ₑ ^ (2 : ℝ) + ‖Dw z‖ₑ ^ (2 : ℝ) +
        ‖D2w z‖ₑ ^ (2 : ℝ) + ‖Dtw z‖ₑ ^ (2 : ℝ)) < ⊤)
    {ρ σ τ : Vec3 × ℝ → ℝ}
    (hρcont : ContinuousOn ρ (Ω ×ˢ I))
    (hσcont : ContinuousOn σ (Ω ×ˢ I))
    (hτcont : ContinuousOn τ (Ω ×ˢ I))
    {c : ℝ}
    (hSmooth : ∀ v : Vec3 × ℝ → Vec3,
      v ∈ spaceTimeTestFunction (V := Vec3) Ω I →
      (∫ z in Ω ×ˢ I,
        σ z * vec3EuclideanNorm (v z) ^ 2 +
          τ z * spatialGradientSq v (spatialGradient v) z
          ∂(volume : Measure (Vec3 × ℝ))) ≤
        c * (∫ z in Ω ×ˢ I,
          ρ z * vec3EuclideanNorm (fun i =>
            timePartial (fun y => v y i) z +
              ∑ j, spatialSecondPartial (fun y => v y i) j j z) ^ 2
            ∂(volume : Measure (Vec3 × ℝ)))) :
    (∫ z in Ω ×ˢ I,
      σ z * vec3EuclideanNorm (w (parabolicHomeomorph.symm z)) ^ 2 +
        τ z * ∑ i, ∑ j, (Dw (parabolicHomeomorph.symm z) i j) ^ 2
        ∂(volume : Measure (Vec3 × ℝ))) ≤
      c * (∫ z in Ω ×ˢ I,
        ρ z * vec3EuclideanNorm (fun i =>
          Dtw (parabolicHomeomorph.symm z) i +
            ∑ j, D2w (parabolicHomeomorph.symm z) i j j) ^ 2
          ∂(volume : Measure (Vec3 × ℝ))) := by
  let U : Set (Vec3 × ℝ) := Ω ×ˢ I
  let K : Set (Vec3 × ℝ) := parabolicHomeomorph '' tsupport w
  let W : Vec3 × ℝ → Vec3 := fun z => w (parabolicHomeomorph.symm z)
  let G : Vec3 × ℝ → Fin 3 → Fin 3 → ℝ :=
    fun z i j => Dw (parabolicHomeomorph.symm z) i j
  let H : Vec3 × ℝ → Fin 3 → Fin 3 → Fin 3 → ℝ :=
    fun z i j k => D2w (parabolicHomeomorph.symm z) i j k
  let T : Vec3 × ℝ → Fin 3 → ℝ :=
    fun z i => Dtw (parabolicHomeomorph.symm z) i
  let W0 : Vec3 × ℝ → Vec3 := zeroExtendField U W
  let G0 : Vec3 × ℝ → Fin 3 → Fin 3 → ℝ := zeroExtendField U G
  let H0 : Vec3 × ℝ → Fin 3 → Fin 3 → Fin 3 → ℝ := zeroExtendField U H
  let T0 : Vec3 × ℝ → Fin 3 → ℝ := zeroExtendField U T
  have hUopen : IsOpen U := by exact hΩ.prod hI
  have hUmeas : MeasurableSet U := hUopen.measurableSet
  let setup := carlemanMollificationSetup_of_compactSupport
    hΩ hI hderiv hcompact htsupport hL2
  let r := setup.radius
  have hr : 0 < r := by simpa [r] using setup.radiusPos
  have hthick : Metric.cthickening r K ⊆ U := by
    simpa [U, K, r] using setup.thickeningSubset
  let K' : Set (Vec3 × ℝ) := setup.thickenedSupport
  have hKcompact : IsCompact K := setup.supportCompact
  have hKU : K ⊆ U := by simpa [U, K] using setup.supportSubset
  have hK'eq : K' = Metric.closedBall 0 (r / 4) + K := by
    simpa [K', r, K] using setup.thickenedSupportEq
  have hK'compact : IsCompact K' := setup.thickenedSupportCompact
  have hK'U : K' ⊆ U := by simpa [K', U] using setup.thickenedSupportSubset
  have hK'meas : MeasurableSet K' := setup.thickenedSupportMeas
  have hL2data := setup.l2Data
  have hWtsupportK : tsupport W ⊆ K := by
    simpa [W, K] using setup.pulledFieldSupport
  have hWrawSupport : tsupport W ⊆ U := by
    simpa [W, U] using setup.pulledFieldRawSupport
  have hWrawEq : zeroExtendField U W = W := by
    simpa [W, U] using setup.pulledFieldRawEq
  have hWmem : MemLp W (2 : ℝ≥0∞) (volume : Measure (Vec3 × ℝ)) := by
    simpa [W] using setup.pulledFieldMemLp
  have hWloc : ∀ i : Fin 3,
      LocallyIntegrable (fun z : Vec3 × ℝ => W z i) (volume : Measure (Vec3 × ℝ)) := by
    simpa [W] using setup.pulledFieldLocallyIntegrable
  have hWcompact : HasCompactSupport W := by
    simpa [W] using setup.pulledFieldCompactSupport
  let δ := setup.delta
  have hδtend : Tendsto δ atTop (nhds 0) := setup.deltaTendsto
  have hδpos : ∀ n, 0 < δ n := setup.deltaPos
  have hδtests : ∀ n, spaceTimeMollifyPi W (δ n) (hδpos n) ∈
      spaceTimeTestFunction (V := Vec3) Ω I := by
    simpa [δ, W] using setup.deltaTests
  have hδsmall : ∀ᶠ n in atTop, 4 * δ n ≤ r / 2 := by
    simpa [δ, r] using setup.deltaSmall
  have hKsubK' : K ⊆ K' := by simpa [K, K'] using setup.supportSubsetThickened
  have hW0mem : MemLp W0 (2 : ℝ≥0∞) (volume : Measure (Vec3 × ℝ)) := hL2data.1
  have hGmem : MemLp G0 (2 : ℝ≥0∞) (volume : Measure (Vec3 × ℝ)) := hL2data.2.1
  have hHmem : MemLp H0 (2 : ℝ≥0∞) (volume : Measure (Vec3 × ℝ)) := hL2data.2.2.1
  have hTmem : MemLp T0 (2 : ℝ≥0∞) (volume : Measure (Vec3 × ℝ)) := hL2data.2.2.2
  let familyState := carlemanMollifiedFamilyState_of_l2 U K' W0 G0 H0 T0 δ
    hδpos hδtend hW0mem hGmem hHmem hTmem
    (by intro z i hz; simp [T0, zeroExtendField, hz])
    (by intro z i j k hz; simp [H0, zeroExtendField, hz])
  let R0 := familyState.residualZeroExtend
  let Wseq := familyState.Wseq
  let Gseq := familyState.Gseq
  let Rseq := familyState.Rseq
  have hRsource := familyState.residualSource
  let weightBounds := compactWeightBounds_of_continuous
    (μ := volume) (K := K') (ρ := ρ) (σ := σ) (τ := τ)
    hK'compact hK'meas (hρcont.mono hK'U) (hσcont.mono hK'U)
    (hτcont.mono hK'U)
  let Cσ := weightBounds.sigmaBound
  let Cτ := weightBounds.tauBound
  have hσaesm := weightBounds.sigmaAesm
  have hτaesm := weightBounds.tauAesm
  have hσbound := weightBounds.sigmaBoundAE
  have hτbound := weightBounds.tauBoundAE
  let Vseq : ℕ → Vec3 × ℝ → Vec3 := fun n =>
    spaceTimeMollifyPi W (δ n) (hδpos n)
  have hMollifiedZeros := mollified_test_derivatives_zero_off
    (W := W) (K := K) (K' := K')
    (fun i => product_component_tsupport_subset hcompact i)
    hKcompact (r := r) δ hδpos hK'eq
  have hVzero := hMollifiedZeros.1
  have hSpatialZero := hMollifiedZeros.2.1
  have hSecondZero := hMollifiedZeros.2.2.1
  have hTimeZero := hMollifiedZeros.2.2.2
  have hoperatorMollify := familyState.residualMollify
  have hBridge (n : ℕ) (hn : 4 * δ n ≤ r / 2) (z : Vec3 × ℝ)
      (hz : z ∈ K') :
      (∀ i j, spatialPartial (fun q : ParabolicPoint => Vseq n q i) j z =
        familyState.Gseq n z (i, j)) ∧
      (∀ i j k, spatialSecondPartial (fun q : ParabolicPoint => Vseq n q i) j k z =
        spaceTimeMollify (fun q => H0 q i j k) (δ n) (hδpos n) z) ∧
      (∀ i, timePartial (fun q : ParabolicPoint => Vseq n q i) z =
        spaceTimeMollify (fun q => T0 q i) (δ n) (hδpos n) z) := by
    have hraw := carlemanMollifiedDerivativeBridgeOnK'
      hΩ hI hderiv htsupport r hr hthick U (by rfl) G0 H0 T0
      (by intro i j; funext q; by_cases hq : q ∈ U <;>
        simp [G0, G, zeroExtendField, U, hq])
      (by intro i j k; funext q; by_cases hq : q ∈ U <;>
        simp [H0, H, zeroExtendField, U, hq])
      (by intro i; funext q; by_cases hq : q ∈ U <;>
        simp [T0, T, zeroExtendField, U, hq]) δ hδpos K'
      hK'eq n hn z hz
    refine ⟨?_, ⟨?_, ?_⟩⟩
    · intro i j
      simpa [Vseq, W] using (hraw.1 i j).trans (familyState.GseqMollify n z i j).symm
    · intro i j k
      simpa [Vseq, W] using hraw.2.1 i j k
    · intro i
      simpa [Vseq, W] using hraw.2.2 i
  have hOperator := mollifiedResidualOperator_eq (Vseq := Vseq) (T0 := T0)
    (H0 := H0) (Rseq := Rseq) δ hδpos r K'
    (by intro n hn z hz; exact ⟨(hBridge n hn z hz).2.1, (hBridge n hn z hz).2.2⟩)
    (by intro n i z
        change spaceTimeMollify (fun q => T0 q i) (δ n) (hδpos n) z +
          ∑ j, spaceTimeMollify (fun q => H0 q i j j) (δ n) (hδpos n) z =
            familyState.Rseq n z i
        rw [familyState.RseqMollify n z i]
        exact (congrFun (hoperatorMollify n i) z).symm)
  let weakMassIntegrand (z : Vec3 × ℝ) : ℝ :=
    σ z * vec3EuclideanNorm (w (parabolicHomeomorph.symm z)) ^ 2
  let weakGradientIntegrand (z : Vec3 × ℝ) : ℝ :=
    τ z * ∑ i, ∑ j, Dw (parabolicHomeomorph.symm z) i j ^ 2
  let weakResidualIntegrand (z : Vec3 × ℝ) : ℝ :=
    ρ z * vec3EuclideanNorm (fun i =>
      Dtw (parabolicHomeomorph.symm z) i +
        ∑ j, D2w (parabolicHomeomorph.symm z) i j j) ^ 2
  let weightedState := carlemanWeightedMollificationState
    hUmeas hK'meas hK'U r δ hδpos hδtend hδsmall
    hW0mem hGmem hHmem hTmem familyState weightBounds Vseq
    (by
      intro n z i
      change spaceTimeMollify (fun q => W q i) (δ n) (hδpos n) z = _
      rfl)
    (by
      change zeroExtendField U W = W
      exact hWrawEq)
    (by intro n hn; exact hδtests n)
    (by intro n hn z hz; exact hBridge n hn z hz)
    (by intro n hn z hz i; exact hOperator n hn z hz i)
    (by intro n i hn z; exact hVzero n i hn)
    (by intro n i j hn z; exact hSpatialZero n i j hn)
    (by intro n i j k hn z; exact hSecondZero n i j k hn)
    (by intro n i hn z; exact hTimeZero n i hn)
    hSmooth
  have hleftLimit := weightedState.leftLimit
  have hrightLimit := weightedState.rightLimit
  have hseqIneq := weightedState.eventualInequality
  have hR0target (z : Vec3 × ℝ) (hz : z ∈ K') (i : Fin 3) :
      R0 z i = Dtw z i + ∑ j, D2w z i j j := by
    have hzU := hK'U hz
    simpa [T0, T, H0, H, zeroExtendField, U, hzU] using congrFun (hRsource i) z
  have hWeakBase := spaceTimeWeakDerivativeData_zero_off_support
    hΩ hI hderiv hcompact htsupport (by rfl) (by rfl)
    (by intro z i j; rfl) (by intro z i j k; rfl) (by intro z i; rfl)
  have hWeakZeros := weakDerivativeData_zero_off_superset hKsubK'
    hWeakBase.1 hWeakBase.2.1 hWeakBase.2.2
  have hWeakPackage := weakCarlemanIntegralPackage_of_components
    (μ := volume) (U := U) (Kbase := K) (K := K') hUmeas hK'meas hK'U hKsubK'
    (σ := σ) (τ := τ) (ρ := ρ) (W := W) (W0 := W0) (G := G) (G0 := G0)
    (H := H) (T := T) (R := fun z i => Dtw (parabolicHomeomorph.symm z) i +
      ∑ j, D2w (parabolicHomeomorph.symm z) i j j) (R0 := R0)
    (Cσ := Cσ) (Cτ := Cτ) (fun i => product_component_tsupport_subset hcompact i)
    hWeakZeros.1 hWeakZeros.2.2 hWeakZeros.2.1 hσaesm hσbound hτaesm hτbound
    (fun i => familyState.Wcomponent i) (fun i j => familyState.Gcomponent i j)
    (fun z hz i => by
      have hzU := hK'U hz
      simp [W0, zeroExtendField, U, hzU])
    (fun z hz i j => by
      have hzU := hK'U hz
      change zeroExtendField U G z i j = G z i j
      simp [zeroExtendField, U, hzU])
    (fun z hz i => by simpa [T, H] using hR0target z hz i)
    (by intro z i; rfl)
  have hfinal := carleman_integral_bound_passes_to_limit
    hleftLimit hrightLimit hseqIneq
  have hweakPass := weakCarlemanIntegralPackage_passes_to_limit
    hUmeas hK'meas hK'U hWeakPackage hfinal
  simpa [U, W, G, weakMassIntegrand, weakGradientIntegrand,
    weakResidualIntegrand] using hweakPass

end ESS
