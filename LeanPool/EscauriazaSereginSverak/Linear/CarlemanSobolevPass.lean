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

/-- A compactly supported space-time weak field inherits any weighted smooth Carleman inequality
whose coefficients are continuous on the product domain and bounded on compact subsets
(`lem:carleman-sobolev`). -/
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
  have hKcompact : IsCompact K := parabolicHomeomorph.isCompact_image.mpr hcompact.isCompact
  have hKU : K ⊆ U := by
    rintro z ⟨p, hp, rfl⟩
    exact htsupport hp
  obtain ⟨r, hr, hthick⟩ := hKcompact.exists_cthickening_subset_open hUopen hKU
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
  have hWsupport : tsupport W ⊆ U := hWrawSupport
  obtain ⟨δ, hδtend, hδtests⟩ :=
    exists_spaceTimeMollifyPi_testSequence hΩ hI hWcompact hWsupport hWloc
  have hδpos : ∀ n, 0 < δ n := fun n => (hδtests n).1
  have hδsmall : ∀ᶠ n in atTop, 4 * δ n ≤ r / 2 := by
    have hev : ∀ᶠ n in atTop, δ n < r / 8 :=
      hδtend.eventually (gt_mem_nhds (by positivity))
    filter_upwards [hev] with n hn
    nlinarith only [hn]
  have hweakZero := spaceTimeWeakDerivs_ae_zero_off_tsupport
    hΩ hI hderiv hcompact htsupport
  have hGmem : MemLp G0 (2 : ℝ≥0∞) (volume : Measure (Vec3 × ℝ)) := hL2data.2.1
  have hHmem : MemLp H0 (2 : ℝ≥0∞) (volume : Measure (Vec3 × ℝ)) := hL2data.2.2.1
  have hTmem : MemLp T0 (2 : ℝ≥0∞) (volume : Measure (Vec3 × ℝ)) := hL2data.2.2.2
  have hWcomponent (i : Fin 3) :
      MemLp (fun z : Vec3 × ℝ => W0 z i) (2 : ℝ≥0∞)
        (volume : Measure (Vec3 × ℝ)) := by
    simpa [W0, W] using memLp_pi_component hL2data.1 i
  have hGcomponent (i j : Fin 3) :
      MemLp (fun z : Vec3 × ℝ => G0 z i j) (2 : ℝ≥0∞)
        (volume : Measure (Vec3 × ℝ)) := by
    simpa [G0] using memLp_pi_component (memLp_pi_component hGmem i) j
  have hHcomponent (i j k : Fin 3) :
      MemLp (fun z : Vec3 × ℝ => H0 z i j k) (2 : ℝ≥0∞)
        (volume : Measure (Vec3 × ℝ)) := by
    simpa [H0] using
      memLp_pi_component (memLp_pi_component (memLp_pi_component hHmem i) j) k
  have hTcomponent (i : Fin 3) :
      MemLp (fun z : Vec3 × ℝ => T0 z i) (2 : ℝ≥0∞)
        (volume : Measure (Vec3 × ℝ)) := by
    simpa [T0] using memLp_pi_component hTmem i
  let R : Vec3 × ℝ → Fin 3 → ℝ := fun z i => T z i + ∑ j, H z i j j
  let R0 : Vec3 × ℝ → Fin 3 → ℝ := zeroExtendField U R
  let Wseq : ℕ → Vec3 × ℝ → Fin 3 → ℝ := fun n z i =>
    spaceTimeMollify (fun q => W0 q i) (δ n) (hδpos n) z
  let Gseq : ℕ → Vec3 × ℝ → Fin 3 × Fin 3 → ℝ := fun n z ij =>
    spaceTimeMollify (fun q => G0 q ij.1 ij.2) (δ n) (hδpos n) z
  let Rseq : ℕ → Vec3 × ℝ → Fin 3 → ℝ := fun n z i =>
    spaceTimeMollify (fun q => R0 q i) (δ n) (hδpos n) z
  have hRcomponent (i : Fin 3) :
      MemLp (fun z : Vec3 × ℝ => R0 z i) (2 : ℝ≥0∞)
        (volume : Measure (Vec3 × ℝ)) := by
    have hdiag : MemLp (fun z : Vec3 × ℝ => ∑ j, H0 z i j j)
        (2 : ℝ≥0∞) (volume : Measure (Vec3 × ℝ)) := by
      simpa only [Finset.univ_eq_attach] using
        memLp_finsetSum (Finset.univ : Finset (Fin 3)) (by
          intro j hj
          exact hHcomponent i j j)
    have hRrewrite : (fun z : Vec3 × ℝ => R0 z i) =
        (fun z => T0 z i + ∑ j, H0 z i j j) := by
      funext z
      by_cases hz : z ∈ U
      · simp [R0, R, T0, H0, zeroExtendField, hz]
      · simp [R0, R, T0, H0, zeroExtendField, hz]
    rw [hRrewrite]
    exact (hTcomponent i).add hdiag
  have hWconv (i : Fin 3) : Tendsto
      (fun n => eLpNorm
        (fun z => Wseq n z i - W0 z i) 2
        ((volume : Measure (Vec3 × ℝ)).restrict K')) atTop (nhds 0) := by
    simpa [Wseq] using tendsto_mollify_l2_restrict
      (hWcomponent i) hδtend hδpos K'
  have hGconv (i j : Fin 3) : Tendsto
      (fun n => eLpNorm
        (fun z => Gseq n z (i, j) - G0 z i j) 2
        ((volume : Measure (Vec3 × ℝ)).restrict K')) atTop (nhds 0) := by
    simpa [Gseq] using tendsto_mollify_l2_restrict
      (hGcomponent i j) hδtend hδpos K'
  have hRconv (i : Fin 3) : Tendsto
      (fun n => eLpNorm
        (fun z => Rseq n z i - R0 z i) 2
        ((volume : Measure (Vec3 × ℝ)).restrict K')) atTop (nhds 0) := by
    simpa [Rseq] using tendsto_mollify_l2_restrict
      (hRcomponent i) hδtend hδpos K'
  have hWseqMem (n : ℕ) (i : Fin 3) :
      MemLp (fun z => Wseq n z i) (2 : ℝ≥0∞)
        ((volume : Measure (Vec3 × ℝ)).restrict K') := by
    exact (spaceTimeMollify_memLp_of_memLp (hδpos n) (hWcomponent i)).restrict K'
  have hGseqMem (n : ℕ) (ij : Fin 3 × Fin 3) :
      MemLp (fun z => Gseq n z ij) (2 : ℝ≥0∞)
        ((volume : Measure (Vec3 × ℝ)).restrict K') := by
    exact (spaceTimeMollify_memLp_of_memLp (hδpos n)
      (hGcomponent ij.1 ij.2)).restrict K'
  have hRseqMem (n : ℕ) (i : Fin 3) :
      MemLp (fun z => Rseq n z i) (2 : ℝ≥0∞)
        ((volume : Measure (Vec3 × ℝ)).restrict K') := by
    exact (spaceTimeMollify_memLp_of_memLp (hδpos n) (hRcomponent i)).restrict K'
  have hρboundOn := hK'compact.exists_bound_of_continuousOn (hρcont.mono hK'U)
  have hσboundOn := hK'compact.exists_bound_of_continuousOn (hσcont.mono hK'U)
  have hτboundOn := hK'compact.exists_bound_of_continuousOn (hτcont.mono hK'U)
  let Cρ : ℝ := max hρboundOn.choose 0
  let Cσ : ℝ := max hσboundOn.choose 0
  let Cτ : ℝ := max hτboundOn.choose 0
  have hCρ : 0 ≤ Cρ := le_max_right _ _
  have hCσ : 0 ≤ Cσ := le_max_right _ _
  have hCτ : 0 ≤ Cτ := le_max_right _ _
  have hρaesm : AEStronglyMeasurable ρ
      ((volume : Measure (Vec3 × ℝ)).restrict K') :=
    (hρcont.mono hK'U).aestronglyMeasurable hK'meas
  have hσaesm : AEStronglyMeasurable σ
      ((volume : Measure (Vec3 × ℝ)).restrict K') :=
    (hσcont.mono hK'U).aestronglyMeasurable hK'meas
  have hτaesm : AEStronglyMeasurable τ
      ((volume : Measure (Vec3 × ℝ)).restrict K') :=
    (hτcont.mono hK'U).aestronglyMeasurable hK'meas
  have hρbound : ∀ᵐ z ∂((volume : Measure (Vec3 × ℝ)).restrict K'), ‖ρ z‖ ≤ Cρ := by
    filter_upwards [ae_restrict_mem hK'meas] with z hz
    exact (hρboundOn.choose_spec z hz).trans (le_max_left _ _)
  have hσbound : ∀ᵐ z ∂((volume : Measure (Vec3 × ℝ)).restrict K'), ‖σ z‖ ≤ Cσ := by
    filter_upwards [ae_restrict_mem hK'meas] with z hz
    exact (hσboundOn.choose_spec z hz).trans (le_max_left _ _)
  have hτbound : ∀ᵐ z ∂((volume : Measure (Vec3 × ℝ)).restrict K'), ‖τ z‖ ≤ Cτ := by
    filter_upwards [ae_restrict_mem hK'meas] with z hz
    exact (hτboundOn.choose_spec z hz).trans (le_max_left _ _)
  have hMassLimit := weightedPiSq_tendsto hCσ hσaesm hσbound
    (fun i => (hWcomponent i).restrict K')
    (fun n i => hWseqMem n i)
    (by intro i; exact hWconv i)
  have hGradLimit := weightedPiSq_tendsto hCτ hτaesm hτbound
    (fun ij => (hGcomponent ij.1 ij.2).restrict K')
    (fun n ij => hGseqMem n ij)
    (by rintro ⟨i, j⟩; exact hGconv i j)
  have hResidualLimit := weightedPiSq_tendsto hCρ hρaesm hρbound
    (fun i => (hRcomponent i).restrict K')
    (fun n i => hRseqMem n i)
    (by intro i; exact hRconv i)
  let Vseq : ℕ → Vec3 × ℝ → Vec3 := fun n =>
    spaceTimeMollifyPi W (δ n) (hδpos n)
  have hVcomponentSupport (n : ℕ) (i : Fin 3) (hn : 4 * δ n ≤ r / 2) :
      tsupport (fun z : Vec3 × ℝ => Vseq n z i) ⊆ K' := by
    have hn' : 8 * δ n ≤ r := by
      calc
        8 * δ n = 2 * (4 * δ n) := by ring
        _ ≤ 2 * (r / 2) := mul_le_mul_of_nonneg_left hn (by norm_num)
        _ = r := by ring
    have hδle : δ n ≤ r / 4 := by
      apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 4)).2
      calc
        δ n * 4 ≤ 8 * δ n := by nlinarith only [hδpos n]
        _ ≤ r := hn'
    have hsupport : Function.support (fun z : Vec3 × ℝ => Vseq n z i) ⊆
        Metric.ball (0 : Vec3 × ℝ) (δ n) +
          Function.support (fun z : Vec3 × ℝ => W z i) := by
      simpa [Vseq, spaceTimeMollifyPi] using
        (spaceTimeMollify_support_subset (f := fun z : Vec3 × ℝ => W z i) (hδpos n))
    have hsum : Function.support (fun z : Vec3 × ℝ => Vseq n z i) ⊆ K' := by
      intro z hz
      rcases hsupport hz with ⟨u, hu, v, hv, rfl⟩
      refine ⟨u, ?_, v, ?_, rfl⟩
      · rw [Metric.mem_closedBall]
        exact (Metric.mem_ball.mp hu).le.trans hδle
      · exact product_component_tsupport_subset hcompact i (subset_tsupport _ hv)
    exact closure_minimal hsum hK'compact.isClosed
  have hSpatialSupport (n : ℕ) (i j : Fin 3) (hn : 4 * δ n ≤ r / 2) :
      tsupport (fun z : Vec3 × ℝ =>
        spatialPartial (fun q : ParabolicPoint => Vseq n q i) j z) ⊆ K' :=
    (spatialPartial_tsupport_subset_product (f := fun z => Vseq n z i) j).trans
      (hVcomponentSupport n i hn)
  have hSecondSupport (n : ℕ) (i j k : Fin 3) (hn : 4 * δ n ≤ r / 2) :
      tsupport (fun z : Vec3 × ℝ =>
        spatialSecondPartial (fun q : ParabolicPoint => Vseq n q i) j k z) ⊆ K' :=
    (spatialSecondPartial_tsupport_subset_product (f := fun z => Vseq n z i) j k).trans
      (hVcomponentSupport n i hn)
  have hTimeSupport (n : ℕ) (i : Fin 3) (hn : 4 * δ n ≤ r / 2) :
      tsupport (fun z : Vec3 × ℝ =>
        timePartial (fun q : ParabolicPoint => Vseq n q i) z) ⊆ K' :=
    (timePartial_tsupport_subset_product (f := fun z => Vseq n z i)).trans
      (hVcomponentSupport n i hn)
  have hVzero (n : ℕ) (i : Fin 3) (hn : 4 * δ n ≤ r / 2)
      {z : Vec3 × ℝ} (hz : z ∉ K') : Vseq n z i = 0 :=
    value_eq_zero_of_tsupport_subset (hVcomponentSupport n i hn) hz
  have hSpatialZero (n : ℕ) (i j : Fin 3) (hn : 4 * δ n ≤ r / 2)
      {z : Vec3 × ℝ} (hz : z ∉ K') :
      spatialPartial (fun q : ParabolicPoint => Vseq n q i) j z = 0 :=
    value_eq_zero_of_tsupport_subset (hSpatialSupport n i j hn) hz
  have hSecondZero (n : ℕ) (i j k : Fin 3) (hn : 4 * δ n ≤ r / 2)
      {z : Vec3 × ℝ} (hz : z ∉ K') :
      spatialSecondPartial (fun q : ParabolicPoint => Vseq n q i) j k z = 0 :=
    value_eq_zero_of_tsupport_subset (hSecondSupport n i j k hn) hz
  have hTimeZero (n : ℕ) (i : Fin 3) (hn : 4 * δ n ≤ r / 2)
      {z : Vec3 × ℝ} (hz : z ∉ K') :
      timePartial (fun q : ParabolicPoint => Vseq n q i) z = 0 :=
    value_eq_zero_of_tsupport_subset (hTimeSupport n i hn) hz
  have hRsource (i : Fin 3) :
      (fun z : Vec3 × ℝ => R0 z i) =
        (fun z => T0 z i + ∑ j, H0 z i j j) := by
    funext z
    by_cases hz : z ∈ U <;> simp [R0, R, T0, H0, zeroExtendField, hz]
  have hdiagMem (i : Fin 3) :
      MemLp (fun z : Vec3 × ℝ => ∑ j, H0 z i j j) (2 : ℝ≥0∞)
        (volume : Measure (Vec3 × ℝ)) := by
    simpa only [Finset.univ_eq_attach] using
      memLp_finsetSum (Finset.univ : Finset (Fin 3)) (by
        intro j hj
        exact hHcomponent i j j)
  have hoperatorMollify (n : ℕ) (i : Fin 3) :
      spaceTimeMollify (fun z : Vec3 × ℝ => R0 z i) (δ n) (hδpos n) =
        fun z => spaceTimeMollify (fun q => T0 q i) (δ n) (hδpos n) z +
          ∑ j, spaceTimeMollify (fun q => H0 q i j j) (δ n) (hδpos n) z := by
    calc
      spaceTimeMollify (fun z : Vec3 × ℝ => R0 z i) (δ n) (hδpos n) =
          spaceTimeMollify (fun z => T0 z i + ∑ j, H0 z i j j)
            (δ n) (hδpos n) := by rw [hRsource i]
      _ = spaceTimeMollify (fun z => T0 z i) (δ n) (hδpos n) +
          spaceTimeMollify (fun z => ∑ j, H0 z i j j) (δ n) (hδpos n) := by
        change spaceTimeMollify
          ((fun z => T0 z i) + (fun z => ∑ j, H0 z i j j))
          (δ n) (hδpos n) = _
        exact spaceTimeMollify_add_of_memLp (hδpos n)
          (hTcomponent i) (hdiagMem i)
      _ = _ := by
        rw [spaceTimeMollify_finset_sum (hδpos n) (by
          intro j hj
          exact hHcomponent i j j)]
        funext z
        rfl
  have hWeakGzero : ∀ᵐ z ∂(volume : Measure (Vec3 × ℝ)),
      ∀ i j : Fin 3, z ∈ U → z ∉ K' → G z i j = 0 := by
    apply ae_all_iff.mpr
    intro i
    apply ae_all_iff.mpr
    intro j
    filter_upwards [hweakZero.1 i j] with z hzero
    intro hzU hzK'
    apply hzero hzU
    intro hzK
    have hr4 : 0 ≤ r / 4 := by positivity
    have hzeroBall : (0 : Vec3 × ℝ) ∈ Metric.closedBall 0 (r / 4) :=
      Metric.mem_closedBall.mpr (by rw [dist_self]; exact hr4)
    exact hzK' ⟨0, hzeroBall, z, hzK, by simp⟩
  have hWeakHzero : ∀ᵐ z ∂(volume : Measure (Vec3 × ℝ)),
      ∀ i j k : Fin 3, z ∈ U → z ∉ K' → H z i j k = 0 := by
    apply ae_all_iff.mpr
    intro i
    apply ae_all_iff.mpr
    intro j
    apply ae_all_iff.mpr
    intro k
    filter_upwards [hweakZero.2.1 i j k] with z hzero
    intro hzU hzK'
    apply hzero hzU
    intro hzK
    have hr4 : 0 ≤ r / 4 := by positivity
    have hzeroBall : (0 : Vec3 × ℝ) ∈ Metric.closedBall 0 (r / 4) :=
      Metric.mem_closedBall.mpr (by rw [dist_self]; exact hr4)
    exact hzK' ⟨0, hzeroBall, z, hzK, by simp⟩
  have hWeakTzero : ∀ᵐ z ∂(volume : Measure (Vec3 × ℝ)),
      ∀ i : Fin 3, z ∈ U → z ∉ K' → T z i = 0 := by
    apply ae_all_iff.mpr
    intro i
    filter_upwards [hweakZero.2.2 i] with z hzero
    intro hzU hzK'
    apply hzero hzU
    intro hzK
    have hr4 : 0 ≤ r / 4 := by positivity
    have hzeroBall : (0 : Vec3 × ℝ) ∈ Metric.closedBall 0 (r / 4) :=
      Metric.mem_closedBall.mpr (by rw [dist_self]; exact hr4)
    exact hzK' ⟨0, hzeroBall, z, hzK, by simp⟩
  have hr4 : 0 ≤ r / 4 := by positivity
  have hzeroBall : (0 : Vec3 × ℝ) ∈ Metric.closedBall 0 (r / 4) :=
    Metric.mem_closedBall.mpr (by rw [dist_self]; exact hr4)
  have hKsubK' : K ⊆ K' := by
    intro z hz
    exact ⟨0, hzeroBall, z, hz, by simp⟩
  have hBridge (n : ℕ) (hn : 4 * δ n ≤ r / 2) (z : Vec3 × ℝ)
      (hz : z ∈ K') :
      (∀ i j : Fin 3,
        spatialPartial (fun q : ParabolicPoint => Vseq n q i) j z =
          Gseq n z (i, j)) ∧
      (∀ i j k : Fin 3,
        spatialSecondPartial (fun q : ParabolicPoint => Vseq n q i) j k z =
          spaceTimeMollify (fun q => H0 q i j k) (δ n) (hδpos n) z) ∧
      (∀ i : Fin 3,
        timePartial (fun q : ParabolicPoint => Vseq n q i) z =
          spaceTimeMollify (fun q => T0 q i) (δ n) (hδpos n) z) := by
    have hz' : z ∈ Metric.closedBall (0 : Vec3 × ℝ) (r / 4) +
        (parabolicHomeomorph '' tsupport w) := by simpa [K'] using hz
    have hraw := spaceTimeMollify_compactSupport_weakDerivs
      hΩ hI hderiv htsupport hr hthick (hδpos n) hn hz'
    have hG0comp (i j : Fin 3) :
        (fun q : Vec3 × ℝ => zeroExtendField U G q i j) =
          zeroExtendField U (fun y : Vec3 × ℝ => Dw (parabolicHomeomorph.symm y) i j) := by
      funext q
      by_cases hq : q ∈ U <;> simp [G, zeroExtendField, U, hq]
    have hH0comp (i j k : Fin 3) :
        (fun q : Vec3 × ℝ => zeroExtendField U H q i j k) =
          zeroExtendField U
            (fun y : Vec3 × ℝ => D2w (parabolicHomeomorph.symm y) i j k) := by
      funext q
      by_cases hq : q ∈ U <;> simp [H, zeroExtendField, U, hq]
    have hT0comp (i : Fin 3) :
        (fun q : Vec3 × ℝ => zeroExtendField U T q i) =
          zeroExtendField U (fun y : Vec3 × ℝ => Dtw (parabolicHomeomorph.symm y) i) := by
      funext q
      by_cases hq : q ∈ U <;> simp [T, zeroExtendField, U, hq]
    refine ⟨?_, ?_, ?_⟩
    · intro i j
      change spatialPartial (fun q : ParabolicPoint =>
        spaceTimeMollify (fun y => w (parabolicHomeomorph.symm y) i)
          (δ n) (hδpos n) q) j z =
        spaceTimeMollify (fun q => zeroExtendField U G q i j)
          (δ n) (hδpos n) z
      rw [hG0comp i j]
      exact hraw.1 i j
    · intro i j k
      change spatialSecondPartial (fun q : ParabolicPoint =>
        spaceTimeMollify (fun y => w (parabolicHomeomorph.symm y) i)
          (δ n) (hδpos n) q) j k z =
        spaceTimeMollify (fun q => zeroExtendField U H q i j k)
          (δ n) (hδpos n) z
      rw [hH0comp i j k]
      exact hraw.2.1 i j k
    · intro i
      change timePartial (fun q : ParabolicPoint =>
        spaceTimeMollify (fun y => w (parabolicHomeomorph.symm y) i)
          (δ n) (hδpos n) q) z =
        spaceTimeMollify (fun q => zeroExtendField U T q i)
          (δ n) (hδpos n) z
      rw [hT0comp i]
      exact hraw.2.2 i
  have hOperator (n : ℕ) (hn : 4 * δ n ≤ r / 2) (z : Vec3 × ℝ)
      (hz : z ∈ K') (i : Fin 3) :
      timePartial (fun q : ParabolicPoint => Vseq n q i) z +
        ∑ j, spatialSecondPartial (fun q : ParabolicPoint => Vseq n q i) j j z =
      Rseq n z i := by
    have hb := hBridge n hn z hz
    calc
      _ = spaceTimeMollify (fun q => T0 q i) (δ n) (hδpos n) z +
          ∑ j, spaceTimeMollify (fun q => H0 q i j j) (δ n) (hδpos n) z := by
        rw [hb.2.2 i]
        congr 1
        apply Finset.sum_congr rfl
        intro j hj
        exact hb.2.1 i j j
      _ = Rseq n z i := by
        dsimp [Rseq]
        exact (congrFun (hoperatorMollify n i) z).symm
  let smoothLeftIntegrand (n : ℕ) (z : Vec3 × ℝ) : ℝ :=
    σ z * vec3EuclideanNorm (Vseq n z) ^ 2 +
      τ z * spatialGradientSq (Vseq n) (spatialGradient (Vseq n)) z
  let smoothRightIntegrand (n : ℕ) (z : Vec3 × ℝ) : ℝ :=
    ρ z * vec3EuclideanNorm (fun i =>
      timePartial (fun y => Vseq n y i) z +
        ∑ j, spatialSecondPartial (fun y => Vseq n y i) j j z) ^ 2
  let massIntegrand (n : ℕ) (z : Vec3 × ℝ) : ℝ :=
    σ z * ∑ i, Wseq n z i ^ 2
  let gradientIntegrand (n : ℕ) (z : Vec3 × ℝ) : ℝ :=
    τ z * ∑ ij : Fin 3 × Fin 3, Gseq n z ij ^ 2
  let residualIntegrand (n : ℕ) (z : Vec3 × ℝ) : ℝ :=
    ρ z * ∑ i, Rseq n z i ^ 2
  let weakMassIntegrand (z : Vec3 × ℝ) : ℝ :=
    σ z * vec3EuclideanNorm (w (parabolicHomeomorph.symm z)) ^ 2
  let weakGradientIntegrand (z : Vec3 × ℝ) : ℝ :=
    τ z * ∑ i, ∑ j, Dw (parabolicHomeomorph.symm z) i j ^ 2
  let weakResidualIntegrand (z : Vec3 × ℝ) : ℝ :=
    ρ z * vec3EuclideanNorm (fun i =>
      Dtw (parabolicHomeomorph.symm z) i +
        ∑ j, D2w (parabolicHomeomorph.symm z) i j j) ^ 2
  have hSmoothPoint (n : ℕ) (hn : 4 * δ n ≤ r / 2) (z : Vec3 × ℝ)
      (hz : z ∈ K') :
      smoothLeftIntegrand n z = massIntegrand n z + gradientIntegrand n z ∧
      smoothRightIntegrand n z = residualIntegrand n z := by
    have hb := hBridge n hn z hz
    have hmass : vec3EuclideanNorm (Vseq n z) ^ 2 = ∑ i, Wseq n z i ^ 2 := by
      rw [vec3EuclideanNorm_sq]
      apply Finset.sum_congr rfl
      intro i hi
      simp [Vseq, Wseq, W0, spaceTimeMollifyPi, hWrawEq]
    have hgrad : spatialGradientSq (Vseq n) (spatialGradient (Vseq n)) z =
        ∑ ij : Fin 3 × Fin 3, Gseq n z ij ^ 2 := by
      calc
        spatialGradientSq (Vseq n) (spatialGradient (Vseq n)) z =
            ∑ i, ∑ j,
              spatialPartial (fun q : ParabolicPoint => Vseq n q i) j z ^ 2 := rfl
        _ = ∑ ij : Fin 3 × Fin 3, Gseq n z ij ^ 2 := by
          rw [fin3_double_sum_eq_product]
          apply Finset.sum_congr rfl
          rintro ⟨i, j⟩ hij
          rw [hb.1 i j]
    have hop (i : Fin 3) := hOperator n hn z hz i
    constructor
    · simp [smoothLeftIntegrand, massIntegrand, gradientIntegrand, hmass, hgrad]
    · dsimp [smoothRightIntegrand, residualIntegrand]
      rw [vec3EuclideanNorm_sq]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      rw [hop i]
  have hSmoothLeftOff (n : ℕ) (hn : 4 * δ n ≤ r / 2) :
      ∀ᵐ z ∂(volume : Measure (Vec3 × ℝ)),
        z ∈ U → z ∉ K' → smoothLeftIntegrand n z = 0 := by
    filter_upwards [] with z
    intro hzU hzK'
    have hv : Vseq n z = 0 := funext fun i => hVzero n i hn hzK'
    have hgrad : spatialGradientSq (Vseq n) (spatialGradient (Vseq n)) z = 0 := by
      unfold spatialGradientSq spatialGradient
      apply Finset.sum_eq_zero
      intro i hi
      apply Finset.sum_eq_zero
      intro j hj
      simp [hSpatialZero n i j hn hzK']
    dsimp [smoothLeftIntegrand]
    rw [hv, hgrad]
    simp [vec3EuclideanNorm]
  have hSmoothRightOff (n : ℕ) (hn : 4 * δ n ≤ r / 2) :
      ∀ᵐ z ∂(volume : Measure (Vec3 × ℝ)),
        z ∈ U → z ∉ K' → smoothRightIntegrand n z = 0 := by
    filter_upwards [] with z
    intro hzU hzK'
    have hop : (fun i : Fin 3 =>
        timePartial (fun y => Vseq n y i) z +
          ∑ j, spatialSecondPartial (fun y => Vseq n y i) j j z) = 0 := by
      funext i
      rw [hTimeZero n i hn hzK']
      have hsum : (∑ j, spatialSecondPartial
          (fun y => Vseq n y i) j j z) = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        exact hSecondZero n i j j hn hzK'
      rw [hsum]
      simp
    dsimp [smoothRightIntegrand]
    rw [hop]
    simp [vec3EuclideanNorm]
  have hleftK (n : ℕ) (hn : 4 * δ n ≤ r / 2) :
      (∫ z in K', smoothLeftIntegrand n z
        ∂(volume : Measure (Vec3 × ℝ))) =
        (∫ z in K', massIntegrand n z + gradientIntegrand n z
          ∂(volume : Measure (Vec3 × ℝ))) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hK'meas] with z hz
    exact (hSmoothPoint n hn z hz).1
  have hrightK (n : ℕ) (hn : 4 * δ n ≤ r / 2) :
      (∫ z in K', smoothRightIntegrand n z
        ∂(volume : Measure (Vec3 × ℝ))) =
        (∫ z in K', residualIntegrand n z
          ∂(volume : Measure (Vec3 × ℝ))) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hK'meas] with z hz
    exact (hSmoothPoint n hn z hz).2
  have hSmoothCompact (n : ℕ) (hn : 4 * δ n ≤ r / 2) :
      (∫ z in K', smoothLeftIntegrand n z ∂(volume : Measure (Vec3 × ℝ))) ≤
        c * (∫ z in K', smoothRightIntegrand n z
          ∂(volume : Measure (Vec3 × ℝ))) := by
    have hsmooth := hSmooth (Vseq n) ((hδtests n).2 (hδpos n))
    have hsmoothU :
        (∫ z in U, smoothLeftIntegrand n z ∂(volume : Measure (Vec3 × ℝ))) ≤
          c * (∫ z in U, smoothRightIntegrand n z
            ∂(volume : Measure (Vec3 × ℝ))) := by
      simpa [smoothLeftIntegrand, smoothRightIntegrand] using hsmooth
    have hleftDomain := setIntegral_eq_of_zero_off hUmeas hK'meas hK'U
      (hSmoothLeftOff n hn)
    have hrightDomain := setIntegral_eq_of_zero_off hUmeas hK'meas hK'U
      (hSmoothRightOff n hn)
    rw [hleftDomain, hrightDomain] at hsmoothU
    exact hsmoothU
  have hmassSeqInt (n : ℕ) : Integrable (massIntegrand n)
      ((volume : Measure (Vec3 × ℝ)).restrict K') := by
    exact weightedPiSq_integrable hσaesm hσbound (fun i => hWseqMem n i)
  have hgradientSeqInt (n : ℕ) : Integrable (gradientIntegrand n)
      ((volume : Measure (Vec3 × ℝ)).restrict K') := by
    exact weightedPiSq_integrable hτaesm hτbound
      (fun ij => hGseqMem n ij)
  have hleftSeqSplit (n : ℕ) :
      (∫ z in K', massIntegrand n z + gradientIntegrand n z
        ∂(volume : Measure (Vec3 × ℝ))) =
      (∫ z in K', massIntegrand n z ∂(volume : Measure (Vec3 × ℝ))) +
        ∫ z in K', gradientIntegrand n z ∂(volume : Measure (Vec3 × ℝ)) :=
    integral_add (hmassSeqInt n) (hgradientSeqInt n)
  let leftSeq (n : ℕ) : ℝ :=
    (∫ z in K', massIntegrand n z ∂(volume : Measure (Vec3 × ℝ))) +
      ∫ z in K', gradientIntegrand n z ∂(volume : Measure (Vec3 × ℝ))
  let rightSeq (n : ℕ) : ℝ :=
    ∫ z in K', residualIntegrand n z ∂(volume : Measure (Vec3 × ℝ))
  let leftLimit : ℝ :=
    (∫ z in K', σ z * ∑ i, W0 z i ^ 2 ∂(volume : Measure (Vec3 × ℝ))) +
      ∫ z in K', τ z * ∑ ij : Fin 3 × Fin 3,
        G0 z ij.1 ij.2 ^ 2 ∂(volume : Measure (Vec3 × ℝ))
  let rightLimit : ℝ :=
    ∫ z in K', ρ z * ∑ i, R0 z i ^ 2 ∂(volume : Measure (Vec3 × ℝ))
  have hleftLimit : Tendsto leftSeq atTop (nhds leftLimit) := by
    have h := hMassLimit.add hGradLimit
    simpa [leftSeq, leftLimit, massIntegrand, gradientIntegrand] using h
  have hrightLimit : Tendsto rightSeq atTop (nhds rightLimit) := by
    simpa [rightSeq, rightLimit, residualIntegrand] using hResidualLimit
  have hseqIneq : ∀ᶠ n in atTop, leftSeq n ≤ c * rightSeq n := by
    filter_upwards [hδsmall] with n hn
    have h := hSmoothCompact n hn
    rw [hleftK n hn, hrightK n hn, hleftSeqSplit n] at h
    simpa [leftSeq, rightSeq] using h
  have hWeakMassInt : Integrable
      (fun z : Vec3 × ℝ => σ z * ∑ i, W0 z i ^ 2)
      ((volume : Measure (Vec3 × ℝ)).restrict K') :=
    weightedPiSq_integrable hσaesm hσbound (fun i => (hWcomponent i).restrict K')
  have hWeakGradientInt : Integrable
      (fun z : Vec3 × ℝ => τ z * ∑ ij : Fin 3 × Fin 3,
        G0 z ij.1 ij.2 ^ 2)
      ((volume : Measure (Vec3 × ℝ)).restrict K') :=
    weightedPiSq_integrable hτaesm hτbound
      (fun ij => (hGcomponent ij.1 ij.2).restrict K')
  have hWeakResidualInt : Integrable
      (fun z : Vec3 × ℝ => ρ z * ∑ i, R0 z i ^ 2)
      ((volume : Measure (Vec3 × ℝ)).restrict K') :=
    weightedPiSq_integrable hρaesm hρbound
      (fun i => (hRcomponent i).restrict K')
  have hWeakMassZero : ∀ᵐ z ∂(volume : Measure (Vec3 × ℝ)),
      z ∈ U → z ∉ K' → weakMassIntegrand z = 0 := by
    filter_upwards [] with z
    intro hzU hzK'
    have hzK : z ∉ K := fun hz => hzK' (hKsubK' hz)
    have hWz : W z = 0 := by
      funext i
      exact value_eq_zero_of_tsupport_subset
        (product_component_tsupport_subset hcompact i) hzK
    change σ z * vec3EuclideanNorm (W z) ^ 2 = 0
    rw [hWz]
    simp [vec3EuclideanNorm]
  have hWeakGradientZero : ∀ᵐ z ∂(volume : Measure (Vec3 × ℝ)),
      z ∈ U → z ∉ K' → weakGradientIntegrand z = 0 := by
    filter_upwards [hWeakGzero] with z hGzero
    intro hzU hzK'
    have hraw (i j : Fin 3) : Dw (parabolicHomeomorph.symm z) i j = 0 := by
      change G z i j = 0
      exact hGzero i j hzU hzK'
    have hraw' (i j : Fin 3) : Dw z i j = 0 := by simpa using hraw i j
    have hsum : (∑ i, ∑ j, Dw (parabolicHomeomorph.symm z) i j ^ 2) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      apply Finset.sum_eq_zero
      intro j hj
      simp [hraw' i j]
    dsimp [weakGradientIntegrand]
    have hsum' : (∑ i, ∑ j, Dw z i j ^ 2) = 0 := by simpa using hsum
    rw [hsum']
    simp
  have hWeakResidualZero : ∀ᵐ z ∂(volume : Measure (Vec3 × ℝ)),
      z ∈ U → z ∉ K' → weakResidualIntegrand z = 0 := by
    filter_upwards [hWeakTzero, hWeakHzero] with z hTzero hHzero
    intro hzU hzK'
    have hraw (i : Fin 3) : Dtw z i + ∑ j, D2w z i j j = 0 := by
      have ht := hTzero i hzU hzK'
      change Dtw (parabolicHomeomorph.symm z) i = 0 at ht
      have ht' : Dtw z i = 0 := by simpa using ht
      have hsum : (∑ j, D2w (parabolicHomeomorph.symm z) i j j) = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        have hjzero := hHzero i j j hzU hzK'
        change D2w (parabolicHomeomorph.symm z) i j j = 0 at hjzero
        exact hjzero
      have hsum' : (∑ j, D2w z i j j) = 0 := by simpa using hsum
      rw [ht', hsum']
      simp
    have hvec : (fun i : Fin 3 =>
        Dtw z i + ∑ j, D2w z i j j) = 0 := funext hraw
    dsimp [weakResidualIntegrand]
    rw [hvec]
    simp [vec3EuclideanNorm]
  have hWeakMassTarget :
      (∫ z in K', weakMassIntegrand z ∂(volume : Measure (Vec3 × ℝ))) =
        ∫ z in K', σ z * ∑ i, W0 z i ^ 2 ∂(volume : Measure (Vec3 × ℝ)) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hK'meas] with z hz
    have hw0 (i : Fin 3) : W0 z i = w (parabolicHomeomorph.symm z) i := by
      have hzU : z ∈ U := hK'U hz
      simp [W0, W, zeroExtendField, U, hzU]
    dsimp [weakMassIntegrand]
    rw [vec3EuclideanNorm_sq]
    simp [hw0]
  have hWeakGradientTarget :
      (∫ z in K', weakGradientIntegrand z ∂(volume : Measure (Vec3 × ℝ))) =
        ∫ z in K', τ z * ∑ ij : Fin 3 × Fin 3,
          G0 z ij.1 ij.2 ^ 2 ∂(volume : Measure (Vec3 × ℝ)) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hK'meas] with z hz
    have hzU : z ∈ U := hK'U hz
    have hg0 (i j : Fin 3) : G0 z i j = Dw (parabolicHomeomorph.symm z) i j := by
      change zeroExtendField U G z i j = Dw z i j
      simp [G, zeroExtendField, U, hzU]
    change τ z * ∑ i, ∑ j, Dw (parabolicHomeomorph.symm z) i j ^ 2 =
      τ z * ∑ ij : Fin 3 × Fin 3, G0 z ij.1 ij.2 ^ 2
    calc
      _ = τ z * ∑ i, ∑ j, (G0 z i j) ^ 2 := by
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        rw [← hg0 i j]
      _ = _ := by rw [fin3_double_sum_eq_product]
  have hR0target (z : Vec3 × ℝ) (hz : z ∈ K') (i : Fin 3) :
      R0 z i = Dtw z i + ∑ j, D2w z i j j := by
    have hzU := hK'U hz
    have h := congrFun (hRsource i) z
    simpa [T0, T, H0, H, zeroExtendField, U, hzU] using h
  have hWeakResidualTarget :
      (∫ z in U, weakResidualIntegrand z ∂(volume : Measure (Vec3 × ℝ))) =
        ∫ z in K', ρ z * ∑ i, R0 z i ^ 2 ∂(volume : Measure (Vec3 × ℝ)) := by
    rw [setIntegral_eq_of_zero_off hUmeas hK'meas hK'U hWeakResidualZero]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hK'meas] with z hz
    dsimp [weakResidualIntegrand]
    rw [vec3EuclideanNorm_sq]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [← hR0target z hz i]
  have hWeakMassAE : weakMassIntegrand =ᵐ[(volume : Measure (Vec3 × ℝ)).restrict K']
      (fun z => σ z * ∑ i, W0 z i ^ 2) := by
    filter_upwards [ae_restrict_mem hK'meas] with z hz
    have hzU : z ∈ U := hK'U hz
    have hw0 (i : Fin 3) : W0 z i = w (parabolicHomeomorph.symm z) i := by
      simp [W0, W, zeroExtendField, U, hzU]
    dsimp [weakMassIntegrand]
    rw [vec3EuclideanNorm_sq]
    simp [hw0]
  have hWeakGradientAE : weakGradientIntegrand =ᵐ[(volume : Measure (Vec3 × ℝ)).restrict K']
      (fun z => τ z * ∑ ij : Fin 3 × Fin 3, G0 z ij.1 ij.2 ^ 2) := by
    filter_upwards [ae_restrict_mem hK'meas] with z hz
    have hzU : z ∈ U := hK'U hz
    have hg0 (i j : Fin 3) : G0 z i j = Dw z i j := by
      change zeroExtendField U G z i j = Dw z i j
      simp [G, zeroExtendField, U, hzU]
    change τ z * ∑ i, ∑ j, Dw z i j ^ 2 =
      τ z * ∑ ij : Fin 3 × Fin 3, G0 z ij.1 ij.2 ^ 2
    calc
      _ = τ z * ∑ i, ∑ j, G0 z i j ^ 2 := by
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        rw [← hg0 i j]
      _ = _ := by rw [fin3_double_sum_eq_product]
  have hWeakMassInt' : Integrable weakMassIntegrand
      ((volume : Measure (Vec3 × ℝ)).restrict K') := hWeakMassInt.congr hWeakMassAE.symm
  have hWeakGradientInt' : Integrable weakGradientIntegrand
      ((volume : Measure (Vec3 × ℝ)).restrict K') :=
    hWeakGradientInt.congr hWeakGradientAE.symm
  have hfinal := le_of_tendsto_of_tendsto hleftLimit
    (hrightLimit.const_mul c) hseqIneq
  have hWeakLeftOff : ∀ᵐ z ∂(volume : Measure (Vec3 × ℝ)),
      z ∈ U → z ∉ K' → weakMassIntegrand z + weakGradientIntegrand z = 0 := by
    filter_upwards [hWeakMassZero, hWeakGradientZero] with z hm hg
    intro hzU hzK'
    rw [hm hzU hzK', hg hzU hzK']
    ring
  calc
    (∫ z in U, weakMassIntegrand z + weakGradientIntegrand z
      ∂(volume : Measure (Vec3 × ℝ))) = leftLimit := by
        rw [setIntegral_eq_of_zero_off hUmeas hK'meas hK'U hWeakLeftOff,
          integral_add hWeakMassInt' hWeakGradientInt',
          hWeakMassTarget, hWeakGradientTarget]
    _ ≤ c * rightLimit := hfinal
    _ = c * (∫ z in U, weakResidualIntegrand z
        ∂(volume : Measure (Vec3 × ℝ))) := by rw [hWeakResidualTarget]

end ESS
