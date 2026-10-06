/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.LerayHopfLimitMomentum
public import LeanPool.CaffarelliKohnNirenberg.Leray.StabilityTestBounds
public import LeanPool.CaffarelliKohnNirenberg.Leray.StabilityBoundedPairing
public import LeanPool.CaffarelliKohnNirenberg.Leray.StabilityQuadraticIntegral
public import LeanPool.CaffarelliKohnNirenberg.Setting.PressureGaugeSlices

/-!
# The weak momentum equation for the Leray–Hopf limit

This is the weak-equation clause (LH3) of `def:leray-hopf` in the proof of
`prop:leray-hopf-limit`. For a solenoidal test supported in `ℝ³ × (0,T)`, the
regularized identity of `lem:reg-momentum` has no pressure term. On the
compact support of the test, strong `L³` convergence of the velocities and of
their mollifications and weak `L²` convergence of the gradients pass every
term to the limit.
-/

public section

open MeasureTheory Filter Set
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

/-- A compact subset of a finite positive-time slab stays a positive distance
away from the initial time. -/
theorem lerayHopfLimit_compact_time_bounds {T : ℝ} (hT : 0 < T)
    {K : Set (Vec3 × ℝ)} (hK : IsCompact K)
    (hKsub : K ⊆ (Set.univ : Set Vec3) ×ˢ Ioo 0 T) :
    ∃ δ : ℝ, 0 < δ ∧ δ < T ∧ K ⊆ (Set.univ : Set Vec3) ×ˢ Ioo δ T := by
  rcases K.eq_empty_or_nonempty with hempty | hne
  · exact ⟨T / 2, by linarith only [hT], by linarith only [hT], by
      rw [hempty]; exact empty_subset _⟩
  obtain ⟨z₀, hz₀, hmin⟩ := (hK.image continuous_snd).exists_isLeast (hne.image _)
  obtain ⟨z, hz, rfl⟩ := hz₀
  have hzpos : 0 < z.2 := (hKsub hz).2.1
  refine ⟨z.2 / 2, by linarith only [hzpos], ?_, ?_⟩
  · have := (hKsub hz).2.2
    linarith only [this, hzpos]
  · intro y hy
    refine ⟨mem_univ _, ?_, (hKsub hy).2.2⟩
    have := hmin ⟨y, hy, rfl⟩
    change z.2 / 2 < y.2
    have hle : z.2 ≤ y.2 := this
    linarith only [hle, hzpos]

private theorem integrable_mul_mul_bounded
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    {f g φ : α → ℝ} (hf : MemLp f 3 μ) (hg : MemLp g 3 μ) (hφ : MemLp φ ∞ μ) :
    Integrable (fun x => f x * g x * φ x) μ := by
  have : ENNReal.HolderTriple (3 : ℝ≥0∞) 3 (3 / 2 : ℝ≥0∞) := by
    have hreal : Real.HolderTriple 3 3 (3 / 2) := by
      exact ⟨by norm_num, by norm_num, by norm_num⟩
    simpa only [CKN.ofReal_threeHalves, ENNReal.ofReal_ofNat] using
      hreal.ennrealOfReal
  have h : MemLp (fun x => f x * g x) (3 / 2 : ℝ≥0∞) μ := hf.mul hg
  have h32 : (1 : ℝ≥0∞) ≤ 3 / 2 := by
    rw [← CKN.ofReal_threeHalves]
    exact ENNReal.one_le_ofReal.mpr (by norm_num)
  exact stability_integrable_mul_bounded_test μ h32 h hφ

/-- The weak momentum clause (LH3) for the limit of regularized solutions. -/
theorem lerayHopfLimit_momentum
    (T : ℝ) (hT : 0 < T)
    (U J : ℕ → ParabolicPoint → Vec3) (P : ℕ → ParabolicPoint → ℝ)
    (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (hU3 : ∀ n, MemLp (U n) 3
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
    (hJ3 : ∀ n, MemLp (J n) 3
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
    (hu3 : MemLp u 3
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
    (hUconv : Tendsto (fun n => eLpNorm (U n - u) 3
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)))) atTop (𝓝 0))
    (hJconv : Tendsto (fun n => eLpNorm (J n - u) 3
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)))) atTop (𝓝 0))
    (hDu : MemLp Du 2
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
    (hDweak : ∀ i j, ∀ w : ParabolicPoint → ℝ,
      MemLp w 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) →
      Tendsto (fun n => ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T),
          spatialPartial (fun y => U n y i) j z * w z)
        atTop (𝓝 (∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T), Du z i j * w z)))
    (hDloc : ∀ δ : ℝ, 0 < δ → δ < T → ∀ n i j,
      MemLp (fun z => spatialPartial (fun y => U n y i) j z) 2
        (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo δ T))))
    (hreg : ∀ n, ∀ φ : ParabolicPoint → Vec3,
      φ ∈ spaceTimeTestFunction (V := Vec3) (Set.univ : Set Vec3) (Ioi 0) →
      ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioi 0),
        (-(∑ i : Fin 3, U n z i * timePartial (fun y => φ y i) z))
          - ∑ i : Fin 3, ∑ j : Fin 3,
              J n z j * U n z i * spatialPartial (fun y => φ y i) j z
          + ∑ i : Fin 3, ∑ j : Fin 3,
              spatialPartial (fun y => U n y i) j z * spatialPartial (fun y => φ y i) j z
          - P n z * (∑ i : Fin 3, spatialPartial (fun y => φ y i) i z) = 0) :
    ∀ φ : ParabolicPoint → Vec3,
      φ ∈ spaceTimeTestFunction (V := Vec3) (Set.univ : Set Vec3) (Ioo 0 T) →
      (∀ z : ParabolicPoint, ∑ i : Fin 3, spatialPartial (fun y => φ y i) i z = 0) →
      ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T),
        (-(∑ i : Fin 3, u z i * timePartial (fun y => φ y i) z))
          - ∑ i : Fin 3, ∑ j : Fin 3,
              u z i * u z j * spatialPartial (fun y => φ y i) j z
          + ∑ i : Fin 3, ∑ j : Fin 3,
              Du z i j * spatialPartial (fun y => φ y i) j z = 0 := by
  intro φ hφ hdivφ
  let S : Set ParabolicPoint := spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)
  let μ : Measure ParabolicPoint := volume.restrict S
  let φP : Vec3 × ℝ → Vec3 := φ
  let K : Set ParabolicPoint := (tsupport φP : Set (Vec3 × ℝ))
  have hKcpt : IsCompact (tsupport φP) := hφ.2.1
  have hKmeas : MeasurableSet K := (isClosed_tsupport φP).measurableSet
  have hKS : K ⊆ S := hφ.2.2
  have hKfin : volume K < ⊤ := by
    have h : (volume : Measure (Vec3 × ℝ)) (tsupport φP) < ⊤ := hKcpt.measure_lt_top
    exact h
  let μK : Measure ParabolicPoint := volume.restrict K
  have : IsFiniteMeasure μK := isFiniteMeasure_restrict.mpr hKfin.ne
  have hμK : μK ≤ μ := Measure.restrict_mono hKS le_rfl
  obtain ⟨δ, hδ, hδT, hKδ⟩ := lerayHopfLimit_compact_time_bounds hT hKcpt hKS
  have hμKδ : μK ≤ volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo δ T)) :=
    Measure.restrict_mono (hKδ : K ⊆ spaceTimeSet (Set.univ : Set Vec3) (Ioo δ T))
      (le_refl (volume : Measure ParabolicPoint))
  -- vanishing of the test derivatives off the support
  have hoff : ∀ z : ParabolicPoint, z ∉ K → ∀ i,
      timePartial (fun y => φ y i) z = 0 ∧
        ∀ j, spatialPartial (fun y => φ y i) j z = 0 := by
    intro z hz i
    have hzc : (z : Vec3 × ℝ) ∉ tsupport (fun w : Vec3 × ℝ => φ w i) := by
      intro hmem
      exact hz ((tsupport_component_subset φP i
        (fun _ h => by rw [h]; rfl)) hmem)
    exact ⟨timePartial_eq_zero_off_tsupport hzc,
      fun j => spatialPartial_eq_zero_off_tsupport hzc j⟩
  -- test bounds
  have hdt : ∀ i, MemLp (fun z : ParabolicPoint => timePartial (fun y => φ y i) z) ∞ μK :=
    fun i => (stability_timePartial_memLp_top (Ω' := Set.univ) (J := Ioo 0 T)
      φP hφ i).mono_measure hμK
  have hφtop : ∀ i j,
      MemLp (fun z : ParabolicPoint => spatialPartial (fun y => φ y i) j z) ∞ μK :=
    fun i j => (stability_spatialPartial_memLp_top (Ω' := Set.univ) (J := Ioo 0 T)
      φP hφ i j).mono_measure hμK
  have hφ2 : ∀ i j,
      MemLp (fun z : ParabolicPoint => spatialPartial (fun y => φ y i) j z) 2 μK :=
    fun i j => (hφtop i j).mono_exponent le_top
  -- the data on the support
  have hUK : ∀ n, MemLp (U n) 3 μK := fun n => (hU3 n).mono_measure hμK
  have hJK : ∀ n, MemLp (J n) 3 μK := fun n => (hJ3 n).mono_measure hμK
  have huK : MemLp u 3 μK := hu3.mono_measure hμK
  have hUconvK : Tendsto (fun n => eLpNorm (U n - u) 3 μK) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hUconv
      (fun _ => bot_le) (fun n => eLpNorm_mono_measure _ hμK)
  have hJconvK : Tendsto (fun n => eLpNorm (J n - u) 3 μK) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hJconv
      (fun _ => bot_le) (fun n => eLpNorm_mono_measure _ hμK)
  let D : ℕ → ParabolicPoint → Fin 3 → Fin 3 → ℝ := fun n z i j =>
    spatialPartial (fun y => U n y i) j z
  have hDK : ∀ n i j, MemLp (fun z => D n z i j) 2 μK :=
    fun n i j => (hDloc δ hδ hδT n i j).mono_measure hμKδ
  have hdK : ∀ i j, MemLp (fun z => Du z i j) 2 μK :=
    fun i j => ((hDu.mono_measure hμK).eval i).eval j
  have hrestrict : μ.restrict K = μK := by
    change (volume.restrict S).restrict K = volume.restrict K
    rw [Measure.restrict_restrict hKmeas, inter_eq_left.mpr hKS]
  have hweakK : ∀ i j (w : ParabolicPoint → ℝ), MemLp w 2 μK →
      Tendsto (fun n => ∫ z, D n z i j * w z ∂μK) atTop (𝓝 (∫ z, Du z i j * w z ∂μK)) := by
    intro i j w hw
    have hw' : MemLp (K.indicator w) 2 μ := by
      rw [memLp_indicator_iff_restrict hKmeas, hrestrict]
      exact hw
    have hconv := hDweak i j (K.indicator w) hw'
    have hloc : ∀ F : ParabolicPoint → ℝ,
        ∫ z in S, F z * K.indicator w z = ∫ z, F z * w z ∂μK := by
      intro F
      have hpt : (fun z => F z * K.indicator w z) = K.indicator (fun z => F z * w z) := by
        funext z
        rw [indicator_mul_right]
      change ∫ z, F z * K.indicator w z ∂μ = _
      rw [hpt, integral_indicator hKmeas, hrestrict]
    have e1 : (fun n => ∫ z in S, spatialPartial (fun y => U n y i) j z * K.indicator w z) =
        fun n => ∫ z, D n z i j * w z ∂μK := funext fun n => hloc _
    have e2 : ∫ z in S, Du z i j * K.indicator w z = ∫ z, Du z i j * w z ∂μK := hloc _
    rw [e1, e2] at hconv
    exact hconv
  -- integrability of the terms
  have hAseq : ∀ n, Integrable
      (fun z => ∑ i : Fin 3, U n z i * timePartial (fun y => φ y i) z) μK := fun n =>
    integrable_finsetSum _ (fun i _ =>
      stability_integrable_mul_bounded_test μK (by norm_num) ((hUK n).eval i) (hdt i))
  have hA : Integrable
      (fun z => ∑ i : Fin 3, u z i * timePartial (fun y => φ y i) z) μK :=
    integrable_finsetSum _ (fun i _ =>
      stability_integrable_mul_bounded_test μK (by norm_num) (huK.eval i) (hdt i))
  have hBseq : ∀ n, Integrable (fun z => ∑ i : Fin 3, ∑ j : Fin 3,
      U n z i * J n z j * spatialPartial (fun y => φ y i) j z) μK := fun n =>
    integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ =>
      integrable_mul_mul_bounded μK ((hUK n).eval i) ((hJK n).eval j) (hφtop i j)))
  have hB : Integrable (fun z => ∑ i : Fin 3, ∑ j : Fin 3,
      u z i * u z j * spatialPartial (fun y => φ y i) j z) μK :=
    integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ =>
      integrable_mul_mul_bounded μK (huK.eval i) (huK.eval j) (hφtop i j)))
  have hCseq : ∀ n, Integrable (fun z => ∑ i : Fin 3, ∑ j : Fin 3,
      D n z i j * spatialPartial (fun y => φ y i) j z) μK := fun n =>
    integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ =>
      stability_integrable_mul_bounded_test μK (by norm_num) (hDK n i j) (hφtop i j)))
  have hC : Integrable (fun z => ∑ i : Fin 3, ∑ j : Fin 3,
      Du z i j * spatialPartial (fun y => φ y i) j z) μK :=
    integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ =>
      stability_integrable_mul_bounded_test μK (by norm_num) (hdK i j) (hφtop i j)))
  -- the regularized identity on the support
  have hφpos : φ ∈ spaceTimeTestFunction (V := Vec3) (Set.univ : Set Vec3) (Ioi 0) :=
    ⟨hφ.1, hφ.2.1, hφ.2.2.trans (Set.prod_mono subset_rfl Ioo_subset_Ioi_self)⟩
  have hKpos : K ⊆ spaceTimeSet (Set.univ : Set Vec3) (Ioi 0) :=
    hφ.2.2.trans (Set.prod_mono subset_rfl Ioo_subset_Ioi_self)
  have hregK : ∀ n, ∫ z,
      -(∑ i : Fin 3, U n z i * timePartial (fun y => φ y i) z)
        - (∑ i : Fin 3, ∑ j : Fin 3, U n z i * J n z j * spatialPartial (fun y => φ y i) j z)
        + (∑ i : Fin 3, ∑ j : Fin 3, D n z i j * spatialPartial (fun y => φ y i) j z) ∂μK
      = 0 := by
    intro n
    let G : ParabolicPoint → ℝ := fun z =>
      -(∑ i : Fin 3, U n z i * timePartial (fun y => φ y i) z)
        - (∑ i : Fin 3, ∑ j : Fin 3, U n z i * J n z j * spatialPartial (fun y => φ y i) j z)
        + (∑ i : Fin 3, ∑ j : Fin 3, D n z i j * spatialPartial (fun y => φ y i) j z)
    have hGoff : ∀ z, z ∉ K → G z = 0 := by
      intro z hz
      simp only [G, fun i => (hoff z hz i).1, fun i j => (hoff z hz i).2 j, mul_zero,
        Finset.sum_const_zero, neg_zero, sub_zero, add_zero]
    have h := hreg n φ hφpos
    have hpt : ∀ z : ParabolicPoint,
        (-(∑ i : Fin 3, U n z i * timePartial (fun y => φ y i) z))
          - ∑ i : Fin 3, ∑ j : Fin 3,
              J n z j * U n z i * spatialPartial (fun y => φ y i) j z
          + ∑ i : Fin 3, ∑ j : Fin 3,
              spatialPartial (fun y => U n y i) j z * spatialPartial (fun y => φ y i) j z
          - P n z * (∑ i : Fin 3, spatialPartial (fun y => φ y i) i z) = G z := by
      intro z
      have hswap : (∑ i : Fin 3, ∑ j : Fin 3,
          J n z j * U n z i * spatialPartial (fun y => φ y i) j z) =
          ∑ i : Fin 3, ∑ j : Fin 3, U n z i * J n z j * spatialPartial (fun y => φ y i) j z :=
        Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))
      rw [hdivφ z, hswap, mul_zero, sub_zero]
    simp only [hpt] at h
    have h1 : ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioi 0), G z = ∫ z, G z :=
      setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun z hz => hGoff z (fun hK => hz (hKpos hK)))
    have h2 : ∫ z, G z ∂μK = ∫ z, G z :=
      setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => hGoff z hz)
    change ∫ z, G z ∂μK = 0
    rw [h2, ← h1]
    exact h
  have hlim := lerayHopfLimit_weakEquation_of_regularized μK U J u D Du hUK hJK huK
    hUconvK hJconvK hDK hdK hweakK (fun i z => timePartial (fun y => φ y i) z) hdt
    (fun i j z => spatialPartial (fun y => φ y i) j z) hφtop hφ2 hAseq hA hBseq hB
    hCseq hC hregK
  let H : ParabolicPoint → ℝ := fun z =>
    (-(∑ i : Fin 3, u z i * timePartial (fun y => φ y i) z))
      - ∑ i : Fin 3, ∑ j : Fin 3, u z i * u z j * spatialPartial (fun y => φ y i) j z
      + ∑ i : Fin 3, ∑ j : Fin 3, Du z i j * spatialPartial (fun y => φ y i) j z
  have hHoff : ∀ z, z ∉ K → H z = 0 := by
    intro z hz
    simp only [H, fun i => (hoff z hz i).1, fun i j => (hoff z hz i).2 j, mul_zero,
      Finset.sum_const_zero, neg_zero, sub_zero, add_zero]
  have h1 : ∫ z in S, H z = ∫ z, H z :=
    setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun z hz => hHoff z (fun hK => hz (hKS hK)))
  have h2 : ∫ z, H z ∂μK = ∫ z, H z :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => hHoff z hz)
  change ∫ z in S, H z = 0
  rw [h1, ← h2]
  exact hlim

end CKN.Leray

end
