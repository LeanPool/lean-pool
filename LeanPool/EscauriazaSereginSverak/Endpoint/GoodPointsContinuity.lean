/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.GoodPointsGlue
public import LeanPool.CaffarelliKohnNirenberg.ClassEquivalence.CompactLp
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.BallBasics
public import Mathlib.MeasureTheory.Measure.AEMeasurable
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Continuity of the local endpoint energy

Local suitability makes the cubic velocity and pressure densities integrable
on compact subsets of the open cylinder. Dominated convergence then gives
continuity of the energy when an interior cylinder is translated.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The velocity-cubed and pressure-to-the-three-halves density used at good points. -/
@[expose] def goodPointEnergyDensity (u : ParabolicPoint → Vec3)
    (p : ParabolicPoint → ℝ) : ParabolicPoint → ℝ≥0∞ :=
  fun z => ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
    ENNReal.ofReal |p z| ^ (3 / 2 : ℝ)

private theorem goodPointPressureDensity_lintegrableOn_compact
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {K : Set ParabolicPoint}
    (hdata : IsSuitableWeakSolutionData (vec3Ball 0 1) (Ioo (-1) 0) 3
      u Du p (fun _ => 0))
    (hK : IsCompact K) (hKsub : K ⊆ goodPointDomain) :
    (∫⁻ z in K, ENNReal.ofReal |p z| ^ (3 / 2 : ℝ)) < ⊤ := by
  have hKsub' : K ⊆ spaceTimeSet (vec3Ball 0 1) (Ioo (-1) 0) := by
    simpa [goodPointDomain, CKN.spaceTimeSet] using hKsub
  have hp := pressure_memLp_threeHalves_on_compact_of_data hdata hK hKsub'
  have hmeas := hp.aestronglyMeasurable
  have hp' := memLp_iff.mp hp
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
      (by norm_num : ENNReal.ofReal (3 / 2 : ℝ) ≠ 0)
      ENNReal.ofReal_ne_top hmeas,
    ENNReal.toReal_ofReal (by norm_num : (3 / 2 : ℝ) ≥ 0)] at hp'
  have hfinite : (∫⁻ z in K, ‖p z‖ₑ ^ (3 / 2 : ℝ)) < ⊤ := by
    by_contra hcon
    have htop : (∫⁻ z in K, ‖p z‖ₑ ^ (3 / 2 : ℝ)) = ⊤ :=
      top_unique (not_lt.mp hcon)
    have hexp : 0 < 1 / (3 / 2 : ℝ) := by norm_num
    simp [htop] at hp'
  have heq (z : ParabolicPoint) : ENNReal.ofReal |p z| = ‖p z‖ₑ := by
    rw [← ofReal_norm, Real.norm_eq_abs]
  have heqpow (z : ParabolicPoint) :
      ENNReal.ofReal |p z| ^ (3 / 2 : ℝ) = ‖p z‖ₑ ^ (3 / 2 : ℝ) := by
    rw [heq]
  simpa only [heqpow] using hfinite

private theorem goodPointEnergyDensity_lintegrableOn_compact
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {K : Set ParabolicPoint}
    (hdata : IsSuitableWeakSolutionData (vec3Ball 0 1) (Ioo (-1) 0) 3
      u Du p (fun _ => 0))
    (hK : IsCompact K) (hKsub : K ⊆ goodPointDomain) :
    (∫⁻ z in K, goodPointEnergyDensity u p z) < ⊤ := by
  have hKsub' : K ⊆ spaceTimeSet (vec3Ball 0 1) (Ioo (-1) 0) := by
    simpa [goodPointDomain, CKN.spaceTimeSet] using hKsub
  have hu := velocity_cube_integrableOn_compact_of_data hdata hK hKsub'
  have hu3 := velocity_memLp_three_on_compact_of_data hdata hK hKsub'
  have huA : AEStronglyMeasurable
      (fun z => vec3EuclideanNorm (u z) ^ (3 : ℕ)) (volume.restrict K) := by
    exact (CKN.Foundation.Parabolic.continuous_vec3EuclideanNorm.pow 3).comp_aestronglyMeasurable
      hu3.aestronglyMeasurable
  have hnonneg : ∀ᵐ z ∂volume.restrict K,
      0 ≤ vec3EuclideanNorm (u z) ^ (3 : ℕ) :=
    Filter.Eventually.of_forall fun z => pow_nonneg (vec3EuclideanNorm_nonneg _) 3
  have hufinne :
      (∫⁻ z in K, ENNReal.ofReal (vec3EuclideanNorm (u z) ^ (3 : ℕ))) ≠ ⊤ :=
    (lintegral_ofReal_ne_top_iff_integrable huA hnonneg).mpr hu
  have hufin :
      (∫⁻ z in K, ENNReal.ofReal (vec3EuclideanNorm (u z) ^ (3 : ℕ))) < ⊤ :=
    lt_of_le_of_ne le_top hufinne
  have huEq (z : ParabolicPoint) :
      ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) =
        ENNReal.ofReal (vec3EuclideanNorm (u z) ^ (3 : ℕ)) := by
    rw [ENNReal.ofReal_rpow_of_nonneg (vec3EuclideanNorm_nonneg _) (by norm_num)]
    norm_num [Real.rpow_natCast]
  have hpfin := goodPointPressureDensity_lintegrableOn_compact hdata hK hKsub
  have hUae : AEMeasurable
      (fun z : ParabolicPoint =>
        ENNReal.ofReal (vec3EuclideanNorm (u z) ^ (3 : ℕ)))
      (volume.restrict K) := by
    exact ENNReal.measurable_ofReal.comp_aemeasurable huA.aemeasurable
  have hsum :
      (∫⁻ z in K,
        ENNReal.ofReal (vec3EuclideanNorm (u z) ^ (3 : ℕ)) +
          ENNReal.ofReal |p z| ^ (3 / 2 : ℝ)) < ⊤ := by
    rw [lintegral_add_left' hUae]
    exact ENNReal.add_lt_top.mpr ⟨hufin, hpfin⟩
  simpa only [goodPointEnergyDensity, huEq] using hsum

private theorem vec3EuclideanSphere_volume_zero (x : Vec3) (r : ℝ) :
    volume {y : Vec3 | vec3EuclideanNorm (y - x) = r} = 0 := by
  let e : Vec3 → PiLp 2 (fun _ : Fin 3 => ℝ) := WithLp.toLp 2
  let S := Metric.sphere (e x) r
  have hS : MeasurableSet S := Metric.isClosed_sphere.measurableSet
  have hzero : volume S = 0 := Measure.addHaar_sphere volume (e x) r
  have heq : {y : Vec3 | vec3EuclideanNorm (y - x) = r} = e ⁻¹' S := by
    ext y
    change vec3EuclideanNorm (y - x) = r ↔ dist (e y) (e x) = r
    rw [dist_eq_norm]
    change vec3EuclideanNorm (y - x) = r ↔
      ‖WithLp.toLp 2 y - WithLp.toLp 2 x‖ = r
    rw [← WithLp.toLp_sub, vec3EuclideanNorm_eq_l2]
  rw [heq]
  exact (PiLp.volume_preserving_toLp (Fin 3)).measure_preimage
    hS.nullMeasurableSet |>.trans hzero

private theorem goodPointEnergy_center_boundary_volume_zero
    (z₀ : ParabolicPoint) (r : ℝ) :
    volume ({z : ParabolicPoint |
        vec3EuclideanNorm (z.1 - z₀.1) = r} ∪
      {z | z.2 = z₀.2 - r ^ 2} ∪ {z | z.2 = z₀.2}) = 0 := by
  have hspace : volume {z : ParabolicPoint |
      vec3EuclideanNorm (z.1 - z₀.1) = r} = 0 := by
    rw [Integration.volume_parabolicPoint_eq_prod]
    change ((volume : Measure Vec3).prod (volume : Measure ℝ))
      {z : Vec3 × ℝ | vec3EuclideanNorm (z.1 - z₀.1) = r} = 0
    rw [show ({z : Vec3 × ℝ | vec3EuclideanNorm (z.1 - z₀.1) = r} :
        Set (Vec3 × ℝ)) = {y : Vec3 | vec3EuclideanNorm (y - z₀.1) = r} ×ˢ
          (Set.univ : Set ℝ) by
      ext ⟨y, t⟩
      simp]
    rw [Measure.prod_prod, vec3EuclideanSphere_volume_zero, zero_mul]
  have htime (t : ℝ) : volume {z : ParabolicPoint | z.2 = t} = 0 := by
    rw [Integration.volume_parabolicPoint_eq_prod]
    change ((volume : Measure Vec3).prod (volume : Measure ℝ))
      {z : Vec3 × ℝ | z.2 = t} = 0
    rw [show ({z : Vec3 × ℝ | z.2 = t} : Set (Vec3 × ℝ)) =
        (Set.univ : Set Vec3) ×ˢ ({t} : Set ℝ) by
      ext ⟨y, s⟩
      simp]
    rw [Measure.prod_prod]
    simp
  exact measure_union_null (measure_union_null hspace (htime (z₀.2 - r ^ 2)))
    (htime z₀.2)

private theorem eventually_lt_iff_of_continuousAt
    {α : Type*} [TopologicalSpace α] {x : α} {f : α → ℝ}
    (hf : ContinuousAt f x) {a : ℝ} (hne : f x ≠ a) :
    ∀ᶠ y in 𝓝 x, (f y < a ↔ f x < a) := by
  by_cases hlt : f x < a
  · filter_upwards [hf.eventually (isOpen_Iio.mem_nhds hlt)] with y hy
    simp [hy, hlt]
  · have hgt : a < f x := lt_of_le_of_ne (le_of_not_gt hlt) hne.symm
    filter_upwards [hf.eventually (isOpen_Ioi.mem_nhds hgt)] with y hy
    simp [not_lt_of_ge hy.le, hlt]

private theorem eventually_le_iff_of_continuousAt
    {α : Type*} [TopologicalSpace α] {x : α} {f : α → ℝ}
    (hf : ContinuousAt f x) {a : ℝ} (hne : f x ≠ a) :
    ∀ᶠ y in 𝓝 x, (a ≤ f y ↔ a ≤ f x) := by
  have hlt := eventually_lt_iff_of_continuousAt hf hne (a := a)
  filter_upwards [hlt] with y hy
  simpa only [not_lt] using not_congr hy

/-- The energy in a fixed interior-radius cylinder is continuous as its center
varies, provided nearby cylinders stay in a compact subset of the domain. -/
theorem goodPointEnergy_continuousAt_of_compact
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} (hdata : IsSuitableWeakSolutionData
      (vec3Ball 0 1) (Ioo (-1) 0) 3 u Du p (fun _ => 0))
    {K : Set ParabolicPoint} (hK : IsCompact K)
    (hKsub : K ⊆ goodPointDomain) {z₀ : ParabolicPoint} {r δ : ℝ}
    (hδ : 0 < δ)
    (hnear : ∀ c : ParabolicPoint, parabolicDist c z₀ < δ →
      parabolicCylinder c.1 c.2 r ⊆ K) :
    Tendsto (fun c : ParabolicPoint => goodPointEnergy u p c.1 c.2 r)
      (𝓝 z₀) (𝓝 (goodPointEnergy u p z₀.1 z₀.2 r)) := by
  let G := goodPointEnergyDensity u p
  have hKsub' : K ⊆ spaceTimeSet (vec3Ball 0 1) (Ioo (-1) 0) := by
    simpa [goodPointDomain, CKN.spaceTimeSet] using hKsub
  have hu3 := velocity_memLp_three_on_compact_of_data hdata hK hKsub'
  have hp32 := pressure_memLp_threeHalves_on_compact_of_data hdata hK hKsub'
  have hU : AEMeasurable
      (fun z : ParabolicPoint => ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ))
      (volume.restrict K) := by
    exact ENNReal.continuous_rpow_const.measurable.comp_aemeasurable
      (ENNReal.measurable_ofReal.comp_aemeasurable
        (CKN.Foundation.Parabolic.continuous_vec3EuclideanNorm.measurable.comp_aemeasurable
          hu3.aestronglyMeasurable.aemeasurable))
  have hP : AEMeasurable
      (fun z : ParabolicPoint => ENNReal.ofReal |p z| ^ (3 / 2 : ℝ))
      (volume.restrict K) := by
    exact ENNReal.continuous_rpow_const.measurable.comp_aemeasurable
      (ENNReal.measurable_ofReal.comp_aemeasurable
        (continuous_abs.measurable.comp_aemeasurable
          hp32.aestronglyMeasurable.aemeasurable))
  have hG : AEMeasurable G (volume.restrict K) := by
    exact hU.add hP
  have hGfinite := goodPointEnergyDensity_lintegrableOn_compact hdata hK hKsub
  have hKmeas : MeasurableSet K := hK.isClosed.measurableSet
  have hBound : AEMeasurable (K.indicator G) volume := by
    exact (aemeasurable_indicator_iff hKmeas).2 hG
  let F : ParabolicPoint → ParabolicPoint → ℝ≥0∞ := fun c z =>
    (parabolicCylinder c.1 c.2 r).indicator G z
  have hCylinderMeas (c : ParabolicPoint) :
      MeasurableSet (parabolicCylinder c.1 c.2 r) := by
    change MeasurableSet (vec3Ball c.1 r ×ˢ Ioc (c.2 - r ^ 2) c.2)
    exact (isOpen_vec3Ball c.1 r).measurableSet.prod measurableSet_Ioc
  have hnearEvent : ∀ᶠ c : ParabolicPoint in 𝓝 z₀,
      parabolicCylinder c.1 c.2 r ⊆ K := by
    filter_upwards [Metric.ball_mem_nhds z₀ hδ] with c hc
    apply hnear c
    simpa only [Metric.mem_ball, dist_eq_parabolicDist] using hc
  have hFmeas : ∀ᶠ c : ParabolicPoint in 𝓝 z₀, AEMeasurable (F c) volume := by
    filter_upwards [hnearEvent] with c hc
    have heq : F c =
        (parabolicCylinder c.1 c.2 r).indicator (K.indicator G) := by
      funext z
      by_cases hz : z ∈ parabolicCylinder c.1 c.2 r
      · simp [F, hz, hc hz]
      · simp [F, hz]
    rw [heq]
    exact hBound.indicator (hCylinderMeas c)
  have hFbound : ∀ᶠ c : ParabolicPoint in 𝓝 z₀,
      ∀ᵐ z ∂volume, F c z ≤ K.indicator G z := by
    filter_upwards [hnearEvent] with c hc
    apply ae_of_all
    intro z
    by_cases hz : z ∈ parabolicCylinder c.1 c.2 r
    · simp [F, hz, hc hz]
    · simp [F, hz]
  have hboundary := goodPointEnergy_center_boundary_volume_zero z₀ r
  let B : Set ParabolicPoint :=
    {z | vec3EuclideanNorm (z.1 - z₀.1) = r} ∪
      {z | z.2 = z₀.2 - r ^ 2} ∪ {z | z.2 = z₀.2}
  have hBnull : volume B = 0 := by
    simpa only [B] using hboundary
  have hboundaryAE : ∀ᵐ z ∂volume,
      z ∉ B := by
    rw [ae_iff]
    have hset : {z : ParabolicPoint | ¬ z ∉ B} = B := by
      ext z
      change (¬ z ∉ B) ↔ z ∈ B
      exact not_not
    rw [hset]
    exact hBnull
  have hFpoint : ∀ᵐ z ∂volume,
      Tendsto (fun c : ParabolicPoint => F c z) (𝓝 z₀) (𝓝 (F z₀ z)) := by
    filter_upwards [hboundaryAE] with z hz
    have hspaceNe : vec3EuclideanNorm (z.1 - z₀.1) ≠ r := by
      intro he
      exact hz (Or.inl (Or.inl he))
    have hlowNe : z.2 ≠ z₀.2 - r ^ 2 := by
      intro he
      exact hz (Or.inl (Or.inr he))
    have htopNe : z.2 ≠ z₀.2 := by
      intro he
      exact hz (Or.inr he)
    have hspace : ∀ᶠ c : ParabolicPoint in 𝓝 z₀,
        (vec3EuclideanNorm (z.1 - c.1) < r ↔
          vec3EuclideanNorm (z.1 - z₀.1) < r) := by
      exact eventually_lt_iff_of_continuousAt
        (CKN.Foundation.Parabolic.continuous_vec3EuclideanNorm.comp
          (continuous_const.sub continuous_fst_parabolicPoint)).continuousAt hspaceNe
    have hlow : ∀ᶠ c : ParabolicPoint in 𝓝 z₀,
        (c.2 - r ^ 2 < z.2 ↔ z₀.2 - r ^ 2 < z.2) := by
      exact eventually_lt_iff_of_continuousAt
        (continuous_snd_parabolicPoint.sub continuous_const).continuousAt hlowNe.symm
    have htop : ∀ᶠ c : ParabolicPoint in 𝓝 z₀,
        (z.2 ≤ c.2 ↔ z.2 ≤ z₀.2) := by
      exact eventually_le_iff_of_continuousAt
        continuous_snd_parabolicPoint.continuousAt htopNe.symm
    have hmem : ∀ᶠ c : ParabolicPoint in 𝓝 z₀,
        (z ∈ parabolicCylinder c.1 c.2 r ↔
          z ∈ parabolicCylinder z₀.1 z₀.2 r) := by
      filter_upwards [hspace, hlow, htop] with c hs hl ht
      change (vec3EuclideanNorm (z.1 - c.1) < r ∧ c.2 - r ^ 2 < z.2 ∧ z.2 ≤ c.2) ↔
        (vec3EuclideanNorm (z.1 - z₀.1) < r ∧ z₀.2 - r ^ 2 < z.2 ∧ z.2 ≤ z₀.2)
      constructor
      · rintro ⟨h₁, h₂, h₃⟩
        exact ⟨hs.mp h₁, hl.mp h₂, ht.mp h₃⟩
      · rintro ⟨h₁, h₂, h₃⟩
        exact ⟨hs.mpr h₁, hl.mpr h₂, ht.mpr h₃⟩
    have hF_eq : (fun c : ParabolicPoint => F c z) =ᶠ[𝓝 z₀]
        fun _ => F z₀ z := by
      filter_upwards [hmem] with c hc
      change (parabolicCylinder c.1 c.2 r).indicator G z =
        (parabolicCylinder z₀.1 z₀.2 r).indicator G z
      by_cases hz' : z ∈ parabolicCylinder c.1 c.2 r
      · rw [Set.indicator_of_mem hz', Set.indicator_of_mem (hc.mp hz')]
      · rw [Set.indicator_of_notMem hz', Set.indicator_of_notMem (mt hc.mpr hz')]
    exact tendsto_const_nhds.congr' hF_eq.symm
  have hGfiniteNe : (∫⁻ z, K.indicator G z ∂volume) ≠ ⊤ := by
    rw [lintegral_indicator hKmeas]
    exact hGfinite.ne
  have hDCT := tendsto_lintegral_filter_of_dominated_convergence'
    (μ := volume) (l := 𝓝 z₀) (F := F) (f := F z₀)
    (K.indicator G) hFmeas hFbound hGfiniteNe hFpoint
  have hEq (c : ParabolicPoint) :
      (∫⁻ z, F c z ∂volume) = goodPointEnergy u p c.1 c.2 r := by
    change (∫⁻ z, (parabolicCylinder c.1 c.2 r).indicator G z ∂volume) =
      goodPointEnergy u p c.1 c.2 r
    rw [lintegral_indicator (hCylinderMeas c)]
    rfl
  have hEqFun : (fun c : ParabolicPoint => ∫⁻ z, F c z ∂volume) =
      fun c => goodPointEnergy u p c.1 c.2 r := funext hEq
  rw [hEqFun] at hDCT
  rw [hEq z₀] at hDCT
  exact hDCT

end ESS
