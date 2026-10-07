/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedLerayLimitEnergy
public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedRegularised
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegUniformTenThirds
public import LeanPool.CaffarelliKohnNirenberg.Foundation.RellichBallsCore
public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.VorticityL2Tools
public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.SerrinPairingLimit

/-!
# Space-time integrability of the forced regularized solutions

`eq:forced-ten-thirds` in `lem:forced-energy-bounds`: on every finite slab the
forced regularized velocity lies in `L^{10/3}`, with a bound depending only on
the constants `E_T` and `G_T` of the uniform energy bounds, and hence, by
interpolation with `L²`, in `L³`. The slice interpolation estimate is
integrated in time on the slab `(0,T)` by applying the positive-time estimate
to the velocity truncated at time `T`.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

/-- The space-time `L^{10/3}` estimate on the finite slab `(0,T)`: slices in
`H¹` with a uniform `L²` bound `A` and a gradient bound `D` on the slab give
`L^{10/3}` on the slab, component by component, with the constant of the
positive-time estimate. -/
theorem forcedLerayLimit_component_tenThirds_slab
    (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (A D : ℝ≥0∞) (T : ℝ)
    (hSlices : ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) T)),
      ∃ h : ∀ _i : Fin 3, CKN.H1Function (Set.univ : Set Vec3),
        (∀ i x, (h i).toFun x = u (x, t) i) ∧
        (∀ i x j, (h i).grad x j = Du (x, t) i j))
    (hSliceBound : ∀ t ∈ Ioo (0 : ℝ) T, ∀ i : Fin 3,
      eLpNorm (fun x : Vec3 => u (x, t) i) 2 volume ≤ A)
    (hUmeasurable : Measurable u) (hDumeasurable : Measurable Du)
    (hGradientBound :
      (∫⁻ t in Ioo (0 : ℝ) T, ∫⁻ x : Vec3,
        ENNReal.ofReal (CKN.spatialGradientSq u Du (x, t)) ∂volume ∂volume) ≤ D)
    (hAfinite : A < ⊤) (hDfinite : D < ⊤) (i : Fin 3) :
    MemLp (fun z : ParabolicPoint => u z i) (ENNReal.ofReal (10 / 3 : ℝ))
        (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) ∧
      eLpNorm (fun z : ParabolicPoint => u z i) (ENNReal.ofReal (10 / 3 : ℝ))
          (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) ^
            (10 / 3 : ℝ) ≤
        (CKN.gagliardoNirenbergSobolevConstant ^ (3 / 5 : ℝ)) ^ (10 / 3 : ℝ) *
          A ^ (4 / 3 : ℝ) * D := by
  classical
  let ut : ParabolicPoint → Vec3 := fun z => if z.2 < T then u z else 0
  let Dt : ParabolicPoint → Fin 3 → Vec3 := fun z => if z.2 < T then Du z else 0
  have hTset : MeasurableSet {z : ParabolicPoint | z.2 < T} :=
    measurableSet_lt measurable_snd measurable_const
  have hut : Measurable ut := Measurable.ite hTset hUmeasurable measurable_const
  have hDt : Measurable Dt := Measurable.ite hTset hDumeasurable measurable_const
  have hut_of_lt : ∀ x t, t < T → ut (x, t) = u (x, t) := fun x t ht => by
    simp only [ut, show (x, t).2 < T from ht, ↓reduceIte]
  have hut_of_ge : ∀ x t, ¬ t < T → ut (x, t) = 0 := fun x t ht => by
    simp only [ut, show ¬ (x, t).2 < T from ht, ↓reduceIte]
  have hDt_of_lt : ∀ x t, t < T → Dt (x, t) = Du (x, t) := fun x t ht => by
    simp only [Dt, show (x, t).2 < T from ht, ↓reduceIte]
  have hDt_of_ge : ∀ x t, ¬ t < T → Dt (x, t) = 0 := fun x t ht => by
    simp only [Dt, show ¬ (x, t).2 < T from ht, ↓reduceIte]
  -- the slices of the truncated field
  have hzero : CKN.HasWeakGradientOn (Set.univ : Set Vec3) (fun _ : Vec3 => (0 : ℝ))
      (fun _ _ => 0) := by
    simpa using CKN.HasWeakGradientOn.of_contDiff (U := (Set.univ : Set Vec3))
      (f := fun _ : Vec3 => (0 : ℝ)) contDiff_const
  let zeroH1 : CKN.H1Function (Set.univ : Set Vec3) :=
    { toFun := fun _ => 0
      grad := fun _ _ => 0
      memL2 := by
        simp [CKN.MemL2On, CKN.MemLpOn, CKN.volumeOn]
      gradMemL2 := by
        intro j
        simp [CKN.MemLpOn, CKN.volumeOn]
      hasWeakGradient := hzero }
  have hSlicesT : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))),
      ∃ h : ∀ _i : Fin 3, CKN.H1Function (Set.univ : Set Vec3),
        (∀ i x, (h i).toFun x = ut (x, t) i) ∧
        (∀ i x j, (h i).grad x j = Dt (x, t) i j) := by
    have hIoo := (ae_restrict_iff' measurableSet_Ioo).1 hSlices
    filter_upwards [ae_restrict_of_ae hIoo, ae_restrict_mem measurableSet_Ioi]
      with t hPt ht
    by_cases htT : t < T
    · obtain ⟨h, hv, hg⟩ := hPt ⟨ht, htT⟩
      refine ⟨h, fun i x => ?_, fun i x j => ?_⟩
      · rw [hut_of_lt x t htT]
        exact hv i x
      · rw [hDt_of_lt x t htT]
        exact hg i x j
    · refine ⟨fun _ => zeroH1, fun i x => ?_, fun i x j => ?_⟩
      · rw [hut_of_ge x t htT]
        rfl
      · rw [hDt_of_ge x t htT]
        rfl
  have hBoundT : ∀ t, 0 < t → ∀ i : Fin 3,
      eLpNorm (fun x : Vec3 => ut (x, t) i) 2 volume ≤ A := by
    intro t ht i
    by_cases htT : t < T
    · have heq : (fun x : Vec3 => ut (x, t) i) = fun x => u (x, t) i := by
        funext x
        rw [hut_of_lt x t htT]
      rw [heq]
      exact hSliceBound t ⟨ht, htT⟩ i
    · have heq : (fun x : Vec3 => ut (x, t) i) = 0 := by
        funext x
        rw [hut_of_ge x t htT]
        rfl
      rw [heq, eLpNorm_zero]
      exact bot_le
  have hGradT : (∫⁻ t in Ioi (0 : ℝ), ∫⁻ x : Vec3,
      ENNReal.ofReal (CKN.spatialGradientSq ut Dt (x, t)) ∂volume ∂volume) ≤ D := by
    have hpt : ∀ t, (∫⁻ x : Vec3, ENNReal.ofReal (CKN.spatialGradientSq ut Dt (x, t))) =
        (Iio T).indicator
          (fun t => ∫⁻ x : Vec3, ENNReal.ofReal (CKN.spatialGradientSq u Du (x, t))) t := by
      intro t
      by_cases htT : t < T
      · rw [indicator_of_mem (show t ∈ Iio T from htT)]
        refine lintegral_congr fun x => ?_
        simp only [CKN.spatialGradientSq, hDt_of_lt x t htT]
      · rw [indicator_of_notMem (show t ∉ Iio T from htT)]
        have h0 : ∀ x : Vec3, ENNReal.ofReal (CKN.spatialGradientSq ut Dt (x, t)) = 0 := by
          intro x
          simp [CKN.spatialGradientSq, hDt_of_ge x t htT]
        simp only [h0, lintegral_zero]
    rw [lintegral_congr hpt, lintegral_indicator measurableSet_Iio,
      Measure.restrict_restrict measurableSet_Iio, Iio_inter_Ioi]
    exact hGradientBound
  obtain ⟨hmem, hbound⟩ := regUniform_component_memLp_tenThirds ut Dt A D hSlicesT hBoundT
    hut hDt hGradT hAfinite hDfinite i
  have hle : (volume : Measure ParabolicPoint).restrict
      (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)) ≤
      volume.restrict (CKN.spaceTimeSet Set.univ (Ioi (0 : ℝ))) :=
    Measure.restrict_mono_set volume (Set.prod_mono subset_rfl Ioo_subset_Ioi_self)
  have heqae : (fun z : ParabolicPoint => ut z i) =ᵐ[volume.restrict
      (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))] fun z => u z i := by
    filter_upwards [ae_restrict_mem (MeasurableSet.univ.prod measurableSet_Ioo)] with z hz
    have hzT : z.2 < T := hz.2.2
    simp only [ut, hzT, ↓reduceIte]
  refine ⟨(memLp_congr_ae heqae).1 (hmem.mono_measure hle), ?_⟩
  rw [← eLpNorm_congr_ae heqae]
  exact (ENNReal.rpow_le_rpow (eLpNorm_mono_measure _ hle) (by norm_num)).trans hbound

/-- `eq:forced-ten-thirds`: on every finite slab the forced regularized
velocity lies in `L²`, `L^{10/3}` and `L³`, and each component obeys the
`L^{10/3}` bound in terms of the constants `E_T` and `G_T²` of
`lem:forced-energy-bounds`, which do not depend on `ε`. -/
theorem forcedRegVelocity_memLp_slab
    (ρ : RegMollifierProfile) (a : Vec3 → Vec3) (ha : IsInJ a)
    (f : ParabolicPoint → Vec3) (hf : IsLocallySquareIntegrableForce f)
    (ε : ℝ) (hε : 0 < ε) (T : ℝ) (hT : 0 < T) :
    let μ : Measure ParabolicPoint :=
      volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))
    let E : ℝ := Real.exp T * ((∑ i : Fin 3, ∫ x : Vec3, a x i ^ 2) +
      ∑ i : Fin 3, ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T), f z i ^ 2)
    let G : ℝ := ((∑ i : Fin 3, ∫ x : Vec3, a x i ^ 2) +
      (∑ i : Fin 3, ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T), f z i ^ 2) +
      T * E) / 2
    MemLp (forcedRegVelocity ρ a ha f hf ε) 2 μ ∧
    MemLp (forcedRegVelocity ρ a ha f hf ε) (ENNReal.ofReal (10 / 3 : ℝ)) μ ∧
    MemLp (forcedRegVelocity ρ a ha f hf ε) 3 μ ∧
    ∀ i : Fin 3,
      eLpNorm (fun z : ParabolicPoint => forcedRegVelocity ρ a ha f hf ε z i)
          (ENNReal.ofReal (10 / 3 : ℝ)) μ ^ (10 / 3 : ℝ) ≤
        (CKN.gagliardoNirenbergSobolevConstant ^ (3 / 5 : ℝ)) ^ (10 / 3 : ℝ) *
          ENNReal.ofReal (Real.sqrt E) ^ (4 / 3 : ℝ) * ENNReal.ofReal G := by
  intro μ E G
  let u := forcedRegVelocity ρ a ha f hf ε
  let Du := forcedRegGradient ρ a ha f hf ε
  have hc := forcedRegularised ρ a ha f hf ε hε
  obtain ⟨⟨hSlice, hcont, -, -⟩, hwg, hR2, -, hE⟩ := hc
  have hUm : Measurable u := by
    change Measurable (forcedRegVelocity ρ a ha f hf ε)
    rw [forcedRegVelocity_eq ρ ha hf hε]
    exact (forcedRegRep_stronglyMeasurable ρ ε hε ha hf).measurable
  have hDm : Measurable Du := by
    change Measurable (forcedMollifiedGrad (forcedRegVelocity ρ a ha f hf ε))
    rw [forcedRegVelocity_eq ρ ha hf hε]
    exact measurable_forcedMollifiedGrad (forcedRegRep_stronglyMeasurable ρ ε hε ha hf)
      (fun t i => forcedRegRep_locallyIntegrable ρ ε hε ha hf t i)
  have hu2 : ∀ S : ℝ, 0 < S →
      MemLp u 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 S))) := by
    intro S _
    change MemLp (forcedRegVelocity ρ a ha f hf ε) 2 _
    rw [forcedRegVelocity_eq ρ ha hf hε]
    exact memLp_slab_of_prod (memLp_curveRep_prod (continuous_forcedRegCurve ρ ε hε ha hf)
      (forcedRegRep_stronglyMeasurable ρ ε hε ha hf) (forcedRegRep_slice ρ ε hε ha hf) S)
  obtain ⟨hkin, hgrad⟩ := forcedLerayLimit_energy_bounds ρ ε hε a ha.1 f hf u Du hSlice hcont
    hu2 (fun S hS => (hR2 S hS).1) (fun t ht => (hE t ht).2) T hT
  -- the gradient bound on the slab
  have hgmeas : Measurable fun z : ParabolicPoint =>
      ENNReal.ofReal (CKN.spatialGradientSq u Du z) := by
    apply ENNReal.measurable_ofReal.comp
    unfold CKN.spatialGradientSq
    fun_prop
  have hGradBound : (∫⁻ t in Ioo (0 : ℝ) T, ∫⁻ x : Vec3,
      ENNReal.ofReal (CKN.spatialGradientSq u Du (x, t)) ∂volume ∂volume) ≤
        ENNReal.ofReal G := by
    have hslab : (∫⁻ t in Ioo (0 : ℝ) T, ∫⁻ x : Vec3,
        ENNReal.ofReal (CKN.spatialGradientSq u Du (x, t)) ∂volume ∂volume) =
        ∫⁻ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T),
          ENNReal.ofReal (CKN.spatialGradientSq u Du z) := by
      exact ((lintegral_slab_eq_prod _ (Ioo 0 T)).trans
        (lintegral_prod_symm _ hgmeas.aemeasurable)).symm
    rw [hslab, ← regUniformDissipation_eq_slab,
      forcedHopf_dissipation_eq_ofReal u Du T (hR2 T hT).1]
    refine ENNReal.ofReal_le_ofReal ?_
    change _ ≤ (_ + _ + T * E) / 2
    linarith only [hgrad]
  have hfin : (∫⁻ t in Ioo (0 : ℝ) T, ∫⁻ x in (Set.univ : Set Vec3),
      ENNReal.ofReal (CKN.spatialGradientSq u Du (x, t)) ∂volume) < ∞ := by
    simp only [Measure.restrict_univ]
    exact hGradBound.trans_lt ENNReal.ofReal_lt_top
  have hgradSlices := CKN.Foundation.ae_memLp_two_spatial_gradient_slice_of_lintegral_lt_top
    (K := (Set.univ : Set Vec3)) (J := Ioo (0 : ℝ) T) u Du hDm hfin
  have hSlices : ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) T)),
      ∃ h : ∀ _i : Fin 3, CKN.H1Function (Set.univ : Set Vec3),
        (∀ i x, (h i).toFun x = u (x, t) i) ∧
        (∀ i x j, (h i).grad x j = Du (x, t) i j) := by
    filter_upwards [hgradSlices, ae_restrict_of_ae_restrict_of_subset Ioo_subset_Ioi_self hwg,
      ae_restrict_mem measurableSet_Ioo] with t hDt hW ht
    have hut : MemLp (fun x : Vec3 => u (x, t)) 2 volume := hSlice t ht.1.le
    let h : ∀ _i : Fin 3, CKN.H1Function (Set.univ : Set Vec3) := fun i => {
      toFun := fun x => u (x, t) i
      grad := fun x => Du (x, t) i
      memL2 := by
        simpa [CKN.MemL2On, CKN.MemLpOn, CKN.volumeOn, Measure.restrict_univ] using
          (memLp_pi_iff.mp hut) i
      gradMemL2 := by
        intro j
        simpa [CKN.GradMemLpOn, CKN.MemLpOn, CKN.volumeOn, Measure.restrict_univ] using
          (memLp_pi_iff.mp ((memLp_pi_iff.mp hDt) i)) j
      hasWeakGradient := hW i }
    exact ⟨h, fun i x => rfl, fun i x j => rfl⟩
  have hSliceBound : ∀ t ∈ Ioo (0 : ℝ) T, ∀ i : Fin 3,
      eLpNorm (fun x : Vec3 => u (x, t) i) 2 volume ≤ ENNReal.ofReal (Real.sqrt E) := by
    intro t ht i
    rw [vorticity_eLpNorm_two_eq_sqrt ((hSlice t ht.1.le).eval i)]
    refine ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt ?_)
    refine le_trans ?_ (hkin t ⟨ht.1.le, ht.2.le⟩)
    exact Finset.single_le_sum (f := fun j : Fin 3 => ∫ x : Vec3, u (x, t) j ^ 2)
      (fun j _ => integral_nonneg fun x => sq_nonneg _) (Finset.mem_univ i)
  have hcomp := fun i : Fin 3 => forcedLerayLimit_component_tenThirds_slab u Du
    (ENNReal.ofReal (Real.sqrt E)) (ENNReal.ofReal G) T hSlices hSliceBound hUm hDm
    hGradBound ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top i
  have h103 : MemLp u (ENNReal.ofReal (10 / 3 : ℝ)) μ :=
    memLp_pi_iff.2 fun i => (hcomp i).1
  have h3le : (3 : ℝ≥0∞) ≤ ENNReal.ofReal (10 / 3 : ℝ) := by
    rw [show (3 : ℝ≥0∞) = ENNReal.ofReal 3 by norm_num]
    exact ENNReal.ofReal_le_ofReal (by norm_num)
  refine ⟨hu2 T hT, h103, ?_, fun i => (hcomp i).2⟩
  exact serrin_memLp_interpolate two_ne_zero ENNReal.ofReal_ne_top (by norm_num) h3le
    (hu2 T hT) h103

end CKN.Leray

end
