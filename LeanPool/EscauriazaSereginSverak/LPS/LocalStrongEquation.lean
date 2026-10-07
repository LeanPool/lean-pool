/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Leray.AssocPressureProviderLimit
public import LeanPool.CaffarelliKohnNirenberg.Leray.AssocPressureIntegrability
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedDirectRoute
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegUniformContracts
public import LeanPool.CaffarelliKohnNirenberg.Leray.RieszPressurePackageAgreement
public import LeanPool.CaffarelliKohnNirenberg.Leray.CompactnessFiniteRankCore
public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcePressureSlice
public import LeanPool.EscauriazaSereginSverak.LPS.GoodTimes
public import LeanPool.EscauriazaSereginSverak.LPS.H1EstimateSpatial
public import LeanPool.EscauriazaSereginSverak.LPS.LocalStrongSlices
public import LeanPool.EscauriazaSereginSverak.LPS.LocalStrongLimitAE
public import LeanPool.CaffarelliKohnNirenberg.Statements.IsInJ
public import LeanPool.CaffarelliKohnNirenberg.Statements.IsLerayHopfSolution
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.H1.Basic
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpaceTimeSet
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpaceTimeTestFunction

/-!
# The pressure-inclusive equation for the strong limit

The canonical double-Riesz pressure of a Leray--Hopf limit gives the
unrestricted-test weak momentum identity.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS.LPS

/-- The canonical associated pressure supplies the pressure-inclusive weak
momentum equation for a Leray--Hopf limit. -/
theorem lps_limit_pressure_inclusive_weak_equation
    {T : ℝ} {b : Vec3 → Vec3}
    {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3}
    (hLH : IsLerayHopfSolution T b u Du) :
    MemLp (CKN.Leray.associatedPressureForSolution hLH)
        (ENNReal.ofReal (5 / 3 : ℝ))
        (volume.restrict
          (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) ∧
      ∀ φ : ParabolicPoint → Vec3,
        φ ∈ spaceTimeTestFunction (V := Vec3)
          (Set.univ : Set Vec3) (Ioo 0 T) →
        ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T),
          (-(∑ i : Fin 3, u z i * timePartial (fun y => φ y i) z)
            - ∑ i : Fin 3, ∑ j : Fin 3,
              u z i * u z j * spatialPartial (fun y => φ y i) j z
            + ∑ i : Fin 3, ∑ j : Fin 3,
              Du z i j * spatialPartial (fun y => φ y i) j z
            - CKN.Leray.associatedPressureForSolution hLH z *
              ∑ i : Fin 3, spatialPartial (fun y => φ y i) i z) = 0 := by
  refine ⟨CKN.Leray.associatedPressureForSolution_memLp_fiveThirds hLH, ?_⟩
  exact CKN.Leray.associatedPressureForSolution_momentum_identity hLH

/-- If the velocity tensor has space-time `L²` components, the associated
double-Riesz pressure is also in space-time `L²`. -/
theorem lps_associatedPressure_memLp_two_of_tensor_memLp_two
    {T : ℝ} {b : Vec3 → Vec3}
    {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3}
    (hLH : IsLerayHopfSolution T b u Du)
    (hTensorTwo : ∀ i j : Fin 3,
      MemLp (CKN.Leray.associatedPressureTensor T u i j) 2
        (volume : Measure (Vec3 × ℝ))) :
    MemLp (CKN.Leray.associatedPressureForSolution hLH) 2
      (volume.restrict
        (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) := by
  let F := CKN.Leray.associatedPressureTensor T u
  let hFfive := CKN.Leray.associatedPressureTensor_memLp_fiveThirds hLH
  let hFtwo : ∀ i j, MemLp (F i j) (ENNReal.ofReal (2 : ℝ))
      (volume : Measure (Vec3 × ℝ)) := by
    intro i j
    simpa only [F,
      show ENNReal.ofReal (2 : ℝ) = (2 : ℝ≥0∞) by norm_num] using
      hTensorTwo i j
  let pTwo := CKN.Leray.rieszPressureSpaceTime (2 : ℝ) (by norm_num) F hFtwo
  have hpTwo : MemLp pTwo (ENNReal.ofReal (2 : ℝ))
      (volume : Measure (Vec3 × ℝ)) :=
    CKN.Leray.rieszPressureSpaceTime_memLp (2 : ℝ) (by norm_num) F hFtwo
  have hcross := CKN.Leray.rieszPressureSpaceTime_ae_eq_of_memLp_common
    (5 / 3 : ℝ) (by norm_num) (2 : ℝ) (by norm_num) F hFfive hFtwo
  have hcrossParabolic :
      (fun z : ParabolicPoint =>
        CKN.Leray.rieszPressureSpaceTime (5 / 3 : ℝ) (by norm_num)
          F hFfive (parabolicHomeomorph z)) =ᵐ[volume]
      fun z : ParabolicPoint => pTwo (parabolicHomeomorph z) :=
    parabolicHomeomorph_measurePreserving.quasiMeasurePreserving.ae hcross
  have hcrossSlab := ae_restrict_of_ae
    (s := spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)) hcrossParabolic
  have hpTwoParabolicRaw : MemLp
      (fun z : ParabolicPoint => pTwo (parabolicHomeomorph z))
      (ENNReal.ofReal (2 : ℝ))
      (volume : Measure ParabolicPoint) :=
    hpTwo.comp_measurePreserving parabolicHomeomorph_measurePreserving
  have hpTwoParabolic : MemLp
      (fun z : ParabolicPoint => pTwo (parabolicHomeomorph z)) 2
      (volume : Measure ParabolicPoint) := by
    simpa only [show ENNReal.ofReal (2 : ℝ) = (2 : ℝ≥0∞) by norm_num] using
      hpTwoParabolicRaw
  have hpTwoSlab := hpTwoParabolic.restrict
    (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))
  have hpressureEq :
      CKN.Leray.associatedPressureForSolution hLH =ᵐ[
        volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))]
        (fun z : ParabolicPoint => pTwo (parabolicHomeomorph z)) := by
    change (fun z : ParabolicPoint =>
      CKN.Leray.rieszPressureSpaceTime (5 / 3 : ℝ) (by norm_num)
        F hFfive (parabolicHomeomorph z)) =ᵐ[
        volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))]
      (fun z : ParabolicPoint => pTwo (parabolicHomeomorph z))
    exact hcrossSlab
  exact (memLp_congr_ae hpressureEq).2 hpTwoSlab

/-- The limit equation and the `L²` pressure estimate are packaged together
when the velocity tensor has square-integrable components. -/
theorem lps_limit_pressure_equation_with_l2_pressure
    {T : ℝ} {b : Vec3 → Vec3}
    {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3}
    (hLH : IsLerayHopfSolution T b u Du)
    (hTensorTwo : ∀ i j : Fin 3,
      MemLp (CKN.Leray.associatedPressureTensor T u i j) 2
        (volume : Measure (Vec3 × ℝ))) :
    MemLp (CKN.Leray.associatedPressureForSolution hLH) 2
      (volume.restrict
        (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) ∧
      (∀ φ : ParabolicPoint → Vec3,
        φ ∈ spaceTimeTestFunction (V := Vec3)
          (Set.univ : Set Vec3) (Ioo 0 T) →
        ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T),
          (-(∑ i : Fin 3, u z i * timePartial (fun y => φ y i) z)
            - ∑ i : Fin 3, ∑ j : Fin 3,
              u z i * u z j * spatialPartial (fun y => φ y i) j z
            + ∑ i : Fin 3, ∑ j : Fin 3,
              Du z i j * spatialPartial (fun y => φ y i) j z
            - CKN.Leray.associatedPressureForSolution hLH z *
              ∑ i : Fin 3, spatialPartial (fun y => φ y i) i z) = 0) := by
  exact ⟨lps_associatedPressure_memLp_two_of_tensor_memLp_two hLH hTensorTwo,
    (lps_limit_pressure_inclusive_weak_equation hLH).2⟩

/-- Uniform `H¹` bounds on every positive-time slice give space-time `L⁴`
velocity on a finite slab by the interpolation estimate in
`lem:lps-H1-estimate`. -/
theorem lps_velocity_memLp_four_of_uniform_h1_slices
    {T : ℝ} {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    (huMeas : AEStronglyMeasurable u
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
    (hGood : ∀ t : ℝ, t ∈ Ioo 0 T → ESS.IsLpsGoodTime u Du t)
    (B : ℝ≥0∞) (hB : B < ⊤)
    (huBound : ∀ t : ℝ, t ∈ Ioo 0 T →
      eLpNorm (fun x : Vec3 => u (x, t)) 2 volume ≤ B)
    (hDuBound : ∀ t : ℝ, t ∈ Ioo 0 T →
      eLpNorm (fun x : Vec3 => Du (x, t)) 2 volume ≤ B) :
    MemLp (fun z : Vec3 × ℝ => u (parabolicHomeomorph.symm z))
      (ENNReal.ofReal (4 : ℝ))
      (volume.restrict
        (parabolicHomeomorph.symm ⁻¹'
          spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) := by
  classical
  let C : ℝ≥0∞ :=
    3 * CKN.gagliardoNirenbergSobolevConstant ^ (3 / 4 : ℝ) *
      (2 : ℝ≥0∞) ^ (3 / 4 : ℝ) * B ^ (1 / 4 : ℝ) * B ^ (3 / 4 : ℝ)
  have hGNnot : CKN.gagliardoNirenbergSobolevConstant ≠ ⊤ :=
    (Classical.choose_spec CKN.sobolev_L6_global).1
  have hGN : CKN.gagliardoNirenbergSobolevConstant < ⊤ :=
    lt_top_iff_ne_top.mpr hGNnot
  have hGNpow : CKN.gagliardoNirenbergSobolevConstant ^ (3 / 4 : ℝ) < ⊤ :=
    ENNReal.rpow_lt_top_of_nonneg (by norm_num) hGN.ne
  have hBquarter : B ^ (1 / 4 : ℝ) < ⊤ :=
    ENNReal.rpow_lt_top_of_nonneg (by norm_num) hB.ne
  have hBthreeQuarter : B ^ (3 / 4 : ℝ) < ⊤ :=
    ENNReal.rpow_lt_top_of_nonneg (by norm_num) hB.ne
  have hC : C < ⊤ := by
    dsimp [C]
    have htwo : (2 : ℝ≥0∞) ^ (3 / 4 : ℝ) < ⊤ :=
      ENNReal.rpow_lt_top_of_nonneg (by norm_num)
        (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
    have hconst : (3 : ℝ≥0∞) *
        CKN.gagliardoNirenbergSobolevConstant ^ (3 / 4 : ℝ) *
        (2 : ℝ≥0∞) ^ (3 / 4 : ℝ) < ⊤ :=
      ENNReal.mul_lt_top (ENNReal.mul_lt_top (by norm_num) hGNpow) htwo
    exact ENNReal.mul_lt_top
      (ENNReal.mul_lt_top hconst hBquarter) hBthreeQuarter
  obtain ⟨u', hu'm, hae⟩ : ∃ u' : ParabolicPoint → Vec3, StronglyMeasurable u' ∧
      u =ᵐ[volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))] u' :=
    ⟨huMeas.mk u, huMeas.stronglyMeasurable_mk, huMeas.ae_eq_mk⟩
  let F : ParabolicPoint → ℝ≥0∞ := fun z => ‖u z‖ₑ ^ (4 : ℝ)
  let F' : ParabolicPoint → ℝ≥0∞ := fun z => ‖u' z‖ₑ ^ (4 : ℝ)
  have hF' : Measurable F' := by
    have := hu'm.measurable
    dsimp [F']
    fun_prop
  have hsliceRaw : ∀ t : ℝ, t ∈ Ioo 0 T →
      (∫⁻ x : Vec3, F (x, t) ∂volume) ≤ C ^ (4 : ℕ) := by
    intro t ht
    have hgood := hGood t ht
    have hu2 : MemLp (fun x : Vec3 => u (x, t)) 2 volume := by
      apply memLp_pi_iff.mpr
      intro i
      obtain ⟨h, hfun, _hgrad⟩ := hgood.1 i
      have hmem : MemLp h.toFun 2 volume := by
        simpa [CKN.MemL2On, CKN.MemLpOn, CKN.volumeOn, Measure.restrict_univ]
          using h.memL2
      simpa only [hfun] using hmem
    have hDu2 : MemLp (fun x : Vec3 => Du (x, t)) 2 volume := by
      apply memLp_pi_iff.mpr
      intro i
      apply memLp_pi_iff.mpr
      intro j
      obtain ⟨h, _hfun, hgrad⟩ := hgood.1 i
      have hmem : MemLp (fun x : Vec3 => h.grad x j) 2 volume := by
        simpa [CKN.GradMemL2On, CKN.MemL2On, CKN.MemLpOn,
          CKN.volumeOn, Measure.restrict_univ] using h.gradMemL2 j
      simpa only [hgrad] using hmem
    have hweak : ∀ i : Fin 3, HasWeakGradientOn (Set.univ : Set Vec3)
        (fun x => u (x, t) i) (fun x j => Du (x, t) i j) := by
      intro i
      obtain ⟨h, hfun, hgrad⟩ := hgood.1 i
      simpa only [hfun, hgrad] using h.hasWeakGradient
    have hinterp := ESS.lps_h1_vector_interpolation
      (s := (4 : ℝ)) (by norm_num) hu2 hDu2 hweak
    have hinterp' : eLpNorm (fun x : Vec3 => u (x, t))
        (ENNReal.ofReal (4 : ℝ)) volume ≤
        3 * CKN.gagliardoNirenbergSobolevConstant ^ (3 / 4 : ℝ) *
          (2 : ℝ≥0∞) ^ (3 / 4 : ℝ) *
            eLpNorm (fun x : Vec3 => u (x, t)) 2 volume ^ (1 / 4 : ℝ) *
              eLpNorm (fun x : Vec3 => Du (x, t)) 2 volume ^ (3 / 4 : ℝ) := by
      convert hinterp using 1 <;> norm_num
    have hinterpC : eLpNorm (fun x : Vec3 => u (x, t))
        (ENNReal.ofReal (4 : ℝ)) volume ≤ C := by
      dsimp [C]
      calc
        _ ≤ 3 * CKN.gagliardoNirenbergSobolevConstant ^ (3 / 4 : ℝ) *
            (2 : ℝ≥0∞) ^ (3 / 4 : ℝ) *
              eLpNorm (fun x : Vec3 => u (x, t)) 2 volume ^ (1 / 4 : ℝ) *
                eLpNorm (fun x : Vec3 => Du (x, t)) 2 volume ^ (3 / 4 : ℝ) := hinterp'
        _ ≤ 3 * CKN.gagliardoNirenbergSobolevConstant ^ (3 / 4 : ℝ) *
            (2 : ℝ≥0∞) ^ (3 / 4 : ℝ) * B ^ (1 / 4 : ℝ) * B ^ (3 / 4 : ℝ) := by
              gcongr
              · exact huBound t ht
              · exact hDuBound t ht
    have hsliceMeas : AEStronglyMeasurable
        (fun x : Vec3 => u (x, t)) volume := hu2.aestronglyMeasurable
    have hpower : eLpNorm (fun x : Vec3 => u (x, t))
        (ENNReal.ofReal (4 : ℝ)) volume ^ (4 : ℝ) =
        ∫⁻ x : Vec3, ‖u (x, t)‖ₑ ^ (4 : ℝ) ∂volume := by
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
        (by norm_num) ENNReal.ofReal_ne_top hsliceMeas,
        ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 4),
        ← ENNReal.rpow_mul, one_div,
        inv_mul_cancel₀ (by norm_num : (4 : ℝ) ≠ 0), ENNReal.rpow_one]
    calc
      ∫⁻ x : Vec3, F (x, t) ∂volume =
          eLpNorm (fun x : Vec3 => u (x, t))
            (ENNReal.ofReal (4 : ℝ)) volume ^ (4 : ℝ) := by
              simpa [F] using hpower.symm
      _ ≤ C ^ (4 : ℝ) := ENNReal.rpow_le_rpow hinterpC (by norm_num)
      _ = C ^ (4 : ℕ) := by norm_num [ENNReal.rpow_natCast]
  have hslices : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      (fun x : Vec3 => u (x, t)) =ᵐ[volume] fun x => u' (x, t) :=
    lps_slab_slice_ae_eq (a := 0) (b := T) hae
  have hfinite :
      (∫⁻ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T), F' z
        ∂(volume : Measure ParabolicPoint)) < ⊤ := by
    change (∫⁻ z in (Set.univ : Set Vec3) ×ˢ Ioo 0 T, F' z
      ∂(volume : Measure ParabolicPoint)) < ⊤
    rw [CKN.Leray.lintegral_parabolic_rectangle_eq_iterated
      (K := (Set.univ : Set Vec3)) (J := Ioo 0 T) F' hF']
    calc (∫⁻ t in Ioo 0 T, ∫⁻ x in (Set.univ : Set Vec3), F' (x, t) ∂volume ∂volume)
        ≤ ∫⁻ t in Ioo 0 T, C ^ (4 : ℕ) ∂volume := by
          refine lintegral_mono_ae ?_
          filter_upwards [hslices, ae_restrict_mem measurableSet_Ioo] with t hs ht
          simp only [setLIntegral_univ]
          calc (∫⁻ x, F' (x, t)) = ∫⁻ x, F (x, t) :=
                lintegral_congr_ae (hs.mono fun x hx => by simp only [F, F', hx])
            _ ≤ C ^ (4 : ℕ) := hsliceRaw t ht
      _ = C ^ (4 : ℕ) * volume (Ioo (0 : ℝ) T) := setLIntegral_const _ _
      _ < ⊤ := ENNReal.mul_lt_top (ENNReal.pow_lt_top hC) (by simp)
  have hphysical' : MemLp u' (ENNReal.ofReal (4 : ℝ))
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) := by
    rw [memLp_iff,
      eLpNorm_eq_lintegral_rpow_enorm_toReal
        (by norm_num) ENNReal.ofReal_ne_top
        (hu'm.aestronglyMeasurable)]
    have hfinite' : (∫⁻ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T),
        ‖u' z‖ₑ ^ (4 : ℝ)
          ∂(volume : Measure ParabolicPoint)) < ⊤ := by
      simpa only [F'] using hfinite
    simpa only [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 4)] using
      ENNReal.rpow_lt_top_of_nonneg (by norm_num) hfinite'.ne
  have hphysical : MemLp u (ENNReal.ofReal (4 : ℝ))
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) :=
    hphysical'.ae_eq hae.symm
  have hQ : MeasurableSet
      (parabolicHomeomorph.symm ⁻¹'
        spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)) := by
    exact (MeasurableSet.prod MeasurableSet.univ measurableSet_Ioo).preimage
      parabolicHomeomorph.symm.measurable
  have hmap := CKN.parabolicHomeomorphSymm_measurePreserving.restrict_preimage hQ
  exact hphysical.comp_measurePreserving hmap

/-- Space-time `L⁴` velocity gives an `L²` velocity tensor on the finite
slab, which is then extended by zero as in `thm:assoc-pressure`. -/
theorem lps_associatedPressure_tensor_memLp_two_of_velocity_memLp_four
    {T : ℝ} {u : ParabolicPoint → Vec3}
    (hU4 : MemLp
      (fun z : Vec3 × ℝ => u (parabolicHomeomorph.symm z))
      (ENNReal.ofReal (4 : ℝ))
      (volume.restrict
        (parabolicHomeomorph.symm ⁻¹'
          spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)))) :
    ∀ i j : Fin 3,
      MemLp (CKN.Leray.associatedPressureTensor T u i j) 2
        (volume : Measure (Vec3 × ℝ)) := by
  classical
  let Q : Set (Vec3 × ℝ) := parabolicHomeomorph.symm ⁻¹'
    spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)
  have hQ : MeasurableSet Q := by
    dsimp [Q]
    exact (MeasurableSet.prod MeasurableSet.univ measurableSet_Ioo).preimage
      parabolicHomeomorph.symm.measurable
  have hHolder : ENNReal.HolderTriple (ENNReal.ofReal (4 : ℝ))
      (ENNReal.ofReal (4 : ℝ)) (ENNReal.ofReal (2 : ℝ)) := by
    have h : Real.HolderTriple (4 : ℝ) 4 2 :=
      ⟨by norm_num, by norm_num, by norm_num⟩
    exact h.ennrealOfReal
  have : ENNReal.HolderTriple (ENNReal.ofReal (4 : ℝ))
      (ENNReal.ofReal (4 : ℝ)) (ENNReal.ofReal (2 : ℝ)) := hHolder
  intro i j
  have hi : MemLp (fun z : Vec3 × ℝ =>
      u (parabolicHomeomorph.symm z) i) (ENNReal.ofReal (4 : ℝ))
      (volume.restrict Q) := (memLp_pi_iff.mp hU4) i
  have hj : MemLp (fun z : Vec3 × ℝ =>
      u (parabolicHomeomorph.symm z) j) (ENNReal.ofReal (4 : ℝ))
      (volume.restrict Q) := (memLp_pi_iff.mp hU4) j
  have hproduct : MemLp (fun z : Vec3 × ℝ =>
      u (parabolicHomeomorph.symm z) i * u (parabolicHomeomorph.symm z) j)
      (ENNReal.ofReal (2 : ℝ)) (volume.restrict Q) := hi.mul hj
  rw [CKN.Leray.associatedPressureTensor,
    memLp_indicator_iff_restrict hQ]
  simpa only [show ENNReal.ofReal (2 : ℝ) = (2 : ℝ≥0∞) by norm_num] using hproduct

/-- The equation interface with the exact regularized uniform bounds and the
space-time `L⁴` velocity consequence supplied by compactness. The tensor
bound follows from the limit's uniform `H¹` slices. -/
theorem lps_strong_limit_pressure_equation
    (ρ : CKN.Leray.RegMollifierProfile)
    (b : Vec3 → Vec3) (Db : Vec3 → Fin 3 → Vec3)
    (hb : (∀ i : Fin 3, ∃ h : H1Function (Set.univ : Set Vec3),
        h.toFun = (fun x : Vec3 => b x i) ∧
        h.grad = (fun x : Vec3 => Db x i)) ∧ IsInJ b)
    (T M : ℝ) (hT : 0 < T) (hM : 0 ≤ M)
    (hUniformBounds :
      ∀ (ε : ℝ) (hε : 0 < ε),
        let Uε : ParabolicPoint → Vec3 :=
          CKN.Leray.regR12Velocity ρ ε hε b (by simpa using hb.2)
        let Dε : ParabolicPoint → Fin 3 → Vec3 := fun z i j =>
          spatialPartial (fun y => Uε y i) j z
        let D2ε : ParabolicPoint → Fin 3 → Fin 3 → Vec3 :=
          fun z i j => fun k => spatialPartial
            (fun y => spatialPartial (fun x => Uε x i) j y) k z
        (∀ t : ℝ, t ∈ Icc 0 T →
          ∫ x : Vec3,
            vec3EuclideanNorm (Uε (x, t)) ^ (2 : ℕ) +
              spatialGradientSq Uε Dε (x, t) ≤ M) ∧
        ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T),
          ∑ i : Fin 3, ∑ j : Fin 3,
            vec3EuclideanNorm (D2ε z i j) ^ (2 : ℕ) ≤ M)
    (σ : ℕ → ℕ) (hσ : StrictMono σ)
    {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3}
    (hweakSlice : ∀ t : ℝ, 0 < t → ∀ w : Vec3 → Vec3,
      MemLp w 2 volume →
      Tendsto
        (fun n => ∫ x : Vec3, ∑ i : Fin 3,
          CKN.Leray.regR12Uε ρ b hb.2
            (1 / ((σ n : ℝ) + 1)) (x, t) i * w x i)
        atTop (nhds (∫ x : Vec3, ∑ i : Fin 3, u (x, t) i * w x i)))
    (hrep : ∀ z : Vec3 × ℝ, 0 < z.2 →
      u (parabolicHomeomorph.symm z) =
        CKN.Leray.compactnessMollifiedLimit
          (fun n => fun y => CKN.Leray.regR12Uε ρ b hb.2
            (1 / ((σ n : ℝ) + 1)) (parabolicHomeomorph.symm y)) σ z)
    (hLH : IsLerayHopfSolution T b u Du) :
    MemLp (CKN.Leray.associatedPressureForSolution hLH) 2
      (volume.restrict
        (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) ∧
      (∀ φ : ParabolicPoint → Vec3,
        φ ∈ spaceTimeTestFunction (V := Vec3)
          (Set.univ : Set Vec3) (Ioo 0 T) →
        ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T),
          (-(∑ i : Fin 3, u z i * timePartial (fun y => φ y i) z)
            - ∑ i : Fin 3, ∑ j : Fin 3,
              u z i * u z j * spatialPartial (fun y => φ y i) j z
            + ∑ i : Fin 3, ∑ j : Fin 3,
              Du z i j * spatialPartial (fun y => φ y i) j z
            - CKN.Leray.associatedPressureForSolution hLH z *
              ∑ i : Fin 3, spatialPartial (fun y => φ y i) i z) = 0) := by
  obtain ⟨Dslice, hsliceData⟩ := lps_strong_limit_all_time_h1_slices
    ρ b Db hb T M hT hM hUniformBounds σ hσ hweakSlice hrep
  let B : ℝ≥0∞ := 9 * ENNReal.ofReal (Real.sqrt M)
  have hB : B < ⊤ := by
    dsimp [B]
    exact ENNReal.mul_lt_top (by norm_num) ENNReal.ofReal_lt_top
  have hGood : ∀ t : ℝ, t ∈ Ioo 0 T → ESS.IsLpsGoodTime u Dslice t := by
    intro t ht
    exact (hsliceData t ⟨ht.1, ht.2.le⟩).1
  have hUBound : ∀ t : ℝ, t ∈ Ioo 0 T →
      eLpNorm (fun x : Vec3 => u (x, t)) 2 volume ≤ B := by
    intro t ht
    exact (hsliceData t ⟨ht.1, ht.2.le⟩).2.1
  have hDsliceBound : ∀ t : ℝ, t ∈ Ioo 0 T →
      eLpNorm (fun x : Vec3 => Dslice (x, t)) 2 volume ≤ B := by
    intro t ht
    exact (hsliceData t ⟨ht.1, ht.2.le⟩).2.2
  exact lps_limit_pressure_equation_with_l2_pressure hLH
    (lps_associatedPressure_tensor_memLp_two_of_velocity_memLp_four
      (lps_velocity_memLp_four_of_uniform_h1_slices hLH.2.2.1 hGood B hB
        hUBound hDsliceBound))

end ESS.LPS

end
