/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.LerayLimitMain

/-!
# Leray Limit Ten Thirds

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Filter Set
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

variable (ρ : RegMollifierProfile)
variable (uε : (a : Vec3 → Vec3) → IsInJ a → ℝ → ParabolicPoint → Vec3)
variable (pε : (a : Vec3 → Vec3) → IsInJ a → ℝ → ParabolicPoint → ℝ)



theorem lerayLimit_regularised_component_tenThirds
    (hregularised : ∀ (a : Vec3 → Vec3) (ha : IsInJ a) (ε : ℝ)
    (hε : 0 < ε),
    let u := uε a ha ε
    let p := pε a ha ε
    let D : ParabolicPoint → Fin 3 → Vec3 := fun z i j =>
      spatialPartial (fun y => u y i) j z
    let DD : ParabolicPoint → Fin 3 → Fin 3 → Vec3 := fun z i j k =>
      spatialPartial (fun y => spatialPartial (fun x => u x i) j y) k z
    let Dt : ParabolicPoint → Vec3 := fun z i => timePartial (fun y => u y i) z
    let Dp : ParabolicPoint → Vec3 := fun z i => spatialPartial (fun y => p y) i z
    (∃ hSlice : ∀ t : ℝ, 0 ≤ t → MemLp (fun x : Vec3 => u (x, t)) 2 volume,
      Continuous (fun t : Set.Ici (0 : ℝ) =>
        realVectorL2OfCoordinateFunction
          (fun x : Vec3 => u (x, t.1)) (hSlice t.1 t.2)) ∧
      (fun x : Vec3 => u (x, 0)) =ᵐ[volume]
        regUniformMollifiedInitial ρ ε hε a ∧
      ∀ t : ℝ, 0 ≤ t → CKN.IsWeakDivFreeL2 (fun x => u (x, t))) ∧
    (∀ i : Fin 3, ContinuousOn (fun z => u z i)
      (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0))) ∧
    (∀ i j, ContinuousOn (fun z => D z i j)
      (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0))) ∧
    (∀ i j k, ContinuousOn (fun z => DD z i j k)
      (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0))) ∧
    (∀ i, ContinuousOn (fun z => Dt z i)
      (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0))) ∧
    ContinuousOn p (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)) ∧
    (∀ i, ContinuousOn (fun z => Dp z i)
      (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0))) ∧
    (letI : TopologicalSpace ParabolicPoint := instTopologicalSpaceProd
     letI : NormedAddCommGroup ParabolicPoint :=
       inferInstanceAs (NormedAddCommGroup (Vec3 × ℝ))
     letI : NormedSpace ℝ ParabolicPoint :=
       inferInstanceAs (NormedSpace ℝ (Vec3 × ℝ))
     ∀ i, ContDiffOn ℝ 1 (fun z => u z i)
       (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0))) ∧
    (∀ z ∈ spaceTimeSet (Set.univ : Set Vec3) (Ioi 0), ∀ i j,
      DifferentiableAt ℝ (fun x : Vec3 => D (x, z.2) i j) z.1) ∧
    (∀ z ∈ spaceTimeSet (Set.univ : Set Vec3) (Ioi 0),
      DifferentiableAt ℝ (fun x : Vec3 => p (x, z.2)) z.1) ∧
    (∀ δ T : ℝ, 0 < δ → δ < T →
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ z ∈ spaceTimeSet (Set.univ : Set Vec3) (Icc δ T),
          vec3EuclideanNorm (u z) ≤ C ∧ |p z| ≤ C ∧
          (∀ i j, |D z i j| ≤ C) ∧
          (∀ i j k, |DD z i j k| ≤ C) ∧
          (∀ i, |Dt z i| ≤ C) ∧ (∀ i, |Dp z i| ≤ C)) ∧
    (∀ δ T : ℝ, 0 < δ → δ < T →
      (∀ i, MemLp (fun z : ParabolicPoint => u z i) 2
        (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo δ T)))) ∧
      (∀ i j, MemLp (fun z : ParabolicPoint => D z i j) 2
        (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo δ T)))) ∧
      (∀ i j k, MemLp (fun z : ParabolicPoint => DD z i j k) 2
        (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo δ T)))) ∧
      (∀ i, MemLp (fun z : ParabolicPoint => Dt z i) 2
        (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo δ T)))) ∧
      MemLp p 2 (volume.restrict
        (spaceTimeSet (Set.univ : Set Vec3) (Ioo δ T)))) ∧
    (∀ z : ParabolicPoint, 0 < z.2 → ∀ i : Fin 3,
      Dt z i - (∑ j : Fin 3, DD z i j j) +
        (∑ j : Fin 3,
          regUniformMollifiedVelocity ρ ε hε u z j * D z i j) + Dp z i = 0) ∧
    (∀ t : ℝ, 0 < t →
      ∃ hF : ∀ i j : Fin 3, MemLp
        (fun x : Vec3 => regUniformMollifiedVelocity ρ ε hε u (x, t) i *
          u (x, t) j) (ENNReal.ofReal 2) volume,
        (fun x : Vec3 => p (x, t)) =ᵐ[volume]
          rieszPressureSliceRepresentative 2 (by norm_num)
            (fun i j => (hF i j).toLp
              (fun x : Vec3 => regUniformMollifiedVelocity ρ ε hε u
                (x, t) i * u (x, t) j)) ∧
        ∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
          (∫ x : Vec3, p (x, t) * spatialLaplacian ψ x) =
            -∑ i : Fin 3, ∑ j : Fin 3,
              ∫ x : Vec3, regUniformMollifiedVelocity ρ ε hε u (x, t) i *
                u (x, t) j * mixedSecond ψ i j x) ∧
    (∀ t : ℝ, 0 ≤ t →
      eLpNorm (regUniformVelocitySlice u t) 2 volume ^ (2 : ℕ) +
        2 * regUniformDissipation u D t =
      eLpNorm (regMollifyVector ρ ε hε (regUniformSpatialField a))
            2 volume ^ (2 : ℕ)))
    (a : Vec3 → Vec3) (ha : IsInJ a) (ε : ℝ) (hε : 0 < ε)
    (i : Fin 3) :
    MemLp (fun z : ParabolicPoint => uε a ha ε z i)
        (ENNReal.ofReal (10 / 3 : ℝ))
        (volume.restrict (spaceTimeSet Set.univ (Ioi (0 : ℝ)))) ∧
      eLpNorm (fun z : ParabolicPoint => uε a ha ε z i)
          (ENNReal.ofReal (10 / 3 : ℝ))
          (volume.restrict (spaceTimeSet Set.univ (Ioi (0 : ℝ)))) ^
            (10 / 3 : ℝ) ≤
        (CKN.gagliardoNirenbergSobolevConstant ^ (3 / 5 : ℝ)) ^
            (10 / 3 : ℝ) *
          eLpNorm (regUniformSpatialField a) 2 volume ^ (4 / 3 : ℝ) *
          (∫⁻ t in Ioi (0 : ℝ), ∫⁻ x : Vec3,
            ENNReal.ofReal (spatialGradientSq
              (uε a ha ε) (fun z i j =>
                spatialPartial (fun y => uε a ha ε y i) j z) (x, t))
              ∂volume ∂volume) := by
  classical
  let U : ParabolicPoint → Vec3 := uε a ha ε
  let D : ParabolicPoint → Fin 3 → Vec3 := fun z i j =>
    spatialPartial (fun y => U y i) j z
  let P : Set ParabolicPoint := spaceTimeSet Set.univ (Ioi 0)
  let Ubar : ParabolicPoint → Vec3 :=
    P.piecewise U (fun z => regUniformMollifiedInitial ρ ε hε a z.1)
  let Dbar : ParabolicPoint → Fin 3 → Vec3 := P.piecewise D (fun _ => 0)
  have hData := lerayLimit_regularised_basic_data
    (ρ := ρ) (uε := uε) (pε := pε)
    (hregularised := hregularised) a ha ε hε
  have hUcont := hData.2.1
  have hDcont := hData.2.2.1
  have hR := hregularised a ha ε hε
  have hUbarPos (x : Vec3) (t : ℝ) (ht : 0 < t) :
      Ubar (x, t) = U (x, t) := by
    change P.piecewise U
      (fun z => regUniformMollifiedInitial ρ ε hε a z.1)
        ((x, t) : ParabolicPoint) = U (x, t)
    rw [Set.piecewise_eq_of_mem P U
      (fun z => regUniformMollifiedInitial ρ ε hε a z.1)
      (show ((x, t) : ParabolicPoint) ∈ P by
        change x ∈ Set.univ ∧ 0 < t
        exact ⟨Set.mem_univ _, ht⟩)]
  have hDbarPos (x : Vec3) (t : ℝ) (ht : 0 < t) (i j : Fin 3) :
      Dbar (x, t) i j = D (x, t) i j := by
    change P.piecewise D (fun _ => 0)
      ((x, t) : ParabolicPoint) i j = D (x, t) i j
    rw [Set.piecewise_eq_of_mem P D (fun _ => 0)
      (show ((x, t) : ParabolicPoint) ∈ P by
      change x ∈ Set.univ ∧ 0 < t
      exact ⟨Set.mem_univ _, ht⟩)]
  have hPmeas : MeasurableSet P := by
    change MeasurableSet (Set.univ ×ˢ Ioi (0 : ℝ))
    exact MeasurableSet.prod MeasurableSet.univ measurableSet_Ioi
  have hUbarCont : ContinuousOn U P := by
    apply continuousOn_pi.mpr
    intro j
    simpa [U] using hUcont j
  have hInitialCont : Continuous
      (fun z : ParabolicPoint => regUniformMollifiedInitial ρ ε hε a z.1) := by
    exact (regUniformMollifiedInitial_contDiff ρ ε hε ha).continuous.comp
      continuous_fst_parabolicPoint
  have hUbarMeas : Measurable Ubar := by
    exact lerayLimit_measurableOn_extension P hPmeas U
      (fun z => regUniformMollifiedInitial ρ ε hε a z.1) hUbarCont
      (hInitialCont.continuousOn.mono (Set.subset_univ (Pᶜ)))
  have hDcont' : ContinuousOn D P := by
    apply continuousOn_pi.mpr
    intro j
    apply continuousOn_pi.mpr
    intro k
    simpa [D, U] using hDcont j k
  have hDbarMeas : Measurable Dbar := by
    exact lerayLimit_measurableOn_extension P hPmeas D
      (fun _ => 0) hDcont' continuousOn_const
  have hEnergyBounds := lerayLimit_regularised_energy_bounds
    ρ a ha ε hε U D hUcont hDcont hData.2.2.2
  have hA : MemLp (regUniformSpatialField a) 2 volume :=
    lerayHopfLimit_initialField_memLp a ha.1
  have hEnergyTop :
      eLpNorm (regUniformSpatialField a) 2 volume ^ (2 : ℕ) < ⊤ := by
    finiteness
  have hEnergyGradient :
      (∫⁻ t in Ioi (0 : ℝ), ∫⁻ x : Vec3,
        ENNReal.ofReal (spatialGradientSq Ubar Dbar (x, t))
          ∂volume ∂volume) ≤ eLpNorm (regUniformSpatialField a) 2 volume ^ (2 : ℕ) := by
    simpa [lerayLimitPiecewise, P, Ubar, D, Dbar] using hEnergyBounds.2.2
  let G : ℝ≥0∞ := ∫⁻ t in Ioi (0 : ℝ), ∫⁻ x : Vec3,
    ENNReal.ofReal (spatialGradientSq Ubar Dbar (x, t)) ∂volume ∂volume
  have hGfinite : G < ⊤ := lt_of_le_of_lt hEnergyGradient hEnergyTop
  have hSlicesRaw := lerayLimit_regularised_h1_slices
    (ρ := ρ) (uε := uε) (pε := pε)
    (hregularised := hregularised) a ha ε hε
  have hSlicesBar : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))),
      ∃ h : ∀ _i : Fin 3, CKN.H1Function (Set.univ : Set Vec3),
        (∀ i x, (h i).toFun x = Ubar (x, t) i) ∧
        (∀ i x j, (h i).grad x j = Dbar (x, t) i j) := by
    filter_upwards [hSlicesRaw, ae_restrict_mem measurableSet_Ioi]
      with t hS htmem
    have ht : 0 < t := htmem
    rcases hS with ⟨h, hvalue, hgradient⟩
    refine ⟨h, ?_, ?_⟩
    · intro j x
      calc
        (h j).toFun x = U (x, t) j := hvalue j x
        _ = Ubar (x, t) j := congrArg (fun v : Vec3 => v j)
          (hUbarPos x t ht).symm
    · intro j x k
      calc
        (h j).grad x k = D (x, t) j k := hgradient j x k
        _ = Dbar (x, t) j k := (hDbarPos x t ht j k).symm
  have hUbarSlice : ∀ t : ℝ, 0 ≤ t →
      MemLp (fun x : Vec3 => Ubar (x, t)) 2 volume := by
    intro t ht
    by_cases ht0 : t = 0
    · subst t
      have hInit : MemLp (regUniformMollifiedInitial ρ ε hε a) 2 volume :=
        (regMollifiedInitial_isInJ ρ ε hε ha).1
      have hEq : (fun x : Vec3 => Ubar (x, 0)) =ᵐ[volume]
          regUniformMollifiedInitial ρ ε hε a := by
        filter_upwards [] with x
        change P.piecewise U
          (fun z => regUniformMollifiedInitial ρ ε hε a z.1)
          ((x, 0) : ParabolicPoint) =
          regUniformMollifiedInitial ρ ε hε a x
        have hxnot : ((x, (0 : ℝ)) : ParabolicPoint) ∉ P := by
          change ¬ (x ∈ Set.univ ∧ 0 < (0 : ℝ))
          simp
        rw [Set.piecewise_eq_of_notMem P U
          (fun z => regUniformMollifiedInitial ρ ε hε a z.1) hxnot]
      exact (memLp_congr_ae hEq).2 hInit
    · have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
      have hEq : (fun x : Vec3 => Ubar (x, t)) = fun x => U (x, t) := by
        funext x
        exact hUbarPos x t htpos
      rw [hEq]
      exact hData.1 t ht
  have hSliceBound : ∀ t : ℝ, 0 < t → ∀ j : Fin 3,
      eLpNorm (fun x : Vec3 => Ubar (x, t) j) 2 volume ≤
        eLpNorm (regUniformSpatialField a) 2 volume := by
    intro t ht j
    have henergy :
        eLpNorm (regUniformVelocitySlice Ubar t) 2 volume ^ (2 : ℕ) ≤
          eLpNorm (regUniformSpatialField a) 2 volume ^ (2 : ℕ) := by
      simpa [lerayLimitPiecewise, P, Ubar, D, Dbar] using
        hEnergyBounds.1 t (le_of_lt ht)
    have hvectorBound :
        eLpNorm (regUniformVelocitySlice Ubar t) 2 volume ≤
          eLpNorm (regUniformSpatialField a) 2 volume :=
      (ENNReal.pow_le_pow_left_iff (by norm_num : (2 : ℕ) ≠ 0)).mp henergy
    have hS : MemLp (regUniformVelocitySlice Ubar t) 2 volume := by
      have hcoord : MemLp (fun x : L2Vec3 => Ubar (WithLp.ofLp x, t))
          2 volume :=
        (hUbarSlice t (le_of_lt ht)).comp_measurePreserving
          (PiLp.volume_preserving_ofLp (Fin 3))
      exact hcoord.continuousLinearMap_comp
        (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toContinuousLinearMap
    have hchange := eLpNorm_comp_measurePreserving
      (p := (2 : ℝ≥0∞))
      (f := (WithLp.toLp 2 : Vec3 → L2Vec3))
      hS.aestronglyMeasurable vec3ToL2Vec3_measurePreserving
    have hvectorEq :
        eLpNorm (fun x : Vec3 => WithLp.toLp 2 (Ubar (x, t))) 2 volume =
          eLpNorm (regUniformVelocitySlice Ubar t) 2 volume := by
      have hfun : (fun x : Vec3 => WithLp.toLp 2 (Ubar (x, t))) =
          fun x => regUniformVelocitySlice Ubar t (WithLp.toLp 2 x) := by
        funext x
        simp [regUniformVelocitySlice]
      rw [hfun]
      exact hchange
    have hcomponent :
        eLpNorm (fun x : Vec3 => Ubar (x, t) j) 2 volume ≤
          eLpNorm (fun x : Vec3 => WithLp.toLp 2 (Ubar (x, t))) 2 volume := by
      apply eLpNorm_mono_ae (p := (2 : ℝ≥0∞))
        ((memLp_pi_iff.mp (hUbarSlice t (le_of_lt ht))) j).aestronglyMeasurable
      filter_upwards [] with x
      calc
        ‖Ubar (x, t) j‖ ≤ ‖Ubar (x, t)‖ := norm_le_pi_norm _ _
        _ ≤ vec3EuclideanNorm (Ubar (x, t)) :=
          CKN.Foundation.Parabolic.norm_le_vec3EuclideanNorm _
        _ = ‖WithLp.toLp 2 (Ubar (x, t))‖ := vec3EuclideanNorm_eq_l2 _
    exact hcomponent.trans (hvectorEq ▸ hvectorBound)
  have hRegResult := regUniform_component_memLp_tenThirds
    Ubar Dbar (eLpNorm (regUniformSpatialField a) 2 volume) G
    hSlicesBar hSliceBound hUbarMeas hDbarMeas
    (by rfl) hA.eLpNorm_lt_top hGfinite i
  have hRawEq : (fun z : ParabolicPoint => Ubar z i) =ᵐ[
      volume.restrict (spaceTimeSet Set.univ (Ioi (0 : ℝ)))]
      fun z => U z i := by
    filter_upwards [ae_restrict_mem hPmeas] with z hz
    rcases z with ⟨x, t⟩
    have ht : 0 < t := hz.2
    have heq := hUbarPos x t ht
    simpa using congrArg (fun v : Vec3 => v i) heq
  have hMemRaw : MemLp (fun z : ParabolicPoint => U z i)
      (ENNReal.ofReal (10 / 3 : ℝ))
      (volume.restrict (spaceTimeSet Set.univ (Ioi (0 : ℝ)))) :=
    (memLp_congr_ae hRawEq).mp hRegResult.1
  have hNormRaw : eLpNorm (fun z : ParabolicPoint => U z i)
      (ENNReal.ofReal (10 / 3 : ℝ))
      (volume.restrict (spaceTimeSet Set.univ (Ioi (0 : ℝ)))) =
        eLpNorm (fun z : ParabolicPoint => Ubar z i)
          (ENNReal.ofReal (10 / 3 : ℝ))
          (volume.restrict (spaceTimeSet Set.univ (Ioi (0 : ℝ)))) :=
    eLpNorm_congr_ae hRawEq.symm
  have hGraw : G = ∫⁻ t in Ioi (0 : ℝ), ∫⁻ x : Vec3,
      ENNReal.ofReal (spatialGradientSq U D (x, t)) ∂volume ∂volume := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    apply lintegral_congr_ae
    filter_upwards [] with x
    congr 1
    unfold spatialGradientSq
    have hD : Dbar (x, t) = D (x, t) := by
      funext j
      funext k
      exact hDbarPos x t ht j k
    rw [hD]
  refine ⟨hMemRaw, ?_⟩
  rw [hNormRaw]
  rw [← hGraw]
  exact hRegResult.2


end CKN.Leray

end
