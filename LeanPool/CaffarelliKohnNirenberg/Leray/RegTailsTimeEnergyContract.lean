/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegTailsMain
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegTailsSliceEstimates
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegTailsTimeEnergy

/-!
# Reg Tails Time Energy Contract

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

/-- The energy identity gives the time-integrated gradient profile and the
almost every slice identification needed in the flux estimates of
`lem:reg-tails`. -/
theorem regTails_contract_timeGradientBounds
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (a : Vec3 → Vec3) (ha : IsInJ a)
    (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (hR5 : ∀ t, 0 ≤ t →
      eLpNorm (regUniformVelocitySlice u t) 2 volume ^ (2 : ℕ) +
        2 * regUniformDissipation u D t =
      eLpNorm (regMollifyVector ρ ε hε (regUniformSpatialField a))
        2 volume ^ (2 : ℕ))
    (hDcont : ∀ i j, ContinuousOn (fun z : ParabolicPoint => D z i j)
      (spaceTimeSet Set.univ (Ioi (0 : ℝ))))
    (hU : ∀ t, 0 ≤ t → MemLp (fun x : Vec3 => u (x, t)) 2 volume)
    (hSpatialC1 : ∀ t, 0 < t → ∀ i : Fin 3,
      ContDiff ℝ (1 : ℕ∞) (fun x : Vec3 => u (x, t) i))
    (hDerivative : ∀ t, 0 < t → ∀ x i j,
      (fderiv ℝ (fun y : Vec3 => u (y, t) i) x) (basisVec j) =
        D (x, t) i j) :
    let Dplus : ParabolicPoint → Fin 3 → Vec3 := regTailsPositiveGradientExtension D
    let B : ℝ := (eLpNorm (regUniformSpatialField a) 2 volume).toReal
    let G : ℝ → ℝ := fun t => Real.sqrt
      (∫⁻ x : Vec3, ENNReal.ofReal (spatialGradientSq u Dplus (x, t)) ∂volume).toReal
    (∀ T : ℝ, 0 < T →
      MemLp G 2 (volume.restrict (Ioo (0 : ℝ) T)) ∧
        (∫ t in Ioo (0 : ℝ) T, G t ^ (2 : ℕ) ∂volume) ≤ B ^ (2 : ℕ) / 2 ∧
        ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) T)),
          (∫⁻ x : Vec3, ENNReal.ofReal
            (spatialGradientSq u Dplus (x, t)) ∂volume) ≠ ⊤) ∧
      ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))),
        (eLpNorm (fun x : Vec3 => Real.sqrt
          (spatialGradientSq u D (x, t))) 2 volume).toReal = G t := by
  dsimp only
  let S : Set ParabolicPoint := spaceTimeSet (Set.univ : Set Vec3) (Ioi (0 : ℝ))
  let Dplus : ParabolicPoint → Fin 3 → Vec3 := regTailsPositiveGradientExtension D
  let B : ℝ := (eLpNorm (regUniformSpatialField a) 2 volume).toReal
  let F : Vec3 × ℝ → ℝ := fun z => spatialGradientSq u Dplus (z.1, z.2)
  let G : ℝ → ℝ := fun t => Real.sqrt
    (∫⁻ x : Vec3, ENNReal.ofReal (F (x, t)) ∂volume).toReal
  have hEnergy := regTails_energy_bounds ρ ε hε a u D hR5 ha.1 hDcont hU
    hSpatialC1 hDerivative
  rcases hEnergy with ⟨_hSliceEnergy, hEnergyD, hH1⟩
  have hDplusMeas : Measurable Dplus := by
    simpa [Dplus, S] using regTails_positiveGradientExtension_measurable D hDcont
  have hFmeas : Measurable F := by
    dsimp [F]
    unfold spatialGradientSq
    fun_prop
  have hSopen : IsOpen S := by
    simpa [S] using isOpen_spaceTimeSet (Set.univ : Set Vec3) (Ioi (0 : ℝ))
      isOpen_univ isOpen_Ioi
  have hSmeas : MeasurableSet S := hSopen.measurableSet
  have hDplusEq (z : ParabolicPoint) (hz : z ∈ S) : Dplus z = D z := by
    simp [Dplus, regTailsPositiveGradientExtension, S, hz]
  have hEnergyDplus : 2 * (∫⁻ z, ENNReal.ofReal
      (spatialGradientSq u Dplus z) ∂regUniformPositiveTimeMeasure) ≤
      eLpNorm (regUniformSpatialField a) 2 volume ^ (2 : ℕ) := by
    have hAE : (fun z : ParabolicPoint => ENNReal.ofReal
        (spatialGradientSq u Dplus z)) =ᵐ[regUniformPositiveTimeMeasure]
        (fun z : ParabolicPoint => ENNReal.ofReal
          (spatialGradientSq u D z)) := by
      filter_upwards [ae_restrict_mem hSmeas] with z hz
      have hEq : spatialGradientSq u Dplus z = spatialGradientSq u D z := by
        unfold spatialGradientSq
        simp only [hDplusEq z hz]
      rw [hEq]
    have hLin := lintegral_congr_ae hAE
    rw [hLin]
    exact hEnergyD
  have hEnergyProduct : 2 * (∫⁻ z, ENNReal.ofReal (F z)
      ∂((volume : Measure Vec3).prod (volume.restrict (Ioi (0 : ℝ))))) ≤
      eLpNorm (regUniformSpatialField a) 2 volume ^ (2 : ℕ) := by
    change 2 * (∫⁻ z : ParabolicPoint, ENNReal.ofReal
      (spatialGradientSq u Dplus z)
      ∂((volume : Measure Vec3).prod (volume.restrict (Ioi (0 : ℝ))))) ≤ _
    rw [← regTails_positiveTimeMeasure_eq_product]
    exact hEnergyDplus
  have hFieldMem : MemLp (regUniformSpatialField a) 2 volume := by
    have hcoord : MemLp (fun x : L2Vec3 => a (WithLp.ofLp x)) 2 volume :=
      ha.1.comp_measurePreserving (PiLp.volume_preserving_ofLp (Fin 3))
    exact hcoord.continuousLinearMap_comp
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toContinuousLinearMap
  have hBfinite : eLpNorm (regUniformSpatialField a) 2 volume ≠ ⊤ :=
    hFieldMem.eLpNorm_ne_top
  have hBidentity : eLpNorm (regUniformSpatialField a) 2 volume = ENNReal.ofReal B :=
    (ENNReal.ofReal_toReal hBfinite).symm
  have hEnergyReal : 2 * (∫⁻ z, ENNReal.ofReal (F z)
      ∂((volume : Measure Vec3).prod (volume.restrict (Ioi (0 : ℝ))))) ≤
      ENNReal.ofReal (B ^ (2 : ℕ)) := by
    rw [hBidentity] at hEnergyProduct
    simpa [ENNReal.ofReal_pow, B] using hEnergyProduct
  have hTime := regTails_timeGradientNorm_sq_integral_bound
    F hFmeas hEnergyReal
  have hSliceProfile : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))),
      (eLpNorm (fun x : Vec3 => Real.sqrt
        (spatialGradientSq u D (x, t))) 2 volume).toReal = G t := by
    filter_upwards [hH1, ae_restrict_mem measurableSet_Ioi] with t hH1t ht
    rcases hH1t with ⟨h, _, hGradients⟩
    have hprofile := regTails_gradient_slice_norm_eq_profile u D t ht hDcont h
      hGradients
    have hFprofile :
        (∫⁻ x : Vec3, ENNReal.ofReal (F (x, t)) ∂volume) =
          ∫⁻ x : Vec3, ENNReal.ofReal
            (spatialGradientSq u D (x, t)) ∂volume := by
      apply lintegral_congr
      intro x
      have hz : parabolicHomeomorph.symm (x, t) ∈ S := by
        change (parabolicHomeomorph.symm (x, t)).1 ∈ (Set.univ : Set Vec3) ∧
          (parabolicHomeomorph.symm (x, t)).2 ∈ Ioi (0 : ℝ)
        simpa only [parabolicHomeomorph_symm_apply, Prod.fst, Prod.snd,
          Set.mem_univ, true_and] using ht
      change ENNReal.ofReal
          (spatialGradientSq u Dplus (parabolicHomeomorph.symm (x, t))) =
        ENNReal.ofReal (spatialGradientSq u D (parabolicHomeomorph.symm (x, t)))
      unfold spatialGradientSq
      rw [hDplusEq (parabolicHomeomorph.symm (x, t)) hz]
    rw [hprofile]
    dsimp [G]
    rw [← hFprofile]
  refine ⟨?_, hSliceProfile⟩
  intro T hT
  have hT' := hTime T hT
  simpa [G, F] using hT'

end CKN.Leray

end
