/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.ParabolicMeasure
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Measure.SliceGradientSelection
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.BallBasics
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpatialPartial
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.SpecificCodomains.Pi
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import LeanPool.CaffarelliKohnNirenberg.Setting.Energy.Calculus
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import LeanPool.CaffarelliKohnNirenberg.Foundation.SpaceTimeMollifier
public import LeanPool.CaffarelliKohnNirenberg.Foundation.WeakDerivMollify

/-!
# Local Energy Weak Gradient

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN

private def energySpatialDir (j : Fin 3) : Vec3 × ℝ := (basisVec j, 0)

/-- The local energy bound makes velocity and weak gradient square integrable on the cylinder.
This is the `L²` input for local mollification. -/
theorem energyL2_components_memLp
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    (hu : AEStronglyMeasurable u
      (volume.restrict (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))))
    (hDu : AEStronglyMeasurable Du
      (volume.restrict (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))))
    (henergy : (∫⁻ z in spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0),
      ‖u z‖ₑ ^ (2 : ℝ) + ‖Du z‖ₑ ^ (2 : ℝ)) < ⊤) :
    MemLp u 2 (volume.restrict (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))) ∧
      MemLp Du 2
        (volume.restrict (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))) := by
  have huFin : (∫⁻ z in spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0),
      ‖u z‖ₑ ^ (2 : ℝ)) < ⊤ := by
    refine lt_of_le_of_lt ?_ henergy
    apply lintegral_mono
    intro z
    exact le_add_of_nonneg_right (by positivity)
  have hDuFin : (∫⁻ z in spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0),
      ‖Du z‖ₑ ^ (2 : ℝ)) < ⊤ := by
    refine lt_of_le_of_lt ?_ henergy
    apply lintegral_mono
    intro z
    exact le_add_of_nonneg_left (by positivity)
  constructor
  · rw [memLp_iff, eLpNorm_eq_lintegral_rpow_enorm_toReal
      (by norm_num) (by norm_num) hu]
    simp only [ENNReal.toReal_ofNat]
    exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) huFin.ne
  · rw [memLp_iff, eLpNorm_eq_lintegral_rpow_enorm_toReal
      (by norm_num) (by norm_num) hDu]
    simp only [ENNReal.toReal_ofNat]
    exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hDuFin.ne

/-- Slice weak gradients give the space-time integration-by-parts identity on the full local
cylinder. This is the product-coordinate form used by the mollified-gradient argument. -/
theorem essLocal_sliceGradient_integrationByParts
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    (hu : AEStronglyMeasurable u
      (volume.restrict (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))))
    (hDu : AEStronglyMeasurable Du
      (volume.restrict (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))))
    (henergy : (∫⁻ z in spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0),
      ‖u z‖ₑ ^ (2 : ℝ) + ‖Du z‖ₑ ^ (2 : ℝ)) < ⊤)
    (hgrad : ∀ᵐ t ∂(volume.restrict (Ioo (-1) 0)), ∀ i : Fin 3,
      HasWeakGradientOn (vec3Ball (0 : Vec3) 1)
        (fun x => u (x, t) i) (fun x => Du (x, t) i))
    {ψ : Vec3 × ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ)
    (hψsupport : tsupport ψ ⊆ vec3Ball (0 : Vec3) 1 ×ˢ Ioo (-1) 0)
    (i j : Fin 3) :
    ∫ z in vec3Ball (0 : Vec3) 1 ×ˢ Ioo (-1) 0,
      u z i * spatialPartial (show ParabolicPoint → ℝ from ψ) j z =
      -∫ z in vec3Ball (0 : Vec3) 1 ×ˢ Ioo (-1) 0,
        Du z i j * ψ z := by
  let B : Set Vec3 := vec3Ball (0 : Vec3) 1
  let J : Set ℝ := Ioo (-1) 0
  let U : Set ParabolicPoint := spaceTimeSet B J
  let Up : Set (Vec3 × ℝ) := B ×ˢ J
  have hparaMeas : MeasurableSet U := by
    have hUopen : IsOpen U := by
      dsimp [U, B, J]
      exact isOpen_spaceTimeSet _ _ (isOpen_vec3Ball (0 : Vec3) 1) isOpen_Ioo
    exact hUopen.measurableSet
  have hprodMeas : MeasurableSet Up := by
    exact (isOpen_vec3Ball (0 : Vec3) 1).measurableSet.prod measurableSet_Ioo
  have hpre : parabolicHomeomorph.symm ⁻¹' U = Up := by
    ext z
    rfl
  have hmp := parabolicHomeomorphSymm_measurePreserving.restrict_preimage hparaMeas
  rw [hpre] at hmp
  rcases energyL2_components_memLp hu hDu henergy with ⟨hu2, hDu2⟩
  have hu_i : MemLp (fun z : ParabolicPoint => u z i) 2 (volume.restrict U) :=
    (memLp_pi_iff.mp hu2) i
  have hDu_i : MemLp (fun z : ParabolicPoint => Du z i) 2 (volume.restrict U) :=
    (memLp_pi_iff.mp hDu2) i
  have hDu_ij : MemLp (fun z : ParabolicPoint => Du z i j) 2
      (volume.restrict U) := (memLp_pi_iff.mp hDu_i) j
  have hBclosure : IsCompact (closure B) := by
    simpa [B] using (isCompact_closure_vec3Ball
      (x := (0 : Vec3)) (r := (1 : ℝ)) (by norm_num))
  have hK : IsCompact (closure B ×ˢ Set.Icc (-1 : ℝ) 0) := hBclosure.prod isCompact_Icc
  have hUK : Up ⊆ closure B ×ˢ Set.Icc (-1 : ℝ) 0 := by
    exact Set.prod_mono subset_closure (by
      intro t ht
      exact ⟨le_of_lt ht.1, le_of_lt ht.2⟩)
  have hUprodMeas : MeasurableSet Up := by simpa [Up, B, J] using hprodMeas
  have hUpFinite : (volume : Measure (Vec3 × ℝ)) Up < ⊤ :=
    lt_of_le_of_lt (measure_mono hUK) hK.measure_lt_top
  let _ : IsFiniteMeasure ((volume : Measure (Vec3 × ℝ)).restrict Up) := ⟨by
    rw [Measure.restrict_apply_univ Up]
    exact hUpFinite
  ⟩
  have huProd : IntegrableOn (fun z : Vec3 × ℝ => u z i) Up
      (volume : Measure (Vec3 × ℝ)) := by
    have hm : MemLp (fun z : Vec3 × ℝ => u z i) 2
        ((volume : Measure (Vec3 × ℝ)).restrict Up) := by
      have h := hu_i.comp_measurePreserving hmp
      change MemLp (fun z : Vec3 × ℝ => u (parabolicHomeomorph.symm z) i) 2
        ((volume : Measure (Vec3 × ℝ)).restrict Up) at h
      have hfun : (fun z : Vec3 × ℝ => u (parabolicHomeomorph.symm z) i) =
          (fun z => u z i) := by
        funext z
        cases z
        rfl
      rw [hfun] at h
      exact h
    exact hm.integrable (by norm_num)
  have hDuProd : IntegrableOn (fun z : Vec3 × ℝ => Du z i j) Up
      (volume : Measure (Vec3 × ℝ)) := by
    have hm : MemLp (fun z : Vec3 × ℝ => Du z i j) 2
        ((volume : Measure (Vec3 × ℝ)).restrict Up) := by
      have h := hDu_ij.comp_measurePreserving hmp
      change MemLp (fun z : Vec3 × ℝ => Du (parabolicHomeomorph.symm z) i j) 2
        ((volume : Measure (Vec3 × ℝ)).restrict Up) at h
      have hfun : (fun z : Vec3 × ℝ => Du (parabolicHomeomorph.symm z) i j) =
          (fun z => Du z i j) := by
        funext z
        cases z
        rfl
      rw [hfun] at h
      exact h
    exact hm.integrable (by norm_num)
  have hψpartial : Continuous (fun z : Vec3 × ℝ =>
      spatialPartial (show ParabolicPoint → ℝ from ψ) j z) :=
    (spatialPartial_contDiff hψ j).continuous
  have hF : IntegrableOn
      (fun z : Vec3 × ℝ => u z i *
        spatialPartial (show ParabolicPoint → ℝ from ψ) j z)
      Up (volume : Measure (Vec3 × ℝ)) := by
    exact huProd.mul_continuousOn_of_subset hψpartial.continuousOn
      hUprodMeas hK hUK
  have hH : IntegrableOn
      (fun z : Vec3 × ℝ => Du z i j * ψ z) Up
      (volume : Measure (Vec3 × ℝ)) := by
    exact hDuProd.mul_continuousOn_of_subset hψ.continuous.continuousOn
      hUprodMeas hK hUK
  have hpair : ∀ᵐ t ∂(volume.restrict J),
      (∫ x in B, u (x, t) i *
        spatialPartial (show ParabolicPoint → ℝ from ψ) j (x, t)) =
      -(∫ x in B, Du (x, t) i j * ψ (x, t)) := by
    filter_upwards [hgrad] with t ht
    have hs := CKN.slice_testFunction hψ hψc hψsupport t
    have hweak := ht i j (fun x : Vec3 => ψ (x, t)) hs.1 hs.2.1 hs.2.2
    simpa only [CKN.spatialPartial] using hweak
  have hiter :
      (∫ t in J, ∫ x in B, u (x, t) i *
        spatialPartial (show ParabolicPoint → ℝ from ψ) j (x, t)) =
      -∫ t in J, ∫ x in B, Du (x, t) i j * ψ (x, t) := by
    calc
      _ = ∫ t in J, -(∫ x in B, Du (x, t) i j * ψ (x, t)) :=
        integral_congr_ae hpair
      _ = _ := by rw [integral_neg]
  have hbox := CKN.setIntegral_prod_eq_of_iterated hF hH hiter
  simpa [B, J, spaceTimeSet, U, Up] using hbox

end CKN
