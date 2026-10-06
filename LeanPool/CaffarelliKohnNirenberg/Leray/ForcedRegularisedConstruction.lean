/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedRegularisedEnergyForm
public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedRegularisedGlobal
public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedRegularisedPressure
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedInitialData

/-!
# The forced regularized solution

The solution of `eq:reg-mild-forced` with the mollified datum and the
strongly measurable modification of the force, its jointly measurable
space-time representative, and the slice properties of `lem:regularised-forced`:
continuity in `L²`, the initial datum, weak divergence freedom, the weak
gradient, the dissipation bound and the energy inequality.
-/

public section

open MeasureTheory Set Filter
open CKN.Foundation.Parabolic
open scoped ENNReal Topology

noncomputable section

namespace CKN.Leray

section Construction

variable (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε) {a : Vec3 → Vec3} (ha : CKN.IsInJ a)
  {f : ParabolicPoint → Vec3} (hf : CKN.IsLocallySquareIntegrableForce f)

theorem forcedRegInitial_memLp {a : Vec3 → Vec3} (ha : CKN.IsInJ a) :
    MemLp (regUniformMollifiedInitial ρ ε hε a) 2 volume :=
  (regMollifiedInitial_isInJ ρ ε hε ha).1

/-- The mollified datum of the forced regularized problem as a real `L²`
field. -/
@[expose]
def forcedRegDatum : RealVectorL2 :=
  realVectorL2OfCoordinateFunction (regUniformMollifiedInitial ρ ε hε a)
    (forcedRegInitial_memLp ρ ε hε ha)

theorem forcedRegDatum_rep :
    realVectorL2Representative (forcedRegDatum ρ ε hε ha) =ᵐ[volume]
      regUniformMollifiedInitial ρ ε hε a :=
  realVectorL2OfCoordinateFunction_rep _ _

theorem forcedRegDatum_mildJData : RegularizedMildJData (forcedRegDatum ρ ε hε ha) := by
  have hJ := CKN.isInJ_iff_weakDivFree.1 (regMollifiedInitial_isInJ ρ ε hε ha)
  exact CKN.isInJ_iff_weakDivFree.2 (isWeakDivFree_congr_ae (forcedRegDatum_rep ρ ε hε ha).symm hJ)

/-- The solution curve of `eq:reg-mild-forced` with the mollified datum and
the force curve of the strongly measurable modification of the force. -/
@[expose]
def forcedRegCurve : ℝ → RealVectorL2 :=
  forcedSolutionCurve ρ ε hε (forcedRegDatum ρ ε hε ha) (forcedRegDatum_mildJData ρ ε hε ha)
    (forcedForceSlice_stronglyMeasurable (forcedForceMod_stronglyMeasurable f hf))
    (integrableOn_forcedForceSlice_sq f hf)

theorem continuous_forcedRegCurve : Continuous (forcedRegCurve ρ ε hε ha hf) :=
  continuous_forcedSolutionCurve _ _ _ _ _ _ _

/-- The jointly measurable space-time representative of the forced
regularized solution. -/
@[expose]
def forcedRegRep : Vec3 × ℝ → Vec3 :=
  forcedCurveRep (forcedRegCurve ρ ε hε ha hf)
    (continuous_forcedRegCurve ρ ε hε ha hf).stronglyMeasurable

theorem forcedRegRep_stronglyMeasurable : StronglyMeasurable (forcedRegRep ρ ε hε ha hf) :=
  forcedCurveRep_stronglyMeasurable _ _

theorem forcedRegRep_slice (t : ℝ) :
    (fun x => forcedRegRep ρ ε hε ha hf (x, t)) =ᵐ[volume]
      realVectorL2Representative (forcedRegCurve ρ ε hε ha hf t) :=
  forcedCurveRep_slice _ _ t

theorem forcedRegRep_memLp (t : ℝ) :
    MemLp (fun x => forcedRegRep ρ ε hε ha hf (x, t)) 2 volume :=
  (realVectorL2Representative_memLp_two _).ae_eq (forcedRegRep_slice ρ ε hε ha hf t).symm

theorem forcedRegRep_locallyIntegrable (t : ℝ) (i : Fin 3) :
    LocallyIntegrable (fun y => forcedRegRep ρ ε hε ha hf (y, t) i) volume :=
  ((forcedRegRep_memLp ρ ε hε ha hf t).eval i).locallyIntegrable (by norm_num)

theorem forcedRegRep_class (t : ℝ) :
    realVectorL2OfCoordinateFunction (fun x => forcedRegRep ρ ε hε ha hf (x, t))
      (forcedRegRep_memLp ρ ε hε ha hf t) = forcedRegCurve ρ ε hε ha hf t :=
  realVectorL2Representative_injective_ae
    ((realVectorL2OfCoordinateFunction_rep _ _).trans (forcedRegRep_slice ρ ε hε ha hf t))

theorem forcedRegRep_initial :
    (fun x => forcedRegRep ρ ε hε ha hf (x, 0)) =ᵐ[volume] regUniformMollifiedInitial ρ ε hε a := by
  have h0 : forcedRegCurve ρ ε hε ha hf 0 = forcedRegDatum ρ ε hε ha :=
    forcedSolutionCurve_zero _ _ _ _ _ _ _
  have h := forcedRegRep_slice ρ ε hε ha hf 0
  rw [h0] at h
  exact h.trans (forcedRegDatum_rep ρ ε hε ha)

theorem forcedRegRep_weakDivFree {t : ℝ} (ht : 0 ≤ t) :
    CKN.IsWeakDivFreeL2 (fun x => forcedRegRep ρ ε hε ha hf (x, t)) := by
  have hJ : RegularizedMildJData (forcedRegCurve ρ ε hε ha hf t) :=
    forcedSolutionCurve_mildJData _ _ _ _ _ _ _ ht
  exact isWeakDivFree_congr_ae (forcedRegRep_slice ρ ε hε ha hf t).symm
    (CKN.isInJ_iff_weakDivFree.1 hJ)

/-- The weak gradient of the forced regularized solution on almost every
positive time slice. -/
theorem forcedRegRep_weakGradient :
    ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), ∀ i : Fin 3,
      CKN.HasWeakGradientOn (Set.univ : Set Vec3) (fun x => forcedRegRep ρ ε hε ha hf (x, t) i)
        (fun x => forcedMollifiedGrad (forcedRegRep ρ ε hε ha hf) (x, t) i) := by
  refine ae_Ioi_of_forall_Ioc fun n => ?_
  obtain ⟨v, hre, hmem, -, -⟩ := forcedSolutionCurve_energy ρ ε hε (forcedRegDatum ρ ε hε ha)
    (forcedRegDatum_mildJData ρ ε hε ha)
    (forcedForceSlice_stronglyMeasurable (forcedForceMod_stronglyMeasurable f hf))
    (integrableOn_forcedForceSlice_sq f hf) (T := (n : ℝ) + 1) (by positivity)
  filter_upwards [hmem, ae_restrict_mem measurableSet_Ioc] with s hs hsI
  exact (forcedSlice_gradient_dissipation (forcedRegRep_slice ρ ε hε ha hf)
    (hre s ⟨hsI.1.le, hsI.2⟩) hs).1

/-- The dissipation bound and the energy inequality of the forced regularized
solution up to time `t`. -/
theorem forcedRegRep_energy {t : ℝ} (ht : 0 ≤ t) :
    ∃ D : ℝ,
      ∫⁻ z, ENNReal.ofReal (CKN.spatialGradientSq (forcedRegRep ρ ε hε ha hf)
          (forcedMollifiedGrad (forcedRegRep ρ ε hε ha hf)) z)
          ∂((volume : Measure Vec3).prod ((volume : Measure ℝ).restrict (Ioo 0 t))) ≤
        ENNReal.ofReal D ∧ 0 ≤ D ∧
      ‖forcedRegCurve ρ ε hε ha hf t‖ ^ 2 + 2 * D ≤
        ‖forcedRegDatum ρ ε hε ha‖ ^ 2 + 2 * ∫ s in Ioc 0 t,
          inner ℝ (forcedRegCurve ρ ε hε ha hf s) (forcedForceSlice (forcedForceMod f hf) s) := by
  obtain ⟨v, hre, hmem, hint, hen⟩ := forcedSolutionCurve_energy ρ ε hε
    (forcedRegDatum ρ ε hε ha) (forcedRegDatum_mildJData ρ ε hε ha)
    (forcedForceSlice_stronglyMeasurable (forcedForceMod_stronglyMeasurable f hf))
    (integrableOn_forcedForceSlice_sq f hf) ht
  refine ⟨∫ s in Ioc 0 t, forcedFourierDissipation (v s), ?_,
    setIntegral_nonneg measurableSet_Ioc fun s _ => forcedFourierDissipation_nonneg _,
    hen t ⟨ht, le_rfl⟩⟩
  refine lintegral_slab_spatialGradientSq_le (forcedRegRep_stronglyMeasurable ρ ε hε ha hf)
    (forcedRegRep_locallyIntegrable ρ ε hε ha hf) hint
    (fun s => forcedFourierDissipation_nonneg _) ?_
  filter_upwards [hmem, ae_restrict_mem measurableSet_Ioc] with s hs hsI
  exact (forcedSlice_gradient_dissipation (forcedRegRep_slice ρ ε hε ha hf)
    (hre s ⟨hsI.1.le, hsI.2⟩) hs).2

end Construction

end CKN.Leray

end
