/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedRegularised
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedGlobalMild
public import LeanPool.CaffarelliKohnNirenberg.Witnesses.ForcedZero

/-!
# The regularized forced curve with zero force

The measurable modification used by the forced construction may differ from
zero on a null set. Its time slices therefore vanish almost everywhere, which
identifies the resulting mild curve with the global zero-force curve.
-/

public section

open MeasureTheory Set
open scoped ENNReal
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

/-- The spatial L² force curve of a modification of zero vanishes for almost
every positive time on each finite interval. -/
theorem forcedZeroForceSlice_ae_eq_zero (T : ℝ) (hT : 0 < T) :
    ∀ᵐ s ∂(volume.restrict (Ioo 0 T)),
      forcedForceSlice
        (forcedForceMod (fun _ : ParabolicPoint => (0 : Vec3))
          CKN.isLocallySquareIntegrableForce_zero) s = 0 := by
  let F : Vec3 × ℝ → Vec3 := forcedForceMod
    (fun _ : ParabolicPoint => (0 : Vec3)) CKN.isLocallySquareIntegrableForce_zero
  have h0 := forcedForceMod_ae_eq
    (fun _ : ParabolicPoint => (0 : Vec3))
    CKN.isLocallySquareIntegrableForce_zero hT
  have h0prod : ∀ᵐ z ∂((volume : Measure Vec3).prod
      ((volume : Measure ℝ).restrict (Ioo 0 T))), F z = 0 := by
    rw [← restrict_spaceTimeSet_eq_prod]
    exact h0
  have hswap := (Measure.measurePreserving_swap
    (μ := (volume : Measure ℝ).restrict (Ioo 0 T))
    (ν := (volume : Measure Vec3))).quasiMeasurePreserving.ae h0prod
  have htime := Measure.ae_ae_of_ae_prod hswap
  filter_upwards [htime] with s hs
  by_cases hmem : MemLp (fun x : Vec3 => F (x, s)) 2 volume
  · have hclass : realVectorL2OfCoordinateFunction (fun x => F (x, s)) hmem = 0 := by
      apply realVectorL2Representative_injective_ae
      filter_upwards [realVectorL2OfCoordinateFunction_rep _ hmem, hs] with x hx hzero
      have hzero' : F (x, s) = 0 := by simpa using hzero
      calc
        realVectorL2Representative
            (realVectorL2OfCoordinateFunction (fun x => F (x, s)) hmem) x =
            F (x, s) := hx
        _ = 0 := hzero'
        _ = realVectorL2Representative (0 : RealVectorL2) x := by
          rw [realVectorL2Representative_apply]
          simp
    unfold forcedForceSlice
    rw [dite_eq_left hmem, hclass]
  · unfold forcedForceSlice
    rw [dite_eq_right hmem]

private theorem forcedZeroForceDuhamel_eq_zero
    (h : ℝ → RealVectorL2)
    (hh : ∀ T : ℝ, 0 < T → ∀ᵐ s ∂(volume.restrict (Ioo 0 T)), h s = 0)
    (t : ℝ) (ht : 0 ≤ t) :
    forcedForceDuhamel h t = 0 := by
  unfold forcedForceDuhamel
  have hzero : ∀ᵐ s ∂(volume.restrict (Ioc 0 t)),
      forcedForceIntegrand h t s = 0 := by
    have htpos : 0 < t + 1 := by linarith only [ht]
    have htime := hh (t + 1) htpos
    have hrestrict : Ioc 0 t ⊆ Ioo 0 (t + 1) := by
      intro s hs
      exact ⟨hs.1, lt_of_le_of_lt hs.2 (by linarith only [hs.2])⟩
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hrestrict htime,
      ae_restrict_mem measurableSet_Ioc] with s hs0 hsI
    rw [forcedForceIntegrand, dite_eq_left hsI.2, hs0]
    exact forcedHeatLeray_zero (t - s) (sub_nonneg.2 hsI.2)
  rw [integral_congr_ae hzero]
  simp

/-- The forced construction with the zero force agrees with the global
zero-force regularized mild curve. -/
theorem forcedRegCurve_zero_eq_regularizedGlobalMildCurve
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (a : Vec3 → Vec3) (ha : IsInJ a) :
    ∀ t : ℝ,
      forcedRegCurve ρ ε hε ha CKN.isLocallySquareIntegrableForce_zero t =
        regularizedGlobalMildCurve ρ ε hε
          (forcedRegDatum ρ ε hε ha)
          (forcedRegDatum_mildJData ρ ε hε ha) t := by
  let h : ℝ → RealVectorL2 := forcedForceSlice
    (forcedForceMod (fun _ : ParabolicPoint => (0 : Vec3))
      CKN.isLocallySquareIntegrableForce_zero)
  have hh : StronglyMeasurable h := by
    exact forcedForceSlice_stronglyMeasurable
      (forcedForceMod_stronglyMeasurable _ _)
  have hH2 (S : ℝ) : IntegrableOn (fun s => ‖h s‖ ^ 2) (Ioc 0 S) :=
    integrableOn_forcedForceSlice_sq _ CKN.isLocallySquareIntegrableForce_zero S
  have hH (S : ℝ) : IntegrableOn (fun s => ‖h s‖) (Ioc 0 S) :=
    integrableOn_norm_of_sq hh (hH2 S)
  have hhzero (S : ℝ) (hS : 0 < S) :
      ∀ᵐ s ∂(volume.restrict (Ioo 0 S)), h s = 0 := by
    exact forcedZeroForceSlice_ae_eq_zero S hS
  intro t
  rcases le_total 0 t with ht | ht
  · let V : C(RegularizedMildTimeInterval (t + 1), RealVectorL2) :=
      ⟨fun s => forcedRegCurve ρ ε hε ha CKN.isLocallySquareIntegrableForce_zero s.1,
        (continuous_forcedRegCurve ρ ε hε ha
          CKN.isLocallySquareIntegrableForce_zero).comp continuous_subtype_val⟩
    let W : C(RegularizedMildTimeInterval (t + 1), RealVectorL2) :=
      ⟨fun s => regularizedGlobalMildCurve ρ ε hε
          (forcedRegDatum ρ ε hε ha)
          (forcedRegDatum_mildJData ρ ε hε ha) s.1,
        (regularizedGlobalMildCurve_continuous ρ ε hε
          (forcedRegDatum ρ ε hε ha)
          (forcedRegDatum_mildJData ρ ε hε ha)).comp continuous_subtype_val⟩
    have hV (s : RegularizedMildTimeInterval (t + 1)) :
        V s = forcedMildRHS (forcedRegDatum ρ ε hε ha) h
          (regularizedMildClampedTensorTrajectory ρ ε hε (t + 1)
            (by linarith only [ht]) V) s.1 s.2.1 := by
      change forcedSolutionCurve ρ ε hε (forcedRegDatum ρ ε hε ha)
        (forcedRegDatum_mildJData ρ ε hε ha) hh hH2 s.1 = _
      rw [forcedSolutionCurve_mild ρ ε hε
        (forcedRegDatum ρ ε hε ha) (forcedRegDatum_mildJData ρ ε hε ha)
        hh hH2 s.2.1]
      unfold forcedMildRHS
      rw [forcedZeroForceDuhamel_eq_zero h hhzero s.1 s.2.1]
      have hI : regularizedMildStokesIntegral
          (fun r => regularizedMildTensor ρ ε hε
            (forcedSolutionCurve ρ ε hε (forcedRegDatum ρ ε hε ha)
              (forcedRegDatum_mildJData ρ ε hε ha) hh hH2 r)) s.1 =
          regularizedMildStokesIntegral
            (regularizedMildClampedTensorTrajectory ρ ε hε (t + 1)
              (by linarith only [ht]) V) s.1 := by
        apply regularizedMildStokesIntegral_congr_Icc
        intro r hr
        have hrT : r ∈ Icc 0 (t + 1) :=
          ⟨hr.1, le_trans hr.2 (by linarith only [s.2.2])⟩
        simp [regularizedMildClampedTensorTrajectory, V, forcedRegCurve,
          regularizedMildTimeClamp_eq_of_mem (t + 1)
            (by linarith only [ht]) hrT]
      rw [hI]
    have hW (s : RegularizedMildTimeInterval (t + 1)) :
        W s = forcedMildRHS (forcedRegDatum ρ ε hε ha) h
          (regularizedMildClampedTensorTrajectory ρ ε hε (t + 1)
            (by linarith only [ht]) W) s.1 s.2.1 := by
      change regularizedGlobalMildCurve ρ ε hε
        (forcedRegDatum ρ ε hε ha)
        (forcedRegDatum_mildJData ρ ε hε ha) s.1 = _
      unfold forcedMildRHS
      rw [forcedZeroForceDuhamel_eq_zero h hhzero s.1 s.2.1]
      rw [regularizedGlobalMildCurve_mild ρ ε hε
        (forcedRegDatum ρ ε hε ha) (forcedRegDatum_mildJData ρ ε hε ha)
        s.1 s.2.1]
      have hI : regularizedMildStokesIntegral
            (regularizedMildTensorTrajectory ρ ε hε
              (regularizedGlobalMildCurve ρ ε hε
                (forcedRegDatum ρ ε hε ha)
                (forcedRegDatum_mildJData ρ ε hε ha))) s.1 =
            regularizedMildStokesIntegral
              (regularizedMildClampedTensorTrajectory ρ ε hε (t + 1)
                (by linarith only [ht]) W) s.1 := by
          apply regularizedMildStokesIntegral_congr_Icc
          intro r hr
          have hrT : r ∈ Icc 0 (t + 1) :=
            ⟨hr.1, le_trans hr.2 (by linarith only [s.2.2])⟩
          simp [regularizedMildTensorTrajectory, regularizedMildClampedTensorTrajectory, W,
            regularizedMildTimeClamp_eq_of_mem (t + 1)
              (by linarith only [ht]) hrT]
      rw [hI]
      simp
    have hEq := forcedMildSolution_unique ρ ε hε
      (forcedRegDatum ρ ε hε ha)
      hh hH
      (t + 1) (by linarith only [ht]) V W hV hW
    have hVt := congrArg (fun X => X ⟨t, ht, by linarith only [ht]⟩) hEq
    exact hVt
  · have ht0 : t ≤ 0 := ht
    have hV0 := forcedSolutionCurve_of_nonpos ρ ε hε
      (forcedRegDatum ρ ε hε ha) (forcedRegDatum_mildJData ρ ε hε ha)
      hh hH2 ht0
    have hW0 := forcedSolutionCurve_of_nonpos ρ ε hε
      (forcedRegDatum ρ ε hε ha) (forcedRegDatum_mildJData ρ ε hε ha)
      (h := fun _ => (0 : RealVectorL2))
      stronglyMeasurable_const (fun S => by simp) ht0
    change forcedSolutionCurve ρ ε hε (forcedRegDatum ρ ε hε ha)
      (forcedRegDatum_mildJData ρ ε hε ha) hh hH2 t =
      forcedSolutionCurve ρ ε hε (forcedRegDatum ρ ε hε ha)
      (forcedRegDatum_mildJData ρ ε hε ha)
        (h := fun _ => (0 : RealVectorL2)) stronglyMeasurable_const
        (fun S => by simp) t
    rw [hV0, hW0,
      forcedSolutionCurve_zero ρ ε hε (forcedRegDatum ρ ε hε ha)
        (forcedRegDatum_mildJData ρ ε hε ha) hh hH2,
      forcedSolutionCurve_zero ρ ε hε (forcedRegDatum ρ ε hε ha)
        (forcedRegDatum_mildJData ρ ε hε ha)
        (h := fun _ => (0 : RealVectorL2)) stronglyMeasurable_const
        (fun S => by simp)]

end CKN.Leray

end
