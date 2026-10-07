/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RieszPressurePackageForceZero
public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcePressureUniqueness
public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedRegMomentumGood
public import LeanPool.CaffarelliKohnNirenberg.Witnesses.ForcedZero

/-!
# Vanishing of the zero-force pressure

The force pressure in the forced regularized momentum identity vanishes on
almost every slice when the force is zero.
-/

public section

open MeasureTheory
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

/-- For zero forcing, the canonical force pressure is zero almost everywhere
on every finite positive-time interval. -/
theorem forcePressure_zero_ae_on_interval (T : ℝ) (hT : 0 < T) :
    ∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Ioo 0 T)),
      (fun x : Vec3 => forcePressure (fun _ : ParabolicPoint => (0 : Vec3))
        CKN.isLocallySquareIntegrableForce_zero (x, t)) =ᵐ[volume] 0 := by
  let f : ParabolicPoint → Vec3 := fun _ => 0
  have hf : CKN.IsLocallySquareIntegrableForce f :=
    CKN.isLocallySquareIntegrableForce_zero
  obtain ⟨hP, hfin, hgrad, -⟩ := forcePressure_spec f hf T hT
  have hPmeas : StronglyMeasurable (fun z : Vec3 × ℝ => forcePressure f hf z) :=
    (Classical.choose_spec (exists_forcePressure f hf)).1
  have h6 : ENNReal.ofReal (6 : ℝ) ≠ 0 := by simp
  have hm : Measurable fun t =>
      eLpNorm (fun x : Vec3 => forcePressure f hf (x, t))
        (ENNReal.ofReal (6 : ℝ)) volume ^ (2 : ℝ) :=
    (measurable_eLpNorm_slice hPmeas h6 ENNReal.ofReal_ne_top volume).pow_const _
  filter_upwards [ae_lt_top' hm.aemeasurable hfin.ne, hgrad] with t htop hgt
  obtain ⟨hft, hweak⟩ := hgt
  have hmem : MemLp (fun x : Vec3 => forcePressure f hf (x, t))
      (ENNReal.ofReal (6 : ℝ)) volume := by
    exact (ENNReal.rpow_lt_top_iff_of_pos (by norm_num)).1 htop
  have hmem' : MemLp (fun x : Vec3 => forcePressure f hf (x, t)) 6 volume := by
    simpa [ENNReal.ofReal_ofNat] using hmem
  have hgradzero : forcePressureGradientFunction (fun x : Vec3 => f (x, t)) hft =
      fun _ => 0 := by
    simpa [f] using forcePressureGradientFunction_zero hft
  have hzero := ae_eq_zero_of_memLp_six_of_hasWeakGradientOn_zero hmem' (by
    change HasWeakGradientOn (Set.univ : Set Vec3)
      (fun x => forcePressure f hf (x, t)) (fun _ => (0 : Vec3))
    simpa only [hgradzero] using hweak)
  simpa [f, hf] using hzero

end CKN.Leray

end
