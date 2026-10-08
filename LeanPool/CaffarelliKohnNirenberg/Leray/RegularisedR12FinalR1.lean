/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedR12FinalVelocityReg
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedGlobalR1

/-!
# The slice properties (R1) of the pointwise regularized velocity

Every nonnegative-time slice of the pointwise velocity represents the global
regularized mild curve, so the velocity inherits the continuity of the curve
in `L²`, the initial trace `J_ε a`, and weak solenoidality from the coordinate
field of the curve (`thm:regularised` (R1)).
-/

public section

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace CKN.Leray

open CKN CKN.Foundation.Parabolic

/-- Weak solenoidality in `L²` depends only on the almost-everywhere class. -/
theorem regR12_isWeakDivFreeL2_congr {f g : Vec3 → Vec3} (hfg : f =ᵐ[volume] g)
    (hf : CKN.IsWeakDivFreeL2 f) : CKN.IsWeakDivFreeL2 g := by
  refine ⟨(memLp_congr_ae hfg).1 hf.1, fun ψ => ?_⟩
  rw [← hf.2 ψ]
  apply integral_congr_ae
  filter_upwards [hfg] with x hx
  rw [hx]

/-- The real `L²` field of a coordinate function depends only on its
almost-everywhere class. -/
theorem regR12_realVectorL2OfCoordinateFunction_congr {f g : Vec3 → Vec3}
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) (hfg : f =ᵐ[volume] g) :
    realVectorL2OfCoordinateFunction f hf = realVectorL2OfCoordinateFunction g hg := by
  unfold realVectorL2OfCoordinateFunction
  apply MemLp.toLp_congr
  have h := (PiLp.volume_preserving_ofLp (Fin 3)).quasiMeasurePreserving.ae_eq_comp hfg
  filter_upwards [h] with y hy
  simp only [Function.comp_apply] at hy
  simp only [hy]

variable (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε) (a : Vec3 → Vec3) (ha : CKN.IsInJ a)
  (hPath : ∀ T : ℝ, 0 ≤ T → ∃ v : C(RegularizedMildTimeInterval T,
    BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * 2 : ℕ) : ℝ) 2),
  ∀ t : RegularizedMildTimeInterval T,
    regularisedBesselSobolevToL2CLM ((2 * 2 : ℕ) : ℝ) regR12_besselOrder_nonneg (v t) =
      complexifyVectorL2 (regR12Curve ρ ε hε a ha t.1))

include hPath in
/-- `thm:regularised` (R1) for the pointwise regularized velocity. -/
theorem regR12Velocity_R1 :
    let u := regR12Velocity ρ ε hε a ha
    ∃ hSlice : ∀ t : ℝ, 0 ≤ t → MemLp (fun x : Vec3 => u (x, t)) 2 volume,
      Continuous (fun t : Set.Ici (0 : ℝ) =>
        CKN.Leray.realVectorL2OfCoordinateFunction
          (fun x : Vec3 => u (x, t.1)) (hSlice t.1 t.2)) ∧
      (fun x : Vec3 => u (x, 0)) =ᵐ[volume]
        CKN.Leray.regUniformMollifiedInitial ρ ε hε a ∧
      ∀ t : ℝ, 0 ≤ t → CKN.IsWeakDivFreeL2 (fun x => u (x, t)) := by
  intro u
  obtain ⟨hSw, hCw, hIw, hDw⟩ := regUniformMollifiedInitial_globalR1 ρ ε hε a ha
  have hae : ∀ t : ℝ, 0 ≤ t → (fun x : Vec3 => u (x, t)) =ᵐ[volume]
      fun x : Vec3 => regularizedGlobalMildField ρ ε hε
        (realVectorL2OfCoordinateFunction (regUniformMollifiedInitial ρ ε hε a)
          (regMollifiedInitial_isInJ ρ ε hε ha).1)
        (regUniformMollifiedInitial_mildJData ρ ε hε ha) (x, t) :=
    fun t ht => regR12Velocity_slice_ae_eq_curve ρ ε hε a ha hPath t ht
  let hSlice : ∀ t : ℝ, 0 ≤ t → MemLp (fun x : Vec3 => u (x, t)) 2 volume :=
    fun t ht => (memLp_congr_ae (hae t ht)).2 (hSw t ht)
  refine ⟨hSlice, ?_, (hae 0 le_rfl).trans hIw,
    fun t ht => regR12_isWeakDivFreeL2_congr (hae t ht).symm (hDw t ht)⟩
  convert hCw using 1
  funext t
  exact regR12_realVectorL2OfCoordinateFunction_congr _ _ (hae t.1 t.2)

end CKN.Leray
