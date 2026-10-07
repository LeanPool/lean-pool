/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedR12FinalField
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedGlobalMild
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedMildInitialData

/-!
# The pointwise regularized velocity

The velocity of `thm:regularised` at a point `(x,t)` is the inverse Fourier
integral, at `x`, of the Fourier transform of the global regularized mild
curve at time `t`. On a time interval `[0,T]` on which the curve lifts
continuously to the Bessel potential space of order four, this is the
space-time field of the Fourier transform of the lift, weighted by the
inverse Bessel weight of order four.
-/

public section

open MeasureTheory FourierTransform Complex
open scoped ENNReal FourierTransform Real

noncomputable section

namespace CKN.Leray

open CKN CKN.Foundation.Parabolic

variable (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε) (a : Vec3 → Vec3) (ha : CKN.IsInJ a)

include ha in
theorem regR12_initial_memLp : MemLp (regUniformMollifiedInitial ρ ε hε a) 2 volume :=
  (regMollifiedInitial_isInJ ρ ε hε ha).1

include ha in
theorem regR12_initial_mildJData : RegularizedMildJData
    (realVectorL2OfCoordinateFunction (regUniformMollifiedInitial ρ ε hε a)
      (regR12_initial_memLp ρ ε hε a ha)) :=
  regUniformMollifiedInitial_mildJData ρ ε hε ha

/-- The global regularized mild curve issued from the mollified datum. -/
@[expose]
def regR12Curve (t : ℝ) : RealVectorL2 :=
  regularizedGlobalMildCurve ρ ε hε
    (realVectorL2OfCoordinateFunction (regUniformMollifiedInitial ρ ε hε a)
      (regR12_initial_memLp ρ ε hε a ha))
    (regR12_initial_mildJData ρ ε hε a ha) t

/-- The Fourier transform of the complexified global curve. -/
@[expose]
def regR12FreqCurve (t : ℝ) : ComplexVectorL2 :=
  Lp.fourierTransformₗᵢ L2Vec3 ComplexVec3 (complexifyVectorL2 (regR12Curve ρ ε hε a ha t))

/-- The real part of the `i`-th coordinate of a complex vector. -/
@[expose]
def regR12CoordCLM (i : Fin 3) : ComplexVec3 →L[ℝ] ℝ :=
  Complex.reCLM.comp ((PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin 3 => ℂ) i).restrictScalars ℝ)

/-- The pointwise regularized velocity: the inverse Fourier integral of the
Fourier transform of the global curve. -/
@[expose]
def regR12Velocity : ParabolicPoint → Vec3 := fun z i =>
  regR12CoordCLM i (𝓕⁻ ((regR12FreqCurve ρ ε hε a ha z.2 : ComplexVectorL2) :
    L2Vec3 → ComplexVec3) (WithLp.toLp 2 z.1))

section Model

variable (T : ℝ) (hT : 0 ≤ T)
  (v : C(RegularizedMildTimeInterval T,
    BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * 2 : ℕ) : ℝ) 2))

/-- The Fourier transform of the Bessel lift, extended to all times by
clamping to `[0,T]`. -/
@[expose]
def regR12LiftFreq (t : ℝ) : ComplexVectorL2 :=
  Lp.fourierTransformₗᵢ L2Vec3 ComplexVec3 ((v (regularizedMildTimeClamp T hT t)).toLp)

theorem regR12LiftFreq_continuous : Continuous (regR12LiftFreq T hT v) := by
  unfold regR12LiftFreq
  have h := (BesselPotentialSpace.toLpₗᵢ L2Vec3 ComplexVec3 _ 2).continuous.comp
    (v.continuous.comp (regularizedMildTimeClamp_continuous T hT))
  simp only [Function.comp_def, BesselPotentialSpace.toLpₗᵢ_apply] at h
  exact (Lp.fourierTransformₗᵢ L2Vec3 ComplexVec3).continuous.comp h

theorem regR12LiftFreq_norm_le (t : ℝ) : ‖regR12LiftFreq T hT v t‖ ≤ ‖v‖ := by
  unfold regR12LiftFreq
  rw [LinearIsometryEquiv.norm_map, BesselPotentialSpace.norm_toLp_eq]
  exact v.norm_coe_le_norm _

theorem regR12_besselOrder_nonneg : (0 : ℝ) ≤ ((2 * 2 : ℕ) : ℝ) := by positivity

variable (hv : ∀ t : RegularizedMildTimeInterval T,
  regularisedBesselSobolevToL2CLM ((2 * 2 : ℕ) : ℝ) regR12_besselOrder_nonneg (v t) =
    complexifyVectorL2 (regR12Curve ρ ε hε a ha t.1))

include hv in
/-- On `[0,T]`, the Fourier transform of the curve is the inverse Bessel
weight of order four times the Fourier transform of the lift. -/
theorem regR12FreqCurve_ae_eq (t : ℝ) (ht : t ∈ Set.Icc 0 T) :
    ((regR12FreqCurve ρ ε hε a ha t : ComplexVectorL2) : L2Vec3 → ComplexVec3) =ᵐ[volume]
      fun ξ => (1 : ℂ) • (((1 + ‖ξ‖ ^ 2) ^ (-2 : ℝ) : ℝ) : ℂ) •
        ((regR12LiftFreq T hT v t : ComplexVectorL2) : L2Vec3 → ComplexVec3) ξ := by
  have hclamp : regularizedMildTimeClamp T hT t = ⟨t, ht⟩ :=
    regularizedMildTimeClamp_eq_of_mem T hT ht
  have h := regularisedBesselSobolevToL2_fourier_ae ((2 * 2 : ℕ) : ℝ) (by positivity)
    (v ⟨t, ht⟩)
  have hvt := hv ⟨t, ht⟩
  rw [regularisedBesselSobolevToL2CLM_apply] at hvt
  rw [hvt] at h
  unfold regR12FreqCurve regR12LiftFreq
  rw [hclamp]
  refine h.trans (Filter.Eventually.of_forall fun ξ => ?_)
  simp only [one_smul]
  norm_num

include hv in
/-- On `[0,T]`, the velocity is the space-time field of the lift. -/
theorem regR12Velocity_eq_model (z : ParabolicPoint) (hz : z.2 ∈ Set.Icc 0 T) (i : Fin 3) :
    regR12Velocity ρ ε hε a ha z i =
      regR12SpaceTimeField (regR12CoordCLM i) (fun _ => 1) (regR12LiftFreq T hT v) z := by
  unfold regR12Velocity regR12SpaceTimeField regR12WeightedField
  rw [Real.fourierInv_congr_ae (regR12FreqCurve_ae_eq ρ ε hε a ha T hT v hv z.2 hz)]

include hv hT in
/-- On `[0,T]`, the velocity slice represents the global curve. -/
theorem regR12Velocity_slice_ae_eq (t : ℝ) (ht : t ∈ Set.Icc 0 T) :
    (fun x : Vec3 => regR12Velocity ρ ε hε a ha (x, t)) =ᵐ[volume]
      realVectorL2Representative (regR12Curve ρ ε hε a ha t) := by
  have hrep := regR12WeightedField_ae_eq (fun _ => (1 : ℂ)) aestronglyMeasurable_const 1
    zero_le_one (fun ξ => by
      rw [norm_one, one_mul]; nlinarith only [sq_nonneg ‖ξ‖])
    (regR12LiftFreq T hT v t) (complexifyVectorL2 (regR12Curve ρ ε hε a ha t))
    (regR12FreqCurve_ae_eq ρ ε hε a ha T hT v hv t ht)
  have hcx := complexifyValue.coeFn_compLpL (p := 2) (μ := volume)
    (regR12Curve ρ ε hε a ha t)
  have hL2 : ∀ᵐ y : L2Vec3 ∂volume, ∀ i : Fin 3,
      regR12CoordCLM i (regR12WeightedField (fun _ => (1 : ℂ))
        (regR12LiftFreq T hT v t) y) = (regR12Curve ρ ε hε a ha t y) i := by
    filter_upwards [hrep, hcx] with y hy1 hy2
    intro i
    rw [hy1]
    change regR12CoordCLM i (complexifyValue.compLpL 2 volume
      (regR12Curve ρ ε hε a ha t) y) = _
    rw [hy2]
    simp [regR12CoordCLM, complexifyValue, complexifyValueLinear, complexifyFrequency]
  have hpull := vec3ToL2Vec3_measurePreserving.quasiMeasurePreserving.ae hL2
  filter_upwards [hpull] with x hx
  funext i
  rw [regR12Velocity_eq_model ρ ε hε a ha T hT v hv (x, t) ht i]
  exact hx i

end Model

end CKN.Leray
