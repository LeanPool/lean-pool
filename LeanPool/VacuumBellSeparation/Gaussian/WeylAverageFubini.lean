/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.WeylGaussianConvolution

/-!
# Bochner Fubini for the relabeled Gaussian Weyl sandwich

The joint vector integrand has an integrable product-Gaussian norm bound.
An actual measure-preserving shear proves integrability after changing
the second label to the total displacement. Fubini and the proved scalar
twisted convolution then give the operator sandwich identity. The premise
on T is precisely preservation of the actual imaginary inner form.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open MeasureTheory ContinuousLinearMap
open scoped ComplexConjugate

variable {m : ℕ}

/-- Preservation of the imaginary part of the phase-space inner product. -/
def PreservesWeylForm (T : MultiModePhaseSpace m →L[ℝ] MultiModePhaseSpace m) : Prop :=
  ∀ z w, (inner ℂ (T z) (T w)).im = (inner ℂ z w).im

theorem weylPhase_relabel {T : MultiModePhaseSpace m →L[ℝ] MultiModePhaseSpace m}
    (hT : PreservesWeylForm T) (z w : MultiModePhaseSpace m) :
    weylPhase (id : MultiModePhaseSpace m → MultiModePhaseSpace m) (T z) (T w) =
      weylPhase (id : MultiModePhaseSpace m → MultiModePhaseSpace m) z w := by
  simp only [weylPhase, id_eq, hT z w]

theorem norm_weylPhase_id (z w : MultiModePhaseSpace m) :
    ‖weylPhase (id : MultiModePhaseSpace m → MultiModePhaseSpace m) z w‖ = 1 := by
  simp [weylPhase, Complex.norm_exp, Complex.mul_re]

theorem relabeledWeyl_triple {T : MultiModePhaseSpace m →L[ℝ] MultiModePhaseSpace m}
    (hT : PreservesWeylForm T) (z a w : MultiModePhaseSpace m) :
    multiOscillatorWeyl (T z) * multiOscillatorWeyl (T a) * multiOscillatorWeyl (T w) =
      (weylPhase id z a * weylPhase id (z + a) w) • multiOscillatorWeyl (T (z + a + w)) := by
  rw [multiOscillatorWeyl_mul, weylPhase_relabel hT, ← map_add,
    smul_mul_assoc, multiOscillatorWeyl_mul, weylPhase_relabel hT,
    ← map_add, smul_smul]

/-- Relabeled Weyl double integrand. -/
def relabeledWeylDoubleIntegrand
    (T : MultiModePhaseSpace m →L[ℝ] MultiModePhaseSpace m)
    (a : MultiModePhaseSpace m) (x : MultiModeOscillatorSpace m)
    (p : (Fin m → ℂ) × (Fin m → ℂ)) : MultiModeOscillatorSpace m :=
  let z : MultiModePhaseSpace m := WithLp.toLp 2 p.1
  let w : MultiModePhaseSpace m := WithLp.toLp 2 p.2
  (weylVacuumWeight m p.1 * weylVacuumWeight m p.2 *
    weylPhase id z a * weylPhase id (z + a) w) • multiOscillatorWeyl (T (z + a + w)) x

theorem continuous_relabeledWeylDoubleIntegrand
    (T : MultiModePhaseSpace m →L[ℝ] MultiModePhaseSpace m)
    (a : MultiModePhaseSpace m) (x : MultiModeOscillatorSpace m) :
    Continuous (relabeledWeylDoubleIntegrand T a x) := by
  have hlabel : Continuous (fun p : (Fin m → ℂ) × (Fin m → ℂ) =>
      T ((WithLp.toLp 2 p.1 : MultiModePhaseSpace m) + a + WithLp.toLp 2 p.2)) := by fun_prop
  have hW := (continuous_multiOscillatorWeyl_apply x).comp hlabel
  have hscalar : Continuous (fun p : (Fin m → ℂ) × (Fin m → ℂ) =>
      weylVacuumWeight m p.1 * weylVacuumWeight m p.2 *
        weylPhase id (WithLp.toLp 2 p.1 : MultiModePhaseSpace m) a *
        weylPhase id ((WithLp.toLp 2 p.1 : MultiModePhaseSpace m) + a) (WithLp.toLp 2 p.2)) := by
    unfold weylVacuumWeight weylPhase
    fun_prop
  exact hscalar.smul hW

theorem norm_relabeledWeylDoubleIntegrand
    (T : MultiModePhaseSpace m →L[ℝ] MultiModePhaseSpace m)
    (a : MultiModePhaseSpace m) (x : MultiModeOscillatorSpace m)
    (p : (Fin m → ℂ) × (Fin m → ℂ)) :
    ‖relabeledWeylDoubleIntegrand T a x p‖ =
      (‖weylVacuumWeight m p.1‖ * ‖weylVacuumWeight m p.2‖) * ‖x‖ := by
  simp only [relabeledWeylDoubleIntegrand, norm_smul, norm_mul,
    norm_weylPhase_id, mul_one, norm_multiOscillatorWeyl_apply]

theorem integrable_relabeledWeylDoubleIntegrand
    (T : MultiModePhaseSpace m →L[ℝ] MultiModePhaseSpace m)
    (a : MultiModePhaseSpace m) (x : MultiModeOscillatorSpace m) :
    Integrable (relabeledWeylDoubleIntegrand T a x)
      ((volume : Measure (Fin m → ℂ)).prod volume) := by
  have hb := ((integrable_weylVacuumWeight m).norm.mul_prod
    (integrable_weylVacuumWeight m).norm).mul_const ‖x‖
  apply hb.mono' (continuous_relabeledWeylDoubleIntegrand T a x).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun p => (norm_relabeledWeylDoubleIntegrand T a x p).le

theorem relabeledWeylDoubleIntegrand_eq_apply
    {T : MultiModePhaseSpace m →L[ℝ] MultiModePhaseSpace m} (hT : PreservesWeylForm T)
    (a : MultiModePhaseSpace m) (x : MultiModeOscillatorSpace m) (z w : Fin m → ℂ) :
    relabeledWeylDoubleIntegrand T a x (z, w) =
      weylVacuumWeight m z • multiOscillatorWeyl (T (WithLp.toLp 2 z))
        (multiOscillatorWeyl (T a)
          (weylVacuumWeight m w • multiOscillatorWeyl (T (WithLp.toLp 2 w)) x)) := by
  have h := congrArg (fun B : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m => B x)
    (relabeledWeyl_triple hT (WithLp.toLp 2 z) a (WithLp.toLp 2 w))
  simp only [mul_apply_eq_comp, smul_apply] at h
  simp only [map_smul, smul_smul]
  rw [h]
  simp only [relabeledWeylDoubleIntegrand, smul_smul]
  congr 1
  ring

theorem relabeledWeylAverage_sandwich_iterated
    {T : MultiModePhaseSpace m →L[ℝ] MultiModePhaseSpace m} (hT : PreservesWeylForm T)
    (a : MultiModePhaseSpace m) (x : MultiModeOscillatorSpace m) :
    relabeledWeylAverage T (multiOscillatorWeyl (T a) (relabeledWeylAverage T x)) =
      ∫ z : Fin m → ℂ, ∫ w : Fin m → ℂ, relabeledWeylDoubleIntegrand T a x (z, w) := by
  rw [relabeledWeylAverage_apply]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun z => by
    let L : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m :=
      weylVacuumWeight m z • (multiOscillatorWeyl (T (WithLp.toLp 2 z)) * multiOscillatorWeyl (T a))
    have hi := L.integral_comp_comm (integrable_relabeledWeylOrbit T x)
    simp_rw [relabeledWeylDoubleIntegrand_eq_apply hT]
    simpa only [L, smul_apply, mul_apply_eq_comp, ← relabeledWeylAverage_apply] using hi.symm

theorem measurePreserving_weylSandwichShear (a : Fin m → ℂ) :
    MeasurePreserving
      (fun p : (Fin m → ℂ) × (Fin m → ℂ) => (p.1, p.2 - p.1 - a))
      ((volume : Measure (Fin m → ℂ)).prod volume)
      ((volume : Measure (Fin m → ℂ)).prod volume) := by
  have h := ((MeasurePreserving.id (volume : Measure (Fin m → ℂ))).prod
    (measurePreserving_add_right (volume : Measure (Fin m → ℂ)) (-a))).comp
      (measurePreserving_prod_sub (volume : Measure (Fin m → ℂ)) volume)
  convert h using 1; funext p;
    simp only [Function.comp_apply, Prod.map_apply, id_eq, sub_eq_add_neg]

theorem relabeledWeylDoubleIntegrand_shear
    (T : MultiModePhaseSpace m →L[ℝ] MultiModePhaseSpace m)
    (a : MultiModePhaseSpace m) (x : MultiModeOscillatorSpace m) (z u : Fin m → ℂ) :
    relabeledWeylDoubleIntegrand T a x (z, u - z - (fun j => a j)) =
      weylSandwichConvolution a (WithLp.toLp 2 u) z •
        multiOscillatorWeyl (T (WithLp.toLp 2 u)) x := by
  have hlabel : (WithLp.toLp 2 z : MultiModePhaseSpace m) + a +
      WithLp.toLp 2 (u - z - (fun j => a j)) = WithLp.toLp 2 u := by
    simp only [WithLp.toLp_sub]
    abel
  have ha : (WithLp.toLp 2 (fun j => a j) : MultiModePhaseSpace m) = a :=
    WithLp.toLp_ofLp 2 a
  simp only [relabeledWeylDoubleIntegrand, weylSandwichConvolution,
    phaseSpaceVacuumWeight, weylVacuumWeight]
  rw [hlabel]
  simp only [WithLp.toLp_sub, ha]

theorem integrable_relabeledWeylShearedIntegrand
    (T : MultiModePhaseSpace m →L[ℝ] MultiModePhaseSpace m)
    (a : MultiModePhaseSpace m) (x : MultiModeOscillatorSpace m) :
    Integrable (fun p : (Fin m → ℂ) × (Fin m → ℂ) =>
      weylSandwichConvolution a (WithLp.toLp 2 p.2) p.1 •
        multiOscillatorWeyl (T (WithLp.toLp 2 p.2)) x)
      ((volume : Measure (Fin m → ℂ)).prod volume) := by
  have h := (measurePreserving_weylSandwichShear (fun j => a j)).integrable_comp_of_integrable
    (integrable_relabeledWeylDoubleIntegrand T a x)
  apply h.congr
  exact Filter.Eventually.of_forall fun p =>
    relabeledWeylDoubleIntegrand_shear T a x p.1 p.2

/-- Actual compressed-Weyl identity, proved by a genuine Bochner Fubini
argument. The unnormalized Gaussian average has factor π^m. -/
theorem relabeledWeylAverage_sandwich
    {T : MultiModePhaseSpace m →L[ℝ] MultiModePhaseSpace m} (hT : PreservesWeylForm T)
    (a : MultiModePhaseSpace m) :
    relabeledWeylAverage T * multiOscillatorWeyl (T a) * relabeledWeylAverage T =
      ((Real.pi : ℂ) ^ m * phaseSpaceVacuumWeight a) • relabeledWeylAverage T := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [mul_apply_eq_comp, smul_apply]
  rw [relabeledWeylAverage_sandwich_iterated hT]
  calc
    _ = ∫ z : Fin m → ℂ, ∫ u : Fin m → ℂ,
        relabeledWeylDoubleIntegrand T a x (z, u - z - (fun j => a j)) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => by
        simp_rw [← sub_add_eq_sub_sub]
        exact (integral_sub_right_eq_self
          (fun w => relabeledWeylDoubleIntegrand T a x (z, w)) (z + (fun j => a j))).symm
    _ = ∫ z : Fin m → ℂ, ∫ u : Fin m → ℂ,
        weylSandwichConvolution a (WithLp.toLp 2 u) z •
          multiOscillatorWeyl (T (WithLp.toLp 2 u)) x := by
      simp_rw [relabeledWeylDoubleIntegrand_shear]
    _ = ∫ u : Fin m → ℂ, ∫ z : Fin m → ℂ,
        weylSandwichConvolution a (WithLp.toLp 2 u) z •
          multiOscillatorWeyl (T (WithLp.toLp 2 u)) x :=
      integral_integral_swap (integrable_relabeledWeylShearedIntegrand T a x)
    _ = ∫ u : Fin m → ℂ,
        ((Real.pi : ℂ) ^ m * phaseSpaceVacuumWeight a * phaseSpaceVacuumWeight (WithLp.toLp 2 u)) •
          multiOscillatorWeyl (T (WithLp.toLp 2 u)) x := by
      simp_rw [integral_smul_const, integral_weylSandwichConvolution]
    _ = _ := by
      simp only [mul_smul]
      rw [integral_smul, integral_smul]
      rfl

end VacuumBellSeparation.Gaussian
