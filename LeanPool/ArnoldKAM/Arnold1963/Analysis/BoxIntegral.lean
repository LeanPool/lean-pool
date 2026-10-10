/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Basic.Spaces
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
Unit-cube integration with product Lebesgue measure and coordinate-by-coordinate Fubini formulas.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set
namespace KamProject.Arnold1963

/-- Lebesgue probability measure restricted to the closed unit interval. -/
def unitIntervalMeasure : Measure ℝ := volume.restrict (Icc 0 1)

instance : IsProbabilityMeasure unitIntervalMeasure := ⟨by
  simp [unitIntervalMeasure, Real.volume_Icc]⟩

/-- Product probability measure on the unit cube, used for normalized Fourier integration. -/
def unitCubeMeasure (n : ℕ) : Measure (RealSpace n) :=
  Measure.pi (fun _ : Fin n => unitIntervalMeasure)

instance (n : ℕ) : IsProbabilityMeasure (unitCubeMeasure n) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun _ : Fin n => unitIntervalMeasure)))

/-- The closed unit cube in real coordinate space. -/
def unitCube (n : ℕ) : Set (RealSpace n) := univ.pi (fun _ => Icc 0 1)

/-- Integration over the unit cube with its product probability measure. -/
def unitCubeIntegral {n : ℕ} (f : RealSpace n → ℂ) : ℂ := ∫ x, f x ∂unitCubeMeasure n

theorem unitCubeMeasure_eq_restrict (n : ℕ) :
    unitCubeMeasure n = volume.restrict (unitCube n) := by
  change Measure.pi (fun _ : Fin n => volume.restrict (Icc (0 : ℝ) 1)) =
    (Measure.pi (fun _ : Fin n => (volume : Measure ℝ))).restrict _
  exact (Measure.restrict_pi_pi _ _).symm

theorem ae_mem_unitCube (n : ℕ) : ∀ᵐ x ∂unitCubeMeasure n, x ∈ unitCube n := by
  rw [unitCubeMeasure_eq_restrict]
  exact ae_restrict_mem (MeasurableSet.univ_pi (fun _ => measurableSet_Icc))

theorem integrable_unitCube {n : ℕ} {f : RealSpace n → ℂ}
    (hf : ContinuousOn f (unitCube n)) : Integrable f (unitCubeMeasure n) := by
  rw [unitCubeMeasure_eq_restrict]
  exact hf.integrableOn_compact (isCompact_univ_pi (fun _ => isCompact_Icc))

theorem unitCubeIntegral_congr {n : ℕ} {f g : RealSpace n → ℂ}
    (h : ∀ x ∈ unitCube n, f x = g x) : unitCubeIntegral f = unitCubeIntegral g :=
  integral_congr_ae ((ae_mem_unitCube n).mono fun x hx => h x hx)

theorem norm_unitCubeIntegral_le {n : ℕ} {f : RealSpace n → ℂ} {M : ℝ}
    (h : ∀ x ∈ unitCube n, ‖f x‖ ≤ M) : ‖unitCubeIntegral f‖ ≤ M := by
  simpa only [unitCubeIntegral, probReal_univ, mul_one] using
    norm_integral_le_of_norm_le_const ((ae_mem_unitCube n).mono fun x hx => h x hx)

theorem integrable_cons_unitCube {n : ℕ} {f : RealSpace (n + 1) → ℂ}
    (hf : Integrable f (unitCubeMeasure (n + 1))) :
    Integrable (fun xy : ℝ × RealSpace n => f (Fin.cons xy.1 xy.2))
      (unitIntervalMeasure.prod (unitCubeMeasure n)) := by
  have hp := (measurePreserving_piFinSuccAbove
    (fun _ : Fin (n + 1) => unitIntervalMeasure) 0).symm
  have hi := (hp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).mpr hf
  simpa only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Fin.insertNth_zero, Fin.zero_succAbove, Function.comp_def, Equiv.coe_fn_mk, cast_eq,
    unitCubeMeasure] using hi

theorem unitCubeIntegral_cons {n : ℕ} {f : RealSpace (n + 1) → ℂ}
    (hf : Integrable f (unitCubeMeasure (n + 1))) :
    unitCubeIntegral f = ∫ x, unitCubeIntegral (fun y => f (Fin.cons x y))
      ∂unitIntervalMeasure := by
  have hp := (measurePreserving_piFinSuccAbove
    (fun _ : Fin (n + 1) => unitIntervalMeasure) 0).symm
  unfold unitCubeIntegral unitCubeMeasure
  rw [← hp.integral_comp']
  simpa only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Fin.insertNth_zero, Fin.zero_succAbove, Function.comp_def, Equiv.coe_fn_mk, cast_eq,
    unitCubeMeasure] using
      integral_prod _ (integrable_cons_unitCube hf)

theorem unitCubeIntegral_cons_symm {n : ℕ} {f : RealSpace (n + 1) → ℂ}
    (hf : Integrable f (unitCubeMeasure (n + 1))) :
    unitCubeIntegral f = ∫ y, (∫ x, f (Fin.cons x y) ∂unitIntervalMeasure)
      ∂unitCubeMeasure n := by
  have hp := (measurePreserving_piFinSuccAbove
    (fun _ : Fin (n + 1) => unitIntervalMeasure) 0).symm
  unfold unitCubeIntegral unitCubeMeasure
  rw [← hp.integral_comp']
  simpa only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Fin.insertNth_zero, Fin.zero_succAbove, Function.comp_def, Equiv.coe_fn_mk, cast_eq,
    unitCubeMeasure] using
      integral_prod_symm _ (integrable_cons_unitCube hf)

theorem integral_unitInterval_eq_interval (f : ℝ → ℂ) :
    (∫ x, f x ∂unitIntervalMeasure) = ∫ x in (0 : ℝ)..1, f x := by
  rw [intervalIntegral.integral_of_le zero_le_one]
  exact integral_Icc_eq_integral_Ioc

theorem unitCubeMeasure_eq_restrict_Ioc (n : ℕ) :
    unitCubeMeasure n = volume.restrict {x : RealSpace n | ∀ j, x j ∈ Ioc 0 1} := by
  have he : {x : RealSpace n | ∀ j, x j ∈ Ioc 0 1} = univ.pi (fun _ => Ioc 0 1) := by
    ext x
    simp
  rw [he]
  change Measure.pi (fun _ : Fin n => volume.restrict (Icc (0 : ℝ) 1)) =
    (Measure.pi (fun _ : Fin n => (volume : Measure ℝ))).restrict _
  rw [Measure.restrict_pi_pi]
  congr 1
  funext j
  exact (Measure.restrict_congr_set Ioc_ae_eq_Icc).symm

end KamProject.Arnold1963
