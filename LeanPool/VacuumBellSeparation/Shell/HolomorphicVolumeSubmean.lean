/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Shell.HolomorphicDiskSubmean
public import LeanPool.VacuumBellSeparation.Gaussian.PolydiscCauchyFormula
public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Submean on actual finite products of complex disks

The measure is complex product Lebesgue volume restricted to the open
coordinate polydisc. Iterating the genuine disk inequality and Tonelli
gives the exact volume factor, including the zero-dimensional case.
-/

@[expose] public section

namespace VacuumBellSeparation

open Complex MeasureTheory Metric Set
open scoped ENNReal
open Gaussian

/-- Complex polydisc measure given by `Measure.pi fun _ : Fin n => volume.restrict (ball (0 : ℂ)
R)`. -/
noncomputable def complexPolydiscMeasure (n : ℕ) (R : ℝ) : Measure (Fin n → ℂ) :=
  Measure.pi fun _ : Fin n => volume.restrict (ball (0 : ℂ) R)

/-- The product of the open complex discs of the same radius, each centered at zero. -/
noncomputable def coordinateOpenPolydisc (n : ℕ) (R : ℝ) : Set (Fin n → ℂ) :=
  Set.univ.pi fun _ => ball (0 : ℂ) R

theorem complexPolydiscMeasure_eq_restrict (n : ℕ) (R : ℝ) :
    complexPolydiscMeasure n R = volume.restrict (coordinateOpenPolydisc n R) := by
  exact (Measure.restrict_pi_pi (fun _ : Fin n => (volume : Measure ℂ))
    (fun _ => ball (0 : ℂ) R)).symm

theorem complexPolydiscMeasure_univ (n : ℕ) (R : ℝ) :
    complexPolydiscMeasure n R univ = volume (ball (0 : ℂ) R) ^ n := by
  simp only [complexPolydiscMeasure, Measure.pi_univ, Measure.restrict_apply_univ,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem complexPolydisc_lintegral_succ (n : ℕ) (R : ℝ)
    (g : (Fin (n + 1) → ℂ) → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ z, g z ∂complexPolydiscMeasure (n + 1) R) =
      ∫⁻ z in ball (0 : ℂ) R, ∫⁻ w, g (Fin.cons z w) ∂complexPolydiscMeasure n R := by
  let : SFinite (complexPolydiscMeasure n R) := by
    unfold complexPolydiscMeasure
    infer_instance
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℂ) 0).symm
  have he := (measurePreserving_piFinSuccAbove
    (fun _ : Fin (n + 1) => volume.restrict (ball (0 : ℂ) R)) 0).symm
  have heq : (fun p : ℂ × (Fin n → ℂ) => g (e p)) =
      (fun p => g (Fin.cons p.1 p.2)) := by
    funext p
    simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
  calc
    _ = ∫⁻ p : ℂ × (Fin n → ℂ), g (e p)
        ∂(volume.restrict (ball (0 : ℂ) R)).prod (complexPolydiscMeasure n R) :=
      (he.lintegral_comp_emb e.measurableEmbedding g).symm
    _ = _ := by
      have hp := hg.comp e.measurable
      change Measurable (fun p => g (e p)) at hp
      rw [heq] at hp ⊢
      exact lintegral_prod _ hp.aemeasurable

theorem holomorphic_polydisc_lintegral_submean_sq (n : ℕ) {R : ℝ} (hR : 0 < R)
    (F : (Fin n → ℂ) → ℂ) (hm : Measurable F)
    (hF : ∀ z ∈ coordinateClosedPolydisc n R, DifferentiableAt ℂ F z) :
    ENNReal.ofReal (‖F 0‖ ^ 2) * volume (ball (0 : ℂ) R) ^ n ≤
      ∫⁻ z, ENNReal.ofReal (‖F z‖ ^ 2) ∂complexPolydiscMeasure n R := by
  induction n with
  | zero =>
    have hzero : (fun z : Fin 0 → ℂ => ENNReal.ofReal (‖F z‖ ^ 2)) =
        (fun _ => ENNReal.ofReal (‖F 0‖ ^ 2)) := by
      funext z
      exact congrArg (fun w => ENNReal.ofReal (‖F w‖ ^ 2)) (Subsingleton.elim z 0)
    simp only [hzero, lintegral_const, complexPolydiscMeasure_univ, le_refl]
  | succ n ih =>
    have hfirst : Measurable (fun z : ℂ => F (Fin.cons z (0 : Fin n → ℂ))) := by
      apply hm.comp
      apply Measurable.of_eval
      intro j
      refine Fin.cases ?_ (fun i => ?_) j
      · change Measurable (fun z : ℂ => z)
        exact measurable_id
      · change Measurable (fun _ : ℂ => (0 : ℂ))
        exact measurable_const
    have htail (z : ℂ) (hz : z ∈ ball (0 : ℂ) R) :
        ENNReal.ofReal (‖F (Fin.cons z (0 : Fin n → ℂ))‖ ^ 2) *
          volume (ball (0 : ℂ) R) ^ n ≤
        ∫⁻ w, ENNReal.ofReal (‖F (Fin.cons z w)‖ ^ 2) ∂complexPolydiscMeasure n R := by
      refine ih (fun w : Fin n → ℂ => F (Fin.cons z w)) ?_ ?_
      · apply hm.comp
        apply Measurable.of_eval
        intro j
        refine Fin.cases ?_ (fun i => ?_) j
        · change Measurable (fun _ : Fin n → ℂ => z)
          exact measurable_const
        · change Measurable (fun w : Fin n → ℂ => w i)
          exact measurable_pi_apply i
      · intro w hw
        apply (hF (Fin.cons z w) (coordinateClosedPolydisc_cons
          ((mem_ball_zero_iff.mp hz).le) hw)).comp w
        apply differentiableAt_pi.mpr
        intro j
        refine Fin.cases ?_ (fun i => ?_) j
        · simpa only [Fin.cons_zero] using (differentiableAt_const (c := z) :
            DifferentiableAt ℂ (fun _ : Fin n → ℂ => z) w)
        · simpa only [Fin.cons_succ] using (differentiableAt_apply i w :
            DifferentiableAt ℂ (fun w : Fin n → ℂ => w i) w)
    have hdisk := holomorphic_disk_lintegral_submean_sq hfirst
      (polydisc_slice_diffContOnCl F hF (0 : Fin n → ℂ)
        (fun j => by simpa using hR.le))
    have hcons : Fin.cons (α := fun _ : Fin (n + 1) => ℂ) (0 : ℂ) (0 : Fin n → ℂ) = 0 := by
      ext j
      refine Fin.cases ?_ (fun i => ?_) j <;> rfl
    rw [hcons] at hdisk
    have hfinite : volume (ball (0 : ℂ) R) ^ n ≠ ⊤ := by
      rw [Complex.volume_ball]
      exact ENNReal.pow_ne_top (by finiteness)
    calc
      _ = (ENNReal.ofReal (‖F 0‖ ^ 2) * volume (ball (0 : ℂ) R)) *
          volume (ball (0 : ℂ) R) ^ n := by
            rw [pow_succ (volume (ball (0 : ℂ) R)) n]
            ac_rfl
      _ ≤ (∫⁻ z in ball (0 : ℂ) R,
          ENNReal.ofReal (‖F (Fin.cons z (0 : Fin n → ℂ))‖ ^ 2)) *
          volume (ball (0 : ℂ) R) ^ n := _root_.mul_le_mul_left hdisk _
      _ = ∫⁻ z in ball (0 : ℂ) R,
          ENNReal.ofReal (‖F (Fin.cons z (0 : Fin n → ℂ))‖ ^ 2) *
          volume (ball (0 : ℂ) R) ^ n := (lintegral_mul_const' _ _ hfinite).symm
      _ ≤ ∫⁻ z in ball (0 : ℂ) R,
          ∫⁻ w, ENNReal.ofReal (‖F (Fin.cons z w)‖ ^ 2) ∂complexPolydiscMeasure n R := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
        exact htail z hz
      _ = _ := (complexPolydisc_lintegral_succ n R _
        (ENNReal.measurable_ofReal.comp (hm.norm.pow_const 2))).symm

/-- The integral is the actual product Lebesgue integral on the polydisc. -/
theorem holomorphic_volume_submean_sq (n : ℕ) {R : ℝ} (hR : 0 < R)
    (F : (Fin n → ℂ) → ℂ) (hm : Measurable F)
    (hF : ∀ z ∈ coordinateClosedPolydisc n R, DifferentiableAt ℂ F z) :
    ENNReal.ofReal (‖F 0‖ ^ 2) * volume (ball (0 : ℂ) R) ^ n ≤
      ∫⁻ z in coordinateOpenPolydisc n R, ENNReal.ofReal (‖F z‖ ^ 2) := by
  simpa only [complexPolydiscMeasure_eq_restrict] using
    holomorphic_polydisc_lintegral_submean_sq n hR F hm hF

end VacuumBellSeparation
