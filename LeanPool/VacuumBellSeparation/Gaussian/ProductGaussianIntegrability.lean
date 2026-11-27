/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.Pi

/-!
# Product Gaussian integrability excludes every nonpositive coefficient

The converse uses actual almost-everywhere integrability of scalar slices
of a product-space integrable function. The other coordinates contribute
a strictly positive finite scalar. This avoids products of totalized
Bochner integrals, which cannot detect a divergent coordinate reliably.
-/

@[expose] public section

namespace VacuumBellSeparation.Gaussian

open MeasureTheory

theorem integrable_fin_productGaussian_iff {n : ℕ} (d : Fin n → ℝ) :
    Integrable (fun x : Fin n → ℝ => ∏ i, Real.exp (-d i * (x i) ^ 2)) ↔
      ∀ i, 0 < d i := by
  constructor
  · intro h i
    cases n with
    | zero => exact Fin.elim0 i
    | succ n =>
      let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i
      have hp := (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i).symm
        |>.integrable_comp_of_integrable h
      have heq : (fun p : ℝ × (Fin n → ℝ) =>
          (∏ j, Real.exp (-d j * (e.symm p j) ^ 2))) =
        fun p => Real.exp (-d i * p.1 ^ 2) *
          ∏ j : Fin n, Real.exp (-d (i.succAbove j) * (p.2 j) ^ 2) := by
        funext p
        rw [Fin.prod_univ_succAbove _ i]
        simp only [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
          Equiv.coe_fn_mk, Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
      change Integrable (fun p : ℝ × (Fin n → ℝ) =>
        ∏ j, Real.exp (-d j * (e.symm p j) ^ 2)) at hp
      rw [heq] at hp
      obtain ⟨y, hy⟩ := hp.prod_left_ae.exists
      have hc : IsUnit (∏ j : Fin n, Real.exp (-d (i.succAbove j) * (y j) ^ 2)) :=
        isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun j _ => Real.exp_ne_zero _)
      exact integrable_exp_neg_mul_sq_iff.mp ((integrable_mul_const_iff hc _).mp hy)
  · intro hd
    exact Integrable.fintype_prod fun i => integrable_exp_neg_mul_sq (hd i)

theorem integrable_productGaussian_iff {ι : Type*} [Fintype ι] (d : ι → ℝ) :
    Integrable (fun x : ι → ℝ => ∏ i, Real.exp (-d i * (x i) ^ 2)) ↔
      ∀ i, 0 < d i := by
  classical
  constructor
  · intro h
    let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
    let E := MeasurableEquiv.piCongrLeft (fun _ : ι => ℝ) e
    have hp := (volume_measurePreserving_piCongrLeft (fun _ : ι => ℝ) e)
      |>.integrable_comp_of_integrable h
    have heq : (fun x : Fin (Fintype.card ι) → ℝ =>
        ∏ i, Real.exp (-d i * (E x i) ^ 2)) =
      fun x => ∏ j, Real.exp (-d (e j) * (x j) ^ 2) := by
      funext x
      rw [← e.prod_comp (fun i => Real.exp (-d i * (E x i) ^ 2))]
      apply Finset.prod_congr rfl
      intro j _
      simp only [E, MeasurableEquiv.piCongrLeft_apply_apply]
    change Integrable (fun x : Fin (Fintype.card ι) → ℝ =>
      ∏ i, Real.exp (-d i * (E x i) ^ 2)) at hp
    rw [heq] at hp
    have hd := (integrable_fin_productGaussian_iff (fun j => d (e j))).mp hp
    intro i
    simpa only [e.apply_symm_apply] using hd (e.symm i)
  · intro hd
    exact Integrable.fintype_prod fun i => integrable_exp_neg_mul_sq (hd i)

end VacuumBellSeparation.Gaussian
