/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P3821T1AngularIncrement
public import Mathlib.Topology.Homotopy.Lifting

-- [TABLET NODE: P3821T1AngularIncrementLaws]

/-!
# P3821T1AngularIncrementLaws

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P3821T1AngularIncrementLaws :
    (∀ (g : C(unitInterval, ℂ)) (p : ℂ), (∀ t, g t ≠ p) →
      ∃ theta : C(unitInterval, ℝ),
        (∀ t, Complex.exp ((theta t : ℂ) * Complex.I) =
          (g t - p) / (‖g t - p‖ : ℂ)) ∧
        (∀ eta : C(unitInterval, ℝ),
          (∀ t, Complex.exp ((eta t : ℂ) * Complex.I) =
            (g t - p) / (‖g t - p‖ : ℂ)) →
          eta ⟨1, by norm_num⟩ - eta ⟨0, by norm_num⟩ =
            P3821T1AngularIncrement g p) ∧
        (g ⟨0, by norm_num⟩ = g ⟨1, by norm_num⟩ →
          ∃ n : ℤ, P3821T1AngularIncrement g p = 2 * Real.pi * n)) ∧
    (∀ (x y z p : ℂ) (g : Path x y) (h : Path y z),
      (∀ t, g t ≠ p) → (∀ t, h t ≠ p) →
      P3821T1AngularIncrement (g.trans h).toContinuousMap p =
        P3821T1AngularIncrement g.toContinuousMap p +
          P3821T1AngularIncrement h.toContinuousMap p) ∧
    (∀ (x y p : ℂ) (g : Path x y), (∀ t, g t ≠ p) →
      P3821T1AngularIncrement g.symm.toContinuousMap p =
        -P3821T1AngularIncrement g.toContinuousMap p) := by
-- BODY
  classical
  have lift_exists (g : C(unitInterval, ℂ)) (p : ℂ) (hg : ∀ t, g t ≠ p) :
      ∃ theta : C(unitInterval, ℝ), ∀ t,
        Complex.exp ((theta t : ℂ) * Complex.I) =
          (g t - p) / (‖g t - p‖ : ℂ) := by
    let n : C(unitInterval, Circle) :=
      ⟨fun t => ⟨(g t - p) / (‖g t - p‖ : ℂ), by
        apply mem_sphere_zero_iff_norm.mpr
        simp only [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_norm]
        exact div_self (norm_ne_zero_iff.mpr (sub_ne_zero.mpr (hg t)))⟩,
        by
          apply Continuous.subtype_mk
          exact (g.continuous.sub continuous_const).div
            (Complex.continuous_ofReal.comp (g.continuous.sub continuous_const).norm)
            (fun t => Complex.ofReal_ne_zero.mpr
              (norm_ne_zero_iff.mpr (sub_ne_zero.mpr (hg t))))⟩
    obtain ⟨theta, htheta, _⟩ := Circle.isCoveringMap_exp.exists_path_lifts n
      (Complex.arg (n 0)) (Circle.exp_arg (n 0)).symm
    exact ⟨theta, fun t => congrArg (fun u : Circle => (u : ℂ)) (congrFun htheta t)⟩
  have difference_eq (theta eta : C(unitInterval, ℝ))
      (h : ∀ t, Circle.exp (theta t) = Circle.exp (eta t)) :
      eta 1 - eta 0 = theta 1 - theta 0 := by
    let shifted : C(unitInterval, ℝ) :=
      ⟨fun t => eta t + (theta 0 - eta 0), by fun_prop⟩
    have hs : Circle.exp ∘ shifted = Circle.exp ∘ theta := by
      funext t
      change Circle.exp (eta t + (theta 0 - eta 0)) = Circle.exp (theta t)
      simp only [Circle.exp_add, Circle.exp_sub, h 0, div_self', mul_one, h t]
    have heq := Circle.isCoveringMap_exp.eq_of_comp_eq
      shifted.continuous theta.continuous hs 0 (by dsimp [shifted]; ring)
    have hv := congrFun heq 1
    dsimp [shifted] at hv
    linarith
  have increment_of_lift (g : C(unitInterval, ℂ)) (p : ℂ)
      (theta : C(unitInterval, ℝ))
      (htheta : ∀ t, Complex.exp ((theta t : ℂ) * Complex.I) =
        (g t - p) / (‖g t - p‖ : ℂ)) :
      P3821T1AngularIncrement g p = theta 1 - theta 0 := by
    unfold P3821T1AngularIncrement
    split_ifs with h
    · apply difference_eq theta (Classical.choose h)
      intro t
      apply Circle.ext
      simp only [Circle.coe_exp]
      exact (htheta t).trans ((Classical.choose_spec h) t).symm
    · exact (h ⟨theta, htheta⟩).elim
  refine ⟨?_, ?_, ?_⟩
  · intro g p hg
    obtain ⟨theta, htheta⟩ := lift_exists g p hg
    refine ⟨theta, htheta, ?_, ?_⟩
    · intro eta heta
      exact (increment_of_lift g p eta heta).symm
    · intro hclosed
      change g 0 = g 1 at hclosed
      have heq : Circle.exp (theta 1) = Circle.exp (theta 0) := by
        apply Circle.ext
        simp only [Circle.coe_exp]
        rw [htheta 1, htheta 0, hclosed]
      obtain ⟨n, hn⟩ := Circle.exp_eq_exp.mp heq
      refine ⟨n, ?_⟩
      rw [increment_of_lift g p theta htheta]
      linarith
  · intro x y z p g h hg hh
    obtain ⟨theta, htheta⟩ := lift_exists g.toContinuousMap p hg
    obtain ⟨eta, heta⟩ := lift_exists h.toContinuousMap p hh
    have hend : Circle.exp (theta 1) = Circle.exp (eta 0) := by
      apply Circle.ext
      simp only [Circle.coe_exp]
      rw [htheta 1, heta 0]
      simp only [Path.coe_toContinuousMap, Path.target, Path.source]
    let shifted : C(unitInterval, ℝ) :=
      ⟨fun t => eta t + (theta 1 - eta 0), by fun_prop⟩
    have hshifted (t : unitInterval) :
        Complex.exp ((shifted t : ℂ) * Complex.I) =
          (h t - p) / (‖h t - p‖ : ℂ) := by
      have hc : Circle.exp (shifted t) = Circle.exp (eta t) := by
        change Circle.exp (eta t + (theta 1 - eta 0)) = Circle.exp (eta t)
        simp only [Circle.exp_add, Circle.exp_sub, hend, div_self', mul_one]
      exact (congrArg (fun u : Circle => (u : ℂ)) hc).trans (heta t)
    let lg : Path (theta 0) (theta 1) := ⟨theta, rfl, rfl⟩
    let lh : Path (theta 1) (shifted 1) :=
      ⟨shifted, by dsimp [shifted]; ring, rfl⟩
    have hconcat (t : unitInterval) :
        Complex.exp (((lg.trans lh) t : ℂ) * Complex.I) =
          ((g.trans h) t - p) / (‖(g.trans h) t - p‖ : ℂ) := by
      rw [Path.trans_apply, Path.trans_apply]
      split_ifs with ht
      · exact htheta _
      · exact hshifted _
    rw [increment_of_lift (g.trans h).toContinuousMap p
      (lg.trans lh).toContinuousMap hconcat,
      increment_of_lift g.toContinuousMap p theta htheta,
      increment_of_lift h.toContinuousMap p eta heta]
    change (lg.trans lh) 1 - (lg.trans lh) 0 = _
    rw [Path.target, Path.source]
    dsimp only [shifted, ContinuousMap.coe_mk]
    ring
  · intro x y p g hg
    obtain ⟨theta, htheta⟩ := lift_exists g.toContinuousMap p hg
    let rev : C(unitInterval, ℝ) :=
      ⟨fun t => theta (unitInterval.symm t), by fun_prop⟩
    have hrev (t : unitInterval) :
        Complex.exp ((rev t : ℂ) * Complex.I) =
          (g.symm t - p) / (‖g.symm t - p‖ : ℂ) := by
      simpa only [rev, ContinuousMap.coe_mk, Path.symm_apply, Function.comp_apply,
        Path.coe_toContinuousMap]
        using htheta (unitInterval.symm t)
    rw [increment_of_lift g.symm.toContinuousMap p rev hrev,
      increment_of_lift g.toContinuousMap p theta htheta]
    simp only [rev, ContinuousMap.coe_mk, unitInterval.symm_one, unitInterval.symm_zero]
    ring

end ApollonianSuperharmonic

end
