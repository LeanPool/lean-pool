/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.PolydiscCauchyCoefficients

/-!
# Repeated Cauchy formula on the actual closed polydisc

All frozen coordinates may lie on the boundary. Ambient differentiability
at each point of the closed polydisc supplies every one-variable slice;
the repeated formula follows without differentiating an integral.
-/

@[expose] public section

open Complex MeasureTheory Set Metric

namespace VacuumBellSeparation.Gaussian

/-- The iterated Cauchy integral over the coordinate circles of a complex polydisc. -/
noncomputable def polydiscCauchyTransform :
    (n : ℕ) → ℝ → ((Fin n → ℂ) → ℂ) → (Fin n → ℂ) → ℂ
  | 0, _, F, _ => F Fin.elim0
  | n + 1, R, F, x => (2 * Real.pi * I : ℂ)⁻¹ •
      ∮ z in C(0, R), (z - x 0)⁻¹ • polydiscCauchyTransform n R
        (fun w => F (Fin.cons z w)) (fun j => x j.succ)

theorem coordinateClosedPolydisc_cons {n : ℕ} {R : ℝ} {z : ℂ} {w : Fin n → ℂ}
    (hz : ‖z‖ ≤ R) (hw : w ∈ coordinateClosedPolydisc n R) :
    Fin.cons z w ∈ coordinateClosedPolydisc (n + 1) R := by
  intro j
  refine Fin.cases ?_ (fun i => ?_) j
  · simpa only [Fin.cons_zero] using hz
  · simpa only [Fin.cons_succ] using hw i

theorem polydisc_slice_diffContOnCl {n : ℕ} {R : ℝ}
    (F : (Fin (n + 1) → ℂ) → ℂ)
    (hF : ∀ x ∈ coordinateClosedPolydisc (n + 1) R, DifferentiableAt ℂ F x)
    (w : Fin n → ℂ) (hw : w ∈ coordinateClosedPolydisc n R) :
    DiffContOnCl ℂ (fun z => F (Fin.cons z w)) (ball 0 R) := by
  have hd : DifferentiableOn ℂ (fun z => F (Fin.cons z w)) (closedBall 0 R) := by
    intro z hz
    apply DifferentiableAt.differentiableWithinAt
    apply (hF (Fin.cons z w) (coordinateClosedPolydisc_cons
      (by simpa only [mem_closedBall_zero_iff] using hz) hw)).comp z
    apply differentiableAt_pi.mpr
    intro j
    refine Fin.cases ?_ (fun i => ?_) j
    · change DifferentiableAt ℂ (fun ζ : ℂ => ζ) z
      exact differentiableAt_id
    · simpa only [Fin.cons_succ] using (differentiableAt_const (c := w i) :
        DifferentiableAt ℂ (fun _ : ℂ => w i) z)
  exact (hd.mono closure_ball_subset_closedBall).diffContOnCl

theorem polydiscCauchyTransform_eq (n : ℕ) {R : ℝ} (hR : 0 < R)
    (F : (Fin n → ℂ) → ℂ)
    (hF : ∀ x ∈ coordinateClosedPolydisc n R, DifferentiableAt ℂ F x)
    (x : Fin n → ℂ) (hx : ∀ j, ‖x j‖ < R) :
    polydiscCauchyTransform n R F x = F x := by
  induction n with
  | zero =>
    change F Fin.elim0 = F x
    congr 1
    funext j
    exact Fin.elim0 j
  | succ n ih =>
    have htail (z : ℂ) (hz : ‖z‖ = R) :
        polydiscCauchyTransform n R (fun w => F (Fin.cons z w))
          (fun j => x j.succ) = F (Fin.cons z (fun j => x j.succ)) := by
      apply ih
      · intro w hw
        apply (hF (Fin.cons z w) (coordinateClosedPolydisc_cons hz.le hw)).comp w
        apply differentiableAt_pi.mpr
        intro j
        refine Fin.cases ?_ (fun i => ?_) j
        · simpa only [Fin.cons_zero] using (differentiableAt_const (c := z) :
            DifferentiableAt ℂ (fun _ : Fin n → ℂ => z) w)
        · simpa only [Fin.cons_succ] using (differentiableAt_apply i w :
            DifferentiableAt ℂ (fun w : Fin n → ℂ => w i) w)
      · exact fun j => hx j.succ
    change (2 * Real.pi * I : ℂ)⁻¹ • _ = F x
    rw [circleIntegral.integral_congr hR.le (fun z hz => by
      rw [htail z (by simpa only [mem_sphere_zero_iff_norm] using hz)])]
    have hs := polydisc_slice_diffContOnCl F hF (fun j => x j.succ)
      (fun j => (hx j.succ).le)
    rw [hs.two_pi_i_inv_smul_circleIntegral_sub_inv_smul
      (by simpa only [mem_ball_zero_iff] using hx 0)]
    congr 1
    exact Fin.cons_self_tail x

end VacuumBellSeparation.Gaussian
