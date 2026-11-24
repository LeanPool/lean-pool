/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.PlurisubharmonicLimits

/-!
# Fatou stability for moving disc-submean inequalities

This file isolates the Fatou half of the locally bounded PSH supremum
theorem.  The approximating functions satisfy `DiscPshOn` on one common
domain, but the centers of the tested discs may move.  A common finite upper
bound makes their nonnegative extended-real deficits measurable.  Pointwise
`limsup` domination on the boundary and convergence at the center then pass
the disc-submean inequality to the target.

The local-to-global theorem upgrading germwise `PlurisubharmonicOn` to a
common-domain `DiscPshOn` hypothesis is deliberately not asserted here.
-/

@[expose] public section

open Set Filter Metric MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.FirstPass

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A finite nonnegative deficit turns a boundary `limsup` domination into
the pointwise `liminf` inequality required by Fatou's lemma.  This statement
retains both infinite values of `EReal`. -/
theorem finiteDeficit_le_liminf_of_limsup_le (C : ℝ) (z : ℕ → EReal)
    (w : EReal) (hzw : limsup z atTop ≤ w) :
    ((C : EReal) - w).toENNReal ≤
      liminf (fun n => ((C : EReal) - z n).toENNReal) atTop := by
  let d : EReal → ℝ≥0∞ := fun a => ((C : EReal) - a).toENNReal
  have hd : Antitone d := by
    intro a b hab
    exact EReal.toENNReal_le_toENNReal (EReal.sub_le_sub le_rfl hab)
  calc
    d w ≤ d (limsup z atTop) := hd hzw
    _ = liminf (d ∘ z) atTop :=
      hd.map_limsup_of_continuousAt z (continuous_finiteDeficit C).continuousAt
    _ = liminf (fun n => ((C : EReal) - z n).toENNReal) atTop := rfl

/-- Fatou's lemma for a sequence of disc-PSH functions tested on discs with
moving centers.  The conclusion is the exact comparison between the target
boundary deficit and the `liminf` of the approximating circle deficits. -/
theorem circleDeficit_le_liminf_of_moving_centers
    {u : ℕ → E → EReal} {w : E → EReal} {V : Set E}
    (hu : ∀ n, DiscPshOn (u n) V)
    (x : E) (centers : ℕ → E) (v : E) {r : ℝ} (hr : 0 ≤ r)
    (hD : ∀ n, affineClosedDisc (centers n) v r ⊆ V) (C : ℝ)
    (hboundary : ∀ t : ℝ,
      limsup (fun n => u n (centers n + circleMap 0 r t • v)) atTop ≤
        w (x + circleMap 0 r t • v)) :
    circleDeficit w x v r C ≤
      liminf (fun n => circleDeficit (u n) (centers n) v r C) atTop := by
  unfold circleDeficit
  calc
    (∫⁻ t in Ioc 0 (2 * Real.pi),
        ((C : EReal) - w (x + circleMap 0 r t • v)).toENNReal) ≤
        ∫⁻ t in Ioc 0 (2 * Real.pi),
          liminf (fun n =>
            ((C : EReal) -
              u n (centers n + circleMap 0 r t • v)).toENNReal) atTop := by
      apply lintegral_mono
      intro t
      exact finiteDeficit_le_liminf_of_limsup_le C
        (fun n => u n (centers n + circleMap 0 r t • v))
        (w (x + circleMap 0 r t • v)) (hboundary t)
    _ ≤ liminf (fun n =>
        ∫⁻ t in Ioc 0 (2 * Real.pi),
          ((C : EReal) -
            u n (centers n + circleMap 0 r t • v)).toENNReal) atTop := by
      exact lintegral_liminf_le fun n =>
        (hu n).measurable_circle_deficit (centers n) v hr (hD n) C

/-- The moving-center Fatou argument passes the full disc-submean inequality
to a target.  All analytic approximation input is explicit: common-domain
disc PSH, a common finite majorant on the moving discs, center convergence,
and boundary `limsup` domination. -/
theorem circleSubmean_of_moving_discPsh
    {u : ℕ → E → EReal} {w : E → EReal} {V : Set E}
    (hu : ∀ n, DiscPshOn (u n) V)
    (x : E) (centers : ℕ → E) (v : E) {r : ℝ} (hr : 0 < r)
    (hD : ∀ n, affineClosedDisc (centers n) v r ⊆ V) (C : ℝ)
    (hC : ∀ n, ∀ y ∈ affineClosedDisc (centers n) v r,
      u n y ≤ (C : EReal))
    (hcenter : Tendsto (fun n => u n (centers n)) atTop (𝓝 (w x)))
    (hboundary : ∀ t : ℝ,
      limsup (fun n => u n (centers n + circleMap 0 r t • v)) atTop ≤
        w (x + circleMap 0 r t • v)) :
    circleDeficit w x v r C ≤
      ENNReal.ofReal (2 * Real.pi) * ((C : EReal) - w x).toENNReal := by
  let d : EReal → ℝ≥0∞ := fun a => ((C : EReal) - a).toENNReal
  have hdcenter : Tendsto (fun n => d (u n (centers n))) atTop (𝓝 (d (w x))) :=
    (continuous_finiteDeficit C).continuousAt.tendsto.comp hcenter
  calc
    circleDeficit w x v r C ≤
        liminf (fun n => circleDeficit (u n) (centers n) v r C) atTop :=
      circleDeficit_le_liminf_of_moving_centers hu x centers v hr.le hD C hboundary
    _ ≤ liminf (fun n => ENNReal.ofReal (2 * Real.pi) *
        ((C : EReal) - u n (centers n)).toENNReal) atTop := by
      simp only [liminf_eq_iSup_iInf_of_nat]
      exact iSup_mono fun _ => iInf_mono fun n => iInf_mono fun _ =>
        (hu n).submean (centers n) v r hr (hD n) C (hC n)
    _ = ENNReal.ofReal (2 * Real.pi) *
        liminf (fun n => d (u n (centers n))) atTop :=
      ENNReal.liminf_const_mul_of_ne_top ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (2 * Real.pi) * ((C : EReal) - w x).toENNReal := by
      rw [hdcenter.liminf_eq]

/-- All data needed to recover the submean inequality of `w` on one fixed
disc from a sequence of disc-PSH functions.  The sequence has one common
domain, while its centers are allowed to move. -/
structure MovingDiscPshApproximation (w : E → EReal) (x v : E) (r : ℝ) where
  /-- The open set on which the sequence is studied. -/
  domain : Set E
  /-- The sequence of plurisubharmonic potentials. -/
  potential : ℕ → E → EReal
  /-- The centers used for the analytic discs. -/
  centers : ℕ → E
  /-- The common upper bound on the potentials. -/
  bound : ℝ
  discPsh : ∀ n, DiscPshOn (potential n) domain
  disc_subset : ∀ n, affineClosedDisc (centers n) v r ⊆ domain
  potential_le_bound : ∀ n, ∀ y ∈ affineClosedDisc (centers n) v r,
    potential n y ≤ (bound : EReal)
  target_le_bound : ∀ y ∈ affineClosedDisc x v r, w y ≤ (bound : EReal)
  center_tendsto : Tendsto (fun n => potential n (centers n)) atTop (𝓝 (w x))
  boundary_limsup_le : ∀ t : ℝ,
    limsup (fun n => potential n (centers n + circleMap 0 r t • v)) atTop ≤
      w (x + circleMap 0 r t • v)

/-- A target admits moving disc-PSH approximations on a set when every
positive-radius affine closed disc in the set has approximation data with a
common finite majorant. -/
def HasMovingDiscPshApproximations (w : E → EReal) (U : Set E) : Prop :=
  ∀ (x v : E) (r : ℝ), 0 < r → affineClosedDisc x v r ⊆ U →
    Nonempty (MovingDiscPshApproximation w x v r)

/-- The Fatou argument for one packaged moving-disc approximation. -/
theorem MovingDiscPshApproximation.circleSubmean
    {w : E → EReal} {x v : E} {r : ℝ}
    (A : MovingDiscPshApproximation w x v r) (hr : 0 < r) :
    circleDeficit w x v r A.bound ≤
      ENNReal.ofReal (2 * Real.pi) * ((A.bound : EReal) - w x).toENNReal :=
  circleSubmean_of_moving_discPsh A.discPsh x A.centers v hr A.disc_subset
    A.bound A.potential_le_bound A.center_tendsto A.boundary_limsup_le

/-- A target with explicit moving common-domain disc-PSH approximations
satisfies the full disc criterion.  Upper semicontinuity and exclusion of
positive infinity are kept separate because the Fatou argument supplies
exactly the submean field. -/
theorem discPshOn_of_hasMovingDiscPshApproximations
    {w : E → EReal} {U : Set E}
    (hne : ∀ x ∈ U, w x ≠ ⊤) (husc : UpperSemicontinuousOn w U)
    (happrox : HasMovingDiscPshApproximations w U) : DiscPshOn w U := by
  refine ⟨hne, husc, ?_⟩
  intro x v r hr hD C hC
  let A := (happrox x v r hr hD).some
  have hA := A.circleSubmean hr
  rcases le_total C A.bound with hCA | hAC
  · have ha : 0 ≤ A.bound - C := sub_nonneg.mpr hCA
    apply (discSubmean_add_bound_iff x v hr.le C (A.bound - C) ha hC).mp
    convert hA using 1 <;> ring_nf
  · have ha : 0 ≤ C - A.bound := sub_nonneg.mpr hAC
    have hraised :=
      (discSubmean_add_bound_iff x v hr.le A.bound (C - A.bound) ha
        A.target_le_bound).mpr hA
    convert hraised using 1 <;> ring_nf

end

end SGPT.Foundations.Analysis.FirstPass
