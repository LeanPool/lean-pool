/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

-- Adapted for Lean Pool's pinned Lean and Mathlib; upstream commit is recorded in projects.yml.
module

public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Analysis.SpecialFunctions.Pow.Real


/-!
# Ball means and the Campanato decay hypothesis

The `C^{k,α}` scale of Schauder theory rests on Campanato's characterisation of Hölder
continuity: a function whose mean oscillation over balls decays like `r^α` has a Hölder
representative of exponent `α`. This file fixes the two objects that characterisation is
stated through, the mean

  `u_{x,r} = ⨍_{B(x,r)} u`

written `ballAverage u x r`, and the decay hypothesis

  `∫_{B(x,r)} |u - u_{x,r}|² ≤ M² r^{d + 2α}` for every ball `B(x,r) ⊆ Ω`,

written `CampanatoOn Ω u α M`. The hypothesis quantifies over balls contained in `Ω`, which is
the form property (H3) of Fernández-Real and Ros-Oton takes, so every mean in sight is a mean
over a ball and has the exact volume `r^d · |B(0,1)|`.

The rest of the file records what the estimates downstream need: the volume of a ball as a real
number, and the integrability of `u` and of `(u - c)²` on a ball, both read off from
`MemLp u 2 (volume.restrict Ω)`.
-/

@[expose] public section

open MeasureTheory Set Metric

open scoped NNReal ENNReal

noncomputable section

namespace EllipticPdes.Campanato

variable {d : ℕ}

/-- The volume of the unit ball of `EuclideanSpace ℝ (Fin d)`, as a real number. Every ball
volume in this library is a multiple of it, so it is convenient to name it once. -/
def unitBallVolume (d : ℕ) : ℝ :=
  (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal

/-- The unit ball has positive volume. -/
theorem unitBallVolume_pos : 0 < unitBallVolume d := by
  rw [unitBallVolume]
  exact ENNReal.toReal_pos (measure_ball_pos volume _ one_pos).ne' measure_ball_lt_top.ne

/-- The volume of `B(x, r)` is `r^d` times the volume of the unit ball. -/
theorem measureReal_ball (x : EuclideanSpace ℝ (Fin d)) {r : ℝ} (hr : 0 < r) :
    volume.real (Metric.ball x r) = r ^ d * unitBallVolume d := by
  rw [measureReal_def, Measure.addHaar_ball_of_pos volume x hr, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity), finrank_euclideanSpace_fin, unitBallVolume]

/-- The volume of `B(x, r)` written with a real exponent, the form the decay hypothesis uses. -/
theorem measureReal_ball_rpow (x : EuclideanSpace ℝ (Fin d)) {r : ℝ} (hr : 0 < r) :
    volume.real (Metric.ball x r) = r ^ (d : ℝ) * unitBallVolume d := by
  rw [measureReal_ball x hr, Real.rpow_natCast]

/-- The restriction of Lebesgue measure to a ball is finite. -/
instance isFiniteMeasure_restrict_ball (x : EuclideanSpace ℝ (Fin d)) (r : ℝ) :
    IsFiniteMeasure (volume.restrict (Metric.ball x r)) :=
  ⟨by rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩

/-- **Mean of `u` over the ball `B(x, r)`.** Campanato's hypothesis measures the oscillation
of `u` about this value, and the characterisation produces the Hölder representative as the limit
of these means as `r → 0`. -/
def ballAverage (u : EuclideanSpace ℝ (Fin d) → ℝ) (x : EuclideanSpace ℝ (Fin d)) (r : ℝ) : ℝ :=
  ⨍ y in Metric.ball x r, u y

/-- **Campanato decay hypothesis.** The mean oscillation of `u` over every ball contained in
`Ω` decays at the rate `r^{d + 2α}`, with constant `M`. For `0 < α ≤ 1` this forces `u` to have a
Hölder representative of exponent `α` on the interior of `Ω`; that is the content of
`EllipticPdes.Campanato.campanato_holderOnWith`. -/
def CampanatoOn (Ω : Set (EuclideanSpace ℝ (Fin d))) (u : EuclideanSpace ℝ (Fin d) → ℝ)
    (α M : ℝ) : Prop :=
  ∀ (x : EuclideanSpace ℝ (Fin d)) (r : ℝ), 0 < r → Metric.ball x r ⊆ Ω →
    ∫ y in Metric.ball x r, (u y - ballAverage u x r) ^ 2 ≤ M ^ 2 * r ^ ((d : ℝ) + 2 * α)

/-- The decay hypothesis weakens when the constant grows. -/
theorem CampanatoOn.mono {Ω : Set (EuclideanSpace ℝ (Fin d))} {u : EuclideanSpace ℝ (Fin d) → ℝ}
    {α M M' : ℝ} (h : CampanatoOn Ω u α M) (hM : 0 ≤ M) (hMM : M ≤ M') :
    CampanatoOn Ω u α M' := by
  intro x r hr hsub
  refine (h x r hr hsub).trans (mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hr.le _))
  exact pow_le_pow_left₀ hM hMM 2

/-- The decay hypothesis shrinks with the domain. -/
theorem CampanatoOn.mono_set {Ω Ω' : Set (EuclideanSpace ℝ (Fin d))}
    {u : EuclideanSpace ℝ (Fin d) → ℝ} {α M : ℝ} (h : CampanatoOn Ω u α M) (hΩ : Ω' ⊆ Ω) :
    CampanatoOn Ω' u α M :=
  fun x r hr hsub => h x r hr (hsub.trans hΩ)

section Integrability

variable {Ω : Set (EuclideanSpace ℝ (Fin d))} {u : EuclideanSpace ℝ (Fin d) → ℝ}

/-- Square integrability on `Ω` restricts to any ball inside `Ω`. -/
theorem memLp_two_ball (hu : MemLp u 2 (volume.restrict Ω)) {x : EuclideanSpace ℝ (Fin d)}
    {r : ℝ} (hsub : Metric.ball x r ⊆ Ω) : MemLp u 2 (volume.restrict (Metric.ball x r)) :=
  hu.mono_measure (Measure.restrict_mono hsub le_rfl)

/-- Subtracting a constant preserves square integrability on a ball. -/
theorem memLp_two_sub_const (hu : MemLp u 2 (volume.restrict Ω))
    {x : EuclideanSpace ℝ (Fin d)} {r : ℝ} (hsub : Metric.ball x r ⊆ Ω) (c : ℝ) :
    MemLp (fun y => u y - c) 2 (volume.restrict (Metric.ball x r)) :=
  (memLp_two_ball hu hsub).sub (memLp_const c)

/-- The squared deviation of `u` from a constant is integrable on a ball inside `Ω`. -/
theorem integrableOn_sq_sub_const (hu : MemLp u 2 (volume.restrict Ω))
    {x : EuclideanSpace ℝ (Fin d)} {r : ℝ} (hsub : Metric.ball x r ⊆ Ω) (c : ℝ) :
    IntegrableOn (fun y => (u y - c) ^ 2) (Metric.ball x r) volume :=
  (memLp_two_sub_const hu hsub c).integrable_sq

end Integrability

end EllipticPdes.Campanato
