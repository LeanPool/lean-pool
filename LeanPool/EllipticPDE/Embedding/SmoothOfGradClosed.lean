/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
module

public import LeanPool.EllipticPDE.Embedding.SobolevLadder
public import LeanPool.EllipticPDE.Embedding.ClassicalDeriv


/-!
# Smoothness of a family closed under differentiation

Put the two halves together. The Sobolev ladder raises every member of a family closed under weak
differentiation from `L²` to `L^{2d}` on an inner ball, Morrey turns that into a Hölder
representative, and the representatives inherit the weak gradients of the members they represent.
A continuous function with a continuous weak gradient is classically differentiable, so each
representative is differentiable with its derivative again in the family, and an induction on the
order reads that as `C^∞`.

Only one ball is lost, at the Morrey step. The ladder shrinks internally between the two radii
it is given, and the differentiability argument runs on the inner ball itself, since the
derivative of a representative is a representative. Were the derivative to force a further
shrinking, no fixed ball would serve every order.

## Main declarations

* `EllipticPdes.Embedding.contDiffOn_of_gradClosed`: smooth representatives for a family closed
  under weak differentiation.
-/

@[expose] public section

open MeasureTheory Set Metric
open scoped NNReal ENNReal

noncomputable section

namespace EllipticPdes.Embedding

variable {d : ℕ}

/-- **Smooth representatives of a family closed under weak differentiation.** Let `F` assign a
function to each index, let `nxt i k` name a weak `k`-derivative of `F i` on `Metric.ball c R`,
and let every member lie in `L²` there. Then on any smaller concentric ball every member has a
representative smooth to every order.

The representatives are produced together, one per index, because the derivative of the
representative of `F i` has to be the representative of `F (nxt i k)` rather than some other
function agreeing with it almost everywhere. Continuity is what makes the choice rigid: two
continuous representatives of one class on an open ball are equal. -/
theorem contDiffOn_of_gradClosed (hd : 0 < d) (c : EuclideanSpace ℝ (Fin d)) {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) {ι : Type*} {F : ι → EuclideanSpace ℝ (Fin d) → ℝ}
    {nxt : ι → Fin d → ι}
    (hgrad : ∀ i, HasWeakGradOn (Metric.ball c R) (F i) (fun k => F (nxt i k)))
    (hmem : ∀ i, MemLp (F i) 2 (volume.restrict (Metric.ball c R))) :
    ∃ v : ι → EuclideanSpace ℝ (Fin d) → ℝ,
      (∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (v i) (Metric.ball c r)) ∧
        ∀ i, v i =ᵐ[volume.restrict (Metric.ball c r)] F i := by
  classical
  have : IsFiniteMeasure (volume.restrict (Metric.ball c r)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hp : (d : ℝ) < 2 * (d : ℝ) := by linarith
  have hp0 : (0 : ℝ) < 2 * (d : ℝ) := by linarith
  -- The ladder, and the exponent it lands on read as an extended real.
  have hladder : ∀ i, MemLp (F i) (ENNReal.ofReal (2 * (d : ℝ)))
      (volume.restrict (Metric.ball c r)) := by
    intro i
    have h := memLp_two_mul_of_gradClosed hd c hr hrR hgrad hmem i
    have hcast : ENNReal.ofReal (2 * (d : ℝ)) = ((2 * (d : ℝ≥0) : ℝ≥0) : ℝ≥0∞) := by
      rw [← ENNReal.ofReal_coe_nnreal]
      congr 1
    rwa [hcast]
  have hFint : ∀ i, IntegrableOn (F i) (Metric.ball c r) volume := fun i =>
    ((hmem i).mono_measure
      (Measure.restrict_mono (Metric.ball_subset_ball hrR.le) le_rfl)).integrable (by norm_num)
  have hgradr : ∀ i, HasWeakGradOn (Metric.ball c r) (F i) (fun k => F (nxt i k)) := fun i =>
    (hgrad i).mono (Metric.ball_subset_ball hrR.le)
  -- Morrey, applied to every member at once.
  obtain ⟨C, hC⟩ := morrey_ball hd hp c hr
  choose v hvae hvhol using fun i =>
    hC (F i) (fun k => F (nxt i k)) (hFint i) (fun k => hladder (nxt i k)) (hgradr i)
  have hγ : 0 < morreyExponent d (2 * (d : ℝ)) :=
    Real.toNNReal_pos.mpr (sub_pos.mpr ((div_lt_one hp0).mpr hp))
  have hvc : ∀ i, ContinuousOn (v i) (Metric.ball c r) := fun i => (hvhol i).continuousOn hγ
  have hvint : ∀ i, IntegrableOn (v i) (Metric.ball c r) volume := fun i =>
    (hFint i).congr (hvae i).symm
  have hvgrad : ∀ i, HasWeakGradOn (Metric.ball c r) (v i) (fun k => v (nxt i k)) := fun i =>
    (hgradr i).congr_ae (hvae i).symm fun k => (hvae (nxt i k)).symm
  -- The classical derivative of a representative is the representative of the derivative.
  have hfd : ∀ (i : ι), ∀ y ∈ Metric.ball c r,
      HasFDerivAt (v i) (gradCLM (fun k => v (nxt i k)) y) y := fun i y hy =>
    hasFDerivAt_of_continuousOn_hasWeakGradOn measurableSet_ball Metric.isOpen_ball (hvint i)
      (fun k => hvint (nxt i k)) (hvc i) (fun k => hvc (nxt i k)) (hvgrad i) hy
  -- Every finite order, by induction, with no further shrinking.
  have hcn : ∀ (n : ℕ) (i : ι), ContDiffOn ℝ (n : ℕ) (v i) (Metric.ball c r) := by
    intro n
    induction n with
    | zero => exact fun i => by simpa using (hvc i)
    | succ n ih =>
      intro i
      rw [show ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 by push_cast; ring,
        contDiffOn_succ_iff_fderiv_of_isOpen Metric.isOpen_ball]
      refine ⟨fun y hy => ((hfd i y hy).differentiableAt).differentiableWithinAt, by simp, ?_⟩
      have hsum : ContDiffOn ℝ (n : ℕ) (fun y => gradCLM (fun k => v (nxt i k)) y)
          (Metric.ball c r) := by
        change ContDiffOn ℝ (n : ℕ)
          (fun y => ∑ k, v (nxt i k) y •
            (EuclideanSpace.proj k : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)) (Metric.ball c r)
        exact ContDiffOn.sum fun k _ => (ih (nxt i k)).smul contDiffOn_const
      exact hsum.congr fun y hy => (hfd i y hy).fderiv
  exact ⟨v, fun i => contDiffOn_infty.mpr fun n => hcn n i, hvae⟩

end EllipticPdes.Embedding
