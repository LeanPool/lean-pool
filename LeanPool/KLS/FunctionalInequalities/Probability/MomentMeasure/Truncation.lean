/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Probability.MomentMeasure.Integrability
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Truncation convergence and the convexified competitor

Dominated convergence for lower truncations, the lower-tail control of the truncation error, and the
epsilon
reduction of every admissible competitor to a convex lower semicontinuous admissible one
(`exists_convexified_lowerTruncate_variational_le_add`), with zero and infinite exponential mass
retained.

Supporting infrastructure for Cordero-Erausquin–Klartag, Proposition 12.
-/

@[expose] public section

noncomputable section

namespace FunctionalInequalities.Probability.MomentMeasure

open FunctionalInequalities.Analysis

section
-- Convergence of lower truncations.

open MeasureTheory
variable {E : Type*} [MeasurableSpace E] {μ : Measure E}
/-- Nonnegative cutoffs do not increase the norm of a real lower truncation. -/
theorem norm_max_neg_le (r M : ℝ) (hM : 0 ≤ M) : ‖max r (-M)‖ ≤ ‖r‖ := by
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  apply abs_le.mpr
  constructor
  · exact (neg_abs_le r).trans (le_max_left _ _)
  · exact max_le (le_abs_self r) ((neg_nonpos.mpr hM).trans (abs_nonneg r))
omit [MeasurableSpace E] in
/-- At a finite input point, the actual sequence of cutoffs eventually leaves
the input unchanged. This avoids any unproved EReal convergence assumption. -/
theorem tendsto_lowerTruncate_toReal (f : E → EReal) (x : E)
    (ht : f x ≠ ⊤) (hb : f x ≠ ⊥) :
    Filter.Tendsto (fun n : ℕ => (lowerTruncate f (n : ℝ) x).toReal)
      Filter.atTop (nhds ((f x).toReal)) := by
  obtain ⟨N, hN⟩ := exists_nat_ge (-(f x).toReal)
  have hev : ∀ᶠ n : ℕ in Filter.atTop,
      (lowerTruncate f (n : ℝ) x).toReal = (f x).toReal := by
    apply Filter.eventually_atTop.mpr
    refine ⟨N, ?_⟩
    intro n hn
    rw [lowerTruncate_toReal_of_finite f (n : ℝ) x ht hb, max_eq_left]
    have hcast : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  exact tendsto_const_nhds.congr' (Filter.EventuallyEq.symm hev)
/-- Dominated convergence for the actual lower truncations, with domination
by the norm of the original real restriction. -/
theorem tendsto_integral_lowerTruncate [IsFiniteMeasure μ]
    (f : E → EReal) (hf : PotentialIntegrable f μ) :
    Filter.Tendsto (fun n : ℕ => ∫ x, (lowerTruncate f (n : ℝ) x).toReal ∂μ)
      Filter.atTop (nhds (∫ x, (f x).toReal ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun x => ‖(f x).toReal‖)
  · intro n
    exact (lowerTruncate_potentialIntegrable f (n : ℝ) hf).2.2.aestronglyMeasurable
  · exact hf.2.2.norm
  · intro n
    filter_upwards [hf.2.1] with x hx
    rw [lowerTruncate_toReal_of_finite f (n : ℝ) x hx (hf.1 x)]
    exact norm_max_neg_le _ _ (Nat.cast_nonneg n)
  · filter_upwards [hf.2.1] with x hx
    exact tendsto_lowerTruncate_toReal f x hx (hf.1 x)
/-- The signed difference of the actual integrals tends to zero; it is the
source's truncation error rather than an assumed tail bound. -/
theorem tendsto_integral_lowerTruncate_error [IsFiniteMeasure μ]
    (f : E → EReal) (hf : PotentialIntegrable f μ) :
    Filter.Tendsto (fun n : ℕ =>
      (∫ x, (lowerTruncate f (n : ℝ) x).toReal ∂μ) - ∫ x, (f x).toReal ∂μ)
      Filter.atTop (nhds 0) := by
  have hconst : Filter.Tendsto (fun _ : ℕ => ∫ x, (f x).toReal ∂μ)
      Filter.atTop (nhds (∫ x, (f x).toReal ∂μ)) := tendsto_const_nhds
  simpa only [sub_self] using (tendsto_integral_lowerTruncate f hf).sub hconst
/-- The truncation integral error is nonnegative for every real cutoff. -/
theorem integral_le_integral_lowerTruncate [IsFiniteMeasure μ]
    (f : E → EReal) (M : ℝ) (hf : PotentialIntegrable f μ) :
    (∫ x, (f x).toReal ∂μ) ≤ ∫ x, (lowerTruncate f M x).toReal ∂μ := by
  have hg := lowerTruncate_potentialIntegrable f M hf
  apply integral_mono_ae hf.2.2 hg.2.2
  filter_upwards [hf.2.1] with x hx
  rw [lowerTruncate_toReal_of_finite f M x hx (hf.1 x)]
  exact le_max_left _ _
/-- The integral of the pointwise truncation error also tends to zero, with
the integral subtraction justified by the proved integrability on both sides. -/
theorem tendsto_integral_pointwise_lowerTruncate_error [IsFiniteMeasure μ]
    (f : E → EReal) (hf : PotentialIntegrable f μ) :
    Filter.Tendsto (fun n : ℕ =>
      ∫ x, (lowerTruncate f (n : ℝ) x).toReal - (f x).toReal ∂μ)
      Filter.atTop (nhds 0) := by
  have heq : (fun n : ℕ => ∫ x, (lowerTruncate f (n : ℝ) x).toReal - (f x).toReal ∂μ) =
      (fun n : ℕ => (∫ x, (lowerTruncate f (n : ℝ) x).toReal ∂μ) - ∫ x, (f x).toReal ∂μ) := by
    funext n
    exact integral_sub (lowerTruncate_potentialIntegrable f (n : ℝ) hf).2.2 hf.2.2
  rw [heq]
  exact tendsto_integral_lowerTruncate_error f hf

end

section
-- A tail bound for the lower-truncation error.

open MeasureTheory
/-- Pointwise truncation error is bounded by the actual lower-tail norm. -/
theorem max_neg_error_le_tail (r M : ℝ) (hM : 0 ≤ M) :
    0 ≤ max r (-M) - r ∧
      max r (-M) - r ≤ if r ≤ -M then ‖r‖ else 0 := by
  refine ⟨sub_nonneg.mpr (le_max_left _ _), ?_⟩
  by_cases h : r ≤ -M
  · rw [ite_eq_left h, max_eq_right h]
    have hn : -r ≤ ‖r‖ := by simpa only [Real.norm_eq_abs] using neg_le_abs r
    linarith
  · rw [ite_eq_right h, max_eq_left (le_of_not_ge h), sub_self]
variable {E : Type*} [MeasurableSpace E] {μ : Measure E}
/-- The exact lower-tail norm of the real restriction; a.e. finiteness ensures
this is the source lower-tail function on the measure's relevant points. -/
def lowerTailNorm (f : E → EReal) (n : ℕ) (x : E) : ℝ :=
  if (f x).toReal ≤ -(n : ℝ) then ‖(f x).toReal‖ else 0
/-- Integrability of the actual tail follows from the input's integrable norm. -/
theorem lowerTailNorm_integrable (f : E → EReal) (hf : PotentialIntegrable f μ) (n : ℕ) :
    Integrable (lowerTailNorm f n) μ := by
  have hm : Measurable (fun r : ℝ => if r ≤ -(n : ℝ) then ‖r‖ else 0) := by
    exact measurable_norm.piecewise measurableSet_Iic measurable_const
  have hae : AEStronglyMeasurable (lowerTailNorm f n) μ :=
    (hm.comp_aemeasurable hf.2.2.aestronglyMeasurable.aemeasurable).aestronglyMeasurable
  apply hf.2.2.norm.mono' hae
  exact
    Filter.Eventually.of_forall fun x => by
      unfold lowerTailNorm
      split_ifs <;> simp
/-- The actual tail integral tends to zero, by dominated convergence and the
Archimedean cutoff property, without an assumed tail estimate. -/
theorem tendsto_integral_lowerTailNorm (f : E → EReal) (hf : PotentialIntegrable f μ) :
    Filter.Tendsto (fun n => ∫ x, lowerTailNorm f n x ∂μ) Filter.atTop (nhds 0) := by
  have hlim : ∀ x, Filter.Tendsto (fun n => lowerTailNorm f n x) Filter.atTop (nhds 0) := by
    intro x
    obtain ⟨N, hN⟩ := exists_nat_ge (-(f x).toReal)
    have hev : ∀ᶠ n in Filter.atTop, lowerTailNorm f n x = 0 := by
      apply Filter.eventually_atTop.mpr
      refine ⟨N + 1, ?_⟩
      intro n hn
      have hcast : (N : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hn
      have hlt : -(n : ℝ) < (f x).toReal := by linarith
      exact ite_eq_right (not_le_of_gt hlt)
    exact tendsto_const_nhds.congr' (Filter.EventuallyEq.symm hev)
  have ht :=
    tendsto_integral_of_dominated_convergence (fun x => ‖(f x).toReal‖)
      (fun n => (lowerTailNorm_integrable f hf n).aestronglyMeasurable) hf.2.2.norm
      (fun n =>
        Filter.Eventually.of_forall fun x => by unfold lowerTailNorm; split_ifs <;> simp)
      (Filter.Eventually.of_forall hlim)
  simpa only [integral_zero] using ht
/-- The exact integral error in (61) is nonnegative and bounded by the actual
tail integral; all integral subtraction and monotonicity are justified. -/
theorem integral_lowerTruncate_error_le_tail [IsFiniteMeasure μ]
    (f : E → EReal) (hf : PotentialIntegrable f μ) (n : ℕ) :
    0 ≤ (∫ x, (lowerTruncate f (n : ℝ) x).toReal ∂μ) - ∫ x, (f x).toReal ∂μ ∧
      (∫ x, (lowerTruncate f (n : ℝ) x).toReal ∂μ) - ∫ x, (f x).toReal ∂μ ≤
        ∫ x, lowerTailNorm f n x ∂μ := by
  have hg := lowerTruncate_potentialIntegrable f (n : ℝ) hf
  refine ⟨sub_nonneg.mpr (integral_le_integral_lowerTruncate f (n : ℝ) hf), ?_⟩
  rw [← integral_sub hg.2.2 hf.2.2]
  apply integral_mono_ae (hg.2.2.sub hf.2.2) (lowerTailNorm_integrable f hf n)
  filter_upwards [hf.2.1] with x hx
  change (lowerTruncate f (n : ℝ) x).toReal - (f x).toReal ≤ lowerTailNorm f n x
  rw [lowerTruncate_toReal_of_finite f (n : ℝ) x hx (hf.1 x)]
  exact (max_neg_error_le_tail (f x).toReal (n : ℝ) (Nat.cast_nonneg n)).2

end

section
-- Convexified lower truncations as variational competitors.

open MeasureTheory
/-- The finite integral error controls subtraction from any extended logarithm,
including `±∞`; no positive finite exponential-mass assumption is required. -/
theorem sub_coe_le_sub_coe_add (z : EReal) (A C ε : ℝ) (h : C - A ≤ ε) :
    z - (A : EReal) ≤ (z - (C : EReal)) + (ε : EReal) := by
  induction z with
  | bot => simp
  | top => simp
  | coe z =>
    exact_mod_cast (show z - A ≤ z - C + ε by linarith)
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E}
/-- Every actual admissible competitor has a convex lsc admissible competitor,
obtained by the actual biconjugate of a positive integer lower truncation, whose
variational value loses at most epsilon. The cutoff is selected from dominated
convergence, and the statement retains extended zero/infinite exponential mass. -/
theorem exists_convexified_lowerTruncate_variational_le_add [IsFiniteMeasure μ]
    (dx : Measure E) (f : E → EReal) (hμ : μ ≠ 0) (hf : PotentialIntegrable f μ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℕ, 0 < n ∧
      let c := legendre (legendre (lowerTruncate f (n : ℝ)))
      ConvexPotential c ∧ LowerSemicontinuous c ∧ PotentialIntegrable c μ ∧
        variationalFunctional dx μ f ≤ variationalFunctional dx μ c + (ε : EReal) := by
  have hev := (tendsto_integral_lowerTruncate_error f hf).eventually (Iio_mem_nhds hε)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
  let n := N + 1
  let g := lowerTruncate f (n : ℝ)
  let c := legendre (legendre g)
  have herr : (∫ x, (g x).toReal ∂μ) - ∫ x, (f x).toReal ∂μ < ε :=
    hN n (Nat.le_succ N)
  have hfinite := potentialIntegrable_exists_finite f hμ hf
  obtain ⟨hc, hls, _, _, hdual⟩ := lowerTruncate_convexification f (n : ℝ) hfinite
  have hcint := biconjugate_lowerTruncate_potentialIntegrable f (n : ℝ) hμ hf
  have hcle := integral_biconjugate_lowerTruncate_le f (n : ℝ) hμ hf
  have hdualFun : legendre c = legendre g := funext hdual
  have hmass : mass dx (legendre c) = mass dx (legendre g) := congrArg (mass dx) hdualFun
  have hmono : ENNReal.log (mass dx (legendre f)) ≤ ENNReal.log (mass dx (legendre g)) :=
    ENNReal.log_le_log (mass_legendre_mono dx (fun x => le_max_left _ _))
  refine ⟨n, Nat.succ_pos N, hc, hls, hcint, ?_⟩
  change ENNReal.log (mass dx (legendre f)) - (∫ x, (f x).toReal ∂μ : ℝ) ≤
    (ENNReal.log (mass dx (legendre c)) - (∫ x, (c x).toReal ∂μ : ℝ)) + (ε : EReal)
  rw [hmass]
  exact (EReal.sub_le_sub hmono le_rfl).trans
    (sub_coe_le_sub_coe_add _ _ _ ε (by linarith [hcle]))

end

end FunctionalInequalities.Probability.MomentMeasure
