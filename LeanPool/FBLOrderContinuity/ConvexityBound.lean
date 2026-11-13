/-
Copyright (c) 2026 Raúl E. Pariente-Martín, Pedro Tradacete. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raúl E. Pariente-Martín, Pedro Tradacete
-/

module

public import LeanPool.FBLOrderContinuity.EuclideanFamilies
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics



/-!
# The exponent obstruction from Euclidean dual families

For an infinite-dimensional space and finite p ≥ 2, `dual_euclidean_family` gives
a lower bound of order n^(1/p) for suitable lattice q-sums of generators. A
q-convexity constant C gives the upper bound 4 C n^(1/q). Growth as n tends to
infinity rules out q > p, including q = infinity, where the reciprocal exponent is
interpreted as zero.

`parameter_bound_ge_two` is the resulting obstruction. `Parameters.lean` extends
it to arbitrary finite p by passing through the intermediate exponent max(2,p).
-/

@[expose] public section

noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open Filter Set

namespace FBLOrderContinuousLH
namespace ConvexityBound

/-- For a nonempty family of n ones, the scalar p-sum is `n^(p.toReal⁻¹)`.
At ∞, `ENNReal.toReal ∞ = 0` makes the exponent zero and the value is one. -/
private theorem scalarPSum_ones (p : Exponent) {n : ℕ} (hn : 0 < n) :
    scalarPSum p (fun _ : Fin n => (1 : ℝ)) = (n : ℝ) ^ p.1.toReal⁻¹ := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  by_cases ht : p.1 = ⊤
  · simp only [scalarPSum, ht, ↓reduceIte, abs_one, ENNReal.toReal_top, inv_zero, Real.rpow_zero]
    change ((Finset.univ.sup (fun _ : Fin n => (1 : ℝ≥0)) : ℝ≥0) : ℝ) = 1
    rw [Finset.sup_const Finset.univ_nonempty]
    rfl
  · simp [scalarPSum, ht, one_div]

/-- A q-convexity constant C for `Free p E` on an infinite-dimensional space,
with p ≥ 2, forces `n^(1/p) ≤ 4 C n^(1/q)` for every positive integer n. Evaluate
lattice q-sums of unit-ball generators on the Euclidean dual family for the lower
bound and use q-convexity for the upper bound. -/
private theorem convexity_growth_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hE : ¬ FiniteDimensional ℝ E) (p q : Exponent) (h2p : Exponent.two ≤ p)
    {C : ℝ} (hC : ConvexWith q C (Free p E)) (n : ℕ) (hn : 0 < n) :
    (n : ℝ) ^ p.1.toReal⁻¹ ≤ 4 * C * (n : ℝ) ^ q.1.toReal⁻¹ := by
  obtain ⟨φ, hφ, hnormφ⟩ := EuclideanFamilies.dual_euclidean_family hE n
  have hφp : NormAdmissible p φ := fun x hx =>
    (scalarPSum_mono_exponent h2p _).trans (hφ x hx)
  choose x hx hxφ using fun i => (φ i).exists_lt_apply_of_lt_opNorm (hnormφ i)
  let f : Free p E := latticePSum q (fun i => delta p (x i))
  have hf (i : Fin n) : (1 / 4 : ℝ) ≤ |f (φ i)| := by
    have hcoord : |φ i (x i)| ≤ scalarPSum q (fun j => φ i (x j)) := by
      rw [scalarPSum_eq_piLp_norm]
      exact PiLp.norm_apply_le (WithLp.toLp q.1 (fun j => φ i (x j))) i
    have heq : f (φ i) = scalarPSum q (fun j => φ i (x j)) := by
      rw [show f = latticePSum q (fun j => delta p (x j)) from rfl, latticePSum_apply]
      simp only [(model_evaluation p (x _) (0 : FVL E) (φ i)).1]
    rw [heq, abs_of_nonneg (scalarPSum_nonneg _ _)]
    exact (show (1 / 4 : ℝ) < |φ i (x i)| by
      simpa only [Real.norm_eq_abs] using hxφ i).le.trans hcoord
  have hconst : scalarPSum p (fun _ : Fin n => (1 / 4 : ℝ)) =
      (1 / 4 : ℝ) * (n : ℝ) ^ p.1.toReal⁻¹ := by
    simpa only [mul_one, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4), scalarPSum_ones p hn] using
      scalarPSum_smul p (1 / 4 : ℝ) (fun _ : Fin n => (1 : ℝ))
  have hlower : (1 / 4 : ℝ) * (n : ℝ) ^ p.1.toReal⁻¹ ≤ ‖f‖ := by
    rw [← hconst]
    exact (scalarPSum_mono_abs p _ _ (fun i => by
      simpa only [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)] using hf i)).trans
      (freeNorm_family_le p f φ hφp)
  have hscalar : scalarPSum q (fun i => ‖delta p (x i)‖) ≤
      scalarPSum q (fun _ : Fin n => (1 : ℝ)) := by
    apply scalarPSum_mono_abs
    intro i
    simpa only [abs_norm, abs_one, LinearIsometry.norm_map] using (hx i).le
  have hupper : ‖f‖ ≤ C * (n : ℝ) ^ q.1.toReal⁻¹ := by
    rw [← scalarPSum_ones q hn]
    exact (hC.2 n (fun i => delta p (x i))).trans
      (mul_le_mul_of_nonneg_left hscalar (zero_le_one.trans hC.1))
  linarith

/-- For an infinite-dimensional real normed space and finite p ≥ 2, q-convexity
of `Free p E` implies q ≤ p. If q were larger, `convexity_growth_bound` would bound
a positive power of n uniformly as n tends to infinity. The argument also excludes
the target exponent ∞ and requires no completeness assumption on E. -/
theorem parameter_bound_ge_two {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hE : ¬ FiniteDimensional ℝ E) (p q : Exponent) (hp : p.IsFinite)
    (h2p : Exponent.two ≤ p) (h : IsPConvex q (Free p E)) : q ≤ p := by
  by_contra! hpq
  obtain ⟨C, hC⟩ := h
  have hp0 : 0 < p.1.toReal :=
    ENNReal.toReal_pos_iff.mpr ⟨lt_of_lt_of_le zero_lt_one p.2, hp⟩
  have hinv : q.1.toReal⁻¹ < p.1.toReal⁻¹ := by
    by_cases hq : q.1 = ⊤
    · simpa only [hq, ENNReal.toReal_top, inv_zero] using inv_pos.mpr hp0
    · have hq0 : 0 < q.1.toReal :=
        ENNReal.toReal_pos_iff.mpr ⟨lt_of_lt_of_le zero_lt_one q.2, lt_top_iff_ne_top.mpr hq⟩
      exact (inv_lt_inv₀ hq0 hp0).mpr ((ENNReal.toReal_lt_toReal hp.ne hq).mpr hpq)
  have ht : Tendsto (fun n : ℕ => (n : ℝ) ^ (p.1.toReal⁻¹ - q.1.toReal⁻¹)) atTop atTop :=
    (tendsto_rpow_atTop (sub_pos.mpr hinv)).comp tendsto_natCast_atTop_atTop
  have hbound (n : ℕ) (hn : 0 < n) :
      (n : ℝ) ^ (p.1.toReal⁻¹ - q.1.toReal⁻¹) ≤ 4 * C := by
    have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
    rw [Real.rpow_sub hn']
    exact (div_le_iff₀ (Real.rpow_pos_of_pos hn' _)).mpr
      (convexity_growth_bound hE p q h2p hC n hn)
  obtain ⟨n, hn, hnC⟩ :=
    ((eventually_gt_atTop (0 : ℕ)).and (ht.eventually (eventually_gt_atTop (4 * C)))).exists
  exact (not_le_of_gt hnC) (hbound n hn)

end ConvexityBound
end FBLOrderContinuousLH
