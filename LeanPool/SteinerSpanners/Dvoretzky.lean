/-
Copyright (c) 2026 Goran Zuzic et al. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Goran Zuzic, David P. Woodruff, Vahab Mirrokni
-/

module

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Convert
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps

import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Probability.Distributions.Gaussian.Fernique
public import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.Normed.Lp.PiLp

public import LeanPool.SteinerSpanners.Defs

/-! # Dvoretzky infrastructure for Steiner spanners

Ported from the upstream formalization to Lean Pool’s pinned Lean and Mathlib. -/

@[expose] public section

open scoped ENNReal
open HighDimSteinerSpanners

namespace HighDimSteinerSpanners.Proofs.Dvoretzky

section Helpers

open scoped NNReal Real
open MeasureTheory ProbabilityTheory

noncomputable section

/-! ### Section 1: `lpDist` properties and geometric-to-Steiner spanner embedding -/

private lemma lpDist_nonneg {p : ℝ} {d : ℕ} (x y : Fin d → ℝ) :
    0 ≤ lpDist p x y := by
  unfold lpDist
  positivity

private lemma lpDist_eq_norm_sub
    (h_lp : ∀ (p : ℝ), 1 ≤ p →
      ∀ {d : ℕ} (x y : Fin d → ℝ),
        lpDist p x y =
          dist (WithLp.toLp (ENNReal.ofReal p) x) (WithLp.toLp (ENNReal.ofReal p) y))
    {p : ℝ} (hp : 1 ≤ p) {d : ℕ} (x y : Fin d → ℝ) :
    lpDist p x y = ‖WithLp.toLp (ENNReal.ofReal p) (x - y)‖ := by
  have : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp⟩
  rw [h_lp p hp x y, dist_eq_norm]
  rfl

private lemma lpDist_zero_eq_norm
    (h_lp : ∀ (p : ℝ), 1 ≤ p →
      ∀ {d : ℕ} (x y : Fin d → ℝ),
        lpDist p x y =
          dist (WithLp.toLp (ENNReal.ofReal p) x) (WithLp.toLp (ENNReal.ofReal p) y))
    {p : ℝ} (hp : 1 ≤ p) {d : ℕ} (x : Fin d → ℝ) :
    lpDist p x 0 = ‖WithLp.toLp (ENNReal.ofReal p) x‖ := by
  simpa using lpDist_eq_norm_sub h_lp hp x 0

private lemma lpDist_two_zero_eq_eucl_norm
    (h_lp : ∀ (p : ℝ), 1 ≤ p →
      ∀ {d : ℕ} (x y : Fin d → ℝ),
        lpDist p x y =
          dist (WithLp.toLp (ENNReal.ofReal p) x) (WithLp.toLp (ENNReal.ofReal p) y))
    {d : ℕ} (x : Fin d → ℝ) :
    lpDist 2 x 0 = ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin d))‖ := by
  rw [lpDist_zero_eq_norm h_lp (by norm_num : (1 : ℝ) ≤ 2) x]
  have h2 : ENNReal.ofReal (2 : ℝ) = 2 := by norm_num
  congr!

private lemma geometric_spanner_to_steiner
    (h_lp : ∀ (p : ℝ), 1 ≤ p →
      ∀ {d : ℕ} (x y : Fin d → ℝ),
        lpDist p x y =
          dist (WithLp.toLp (ENNReal.ofReal p) x) (WithLp.toLp (ENNReal.ofReal p) y))
    {p : ℝ} (hp : 1 ≤ p) {n d : ℕ} (P : Fin n → (Fin d → ℝ)) (C : ℝ)
    (G : SimpleGraph (Fin n)) (hGeom : IsGeometricSpanner p P C G) :
    ∃ (H : SimpleGraph (Fin n ⊕ PEmpty)) (w : Sym2 (Fin n ⊕ PEmpty) → ℝ),
      IsNonMetricSteinerSpanner p P C H w ∧
      (Nat.card H.edgeSet : ℝ) ≤ (Nat.card G.edgeSet : ℝ) := by
  have : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp⟩
  let proj : Fin n ⊕ PEmpty → Fin n := Sum.elim id PEmpty.elim
  let wG : Sym2 (Fin n) → ℝ :=
    Sym2.lift ⟨fun u v => lpDist p (P u) (P v), fun u v => by
      simp only [lpDist, abs_sub_comm]⟩
  let H : SimpleGraph (Fin n ⊕ PEmpty) :=
    { Adj := fun x y => G.Adj (proj x) (proj y)
      symm := ⟨fun _ _ h => G.adj_symm h⟩
      loopless := ⟨fun _ h => G.irrefl h⟩ }
  let w : Sym2 (Fin n ⊕ PEmpty) → ℝ := fun e => wG (Sym2.map proj e)
  refine ⟨H, w, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro e _
      revert e
      refine Sym2.ind (fun x y _ => ?_)
      simpa [w, wG] using lpDist_nonneg (P (proj x)) (P (proj y))
    · intro i j
      have hwalk_lb : ∀ {u v : Fin n ⊕ PEmpty} (q : H.Walk u v),
          lpDist p (P (proj u)) (P (proj v)) ≤ walkWeight w q := by
        intro u v q
        induction q with
        | @nil u =>
          simp [walkWeight, h_lp p hp]
        | @cons u b v _ q' ih =>
          have htri : lpDist p (P (proj u)) (P (proj v)) ≤
              lpDist p (P (proj u)) (P (proj b)) + lpDist p (P (proj b)) (P (proj v)) := by
            simp only [h_lp p hp]
            exact dist_triangle _ _ _
          have hw_eq : w s(u, b) = lpDist p (P (proj u)) (P (proj b)) := by
            simp [w, wG]
          simp only [walkWeight, hw_eq]
          linarith
      exact le_iInf (fun q => ENNReal.ofReal_le_ofReal (hwalk_lb q))
    · intro i j
      let emb : G →g H := ⟨Sum.inl, fun h => h⟩
      have hww_map : ∀ {u v : Fin n} (q : G.Walk u v),
          walkWeight w (q.map emb) = walkWeight wG q := by
        intro u v q
        induction q with
        | nil => simp [walkWeight]
        | @cons u b v _ q' ih =>
          simp only [SimpleGraph.Walk.map_cons, walkWeight, ih]
          rfl
      have hle_gd : graphDist H w (.inl i) (.inl j) ≤ graphDist G wG i j := by
        unfold graphDist
        refine le_iInf (fun q => ?_)
        calc
          (⨅ p_w : H.Walk (.inl i) (.inl j), ENNReal.ofReal (walkWeight w p_w))
            ≤ ENNReal.ofReal (walkWeight w (q.map emb)) := iInf_le _ (q.map emb)
          _ = ENNReal.ofReal (walkWeight wG q) := by rw [hww_map]
      exact le_trans hle_gd (hGeom i j)
  · have hproj_inj : Function.Injective proj := by
      rintro (u | s) (v | s) h
      · exact congrArg Sum.inl h
      · exact PEmpty.elim s
      · exact PEmpty.elim s
      · exact PEmpty.elim s
    let f_edge : H.edgeSet → G.edgeSet := fun e =>
      ⟨Sym2.map proj e.1, by
        rcases e with ⟨s, hs⟩
        revert hs
        refine Sym2.ind (fun x y hs => ?_) s
        simpa [SimpleGraph.mem_edgeSet] using hs⟩
    have hf_inj : Function.Injective f_edge := by
      intro e₁ e₂ heq
      apply Subtype.ext
      exact Sym2.map.injective hproj_inj (Subtype.mk.inj heq)
    have hnat : Nat.card H.edgeSet ≤ Nat.card G.edgeSet :=
      Nat.card_le_card_of_injective f_edge hf_inj
    exact_mod_cast hnat

/-! ### Section 2: Volumetric `(1 / 10)`-net on `S^{d₂ - 1}` -/

private lemma sep_finset_card_le (d₂ : ℕ) (S : Finset (EuclideanSpace ℝ (Fin d₂)))
    (hS_norm : ∀ u ∈ S, ‖u‖ = 1)
    (hS_sep : ∀ u ∈ S, ∀ v ∈ S, u ≠ v → (1 : ℝ) / 10 ≤ ‖u - v‖) :
    S.card ≤ 21 ^ d₂ := by
  let μ : Measure (EuclideanSpace ℝ (Fin d₂)) := volume
  have hdisj : (S : Set (EuclideanSpace ℝ (Fin d₂))).PairwiseDisjoint
      (fun u => Metric.ball u (1 / 20 : ℝ)) := by
    intro u hu v hv huv
    rw [Function.onFun, Set.disjoint_left]
    intro x hxu hxv
    rw [Metric.mem_ball] at hxu hxv
    have hsep := hS_sep u hu v hv huv
    rw [← dist_eq_norm] at hsep
    have htri := dist_triangle_left u v x
    linarith
  have hsub : (⋃ u ∈ S, Metric.ball u (1 / 20 : ℝ)) ⊆
      Metric.ball (0 : EuclideanSpace ℝ (Fin d₂)) (21 / 20 : ℝ) := by
    intro x hx
    simp only [Set.mem_iUnion, Metric.mem_ball, dist_zero_right] at hx ⊢
    obtain ⟨u, huS, hxu⟩ := hx
    rw [dist_eq_norm] at hxu
    have hu1 := hS_norm u huS
    calc ‖x‖ = ‖(x - u) + u‖ := by abel_nf
      _ ≤ ‖x - u‖ + ‖u‖ := norm_add_le _ _
      _ < 1 / 20 + 1 := by linarith
      _ = 21 / 20 := by norm_num
  have hmeas_union : (∑ u ∈ S, μ (Metric.ball u (1 / 20 : ℝ))) ≤
      μ (Metric.ball (0 : EuclideanSpace ℝ (Fin d₂)) (21 / 20 : ℝ)) := by
    rw [← measure_biUnion_finset hdisj (fun _ _ => measurableSet_ball)]
    exact measure_mono hsub
  have hr1 : (0 : ℝ) < 1 / 20 := by norm_num
  have hr2 : (0 : ℝ) < 21 / 20 := by norm_num
  simp only [μ.addHaar_ball_of_pos _ hr1, μ.addHaar_ball_of_pos _ hr2,
    finrank_euclideanSpace_fin, Finset.sum_const, nsmul_eq_mul, ← mul_assoc] at hmeas_union
  have hball_ne_zero : μ (Metric.ball 0 1) ≠ 0 :=
    Measure.IsOpenPosMeasure.open_pos _ Metric.isOpen_ball (Metric.nonempty_ball.mpr zero_lt_one)
  have hball_lt_top : μ (Metric.ball 0 1) < ⊤ := measure_ball_lt_top
  have hle_enn : (S.card : ℝ≥0∞) * ENNReal.ofReal ((1 / 20 : ℝ) ^ d₂) ≤
      ENNReal.ofReal ((21 / 20 : ℝ) ^ d₂) :=
    (ENNReal.mul_le_mul_iff_left hball_ne_zero hball_lt_top.ne).mp hmeas_union
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)] at hle_enn
  have hle_real : (S.card : ℝ) * (1 / 20 : ℝ) ^ d₂ ≤ (21 / 20 : ℝ) ^ d₂ :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hle_enn
  have hcard_real : (S.card : ℝ) ≤ (21 : ℝ) ^ d₂ := by
    have h20 : (0 : ℝ) < (20 : ℝ) ^ d₂ := by positivity
    have h1 : (S.card : ℝ) * (1 / 20 : ℝ) ^ d₂ * (20 : ℝ) ^ d₂ ≤
        (21 / 20 : ℝ) ^ d₂ * (20 : ℝ) ^ d₂ :=
      mul_le_mul_of_nonneg_right hle_real h20.le
    rw [mul_assoc, ← mul_pow, ← mul_pow] at h1
    norm_num at h1
    exact h1
  exact_mod_cast hcard_real

private lemma sphere_tenth_net (d₂ : ℕ) :
    ∃ N_net : Finset (EuclideanSpace ℝ (Fin d₂)),
      N_net.card ≤ 21 ^ d₂ ∧
      (∀ u ∈ N_net, ‖u‖ = 1) ∧
      (∀ v : EuclideanSpace ℝ (Fin d₂), ‖v‖ = 1 → ∃ u ∈ N_net, ‖v - u‖ ≤ 1 / 10) := by
  have step : ∀ (m : ℕ) (S : Finset (EuclideanSpace ℝ (Fin d₂))),
      21 ^ d₂ - S.card ≤ m →
      (∀ u ∈ S, ‖u‖ = 1) →
      (∀ u ∈ S, ∀ v ∈ S, u ≠ v → (1 : ℝ) / 10 ≤ ‖u - v‖) →
      ∃ N_net : Finset (EuclideanSpace ℝ (Fin d₂)),
        N_net.card ≤ 21 ^ d₂ ∧
        (∀ u ∈ N_net, ‖u‖ = 1) ∧
        (∀ v : EuclideanSpace ℝ (Fin d₂), ‖v‖ = 1 → ∃ u ∈ N_net, ‖v - u‖ ≤ 1 / 10) := by
    intro m
    induction m using Nat.strong_induction_on
    rename_i m ih
    intro S hm hS_norm hS_sep
    have hS_card := sep_finset_card_le d₂ S hS_norm hS_sep
    by_cases hcov : ∀ v : EuclideanSpace ℝ (Fin d₂), ‖v‖ = 1 → ∃ u ∈ S, ‖v - u‖ ≤ 1 / 10
    · exact ⟨S, hS_card, hS_norm, hcov⟩
    · push Not at hcov
      obtain ⟨v, hv_norm, hv_far⟩ := hcov
      have hv_not_mem : v ∉ S := by
        intro hvS
        have := hv_far v hvS
        simp at this
        linarith
      let S' := insert v S
      have hS'_norm : ∀ u ∈ S', ‖u‖ = 1 := by
        intro u hu
        rcases Finset.mem_insert.mp hu with rfl | huS
        · exact hv_norm
        · exact hS_norm u huS
      have hS'_sep : ∀ a ∈ S', ∀ b ∈ S', a ≠ b → (1 : ℝ) / 10 ≤ ‖a - b‖ := by
        intro a ha b hb hab
        rcases Finset.mem_insert.mp ha with rfl | haS <;>
          rcases Finset.mem_insert.mp hb with rfl | hbS
        · exact absurd rfl hab
        · exact (hv_far b hbS).le
        · rw [norm_sub_rev]; exact (hv_far a haS).le
        · exact hS_sep a haS b hbS hab
      have hS'_card_le := sep_finset_card_le d₂ S' hS'_norm hS'_sep
      have hS'_card_eq : S'.card = S.card + 1 := Finset.card_insert_of_notMem hv_not_mem
      exact ih (21 ^ d₂ - S'.card) (by omega) S' le_rfl hS'_norm hS'_sep
  exact step (21 ^ d₂) ∅ (by simp) (by simp) (by simp)

/-! ### Section 3: Standard Gaussian on `EuclideanSpace ℝ (Fin d)` -/

private lemma pi_gaussianReal_map_sum_mul {ι : Type*} [Fintype ι] (a : ι → ℝ) :
    (Measure.pi (fun _ : ι => gaussianReal 0 1)).map (fun x : ι → ℝ => ∑ i : ι, a i * x i) =
      gaussianReal 0 (NNReal.mk (∑ i : ι, (a i) ^ 2) (Finset.sum_nonneg (fun _ _ => sq_nonneg
          _))) := by
  let γ_ι : Measure (ι → ℝ) := Measure.pi (fun _ : ι => gaussianReal 0 1)
  have : IsProbabilityMeasure γ_ι := inferInstance
  have hmeas : Measurable (fun x : ι → ℝ => ∑ i : ι, a i * x i) := by fun_prop
  have : IsProbabilityMeasure (γ_ι.map (fun x : ι → ℝ => ∑ i : ι, a i * x i)) :=
    inferInstance
  refine Measure.ext_of_charFun ?_
  ext t
  rw [charFun_apply_real, integral_map hmeas.aemeasurable (by fun_prop), charFun_gaussianReal]
  simp only [Complex.ofReal_zero, mul_zero, zero_mul, zero_sub, NNReal.coe_mk]
  have h_integrand : ∀ x : ι → ℝ,
      Complex.exp (↑t * ↑(∑ i : ι, a i * x i) * Complex.I) =
      ∏ i : ι, Complex.exp (↑(t * a i) * ↑(x i) * Complex.I) := by
    intro x
    rw [← Complex.exp_sum]
    congr 1
    push_cast
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  simp_rw [h_integrand]
  rw [integral_fintype_prod_eq_prod (f := fun i (y : ℝ) => Complex.exp (↑(t * a i) * ↑y *
      Complex.I))]
  have h_each : ∀ i : ι,
      (∫ y : ℝ, Complex.exp (↑(t * a i) * ↑y * Complex.I) ∂gaussianReal 0 1) =
      Complex.exp (- ((a i) ^ 2 * t ^ 2 / 2 : ℝ)) := by
    intro i
    have hcf := charFun_gaussianReal (μ := 0) (v := 1) (t * a i)
    rw [charFun_apply_real] at hcf
    simpa [mul_pow, mul_comm] using hcf
  simp_rw [h_each, ← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.sum_neg_distrib, ← Finset.sum_div, ← Finset.sum_mul]

private def stdGaussian (d : ℕ) : Measure (EuclideanSpace ℝ (Fin d)) :=
  (Measure.pi (fun _ : Fin d => gaussianReal 0 1)).map
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm

private lemma stdGaussian_map_dual (d : ℕ) (L : StrongDual ℝ (EuclideanSpace ℝ (Fin d))) :
    (stdGaussian d).map L =
      gaussianReal 0 (NNReal.mk (∑ k : Fin d, (L (EuclideanSpace.single k 1)) ^ 2)
        (Finset.sum_nonneg (fun _ _ => sq_nonneg _))) := by
  let e := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm
  unfold stdGaussian
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  have hfun : (L ∘ e : (Fin d → ℝ) → ℝ) =
      fun x => ∑ k : Fin d, L (EuclideanSpace.single k 1) * x k := by
    ext x
    simp only [Function.comp_apply]
    have hx : e x = ∑ k : Fin d, x k • EuclideanSpace.single k (1 : ℝ) := by
      ext k
      simp [e, Pi.single_apply]
    rw [hx, map_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [map_smul, smul_eq_mul, mul_comm]
  rw [hfun]
  exact pi_gaussianReal_map_sum_mul _

private instance instIsGaussianStdGaussian (d : ℕ) : IsGaussian (stdGaussian d) :=
  isGaussian_of_map_eq_gaussianReal (fun L => ⟨0, _, stdGaussian_map_dual d L⟩)

private lemma stdGaussian_dual_var_le (d : ℕ) (L : StrongDual ℝ (EuclideanSpace ℝ (Fin d))) :
    ∑ k : Fin d, (L (EuclideanSpace.single k 1)) ^ 2 ≤ ‖L‖ ^ 2 := by
  let w : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 (fun k => L (EuclideanSpace.single k 1))
  have hw_sq : ‖w‖ ^ 2 = ∑ k : Fin d, (L (EuclideanSpace.single k 1)) ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    simp [w]
  have hLw : L w = ‖w‖ ^ 2 := by
    have hw_sum : w = ∑ k : Fin d, L (EuclideanSpace.single k 1) • EuclideanSpace.single k (1 :
        ℝ) := by
      ext k
      simp [w, Pi.single_apply]
    conv_lhs => rw [hw_sum]
    rw [map_sum]
    simp only [map_smul, smul_eq_mul, ← sq, hw_sq]
  have hbound : ‖w‖ ^ 2 ≤ ‖L‖ * ‖w‖ := by
    calc ‖w‖ ^ 2 = L w := hLw.symm
      _ ≤ ‖L w‖ := le_abs_self _
      _ ≤ ‖L‖ * ‖w‖ := L.le_opNorm w
  by_cases hw0 : ‖w‖ = 0
  · rw [← hw_sq, hw0, zero_pow two_ne_zero]; positivity
  · have hw_pos : 0 < ‖w‖ := lt_of_le_of_ne (norm_nonneg w) (Ne.symm hw0)
    have hle : ‖w‖ ≤ ‖L‖ := le_of_mul_le_mul_right (by simpa [sq] using hbound) hw_pos
    rw [← hw_sq]
    exact pow_le_pow_left₀ (norm_nonneg w) hle 2

private lemma stdGaussian_integral_dual_zero (d : ℕ) (L : StrongDual ℝ (EuclideanSpace ℝ (Fin d))) :
    ∫ x, L x ∂(stdGaussian d) = 0 := by
  have h := integral_map (μ := stdGaussian d) (φ := L) (f := fun y : ℝ => y)
    (by fun_prop) (by fun_prop)
  rw [stdGaussian_map_dual, integral_id_gaussianReal] at h
  exact h.symm

private def matMeasure (d d₂ : ℕ) : Measure (Fin d → Fin d₂ → ℝ) :=
  Measure.pi (fun _ : Fin d => Measure.pi (fun _ : Fin d₂ => gaussianReal 0 1))

private instance instIsProbMatMeasure (d d₂ : ℕ) : IsProbabilityMeasure (matMeasure d d₂) := by
  unfold matMeasure
  infer_instance

private lemma matMeasure_map_eval_unit {d d₂ : ℕ} (u : EuclideanSpace ℝ (Fin d₂)) (hu : ‖u‖ = 1) :
    (matMeasure d d₂).map
      (fun M : Fin d → Fin d₂ → ℝ =>
        (WithLp.toLp 2 (fun k => ∑ j : Fin d₂, u.ofLp j * M k j) : EuclideanSpace ℝ (Fin d))) =
      stdGaussian d := by
  let g : (Fin d₂ → ℝ) → ℝ := fun row => ∑ j : Fin d₂, u.ofLp j * row j
  have hg_meas : Measurable g := by fun_prop
  have hfun : (fun M : Fin d → Fin d₂ → ℝ =>
      (WithLp.toLp 2 (fun k => ∑ j : Fin d₂, u.ofLp j * M k j) : EuclideanSpace ℝ (Fin d))) =
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm ∘ (fun M k => g (M k)) := rfl
  rw [hfun, ← Measure.map_map (by fun_prop) (by fun_prop)]
  unfold matMeasure stdGaussian
  congr 1
  rw [Measure.pi_map_pi (fun _ => hg_meas.aemeasurable)]
  refine congrArg Measure.pi (funext fun k => ?_)
  rw [pi_gaussianReal_map_sum_mul]
  apply congrArg (gaussianReal 0)
  apply Subtype.ext
  have hu_sq : ∑ j : Fin d₂, (u.ofLp j) ^ 2 = 1 := by
    have h1 := PiLp.norm_sq_eq_of_L2 (β := fun _ : Fin d₂ => ℝ) u
    simp only [Real.norm_eq_abs, sq_abs] at h1
    rw [← h1, hu, one_pow]
  exact hu_sq

private lemma integral_abs_gaussianReal_ge :
    (1 : ℝ) / 48 ≤ ∫ x : ℝ, |x| ∂(gaussianReal 0 1) := by
  have hint : Integrable (fun x : ℝ => |x|) (gaussianReal 0 1) :=
    ((memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable le_rfl).norm
  have h1 : ∫ x in Set.Icc (1 : ℝ) 2, |x| ∂(gaussianReal 0 1) ≤ ∫ x : ℝ, |x| ∂(gaussianReal 0 1) :=
    setIntegral_le_integral hint (ae_of_all _ (fun x => abs_nonneg x))
  have h2 : ∫ x in Set.Icc (1 : ℝ) 2, |x| ∂(gaussianReal 0 1) =
      ∫ x in Set.Icc (1 : ℝ) 2, gaussianPDFReal 0 1 x * |x| := by
    rw [← integral_indicator measurableSet_Icc,
      integral_gaussianReal_eq_integral_smul one_ne_zero,
      ← integral_indicator measurableSet_Icc]
    congr with x
    by_cases hx : x ∈ Set.Icc (1 : ℝ) 2 <;> simp [hx, smul_eq_mul]
  have hexp_m2 : (1 : ℝ) / 16 ≤ Real.exp (-2) := by
    have hhalf : (1 : ℝ) / 2 ≤ Real.exp (-1 / 2) := by
      have := Real.add_one_le_exp (-1 / 2)
      linarith
    have hpow : ((1 : ℝ) / 2) ^ 4 ≤ (Real.exp (-1 / 2)) ^ 4 :=
      pow_le_pow_left₀ (by norm_num) hhalf 4
    rw [← Real.exp_nat_mul] at hpow
    norm_num at hpow
    exact hpow
  have hsqrt_le : √(2 * π * (1 : ℝ)) ≤ 3 := by
    have hpi : 2 * π * (1 : ℝ) ≤ 9 := by
      have := Real.pi_lt_four
      linarith
    calc √(2 * π * (1 : ℝ)) ≤ √(9 : ℝ) := Real.sqrt_le_sqrt hpi
      _ = 3 := by norm_num
  have hpoint : ∀ x ∈ Set.Icc (1 : ℝ) 2, (1 : ℝ) / 48 ≤ gaussianPDFReal 0 1 x * |x| := by
    intro x hx
    rcases hx with ⟨hx1, hx2⟩
    unfold gaussianPDFReal
    simp only [NNReal.coe_one, sub_zero]
    have hx_abs : (1 : ℝ) ≤ |x| := le_trans hx1 (le_abs_self x)
    have hexp_ge : Real.exp (-2) ≤ Real.exp (-x ^ 2 / (2 * 1)) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    have hinv_ge : (1 : ℝ) / 3 ≤ (√(2 * π * 1))⁻¹ := by
      rw [one_div]
      exact inv_anti₀ (by positivity) hsqrt_le
    calc (1 : ℝ) / 48 = (1 / 3) * ((1 / 16) * 1) := by norm_num
      _ ≤ (√(2 * π * 1))⁻¹ * (Real.exp (-x ^ 2 / (2 * 1)) * |x|) :=
          mul_le_mul hinv_ge
            (mul_le_mul (le_trans hexp_m2 hexp_ge) hx_abs (by norm_num) (Real.exp_pos _).le)
            (by norm_num) (by positivity)
      _ = (√(2 * π * 1))⁻¹ * Real.exp (-x ^ 2 / (2 * 1)) * |x| := by ring
  have h3 : ∫ _x in Set.Icc (1 : ℝ) 2, ((1 : ℝ) / 48) ≤
      ∫ x in Set.Icc (1 : ℝ) 2, gaussianPDFReal 0 1 x * |x| := by
    have hcont_pdf : Continuous (gaussianPDFReal 0 1) := by
      unfold gaussianPDFReal
      fun_prop
    refine setIntegral_mono_on (integrableOn_const (by simp)) ?_ measurableSet_Icc hpoint
    exact (hcont_pdf.mul continuous_abs).integrableOn_Icc
  have hconst : ∫ _x in Set.Icc (1 : ℝ) 2, ((1 : ℝ) / 48) = (1 : ℝ) / 48 := by
    simp
    norm_num
  linarith

private lemma lpDist_ge_rpow_sum_abs {d : ℕ} (hd : 1 ≤ d) {p : ℝ} (hp : 1 ≤ p) (z : Fin d → ℝ) :
    (d : ℝ) ^ (1 / p - 1) * ∑ k : Fin d, |z k| ≤ lpDist p z 0 := by
  have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hp_pos : 0 < p := by linarith
  have hconv := (convexOn_rpow hp).map_sum_le (t := Finset.univ)
    (w := fun _ : Fin d => (d : ℝ)⁻¹) (p := fun k : Fin d => |z k|)
    (fun _ _ => by positivity)
    (by simp [hd_pos.ne'])
    (fun _ _ => Set.mem_Ici.mpr (abs_nonneg _))
  simp only [smul_eq_mul, ← Finset.mul_sum] at hconv
  have hrpow := Real.rpow_le_rpow (by positivity) hconv (by positivity : 0 ≤ 1 / p)
  rw [← Real.rpow_mul (by positivity), mul_one_div_cancel hp_pos.ne', Real.rpow_one,
    Real.mul_rpow (by positivity) (Finset.sum_nonneg (fun _ _ => by positivity))] at hrpow
  have hlp : (∑ k : Fin d, |z k| ^ p) ^ (1 / p) = lpDist p z 0 := by
    simp [lpDist]
  rw [hlp, Real.inv_rpow hd_pos.le] at hrpow
  calc (d : ℝ) ^ (1 / p - 1) * ∑ k : Fin d, |z k|
      = (d : ℝ) ^ (1 / p) * ((d : ℝ)⁻¹ * ∑ k : Fin d, |z k|) := by
        rw [sub_eq_add_neg, Real.rpow_add hd_pos, Real.rpow_neg_one]
        ring
    _ ≤ (d : ℝ) ^ (1 / p) * (((d : ℝ) ^ (1 / p))⁻¹ * lpDist p z 0) :=
        mul_le_mul_of_nonneg_left hrpow (by positivity)
    _ = lpDist p z 0 := by
        have hne : (d : ℝ) ^ (1 / p) ≠ 0 := by positivity
        field_simp [hne]

private lemma rpow_sum_le_sum_rpow_of_le_one {ι : Type*} (s : Finset ι) {f : ι → ℝ}
    (hf : ∀ i ∈ s, 0 ≤ f i) {q : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1) :
    (∑ i ∈ s, f i) ^ q ≤ ∑ i ∈ s, (f i) ^ q := by
  by_cases hsum0 : ∑ i ∈ s, f i = 0
  · rw [hsum0, Real.zero_rpow hq0.ne']
    exact Finset.sum_nonneg (fun i hi => Real.rpow_nonneg (hf i hi) q)
  · have hsum_pos : 0 < ∑ i ∈ s, f i :=
      lt_of_le_of_ne (Finset.sum_nonneg hf) (Ne.symm hsum0)
    let S := ∑ i ∈ s, f i
    have hterm : ∀ i ∈ s, f i / S ≤ (f i / S) ^ q := by
      intro i hi
      by_cases hfi0 : f i = 0
      · simp [hfi0, Real.zero_rpow hq0.ne']
      · have hfi_pos : 0 < f i := lt_of_le_of_ne (hf i hi) (Ne.symm hfi0)
        have hdiv_pos : 0 < f i / S := div_pos hfi_pos hsum_pos
        have hdiv_le : f i / S ≤ 1 :=
          (div_le_one hsum_pos).mpr (Finset.single_le_sum hf hi)
        calc f i / S = (f i / S) ^ (1 : ℝ) := (Real.rpow_one _).symm
          _ ≤ (f i / S) ^ q := Real.rpow_le_rpow_of_exponent_ge hdiv_pos hdiv_le hq1
    have hsum_div : (1 : ℝ) ≤ ∑ i ∈ s, (f i / S) ^ q := by
      calc (1 : ℝ) = (∑ i ∈ s, f i) / S := (div_self hsum_pos.ne').symm
        _ = ∑ i ∈ s, f i / S := Finset.sum_div _ _ _
        _ ≤ ∑ i ∈ s, (f i / S) ^ q := Finset.sum_le_sum hterm
    calc S ^ q = S ^ q * 1 := (mul_one _).symm
      _ ≤ S ^ q * ∑ i ∈ s, (f i / S) ^ q :=
          mul_le_mul_of_nonneg_left hsum_div (by positivity)
      _ = ∑ i ∈ s, S ^ q * (f i / S) ^ q := Finset.mul_sum _ _ _
      _ = ∑ i ∈ s, (f i) ^ q := by
          refine Finset.sum_congr rfl (fun i hi => ?_)
          rw [← Real.mul_rpow hsum_pos.le (div_nonneg (hf i hi) hsum_pos.le),
            mul_div_cancel₀ _ hsum_pos.ne']

private lemma lpDist_le_sum_abs {d : ℕ} {p : ℝ} (hp : 1 ≤ p) (z : Fin d → ℝ) :
    lpDist p z 0 ≤ ∑ k : Fin d, |z k| := by
  have hp_pos : 0 < p := by linarith
  have h1 := rpow_sum_le_sum_rpow_of_le_one Finset.univ
    (f := fun k : Fin d => |z k| ^ p) (fun _ _ => by positivity)
    (q := 1 / p) (by positivity) (div_le_one_of_le₀ hp (by positivity))
  simp only [lpDist, Pi.zero_apply, sub_zero]
  refine le_trans h1 ?_
  refine Finset.sum_le_sum (fun k _ => ?_)
  rw [← Real.rpow_mul (abs_nonneg _), mul_one_div_cancel hp_pos.ne', Real.rpow_one]

private def coordCLM {d : ℕ} (k : Fin d) : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj k).comp
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).toContinuousLinearMap

private lemma coordCLM_apply {d : ℕ} (k : Fin d) (z : EuclideanSpace ℝ (Fin d)) :
    coordCLM k z = z.ofLp k := rfl

private lemma stdGaussian_integrable_lpDist (d : ℕ) {p : ℝ} (hp : 1 ≤ p) :
    Integrable (fun z : EuclideanSpace ℝ (Fin d) => lpDist p z.ofLp 0) (stdGaussian d) := by
  have hcont : Continuous (fun z : EuclideanSpace ℝ (Fin d) => lpDist p z.ofLp 0) := by
    unfold lpDist
    refine Continuous.rpow_const ?_ (fun _ => Or.inr (by positivity))
    refine continuous_finsetSum _ (fun k _ => ?_)
    exact ((coordCLM k).continuous.sub continuous_const).abs.rpow_const
      (fun _ => Or.inr (by linarith))
  have hdom : Integrable (fun z : EuclideanSpace ℝ (Fin d) => ∑ k : Fin d, |z.ofLp k|)
      (stdGaussian d) := by
    refine integrable_finsetSum _ (fun k _ => ?_)
    exact (IsGaussian.integrable_dual (stdGaussian d) (coordCLM k)).norm
  refine hdom.mono' hcont.aestronglyMeasurable (ae_of_all _ (fun z => ?_))
  rw [Real.norm_of_nonneg (lpDist_nonneg _ _)]
  exact lpDist_le_sum_abs hp z.ofLp

private lemma stdGaussian_integral_lpDist_ge {d : ℕ} (hd : 1 ≤ d) {p : ℝ} (hp : 1 ≤ p) :
    (1 : ℝ) / 48 * (d : ℝ) ^ (1 / p) ≤
      ∫ z : EuclideanSpace ℝ (Fin d), lpDist p z.ofLp 0 ∂(stdGaussian d) := by
  have hint_lp := stdGaussian_integrable_lpDist d hp
  have hint_abs : ∀ k : Fin d,
      Integrable (fun z : EuclideanSpace ℝ (Fin d) => |z.ofLp k|) (stdGaussian d) :=
    fun k => (IsGaussian.integrable_dual (stdGaussian d) (coordCLM k)).norm
  have hsum_int : Integrable (fun z : EuclideanSpace ℝ (Fin d) =>
      (d : ℝ) ^ (1 / p - 1) * ∑ k : Fin d, |z.ofLp k|) (stdGaussian d) :=
    (integrable_finsetSum _ (fun k _ => hint_abs k)).const_mul _
  have hmono : ∫ z : EuclideanSpace ℝ (Fin d),
      ((d : ℝ) ^ (1 / p - 1) * ∑ k : Fin d, |z.ofLp k|) ∂(stdGaussian d) ≤
      ∫ z : EuclideanSpace ℝ (Fin d), lpDist p z.ofLp 0 ∂(stdGaussian d) :=
    integral_mono hsum_int hint_lp (fun z => lpDist_ge_rpow_sum_abs hd hp z.ofLp)
  rw [integral_const_mul, integral_finsetSum _ (fun k _ => hint_abs k)] at hmono
  have hcoord : ∀ k : Fin d,
      (1 : ℝ) / 48 ≤ ∫ z : EuclideanSpace ℝ (Fin d), |z.ofLp k| ∂(stdGaussian d) := by
    intro k
    have hmap : (stdGaussian d).map (coordCLM k) = gaussianReal 0 1 := by
      rw [stdGaussian_map_dual]
      congr 1
      apply Subtype.ext
      have hsingle : ∀ j : Fin d, coordCLM k (EuclideanSpace.single j 1) =
          if j = k then 1 else 0 := by
        intro j
        simp [coordCLM, PiLp.single_apply, eq_comm]
      simp [hsingle]
    have hint_eq := integral_map (μ := stdGaussian d) (φ := coordCLM k)
      (f := fun y : ℝ => |y|) (by fun_prop) (by fun_prop)
    dsimp only [coordCLM_apply] at hint_eq
    rw [hmap] at hint_eq
    linarith [integral_abs_gaussianReal_ge, hint_eq]
  have hsum_ge : (d : ℝ) * ((1 : ℝ) / 48) ≤
      ∑ k : Fin d, ∫ z : EuclideanSpace ℝ (Fin d), |z.ofLp k| ∂(stdGaussian d) := by
    calc (d : ℝ) * ((1 : ℝ) / 48)
        = ∑ _k : Fin d, ((1 : ℝ) / 48) := by simp
      _ ≤ ∑ k : Fin d, ∫ z : EuclideanSpace ℝ (Fin d), |z.ofLp k| ∂(stdGaussian d) :=
          Finset.sum_le_sum (fun k _ => hcoord k)
  have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  calc (1 : ℝ) / 48 * (d : ℝ) ^ (1 / p)
      = (d : ℝ) ^ (1 / p - 1) * ((d : ℝ) * ((1 : ℝ) / 48)) := by
          rw [sub_eq_add_neg, Real.rpow_add hd_pos, Real.rpow_neg_one]
          field_simp [hd_pos.ne']
    _ ≤ (d : ℝ) ^ (1 / p - 1) *
          ∑ k : Fin d, ∫ z : EuclideanSpace ℝ (Fin d), |z.ofLp k| ∂(stdGaussian d) :=
        mul_le_mul_of_nonneg_left hsum_ge (by positivity)
    _ ≤ ∫ z : EuclideanSpace ℝ (Fin d), lpDist p z.ofLp 0 ∂(stdGaussian d) := hmono

/-! ### Section 4: Smooth `1`-Lipschitz approximation `smoothLp` of `‖·‖_p` (`p > 2`) -/

private def smoothLpSum (p ε : ℝ) {d : ℕ} (z : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∑ k : Fin d, ((z.ofLp k) ^ 2 + ε ^ 2) ^ (p / 2)

private def smoothLp (p ε : ℝ) {d : ℕ} (z : EuclideanSpace ℝ (Fin d)) : ℝ :=
  (smoothLpSum p ε z) ^ (1 / p)

private def smoothLpDeriv (p ε : ℝ) {d : ℕ} (z : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ :=
  ∑ k : Fin d,
    ((smoothLpSum p ε z) ^ (1 / p - 1) * z.ofLp k *
      ((z.ofLp k) ^ 2 + ε ^ 2) ^ (p / 2 - 1)) • coordCLM k

private lemma smoothLpSum_pos {d : ℕ} (hd : 1 ≤ d) (p : ℝ) {ε : ℝ} (hε : 0 < ε)
    (z : EuclideanSpace ℝ (Fin d)) :
    0 < smoothLpSum p ε z := by
  unfold smoothLpSum
  have hne : (Finset.univ : Finset (Fin d)).Nonempty := ⟨⟨0, hd⟩, Finset.mem_univ _⟩
  exact Finset.sum_pos (fun k _ => Real.rpow_pos_of_pos (by positivity) _) hne

private lemma hasFDerivAt_smoothLp {d : ℕ} (hd : 1 ≤ d) {p : ℝ} (hp : 2 < p) {ε : ℝ} (hε : 0 < ε)
    (z : EuclideanSpace ℝ (Fin d)) :
    HasFDerivAt (smoothLp p ε) (smoothLpDeriv p ε z) z := by
  have hp_ne : p ≠ 0 := by linarith
  have hterm : ∀ k : Fin d,
      HasFDerivAt (fun w : EuclideanSpace ℝ (Fin d) => ((w.ofLp k) ^ 2 + ε ^ 2) ^ (p / 2))
        ((p * z.ofLp k * ((z.ofLp k) ^ 2 + ε ^ 2) ^ (p / 2 - 1)) • coordCLM k) z := by
    intro k
    have h1 : HasFDerivAt (fun w : EuclideanSpace ℝ (Fin d) => (w.ofLp k) ^ 2 + ε ^ 2)
        ((2 * z.ofLp k) • coordCLM k) z := by
      have hc : HasFDerivAt (coordCLM k) (coordCLM k) z := (coordCLM k).hasFDerivAt
      have hsq : HasDerivAt (fun t : ℝ => t ^ 2 + ε ^ 2) (2 * z.ofLp k) (z.ofLp k) := by
        simpa using (hasDerivAt_pow 2 (z.ofLp k)).add_const (ε ^ 2)
      exact hsq.comp_hasFDerivAt z hc
    have hpos : (z.ofLp k) ^ 2 + ε ^ 2 ≠ 0 := by positivity
    have hrpow := (Real.hasDerivAt_rpow_const (p := p / 2) (Or.inl hpos)).comp_hasFDerivAt z h1
    have hscalar : (p / 2 * ((z.ofLp k) ^ 2 + ε ^ 2) ^ (p / 2 - 1)) *
        (2 * z.ofLp k) = p * z.ofLp k * ((z.ofLp k) ^ 2 + ε ^ 2) ^ (p / 2 - 1) := by ring
    simpa only [Function.comp_def, smul_smul, hscalar] using hrpow
  have hsum : HasFDerivAt (smoothLpSum p ε)
      (∑ k : Fin d, (p * z.ofLp k * ((z.ofLp k) ^ 2 + ε ^ 2) ^ (p / 2 - 1)) • coordCLM k) z := by
    have h0 := HasFDerivAt.sum (u := Finset.univ) (fun k _ => hterm k)
    refine h0.congr_of_eventuallyEq (Filter.Eventually.of_forall fun w => ?_)
    simp [smoothLpSum]
  have hS_pos := smoothLpSum_pos hd p hε z
  have hout := (Real.hasDerivAt_rpow_const (p := 1 / p) (Or.inl hS_pos.ne')).comp_hasFDerivAt z hsum
  have hderiv :
      (1 / p * (smoothLpSum p ε z) ^ (1 / p - 1)) •
        (∑ k : Fin d, (p * z.ofLp k * ((z.ofLp k) ^ 2 + ε ^ 2) ^ (p / 2 - 1)) • coordCLM k) =
      smoothLpDeriv p ε z := by
    unfold smoothLpDeriv
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [smul_smul]
    congr 1
    field_simp [hp_ne]
  rw [hderiv] at hout
  convert! hout using 1

private lemma continuous_smoothLpDeriv {d : ℕ} (hd : 1 ≤ d) (p : ℝ) {ε : ℝ} (hε : 0 < ε) :
    Continuous (smoothLpDeriv p ε (d := d)) := by
  unfold smoothLpDeriv
  refine continuous_finsetSum _ (fun k _ => ?_)
  have hcont_S : Continuous (smoothLpSum p ε (d := d)) := by
    unfold smoothLpSum
    refine continuous_finsetSum _ (fun j _ => ?_)
    exact (((coordCLM j).continuous.pow 2).add continuous_const).rpow_const
      (fun z => Or.inl (show (coordCLM j z) ^ 2 + ε ^ 2 ≠ 0 by
        have : 0 < ε ^ 2 := sq_pos_of_pos hε
        nlinarith only [sq_nonneg (coordCLM j z), this]))
  have hscalar : Continuous (fun z : EuclideanSpace ℝ (Fin d) =>
      (smoothLpSum p ε z) ^ (1 / p - 1) * z.ofLp k *
        ((z.ofLp k) ^ 2 + ε ^ 2) ^ (p / 2 - 1)) := by
    refine ((hcont_S.rpow_const (fun z => Or.inl (smoothLpSum_pos hd p hε z).ne')).mul
      (coordCLM k).continuous).mul ?_
    exact (((coordCLM k).continuous.pow 2).add continuous_const).rpow_const
      (fun z => Or.inl (show (coordCLM k z) ^ 2 + ε ^ 2 ≠ 0 by
        have : 0 < ε ^ 2 := sq_pos_of_pos hε
        nlinarith only [sq_nonneg (coordCLM k z), this]))
  exact hscalar.smul continuous_const

private lemma norm_smoothLpDeriv_le_one {d : ℕ} (hd : 1 ≤ d) {p : ℝ} (hp : 2 < p) {ε : ℝ} (hε :
    0 < ε)
    (z : EuclideanSpace ℝ (Fin d)) :
    ‖smoothLpDeriv p ε z‖ ≤ 1 := by
  have hp_pos : 0 < p := by linarith
  let c : Fin d → ℝ := fun k =>
    (smoothLpSum p ε z) ^ (1 / p - 1) * z.ofLp k * ((z.ofLp k) ^ 2 + ε ^ 2) ^ (p / 2 - 1)
  let w : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 c
  have happly : ∀ v : EuclideanSpace ℝ (Fin d), smoothLpDeriv p ε z v = @inner ℝ _ _ w v := by
    intro v
    simp [smoothLpDeriv, c, w, coordCLM_apply, EuclideanSpace.inner_eq_star_dotProduct,
      dotProduct, mul_comm]
  have hop : ‖smoothLpDeriv p ε z‖ ≤ ‖w‖ := by
    refine (smoothLpDeriv p ε z).opNorm_le_bound (norm_nonneg w) (fun v => ?_)
    rw [Real.norm_eq_abs, happly v]
    exact abs_real_inner_le_norm w v
  suffices hsq : ‖w‖ ^ 2 ≤ 1 by
    have hw_le : ‖w‖ ≤ 1 := by nlinarith [norm_nonneg w]
    exact le_trans hop hw_le
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [w, Real.norm_eq_abs, sq_abs]
  let a : Fin d → ℝ := fun k => ((z.ofLp k) ^ 2 + ε ^ 2) ^ (p / 2)
  have ha_pos : ∀ k : Fin d, 0 < a k := fun k => Real.rpow_pos_of_pos (by positivity) _
  let S := smoothLpSum p ε z
  have hS_pos : 0 < S := smoothLpSum_pos hd p hε z
  let q : ℝ := 2 * (p - 1) / p
  have hq_ge1 : 1 ≤ q := by
    dsimp [q]
    rw [le_div_iff₀ hp_pos]
    linarith
  have hck_le : ∀ k : Fin d, (c k) ^ 2 ≤ S ^ (-q) * (a k) ^ q := by
    intro k
    dsimp [c]
    let u := (z.ofLp k) ^ 2 + ε ^ 2
    have hu_pos : 0 < u := by positivity
    have hzk_le : (z.ofLp k) ^ 2 ≤ u := by dsimp [u]; linarith [sq_nonneg ε]
    have h1 : (S ^ (1 / p - 1)) ^ 2 = S ^ (-q) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hS_pos.le]
      congr 1; dsimp [q]; field_simp [hp_pos.ne']; ring
    have h2 : (z.ofLp k) ^ 2 * (u ^ (p / 2 - 1)) ^ 2 ≤ (a k) ^ q := by
      calc (z.ofLp k) ^ 2 * (u ^ (p / 2 - 1)) ^ 2
          ≤ u * (u ^ (p / 2 - 1)) ^ 2 :=
            mul_le_mul_of_nonneg_right hzk_le (sq_nonneg _)
        _ = u ^ (1 : ℝ) * u ^ ((p / 2 - 1) * 2) := by
            rw [Real.rpow_one, ← Real.rpow_natCast (u ^ _), ← Real.rpow_mul hu_pos.le]
            push_cast; rfl
        _ = u ^ (p - 1) := by
            rw [← Real.rpow_add hu_pos]
            congr 1; ring
        _ = (a k) ^ q := by
            dsimp [a, u, q]
            rw [← Real.rpow_mul hu_pos.le]
            congr 1; field_simp [hp_pos.ne']
    calc (S ^ (1 / p - 1) * z.ofLp k * u ^ (p / 2 - 1)) ^ 2
        = (S ^ (1 / p - 1)) ^ 2 * ((z.ofLp k) ^ 2 * (u ^ (p / 2 - 1)) ^ 2) := by ring
      _ ≤ S ^ (-q) * (a k) ^ q := by
          rw [h1]
          exact mul_le_mul_of_nonneg_left h2 (by positivity)
  have hsum_aq : ∑ k : Fin d, (a k) ^ q ≤ S ^ q := by
    have hq_pos : 0 < q := by linarith
    have hinv := rpow_sum_le_sum_rpow_of_le_one Finset.univ
      (f := fun k : Fin d => (a k) ^ q) (fun k _ => by positivity)
      (q := 1 / q) (by positivity) (div_le_one_of_le₀ hq_ge1 (by positivity))
    have hsimp : ∑ k : Fin d, ((a k) ^ q) ^ (1 / q) = S := by
      unfold S smoothLpSum
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [← Real.rpow_mul (ha_pos k).le, mul_one_div_cancel hq_pos.ne', Real.rpow_one]
    rw [hsimp] at hinv
    have hrpow := Real.rpow_le_rpow (by positivity) hinv hq_pos.le
    rwa [← Real.rpow_mul (by positivity), one_div_mul_cancel hq_pos.ne', Real.rpow_one] at hrpow
  calc ∑ k : Fin d, (c k) ^ 2
      ≤ ∑ k : Fin d, S ^ (-q) * (a k) ^ q := Finset.sum_le_sum (fun k _ => hck_le k)
    _ = S ^ (-q) * ∑ k : Fin d, (a k) ^ q := (Finset.mul_sum _ _ _).symm
    _ ≤ S ^ (-q) * S ^ q := mul_le_mul_of_nonneg_left hsum_aq (by positivity)
    _ = 1 := by rw [← Real.rpow_add hS_pos, neg_add_cancel, Real.rpow_zero]

private lemma smoothLp_approx
    (h_lp : ∀ (p : ℝ), 1 ≤ p →
      ∀ {d : ℕ} (x y : Fin d → ℝ),
        lpDist p x y =
          dist (WithLp.toLp (ENNReal.ofReal p) x) (WithLp.toLp (ENNReal.ofReal p) y))
    {d : ℕ} {p : ℝ} (hp : 2 < p) {ε : ℝ} (hε : 0 < ε) (z : EuclideanSpace ℝ (Fin d)) :
    lpDist p z.ofLp 0 ≤ smoothLp p ε z ∧
    smoothLp p ε z ≤ lpDist p z.ofLp 0 + (d : ℝ) ^ (1 / p) * ε := by
  have hp1 : 1 ≤ p := by linarith
  have hp_pos : 0 < p := by linarith
  have : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp1⟩
  let u : Fin d → ℝ := fun k => √((z.ofLp k) ^ 2 + ε ^ 2)
  let v : Fin d → ℝ := fun k => |z.ofLp k|
  have h_smooth_eq : smoothLp p ε z = lpDist p u 0 := by
    unfold smoothLp smoothLpSum lpDist
    congr 1
    refine Finset.sum_congr rfl (fun k _ => ?_)
    have hnn : 0 ≤ (z.ofLp k) ^ 2 + ε ^ 2 := by positivity
    dsimp [u]
    rw [sub_zero, abs_of_nonneg (Real.sqrt_nonneg _), Real.sqrt_eq_rpow,
      ← Real.rpow_mul hnn]
    ring_nf
  have h_lp_v : lpDist p z.ofLp 0 = lpDist p v 0 := by
    simp [lpDist, v]
  constructor
  · unfold lpDist smoothLp smoothLpSum
    refine Real.rpow_le_rpow (Finset.sum_nonneg (fun _ _ => by positivity)) ?_ (by positivity)
    refine Finset.sum_le_sum (fun k _ => ?_)
    simp only [Pi.zero_apply, sub_zero]
    have hsq_eq : |z.ofLp k| ^ p = ((z.ofLp k) ^ 2) ^ (p / 2) := by
      have : |z.ofLp k| = ((z.ofLp k) ^ 2) ^ ((1 : ℝ) / 2) := by
        rw [← Real.sqrt_eq_rpow, Real.sqrt_sq_eq_abs]
      rw [this, ← Real.rpow_mul (sq_nonneg _)]
      ring_nf
    rw [hsq_eq]
    exact Real.rpow_le_rpow (sq_nonneg _) (by linarith [sq_nonneg ε]) (by positivity)
  · rw [h_smooth_eq, h_lp_v]
    have htri : lpDist p u 0 ≤ lpDist p v 0 + lpDist p (u - v) 0 := by
      rw [lpDist_zero_eq_norm h_lp hp1 u, lpDist_zero_eq_norm h_lp hp1 v,
        lpDist_zero_eq_norm h_lp hp1 (u - v)]
      have hadd : WithLp.toLp (ENNReal.ofReal p) u =
          WithLp.toLp (ENNReal.ofReal p) v + WithLp.toLp (ENNReal.ofReal p) (u - v) := by
        ext k; simp
      rw [hadd]
      exact norm_add_le _ _
    have hdiff_le : lpDist p (u - v) 0 ≤ (d : ℝ) ^ (1 / p) * ε := by
      unfold lpDist
      have hterm : ∀ k : Fin d, |(u - v) k - 0| ^ p ≤ ε ^ p := by
        intro k
        simp only [Pi.sub_apply, sub_zero]
        have hge : 0 ≤ u k - v k := by
          dsimp [u, v]
          rw [← Real.sqrt_sq_eq_abs]
          exact sub_nonneg.mpr (Real.sqrt_le_sqrt (by linarith [sq_nonneg ε]))
        have hle : u k - v k ≤ ε := by
          dsimp [u, v]
          have h1 : √((z.ofLp k) ^ 2 + ε ^ 2) ≤ |z.ofLp k| + ε := by
            rw [← Real.sqrt_sq (by positivity : 0 ≤ |z.ofLp k| + ε)]
            refine Real.sqrt_le_sqrt ?_
            have : |z.ofLp k| ^ 2 = (z.ofLp k) ^ 2 := sq_abs _
            nlinarith [abs_nonneg (z.ofLp k)]
          linarith
        rw [abs_of_nonneg hge]
        exact Real.rpow_le_rpow hge hle hp_pos.le
      calc (∑ k : Fin d, |(u - v) k - 0| ^ p) ^ (1 / p)
          ≤ (∑ _k : Fin d, ε ^ p) ^ (1 / p) :=
            Real.rpow_le_rpow (Finset.sum_nonneg (fun _ _ => by positivity))
              (Finset.sum_le_sum (fun k _ => hterm k)) (by positivity)
        _ = ((d : ℝ) * ε ^ p) ^ (1 / p) := by simp
        _ = (d : ℝ) ^ (1 / p) * ε := by
            rw [Real.mul_rpow (by positivity) (by positivity),
              ← Real.rpow_mul hε.le, mul_one_div_cancel hp_pos.ne', Real.rpow_one]
    linarith

/-! ### Section 5: Maurey–Pisier Gaussian Concentration -/

open Classical in
private lemma dvoretzky_hjensen_theta :
    ∀ {d : ℕ} {f : EuclideanSpace ℝ (Fin d) → ℝ} {f' : EuclideanSpace ℝ (Fin d) → EuclideanSpace
        ℝ (Fin d) →L[ℝ] ℝ},
      (∀ (z : EuclideanSpace ℝ (Fin d)), HasFDerivAt f (f' z) z) →
        Continuous f' →
          (∀ (z : EuclideanSpace ℝ (Fin d)), ‖f' z‖ ≤ 1) →
            ∀ (lam : ℝ),
              let E : Type := EuclideanSpace ℝ (Fin d);
              let ν : Measure ℝ := ENNReal.ofReal (2 / π) • volume.restrict (Set.Icc 0 (π / 2));
              IsProbabilityMeasure ν →
                ∀ (p_xy : E × E),
                  ENNReal.ofReal (rexp (lam * (f p_xy.2 - f p_xy.1))) ≤
                    ∫⁻ (θ : ℝ),
                      ENNReal.ofReal
                        (rexp
                          (lam * (π / 2) *
                            (f' ((ContinuousLinearMap.rotation θ) p_xy).1)
                                ((ContinuousLinearMap.rotation θ) p_xy).2)) ∂ν := by
  classical
  intro d f f' hf_deriv hf'_cont hf'_norm lam E ν this
  have hpi_pos := Real.pi_pos
  intro p_xy
  let Z : ℝ → E := fun θ => (ContinuousLinearMap.rotation θ p_xy).1
  let W : ℝ → E := fun θ => (ContinuousLinearMap.rotation θ p_xy).2
  have hZ_deriv : ∀ θ : ℝ, HasDerivAt Z (W θ) θ := by
    intro θ
    dsimp [Z, W, ContinuousLinearMap.rotation_apply]
    have h1 : HasDerivAt (fun t : ℝ => Real.cos t • p_xy.1) (-Real.sin θ • p_xy.1) θ := by
      simpa [neg_smul] using (Real.hasDerivAt_cos θ).smul_const p_xy.1
    have h2 : HasDerivAt (fun t : ℝ => Real.sin t • p_xy.2) (Real.cos θ • p_xy.2) θ :=
      (Real.hasDerivAt_sin θ).smul_const p_xy.2
    exact h1.add h2
  have hcomp_deriv : ∀ θ : ℝ, HasDerivAt (fun t => f (Z t)) (f' (Z θ) (W θ)) θ :=
    fun θ => (hf_deriv (Z θ)).comp_hasDerivAt θ (hZ_deriv θ)
  let ψ : ℝ → ℝ := fun θ => (π / 2) * f' (Z θ) (W θ)
  have hψ_cont : Continuous ψ := by
    dsimp [ψ]
    refine continuous_const.mul ?_
    have hZ_cont : Continuous Z := by
      dsimp [Z, ContinuousLinearMap.rotation_apply]; fun_prop
    have hW_cont : Continuous W := by
      dsimp [W, ContinuousLinearMap.rotation_apply]; fun_prop
    exact isBoundedBilinearMap_apply.continuous.comp ((hf'_cont.comp hZ_cont).prodMk hW_cont)
  have hftc : ∫ θ in (0 : ℝ)..(π / 2), f' (Z θ) (W θ) = f p_xy.2 - f p_xy.1 := by
    have hint_ivl : IntervalIntegrable (fun θ => f' (Z θ) (W θ)) volume 0 (π / 2) := by
      have hcont_inner : Continuous (fun θ => f' (Z θ) (W θ)) := by
        have hZ_cont : Continuous Z := by dsimp [Z, ContinuousLinearMap.rotation_apply]; fun_prop
        have hW_cont : Continuous W := by dsimp [W, ContinuousLinearMap.rotation_apply]; fun_prop
        exact isBoundedBilinearMap_apply.continuous.comp ((hf'_cont.comp hZ_cont).prodMk hW_cont)
      exact hcont_inner.intervalIntegrable 0 (π / 2)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ => hcomp_deriv θ) hint_ivl]
    simp [Z, ContinuousLinearMap.rotation_apply]
  have hν_int_ψ : ∫ θ, ψ θ ∂ν = f p_xy.2 - f p_xy.1 := by
    dsimp [ν]
    rw [integral_smul_measure, ENNReal.toReal_ofReal (by positivity), smul_eq_mul,
      MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ π / 2)]
    dsimp [ψ]
    rw [intervalIntegral.integral_const_mul, hftc]
    field_simp [hpi_pos.ne']
  have hconv : ConvexOn ℝ Set.univ (fun t : ℝ => Real.exp (lam * t)) :=
    convexOn_exp.comp_linearMap (LinearMap.mul ℝ ℝ lam)
  have hψ_bdd : ∀ θ : ℝ, ‖ψ θ‖ ≤ (π / 2) * (‖p_xy.1‖ + ‖p_xy.2‖) := by
    intro θ
    simp only [ψ, Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < π / 2)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have h1 : |f' (Z θ) (W θ)| ≤ ‖f' (Z θ)‖ * ‖W θ‖ := (f' (Z θ)).le_opNorm (W θ)
    have h2 : ‖f' (Z θ)‖ * ‖W θ‖ ≤ 1 * ‖W θ‖ :=
      mul_le_mul_of_nonneg_right (hf'_norm (Z θ)) (norm_nonneg _)
    have hW_norm : ‖W θ‖ ≤ ‖p_xy.1‖ + ‖p_xy.2‖ := by
      dsimp [W, ContinuousLinearMap.rotation_apply]
      calc ‖-Real.sin θ • p_xy.1 + Real.cos θ • p_xy.2‖
          ≤ ‖-Real.sin θ • p_xy.1‖ + ‖Real.cos θ • p_xy.2‖ := norm_add_le _ _
        _ = |Real.sin θ| * ‖p_xy.1‖ + |Real.cos θ| * ‖p_xy.2‖ := by
            simp [norm_smul]
        _ ≤ 1 * ‖p_xy.1‖ + 1 * ‖p_xy.2‖ :=
            add_le_add
              (mul_le_mul_of_nonneg_right (Real.abs_sin_le_one θ) (norm_nonneg _))
              (mul_le_mul_of_nonneg_right (Real.abs_cos_le_one θ) (norm_nonneg _))
        _ = ‖p_xy.1‖ + ‖p_xy.2‖ := by ring
    linarith
  have hψ_int : Integrable ψ ν :=
    Integrable.of_bound hψ_cont.aestronglyMeasurable ((π / 2) * (‖p_xy.1‖ + ‖p_xy.2‖))
      (ae_of_all _ hψ_bdd)
  have hexp_ψ_int : Integrable (fun θ : ℝ => Real.exp (lam * ψ θ)) ν := by
    refine Integrable.of_bound (by fun_prop)
      (Real.exp (|lam| * ((π / 2) * (‖p_xy.1‖ + ‖p_xy.2‖)))) (ae_of_all _ (fun θ => ?_))
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    apply Real.exp_le_exp.mpr
    calc lam * ψ θ ≤ |lam * ψ θ| := le_abs_self _
      _ = |lam| * ‖ψ θ‖ := by rw [abs_mul, Real.norm_eq_abs]
      _ ≤ |lam| * ((π / 2) * (‖p_xy.1‖ + ‖p_xy.2‖)) :=
          mul_le_mul_of_nonneg_left (hψ_bdd θ) (abs_nonneg _)
  have hmap := hconv.map_integral_le (μ := ν) (f := ψ)
    (by fun_prop) isClosed_univ (ae_of_all _ (fun _ => Set.mem_univ _))
    hψ_int hexp_ψ_int
  change Real.exp (lam * ∫ θ, ψ θ ∂ν) ≤ ∫ θ, Real.exp (lam * ψ θ) ∂ν at hmap
  rw [hν_int_ψ] at hmap
  have h_enn := ENNReal.ofReal_le_ofReal hmap
  rw [ofReal_integral_eq_lintegral_ofReal hexp_ψ_int
    (ae_of_all _ (fun _ => (Real.exp_pos _).le))] at h_enn
  refine le_trans h_enn (lintegral_mono (fun θ => ?_))
  simp only [ψ]
  ring_nf
  exact le_rfl

private lemma maurey_pisier_mgf {d : ℕ} {f : EuclideanSpace ℝ (Fin d) → ℝ}
    {f' : EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)}
    (hf_deriv : ∀ z, HasFDerivAt f (f' z) z)
    (hf'_cont : Continuous f')
    (hf'_norm : ∀ z, ‖f' z‖ ≤ 1)
    (lam : ℝ) :
    ∫⁻ y, ENNReal.ofReal (Real.exp (lam * (f y - ∫ x, f x ∂(stdGaussian d)))) ∂(stdGaussian d) ≤
      ENNReal.ofReal (Real.exp (π ^ 2 * lam ^ 2 / 8)) := by
  let E := EuclideanSpace ℝ (Fin d)
  let γ := stdGaussian d
  have hf_diff : Differentiable ℝ f := fun z => (hf_deriv z).differentiableAt
  have hf_cont : Continuous f := hf_diff.continuous
  have hf_lip : ∀ x y : E, ‖f x - f y‖ ≤ 1 * ‖x - y‖ := fun x y =>
    Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun z _ => (hf_deriv z).hasFDerivWithinAt) (fun z _ => hf'_norm z)
      convex_univ (Set.mem_univ _) (Set.mem_univ _)
  have hf_bound : ∀ x : E, ‖f x‖ ≤ |f 0| + ‖x‖ := by
    intro x
    have h1 := hf_lip x 0
    simp only [Real.norm_eq_abs, one_mul, sub_zero] at h1 ⊢
    calc |f x| = |(f x - f 0) + f 0| := by ring_nf
      _ ≤ |f x - f 0| + |f 0| := abs_add_le _ _
      _ ≤ ‖x‖ + |f 0| := by linarith
      _ = |f 0| + ‖x‖ := add_comm _ _
  have hf_int : Integrable f γ := by
    have hdom : Integrable (fun x : E => |f 0| + ‖x‖) γ :=
      (integrable_const _).add (IsGaussian.integrable_id.norm)
    exact hdom.mono' hf_cont.aestronglyMeasurable (ae_of_all _ hf_bound)
  have hexp_int : ∀ c : ℝ, Integrable (fun x : E => Real.exp (c * f x)) γ := by
    intro c
    obtain ⟨C, hC_pos, hC_int⟩ := IsGaussian.exists_integrable_exp_sq γ
    let K : ℝ := |c| * |f 0| + c ^ 2 / (4 * C)
    have hdom : Integrable (fun x : E => Real.exp K * Real.exp (C * ‖x‖ ^ 2)) γ :=
      hC_int.const_mul _
    refine hdom.mono' (by fun_prop) (ae_of_all _ (fun x => ?_))
    rw [Real.norm_of_nonneg (Real.exp_pos _).le, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h1 : c * f x ≤ |c| * |f x| := le_trans (le_abs_self _) (by rw [abs_mul])
    have h2 : |c| * |f x| ≤ |c| * (|f 0| + ‖x‖) :=
      mul_le_mul_of_nonneg_left (hf_bound x) (abs_nonneg c)
    have hsq : 0 ≤ (2 * C * ‖x‖ - |c|) ^ 2 := sq_nonneg _
    have h3 : |c| * ‖x‖ ≤ c ^ 2 / (4 * C) + C * ‖x‖ ^ 2 := by
      rw [div_add' _ _ _ (by positivity), le_div_iff₀ (by positivity)]
      have hc2 : |c| ^ 2 = c ^ 2 := sq_abs c
      nlinarith
    dsimp [K]
    linarith
  -- Step 1: Jensen on inner integral over x
  have hjensen_x : ∀ y : E,
      Real.exp (lam * (f y - ∫ x, f x ∂γ)) ≤ ∫ x, Real.exp (lam * (f y - f x)) ∂γ := by
    intro y
    have hconv : ConvexOn ℝ Set.univ (fun t : ℝ => Real.exp ((-lam) * t)) :=
      convexOn_exp.comp_linearMap (LinearMap.mul ℝ ℝ (-lam))
    have hmap := hconv.map_integral_le (μ := γ) (f := f)
      (by fun_prop) isClosed_univ (ae_of_all _ (fun _ => Set.mem_univ _))
      hf_int (hexp_int (-lam))
    calc Real.exp (lam * (f y - ∫ x, f x ∂γ))
        = Real.exp (lam * f y) * Real.exp ((-lam) * ∫ x, f x ∂γ) := by
          rw [← Real.exp_add]; ring_nf
      _ ≤ Real.exp (lam * f y) * ∫ x, Real.exp ((-lam) * f x) ∂γ :=
          mul_le_mul_of_nonneg_left hmap (Real.exp_pos _).le
      _ = ∫ x, Real.exp (lam * f y) * Real.exp ((-lam) * f x) ∂γ :=
          (integral_const_mul _ _).symm
      _ = ∫ x, Real.exp (lam * (f y - f x)) ∂γ := by
          refine integral_congr_ae (ae_of_all _ (fun x => ?_))
          dsimp only
          rw [← Real.exp_add]; ring_nf
  -- Step 2: Smart path + Jensen over θ ∈ [0, π / 2]
  let ν : Measure ℝ := ENNReal.ofReal (2 / π) • (volume.restrict (Set.Icc 0 (π / 2)))
  have hpi_pos : 0 < π := Real.pi_pos
  have : IsProbabilityMeasure ν := by
    refine ⟨?_⟩
    simp only [ν, Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul, Real.volume_Icc,
      sub_zero, ← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 / π)]
    have : (2 / π) * (π / 2) = 1 := by field_simp [hpi_pos.ne']
    rw [this, ENNReal.ofReal_one]
  have hjensen_theta : ∀ p_xy : E × E,
      ENNReal.ofReal (Real.exp (lam * (f p_xy.2 - f p_xy.1))) ≤
        ∫⁻ θ, ENNReal.ofReal (Real.exp ((lam * (π / 2)) *
          f' (ContinuousLinearMap.rotation θ p_xy).1
             (ContinuousLinearMap.rotation θ p_xy).2)) ∂ν :=
    @dvoretzky_hjensen_theta d f f' hf_deriv hf'_cont hf'_norm lam this
  -- Step 3: Tonelli + rotation invariance + 1D Gaussian MGF
  let c : ℝ := lam * (π / 2)
  let G_fn : E × E → ℝ≥0∞ := fun p_xy => ENNReal.ofReal (Real.exp (c * f' p_xy.1 p_xy.2))
  have hG_cont : Continuous G_fn := by
    dsimp [G_fn]
    refine ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_const.mul ?_))
    exact isBoundedBilinearMap_apply.continuous.comp
      ((hf'_cont.comp continuous_fst).prodMk continuous_snd)
  have hrot_inv : ∀ θ : ℝ,
      ∫⁻ p_xy, G_fn (ContinuousLinearMap.rotation θ p_xy) ∂(γ.prod γ) ≤
        ENNReal.ofReal (Real.exp (π ^ 2 * lam ^ 2 / 8)) := by
    intro θ
    have hrot := IsGaussian.map_rotation_eq_self_of_forall_strongDual_eq_zero
      (stdGaussian_integral_dual_zero d) θ
    have h1 : ∫⁻ p_xy, G_fn (ContinuousLinearMap.rotation θ p_xy) ∂(γ.prod γ) =
        ∫⁻ p_xy, G_fn p_xy ∂(γ.prod γ) := by
      rw [← lintegral_map hG_cont.measurable (ContinuousLinearMap.rotation θ).measurable, hrot]
    rw [h1, lintegral_prod G_fn hG_cont.measurable.aemeasurable]
    have hinner : ∀ z : E,
        ∫⁻ w, ENNReal.ofReal (Real.exp (c * f' z w)) ∂γ ≤
          ENNReal.ofReal (Real.exp (π ^ 2 * lam ^ 2 / 8)) := by
      intro z
      let L := f' z
      let v_z : ℝ≥0 := ⟨∑ k : Fin d, (L (EuclideanSpace.single k 1)) ^ 2,
        Finset.sum_nonneg (fun _ _ => sq_nonneg _)⟩
      have hmap_L : γ.map L = gaussianReal 0 v_z := stdGaussian_map_dual d L
      have h_lint : ∫⁻ w, ENNReal.ofReal (Real.exp (c * L w)) ∂γ =
          ENNReal.ofReal (∫ t, Real.exp (c * t) ∂(gaussianReal 0 v_z)) := by
        have hmap_lint := lintegral_map (μ := γ)
          (f := fun t : ℝ => ENNReal.ofReal (Real.exp (c * t))) (by fun_prop) L.measurable
        rw [← hmap_lint, hmap_L,
          ← ofReal_integral_eq_lintegral_ofReal (integrable_exp_mul_gaussianReal c)
            (ae_of_all _ (fun _ => (Real.exp_pos _).le))]
      rw [h_lint]
      have hmgf : ∫ t, Real.exp (c * t) ∂(gaussianReal 0 v_z) = Real.exp (v_z * c ^ 2 / 2) := by
        have hm := congr_fun (mgf_fun_id_gaussianReal (μ := 0) (v := v_z)) c
        simpa [mgf] using hm
      rw [hmgf]
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      have hv_le : (v_z : ℝ) ≤ 1 := by
        calc (v_z : ℝ) = ∑ k : Fin d, (L (EuclideanSpace.single k 1)) ^ 2 := rfl
          _ ≤ ‖L‖ ^ 2 := stdGaussian_dual_var_le d L
          _ ≤ 1 ^ 2 := pow_le_pow_left₀ (norm_nonneg L) (hf'_norm z) 2
          _ = 1 := one_pow 2
      calc (v_z : ℝ) * c ^ 2 / 2 ≤ 1 * c ^ 2 / 2 := by gcongr
        _ = π ^ 2 * lam ^ 2 / 8 := by dsimp [c]; ring
    calc ∫⁻ z, (∫⁻ w, G_fn (z, w) ∂γ) ∂γ
        ≤ ∫⁻ _z, ENNReal.ofReal (Real.exp (π ^ 2 * lam ^ 2 / 8)) ∂γ :=
          lintegral_mono hinner
      _ = ENNReal.ofReal (Real.exp (π ^ 2 * lam ^ 2 / 8)) := by simp [γ]
  have hjoint_meas : Measurable (fun q : (E × E) × ℝ =>
      G_fn (ContinuousLinearMap.rotation q.2 q.1)) := by
    refine hG_cont.measurable.comp ?_
    have hrot_cont : Continuous (fun q : (E × E) × ℝ => ContinuousLinearMap.rotation q.2 q.1) := by
      simp only [ContinuousLinearMap.rotation_apply]
      fun_prop
    exact hrot_cont.measurable
  have hmeas_yx : Measurable (fun p_xy : E × E =>
      ENNReal.ofReal (Real.exp (lam * (f p_xy.2 - f p_xy.1)))) :=
    ENNReal.continuous_ofReal.measurable.comp
      (Real.continuous_exp.measurable.comp
        (measurable_const.mul ((hf_cont.comp continuous_snd).sub (hf_cont.comp
            continuous_fst)).measurable))
  calc ∫⁻ y, ENNReal.ofReal (Real.exp (lam * (f y - ∫ x, f x ∂γ))) ∂γ
      ≤ ∫⁻ y, ENNReal.ofReal (∫ x, Real.exp (lam * (f y - f x)) ∂γ) ∂γ :=
        lintegral_mono (fun y => ENNReal.ofReal_le_ofReal (hjensen_x y))
    _ = ∫⁻ y, (∫⁻ x, ENNReal.ofReal (Real.exp (lam * (f y - f x))) ∂γ) ∂γ := by
        refine lintegral_congr (fun y => ?_)
        have hint_yx : Integrable (fun x : E => Real.exp (lam * (f y - f x))) γ := by
          have heq : (fun x : E => Real.exp (lam * (f y - f x))) =
              fun x : E => Real.exp (lam * f y) * Real.exp ((-lam) * f x) := by
            ext x; rw [← Real.exp_add]; ring_nf
          rw [heq]
          exact (hexp_int (-lam)).const_mul _
        exact ofReal_integral_eq_lintegral_ofReal hint_yx
          (ae_of_all _ (fun _ => (Real.exp_pos _).le))
    _ = ∫⁻ p_xy, ENNReal.ofReal (Real.exp (lam * (f p_xy.2 - f p_xy.1))) ∂(γ.prod γ) :=
        (lintegral_prod_symm _ hmeas_yx.aemeasurable).symm
    _ ≤ ∫⁻ p_xy, (∫⁻ θ, G_fn (ContinuousLinearMap.rotation θ p_xy) ∂ν) ∂(γ.prod γ) :=
        lintegral_mono hjensen_theta
    _ = ∫⁻ θ, (∫⁻ p_xy, G_fn (ContinuousLinearMap.rotation θ p_xy) ∂(γ.prod γ)) ∂ν :=
        lintegral_lintegral_swap hjoint_meas.aemeasurable
    _ ≤ ∫⁻ _θ, ENNReal.ofReal (Real.exp (π ^ 2 * lam ^ 2 / 8)) ∂ν :=
        lintegral_mono hrot_inv
    _ = ENNReal.ofReal (Real.exp (π ^ 2 * lam ^ 2 / 8)) := by simp

private lemma maurey_pisier_tail {d : ℕ} {f : EuclideanSpace ℝ (Fin d) → ℝ}
    {f' : EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)}
    (hf_deriv : ∀ z, HasFDerivAt f (f' z) z)
    (hf'_cont : Continuous f')
    (hf'_norm : ∀ z, ‖f' z‖ ≤ 1)
    {s : ℝ} (hs : 0 < s) :
    (stdGaussian d) {y | s ≤ |f y - ∫ x, f x ∂(stdGaussian d)|} ≤
      2 * ENNReal.ofReal (Real.exp (- s ^ 2 / 8)) := by
  let E := EuclideanSpace ℝ (Fin d)
  let γ := stdGaussian d
  have one_side : ∀ (g : E → ℝ) (g' : E → (E →L[ℝ] ℝ)),
      (∀ z, HasFDerivAt g (g' z) z) → Continuous g' → (∀ z, ‖g' z‖ ≤ 1) →
      γ {y | s ≤ g y - ∫ x, g x ∂γ} ≤ ENNReal.ofReal (Real.exp (- s ^ 2 / 8)) := by
    intro g g' hg_d hg'_c hg'_n
    have hg_diff : Differentiable ℝ g := fun z => (hg_d z).differentiableAt
    have hg_cont : Continuous g := hg_diff.continuous
    let lam : ℝ := 4 * s / π ^ 2
    have hlam_pos : 0 < lam := by dsimp [lam]; positivity
    have hmgf := maurey_pisier_mgf hg_d hg'_c hg'_n lam
    let A := {y : E | s ≤ g y - ∫ x, g x ∂γ}
    have hA_meas : MeasurableSet A :=
      measurableSet_le measurable_const (hg_cont.measurable.sub measurable_const)
    have hmarkov : ENNReal.ofReal (Real.exp (lam * s)) * γ A ≤
        ∫⁻ y, ENNReal.ofReal (Real.exp (lam * (g y - ∫ x, g x ∂γ))) ∂γ := by
      calc ENNReal.ofReal (Real.exp (lam * s)) * γ A
          = ∫⁻ _y in A, ENNReal.ofReal (Real.exp (lam * s)) ∂γ := by
              rw [lintegral_const, Measure.restrict_apply_univ]
        _ ≤ ∫⁻ y in A, ENNReal.ofReal (Real.exp (lam * (g y - ∫ x, g x ∂γ))) ∂γ := by
              refine setLIntegral_mono (by fun_prop) (fun y hy => ?_)
              apply ENNReal.ofReal_le_ofReal
              apply Real.exp_le_exp.mpr
              exact mul_le_mul_of_nonneg_left hy hlam_pos.le
        _ ≤ ∫⁻ y, ENNReal.ofReal (Real.exp (lam * (g y - ∫ x, g x ∂γ))) ∂γ :=
              lintegral_mono' Measure.restrict_le_self le_rfl
    have hcomb := le_trans hmarkov hmgf
    have hexp_pos : 0 < ENNReal.ofReal (Real.exp (lam * s)) :=
      ENNReal.ofReal_pos.mpr (Real.exp_pos _)
    have hexp_ne_top : ENNReal.ofReal (Real.exp (lam * s)) ≠ ⊤ := ENNReal.ofReal_ne_top
    have hmul_inv := mul_le_mul_of_nonneg_left hcomb
      (show (0 : ℝ≥0∞) ≤ ENNReal.ofReal (Real.exp (-lam * s)) from zero_le)
    have hprod_one : ENNReal.ofReal (Real.exp (-lam * s)) * ENNReal.ofReal (Real.exp (lam * s))
        = 1 := by
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      ring_nf
      rw [Real.exp_zero, ENNReal.ofReal_one]
    rw [← mul_assoc, hprod_one, one_mul,
      ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add] at hmul_inv
    refine le_trans hmul_inv (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_))
    have hexp_eq : -lam * s + π ^ 2 * lam ^ 2 / 8 = - 2 * s ^ 2 / π ^ 2 := by
      dsimp [lam]
      have hpi_ne : π ≠ 0 := Real.pi_pos.ne'
      field_simp [hpi_ne]
      ring
    rw [hexp_eq]
    have hpi_sq : π ^ 2 ≤ 16 := by
      have h4 := Real.pi_lt_four
      have h0 := Real.pi_pos
      nlinarith
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have h_upper := one_side f f' hf_deriv hf'_cont hf'_norm
  have h_lower_raw := one_side (fun z => -f z) (fun z => -f' z)
    (fun z => (hf_deriv z).neg) hf'_cont.neg (fun z => by simpa using hf'_norm z)
  have h_lower : γ {y | s ≤ ∫ x, f x ∂γ - f y} ≤ ENNReal.ofReal (Real.exp (- s ^ 2 / 8)) := by
    convert h_lower_raw using 2
    ext y
    simp only [Set.mem_ofPred_eq, integral_neg]
    ring_nf
  have hsub : {y : E | s ≤ |f y - ∫ x, f x ∂γ|} ⊆
      {y : E | s ≤ f y - ∫ x, f x ∂γ} ∪ {y : E | s ≤ ∫ x, f x ∂γ - f y} := by
    intro y hy
    simp only [Set.mem_ofPred_eq, Set.mem_union] at hy ⊢
    rcases le_abs.mp hy with h1 | h2
    · exact Or.inl h1
    · exact Or.inr (by linarith)
  calc γ {y | s ≤ |f y - ∫ x, f x ∂γ|}
      ≤ γ ({y | s ≤ f y - ∫ x, f x ∂γ} ∪ {y | s ≤ ∫ x, f x ∂γ - f y}) := measure_mono hsub
    _ ≤ γ {y | s ≤ f y - ∫ x, f x ∂γ} + γ {y | s ≤ ∫ x, f x ∂γ - f y} := measure_union_le _ _
    _ ≤ ENNReal.ofReal (Real.exp (- s ^ 2 / 8)) + ENNReal.ofReal (Real.exp (- s ^ 2 / 8)) :=
        add_le_add h_upper h_lower
    _ = 2 * ENNReal.ofReal (Real.exp (- s ^ 2 / 8)) := ( two_mul _ ).symm

private lemma stdGaussian_lpDist_tail
    (h_lp : ∀ (p : ℝ), 1 ≤ p →
      ∀ {d : ℕ} (x y : Fin d → ℝ),
        lpDist p x y =
          dist (WithLp.toLp (ENNReal.ofReal p) x) (WithLp.toLp (ENNReal.ofReal p) y))
    {d : ℕ} (hd : 1 ≤ d) {p : ℝ} (hp : 2 < p) {t : ℝ} (ht : 0 < t) :
    (stdGaussian d)
        {y | t ≤ |lpDist p y.ofLp 0 - ∫ x, lpDist p x.ofLp 0 ∂(stdGaussian d)|} ≤
      2 * ENNReal.ofReal (Real.exp (- t ^ 2 / 32)) := by
  let γ := stdGaussian d
  have hp1 : 1 ≤ p := by linarith
  have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  let ε : ℝ := (d : ℝ) ^ (-1 / p) * (t / 2)
  have hε_pos : 0 < ε := by dsimp [ε]; positivity
  have hdε : (d : ℝ) ^ (1 / p) * ε = t / 2 := by
    dsimp [ε]
    rw [← mul_assoc, ← Real.rpow_add hd_pos]
    have : 1 / p + -1 / p = 0 := by ring
    rw [this, Real.rpow_zero, one_mul]
  have hf_int : Integrable (smoothLp p ε) γ := by
    have hdiff : Differentiable ℝ (smoothLp p ε (d := d)) :=
      fun z => (hasFDerivAt_smoothLp hd hp hε_pos z).differentiableAt
    have hcont : Continuous (smoothLp p ε (d := d)) := hdiff.continuous
    have hdom : Integrable (fun z : EuclideanSpace ℝ (Fin d) =>
        lpDist p z.ofLp 0 + (d : ℝ) ^ (1 / p) * ε) γ :=
      (stdGaussian_integrable_lpDist d hp1).add (integrable_const _)
    refine hdom.mono' hcont.aestronglyMeasurable (ae_of_all _ (fun z => ?_))
    have happr := smoothLp_approx h_lp hp hε_pos z
    rw [Real.norm_of_nonneg (le_trans (lpDist_nonneg _ _) happr.1)]
    exact happr.2
  have hg_int := stdGaussian_integrable_lpDist d hp1
  have hint_le1 : ∫ x, lpDist p x.ofLp 0 ∂γ ≤ ∫ x, smoothLp p ε x ∂γ :=
    integral_mono hg_int hf_int (fun z => (smoothLp_approx h_lp hp hε_pos z).1)
  have hint_le2 : ∫ x, smoothLp p ε x ∂γ ≤ ∫ x, lpDist p x.ofLp 0 ∂γ + t / 2 := by
    calc ∫ x, smoothLp p ε x ∂γ
        ≤ ∫ x, (lpDist p x.ofLp 0 + (d : ℝ) ^ (1 / p) * ε) ∂γ :=
          integral_mono hf_int (hg_int.add (integrable_const _))
            (fun z => (smoothLp_approx h_lp hp hε_pos z).2)
      _ = ∫ x, lpDist p x.ofLp 0 ∂γ + (d : ℝ) ^ (1 / p) * ε := by
          rw [integral_add hg_int (integrable_const _), integral_const]
          simp [γ]
      _ = ∫ x, lpDist p x.ofLp 0 ∂γ + t / 2 := by rw [hdε]
  have hsub : {y : EuclideanSpace ℝ (Fin d) |
        t ≤ |lpDist p y.ofLp 0 - ∫ x, lpDist p x.ofLp 0 ∂γ|} ⊆
      {y : EuclideanSpace ℝ (Fin d) |
        t / 2 ≤ |smoothLp p ε y - ∫ x, smoothLp p ε x ∂γ|} := by
    intro y hy
    simp only [Set.mem_ofPred_eq] at hy ⊢
    have happr := smoothLp_approx h_lp hp hε_pos y
    rw [hdε] at happr
    have hdiff_abs : |(lpDist p y.ofLp 0 - ∫ x, lpDist p x.ofLp 0 ∂γ) -
        (smoothLp p ε y - ∫ x, smoothLp p ε x ∂γ)| ≤ t / 2 := by
      rw [abs_le]
      constructor <;> linarith [happr.1, happr.2, hint_le1, hint_le2]
    have htri := abs_sub_abs_le_abs_sub
      (lpDist p y.ofLp 0 - ∫ x, lpDist p x.ofLp 0 ∂γ)
      (smoothLp p ε y - ∫ x, smoothLp p ε x ∂γ)
    linarith
  have htail := maurey_pisier_tail
    (fun z => hasFDerivAt_smoothLp hd hp hε_pos z)
    (continuous_smoothLpDeriv hd p hε_pos)
    (fun z => norm_smoothLpDeriv_le_one hd hp hε_pos z)
    (by positivity : 0 < t / 2)
  calc γ {y | t ≤ |lpDist p y.ofLp 0 - ∫ x, lpDist p x.ofLp 0 ∂γ|}
      ≤ γ {y | t / 2 ≤ |smoothLp p ε y - ∫ x, smoothLp p ε x ∂γ|} := measure_mono hsub
    _ ≤ 2 * ENNReal.ofReal (Real.exp (- (t / 2) ^ 2 / 8)) := htail
    _ = 2 * ENNReal.ofReal (Real.exp (- t ^ 2 / 32)) := by
        congr 3; ring

/-! ### Section 6: Figiel–Lindenstrauss–Milman [FLM77, Example 3.1] embedding `ℓ_2^{d₂} ↪ ℓ_p^d` -/

private lemma lpDist_eq_sub_zero {p : ℝ} {d : ℕ} (x y : Fin d → ℝ) :
    lpDist p x y = lpDist p (x - y) 0 := by
  simp [lpDist]

private lemma opNorm_le_of_tenth_net {d₂ : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (G : EuclideanSpace ℝ (Fin d₂) →L[ℝ] E) (μ : ℝ) (hμ : 0 < μ)
    (N_net : Finset (EuclideanSpace ℝ (Fin d₂)))
    (hN_cov : ∀ v : EuclideanSpace ℝ (Fin d₂), ‖v‖ = 1 →
      ∃ u ∈ N_net, ‖v - u‖ ≤ 1 / 10)
    (hG_net : ∀ u ∈ N_net, ‖G u‖ ≤ (11 / 10 : ℝ) * μ) :
    ‖G‖ ≤ (11 / 10 : ℝ) * μ + (1 / 10 : ℝ) * ‖G‖ := by
  refine G.opNorm_le_bound (by positivity) (fun x => ?_)
  by_cases hx0 : ‖x‖ = 0
  · simp [norm_eq_zero.mp hx0]
  · have hx_pos : 0 < ‖x‖ := lt_of_le_of_ne (norm_nonneg x) (Ne.symm hx0)
    let v : EuclideanSpace ℝ (Fin d₂) := (‖x‖⁻¹) • x
    have hv_norm : ‖v‖ = 1 := by
      simp [v, norm_smul, hx0]
    obtain ⟨u, huN, hvu⟩ := hN_cov v hv_norm
    have hGv : ‖G v‖ ≤ (11 / 10 : ℝ) * μ + (1 / 10 : ℝ) * ‖G‖ := by
      calc ‖G v‖ = ‖G u + G (v - u)‖ := by
            rw [← map_add, add_sub_cancel]
        _ ≤ ‖G u‖ + ‖G (v - u)‖ := norm_add_le _ _
        _ ≤ (11 / 10 : ℝ) * μ + ‖G‖ * ‖v - u‖ :=
            add_le_add (hG_net u huN) (G.le_opNorm _)
        _ ≤ (11 / 10 : ℝ) * μ + ‖G‖ * (1 / 10 : ℝ) :=
            add_le_add le_rfl (mul_le_mul_of_nonneg_left hvu (norm_nonneg _))
        _ = (11 / 10 : ℝ) * μ + (1 / 10 : ℝ) * ‖G‖ := by ring
    have hx_eq : x = ‖x‖ • v := by
      simp [v, smul_smul, hx0]
    calc ‖G x‖ = ‖G (‖x‖ • v)‖ := by rw [← hx_eq]
      _ = ‖x‖ * ‖G v‖ := by
          rw [map_smul, norm_smul, Real.norm_of_nonneg hx_pos.le]
      _ ≤ ‖x‖ * ((11 / 10 : ℝ) * μ + (1 / 10 : ℝ) * ‖G‖) :=
          mul_le_mul_of_nonneg_left hGv hx_pos.le
      _ = ((11 / 10 : ℝ) * μ + (1 / 10 : ℝ) * ‖G‖) * ‖x‖ := mul_comm _ _

private lemma linearMap_bounds_of_tenth_net {d₂ : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (G : EuclideanSpace ℝ (Fin d₂) →L[ℝ] E) (μ : ℝ) (hμ : 0 < μ)
    (N_net : Finset (EuclideanSpace ℝ (Fin d₂)))
    (hN_cov : ∀ v : EuclideanSpace ℝ (Fin d₂), ‖v‖ = 1 →
      ∃ u ∈ N_net, ‖v - u‖ ≤ 1 / 10)
    (hG_net : ∀ u ∈ N_net, (9 / 10 : ℝ) * μ ≤ ‖G u‖)
    (hG_opnorm : ‖G‖ ≤ (11 / 9 : ℝ) * μ) :
    ∀ x : EuclideanSpace ℝ (Fin d₂),
      (7 / 9 : ℝ) * μ * ‖x‖ ≤ ‖G x‖ ∧ ‖G x‖ ≤ (11 / 9 : ℝ) * μ * ‖x‖ := by
  intro x
  constructor
  · by_cases hx0 : ‖x‖ = 0
    · rw [hx0, mul_zero]; exact norm_nonneg _
    · have hx_pos : 0 < ‖x‖ := lt_of_le_of_ne (norm_nonneg x) (Ne.symm hx0)
      let v : EuclideanSpace ℝ (Fin d₂) := (‖x‖⁻¹) • x
      have hv_norm : ‖v‖ = 1 := by simp [v, norm_smul, hx0]
      obtain ⟨u, huN, hvu⟩ := hN_cov v hv_norm
      have hGv_lo : (7 / 9 : ℝ) * μ ≤ ‖G v‖ := by
        have h1 : (9 / 10 : ℝ) * μ ≤ ‖G v‖ + ‖G (v - u)‖ := by
          calc (9 / 10 : ℝ) * μ ≤ ‖G u‖ := hG_net u huN
            _ = ‖G v - G (v - u)‖ := by rw [← map_sub, sub_sub_cancel]
            _ ≤ ‖G v‖ + ‖G (v - u)‖ := norm_sub_le _ _
        have h2 : ‖G (v - u)‖ ≤ (11 / 90 : ℝ) * μ := by
          calc ‖G (v - u)‖ ≤ ‖G‖ * ‖v - u‖ := G.le_opNorm _
            _ ≤ ((11 / 9 : ℝ) * μ) * (1 / 10 : ℝ) :=
                mul_le_mul hG_opnorm hvu (norm_nonneg _) (by positivity)
            _ = (11 / 90 : ℝ) * μ := by ring
        linarith
      have hx_eq : x = ‖x‖ • v := by simp [v, smul_smul, hx0]
      calc (7 / 9 : ℝ) * μ * ‖x‖
          = ‖x‖ * ((7 / 9 : ℝ) * μ) := mul_comm _ _
        _ ≤ ‖x‖ * ‖G v‖ := mul_le_mul_of_nonneg_left hGv_lo hx_pos.le
        _ = ‖G x‖ := by
            conv_rhs => rw [hx_eq, map_smul, norm_smul, Real.norm_of_nonneg hx_pos.le]
  · calc ‖G x‖ ≤ ‖G‖ * ‖x‖ := G.le_opNorm x
      _ ≤ (11 / 9 : ℝ) * μ * ‖x‖ :=
          mul_le_mul_of_nonneg_right hG_opnorm (norm_nonneg x)

private lemma flm_l2_into_lp
    (h_lp : ∀ (p : ℝ), 1 ≤ p →
      ∀ {d : ℕ} (x y : Fin d → ℝ),
        lpDist p x y =
          dist (WithLp.toLp (ENNReal.ofReal p) x) (WithLp.toLp (ENNReal.ofReal p) y))
    {p : ℝ} (hp : 2 < p) :
    ∃ (κ₁ κ₂ : ℝ), 0 < κ₁ ∧ κ₁ ≤ κ₂ ∧
      ∀ (d₂ : ℕ), 1 ≤ d₂ →
        ∃ (d : ℕ) (T : (Fin d₂ → ℝ) →ₗ[ℝ] (Fin d → ℝ)),
          1 ≤ d ∧
          κ₁ * (d₂ : ℝ) ^ (p / 2) ≤ (d : ℝ) ∧
          (d : ℝ) ≤ κ₂ * (d₂ : ℝ) ^ (p / 2) ∧
          ∀ v : Fin d₂ → ℝ,
            lpDist 2 v 0 ≤ lpDist p (T v) 0 ∧
            lpDist p (T v) 0 ≤ 2 * lpDist 2 v 0 := by
  have hp1 : 1 ≤ p := by linarith
  have hp_pos : 0 < p := by linarith
  have : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp1⟩
  let K_p : ℝ := (50000000 : ℝ) ^ (p / 2)
  have hKp_pos : 0 < K_p := by dsimp [K_p]; positivity
  have hKp_ge1 : 1 ≤ K_p := Real.one_le_rpow (by norm_num) (by positivity)
  refine ⟨K_p, K_p + 1, hKp_pos, by linarith, ?_⟩
  intro d₂ hd₂
  have hd₂_real : (1 : ℝ) ≤ (d₂ : ℝ) := by exact_mod_cast hd₂
  have hd₂_rpow_ge1 : (1 : ℝ) ≤ (d₂ : ℝ) ^ (p / 2) :=
    Real.one_le_rpow hd₂_real (by positivity)
  let d : ℕ := ⌈K_p * (d₂ : ℝ) ^ (p / 2)⌉₊
  have hd_lo : K_p * (d₂ : ℝ) ^ (p / 2) ≤ (d : ℝ) := Nat.le_ceil _
  have hd_ge1_real : (1 : ℝ) ≤ (d : ℝ) := by nlinarith
  have hd_ge1 : 1 ≤ d := by exact_mod_cast hd_ge1_real
  have hd_hi : (d : ℝ) ≤ (K_p + 1) * (d₂ : ℝ) ^ (p / 2) := by
    have hlt := Nat.ceil_lt_add_one (show 0 ≤ K_p * (d₂ : ℝ) ^ (p / 2) by positivity)
    change (d : ℝ) < _ at hlt
    nlinarith
  -- Step 1: Lower bound on `μ_d = E[‖Z‖_p]` and concentration parameter `t = μ_d / 10`
  let μ_d : ℝ := ∫ x : EuclideanSpace ℝ (Fin d), lpDist p x.ofLp 0 ∂(stdGaussian d)
  have hμ_ge_d : (1 : ℝ) / 48 * (d : ℝ) ^ (1 / p) ≤ μ_d :=
    stdGaussian_integral_lpDist_ge hd_ge1 hp1
  have hd_rpow_ge : (50000000 * (d₂ : ℝ)) ^ ((1 : ℝ) / 2) ≤ (d : ℝ) ^ (1 / p) := by
    have h1 : (50000000 * (d₂ : ℝ)) ^ (p / 2) ≤ (d : ℝ) := by
      rw [Real.mul_rpow (by norm_num) (by positivity)]
      exact hd_lo
    have h2 := Real.rpow_le_rpow (by positivity) h1 (by positivity : 0 ≤ 1 / p)
    rw [← Real.rpow_mul (by positivity)] at h2
    have hexp : p / 2 * (1 / p) = (1 : ℝ) / 2 := by field_simp [hp_pos.ne']
    rwa [hexp] at h2
  have hμ_pos : 0 < μ_d := by
    have : (0 : ℝ) < (1 : ℝ) / 48 * (50000000 * (d₂ : ℝ)) ^ ((1 : ℝ) / 2) := by positivity
    linarith [mul_le_mul_of_nonneg_left hd_rpow_ge (by norm_num : (0 : ℝ) ≤ 1 / 48)]
  let t : ℝ := (1 / 10 : ℝ) * μ_d
  have ht_pos : 0 < t := by dsimp [t]; positivity
  have ht_sq : 6 * (d₂ : ℝ) ≤ t ^ 2 / 32 := by
    have ht_ge : (1 / 480 : ℝ) * (50000000 * (d₂ : ℝ)) ^ ((1 : ℝ) / 2) ≤ t := by
      dsimp [t]
      have := mul_le_mul_of_nonneg_left hd_rpow_ge (by norm_num : (0 : ℝ) ≤ 1 / 48)
      linarith
    have hsq1 : ((1 / 480 : ℝ) * (50000000 * (d₂ : ℝ)) ^ ((1 : ℝ) / 2)) ^ 2 ≤ t ^ 2 :=
      pow_le_pow_left₀ (by positivity) ht_ge 2
    rw [mul_pow, ← Real.rpow_natCast ((50000000 * _) ^ _), ← Real.rpow_mul (by positivity)] at hsq1
    have hexp2 : (1 : ℝ) / 2 * ((2 : ℕ) : ℝ) = 1 := by norm_num
    rw [hexp2, Real.rpow_one] at hsq1
    linarith
  -- Step 2: Union bound over `(1 / 10)`-net on `S^{d₂ - 1}` under `matMeasure d d₂`
  obtain ⟨N_net, hN_card, hN_norm, hN_cov⟩ := sphere_tenth_net d₂
  let eval_u : EuclideanSpace ℝ (Fin d₂) → (Fin d → Fin d₂ → ℝ) → EuclideanSpace ℝ (Fin d) :=
    fun u M => WithLp.toLp 2 (fun k => ∑ j : Fin d₂, u.ofLp j * M k j)
  have hmeas_eval : ∀ u, Measurable (eval_u u) := by
    intro u
    have heq : eval_u u = (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm ∘
        (fun M : Fin d → Fin d₂ → ℝ => fun k : Fin d => ∑ j : Fin d₂, u.ofLp j * M k j) := rfl
    rw [heq]
    fun_prop
  have hcont_lp : Continuous (fun z : EuclideanSpace ℝ (Fin d) => lpDist p z.ofLp 0) := by
    unfold lpDist
    refine Continuous.rpow_const ?_ (fun _ => Or.inr (by positivity))
    refine continuous_finsetSum _ (fun k _ => ?_)
    exact ((coordCLM k).continuous.sub continuous_const).abs.rpow_const
      (fun _ => Or.inr (by linarith))
  let B_target : Set (EuclideanSpace ℝ (Fin d)) := {y | t ≤ |lpDist p y.ofLp 0 - μ_d|}
  have hB_meas : MeasurableSet B_target :=
    measurableSet_le measurable_const ((hcont_lp.sub continuous_const).abs.measurable)
  have hexp_bound : Real.exp (- t ^ 2 / 32) ≤ (1 / 64 : ℝ) ^ d₂ := by
    have hexp1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have h64 : (64 : ℝ) ^ d₂ ≤ Real.exp (6 * (d₂ : ℝ)) := by
      have hpow : (2 : ℝ) ^ (6 * d₂) ≤ (Real.exp 1) ^ (6 * d₂) :=
        pow_le_pow_left₀ (by norm_num) hexp1 (6 * d₂)
      rw [← Real.exp_nat_mul, mul_one, Nat.cast_mul, Nat.cast_ofNat] at hpow
      have h64_eq : (2 : ℝ) ^ (6 * d₂) = (64 : ℝ) ^ d₂ := by
        rw [pow_mul]
        norm_num
      rwa [h64_eq] at hpow
    calc Real.exp (- t ^ 2 / 32)
        ≤ Real.exp (- (6 * (d₂ : ℝ))) := by
          apply Real.exp_le_exp.mpr; linarith
      _ = (Real.exp (6 * (d₂ : ℝ)))⁻¹ := Real.exp_neg _
      _ ≤ ((64 : ℝ) ^ d₂)⁻¹ := inv_anti₀ (by positivity) h64
      _ = (1 / 64 : ℝ) ^ d₂ := by rw [← inv_pow, one_div]
  have heach_u : ∀ u ∈ N_net,
      matMeasure d d₂ (eval_u u ⁻¹' B_target) ≤ 2 * ENNReal.ofReal ((1 / 64 : ℝ) ^ d₂) := by
    intro u hu
    rw [← Measure.map_apply (hmeas_eval u) hB_meas, matMeasure_map_eval_unit u (hN_norm u hu)]
    calc (stdGaussian d) B_target
        ≤ 2 * ENNReal.ofReal (Real.exp (- t ^ 2 / 32)) :=
          stdGaussian_lpDist_tail h_lp hd_ge1 hp ht_pos
      _ ≤ 2 * ENNReal.ofReal ((1 / 64 : ℝ) ^ d₂) :=
          mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal hexp_bound) (zero_le)
  have hunion_lt_one : matMeasure d d₂ (⋃ u ∈ N_net, eval_u u ⁻¹' B_target) < 1 := by
    have hub1 : matMeasure d d₂ (⋃ u ∈ N_net, eval_u u ⁻¹' B_target) ≤
        ((21 ^ d₂ : ℕ) : ℝ≥0∞) * (2 * ENNReal.ofReal ((1 / 64 : ℝ) ^ d₂)) := by
      calc matMeasure d d₂ (⋃ u ∈ N_net, eval_u u ⁻¹' B_target)
          ≤ ∑ u ∈ N_net, matMeasure d d₂ (eval_u u ⁻¹' B_target) :=
            measure_biUnion_finset_le N_net _
        _ ≤ ∑ _u ∈ N_net, (2 * ENNReal.ofReal ((1 / 64 : ℝ) ^ d₂)) :=
            Finset.sum_le_sum heach_u
        _ = (N_net.card : ℝ≥0∞) * (2 * ENNReal.ofReal ((1 / 64 : ℝ) ^ d₂)) := by simp
        _ ≤ ((21 ^ d₂ : ℕ) : ℝ≥0∞) * (2 * ENNReal.ofReal ((1 / 64 : ℝ) ^ d₂)) :=
            mul_le_mul_of_nonneg_right (by exact_mod_cast hN_card) (zero_le)
    have heq_enn : ((21 ^ d₂ : ℕ) : ℝ≥0∞) * (2 * ENNReal.ofReal ((1 / 64 : ℝ) ^ d₂)) =
        ENNReal.ofReal (2 * (21 / 64 : ℝ) ^ d₂) := by
      have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by norm_num
      rw [← ENNReal.ofReal_natCast, h2,
        ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      push_cast
      rw [show (21 : ℝ) ^ d₂ * (2 * (1 / 64 : ℝ) ^ d₂) = 2 * ((21 : ℝ) ^ d₂ * (1 / 64 : ℝ) ^ d₂)
          by ring,
        ← mul_pow]
      ring_nf
    rw [heq_enn] at hub1
    have hpow_le : (21 / 64 : ℝ) ^ d₂ ≤ 21 / 64 := by
      have hpow_one : ∀ m : ℕ, (21 / 64 : ℝ) ^ m ≤ 1 := by
        intro m
        induction m with
        | zero => norm_num
        | succ m ih =>
          rw [pow_succ]
          nlinarith [show (0 : ℝ) ≤ (21 / 64 : ℝ) ^ m by positivity]
      obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hd₂
      rw [pow_add, pow_one]
      nlinarith [hpow_one m]
    have hlt_real : ENNReal.ofReal (2 * (21 / 64 : ℝ) ^ d₂) < 1 := by
      rw [← ENNReal.ofReal_one]
      exact (ENNReal.ofReal_lt_ofReal_iff zero_lt_one).mpr (by linarith)
    exact lt_of_le_of_lt hub1 hlt_real
  have hex_M : ∃ M₀ : Fin d → Fin d₂ → ℝ,
      ∀ u ∈ N_net, |lpDist p (eval_u u M₀).ofLp 0 - μ_d| < t := by
    by_contra h_all
    push Not at h_all
    have huniv_sub : (Set.univ : Set (Fin d → Fin d₂ → ℝ)) ⊆
        ⋃ u ∈ N_net, eval_u u ⁻¹' B_target := by
      intro M _
      obtain ⟨u, huN, hMu⟩ := h_all M
      exact Set.mem_biUnion huN hMu
    have h1 : (1 : ℝ≥0∞) ≤ matMeasure d d₂ (⋃ u ∈ N_net, eval_u u ⁻¹' B_target) := by
      rw [← measure_univ (μ := matMeasure d d₂)]
      exact measure_mono huniv_sub
    exact not_lt_of_ge h1 hunion_lt_one
  obtain ⟨M₀, hM₀⟩ := hex_M
  -- Step 3: Net extension via operator norm of `G_clm` and rescaling
  let G_raw : (Fin d₂ → ℝ) →ₗ[ℝ] (Fin d → ℝ) :=
    { toFun := fun v k => ∑ j : Fin d₂, v j * M₀ k j
      map_add' := fun x y => by ext k; simp [add_mul, Finset.sum_add_distrib]
      map_smul' := fun r x => by ext k; simp [mul_assoc, ← Finset.mul_sum] }
  let G_lin : EuclideanSpace ℝ (Fin d₂) →ₗ[ℝ] PiLp (ENNReal.ofReal p) (fun _ : Fin d => ℝ) :=
    { toFun := fun x => WithLp.toLp (ENNReal.ofReal p) (G_raw x.ofLp)
      map_add' := fun x y => by
        ext k; simp [G_raw, add_mul, Finset.sum_add_distrib]
      map_smul' := fun r x => by
        ext k; simp [G_raw] }
  let G_clm := G_lin.toContinuousLinearMap
  have hG_norm_eq : ∀ x : EuclideanSpace ℝ (Fin d₂),
      ‖G_clm x‖ = lpDist p (G_raw x.ofLp) 0 := by
    intro x
    rw [lpDist_zero_eq_norm h_lp hp1]
    rfl
  have hG_net : ∀ u ∈ N_net,
      (9 / 10 : ℝ) * μ_d ≤ ‖G_clm u‖ ∧ ‖G_clm u‖ ≤ (11 / 10 : ℝ) * μ_d := by
    intro u hu
    have h_abs := (hM₀ u hu).le
    have heval : (eval_u u M₀).ofLp = G_raw u.ofLp := rfl
    rw [heval, ← hG_norm_eq u] at h_abs
    rw [abs_le] at h_abs
    dsimp [t] at h_abs
    constructor <;> linarith
  have hG_opnorm_step := opNorm_le_of_tenth_net G_clm μ_d hμ_pos N_net hN_cov
    (fun u hu => (hG_net u hu).2)
  have hG_opnorm : ‖G_clm‖ ≤ (11 / 9 : ℝ) * μ_d := by linarith
  have hG_all := linearMap_bounds_of_tenth_net G_clm μ_d hμ_pos N_net hN_cov
    (fun u hu => (hG_net u hu).1) hG_opnorm
  let α : ℝ := (9 : ℝ) / (7 * μ_d)
  have hα_pos : 0 < α := by dsimp [α]; positivity
  let T : (Fin d₂ → ℝ) →ₗ[ℝ] (Fin d → ℝ) := α • G_raw
  refine ⟨d, T, hd_ge1, hd_lo, hd_hi, ?_⟩
  intro v
  let x : EuclideanSpace ℝ (Fin d₂) := WithLp.toLp 2 v
  have hx_l2 : lpDist 2 v 0 = ‖x‖ := lpDist_two_zero_eq_eucl_norm h_lp v
  have hTv_lp : lpDist p (T v) 0 = α * ‖G_clm x‖ := by
    rw [lpDist_zero_eq_norm h_lp hp1]
    have h_eq : WithLp.toLp (ENNReal.ofReal p) (T v) = α • G_clm x := by
      ext k; rfl
    rw [h_eq, norm_smul, Real.norm_of_nonneg hα_pos.le]
  rw [hx_l2, hTv_lp]
  obtain ⟨hlo, hhi⟩ := hG_all x
  constructor
  · calc ‖x‖ = α * ((7 / 9 : ℝ) * μ_d * ‖x‖) := by
          dsimp [α]; field_simp [hμ_pos.ne']
      _ ≤ α * ‖G_clm x‖ := mul_le_mul_of_nonneg_left hlo hα_pos.le
  · calc α * ‖G_clm x‖
        ≤ α * ((11 / 9 : ℝ) * μ_d * ‖x‖) := mul_le_mul_of_nonneg_left hhi hα_pos.le
      _ = (11 / 7 : ℝ) * ‖x‖ := by dsimp [α]; field_simp [hμ_pos.ne']
      _ ≤ 2 * ‖x‖ := by nlinarith [norm_nonneg x]


end

end Helpers

/-- **Corollary 1.4 (`p`-Independent Exponent for `p > 2` via Dvoretzky Embedding)** Takes
`lpDist_eq_toLp_dist` and Theorem 1.3 as explicit hypotheses so this module compiles
independently. -/
theorem cor_1_4_from_1_3
    (h_lp : ∀ (p : ℝ), 1 ≤ p →
      ∀ {d : ℕ} (x y : Fin d → ℝ),
        lpDist p x y =
          dist (WithLp.toLp (ENNReal.ofReal p) x) (WithLp.toLp (ENNReal.ofReal p) y))
    (h_1_3 : ∃ (M : ℝ) (c c₀ β₁ β₂ A : ℕ → ℝ),
      0 < M ∧
      (∀ C₁ : ℕ, 3 ≤ C₁ →
        (2 : ℝ) ^ (-M * (C₁ : ℝ) ^ 3 * Real.logb 2 (C₁ : ℝ)) ≤ c C₁ ∧
        0 < c₀ C₁ ∧ 0 < β₁ C₁ ∧ β₁ C₁ ≤ β₂ C₁ ∧ 0 < A C₁) ∧
      ∀ (p : ℝ), 1 ≤ p →
        ∀ (C : ℝ), 1 ≤ C →
          let C₁ : ℕ := max 3 ⌈C ^ p⌉₊
          (2 : ℝ) ^ (-(81 * M) * C ^ (4 * p)) ≤
            (2 : ℝ) ^ (-(81 * M) * C ^ (3 * p) * Real.logb 2 (C ^ p + 1)) ∧
          (2 : ℝ) ^ (-(81 * M) * C ^ (3 * p) * Real.logb 2 (C ^ p + 1)) ≤ c C₁ ∧
          ∃ nSeq : ℕ → ℕ, StrictMono nSeq ∧ (∀ j : ℕ, 2 ≤ nSeq j) ∧
            ∀ j : ℕ,
              ∃ (d : ℕ) (P : Fin (nSeq j) → (Fin d → ℝ)),
                1 ≤ d ∧
                β₁ C₁ * Real.logb 2 (nSeq j : ℝ) ≤ (d : ℝ) ∧
                (d : ℝ) ≤ β₂ C₁ * Real.logb 2 (nSeq j : ℝ) ∧
                (∀ i : Fin (nSeq j), ∀ k : Fin d, P i k = 0 ∨ P i k = 1) ∧
                Function.Injective P ∧
                aspectRatio p P ≤ A C₁ ∧
                ∀ (S : Type) [Fintype S]
                  (H : SimpleGraph (Fin (nSeq j) ⊕ S))
                  (w : Sym2 (Fin (nSeq j) ⊕ S) → ℝ),
                  IsNonMetricSteinerSpanner p P C H w →
                  c₀ C₁ * (nSeq j : ℝ) ^ (1 + c C₁) ≤ (Nat.card H.edgeSet : ℝ)) :
    ∃ (M : ℝ) (c c₀ A : ℝ → ℝ),
      0 < M ∧
      (∀ C : ℝ, 1 ≤ C →
        (2 : ℝ) ^ (-M * C ^ (6 : ℕ) * Real.logb 2 (C + 1)) ≤ c C ∧ 0 < c₀ C ∧ 0 < A C) ∧
      ∀ (p : ℝ), 2 < p →
        ∀ (C : ℝ), 1 ≤ C →
          ∃ (β₁ β₂ : ℝ), 0 < β₁ ∧ β₁ ≤ β₂ ∧
            ∃ nSeq : ℕ → ℕ, StrictMono nSeq ∧ (∀ j : ℕ, 2 ≤ nSeq j) ∧
              ∀ j : ℕ,
                ∃ (d : ℕ) (P : Fin (nSeq j) → (Fin d → ℝ)),
                  1 ≤ d ∧
                  β₁ * (Real.logb 2 (nSeq j : ℝ)) ^ (p / 2) ≤ (d : ℝ) ∧
                  (d : ℝ) ≤ β₂ * (Real.logb 2 (nSeq j : ℝ)) ^ (p / 2) ∧
                  Function.Injective P ∧
                  aspectRatio p P ≤ A C ∧
                  (∀ (S : Type) [Fintype S]
                    (H : SimpleGraph (Fin (nSeq j) ⊕ S))
                    (w : Sym2 (Fin (nSeq j) ⊕ S) → ℝ),
                    IsNonMetricSteinerSpanner p P C H w →
                    c₀ C * (nSeq j : ℝ) ^ (1 + c C) ≤ (Nat.card H.edgeSet : ℝ)) ∧
                  (∀ (G : SimpleGraph (Fin (nSeq j))),
                    IsGeometricSpanner p P C G →
                    c₀ C * (nSeq j : ℝ) ^ (1 + c C) ≤ (Nat.card G.edgeSet : ℝ)) := by
  obtain ⟨M₀, c₁, c₀₁, β₁₁, β₂₁, A₁, hM₀_pos, h_params, h_main⟩ := h_1_3
  let C₁_fn : ℝ → ℕ := fun C => max 3 ⌈(2 * C) ^ (2 : ℝ)⌉₊
  let M : ℝ := 20736 * M₀
  let c : ℝ → ℝ := fun C => c₁ (C₁_fn C)
  let c₀ : ℝ → ℝ := fun C => c₀₁ (C₁_fn C)
  let A : ℝ → ℝ := fun C => 2 * A₁ (C₁_fn C)
  refine ⟨M, c, c₀, A, by dsimp [M]; positivity, ?_, ?_⟩
  · intro C hC
    have hpar := h_params (C₁_fn C) (le_max_left 3 _)
    obtain ⟨_, hc_2C, _⟩ := h_main 2 (by norm_num) (2 * C) (by linarith)
    refine ⟨?_, hpar.2.1, by dsimp [A]; linarith [hpar.2.2.2.2]⟩
    refine le_trans ?_ hc_2C
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have hpow6 : (2 * C) ^ ((3 : ℝ) * (2 : ℝ)) = 64 * C ^ (6 : ℕ) := by
      have h6 : (3 : ℝ) * (2 : ℝ) = ((6 : ℕ) : ℝ) := by norm_num
      rw [h6, Real.rpow_natCast]
      ring
    have hpow2 : (2 * C) ^ (2 : ℝ) + 1 = 4 * C ^ (2 : ℕ) + 1 := by
      have h2 : (2 : ℝ) = ((2 : ℕ) : ℝ) := by norm_num
      rw [h2, Real.rpow_natCast]
      ring
    have hlog_le : Real.logb 2 (4 * C ^ (2 : ℕ) + 1) ≤ 4 * Real.logb 2 (C + 1) := by
      have hle : 4 * C ^ (2 : ℕ) + 1 ≤ (C + 1) ^ (4 : ℕ) := by
        nlinarith [sq_nonneg C, pow_nonneg (by linarith : 0 ≤ C) 3,
          pow_nonneg (by linarith : 0 ≤ C) 4]
      have hb : Real.logb 2 (4 * C ^ (2 : ℕ) + 1) ≤ Real.logb 2 ((C + 1) ^ (4 : ℕ)) :=
        Real.logb_le_logb_of_le (by norm_num) (by positivity) hle
      have heq : Real.logb 2 ((C + 1) ^ (4 : ℕ)) = 4 * Real.logb 2 (C + 1) := by
        simp only [Real.logb, Real.log_pow]
        ring
      linarith
    rw [hpow6, hpow2]
    have hMC_nn : 0 ≤ 81 * M₀ * (64 * C ^ (6 : ℕ)) := by positivity
    have hprod := mul_le_mul_of_nonneg_left hlog_le hMC_nn
    dsimp [M]
    linarith
  · intro p hp C hC
    have hp1 : 1 ≤ p := by linarith
    have hpar := h_params (C₁_fn C) (le_max_left 3 _)
    have hβ₁₁_pos : 0 < β₁₁ (C₁_fn C) := hpar.2.2.1
    have hβ_le₁ : β₁₁ (C₁_fn C) ≤ β₂₁ (C₁_fn C) := hpar.2.2.2.1
    obtain ⟨κ₁, κ₂, hκ₁_pos, hκ_le, h_flm⟩ := flm_l2_into_lp h_lp hp
    obtain ⟨_, _, nSeq, hn_mono, hn_ge2, h_inst⟩ := h_main 2 (by norm_num) (2 * C) (by linarith)
    let β₁ : ℝ := κ₁ * (β₁₁ (C₁_fn C)) ^ (p / 2)
    let β₂ : ℝ := κ₂ * (β₂₁ (C₁_fn C)) ^ (p / 2)
    have hβ₁_pos : 0 < β₁ := by dsimp [β₁]; positivity
    have hβ_le : β₁ ≤ β₂ := by
      dsimp [β₁, β₂]
      exact mul_le_mul hκ_le
        (Real.rpow_le_rpow hβ₁₁_pos.le hβ_le₁ (by positivity))
        (by positivity) (le_trans hκ₁_pos.le hκ_le)
    refine ⟨β₁, β₂, hβ₁_pos, hβ_le, nSeq, hn_mono, hn_ge2, ?_⟩
    intro j
    obtain ⟨d₂, Q, hd₂_ge1, hd₂_lo, hd₂_hi, _hQ_bool, hQ_inj, hQ_ar, hQ_spanner⟩ := h_inst j
    obtain ⟨d, T, hd_ge1, hd_lo, hd_hi, hT_dist⟩ := h_flm d₂ hd₂_ge1
    let P : Fin (nSeq j) → (Fin d → ℝ) := fun i => T (Q i)
    have hPQ_dist : ∀ i₁ i₂ : Fin (nSeq j),
        lpDist 2 (Q i₁) (Q i₂) ≤ lpDist p (P i₁) (P i₂) ∧
        lpDist p (P i₁) (P i₂) ≤ 2 * lpDist 2 (Q i₁) (Q i₂) := by
      intro i₁ i₂
      rw [lpDist_eq_sub_zero (Q i₁) (Q i₂), lpDist_eq_sub_zero (P i₁) (P i₂)]
      have hsub : P i₁ - P i₂ = T (Q i₁ - Q i₂) := (T.map_sub (Q i₁) (Q i₂)).symm
      rw [hsub]
      exact hT_dist (Q i₁ - Q i₂)
    have hlog_nn : 0 ≤ Real.logb 2 (nSeq j : ℝ) := by
      unfold Real.logb
      have hn1 : (1 : ℝ) ≤ (nSeq j : ℝ) := by
        exact_mod_cast le_trans (by decide : 1 ≤ 2) (hn_ge2 j)
      exact div_nonneg (Real.log_nonneg hn1) (Real.log_nonneg (by norm_num))
    have hd_lo_final : β₁ * (Real.logb 2 (nSeq j : ℝ)) ^ (p / 2) ≤ (d : ℝ) := by
      have hrpow := Real.rpow_le_rpow (by positivity) hd₂_lo (by positivity : 0 ≤ p / 2)
      rw [Real.mul_rpow hβ₁₁_pos.le hlog_nn] at hrpow
      calc β₁ * (Real.logb 2 (nSeq j : ℝ)) ^ (p / 2)
          = κ₁ * ((β₁₁ (C₁_fn C)) ^ (p / 2) * (Real.logb 2 (nSeq j : ℝ)) ^ (p / 2)) := by
              dsimp [β₁]; ring
        _ ≤ κ₁ * (d₂ : ℝ) ^ (p / 2) := mul_le_mul_of_nonneg_left hrpow hκ₁_pos.le
        _ ≤ (d : ℝ) := hd_lo
    have hd_hi_final : (d : ℝ) ≤ β₂ * (Real.logb 2 (nSeq j : ℝ)) ^ (p / 2) := by
      have hβ₂₁_nn : 0 ≤ β₂₁ (C₁_fn C) := le_trans hβ₁₁_pos.le hβ_le₁
      have hrpow := Real.rpow_le_rpow (by positivity) hd₂_hi (by positivity : 0 ≤ p / 2)
      rw [Real.mul_rpow hβ₂₁_nn hlog_nn] at hrpow
      calc (d : ℝ) ≤ κ₂ * (d₂ : ℝ) ^ (p / 2) := hd_hi
        _ ≤ κ₂ * ((β₂₁ (C₁_fn C)) ^ (p / 2) * (Real.logb 2 (nSeq j : ℝ)) ^ (p / 2)) :=
            mul_le_mul_of_nonneg_left hrpow (le_trans hκ₁_pos.le hκ_le)
        _ = β₂ * (Real.logb 2 (nSeq j : ℝ)) ^ (p / 2) := by dsimp [β₂]; ring
    have hP_inj : Function.Injective P := by
      intro i₁ i₂ heq
      have : Fact (1 ≤ ENNReal.ofReal 2) := ⟨ENNReal.one_le_ofReal.mpr (by norm_num)⟩
      have : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp1⟩
      have hP0 : lpDist p (P i₁) (P i₂) = 0 := by
        rw [h_lp p hp1, heq, dist_self]
      have hQ_le0 : lpDist 2 (Q i₁) (Q i₂) ≤ 0 := by
        linarith [(hPQ_dist i₁ i₂).1]
      have hQ0 : lpDist 2 (Q i₁) (Q i₂) = 0 :=
        le_antisymm hQ_le0 (lpDist_nonneg _ _)
      rw [h_lp 2 (by norm_num), dist_eq_zero] at hQ0
      exact hQ_inj (congrArg WithLp.ofLp hQ0)
    have hP_ar : aspectRatio p P ≤ A C := by
      have : Fact (1 ≤ ENNReal.ofReal 2) := ⟨ENNReal.one_le_ofReal.mpr (by norm_num)⟩
      have hn2 := hn_ge2 j
      have hn_pos : 0 < nSeq j := by omega
      let i₀ : Fin (nSeq j) := ⟨0, by omega⟩
      let i₁ : Fin (nSeq j) := ⟨1, by omega⟩
      let offDiag : Finset (Fin (nSeq j) × Fin (nSeq j)) :=
        Finset.univ.filter (fun ij => ij.1 ≠ ij.2)
      have hne_off : offDiag.Nonempty := ⟨(i₀, i₁), by simp [offDiag, i₀, i₁]⟩
      have hmin_Q_eq : minDistinctPairwiseDist 2 Q =
          offDiag.inf' hne_off (fun ij => lpDist 2 (Q ij.1) (Q ij.2)) := by
        unfold minDistinctPairwiseDist
        dsimp only
        rw [dite_eq_left hne_off]
      have hmin_P_eq : minDistinctPairwiseDist p P =
          offDiag.inf' hne_off (fun ij => lpDist p (P ij.1) (P ij.2)) := by
        unfold minDistinctPairwiseDist
        dsimp only
        rw [dite_eq_left hne_off]
      have hmin_Q_pos : 0 < minDistinctPairwiseDist 2 Q := by
        rw [hmin_Q_eq, Finset.lt_inf'_iff]
        intro ij hij
        have hne_ij : ij.1 ≠ ij.2 := (Finset.mem_filter.mp hij).2
        have hQ_ne : WithLp.toLp (ENNReal.ofReal 2) (Q ij.1) ≠
            WithLp.toLp (ENNReal.ofReal 2) (Q ij.2) := by
          intro heq
          exact hne_ij (hQ_inj (congrArg WithLp.ofLp heq))
        rw [h_lp 2 (by norm_num)]
        exact dist_pos.mpr hQ_ne
      have hmin_le : minDistinctPairwiseDist 2 Q ≤ minDistinctPairwiseDist p P := by
        rw [hmin_P_eq, Finset.le_inf'_iff]
        intro ij hij
        calc minDistinctPairwiseDist 2 Q
            ≤ lpDist 2 (Q ij.1) (Q ij.2) := by
              rw [hmin_Q_eq]; exact Finset.inf'_le _ hij
          _ ≤ lpDist p (P ij.1) (P ij.2) := (hPQ_dist ij.1 ij.2).1
      have hmin_P_pos : 0 < minDistinctPairwiseDist p P := lt_of_lt_of_le hmin_Q_pos hmin_le
      have : Nonempty (Fin (nSeq j) × Fin (nSeq j)) := ⟨(i₀, i₀)⟩
      have hmax_le : maxPairwiseDist p P ≤ 2 * maxPairwiseDist 2 Q := by
        unfold maxPairwiseDist
        rw [dite_eq_left hn_pos, dite_eq_left hn_pos, Finset.sup'_le_iff]
        intro ij hij
        calc lpDist p (P ij.1) (P ij.2)
            ≤ 2 * lpDist 2 (Q ij.1) (Q ij.2) := (hPQ_dist ij.1 ij.2).2
          _ ≤ 2 * Finset.univ.sup' Finset.univ_nonempty
                (fun ab : Fin (nSeq j) × Fin (nSeq j) => lpDist 2 (Q ab.1) (Q ab.2)) :=
              mul_le_mul_of_nonneg_left
                (Finset.le_sup' (fun ab : Fin (nSeq j) × Fin (nSeq j) => lpDist 2 (Q ab.1) (Q
                    ab.2)) hij)
                (by norm_num)
      have hmax_P_nn : 0 ≤ maxPairwiseDist p P := by
        unfold maxPairwiseDist
        rw [dite_eq_left hn_pos]
        have hmem : (i₀, i₀) ∈ (Finset.univ : Finset (Fin (nSeq j) × Fin (nSeq j))) :=
            Finset.mem_univ _
        exact le_trans (lpDist_nonneg _ _)
          (Finset.le_sup' (fun ab : Fin (nSeq j) × Fin (nSeq j) => lpDist p (P ab.1) (P ab.2)) hmem)
      calc aspectRatio p P
          = maxPairwiseDist p P / minDistinctPairwiseDist p P := rfl
        _ ≤ (2 * maxPairwiseDist 2 Q) / minDistinctPairwiseDist 2 Q := by
            rw [div_le_div_iff₀ hmin_P_pos hmin_Q_pos]
            exact (mul_le_mul_of_nonneg_left hmin_le hmax_P_nn).trans
              (mul_le_mul_of_nonneg_right hmax_le hmin_P_pos.le)
        _ = 2 * aspectRatio 2 Q := by unfold aspectRatio; ring
        _ ≤ 2 * A₁ (C₁_fn C) := mul_le_mul_of_nonneg_left hQ_ar (by norm_num)
        _ = A C := rfl
    have hP_steiner : ∀ (S : Type) [Fintype S]
        (H : SimpleGraph (Fin (nSeq j) ⊕ S))
        (w : Sym2 (Fin (nSeq j) ⊕ S) → ℝ),
        IsNonMetricSteinerSpanner p P C H w →
        c₀ C * (nSeq j : ℝ) ^ (1 + c C) ≤ (Nat.card H.edgeSet : ℝ) := by
      intro S _ H w hSp
      have hSp_Q : IsNonMetricSteinerSpanner 2 Q (2 * C) H w := by
        refine ⟨hSp.weight_nonneg, ?_, ?_⟩
        · intro i₁ i₂
          exact le_trans (ENNReal.ofReal_le_ofReal (hPQ_dist i₁ i₂).1) (hSp.noncontracting i₁ i₂)
        · intro i₁ i₂
          refine le_trans (hSp.stretch i₁ i₂) (ENNReal.ofReal_le_ofReal ?_)
          have hhi := (hPQ_dist i₁ i₂).2
          have hmul := mul_le_mul_of_nonneg_left hhi (show 0 ≤ C by linarith only [hC])
          nlinarith only [hmul]
      exact hQ_spanner S H w hSp_Q
    refine ⟨d, P, hd_ge1, hd_lo_final, hd_hi_final, hP_inj, hP_ar, hP_steiner, ?_⟩
    intro G hGeom
    obtain ⟨H, w, hSteiner, hCard_le⟩ := geometric_spanner_to_steiner h_lp hp1 P C G hGeom
    exact le_trans (hP_steiner PEmpty H w hSteiner) hCard_le

end HighDimSteinerSpanners.Proofs.Dvoretzky
