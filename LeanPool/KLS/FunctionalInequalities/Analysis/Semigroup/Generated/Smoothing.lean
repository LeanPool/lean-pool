/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.Semigroup.Generated.FormDomain
public import LeanPool.KLS.FunctionalInequalities.Analysis.Semigroup.Exponential.Dissipation

/-!
# Positive-time smoothing for `P_t = exp (-t T†T)`

`Generated/Domain.lean` (operator-domain invariance) and `Generated/FormDomain.lean` (the
operator-domain energy bound) both start from a
datum that already lies in `D(T†T)` or `D(T)`. This module removes that assumption: for `T` closed
and densely defined and **every** `g : H₀`,

* `mem_domain_apply_of_pos` / `two_mul_norm_map_apply_sq_le`: `t > 0` implies `P_t g ∈ D(T)` and
  `2 t ‖T (P_t g)‖ ² ≤ ‖g‖ ²`;
* `mem_adjointComp_domain_apply_of_pos` / `mul_norm_adjointComp_apply_le`: `t > 0` implies
  `P_t g ∈ D(T†T)` and `t ‖T†T (P_t g)‖ ≤ ‖g‖`.
* `pow_three_mul_norm_map_adjointComp_apply_sq_le`: `t³ ‖T (T†T (P_t g))‖² ≤ 4 ‖g‖²`;
* `tendsto_map_apply_of_pos` / `tendsto_map_adjointComp_apply_of_pos`: both fields converge
  under convergence of the initial data, at each fixed strictly positive time.

The constants are the ones the proof
produces: `‖T (P_t g)‖ ≤ ‖g‖ / √(2t)` and `‖T†T (P_t g)‖ ≤ ‖g‖ / t`. The sharp scalar maxima
`sup_{λ ≥ 0} λ exp (-2tλ) = 1/(2et)` and `sup_{λ ≥ 0} λ ² exp (-2tλ) = 1/(et) ²` are **not**
claimed here; `1/√(2et)` and `1/(et)` are outside the estimates proved in this module.

## Proofs

**On `D(T†T)` the estimates come from the bounded level.** `Exponential/Dissipation.lean` proves,
for a bounded symmetric `L` and `u ≥ 0` with `v = exp (-u • L) y`,
`2 u ⟪L v, v⟫ ≤ ‖y‖ ² - ‖v‖ ²` and (for `L ≥ 0`) `2 u ‖L v‖ ² ≤ ⟪L y, y⟫ - ⟪L v, v⟫`. Applied to
the Yosida approximation `L_s` and passed to the limit `s ↓ 0` along any positive null sequence,
using `L_s (exp (-t • L_s) f) = exp (-t • L_s) (L_s f)`, the strong convergence
`exists_delta_norm_yosida_sub_adjointComp_lt` and the adjoint-product identification, they become

`2 t ‖T (P_t f)‖ ² ≤ ‖f‖ ² - ‖P_t f‖ ²` and `2 t ‖T†T (P_t f)‖ ² ≤ ‖T f‖ ² - ‖T (P_t f)‖ ²`

for `f ∈ D(T†T)` (`two_mul_norm_map_apply_sq_le_sub`, `two_mul_norm_adjointComp_apply_sq_le_sub`),
after rewriting `⟪T†T (P_t f), P_t f⟫ = ‖T (P_t f)‖ ²` with the form identity and `T†T (P_t f) = P_t
(T†T f)`
with operator-domain invariance.

**Off the domain the estimates are transported by density.** Each estimate is applied to
differences, which turns it into a Cauchy estimate: from `g_n → g` with `g_n ∈ D(T†T)` the
sequence `T (P_t g_n)` is Cauchy because `2 t ‖T (P_t (g_n - g_m))‖ ² ≤ ‖g_n - g_m‖ ²`, and
`exists_mem_domain_apply_eq_of_tendsto` (closedness of `T`) identifies the limit. The same
argument with graph-norm approximation and closedness of `T†T` (self-adjoint, so closed)
upgrades the second estimate to every `f ∈ D(T)`
(`mem_adjointComp_domain_apply_of_mem_domain`). Composing the two through
`P_t = P_{t/2} P_{t/2}` gives the operator-domain statement for arbitrary data.

## Deliberately out of scope

A **classical** or smooth representative of `P_t g`, pointwise gradient bounds, gradient
commutation, `Γ`/`Γ₂` estimates for the semigroup and their `L¹` self-improvement, BGL, small-time
BV bounds, general-law passage and Buser's inequality are all still open. The generator image
is in `D(T)` with the bound above, but no smooth operator-core statement is proved. This is
general real Hilbert space material: no measure, no log-concavity and no KLS quantity.
-/

@[expose] public section

noncomputable section

open InnerProductSpace

open scoped RealInnerProductSpace LinearPMap

namespace FunctionalInequalities.Analysis.Semigroup.Generated

variable {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
  [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
  (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) (hd : Dense (T.domain : Set H₀))

/-! ### Passing the Yosida estimates to the limit -/

section YosidaLimits

variable (s : ℕ → ℝ) (hs : ∀ n, 0 < s n) (hs0 : Filter.Tendsto s Filter.atTop (nhds 0))

include hT hd hs hs0 in
/--
the adjoint-product identification along a sequence: `exp (-t • L_{s n}) g → P_t g` for any positive
null sequence `s`. -/
theorem tendsto_exp_neg_smul_yosida (g : H₀) {t : ℝ} (ht : 0 ≤ t) :
    Filter.Tendsto (fun n : ℕ => NormedSpace.exp (-t • yosida T hT (hs n)) g) Filter.atTop
      (nhds (apply T hT hd t g)) := by
  refine Metric.tendsto_atTop.mpr fun ε hε => ?_
  obtain ⟨δ, hδ, hlt⟩ := yosida_limit T hT hd ht g hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hs0 δ hδ
  refine ⟨N, fun n hn => ?_⟩
  have habs := hN n hn
  rw [Real.dist_eq, sub_zero, abs_of_pos (hs n)] at habs
  rw [dist_eq_norm]
  exact hlt (hs n) habs

include hT hd hs hs0 in
/-- Strong Yosida convergence along a sequence: `L_{s n} f → T†T f` for `f ∈ D(T†T)`. -/
theorem tendsto_yosida_apply (f : (adjointComp T).domain) :
    Filter.Tendsto (fun n : ℕ => yosida T hT (hs n) (f : H₀))
      Filter.atTop (nhds (adjointComp T f)) := by
  refine Metric.tendsto_atTop.mpr fun ε hε => ?_
  obtain ⟨δ, hδ, hlt⟩ := exists_delta_norm_yosida_sub_adjointComp_lt T hT hd f hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hs0 δ hδ
  refine ⟨N, fun n hn => ?_⟩
  have habs := hN n hn
  rw [Real.dist_eq, sub_zero, abs_of_pos (hs n)] at habs
  rw [dist_eq_norm]
  exact hlt (hs n) habs

include hT hd hs hs0 in
/-- The mixed limit `L_{s n} (exp (-t • L_{s n}) f) → P_t (T†T f)` for `f ∈ D(T†T)`.

`L_s` commutes with its own exponential (`exp_neg_smul_apply_comm`), so the sequence equals
`exp (-t • L_{s n}) (L_{s n} f)`; the contraction property absorbs `L_{s n} f - T†T f` and the
adjoint-product identification
handles the remaining `exp (-t • L_{s n}) (T†T f) - P_t (T†T f)`. -/
theorem tendsto_yosida_exp_neg_smul_apply (f : (adjointComp T).domain) {t : ℝ} (ht : 0 ≤ t) :
    Filter.Tendsto
      (fun n : ℕ => yosida T hT (hs n) (NormedSpace.exp (-t • yosida T hT (hs n)) (f : H₀)))
      Filter.atTop (nhds (apply T hT hd t (adjointComp T f))) := by
  refine Metric.tendsto_atTop.mpr fun ε hε => ?_
  obtain ⟨N₁, hN₁⟩ :=
    Metric.tendsto_atTop.mp (tendsto_yosida_apply T hT hd s hs hs0 f) (ε / 2) (by positivity)
  obtain ⟨N₂, hN₂⟩ :=
    Metric.tendsto_atTop.mp (tendsto_exp_neg_smul_yosida T hT hd s hs hs0 (adjointComp T f) ht)
      (ε / 2) (by positivity)
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  have h₁ : ‖yosida T hT (hs n) (f : H₀) - adjointComp T f‖ < ε / 2 := by
    have h := hN₁ n (le_trans (le_max_left _ _) hn)
    rwa [dist_eq_norm] at h
  have h₂ :
    ‖NormedSpace.exp (-t • yosida T hT (hs n)) (adjointComp T f) -
          apply T hT hd t (adjointComp T f)‖ <
      ε / 2 := by
    have h := hN₂ n (le_trans (le_max_right _ _) hn)
    rwa [dist_eq_norm] at h
  rw [dist_eq_norm, exp_neg_smul_apply_comm]
  have hcontr :
    ‖NormedSpace.exp (-t • yosida T hT (hs n)) (yosida T hT (hs n) (f : H₀)) -
          NormedSpace.exp (-t • yosida T hT (hs n)) (adjointComp T f)‖ ≤
      ‖yosida T hT (hs n) (f : H₀) - adjointComp T f‖ := by
    rw [← _root_.map_sub]
    exact norm_exp_neg_smul_apply_le _ (yosida_nonneg T hT (hs n)) ht _
  have htri :
    ‖NormedSpace.exp (-t • yosida T hT (hs n)) (yosida T hT (hs n) (f : H₀)) -
          apply T hT hd t (adjointComp T f)‖ ≤
      ‖NormedSpace.exp (-t • yosida T hT (hs n)) (yosida T hT (hs n) (f : H₀)) -
            NormedSpace.exp (-t • yosida T hT (hs n)) (adjointComp T f)‖ +
        ‖NormedSpace.exp (-t • yosida T hT (hs n)) (adjointComp T f) -
            apply T hT hd t (adjointComp T f)‖ :=
    norm_sub_le_add_norm_sub _ _ _
  linarith

end YosidaLimits

/-! ### The two dissipation estimates on `D(T†T)` -/

/-- **Norm-level dissipation.** For `f ∈ D(T†T)` and `t ≥ 0`,

`2 t ‖T (P_t f)‖ ² ≤ ‖f‖ ² - ‖P_t f‖ ²`.

`two_mul_inner_exp_neg_smul_le` for the Yosida approximation, passed to the limit along
`s n = 1 / (n + 1)`; the left-hand side is `2 t ⟪T†T (P_t f), P_t f⟫` by the form identity and
operator-domain invariance. -/
theorem two_mul_norm_map_apply_sq_le_sub (f : (adjointComp T).domain) {t : ℝ} (ht : 0 ≤ t)
    (hft : apply T hT hd t (f : H₀) ∈ T.domain) :
    2 * t * ‖T ⟨apply T hT hd t (f : H₀), hft⟩‖ ^ 2 ≤
      ‖(f : H₀)‖ ^ 2 - ‖apply T hT hd t (f : H₀)‖ ^ 2 := by
  have hspos : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n => by positivity
  have hs0 : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) Filter.atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hx := tendsto_exp_neg_smul_yosida T hT hd _ hspos hs0 (f : H₀) ht
  have hy := tendsto_yosida_exp_neg_smul_apply T hT hd _ hspos hs0 f ht
  have hlhs :
    Filter.Tendsto
      (fun n : ℕ =>
        2 * t *
          ⟪yosida T hT (hspos n) (NormedSpace.exp (-t • yosida T hT (hspos n)) (f : H₀)),
            NormedSpace.exp (-t • yosida T hT (hspos n)) (f : H₀)⟫)
      Filter.atTop
      (nhds (2 * t * ⟪apply T hT hd t (adjointComp T f), apply T hT hd t (f : H₀)⟫)) :=
    (hy.inner hx).const_mul _
  have hrhs :
    Filter.Tendsto
      (fun n : ℕ =>
        ‖(f : H₀)‖ ^ 2 - ‖NormedSpace.exp (-t • yosida T hT (hspos n)) (f : H₀)‖ ^ 2)
      Filter.atTop (nhds (‖(f : H₀)‖ ^ 2 - ‖apply T hT hd t (f : H₀)‖ ^ 2)) :=
    tendsto_const_nhds.sub (hx.norm.pow 2)
  have hlim :=
    le_of_tendsto_of_tendsto' hlhs hrhs fun n =>
      two_mul_inner_exp_neg_smul_le (yosida T hT (hspos n)) (yosida_symm T hT (hspos n))
        (f : H₀) ht
  have hform :
    ⟪apply T hT hd t (adjointComp T f), apply T hT hd t (f : H₀)⟫ =
      ‖T ⟨apply T hT hd t (f : H₀), hft⟩‖ ^ 2 := by
    rw [← generator_comm T hT hd f ht,
      inner_adjointComp_self hd ⟨apply T hT hd t (f : H₀), preserves_domain T hT hd f ht⟩]
  rw [hform] at hlim
  exact hlim

/-- **Form-level dissipation.** For `f ∈ D(T†T)` and `t ≥ 0`,

`2 t ‖T†T (P_t f)‖ ² ≤ ‖T f‖ ² - ‖T (P_t f)‖ ²`.

`two_mul_norm_apply_exp_neg_smul_sq_le` for the Yosida approximation, passed to the limit;
nonnegativity of `L_s` (`yosida_nonneg`) is what makes the bounded-level estimate available. -/
theorem two_mul_norm_adjointComp_apply_sq_le_sub (f : (adjointComp T).domain) {t : ℝ}
    (ht : 0 ≤ t) (hft : apply T hT hd t (f : H₀) ∈ T.domain) :
    2 * t * ‖adjointComp T ⟨apply T hT hd t (f : H₀), preserves_domain T hT hd f ht⟩‖ ^ 2
      ≤ ‖T ⟨(f : H₀), f.2.2⟩‖ ^ 2 - ‖T ⟨apply T hT hd t (f : H₀), hft⟩‖ ^ 2 := by
  have hspos : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n => by positivity
  have hs0 : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) Filter.atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hx := tendsto_exp_neg_smul_yosida T hT hd _ hspos hs0 (f : H₀) ht
  have hy := tendsto_yosida_exp_neg_smul_apply T hT hd _ hspos hs0 f ht
  have hL := tendsto_yosida_apply T hT hd _ hspos hs0 f
  have hlhs : Filter.Tendsto (fun n : ℕ => 2 * t * ‖yosida T hT (hspos n)
        (NormedSpace.exp (-t • yosida T hT (hspos n)) (f : H₀))‖ ^ 2)
      Filter.atTop (nhds (2 * t * ‖apply T hT hd t (adjointComp T f)‖ ^ 2)) :=
    ((hy.norm.pow 2).const_mul _)
  have hrhs : Filter.Tendsto (fun n : ℕ => ⟪yosida T hT (hspos n) (f : H₀), (f : H₀)⟫
        - ⟪yosida T hT (hspos n) (NormedSpace.exp (-t • yosida T hT (hspos n)) (f : H₀)),
            NormedSpace.exp (-t • yosida T hT (hspos n)) (f : H₀)⟫)
      Filter.atTop (nhds (⟪adjointComp T f, (f : H₀)⟫
        - ⟪apply T hT hd t (adjointComp T f), apply T hT hd t (f : H₀)⟫)) :=
    (hL.inner tendsto_const_nhds).sub (hy.inner hx)
  have hlim := le_of_tendsto_of_tendsto' hlhs hrhs fun n =>
    two_mul_norm_apply_exp_neg_smul_sq_le (yosida T hT (hspos n)) (yosida_symm T hT (hspos n))
      (yosida_nonneg T hT (hspos n)) (f : H₀) ht
  have hform : ⟪apply T hT hd t (adjointComp T f), apply T hT hd t (f : H₀)⟫
      = ‖T ⟨apply T hT hd t (f : H₀), hft⟩‖ ^ 2 := by
    rw [← generator_comm T hT hd f ht,
      inner_adjointComp_self hd ⟨apply T hT hd t (f : H₀), preserves_domain T hT hd f ht⟩]
  have hnorm : ‖apply T hT hd t (adjointComp T f)‖
      = ‖adjointComp T ⟨apply T hT hd t (f : H₀), preserves_domain T hT hd f ht⟩‖ := by
    rw [generator_comm T hT hd f ht]
  rw [hform, inner_adjointComp_self hd f, hnorm] at hlim
  exact hlim


/-! ### Positive-time smoothing for arbitrary data -/

/-- The arithmetic step of the two Cauchy estimates below: `2 t a ² ≤ b ²` and
`b < ε √(2t)` force `a < ε`. -/
private theorem lt_of_two_mul_sq_le {t a b ε : ℝ} (ht : 0 < t) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hε : 0 < ε) (hle : 2 * t * a ^ 2 ≤ b ^ 2) (hlt : b < ε * Real.sqrt (2 * t)) : a < ε := by
  have hsq : Real.sqrt (2 * t) ^ 2 = 2 * t := Real.sq_sqrt (by linarith)
  have hpos : 0 < ε * Real.sqrt (2 * t) := lt_of_le_of_lt hb hlt
  have hA0 : b ^ 2 < (ε * Real.sqrt (2 * t)) ^ 2 := sq_lt_sq' (by linarith) hlt
  rw [mul_pow, hsq] at hA0
  have hC : 2 * t * a ^ 2 < 2 * t * ε ^ 2 := by linarith
  have hX2 : a ^ 2 < ε ^ 2 := lt_of_mul_lt_mul_left hC (by linarith)
  nlinarith [hX2, ha, hε]

/-- **Positive-time smoothing into the form domain, with its estimate.**  For every `g : H₀` and
every `t > 0`, `P_t g ∈ D(T)` and `2 t ‖T (P_t g)‖ ² ≤ ‖g‖ ²`.

`D(T†T)` is dense, so pick `u n ∈ D(T†T)` with `u n → g`.  Applying
`two_mul_norm_map_apply_sq_le_sub` to the differences `u n - u m ∈ D(T†T)` turns the estimate into
a Cauchy estimate for `T (P_t (u n))`, whose limit closedness of `T` identifies
(`exists_mem_domain_apply_eq_of_tendsto`).  `t > 0` is needed to divide by `2t`; at `t = 0` an
arbitrary datum has no reason to lie in `D(T)`. -/
theorem exists_mem_domain_apply_of_pos (g : H₀) {t : ℝ} (ht : 0 < t) :
    ∃ h : apply T hT hd t g ∈ T.domain,
      2 * t * ‖T ⟨apply T hT hd t g, h⟩‖ ^ 2 ≤ ‖g‖ ^ 2 := by
  have hchoice : ∀ n : ℕ, ∃ b : H₀, ∃ _ : b ∈ (adjointComp T).domain,
      ‖g - b‖ < 1 / ((n : ℝ) + 1) := by
    intro n
    obtain ⟨b, hb, hdist⟩ := Metric.mem_closure_iff.mp (dense_adjointComp_domain T hT hd g)
      (1 / ((n : ℝ) + 1)) (by positivity)
    exact ⟨b, hb, by rwa [dist_eq_norm] at hdist⟩
  choose u hu hulim using hchoice
  have hug : Filter.Tendsto u Filter.atTop (nhds g) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
      tendsto_one_div_add_atTop_nhds_zero_nat
    rw [norm_sub_rev]
    exact (hulim n).le
  have hPA : ∀ n, apply T hT hd t (u n) ∈ (adjointComp T).domain := fun n =>
    preserves_domain T hT hd ⟨u n, hu n⟩ ht.le
  have hPT : ∀ n, apply T hT hd t (u n) ∈ T.domain := fun n => (hPA n).2
  have hbound : ∀ n, 2 * t * ‖T ⟨apply T hT hd t (u n), hPT n⟩‖ ^ 2 ≤ ‖u n‖ ^ 2 := by
    intro n
    have h := two_mul_norm_map_apply_sq_le_sub T hT hd ⟨u n, hu n⟩ ht.le (hPT n)
    have h0 : (0 : ℝ) ≤ ‖apply T hT hd t (u n)‖ ^ 2 := sq_nonneg _
    linarith
  have hdiff : ∀ n m : ℕ,
      2 * t * ‖T ⟨apply T hT hd t (u n), hPT n⟩ - T ⟨apply T hT hd t (u m), hPT m⟩‖ ^ 2
        ≤ ‖u n - u m‖ ^ 2 := by
    intro n m
    set w : (adjointComp T).domain := ⟨u n, hu n⟩ - ⟨u m, hu m⟩ with hw
    have hwval : (w : H₀) = u n - u m := rfl
    have hsplit : T ⟨apply T hT hd t (w : H₀), (preserves_domain T hT hd w ht.le).2⟩
        = T ⟨apply T hT hd t (u n), hPT n⟩ - T ⟨apply T hT hd t (u m), hPT m⟩ := by
      refine apply_sub_of_eq_sub _ _ _ ?_
      rw [hwval, map_sub T hT hd ht.le]
    have h := two_mul_norm_map_apply_sq_le_sub T hT hd w ht.le
      (preserves_domain T hT hd w ht.le).2
    rw [hsplit, hwval] at h
    have h0 : (0 : ℝ) ≤ ‖apply T hT hd t (u n - u m)‖ ^ 2 := sq_nonneg _
    linarith
  have hcauchy : CauchySeq fun n => T ⟨apply T hT hd t (u n), hPT n⟩ := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff'.mp hug.cauchySeq (ε * Real.sqrt (2 * t))
      (by positivity)
    refine ⟨N, fun n hn => ?_⟩
    have h1 := hN n hn
    rw [dist_eq_norm] at h1 ⊢
    exact lt_of_two_mul_sq_le ht (norm_nonneg _) (norm_nonneg _) hε (hdiff n N) h1
  obtain ⟨η, hη⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hPconv : Filter.Tendsto (fun n => apply T hT hd t (u n)) Filter.atTop
      (nhds (apply T hT hd t g)) := by
    have h := ((operator T hT hd ht.le).continuous.tendsto g).comp hug
    simpa [Function.comp_def] using h
  obtain ⟨hmem, heq⟩ := exists_mem_domain_apply_eq_of_tendsto hT hPT hPconv hη
  refine ⟨hmem, ?_⟩
  rw [heq]
  exact le_of_tendsto_of_tendsto' ((hη.norm.pow 2).const_mul (2 * t)) (hug.norm.pow 2) hbound

/-- **Positive-time smoothing into the form domain.**  For every `g : H₀` and `t > 0`,
`P_t g ∈ D(T)`. -/
theorem mem_domain_apply_of_pos (g : H₀) {t : ℝ} (ht : 0 < t) :
    apply T hT hd t g ∈ T.domain := by
  obtain ⟨h, _⟩ := exists_mem_domain_apply_of_pos T hT hd g ht
  exact h

/-- The gradient bound behind `mem_domain_apply_of_pos`: `2 t ‖T (P_t g)‖ ² ≤ ‖g‖ ²`, that is
`‖T (P_t g)‖ ≤ ‖g‖ / √(2t)`, for arbitrary `g : H₀` and `t > 0`.  The sharp constant
`1 / √(2 e t)` is not claimed. -/
theorem two_mul_norm_map_apply_sq_le (g : H₀) {t : ℝ} (ht : 0 < t)
    (h : apply T hT hd t g ∈ T.domain) :
    2 * t * ‖T ⟨apply T hT hd t g, h⟩‖ ^ 2 ≤ ‖g‖ ^ 2 := by
  obtain ⟨_, hle⟩ := exists_mem_domain_apply_of_pos T hT hd g ht
  exact hle

/-- **Form-domain data enter the generator domain at positive times**, with the estimate
`2 t ‖T†T (P_t f)‖ ² ≤ ‖T f‖ ²`.

Same transport one level up: graph-norm density supplies `u n ∈ D(T†T)` with `u n → f` **and** `T (u
n) → T f`,
`two_mul_norm_adjointComp_apply_sq_le_sub` applied to differences makes `T†T (P_t (u n))` Cauchy,
and `T†T` is self-adjoint, hence closed, so it absorbs the limit. -/
theorem exists_mem_adjointComp_domain_apply_of_mem_domain (f : T.domain) {t : ℝ} (ht : 0 < t) :
    ∃ h : apply T hT hd t (f : H₀) ∈ (adjointComp T).domain,
      2 * t * ‖adjointComp T ⟨apply T hT hd t (f : H₀), h⟩‖ ^ 2 ≤ ‖T f‖ ^ 2 := by
  obtain ⟨u, hu, hu₀, hu₁⟩ := exists_seq_mem_adjointComp_domain_tendsto_graph T hT hd f
  have hAclosed : (adjointComp T).IsClosed := (isSelfAdjoint_adjointComp T hT hd).isClosed
  have hPA : ∀ n, apply T hT hd t (u n) ∈ (adjointComp T).domain := fun n =>
    preserves_domain T hT hd ⟨u n, hu n⟩ ht.le
  have hbound :
    ∀ n, 2 * t * ‖adjointComp T ⟨apply T hT hd t (u n), hPA n⟩‖ ^ 2 ≤ ‖T ⟨u n, (hu n).2⟩‖ ^ 2 := by
    intro n
    have h := two_mul_norm_adjointComp_apply_sq_le_sub T hT hd ⟨u n, hu n⟩ ht.le (hPA n).2
    have h0 : (0 : ℝ) ≤ ‖T ⟨apply T hT hd t (u n), (hPA n).2⟩‖ ^ 2 := sq_nonneg _
    linarith
  have hdiff :
    ∀ n m : ℕ,
      2 * t *
          ‖adjointComp T ⟨apply T hT hd t (u n), hPA n⟩ -
                adjointComp T ⟨apply T hT hd t (u m), hPA m⟩‖ ^
            2 ≤
        ‖T ⟨u n, (hu n).2⟩ - T ⟨u m, (hu m).2⟩‖ ^ 2 := by
    intro n m
    set w : (adjointComp T).domain := ⟨u n, hu n⟩ - ⟨u m, hu m⟩ with hw
    have hwval : (w : H₀) = u n - u m := rfl
    have hA :
      adjointComp T ⟨apply T hT hd t (w : H₀), preserves_domain T hT hd w ht.le⟩ =
        adjointComp T ⟨apply T hT hd t (u n), hPA n⟩ -
          adjointComp T ⟨apply T hT hd t (u m), hPA m⟩ := by
      refine apply_sub_of_eq_sub _ _ _ ?_
      rw [hwval, map_sub T hT hd ht.le]
    have hTw : T ⟨(w : H₀), w.2.2⟩ = T ⟨u n, (hu n).2⟩ - T ⟨u m, (hu m).2⟩ :=
      apply_sub_of_eq_sub _ _ _ hwval
    have h :=
      two_mul_norm_adjointComp_apply_sq_le_sub T hT hd w ht.le
        (preserves_domain T hT hd w ht.le).2
    rw [hA, hTw] at h
    have h0 :
      (0 : ℝ) ≤ ‖T ⟨apply T hT hd t (w : H₀), (preserves_domain T hT hd w ht.le).2⟩‖ ^ 2 :=
      sq_nonneg _
    linarith
  have hcauchy : CauchySeq fun n => adjointComp T ⟨apply T hT hd t (u n), hPA n⟩ := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    obtain ⟨N, hN⟩ :=
      Metric.cauchySeq_iff'.mp hu₁.cauchySeq (ε * Real.sqrt (2 * t)) (by positivity)
    refine ⟨N, fun n hn => ?_⟩
    have h1 := hN n hn
    rw [dist_eq_norm] at h1 ⊢
    exact lt_of_two_mul_sq_le ht (norm_nonneg _) (norm_nonneg _) hε (hdiff n N) h1
  obtain ⟨ζ, hζ⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hPconv :
    Filter.Tendsto (fun n => apply T hT hd t (u n)) Filter.atTop
      (nhds (apply T hT hd t (f : H₀))) := by
    have h := ((operator T hT hd ht.le).continuous.tendsto ((f : H₀))).comp hu₀
    simpa [Function.comp_def] using h
  obtain ⟨hmem, heq⟩ := exists_mem_domain_apply_eq_of_tendsto hAclosed hPA hPconv hζ
  refine ⟨hmem, ?_⟩
  rw [heq]
  exact le_of_tendsto_of_tendsto' ((hζ.norm.pow 2).const_mul (2 * t)) (hu₁.norm.pow 2) hbound

/-- **Positive-time smoothing into the generator domain, with its estimate.**  For every
`g : H₀` and `t > 0`, `P_t g ∈ D(T†T)` and `t ‖T†T (P_t g)‖ ≤ ‖g‖`.

Compose the two previous statements through `P_t = P_{t/2} P_{t/2}`: the first sends `g` into
`D(T)` with `(t/2)`-gradient bound `t ‖T (P_{t/2} g)‖ ² ≤ ‖g‖ ²`, the second sends that value into
`D(T†T)` with `t ‖T†T (P_t g)‖ ² ≤ ‖T (P_{t/2} g)‖ ²`.  Multiplying the two gives
`t ² ‖T†T (P_t g)‖ ² ≤ ‖g‖ ²`.  The constant `1/t` is what this composition produces; the sharp
`1/(e t)` is not claimed. -/
theorem exists_mem_adjointComp_domain_apply_of_pos (g : H₀) {t : ℝ} (ht : 0 < t) :
    ∃ h : apply T hT hd t g ∈ (adjointComp T).domain,
      t * ‖adjointComp T ⟨apply T hT hd t g, h⟩‖ ≤ ‖g‖ := by
  have hhalf : (0 : ℝ) < t / 2 := by linarith
  have hf : apply T hT hd (t / 2) g ∈ T.domain := mem_domain_apply_of_pos T hT hd g hhalf
  have hgrad := two_mul_norm_map_apply_sq_le T hT hd g hhalf hf
  obtain ⟨hmem2, hb⟩ := exists_mem_adjointComp_domain_apply_of_mem_domain T hT hd
    ⟨apply T hT hd (t / 2) g, hf⟩ hhalf
  have heq : apply T hT hd (t / 2) (apply T hT hd (t / 2) g) = apply T hT hd t g := by
    rw [← add_time T hT hd hhalf.le hhalf.le]
    norm_num
  have hmem : apply T hT hd t g ∈ (adjointComp T).domain := heq ▸ hmem2
  refine ⟨hmem, ?_⟩
  have hsub : (⟨apply T hT hd (t / 2) (apply T hT hd (t / 2) g), hmem2⟩ :
      (adjointComp T).domain) = ⟨apply T hT hd t g, hmem⟩ := Subtype.ext heq
  rw [hsub] at hb
  nlinarith [hb, hgrad, norm_nonneg (adjointComp T ⟨apply T hT hd t g, hmem⟩), norm_nonneg g,
    sq_nonneg (t * ‖adjointComp T ⟨apply T hT hd t g, hmem⟩‖ - ‖g‖)]

/-- **Positive-time smoothing into the generator domain.**  For every `g : H₀` and `t > 0`,
`P_t g ∈ D(T†T)`. -/
theorem mem_adjointComp_domain_apply_of_pos (g : H₀) {t : ℝ} (ht : 0 < t) :
    apply T hT hd t g ∈ (adjointComp T).domain := by
  obtain ⟨h, _⟩ := exists_mem_adjointComp_domain_apply_of_pos T hT hd g ht
  exact h

/-- The generator bound behind `mem_adjointComp_domain_apply_of_pos`:
`t ‖T†T (P_t g)‖ ≤ ‖g‖` for arbitrary `g : H₀` and `t > 0`.  The sharp constant `1/(e t)` is not
claimed. -/
theorem mul_norm_adjointComp_apply_le (g : H₀) {t : ℝ} (ht : 0 < t)
    (h : apply T hT hd t g ∈ (adjointComp T).domain) :
    t * ‖adjointComp T ⟨apply T hT hd t g, h⟩‖ ≤ ‖g‖ := by
  obtain ⟨_, hle⟩ := exists_mem_adjointComp_domain_apply_of_pos T hT hd g ht
  exact hle

/-- **Second-order positive-time regularity.**  For every `g : H₀` and every `t > 0`, the
generator image `T†T (P_t g)` again lies in the **form** domain `D(T)`.

Split the time, `P_t = P_{t/2} P_{t/2}`.  The inner half puts `g` in `D(T†T)`
(`mem_adjointComp_domain_apply_of_pos`), so
commutation gives `T†T (P_t g) = P_{t/2} (T†T (P_{t/2} g))`, and the outer half sends that
`H₀`-vector into `D(T)` (`mem_domain_apply_of_pos`).  Nothing beyond these two statements and
the generator commutation `generator_comm` is used; in
particular no classical representative and no second application of the adjoint. -/
theorem mem_domain_adjointComp_apply_of_pos (g : H₀) {t : ℝ} (ht : 0 < t)
    (h : apply T hT hd t g ∈ (adjointComp T).domain) :
    (adjointComp T ⟨apply T hT hd t g, h⟩ : H₀) ∈ T.domain := by
  have hhalf : (0 : ℝ) < t / 2 := by linarith
  have hmem2 : apply T hT hd (t / 2) g ∈ (adjointComp T).domain :=
    mem_adjointComp_domain_apply_of_pos T hT hd g hhalf
  have heq : apply T hT hd (t / 2) (apply T hT hd (t / 2) g) = apply T hT hd t g := by
    rw [← add_time T hT hd hhalf.le hhalf.le]
    norm_num
  have hsub : (⟨apply T hT hd (t / 2) (apply T hT hd (t / 2) g),
        preserves_domain T hT hd ⟨_, hmem2⟩ hhalf.le⟩ : (adjointComp T).domain) =
      ⟨apply T hT hd t g, h⟩ := Subtype.ext heq
  rw [← hsub, generator_comm T hT hd ⟨_, hmem2⟩ hhalf.le]
  exact mem_domain_apply_of_pos T hT hd _ hhalf

/-- A quantitative bound on the second field: `t³ ‖T A P_t g‖² ≤ 4 ‖g‖²`.
This uses positive-time smoothing and generator commutation, not a pointwise gradient
estimate or a smooth representative. The constant is not claimed sharp. -/
theorem pow_three_mul_norm_map_adjointComp_apply_sq_le (g : H₀) {t : ℝ} (ht : 0 < t)
    (h : apply T hT hd t g ∈ (adjointComp T).domain)
    (hA : (adjointComp T ⟨apply T hT hd t g, h⟩ : H₀) ∈ T.domain) :
    t ^ 3 * ‖T ⟨adjointComp T ⟨apply T hT hd t g, h⟩, hA⟩‖ ^ 2 ≤ 4 * ‖g‖ ^ 2 := by
  have hh : 0 < t / 2 := by positivity
  let f : (adjointComp T).domain :=
    ⟨apply T hT hd (t / 2) g, mem_adjointComp_domain_apply_of_pos T hT hd g hh⟩
  have heq : apply T hT hd (t / 2) (f : H₀) = apply T hT hd t g := by
    dsimp only [f]
    rw [← add_time T hT hd hh.le hh.le]
    norm_num
  have hsub : (⟨apply T hT hd (t / 2) (f : H₀),
      preserves_domain T hT hd f hh.le⟩ : (adjointComp T).domain) =
      ⟨apply T hT hd t g, h⟩ := Subtype.ext heq
  have hcomm : adjointComp T ⟨apply T hT hd t g, h⟩ =
      apply T hT hd (t / 2) (adjointComp T f) := by
    rw [← hsub, generator_comm T hT hd f hh.le]
  have hgrad := two_mul_norm_map_apply_sq_le T hT hd (adjointComp T f) hh
    (mem_domain_apply_of_pos T hT hd (adjointComp T f) hh)
  have hfield : (⟨apply T hT hd (t / 2) (adjointComp T f),
      mem_domain_apply_of_pos T hT hd (adjointComp T f) hh⟩ : T.domain) =
      ⟨adjointComp T ⟨apply T hT hd t g, h⟩, hA⟩ := Subtype.ext hcomm.symm
  rw [hfield] at hgrad
  have hgen := mul_norm_adjointComp_apply_le T hT hd g hh f.property
  change t / 2 * ‖adjointComp T f‖ ≤ ‖g‖ at hgen
  have hsq := sq_le_sq₀ (by positivity : 0 ≤ t / 2 * ‖adjointComp T f‖)
    (norm_nonneg g)
  have hscaled := mul_le_mul_of_nonneg_left hgrad (sq_nonneg t)
  nlinarith [hsq.mpr hgen]

/-- At a fixed positive time the closed-gradient field depends continuously on the initial
Hilbert-space datum. No regularity of the approximating data is required. -/
theorem tendsto_map_apply_of_pos {g : ℕ → H₀} {g₀ : H₀}
    (hg : Filter.Tendsto g Filter.atTop (nhds g₀)) {t : ℝ} (ht : 0 < t) :
    Filter.Tendsto (fun n => T ⟨apply T hT hd t (g n),
      mem_domain_apply_of_pos T hT hd (g n) ht⟩) Filter.atTop
      (nhds (T ⟨apply T hT hd t g₀, mem_domain_apply_of_pos T hT hd g₀ ht⟩)) := by
  rw [Metric.tendsto_atTop] at hg ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := hg (ε * Real.sqrt (2 * t)) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have hb := two_mul_norm_map_apply_sq_le T hT hd (g n - g₀) ht
    (mem_domain_apply_of_pos T hT hd (g n - g₀) ht)
  rw [apply_sub_of_eq_sub (mem_domain_apply_of_pos T hT hd (g n) ht)
    (mem_domain_apply_of_pos T hT hd g₀ ht) _ (map_sub T hT hd ht.le _ _)] at hb
  rw [dist_eq_norm]
  exact lt_of_two_mul_sq_le ht (norm_nonneg _) (norm_nonneg _) hε hb
    (by simpa [dist_eq_norm] using hN n hn)

/-- At a fixed positive time the second field `T A P_t g` depends continuously on arbitrary
initial data. This does not make `P_t g` a compactly supported smooth datum. -/
theorem tendsto_map_adjointComp_apply_of_pos {g : ℕ → H₀} {g₀ : H₀}
    (hg : Filter.Tendsto g Filter.atTop (nhds g₀)) {t : ℝ} (ht : 0 < t) :
    Filter.Tendsto (fun n => T ⟨adjointComp T ⟨apply T hT hd t (g n),
      mem_adjointComp_domain_apply_of_pos T hT hd (g n) ht⟩,
      mem_domain_adjointComp_apply_of_pos T hT hd (g n) ht _⟩) Filter.atTop
      (nhds (T ⟨adjointComp T ⟨apply T hT hd t g₀,
        mem_adjointComp_domain_apply_of_pos T hT hd g₀ ht⟩,
        mem_domain_adjointComp_apply_of_pos T hT hd g₀ ht _⟩)) := by
  rw [Metric.tendsto_atTop] at hg ⊢
  intro ε hε
  have hc : 0 < t ^ 3 / 8 := by positivity
  obtain ⟨N, hN⟩ := hg (ε * Real.sqrt (2 * (t ^ 3 / 8))) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have hdiff := apply_sub_of_eq_sub
    (mem_adjointComp_domain_apply_of_pos T hT hd (g n) ht)
    (mem_adjointComp_domain_apply_of_pos T hT hd g₀ ht)
    (mem_adjointComp_domain_apply_of_pos T hT hd (g n - g₀) ht)
    (map_sub T hT hd ht.le (g n) g₀)
  have hb := pow_three_mul_norm_map_adjointComp_apply_sq_le T hT hd (g n - g₀) ht
    (mem_adjointComp_domain_apply_of_pos T hT hd (g n - g₀) ht)
    (mem_domain_adjointComp_apply_of_pos T hT hd (g n - g₀) ht _)
  rw [apply_sub_of_eq_sub (mem_domain_adjointComp_apply_of_pos T hT hd (g n) ht _)
    (mem_domain_adjointComp_apply_of_pos T hT hd g₀ ht _) _ hdiff] at hb
  rw [dist_eq_norm]
  apply lt_of_two_mul_sq_le hc (norm_nonneg _) (norm_nonneg (g n - g₀)) hε
  · nlinarith [hb]
  · simpa [dist_eq_norm] using hN n hn

end FunctionalInequalities.Analysis.Semigroup.Generated
