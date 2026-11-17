/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.Semigroup.AdjointClosure
public import LeanPool.KLS.FunctionalInequalities.Analysis.Semigroup.Generated.Domain
public import LeanPool.KLS.FunctionalInequalities.Analysis.Semigroup.Resolvent.Limit

/-!
# Form-domain invariance and energy contraction for `P_t = exp (-t T†T)`

`Generated/Domain.lean` (operator-domain invariance) keeps the **operator** domain `D(T†T)`
invariant.  This module
extends the gradient interface to the whole **form** domain `D(T)`, for `T` closed and densely
defined between real Hilbert spaces:

* `norm_map_apply_le_of_generator` (the operator-domain energy bound): `‖T (P_t f)‖ ≤ ‖T f‖` for `f
  ∈ D(T†T)`, with
  `inner_adjointComp_apply_le` its Dirichlet-form phrasing `⟪T†T (P_t f), P_t f⟫ ≤ ⟪T†T f, f⟫`;
* `exists_seq_mem_adjointComp_domain_tendsto_graph` (graph-norm density): `D(T†T)` is dense in
  `D(T)` **for the
  graph norm of `T`** — every `f ∈ D(T)` is the limit of `f_n ∈ D(T†T)` with `T f_n → T f`;
* `preserves_form_domain` (form-domain invariance): `P_t f ∈ D(T)` for every `f ∈ D(T)` and `t ≥ 0`;
* `norm_map_apply_le` (form-energy contraction): `‖T (P_t f)‖ ≤ ‖T f‖` for every `f ∈ D(T)` and `t ≥
  0`.

form-domain invariance and form-energy contraction are delivered together by
`exists_mem_domain_norm_map_apply_le`, because the
membership witness is what the norm even refers to.

## Proofs

the operator-domain energy bound.  the form identity turns the energy into the form: `‖T x‖ ² = ⟪T†T
x, x⟫` for `x ∈ D(T†T)`
(`inner_adjointComp_self`).  With operator-domain invariance's invariance and commutation, symmetry
symmetry and the
semigroup law the semigroup law,

`‖T (P_t f)‖ ² = ⟪T†T (P_t f), P_t f⟫ = ⟪P_t (T†T f), P_t f⟫ = ⟪T†T f, P_{2t} f⟫
  = ⟪T f, T (P_{2t} f)⟫ ≤ ‖T f‖ ‖T (P_{2t} f)‖`,

which is `norm_map_apply_sq_le_mul`: the energy at time `t` is controlled by the **doubled** time.
The `L²` contraction bounds all these energies at once by `‖T†T f‖ ‖f‖`
(`norm_map_apply_sq_le_mul_norm`), so `M = sup_{t ≥ 0} ‖T (P_t f)‖` is finite and satisfies
`M ² ≤ ‖T f‖ M`, i.e. `M ≤ ‖T f‖`.  No time derivative, no monotonicity theorem and no spectral
calculus is used, and the doubling step is applied to a supremum rather than iterated.

graph-norm density.  Take `f_n = J_{1/(n+1)} f`.  the resolvent domain identity puts `J_s f` in
`D(T†T)`, the quantitative resolvent bound gives `f_n → f` in `H₀`,
and `exists_delta_norm_map_resolventDomain_sub_map_lt` of `Resolvent/Limit.lean` gives
`T f_n → T f` in `H₁`.  The second convergence is the substantive one; a uniform energy bound
would not suffice.

form-domain invariance–form-energy contraction.  For `f ∈ D(T)` take `f_n` from graph-norm density.
Then `P_t f_n ∈ D(T†T) ⊆ D(T)`, and the operator-domain energy bound applied
to the differences `f_n - f_m ∈ D(T†T)` gives
`‖T (P_t f_n) - T (P_t f_m)‖ ≤ ‖T f_n - T f_m‖`, so `T (P_t f_n)` is Cauchy and converges in `H₁`;
`P_t f_n → P_t f` because `P_t` is bounded.  **Closedness of `T`** identifies the limit, giving
`P_t f ∈ D(T)` and `T (P_t f) = lim T (P_t f_n)`, whose norm is at most `lim ‖T f_n‖ = ‖T f‖`
by the operator-domain energy bound.

## Deliberately out of scope

Nothing here regularizes an arbitrary `L²` datum: positive-time membership of `P_t g` in `D(T†T)`
for general `g`, a `C/t` generator bound, classical smooth representatives, preservation of
compactly supported smooth functions, pointwise gradient estimates, gradient commutation,
`Γ`/`Γ₂` estimates, their `L¹` self-improvement, BGL, small-time BV bounds, general-law passage
and Buser's inequality are outside this module's statements. Positive-time domain regularization
is supplied separately by `Generated/Smoothing.lean`; measure-specific estimates belong to their
analytic and log-concave consumers. This is general real Hilbert space material: no measure,
no log-concavity and no KLS quantity.
-/

@[expose] public section

noncomputable section

open InnerProductSpace

open scoped RealInnerProductSpace LinearPMap

namespace FunctionalInequalities.Analysis.Semigroup.Generated

variable {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
  [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
  (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) (hd : Dense (T.domain : Set H₀))

/-! ### The approximating parameters -/

private theorem one_div_succ_pos (n : ℕ) : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity

private theorem one_div_succ_le {m n : ℕ} (h : m ≤ n) :
    (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) := by
  have hmn : ((m : ℝ) + 1) ≤ ((n : ℝ) + 1) := by
    have h' := (Nat.cast_le (α := ℝ)).mpr h
    linarith
  exact one_div_le_one_div_of_le (by positivity) hmn

/-! ### the operator-domain energy bound: energy contraction on the generator domain -/

/-- The doubling estimate: for `f ∈ D(T†T)`, `t ≥ 0` and `u = 2t`,

`‖T (P_t f)‖ ² ≤ ‖T f‖ ‖T (P_u f)‖`.

the form identity (`inner_adjointComp_self`), the operator-domain invariance commutation
`generator_comm`, symmetry symmetry and the
semigroup law the semigroup law, closed by Cauchy–Schwarz.  The membership witnesses are hypotheses
so that
`u` can be any expression equal to `t + t`. -/
theorem norm_map_apply_sq_le_mul (f : (adjointComp T).domain) {t u : ℝ} (ht : 0 ≤ t)
    (hu : u = t + t) (hft : apply T hT hd t (f : H₀) ∈ T.domain)
    (hfu : apply T hT hd u (f : H₀) ∈ T.domain) :
    ‖T ⟨apply T hT hd t (f : H₀), hft⟩‖ ^ 2 ≤
      ‖T ⟨(f : H₀), f.2.2⟩‖ * ‖T ⟨apply T hT hd u (f : H₀), hfu⟩‖ := by
  have h1 :
    ‖T ⟨apply T hT hd t (f : H₀), hft⟩‖ ^ 2 =
      ⟪adjointComp T ⟨apply T hT hd t (f : H₀), preserves_domain T hT hd f ht⟩,
        apply T hT hd t (f : H₀)⟫ :=
    (inner_adjointComp_self hd ⟨apply T hT hd t (f : H₀), preserves_domain T hT hd f ht⟩).symm
  rw [generator_comm T hT hd f ht] at h1
  have h2 :
    ⟪apply T hT hd t (adjointComp T f), apply T hT hd t (f : H₀)⟫ =
      ⟪adjointComp T f, apply T hT hd u (f : H₀)⟫ := by
    rw [symmetric T hT hd ht (adjointComp T f) (apply T hT hd t (f : H₀)), ←
      add_time T hT hd ht ht (f : H₀), ← hu]
  have h3 :
    ⟪adjointComp T f, apply T hT hd u (f : H₀)⟫ =
      ⟪T ⟨(f : H₀), f.2.2⟩, T ⟨apply T hT hd u (f : H₀), hfu⟩⟫ :=
    inner_adjointComp hd f hfu
  rw [h1, h2, h3]
  exact real_inner_le_norm _ _

/-- The energies along the orbit of `f ∈ D(T†T)` are bounded, uniformly in `t ≥ 0`:

`‖T (P_t f)‖ ² = ⟪P_t (T†T f), P_t f⟫ ≤ ‖T†T f‖ ‖f‖`,

using only the operator-domain invariance commutation and the `L²` contraction. -/
theorem norm_map_apply_sq_le_mul_norm (f : (adjointComp T).domain) {t : ℝ} (ht : 0 ≤ t)
    (hft : apply T hT hd t (f : H₀) ∈ T.domain) :
    ‖T ⟨apply T hT hd t (f : H₀), hft⟩‖ ^ 2 ≤ ‖adjointComp T f‖ * ‖(f : H₀)‖ := by
  have h1 : ‖T ⟨apply T hT hd t (f : H₀), hft⟩‖ ^ 2
      = ⟪adjointComp T ⟨apply T hT hd t (f : H₀), preserves_domain T hT hd f ht⟩,
          apply T hT hd t (f : H₀)⟫ :=
    (inner_adjointComp_self hd ⟨apply T hT hd t (f : H₀), preserves_domain T hT hd f ht⟩).symm
  rw [generator_comm T hT hd f ht] at h1
  rw [h1]
  refine le_trans (real_inner_le_norm _ _) ?_
  exact mul_le_mul (norm_apply_le T hT hd ht _) (norm_apply_le T hT hd ht _)
    (norm_nonneg _) (norm_nonneg _)

/--
**the operator-domain energy bound: the semigroup contracts the energy on the generator domain.**
For `f ∈ D(T†T)` and
`t ≥ 0`, `‖T (P_t f)‖ ≤ ‖T f‖`.

The supremum `M` of `‖T (P_t f)‖` over all `t ≥ 0` is finite by
`norm_map_apply_sq_le_mul_norm`, and `norm_map_apply_sq_le_mul` gives `y ² ≤ ‖T f‖ M` for every
`y` in that family, hence `M ² ≤ ‖T f‖ M` and `M ≤ ‖T f‖`.  Time zero is allowed. -/
theorem norm_map_apply_le_of_generator (f : (adjointComp T).domain) {t : ℝ} (ht : 0 ≤ t)
    (hft : apply T hT hd t (f : H₀) ∈ T.domain) :
    ‖T ⟨apply T hT hd t (f : H₀), hft⟩‖ ≤ ‖T ⟨(f : H₀), f.2.2⟩‖ := by
  set a := ‖T ⟨(f : H₀), f.2.2⟩‖ with hadef
  have ha0 : 0 ≤ a := norm_nonneg _
  set S : Set ℝ :=
    {y : ℝ |
      ∃ τ : ℝ,
        ∃ hτ : 0 ≤ τ,
          y = ‖T ⟨apply T hT hd τ (f : H₀), (preserves_domain T hT hd f hτ).2⟩‖} with
    hSdef
  have hmemS :
    ∀ (τ : ℝ) (hτ : 0 ≤ τ) (h : apply T hT hd τ (f : H₀) ∈ T.domain),
      ‖T ⟨apply T hT hd τ (f : H₀), h⟩‖ ∈ S :=
    fun τ hτ _ => ⟨τ, hτ, rfl⟩
  have hSnn : ∀ y ∈ S, 0 ≤ y := by
    rintro y ⟨τ, hτ, rfl⟩
    exact norm_nonneg _
  have hSbdd : BddAbove S := by
    refine ⟨‖adjointComp T f‖ * ‖(f : H₀)‖ + 1, ?_⟩
    rintro y ⟨τ, hτ, rfl⟩
    have hsq := norm_map_apply_sq_le_mul_norm T hT hd f hτ (preserves_domain T hT hd f hτ).2
    nlinarith [norm_nonneg (T ⟨apply T hT hd τ (f : H₀), (preserves_domain T hT hd f hτ).2⟩)]
  have hSne : S.Nonempty := ⟨_, hmemS t ht hft⟩
  set M := sSup S with hMdef
  have hMle : ∀ y ∈ S, y ≤ M := fun y hy => le_csSup hSbdd hy
  have hM0 : 0 ≤ M := le_trans (hSnn _ (hmemS t ht hft)) (hMle _ (hmemS t ht hft))
  have hSsq : ∀ y ∈ S, y ^ 2 ≤ a * M := by
    rintro y ⟨τ, hτ, rfl⟩
    have hdouble :=
      norm_map_apply_sq_le_mul T hT hd f hτ (by ring : 2 * τ = τ + τ)
        (preserves_domain T hT hd f hτ).2
        (preserves_domain T hT hd f (by linarith : (0 : ℝ) ≤ 2 * τ)).2
    have hnext :=
      hMle _
        (hmemS (2 * τ) (by linarith)
          (preserves_domain T hT hd f (by linarith : (0 : ℝ) ≤ 2 * τ)).2)
    nlinarith [hdouble, hnext, ha0]
  have hMsqrt : M ≤ Real.sqrt (a * M) := by
    refine csSup_le hSne fun y hy => ?_
    calc
      y = Real.sqrt (y ^ 2) := (Real.sqrt_sq (hSnn y hy)).symm
      _ ≤ Real.sqrt (a * M) := Real.sqrt_le_sqrt (hSsq y hy)
  have hMsq : M ^ 2 ≤ a * M := by
    have hsq := Real.sq_sqrt (mul_nonneg ha0 hM0)
    nlinarith [hMsqrt, hM0, Real.sqrt_nonneg (a * M)]
  have hMa : M ≤ a := by
    rcases eq_or_lt_of_le hM0 with h | h
    · rw [← h]; exact ha0
    · exact le_of_mul_le_mul_right (by nlinarith [hMsq]) h
  exact le_trans (hMle _ (hmemS t ht hft)) hMa

/-- **the operator-domain energy bound, Dirichlet-form phrasing.**  For `f ∈ D(T†T)` and `t ≥ 0`,
`⟪T†T (P_t f), P_t f⟫ ≤ ⟪T†T f, f⟫`. -/
theorem inner_adjointComp_apply_le (f : (adjointComp T).domain) {t : ℝ} (ht : 0 ≤ t) :
    ⟪adjointComp T ⟨apply T hT hd t (f : H₀), preserves_domain T hT hd f ht⟩,
        apply T hT hd t (f : H₀)⟫ ≤ ⟪adjointComp T f, (f : H₀)⟫ := by
  rw [inner_adjointComp_self hd ⟨apply T hT hd t (f : H₀), preserves_domain T hT hd f ht⟩,
    inner_adjointComp_self hd f]
  have h := norm_map_apply_le_of_generator T hT hd f ht (preserves_domain T hT hd f ht).2
  nlinarith [h, norm_nonneg (T ⟨apply T hT hd t (f : H₀), (preserves_domain T hT hd f ht).2⟩),
    norm_nonneg (T ⟨(f : H₀), f.2.2⟩)]

/-! ### graph-norm density: `D(T†T)` is dense in `D(T)` for the graph norm -/

include hT hd in
/--
**graph-norm density.**  Every `f ∈ D(T)` is approximated in the **graph norm** of `T` by elements
of
`D(T†T)`: there is a sequence `u n ∈ D(T†T)` with `u n → f` in `H₀` **and** `T (u n) → T f`
in `H₁`.

The sequence is `u n = J_{1/(n+1)} f`.  Membership is the resolvent domain identity
(`mem_adjointComp_domain_resolventDomain`), the `H₀` convergence is strong resolvent convergence,
and the `H₁`
convergence is `exists_delta_norm_map_resolventDomain_sub_map_lt`. -/
theorem exists_seq_mem_adjointComp_domain_tendsto_graph (f : T.domain) :
    ∃ (u : ℕ → H₀) (hu : ∀ n, u n ∈ (adjointComp T).domain),
      Filter.Tendsto u Filter.atTop (nhds (f : H₀)) ∧
        Filter.Tendsto (fun n => T ⟨u n, (hu n).2⟩) Filter.atTop (nhds (T f)) := by
  refine
    ⟨fun n => (resolventDomain T hT (one_div_succ_pos n) (f : H₀) : H₀), fun n =>
      mem_adjointComp_domain_resolventDomain T hT (one_div_succ_pos n) (f : H₀), ?_, ?_⟩
  · refine Metric.tendsto_atTop.mpr fun ε hε => ?_
    obtain ⟨δ, hδ, hlt⟩ := exists_delta_norm_resolventCLM_sub_lt T hT hd (f : H₀) hε
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
    refine ⟨N, fun n hn => ?_⟩
    rw [dist_eq_norm]
    exact hlt (one_div_succ_pos n) (lt_of_le_of_lt (one_div_succ_le hn) hN)
  · refine Metric.tendsto_atTop.mpr fun ε hε => ?_
    obtain ⟨δ, hδ, hlt⟩ := exists_delta_norm_map_resolventDomain_sub_map_lt T hT f hε
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
    refine ⟨N, fun n hn => ?_⟩
    rw [dist_eq_norm]
    exact hlt (one_div_succ_pos n) (lt_of_le_of_lt (one_div_succ_le hn) hN)

/-!
### Form-domain invariance and form-energy contraction
-/

/--
**form-domain invariance and form-energy contraction together.**  For every `f ∈ D(T)` and every `t
≥ 0` the semigroup value
`P_t f` lies in `D(T)`, and `‖T (P_t f)‖ ≤ ‖T f‖`.

The membership witness and the estimate are produced in one statement because the estimate
mentions the witness.  `preserves_form_domain` and `norm_map_apply_le` are the two halves. -/
theorem exists_mem_domain_norm_map_apply_le (f : T.domain) {t : ℝ} (ht : 0 ≤ t) :
    ∃ h : apply T hT hd t (f : H₀) ∈ T.domain, ‖T ⟨apply T hT hd t (f : H₀), h⟩‖ ≤ ‖T f‖ := by
  obtain ⟨u, hu, hu₀, hu₁⟩ := exists_seq_mem_adjointComp_domain_tendsto_graph T hT hd f
  have hPmem : ∀ n, apply T hT hd t (u n) ∈ (adjointComp T).domain := fun n =>
    preserves_domain T hT hd ⟨u n, hu n⟩ ht
  have hcontr : ∀ n, ‖T ⟨apply T hT hd t (u n), (hPmem n).2⟩‖ ≤ ‖T ⟨u n, (hu n).2⟩‖ := fun n =>
    norm_map_apply_le_of_generator T hT hd ⟨u n, hu n⟩ ht (hPmem n).2
  have hstep :
    ∀ n m : ℕ,
      ‖T ⟨apply T hT hd t (u n), (hPmem n).2⟩ - T ⟨apply T hT hd t (u m), (hPmem m).2⟩‖ ≤
        ‖T ⟨u n, (hu n).2⟩ - T ⟨u m, (hu m).2⟩‖ := by
    intro n m
    set g : (adjointComp T).domain := ⟨u n, hu n⟩ - ⟨u m, hu m⟩ with hgdef
    have hgval : (g : H₀) = u n - u m := rfl
    have h1 :
      T ⟨apply T hT hd t (g : H₀), (preserves_domain T hT hd g ht).2⟩ =
        T ⟨apply T hT hd t (u n), (hPmem n).2⟩ - T ⟨apply T hT hd t (u m), (hPmem m).2⟩ := by
      refine apply_sub_of_eq_sub _ _ _ ?_
      rw [hgval, map_sub T hT hd ht]
    have h2 : T ⟨(g : H₀), g.2.2⟩ = T ⟨u n, (hu n).2⟩ - T ⟨u m, (hu m).2⟩ :=
      apply_sub_of_eq_sub _ _ _ hgval
    rw [← h1, ← h2]
    exact norm_map_apply_le_of_generator T hT hd g ht (preserves_domain T hT hd g ht).2
  have hcauchy : CauchySeq fun n => T ⟨apply T hT hd t (u n), (hPmem n).2⟩ := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff'.mp hu₁.cauchySeq ε hε
    refine ⟨N, fun n hn => ?_⟩
    have h := hN n hn
    rw [dist_eq_norm] at h ⊢
    exact lt_of_le_of_lt (hstep n N) h
  obtain ⟨η, hη⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hPconv :
    Filter.Tendsto (fun n => apply T hT hd t (u n)) Filter.atTop
      (nhds (apply T hT hd t (f : H₀))) := by
    have h := ((operator T hT hd ht).continuous.tendsto ((f : H₀))).comp hu₀
    simpa [Function.comp_def] using h
  have hgraph : (apply T hT hd t (f : H₀), η) ∈ T.graph := by
    refine hT.mem_of_tendsto (hPconv.prodMk_nhds hη) (Filter.Eventually.of_forall fun n => ?_)
    exact T.mem_graph ⟨apply T hT hd t (u n), (hPmem n).2⟩
  obtain ⟨z, hz₁, hz₂⟩ := T.mem_graph_iff.mp hgraph
  have hz₁' : (z : H₀) = apply T hT hd t (f : H₀) := hz₁
  have hz₂' : T z = η := hz₂
  have hmem : apply T hT hd t (f : H₀) ∈ T.domain := by rw [← hz₁']; exact z.2
  refine ⟨hmem, ?_⟩
  have hzeq : (⟨apply T hT hd t (f : H₀), hmem⟩ : T.domain) = z := Subtype.ext hz₁'.symm
  rw [hzeq, hz₂']
  exact le_of_tendsto_of_tendsto' hη.norm hu₁.norm hcontr

/--
**form-domain invariance: the form domain is invariant.**  For `f ∈ D(T)` and `t ≥ 0`, `P_t f ∈
D(T)`.  Time
zero and the zero vector are allowed, and the datum is only assumed to be in the form domain. -/
theorem preserves_form_domain (f : T.domain) {t : ℝ} (ht : 0 ≤ t) :
    apply T hT hd t (f : H₀) ∈ T.domain := by
  obtain ⟨h, _⟩ := exists_mem_domain_norm_map_apply_le T hT hd f ht
  exact h

/--
**form-energy contraction: the semigroup contracts the energy on the whole form domain.**  For `f ∈
D(T)`,
`t ≥ 0` and any witness of `P_t f ∈ D(T)`, `‖T (P_t f)‖ ≤ ‖T f‖`.  The gradient is `T` in the
closed-operator sense; no classical representative is claimed. -/
theorem norm_map_apply_le (f : T.domain) {t : ℝ} (ht : 0 ≤ t)
    (hft : apply T hT hd t (f : H₀) ∈ T.domain) : ‖T ⟨apply T hT hd t (f : H₀), hft⟩‖ ≤ ‖T f‖ := by
  obtain ⟨_, hle⟩ := exists_mem_domain_norm_map_apply_le T hT hd f ht
  exact hle

end FunctionalInequalities.Analysis.Semigroup.Generated
