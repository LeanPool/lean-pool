/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.Semigroup.Generated.Convergence

/-!
# The inverse of `T†T` on the orthogonal complement of `ker T`

For a closed densely defined `T : H₀ →ₗ.[ℝ] H₁` between real Hilbert spaces and `A = T†T`, a
gap inequality `‖y‖² ≤ C ‖T y‖²` for form-domain vectors orthogonal to `ker T` makes `A` invertible
on `(ker T)ᗮ`: every `g ⊥ ker T` is `A u` for exactly one `u ⊥ ker T` in the operator domain, with
`‖u‖ ≤ C ‖g‖`, `‖T u‖² = ⟪g, u⟫` and `⟪g, u⟫ ≤ C ‖g‖²`. This is the operator-theoretic core of
Bizeul–Klartag–Lehec (arXiv:2610.05474v1), Lemma 2.1, with `C = λ⁻¹`.
-/

@[expose] public section

noncomputable section

open scoped InnerProductSpace RealInnerProductSpace

namespace FunctionalInequalities.Analysis.Semigroup.Generated

variable {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
  [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
  (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) (hd : Dense (T.domain : Set H₀))

omit [CompleteSpace H₁] in
include hd in
/-- On the operator domain, a gap inequality on `(ker T)ᗮ` gives the norm and energy bounds:
`‖u‖ ≤ C ‖A u‖`, `‖T u‖² = ⟪A u, u⟫` and `⟪A u, u⟫ ≤ C ‖A u‖²`. -/
theorem norm_le_of_gap {C : ℝ}
    (hgap : ∀ y : T.domain, (∀ k : T.domain, T k = 0 → ⟪(y : H₀), (k : H₀)⟫ = 0) →
      ‖(y : H₀)‖ ^ 2 ≤ C * ‖T y‖ ^ 2)
    (u : (adjointComp T).domain)
    (hu : ∀ k : T.domain, T k = 0 → ⟪(u : H₀), (k : H₀)⟫ = 0) :
    ‖(u : H₀)‖ ≤ C * ‖adjointComp T u‖ ∧
      ‖T ⟨(u : H₀), u.2.2⟩‖ ^ 2 = ⟪adjointComp T u, (u : H₀)⟫ ∧
      ⟪adjointComp T u, (u : H₀)⟫ ≤ C * ‖adjointComp T u‖ ^ 2 := by
    have hgap' :
        ‖(u : H₀)‖ ^ 2 ≤ C * ‖T ⟨(u : H₀), u.2.2⟩‖ ^ 2 :=
      hgap ⟨(u : H₀), u.2.2⟩ hu
    have henergy :
        ‖T ⟨(u : H₀), u.2.2⟩‖ ^ 2 =
          ⟪adjointComp T u, (u : H₀)⟫ :=
      (inner_adjointComp_self (T := T) hd u).symm
    have hcs :
        ⟪adjointComp T u, (u : H₀)⟫ ≤
          ‖adjointComp T u‖ * ‖(u : H₀)‖ :=
      real_inner_le_norm _ _
    rcases le_total 0 C with hC | hC
    · by_cases hu0 : (u : H₀) = 0
      · have hz : (⟨(u : H₀), u.2.2⟩ : T.domain) = 0 := by
          apply Subtype.ext
          exact hu0
        have hTzero : T ⟨(u : H₀), u.2.2⟩ = 0 := by
          rw [hz]
          simp
        have hAu : adjointComp T u = 0 :=
          (adjointComp_eq_zero_iff T hd u).2 hTzero
        refine ⟨?_, henergy, ?_⟩
        · rw [hu0, hAu]
          simp
        · rw [hAu, hu0]
          simp
      · have hupos : 0 < ‖(u : H₀)‖ := norm_pos_iff.mpr hu0
        have hcsC :
            C * ⟪adjointComp T u, (u : H₀)⟫ ≤
              C * (‖adjointComp T u‖ * ‖(u : H₀)‖) :=
          mul_le_mul_of_nonneg_left hcs hC
        have hnorm : ‖(u : H₀)‖ ≤ C * ‖adjointComp T u‖ := by
          by_contra hn
          have hlt : C * ‖adjointComp T u‖ < ‖(u : H₀)‖ :=
            lt_of_not_ge hn
          have hmul :
              C * ‖adjointComp T u‖ * ‖(u : H₀)‖ <
                ‖(u : H₀)‖ * ‖(u : H₀)‖ :=
            mul_lt_mul_of_pos_right hlt hupos
          nlinarith [hgap', henergy, hcsC, hmul]
        have hmul :
            ‖adjointComp T u‖ * ‖(u : H₀)‖ ≤
              ‖adjointComp T u‖ * (C * ‖adjointComp T u‖) :=
          mul_le_mul_of_nonneg_left hnorm (norm_nonneg _)
        refine ⟨hnorm, henergy, ?_⟩
        nlinarith [hcs, hmul]
    · have hTnonneg :
          0 ≤ ‖T ⟨(u : H₀), u.2.2⟩‖ ^ 2 :=
        sq_nonneg _
      have hCnonpos :
          C * ‖T ⟨(u : H₀), u.2.2⟩‖ ^ 2 ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hC hTnonneg
      have hu_norm : ‖(u : H₀)‖ ^ 2 = 0 := by
        nlinarith [hgap', hCnonpos]
      have hu0 : (u : H₀) = 0 := by
        apply norm_eq_zero.mp
        nlinarith [hu_norm]
      have hz : (⟨(u : H₀), u.2.2⟩ : T.domain) = 0 := by
        apply Subtype.ext
        exact hu0
      have hTzero : T ⟨(u : H₀), u.2.2⟩ = 0 := by
        rw [hz]
        simp
      have hAu : adjointComp T u = 0 :=
        (adjointComp_eq_zero_iff T hd u).2 hTzero
      refine ⟨?_, henergy, ?_⟩
      · rw [hu0, hAu]
        simp
      · rw [hAu, hu0]
        simp

open Filter Topology Set

omit [CompleteSpace H₁] in
include hT hd in
private theorem exists_orthogonal_ker_adjointComp_eq (y : (adjointComp T).domain) :
    ∃ v : (adjointComp T).domain,
      (∀ k : T.domain, T k = 0 → ⟪(v : H₀), (k : H₀)⟫ = 0) ∧
        adjointComp T v = adjointComp T y := by
  classical
  let K : Submodule ℝ H₀ :=
    T.graph.comap
      ((LinearMap.id : H₀ →ₗ[ℝ] H₀).prod (0 : H₀ →ₗ[ℝ] H₁))
  have hK (x : H₀) :
      x ∈ K ↔ ∃ hx : x ∈ T.domain, T ⟨x, hx⟩ = 0 := by
    change (x, (0 : H₁)) ∈ T.graph ↔ _
    rw [LinearPMap.mem_graph_iff]
    constructor
    · rintro ⟨a, ha, hTa⟩
      change (a : H₀) = x at ha
      change T a = 0 at hTa
      subst x
      exact ⟨a.2, hTa⟩
    · rintro ⟨hx, hTx⟩
      exact ⟨⟨x, hx⟩, rfl, hTx⟩
  have hKclosed : IsClosed (K : Set H₀) := by
    change IsClosed
      ((fun x : H₀ => (x, (0 : H₁))) ⁻¹' (T.graph : Set (H₀ × H₁)))
    exact hT.preimage (continuous_id.prodMk continuous_const)
  let _ : CompleteSpace K := hKclosed.completeSpace_coe
  let p : H₀ := K.starProjection (y : H₀)
  obtain ⟨hp, hTp⟩ :=
    (hK p).1 (K.starProjection_apply_mem (y : H₀))
  obtain ⟨hpA, hAp⟩ :=
    exists_mem_adjointComp_domain_of_map_eq_zero
      T hd (⟨p, hp⟩ : T.domain) hTp
  let v : (adjointComp T).domain := y - ⟨p, hpA⟩
  refine ⟨v, ?_, ?_⟩
  · intro k hk
    exact
      K.starProjection_inner_eq_zero (y : H₀) (k : H₀)
        ((hK k).2 ⟨k.2, hk⟩)
  · change adjointComp T (y - ⟨p, hpA⟩) = adjointComp T y
    rw [LinearPMap.map_sub, hAp, sub_zero]

include hT hd in
/-- Existence: under the gap inequality, every `g ⊥ ker T` is `A u` for some `u ⊥ ker T` in the
operator domain. -/
theorem exists_adjointComp_eq_of_gap {C : ℝ}
    (hgap : ∀ y : T.domain, (∀ k : T.domain, T k = 0 → ⟪(y : H₀), (k : H₀)⟫ = 0) →
      ‖(y : H₀)‖ ^ 2 ≤ C * ‖T y‖ ^ 2)
    (g : H₀) (hg : ∀ k : T.domain, T k = 0 → ⟪g, (k : H₀)⟫ = 0) :
    ∃ u : (adjointComp T).domain,
      (∀ k : T.domain, T k = 0 → ⟪(u : H₀), (k : H₀)⟫ = 0) ∧ adjointComp T u = g := by
  classical
  have hgcl :
      g ∈ closure
        (Set.range fun y : (adjointComp T).domain => adjointComp T y) := by
    apply mem_closure_range_of_inner_eq_zero T hT hd g
    intro k hk
    exact
      hg ⟨(k : H₀), k.2.2⟩
        ((adjointComp_eq_zero_iff T hd k).1 hk)
  obtain ⟨a, ha, halim⟩ := mem_closure_iff_seq_limit.1 hgcl
  have hrep (n : ℕ) :
      ∃ u : (adjointComp T).domain,
        (∀ k : T.domain, T k = 0 → ⟪(u : H₀), (k : H₀)⟫ = 0) ∧
          adjointComp T u = a n := by
    obtain ⟨y, hy⟩ := ha n
    obtain ⟨v, hv, hvA⟩ := exists_orthogonal_ker_adjointComp_eq T hT hd y
    exact ⟨v, hv, hvA.trans hy⟩
  choose u hu hAu using hrep
  have hbound (n m : ℕ) :
      ‖(u n : H₀) - (u m : H₀)‖ ≤
        max C 0 * ‖a n - a m‖ := by
    have horth : ∀ k : T.domain, T k = 0 →
        ⟪((u n - u m : (adjointComp T).domain) : H₀), (k : H₀)⟫ = 0 := by
      intro k hk
      change ⟪(u n : H₀) - (u m : H₀), (k : H₀)⟫ = 0
      rw [inner_sub_left, hu n k hk, hu m k hk, sub_self]
    have hnorm :=
      (norm_le_of_gap T hd hgap (u n - u m) horth).1
    change
      ‖(u n : H₀) - (u m : H₀)‖ ≤
        C * ‖adjointComp T (u n - u m)‖ at hnorm
    rw [LinearPMap.map_sub, hAu n, hAu m] at hnorm
    exact
      hnorm.trans
        (mul_le_mul_of_nonneg_right (le_max_left C 0) (norm_nonneg _))
  have hc : CauchySeq (fun n => (u n : H₀)) := by
    apply Metric.cauchySeq_iff.2
    intro ε hε
    have hε' : 0 < ε / (max C 0 + 1) :=
      div_pos hε (by positivity)
    obtain ⟨N, hN⟩ :=
      Metric.cauchySeq_iff.1 halim.cauchySeq
        (ε / (max C 0 + 1)) hε'
    refine ⟨N, ?_⟩
    intro n hn m hm
    have hnm : ‖a n - a m‖ < ε / (max C 0 + 1) := by
      simpa only [dist_eq_norm] using hN n hn m hm
    have hmul : ‖a n - a m‖ * (max C 0 + 1) < ε :=
      (lt_div_iff₀ (by positivity)).1 hnm
    rw [dist_eq_norm]
    have hnonneg : 0 ≤ ‖a n - a m‖ := norm_nonneg _
    linarith [hbound n m]
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hc
  have hAclosed : (adjointComp T).IsClosed :=
    (isSelfAdjoint_adjointComp T hT hd).isClosed
  have hgraph : (x, g) ∈ (adjointComp T).graph := by
    apply hAclosed.mem_of_tendsto (hx.prodMk_nhds halim)
    exact Eventually.of_forall fun n => by
      rw [← hAu n]
      exact (adjointComp T).mem_graph (u n)
  obtain ⟨v, hvx, hvg⟩ :=
    (LinearPMap.mem_graph_iff (adjointComp T)).1 hgraph
  refine ⟨v, ?_, hvg⟩
  intro k hk
  have hinner :
      Tendsto (fun n => ⟪(u n : H₀), (k : H₀)⟫)
        atTop (𝓝 ⟪x, (k : H₀)⟫) :=
    hx.inner tendsto_const_nhds
  have hzero :
      Tendsto (fun n => ⟪(u n : H₀), (k : H₀)⟫)
        atTop (𝓝 (0 : ℝ)) := by
    simpa only [hu _ k hk] using
      (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  rw [hvx]
  exact tendsto_nhds_unique hinner hzero

omit [CompleteSpace H₁] in
include hd in
/-- Uniqueness: two operator-domain vectors orthogonal to `ker T` with the same image under `A`
coincide. -/
theorem eq_of_adjointComp_eq (u v : (adjointComp T).domain)
    (hu : ∀ k : T.domain, T k = 0 → ⟪(u : H₀), (k : H₀)⟫ = 0)
    (hv : ∀ k : T.domain, T k = 0 → ⟪(v : H₀), (k : H₀)⟫ = 0)
    (huv : adjointComp T u = adjointComp T v) : (u : H₀) = v := by
    let w : (adjointComp T).domain := u - v
    have hAw : adjointComp T w = 0 := by
      change adjointComp T (u - v) = 0
      rw [LinearPMap.map_sub, huv, sub_self]
    have hTw : T ⟨(w : H₀), w.2.2⟩ = 0 :=
      (adjointComp_eq_zero_iff T hd w).mp hAw
    have hinneru : ⟪(u : H₀), (w : H₀)⟫_ℝ = 0 := by
      exact hu ⟨(w : H₀), w.2.2⟩ hTw
    have hinnerv : ⟪(v : H₀), (w : H₀)⟫_ℝ = 0 := by
      exact hv ⟨(w : H₀), w.2.2⟩ hTw
    have hww : ⟪(w : H₀), (w : H₀)⟫_ℝ = 0 := by
      change ⟪(u : H₀) - (v : H₀), (w : H₀)⟫_ℝ = 0
      rw [inner_sub_left, hinneru, hinnerv, sub_zero]
    have hwzero : (w : H₀) = 0 := inner_self_eq_zero.mp hww
    change (u : H₀) - (v : H₀) = 0 at hwzero
    exact sub_eq_zero.mp hwzero

end FunctionalInequalities.Analysis.Semigroup.Generated
