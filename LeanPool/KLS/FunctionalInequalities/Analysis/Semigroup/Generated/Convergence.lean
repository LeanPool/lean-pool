/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.Semigroup.Generated.Smoothing
public import LeanPool.KLS.FunctionalInequalities.Analysis.Semigroup.Generated.Domain
public import LeanPool.KLS.FunctionalInequalities.Analysis.Semigroup.VonNeumann

/-!
# Strong convergence of `P_t = exp (-t T†T)` on the orthogonal complement of the kernel

For `T` closed and densely defined between real Hilbert spaces and `A = T†T`, the semigroup
`P_t = exp (-t A)` converges strongly to `0` as `t → ∞` on every vector orthogonal to `ker T`.
This is the abstract ergodicity step of Bakry–Gentil–Ledoux (2014), Section 4.8: once `ker T`
consists of the constants, centered data relax to zero.

The argument: `ker A = ker T` on the operator domain; a vector orthogonal to `range A` lies in
`ker A` (self-adjointness of `A`); hence a vector orthogonal to `ker A` lies in the closure of
`range A`; on `range A`, `P_t (A y) = A (P_t y)` has norm at most `‖y‖ / t`, and the
contraction `‖P_t‖ ≤ 1` extends the convergence to the closure.
-/

@[expose] public section

noncomputable section

open Filter Topology Set
open scoped RealInnerProductSpace LinearPMap

namespace FunctionalInequalities.Analysis.Semigroup.Generated

variable {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
  [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
  (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) (hd : Dense (T.domain : Set H₀))

omit [CompleteSpace H₁] in
include hd in
/-- On the operator domain, `A y = 0` exactly when `T y = 0`. -/
theorem adjointComp_eq_zero_iff (y : (adjointComp T).domain) :
    adjointComp T y = 0 ↔ T ⟨y, y.2.2⟩ = 0 := by
  constructor
  · intro hA
    have hnorm2 : ‖T ⟨(y : H₀), y.2.2⟩‖ ^ 2 = 0 := by
      rw [← inner_adjointComp_self hd y, hA, inner_zero_left]
    have hnorm : ‖T ⟨(y : H₀), y.2.2⟩‖ = 0 := by
      nlinarith [hnorm2]
    exact norm_eq_zero.mp hnorm
  · intro h
    refine hd.eq_zero_of_inner_left ℝ (fun z hz => ?_)
    rw [inner_adjointComp hd y hz, h, inner_zero_left]

omit [CompleteSpace H₁] in
include hd in
/-- A form-domain vector killed by `T` lies in the operator domain and is killed by `A`. -/
theorem exists_mem_adjointComp_domain_of_map_eq_zero (x : T.domain) (hx : T x = 0) :
    ∃ h : (x : H₀) ∈ (adjointComp T).domain, adjointComp T ⟨x, h⟩ = 0 := by
  have hmem : (x : H₀) ∈ (adjointComp T).domain := by
    rw [adjointComp_domain]
    refine ⟨mem_adjointCompDomain.2 ⟨x.2, ?_⟩, x.2⟩
    have hTx : T ⟨(x : H₀), x.2⟩ = T x := rfl
    rw [hTx, hx]
    exact Submodule.zero_mem _
  refine ⟨hmem, ?_⟩
  apply (adjointComp_eq_zero_iff T hd ⟨x, hmem⟩).2
  change T ⟨(x : H₀), _⟩ = 0
  exact hx

include hT hd in
/-- A vector orthogonal to the range of `A` lies in the kernel of `A` (self-adjointness). -/
theorem exists_mem_adjointComp_domain_of_inner_eq_zero (q : H₀)
    (hq : ∀ y : (adjointComp T).domain, ⟪q, adjointComp T y⟫ = 0) :
    ∃ h : q ∈ (adjointComp T).domain, adjointComp T ⟨q, h⟩ = 0 := by
  have hqdom : q ∈ (adjointComp T)†.domain := by
    rw [LinearPMap.mem_adjoint_domain_iff]
    have heq :
        (innerₛₗ ℝ q).comp (adjointComp T).toFun = 0 := by
      ext y
      simpa using hq y
    rw [heq]
    exact continuous_zero
  have hzero : (adjointComp T)† ⟨q, hqdom⟩ = 0 := by
    have h :=
      LinearPMap.adjoint_apply_eq
        (dense_adjointComp_domain T hT hd) (⟨q, hqdom⟩ : (adjointComp T)†.domain)
        (x₀ := (0 : H₀)) (by
          intro y
          simpa using (hq y).symm)
    exact h
  have hsa : (adjointComp T)† = adjointComp T :=
    (LinearPMap.isSelfAdjoint_def).1
      (isSelfAdjoint_adjointComp T hT hd)
  obtain ⟨hdom, hval⟩ := LinearPMap.ext_iff.1 hsa
  have hqdom' : q ∈ (adjointComp T).domain := by
    rw [← hdom]
    exact hqdom
  refine ⟨hqdom', ?_⟩
  have hv :
      (adjointComp T)† ⟨q, hqdom⟩ =
        adjointComp T ⟨q, hqdom'⟩ :=
    hval (x := q) (hf := hqdom) (hg := hqdom')
  rw [← hv]
  exact hzero

include hT hd in
/-- A vector orthogonal to the kernel of `A` lies in the closure of the range of `A`. -/
theorem mem_closure_range_of_inner_eq_zero (g : H₀)
    (hg : ∀ k : (adjointComp T).domain, adjointComp T k = 0 → ⟪g, (k : H₀)⟫ = 0) :
    g ∈ closure (Set.range fun y : (adjointComp T).domain => adjointComp T y) := by
  let R : Submodule ℝ H₀ := LinearMap.range (adjointComp T).toFun
  have hgorth : g ∈ Rᗮᗮ := by
    apply (Submodule.mem_orthogonal' (Rᗮ) g).2
    intro q hq
    have hq' : ∀ y : (adjointComp T).domain, ⟪q, adjointComp T y⟫ = 0 := by
      intro y
      have hy : adjointComp T y ∈ R := by
        exact ⟨y, rfl⟩
      have hyorth : ⟪q, adjointComp T y⟫ = 0 :=
        (Submodule.mem_orthogonal' R q).1 hq (adjointComp T y) hy
      exact hyorth
    obtain ⟨hdom, hzero⟩ :=
      exists_mem_adjointComp_domain_of_inner_eq_zero T hT hd q hq'
    have hzero_inner : ⟪g, q⟫ = 0 :=
      hg ⟨q, hdom⟩ hzero
    simpa [real_inner_comm] using hzero_inner
  have htop : g ∈ (R.topologicalClosure : Set H₀) := by
    rw [← Submodule.orthogonal_orthogonal_eq_closure R]
    exact hgorth
  rw [Submodule.topologicalClosure_coe] at htop
  have hR :
      (R : Set H₀) = Set.range (fun y : (adjointComp T).domain => adjointComp T y) := by
    ext x
    constructor
    · intro hx
      exact hx
    · intro hx
      exact hx
  rw [hR] at htop
  exact htop

/-- On the range of `A`, the semigroup converges strongly to `0`: `P_t (A y) → 0`. -/
theorem tendsto_apply_adjointComp (y : (adjointComp T).domain) :
    Tendsto (fun t : ℝ => apply T hT hd t (adjointComp T y)) atTop (𝓝 0) := by
  refine
    squeeze_zero_norm'
      (f := fun t : ℝ => apply T hT hd t (adjointComp T y))
      (a := fun t : ℝ => ‖(y : H₀)‖ / t) ?_ ?_
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    have hdom : apply T hT hd t (y : H₀) ∈ (adjointComp T).domain :=
      preserves_domain T hT hd y ht.le
    have hmul :
        t * ‖adjointComp T ⟨apply T hT hd t (y : H₀), hdom⟩‖ ≤ ‖(y : H₀)‖ :=
      mul_norm_adjointComp_apply_le T hT hd (y : H₀) ht hdom
    calc
      ‖apply T hT hd t (adjointComp T y)‖ =
          ‖adjointComp T ⟨apply T hT hd t (y : H₀), hdom⟩‖ := by
            rw [generator_comm T hT hd y ht.le]
      _ ≤ ‖(y : H₀)‖ / t := (le_div_iff₀ ht).2 (by
        simpa [mul_comm] using hmul)
  · simpa using
      (tendsto_const_nhds.div_atTop
        (tendsto_id : Tendsto (fun t : ℝ => t) atTop atTop))

/-- On the closure of the range of `A`, the semigroup converges strongly to `0`. -/
theorem tendsto_apply_of_mem_closure_range {g : H₀}
    (hg : g ∈ closure (Set.range fun y : (adjointComp T).domain => adjointComp T y)) :
    Tendsto (fun t : ℝ => apply T hT hd t g) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨z, hz, hdist⟩ :=
    (Metric.mem_closure_iff.1 hg) (ε / 2) (by linarith)
  obtain ⟨y, rfl⟩ := hz
  obtain ⟨N, hN⟩ :=
    (Metric.tendsto_atTop.1 (tendsto_apply_adjointComp T hT hd y))
      (ε / 2) (by linarith)
  refine ⟨max N 0, ?_⟩
  intro t ht
  have htN : N ≤ t := le_trans (le_max_left N 0) ht
  have ht0 : 0 ≤ t := le_trans (le_max_right N 0) ht
  have hdist' : ‖g - adjointComp T y‖ < ε / 2 := by
    simpa [dist_eq_norm] using hdist
  have hnorm' :
      ‖apply T hT hd t (adjointComp T y)‖ < ε / 2 := by
    simpa [dist_eq_norm] using hN t htN
  have hmap :
      apply T hT hd t g =
        apply T hT hd t (g - adjointComp T y) +
          apply T hT hd t (adjointComp T y) := by
    rw [Generated.map_sub T hT hd ht0]
    abel
  have hnorm : ‖apply T hT hd t g‖ < ε := by
    calc
      ‖apply T hT hd t g‖ =
          ‖apply T hT hd t (g - adjointComp T y) +
            apply T hT hd t (adjointComp T y)‖ := by rw [hmap]
      _ ≤ ‖apply T hT hd t (g - adjointComp T y)‖ +
            ‖apply T hT hd t (adjointComp T y)‖ := norm_add_le _ _
      _ ≤ ‖g - adjointComp T y‖ +
            ‖apply T hT hd t (adjointComp T y)‖ := by
        gcongr
        exact Generated.norm_apply_le T hT hd ht0 (g - adjointComp T y)
      _ < ε := by linarith
  simpa [dist_eq_norm] using hnorm

/-- **Strong convergence on `(ker T)ᗮ`**: if `g` is orthogonal to every `x ∈ D(T)` with `T x = 0`,
then `P_t g → 0` as `t → ∞`. -/
theorem tendsto_apply_of_inner_eq_zero (g : H₀)
    (hg : ∀ x : T.domain, T x = 0 → ⟪g, (x : H₀)⟫ = 0) :
    Tendsto (fun t : ℝ => apply T hT hd t g) atTop (𝓝 0) := by
  apply tendsto_apply_of_mem_closure_range T hT hd
  apply mem_closure_range_of_inner_eq_zero T hT hd g
  intro k hk
  apply hg ⟨(k : H₀), k.2.2⟩
  exact (adjointComp_eq_zero_iff T hd k).1 hk

end FunctionalInequalities.Analysis.Semigroup.Generated
