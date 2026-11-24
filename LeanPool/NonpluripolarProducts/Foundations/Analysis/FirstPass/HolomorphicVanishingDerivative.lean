/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import Mathlib.Analysis.Complex.TaylorSeries
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.HolomorphicContDiff

/-!
# A holomorphic function vanishing on a set, with nonzero differential there

Let `H` be holomorphic on an open set `U` of a complex normed space, vanishing on
`Z ⊆ U`, and not identically zero near some `w₀ ∈ Z`.  Then some holomorphic `G` on `U`
vanishes on `Z` and has a nonzero differential at some point of `Z`.

Otherwise every holomorphic function vanishing on `Z` has zero differential on `Z`, so
all iterated directional derivatives `D_v^k H` vanish on `Z`, in particular at `w₀`.
Along each complex line `t ↦ H (w₀ + t v)` inside a ball around `w₀` the one-variable
Taylor expansion (`Complex.taylorSeries_eq_on_ball`) then forces `H = 0`, so `H` vanishes
near `w₀`.
-/

@[expose] public section

open Set Filter Metric
open scoped Topology

namespace SGPT.Foundations.Analysis.FirstPass

noncomputable section

/-- Iterated directional derivatives of a holomorphic function on an open set are
holomorphic there. -/
theorem differentiableOn_iterate_fderiv_apply {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {U : Set E} (hU : IsOpen U) {H : E → ℂ} (hH : DifferentiableOn ℂ H U)
    (v : E) (k : ℕ) :
    DifferentiableOn ℂ ((fun (G : E → ℂ) (z : E) => fderiv ℂ G z v)^[k] H) U := by
  induction k with
  | zero => simpa using hH
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact differentiableOn_fderiv_apply_of_isOpen ih hU v

/-- Along the complex line `s ↦ w + s • v`, the `k`-th derivative of a holomorphic function
is the `k`-th iterated directional derivative in direction `v`. -/
theorem iteratedDeriv_comp_add_smul_eq {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {U : Set E} (hU : IsOpen U) {H : E → ℂ} (hH : DifferentiableOn ℂ H U)
    (w v : E) (k : ℕ) {t : ℂ} (ht : w + t • v ∈ U) :
    iteratedDeriv k (fun s : ℂ => H (w + s • v)) t =
      (fun (G : E → ℂ) (z : E) => fderiv ℂ G z v)^[k] H (w + t • v) := by
  induction k generalizing t with
  | zero => simp
  | succ k ih =>
    have hS : IsOpen {s : ℂ | w + s • v ∈ U} :=
      hU.preimage (by fun_prop)
    have heq : iteratedDeriv k (fun s : ℂ => H (w + s • v)) =ᶠ[𝓝 t]
        fun s => (fun (G : E → ℂ) (z : E) => fderiv ℂ G z v)^[k] H (w + s • v) :=
      Filter.eventually_of_mem (hS.mem_nhds ht) fun s hs => ih hs
    rw [iteratedDeriv_succ, heq.deriv_eq, Function.iterate_succ_apply']
    have hG := ((differentiableOn_iterate_fderiv_apply hU hH v k).differentiableAt
      (hU.mem_nhds ht)).hasFDerivAt
    have hl : HasDerivAt (fun s : ℂ => w + s • v) v t := by
      simpa using ((hasDerivAt_id t).smul_const v).const_add w
    exact (hG.comp_hasDerivAt t hl).deriv

theorem exists_fderiv_ne_zero_of_not_eventuallyEq_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {U Z : Set E} (hU : IsOpen U) (hZU : Z ⊆ U) {H : E → ℂ}
    (hH : DifferentiableOn ℂ H U) (hHZ : ∀ x ∈ Z, H x = 0) {w₀ : E} (hw₀ : w₀ ∈ Z)
    (hne : ¬ H =ᶠ[𝓝 w₀] 0) :
    ∃ G : E → ℂ, DifferentiableOn ℂ G U ∧ (∀ x ∈ Z, G x = 0) ∧
      ∃ x ∈ Z, fderiv ℂ G x ≠ 0 := by
  by_contra hcon
  push Not at hcon
  apply hne
  have hvan : ∀ (v : E) (k : ℕ) (x : E), x ∈ Z →
      (fun (G : E → ℂ) (z : E) => fderiv ℂ G z v)^[k] H x = 0 := by
    intro v k
    induction k with
    | zero => simpa using hHZ
    | succ k ih =>
      intro x hx
      rw [Function.iterate_succ_apply', hcon _ (differentiableOn_iterate_fderiv_apply hU hH v k)
        ih x hx]
      rfl
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 hU w₀ (hZU hw₀)
  filter_upwards [ball_mem_nhds w₀ hr] with z hz
  rw [Pi.zero_apply]
  rcases eq_or_ne z w₀ with rfl | hzw
  · exact hHZ z hw₀
  set v := z - w₀ with hv
  have hv0 : 0 < ‖v‖ := norm_pos_iff.2 (sub_ne_zero.2 hzw)
  have hzr : ‖v‖ < r := by simpa [dist_eq_norm] using hz
  have hball : ∀ t ∈ ball (0 : ℂ) (r / ‖v‖), w₀ + t • v ∈ U := by
    intro t ht
    apply hrU
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul]
    rw [mem_ball, dist_zero_right, lt_div_iff₀ hv0] at ht
    exact ht
  have hφ : DifferentiableOn ℂ (fun s : ℂ => H (w₀ + s • v)) (ball (0 : ℂ) (r / ‖v‖)) := by
    intro t ht
    have hd := (hH.differentiableAt (hU.mem_nhds (hball t ht)))
    exact (hd.comp t (by fun_prop)).differentiableWithinAt
  have h1 : (1 : ℂ) ∈ ball (0 : ℂ) (r / ‖v‖) := by
    rw [mem_ball, dist_zero_right, norm_one, one_lt_div hv0]
    exact hzr
  have hT := Complex.taylorSeries_eq_on_ball hφ h1
  have h0 : (0 : ℂ) ∈ ball (0 : ℂ) (r / ‖v‖) := mem_ball_self (div_pos hr hv0)
  have hk : ∀ k : ℕ, iteratedDeriv k (fun s : ℂ => H (w₀ + s • v)) 0 = 0 := fun k => by
    rw [iteratedDeriv_comp_add_smul_eq hU hH w₀ v k (hball 0 h0)]
    simpa using hvan v k w₀ hw₀
  simp only [hk, smul_zero, tsum_zero] at hT
  simpa [hv] using hT.symm

end

end SGPT.Foundations.Analysis.FirstPass
