/-
Copyright (c) 2026 Carlo Perassi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carlo Perassi
-/
module

public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Monotonicity.Lemmas
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Presheaf
import Std.Tactic.BVDecide.Normalize.Prop

/-!
# A Cauchy estimate with zeros

Dividing an entire function by the zeros it has at prescribed points, and the resulting bound on a
disc, used to extend the vanishing of the auxiliary function.

From `SixExponentials/Basic/cauchy_estimate_with_zeros.lean` of `carlok/six-exponentials-lean`;
see `LeanPool.SixExponentials` for provenance.
-/

@[expose] public section

namespace SixExponentials

open Finset Metric

namespace FourExpCauchy

lemma order_sub_self (a : ℂ) : analyticOrderAt (· - a) a = 1 := by
  have := analyticOrderAt_centeredMonomial (n := 1) (z₀ := a)
  simp_all [pow_one]

lemma order_sub_of_ne {a b : ℂ} (h : b ≠ a) : analyticOrderAt (· - a) b = 0 :=
  analyticOrderAt_eq_zero.2 (Or.inr (by simp [sub_eq_zero, h]))

/-- Divide out one zero of an entire function with `dslope`. -/
lemma peel_one (F : ℂ → ℂ) (hF : Differentiable ℂ F) (a : ℂ) (ha : F a = 0) :
    Differentiable ℂ (dslope F a) ∧ ∀ z, F z = (z - a) * dslope F a z := by
  refine ⟨?_, fun z => ?_⟩
  · exact differentiableOn_univ.mp
      ((Complex.differentiableOn_dslope (s := Set.univ) (f := F) (c := a) Filter.univ_mem).2
        hF.differentiableOn)
  · have h := sub_smul_dslope F a z
    simp only [smul_eq_mul, ha, sub_zero] at h
    exact h.symm

/-- Divide out a zero of order at least `k`, keeping the orders at every other point. -/
lemma peel (a : ℂ) : ∀ (k : ℕ) (F : ℂ → ℂ), Differentiable ℂ F → (k : ℕ∞) ≤ analyticOrderAt F a →
    ∃ D : ℂ → ℂ, Differentiable ℂ D ∧ (∀ z, F z = (z - a) ^ k * D z) ∧
      ∀ b, b ≠ a → analyticOrderAt D b = analyticOrderAt F b
  | 0, F, hF, _ => ⟨F, hF, fun z => by simp, fun _ _ => rfl⟩
  | k + 1, F, hF, hk => by
    have hFa : F a = 0 := by
      have h0 : analyticOrderAt F a ≠ 0 := by
        intro h
        rw [h] at hk
        simp at hk
      exact (analyticOrderAt_ne_zero.1 h0).2
    obtain ⟨hD1, hfac⟩ := peel_one F hF a hFa
    have hFeq : F = (· - a) * dslope F a := funext fun z => hfac z
    have hord : ∀ b, analyticOrderAt F b
        = analyticOrderAt (· - a) b + analyticOrderAt (dslope F a) b := by
      intro b
      conv_lhs => rw [hFeq]
      exact analyticOrderAt_mul (analyticAt_id.sub analyticAt_const) (hD1.analyticAt b)
    have hk' : (k : ℕ∞) ≤ analyticOrderAt (dslope F a) a := by
      have h1 := hord a
      rw [order_sub_self] at h1
      rw [h1] at hk
      generalize analyticOrderAt (dslope F a) a = x at hk ⊢
      induction x using ENat.recTopCoe with
      | top => simp
      | coe x =>
        norm_cast at hk ⊢
        omega
    obtain ⟨D, hD, hfacD, hordD⟩ := peel a k (dslope F a) hD1 hk'
    refine ⟨D, hD, fun z => by rw [hfac z, hfacD z]; ring, fun b hb => ?_⟩
    rw [hordD b hb, hord b, order_sub_of_ne hb, zero_add]

/-- An entire function is divisible by the polynomial carrying its zeros on a finite set. -/
lemma factor (S : Finset ℂ) : ∀ (n : ℂ → ℕ) (F : ℂ → ℂ), Differentiable ℂ F →
    (∀ a ∈ S, (n a : ℕ∞) ≤ analyticOrderAt F a) →
    ∃ G : ℂ → ℂ, Differentiable ℂ G ∧ ∀ z, F z = (∏ a ∈ S, (z - a) ^ n a) * G z := by
  induction S using Finset.induction_on with
  | empty => intro n F hF _; exact ⟨F, hF, fun z => by simp⟩
  | insert a S haS ih =>
    intro n F hF hn
    obtain ⟨D, hD, hfac, hord⟩ := peel a (n a) F hF (hn a (mem_insert_self a S))
    obtain ⟨G, hG, hfacG⟩ := ih n D hD (fun b hb => by
      rw [hord b (fun h => haS (h ▸ hb))]
      exact hn b (mem_insert_of_mem hb))
    exact ⟨G, hG, fun z => by rw [hfac z, hfacG z, prod_insert haS]; ring⟩

end FourExpCauchy

theorem cauchy_estimate_with_zeros
    (F : ℂ → ℂ) (hF : Differentiable ℂ F) (c : ℂ) (ρ R M : ℝ) (hρ : 0 ≤ ρ) (hR : ρ + 1 < R)
    (S : Finset ℂ) (hS : ∀ z ∈ S, ‖z - c‖ ≤ ρ)
    (hM : ∀ z : ℂ, ‖z - c‖ = R → ‖F z‖ ≤ M) (s : ℕ) :
    ‖iteratedDeriv s F c‖
      ≤ (s.factorial : ℝ) * (R / (R - 1)) *
          ((ρ + 1) / (R - ρ)) ^ (∑ z ∈ S, analyticOrderNatAt F z) * M := by
  obtain ⟨G, hG, hfac⟩ := FourExpCauchy.factor S (analyticOrderNatAt F) F hF (fun a _ => by
    unfold analyticOrderNatAt
    generalize analyticOrderAt F a = x
    induction x using ENat.recTopCoe <;> simp)
  set N := ∑ z ∈ S, analyticOrderNatAt F z with hN
  have hR0 : 0 < R := by linarith
  have hRρ : 0 < R - ρ := by linarith
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM (c + R) (by simp [abs_of_pos hR0]))
  -- On the sphere of radius `R` every factor `z - a` has norm at least `R - ρ`.
  have hGsphere : ∀ z : ℂ, ‖z - c‖ = R → ‖G z‖ ≤ M / (R - ρ) ^ N := by
    intro z hz
    have hP : (R - ρ) ^ N ≤ ‖∏ a ∈ S, (z - a) ^ analyticOrderNatAt F a‖ := by
      rw [norm_prod, hN, ← prod_pow_eq_pow_sum]
      refine prod_le_prod₀ (fun _ _ => pow_nonneg hRρ.le _) (fun a ha => ?_)
      rw [norm_pow]
      apply pow_le_pow_left₀ hRρ.le
      have h1 := norm_sub_norm_le (z - c) (a - c)
      rw [show z - c - (a - c) = z - a by ring] at h1
      linarith [hS a ha]
    rw [le_div_iff₀ (pow_pos hRρ N)]
    calc ‖G z‖ * (R - ρ) ^ N
        ≤ ‖G z‖ * ‖∏ a ∈ S, (z - a) ^ analyticOrderNatAt F a‖ :=
          mul_le_mul_of_nonneg_left hP (norm_nonneg _)
      _ = ‖F z‖ := by rw [hfac z, norm_mul, mul_comm]
      _ ≤ M := hM z hz
  -- Maximum principle for `G` on the disc of radius `R`.
  have hGball : ∀ w : ℂ, ‖w - c‖ ≤ R → ‖G w‖ ≤ M / (R - ρ) ^ N := by
    intro w hw
    exact Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hG.diffContOnCl
      (fun y hy => hGsphere y (by
        rw [frontier_ball _ hR0.ne'] at hy
        simpa [mem_sphere_iff_norm] using hy))
      (by rw [closure_ball _ hR0.ne', mem_closedBall_iff_norm]; exact hw)
  -- On the unit sphere every factor `z - a` has norm at most `ρ + 1`.
  have hFsmall : ∀ z ∈ sphere c 1, ‖F z‖ ≤ ((ρ + 1) / (R - ρ)) ^ N * M := by
    intro z hz
    rw [mem_sphere_iff_norm] at hz
    have hP : ‖∏ a ∈ S, (z - a) ^ analyticOrderNatAt F a‖ ≤ (ρ + 1) ^ N := by
      rw [norm_prod, hN, ← prod_pow_eq_pow_sum]
      refine prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun a ha => ?_)
      rw [norm_pow]
      apply pow_le_pow_left₀ (norm_nonneg _)
      have h1 := norm_sub_le (z - c) (a - c)
      rw [show z - c - (a - c) = z - a by ring] at h1
      linarith [hS a ha]
    have hGz := hGball z (by rw [hz]; linarith)
    calc ‖F z‖ = ‖∏ a ∈ S, (z - a) ^ analyticOrderNatAt F a‖ * ‖G z‖ := by
          rw [hfac z, norm_mul]
      _ ≤ (ρ + 1) ^ N * (M / (R - ρ) ^ N) :=
          mul_le_mul hP hGz (norm_nonneg _) (pow_nonneg (by linarith) _)
      _ = ((ρ + 1) / (R - ρ)) ^ N * M := by rw [div_pow]; ring
  -- Cauchy's estimate on the unit circle; the factor `R / (R - 1) ≥ 1` is slack.
  have hC := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le s one_pos
    hF.diffContOnCl hFsmall
  simp only [one_pow, div_one] at hC
  have hRR : 1 ≤ R / (R - 1) := by rw [le_div_iff₀ (by linarith)]; linarith
  have hK : 0 ≤ ((ρ + 1) / (R - ρ)) ^ N * M :=
    mul_nonneg (pow_nonneg (div_nonneg (by linarith) hRρ.le) _) hM0
  have hf : (0 : ℝ) ≤ s.factorial := by positivity
  calc ‖iteratedDeriv s F c‖ ≤ s.factorial * (((ρ + 1) / (R - ρ)) ^ N * M) := hC
    _ = s.factorial * 1 * (((ρ + 1) / (R - ρ)) ^ N * M) := by ring
    _ ≤ s.factorial * (R / (R - 1)) * (((ρ + 1) / (R - ρ)) ^ N * M) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hRR hf) hK
    _ = s.factorial * (R / (R - 1)) * ((ρ + 1) / (R - ρ)) ^ N * M := by ring

end SixExponentials
