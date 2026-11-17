/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.EhrhardGaussian.GaussianConvexity.OneCrossing
public import Mathlib.Analysis.Convex.Basic
import Mathlib.Tactic.Linarith

/-!
# All crossing-set cases under two moment cancellations

A convex positive set is either a genuine bounded interval or the function
vanishes almost everywhere. Empty, singleton and unbounded sets are included;
no crossing endpoints are postulated.
-/

@[expose] public section

open MeasureTheory Set Filter

namespace EhrhardGaussian.GaussianConvexity

/-- The nonnegative analogue of one-sign exponential cancellation. -/
theorem ae_eq_zero_of_nonneg_of_exp_integral_eq_zero {f : ℝ → ℝ} {p : ℝ}
    (hi : Integrable (fun t => Real.exp (p * t) * f t))
    (hz : ∫ t, Real.exp (p * t) * f t = 0) (hf : ∀ᵐ t ∂volume, 0 ≤ f t) :
    f =ᵐ[volume] 0 := by
  have hnonneg : ∀ᵐ t ∂volume, 0 ≤ Real.exp (p * t) * f t := by
    filter_upwards [hf] with t ht
    exact mul_nonneg (Real.exp_pos _).le ht
  have heq := (integral_eq_zero_iff_of_nonneg_ae hnonneg hi).mp hz
  filter_upwards [heq] with t ht
  exact (mul_eq_zero.mp ht).resolve_left (Real.exp_ne_zero _)

/-- An order-connected set unbounded at both ends is all of the line. -/
theorem mem_of_not_bddBelow_of_not_bddAbove {s : Set ℝ} (hs : s.OrdConnected)
    (hlo : ¬ BddBelow s) (hhi : ¬ BddAbove s) (t : ℝ) : t ∈ s := by
  obtain ⟨x, hx, hxt⟩ := not_bddBelow_iff.mp hlo t
  obtain ⟨y, hy, hty⟩ := not_bddAbove_iff.mp hhi t
  exact hs.out hx hy ⟨hxt.le, hty.le⟩

/-- A convex positive set with two cancellations is bounded above unless the function is zero a.e.
-/
theorem bddAbove_positive_of_not_ae_zero {f : ℝ → ℝ} {p q : ℝ} (hpq : p < q)
    (hc : Convex ℝ {t | 0 < f t})
    (hi : Integrable (fun t => Real.exp (p * t) * f t))
    (hj : Integrable (fun t => Real.exp (q * t) * f t))
    (hz : ∫ t, Real.exp (p * t) * f t = 0)
    (hw : ∫ t, Real.exp (q * t) * f t = 0)
    (hne : ¬ f =ᵐ[volume] 0) : BddAbove {t | 0 < f t} := by
  by_contra hhi
  have hs := convex_iff_ordConnected.mp hc
  by_cases hlo : BddBelow {t | 0 < f t}
  · have hS : {t | 0 < f t}.Nonempty := by
      obtain ⟨x, hx, _⟩ := not_bddAbove_iff.mp hhi 0
      exact ⟨x, hx⟩
    apply hne
    apply ae_eq_zero_of_one_upward_crossing (c := sInf {t | 0 < f t}) hpq hi hj hz hw
    · intro t ht
      apply le_of_not_gt
      intro hpos
      exact ht.not_ge (csInf_le hlo hpos)
    · intro t ht
      obtain ⟨x, hx, hxt⟩ := (csInf_lt_iff hlo hS).mp ht
      obtain ⟨y, hy, hty⟩ := not_bddAbove_iff.mp hhi t
      exact (hs.out hx hy ⟨hxt.le, hty.le⟩).le
  · apply hne
    apply ae_eq_zero_of_nonneg_of_exp_integral_eq_zero hi hz
    exact ae_of_all _ fun t => (mem_of_not_bddBelow_of_not_bddAbove hs hlo hhi t).le

/-- The analogous lower bound for the convex positive set. -/
theorem bddBelow_positive_of_not_ae_zero {f : ℝ → ℝ} {p q : ℝ} (hpq : p < q)
    (hc : Convex ℝ {t | 0 < f t})
    (hi : Integrable (fun t => Real.exp (p * t) * f t))
    (hj : Integrable (fun t => Real.exp (q * t) * f t))
    (hz : ∫ t, Real.exp (p * t) * f t = 0)
    (hw : ∫ t, Real.exp (q * t) * f t = 0)
    (hne : ¬ f =ᵐ[volume] 0) : BddBelow {t | 0 < f t} := by
  have hhi := bddAbove_positive_of_not_ae_zero hpq hc hi hj hz hw hne
  by_contra hlo
  have hs := convex_iff_ordConnected.mp hc
  have hS : {t | 0 < f t}.Nonempty := by
    obtain ⟨x, hx, _⟩ := not_bddBelow_iff.mp hlo 0
    exact ⟨x, hx⟩
  apply hne
  apply ae_eq_zero_of_one_downward_crossing (c := sSup {t | 0 < f t}) hpq hi hj hz hw
  · intro t ht
    obtain ⟨x, hx, hxt⟩ := not_bddBelow_iff.mp hlo t
    obtain ⟨y, hy, hty⟩ := (lt_csSup_iff hhi hS).mp ht
    exact (hs.out hx hy ⟨hxt.le, hty.le⟩).le
  · intro t ht
    apply le_of_not_gt
    intro hpos
    exact ht.not_ge (le_csSup hhi hpos)

/-- Two exponential cancellations justify finite, distinct crossing endpoints, or give zero a.e. -/
theorem ae_zero_or_two_crossings {f : ℝ → ℝ} {p q : ℝ} (hpq : p < q)
    (hc : Convex ℝ {t | 0 < f t})
    (hi : Integrable (fun t => Real.exp (p * t) * f t))
    (hj : Integrable (fun t => Real.exp (q * t) * f t))
    (hz : ∫ t, Real.exp (p * t) * f t = 0)
    (hw : ∫ t, Real.exp (q * t) * f t = 0) :
    f =ᵐ[volume] 0 ∨ ∃ a b : ℝ, a < b ∧
      (∀ t, t ∈ Ioo a b → 0 < f t) ∧
      (∀ t, t < a ∨ b < t → f t ≤ 0) := by
  by_cases hne : f =ᵐ[volume] 0
  · exact Or.inl hne
  apply Or.inr
  have hlo := bddBelow_positive_of_not_ae_zero hpq hc hi hj hz hw hne
  have hhi := bddAbove_positive_of_not_ae_zero hpq hc hi hj hz hw hne
  have hS : {t | 0 < f t}.Nonempty := by
    by_contra hempty
    apply hne
    apply ae_eq_zero_of_nonpos_of_exp_integral_eq_zero hi hz
    apply ae_of_all
    intro t
    exact le_of_not_gt (fun ht => hempty ⟨t, ht⟩)
  have hle : sInf {t | 0 < f t} ≤ sSup {t | 0 < f t} :=
    csInf_le_csSup hS hlo hhi
  have hlt : sInf {t | 0 < f t} < sSup {t | 0 < f t} := by
    apply lt_of_le_of_ne hle
    intro heq
    apply hne
    apply ae_eq_zero_of_nonpos_of_exp_integral_eq_zero hi hz
    filter_upwards [volume.ae_ne (sInf {t | 0 < f t})] with t ht
    apply le_of_not_gt
    intro hpos
    exact ht (le_antisymm ((le_csSup hhi hpos).trans_eq heq.symm) (csInf_le hlo hpos))
  refine ⟨sInf {t | 0 < f t}, sSup {t | 0 < f t}, hlt, ?_, ?_⟩
  · intro t ht
    obtain ⟨x, hx, hxt⟩ := (csInf_lt_iff hlo hS).mp ht.1
    obtain ⟨y, hy, hty⟩ := (lt_csSup_iff hhi hS).mp ht.2
    exact (convex_iff_ordConnected.mp hc).out hx hy ⟨hxt.le, hty.le⟩
  · intro t ht
    apply le_of_not_gt
    intro hpos
    rcases ht with ht | ht
    · exact ht.not_ge (csInf_le hlo hpos)
    · exact ht.not_ge (le_csSup hhi hpos)

end EhrhardGaussian.GaussianConvexity
