/-
Copyright (c) 2026 Qian Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qian Tang
-/
module
public import LeanPool.Zeta32.Arith.Sum.PNT.PrimeThetaInterval
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Zeta32 — Arith — Sum — PNT — PrimeWeightedAbel. -/

-- adapted from
-- dtq1997/li2-half-irrationality@d5d8206:Li2Unified/Modular/Base/PrimeWeightedAbel.lean
-- (namespace Li2 -> Zeta32.ArithSum, imports renamed; proof and style updated for Lean Pool)

@[expose] public section

open Finset Filter Topology MeasureTheory Set Real Asymptotics
namespace Zeta32.ArithSum.PrimeSums
noncomputable section

/-- Sum of prime logarithms weighted by their indices over `(a, b]`. -/
def wsum (a b : ℝ) : ℝ :=
  ∑ k ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, (k : ℝ)*cPrime k

lemma theta_eq_sum_Icc_cPrime (t : ℝ) :
    Chebyshev.theta t = ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, cPrime k := by
  rw [Chebyshev.theta_eq_sum_Icc, Finset.sum_filter]
  rfl

lemma wsum_eq {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    wsum a b = b*Chebyshev.theta b-a*Chebyshev.theta a-
      ∫ t in Set.Ioc a b, Chebyshev.theta t := by
  unfold wsum
  have hd : deriv (fun t : ℝ => t) = fun _ => 1 := by funext t; simp
  have h := sum_mul_eq_sub_sub_integral_mul cPrime (f := fun t : ℝ => t) ha hab
    (fun t _ => differentiableAt_id) (by
      rw [hd]
      exact integrableOn_const measure_Icc_lt_top.ne)
  simp only [hd, one_mul] at h
  rw [h, ← theta_eq_sum_Icc_cPrime, ← theta_eq_sum_Icc_cPrime]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioc fun t _ => ?_
  exact (theta_eq_sum_Icc_cPrime t).symm

lemma theta_eventually_close {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ y : ℝ in atTop, |Chebyshev.theta y-y| ≤ ε*y := by
  have h := Zeta32.ArithSum.PNT.theta_isEquivalent_id
  rw [IsEquivalent, IsLittleO] at h
  have h2 := h hε
  rw [IsBigOWith] at h2
  filter_upwards [h2, eventually_ge_atTop (0 : ℝ)] with y hy hy0
  simp only [Pi.sub_apply, id, Real.norm_eq_abs, abs_of_nonneg hy0] at hy
  exact hy

lemma integral_theta_bounds {a b ε : ℝ} (hab : a ≤ b)
    (h : ∀ y ∈ Set.Icc a b, |Chebyshev.theta y - y| ≤ ε * y) :
    |(∫ t in Set.Ioc a b, Chebyshev.theta t)-(b^2-a^2)/2| ≤ ε*(b^2-a^2)/2 := by
  have hint : IntegrableOn Chebyshev.theta (Set.Ioc a b) :=
    (Chebyshev.theta_mono.intervalIntegrable (μ := volume) (a := a) (b := b)).1
  have hsub : IntegrableOn (fun t : ℝ => t) (Set.Ioc a b) :=
    (continuous_id.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hid : ∫ t in Set.Ioc a b, t = (b^2-a^2)/2 := by
    rw [← intervalIntegral.integral_of_le hab, integral_id]
  have hε : IntegrableOn (fun t : ℝ => ε*t) (Set.Ioc a b) := hsub.const_mul ε
  calc
    |(∫ t in Set.Ioc a b, Chebyshev.theta t)-(b^2-a^2)/2| =
        ‖∫ t in Set.Ioc a b, (Chebyshev.theta t-t)‖ := by
      rw [← hid, ← integral_sub hint hsub, Real.norm_eq_abs]
    _ ≤ ∫ t in Set.Ioc a b, ‖Chebyshev.theta t-t‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t in Set.Ioc a b, ε*t := by
      refine setIntegral_mono_on (hint.sub hsub).norm hε measurableSet_Ioc fun t ht => ?_
      rw [Real.norm_eq_abs]
      exact h t (Ioc_subset_Icc_self ht)
    _ = ε*(b^2-a^2)/2 := by rw [integral_const_mul, hid]; ring

lemma wsum_close {a b η : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hη : 0 ≤ η)
    (h : ∀ y ∈ Set.Icc a b, |Chebyshev.theta y - y| ≤ η * y) :
    |wsum a b-(b^2-a^2)/2| ≤ 2*η*b^2 := by
  rw [wsum_eq ha hab]
  have h1 := h b ⟨hab, le_rfl⟩
  have h2 := h a ⟨le_rfl, hab⟩
  have h3 := integral_theta_bounds hab h
  have hb : 0 ≤ b := ha.trans hab
  have e1 : |b*Chebyshev.theta b-b^2| ≤ η*b^2 := by
    rw [show b*Chebyshev.theta b-b^2 = b*(Chebyshev.theta b-b) by ring,
      abs_mul, abs_of_nonneg hb]
    have hm := mul_le_mul_of_nonneg_left h1 hb
    nlinarith only [hm]
  have e2 : |a*Chebyshev.theta a-a^2| ≤ η*a^2 := by
    rw [show a*Chebyshev.theta a-a^2 = a*(Chebyshev.theta a-a) by ring,
      abs_mul, abs_of_nonneg ha]
    have hm := mul_le_mul_of_nonneg_left h2 ha
    nlinarith only [hm]
  have ha2 : a^2 ≤ b^2 := by nlinarith
  have hηab : η*a^2 ≤ η*b^2 := mul_le_mul_of_nonneg_left ha2 hη
  rw [abs_le] at e1 e2 h3 ⊢
  constructor <;> nlinarith only [e1.1, e1.2, e2.1, e2.2, h3.1, h3.2, hηab]

end
end Zeta32.ArithSum.PrimeSums

end
