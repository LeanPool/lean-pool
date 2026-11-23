/-
Copyright (c) 2026 Fang, Hu, Li, Tang, and Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pengcheng Fang, Tao Hu, Yanyang Li, Quanyu Tang, Haiqi Zhang
-/

module

public import LeanPool.Bruck.HyperOrder
import LeanPool.Bruck.OrderFacts
import LeanPool.Bruck.Sharing

/-! # The zero shared-value case -/

public section

open scoped ENNReal

namespace Bruck

/-- Sharing zero with the derivative gives a constant quotient at finite
hyper-order outside the positive integers. -/
theorem exists_constant_mul_of_sharesCM_zero {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hshare : SharesCM f (deriv f) 0)
    (hfinite : hyperOrder f < ⊤)
    (hnotint : ∀ n : ℕ, 0 < n → hyperOrder f ≠ (n : ℝ≥0∞)) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ z, deriv f z = c * f z := by
  have hfree := zero_free_of_sharesCM_zero hf hshare
  obtain ⟨g, hg, hfg⟩ := exists_entire_log hf (fun z => (hfree z).1)
  have hgnon : ¬ ∀ z, g z = g 0 := by
    intro hconst
    have heq : f = fun _ => Complex.exp (g 0) :=
      funext fun z => by rw [← hfg z, hconst z]
    exact (hfree 0).2 (by rw [heq, deriv_const])
  have hdf (z : ℂ) : deriv f z = Complex.exp (g z) * deriv g z := by
    have heq : (fun w => Complex.exp (g w)) = f := funext hfg
    exact heq ▸ (hg z).hasDerivAt.cexp.deriv
  have hdgnz (z : ℂ) : deriv g z ≠ 0 := by
    intro hz
    exact (hfree z).2 (by rw [hdf, hz, mul_zero])
  have hord : hyperOrder f = ordinaryOrder g := by
    simpa only [hfg] using hyperOrder_exp_comp_eq_ordinaryOrder hg hgnon
  by_cases hconst : ∀ z, deriv g z = deriv g 0
  · refine ⟨deriv g 0, hdgnz 0, fun z => ?_⟩
    rw [hdf, hconst z, hfg, mul_comm]
  · exfalso
    have hgord : ordinaryOrder (deriv g) = hyperOrder f :=
      (ordinaryOrder_deriv_eq hg hconst).trans hord.symm
    have hgfinite : ordinaryOrder (deriv g) < ⊤ := by rwa [hgord]
    obtain ⟨p, hp⟩ := exists_exp_polynomial_of_finite_ordinaryOrder hg.deriv hdgnz
      hgfinite
    have hpdeg : 0 < p.natDegree := (polynomial_eval_nonconstant_iff p).mp
      fun hconstant => hconst fun z => by rw [hp z, hp 0, hconstant z]
    have heq : deriv g = fun z => Complex.exp (p.eval z) := funext hp
    rw [heq, ordinaryOrder_exp_polynomial_eq_natDegree p hpdeg] at hgord
    exact hnotint p.natDegree hpdeg hgord.symm

end Bruck
