/-
Copyright (c) 2026 Fang, Hu, Li, Tang, and Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pengcheng Fang, Tao Hu, Yanyang Li, Quanyu Tang, Haiqi Zhang
-/

module

public import LeanPool.Bruck.Classification
public import LeanPool.Bruck.Sharing
public import LeanPool.Bruck.ZeroSharing

/-!
# Brück's conjecture

The zero shared value is handled via zero-free entire functions and
ordinary order. For a nonzero value, the normalization yields the
inhomogeneous equation whose possible hyper-orders are constrained
by the polynomial and transcendental growth estimates.
-/

public section

open scoped ENNReal

namespace Bruck

/-- A nonconstant entire function of finite hyper-order different from every
positive integer, sharing a finite value with its derivative counting
multiplicities, has a nonzero constant sharing quotient. -/
theorem bruck {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hnon : ¬ ∀ z, f z = f 0) (a : ℂ) (hshare : SharesCM f (deriv f) a)
    (hfinite : hyperOrder f < ⊤)
    (hnotint : ∀ n : ℕ, 0 < n → hyperOrder f ≠ (n : ℝ≥0∞)) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ z, deriv f z - a = c * (f z - a) := by
  classical
  by_cases ha : a = 0
  · subst a
    simpa only [sub_zero] using
      exists_constant_mul_of_sharesCM_zero hf hnon hshare hfinite hnotint
  obtain ⟨h, hh, heq, hODE⟩ := normalized_solution_of_sharesCM ha hf hshare
  let y : ℂ → ℂ := fun z => (f z - a) / a
  have hy : Differentiable ℂ y := (hf.sub_const a).div_const a
  have hynon : ¬ ∀ z, y z = y 0 := by
    intro hc
    apply hnon
    intro z
    have h := hc z
    change (f z - a) / a = (f 0 - a) / a at h
    have hmul := congrArg (· * a) h
    simp only [div_mul_cancel₀ _ ha] at hmul
    linear_combination hmul
  have haff : (fun z => a⁻¹ * f z + -1) = y := by
    funext z
    change a⁻¹ * f z + -1 = (f z - a) / a
    field_simp [ha]
    ring
  have hrho : hyperOrder y = hyperOrder f := by
    rw [← haff]
    exact hyperOrder_affine hf hnon (inv_ne_zero ha) (-1)
  have hconst : ∀ z, h z = h 0 := by
    by_contra hhnon
    by_cases htrans : WVNonPolynomial h
    · have htop := hyperOrder_eq_top_of_transcendental_ode hh hhnon htrans hy hynon hODE
      rw [hrho] at htop
      exact (ne_of_lt hfinite) htop
    · simp only [WVNonPolynomial, not_forall, not_exists, not_not] at htrans
      obtain ⟨P, hP⟩ := htrans
      have hPh : h = P.eval := funext hP
      have hPd : 0 < P.natDegree := by
        by_contra! hz
        have hpcons := Polynomial.eq_C_of_natDegree_eq_zero (Nat.eq_zero_of_le_zero hz)
        apply hhnon
        rw [hPh, hpcons]
        intro z
        simp
      have hODE' : ∀ z, deriv y z = Complex.exp (P.eval z) * y z + 1 := by
        simpa only [hPh] using hODE
      have hd := hyperOrder_eq_natDegree_of_polynomial_ode P hPd hy hynon hODE'
      rw [hrho] at hd
      exact hnotint P.natDegree hPd hd
  exact ⟨Complex.exp (h 0), Complex.exp_ne_zero _, fun z => by simpa only [hconst z] using heq z⟩

end Bruck
