/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.ModelFree.SVI.Assembly
public import LeanPool.MathFin.Models.ModelFree.SVI.Admissibility

/-! # The critical-point certificate, all degrees

Part of the SVI polynomial-sign certificate (#174).

`criticalCertificate` handles constant and nonconstant numerator polynomials alike. For `σ > 0`,
`b ≥ 0`, `ρ² ≤ 1` and under the variance gate, `criticalCertificate (polynomial p)` is equivalent to
`g(k) ≥ 0` for every `k` (`svi_criticalCertificate_iff`).

## Main definitions

* `criticalCertificate`: for a real polynomial `P`, `0 ≤ P.coeff 0` if `P` is constant, and
  otherwise `0 < P.leadingCoeff`, `0 ≤ P.eval 0` and `badCriticalCount P = 0`.

## Main results

* `criticalCertificate_iff`: `criticalCertificate P` iff `0 ≤ P.eval t` for every `t > 0`.
* `svi_criticalCertificate_iff`: for `σ > 0`, `b ≥ 0`, `1 - ρ² ≥ 0` and `varianceGate p`,
  `criticalCertificate (polynomial p)` iff `durrleman p k ≥ 0` for every `k`.

## Tags

critical point certificate, Durrleman condition, raw SVI, butterfly arbitrage, MSC 91G20, JEL G13
-/

@[expose] public section

namespace MathFin
namespace SVI
open Polynomial

/-- The analytic finite-critical-point certificate, with the constant and
zero cases included. The determinant replacement is proved separately. -/
noncomputable def criticalCertificate (P : ℝ[X]) : Prop :=
  if P.natDegree = 0 then 0 ≤ P.coeff 0
  else 0 < P.leadingCoeff ∧ 0 ≤ P.eval 0 ∧ badCriticalCount P = 0

theorem criticalCertificate_iff (P : ℝ[X]) :
    criticalCertificate P ↔ ∀ t : ℝ, 0 < t → 0 ≤ P.eval t := by
  unfold criticalCertificate
  split_ifs with hd
  · rw [eq_C_of_natDegree_eq_zero hd]
    simp only [coeff_C_zero, eval_C]
    exact ⟨fun h _ _ ↦ h, fun h ↦ h 1 (by norm_num)⟩
  · have hdeg : 0 < P.degree := natDegree_pos_iff_degree_pos.mp (Nat.pos_of_ne_zero hd)
    rw [badCriticalCount_eq_zero_iff P hdeg]
    exact (polynomial_nonneg_criterion P hdeg).symm

/-- All SVI degree branches under the exact polynomial variance gate. -/
theorem svi_criticalCertificate_iff (p : Params) (hs : 0 < p.sigma)
    (hb : 0 ≤ p.b) (hr : 0 ≤ 1 - p.rho ^ 2) (hg : varianceGate p) :
    criticalCertificate (polynomial p) ↔ ∀ k : ℝ, 0 ≤ durrleman p k := by
  rw [criticalCertificate_iff,
    durrleman_nonneg_iff p hs ((varianceGate_iff p hs hb hr).mp hg)]
  simp only [eval_polynomial]

end SVI
end MathFin
