/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.ModelFree.SVI.NilpotentSquareRoot
public import LeanPool.MathFin.Models.ModelFree.SVI.ImaginaryTraceSignature

/-! # A conjugate pair contributes zero signature

Part of the SVI polynomial-sign certificate (#174).

For a positive quadratic `(X − a)² + b²`, `b ≠ 0`, the quotient by any power contains a square
root of `−1`, so its weighted trace form has signature zero.

## Main definitions

* `positiveQuadratic`: the quadratic `(X - C a)² + C (b²)` over `ℝ`.

## Main results

* `positiveQuadratic_degree`: `positiveQuadratic a b` has `natDegree` `2`.
* `quadraticRoot_has_imaginary`: for `b ≠ 0` and `r > 0`, `AdjoinRoot ((positiveQuadratic a b)^r)`
  contains `u` with `u ^ 2 = -1`.
* `weightedTraceForm_quadratic_signature`: for `b ≠ 0` and `r > 0`, the weighted trace form of
  `(positiveQuadratic a b)^r` with any weight `q` has signature `0`.

## Tags

conjugate pair roots, trace form signature, irreducible quadratic, SVI, MSC 91G20, JEL G13
-/

@[expose] public section

namespace MathFin
namespace SVI
open Polynomial

/-- The quadratic `(X − a)² + b²`. -/
noncomputable def positiveQuadratic (a b : ℝ) : ℝ[X] := (X-C a)^2 + C (b^2)

theorem positiveQuadratic_degree (a b : ℝ) : (positiveQuadratic a b).natDegree = 2 := by
  unfold positiveQuadratic
  compute_degree!

/-- A power of a real quadratic with no real roots contains an exact square
root of -1, even when the power produces nilpotents. -/
theorem quadraticRoot_has_imaginary (a b : ℝ) (hb : b ≠ 0) (r : ℕ) (hr : 0 < r) :
    ∃ u : AdjoinRoot ((positiveQuadratic a b)^r), u^2 = -1 := by
  let f := (positiveQuadratic a b)^r
  let A := AdjoinRoot f
  have hdeg : f.natDegree = 2*r := by
    simp [f, natDegree_pow, positiveQuadratic_degree, Nat.mul_comm]
  let : Nontrivial A := AdjoinRoot.nontrivial f
    (ne_of_gt (natDegree_pos_iff_degree_pos.mp (by rw [hdeg]; omega)))
  let z : A := AdjoinRoot.root f
  let alpha : A := algebraMap ℝ A a
  let beta : A := algebraMap ℝ A b
  let ibeta : A := algebraMap ℝ A b⁻¹
  let x : A := (z-alpha)*ibeta
  have hbi : ibeta^2*beta^2 = 1 := by
    dsimp [ibeta, beta]
    rw [← mul_pow, ← map_mul, inv_mul_cancel₀ hb, map_one, one_pow]
  have he : x^2+1 = ibeta^2 * aeval z (positiveQuadratic a b) := by
    calc
      x^2+1 = ibeta^2*(z-alpha)^2+1 := by dsimp [x]; ring
      _ = ibeta^2*(z-alpha)^2+ibeta^2*beta^2 := by rw [hbi]
      _ = ibeta^2 * aeval z (positiveQuadratic a b) := by
        simp only [positiveQuadratic, map_add, map_pow, map_sub, aeval_X, aeval_C]
        dsimp [alpha, beta]
        ring
  have hnil : IsNilpotent (x^2+1) := by
    refine ⟨r, ?_⟩
    rw [he, mul_pow, ← map_pow (aeval z) (positiveQuadratic a b) r]
    change (ibeta^2)^r * aeval (AdjoinRoot.root f) f = 0
    rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self, mul_zero]
  have hhalf : (2 : A) * algebraMap ℝ A (1/2) = 1 := by
    have hh : (2 : ℝ)*(1/2) = 1 := by norm_num
    simpa only [map_mul, map_ofNat, map_one] using congrArg (algebraMap ℝ A) hh
  exact exists_sq_neg_one_of_nilpotent _ hhalf x hnil

/-- A conjugate pair, at any multiplicity, contributes zero net signature. -/
theorem weightedTraceForm_quadratic_signature (a b : ℝ) (hb : b ≠ 0)
    (r : ℕ) (hr : 0 < r) (q : ℝ[X]) :
    formSignature (weightedTraceForm ((positiveQuadratic a b)^r) q).toQuadraticMap = 0 := by
  obtain ⟨u, hu⟩ := quadraticRoot_has_imaginary a b hb r hr
  exact weightedTraceForm_signature_zero_of_imaginary _ q u hu

end SVI
end MathFin
