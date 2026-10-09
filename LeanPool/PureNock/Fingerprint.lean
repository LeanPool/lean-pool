/-
Copyright (c) 2026 Pure Nock formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pure Nock formalization contributors
-/

module

public import LeanPool.PureNock.NPR

/-!
# Computable noun fingerprint

`NPR.fn` (`Nock/NPR.lean`, `def:ion_univariate`, `main.tex:1180–1184`) evaluates the noun
polynomials with Mathlib's `Polynomial`, which is `noncomputable`.  This module gives the
extractable Horner evaluation `fnHorner` and proves it equals `NPR.fn`
(`fnHorner_eq_fn`), so the collision-soundness bounds of `Nock/NPR.lean` apply to the code that
actually runs.  Instantiated at a concrete prime field `ZMod q` (with `[Fact (Nat.Prime q)]`
supplied by the caller — never as an axiom), `fnHorner` compiles and evaluates.
-/

@[expose] public section

namespace Nock
namespace NPR

open Polynomial

/-- Horner evaluation of a coefficient list: `hornerEval r [a₀,…,aₙ] = a₀ + r·(a₁ + r·(…))`,
    i.e. `Σᵢ aᵢ rⁱ`.  Computable (no `Polynomial`); the extractable core of the fingerprint. -/
def hornerEval {K : Type*} [Semiring K] (r : K) : List K → K
  | []     => 0
  | a :: l => a + r * hornerEval r l

section Horner
variable {K : Type*} [Field K]

/-- **Horner = polynomial evaluation.**  `hornerEval r l = (listPoly l).eval r`: the computable
    Horner scheme agrees with evaluating the coefficient polynomial `Σᵢ lᵢ Xⁱ` at `r`. -/
theorem hornerEval_eq_listPoly_eval (r : K) (l : List K) :
    hornerEval r l = (listPoly l).eval r := by
  induction l with
  | nil => simp [hornerEval, listPoly_nil]
  | cons x l ih =>
      simp only [hornerEval, listPoly_cons, eval_add, eval_C, eval_mul, eval_X, ih]

/-- **The computable fingerprint (`def:ion_univariate`, `main.tex:1180–1184`).**  `fnHorner r n =
    (r^{|dt|}, Σ dtᵢ rⁱ, Σ wᵢ rⁱ)` via Horner, with no `Polynomial`.  Equal to `NPR.fn`
    (`fnHorner_eq_fn`), so it inherits the collision bounds. -/
def fnHorner (r : K) (n : Noun) : K × K × K :=
  (r ^ n.leaves, hornerEval r (leafF n), hornerEval r (dyckBits n))

/-- **`fnHorner` computes `NPR.fn`.**  The extractable Horner fingerprint equals the polynomial
    fingerprint `fn` (`main.tex:1180–1184`), so `lem:ion_univariate_sec` /
    `corr:ion_single_security`
    (`Nock/NPR.lean`) transfer verbatim to the running code. -/
theorem fnHorner_eq_fn (n : Noun) (r : K) : fnHorner r n = fn n r := by
  simp only [fnHorner, fn, hornerEval_eq_listPoly_eval]

end Horner

end NPR
end Nock
