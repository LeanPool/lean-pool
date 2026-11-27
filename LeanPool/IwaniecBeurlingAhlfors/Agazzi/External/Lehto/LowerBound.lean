/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

-- Modified for Lean Pool. See the project entry module for upstream attribution.

public import LeanPool.IwaniecBeurlingAhlfors.HarmonicAnalysis.Defs
import LeanPool.IwaniecBeurlingAhlfors.HarmonicAnalysis.BeurlingAhlfors.Duality
import LeanPool.IwaniecBeurlingAhlfors.HarmonicAnalysis.BeurlingAhlfors.LowerBound

/-!
# Lehto: the lower bound `‖𝒮‖_p ≥ p* − 1`

O. Lehto, *Remarks on the integrability of the derivatives of quasiconformal mappings*, Ann. Acad.
Sci. Fenn. Ser. A I No. 371 (1965). The paper (arXiv:2609.28311, TeX line 320) cites it for the
lower bound in `(eq:BA-sharp-norm)`: "the lower bound in (eq:BA-sharp-norm) is classical
[Lehto1965]".

Stated (`lowerBound`) with the package `HarmonicAnalysis`'s Beurling–Ahlfors transform `𝓑`
(symbol `(conj ξ) / ξ`) and its norm on `L^p (ℂ)`, the supremum over Schwartz functions
(`HarmonicAnalysis.beurlingPowNorm 1 p`).
The source has not been read: its statement is the classical one, as the paper uses it.

## Proof

Not Lehto's, which was not read. First `‖𝓑‖_p ≥ p − 1`: the package's
`HarmonicAnalysis.sub_one_le_beurlingPowNorm_one`, the case `n = 1` of Dragičević's lower bound
`‖𝓑^n‖_p ≥ κ_n (p)` (Arch. Math. 96 (2011), Theorem 1.1, `κ₁ (p) = p − 1`), proved there by
Dragičević's argument with the test functions of that paper for `n = 1`, which on the unit disc
are the extremal functions `f_α (z) = z |z|^{−2α}`, `0 < α < 1/p`, of Baernstein–Montgomery-Smith
(1999, §1):

* `‖∂f_α‖_p ≤ ‖𝓑‖_p ‖∂_zbar f_α‖_p`, by `𝓑 (∂_zbar φ) = ∂φ` for Schwartz functions `φ` and Schwartz
  approximations of `f_α` in `W^{1,p}`;
* `‖∂f_α‖_p / ‖∂_zbar f_α‖_p → p − 1` as `α → 1/p`.

Then `‖𝓑‖_p = ‖𝓑‖_q`, `q = p / (p − 1)` (`HarmonicAnalysis.beurlingPowNorm_conjExponent`), gives
`‖𝓑‖_p ≥ q − 1`; Baernstein and Montgomery-Smith take the conjugates `conj f_α` instead.

## References

* A. Baernstein II and S. J. Montgomery-Smith, *Some conjectures about integral means of `∂f` and
  `∂_zbar f`*, in: Complex analysis and differential equations (Uppsala, 1997), Acta Univ.
  Upsaliensis
  Skr. Uppsala Univ. C Organ. Hist. 64 (1999), 92–109; arXiv:math/9709215v2, §1.
* O. Dragičević, *Some remarks on the `L^p` estimates for powers of the Ahlfors–Beurling
  operator*, Arch. Math. 96 (2011), 463–471.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology

namespace External.Lehto

open HarmonicAnalysis

/-- **Lehto's lower bound**: `‖𝒮‖_{L^p → L^p} ≥ p* − 1`, `p* = max (p, p / (p − 1))`, for
`1 < p < ∞`.

Proof: `‖𝒮‖_p ≥ p − 1` is the case `n = 1` of Dragičević's lower bound, with the extremal
functions `f_α` of Baernstein–Montgomery-Smith (1999, §1), in the package `HarmonicAnalysis`
(`HarmonicAnalysis.sub_one_le_beurlingPowNorm_one`); duality, `‖𝒮‖_p = ‖𝒮‖_{p'}`
(`HarmonicAnalysis.beurlingPowNorm_conjExponent`), gives `‖𝒮‖_p ≥ p' − 1`. Lehto's own argument
was not read. -/
theorem lowerBound {p : ℝ} (hp : 1 < p) :
    ENNReal.ofReal (max p (p / (p - 1)) - 1) ≤ HarmonicAnalysis.beurlingPowNorm 1 p := by
  have hq : 1 < p / (p - 1) := by rw [lt_div_iff₀ (by linarith)]; linarith
  rw [← max_sub_sub_right, ENNReal.ofReal_max]
  refine max_le (HarmonicAnalysis.sub_one_le_beurlingPowNorm_one hp) ?_
  rw [beurlingPowNorm_conjExponent 1 hp]
  exact HarmonicAnalysis.sub_one_le_beurlingPowNorm_one hq

end External.Lehto
