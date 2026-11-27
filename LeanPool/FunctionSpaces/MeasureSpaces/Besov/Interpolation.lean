/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.MeasureSpaces.Besov.Basic
public import LeanPool.FunctionSpaces.ApproximationSpaces.Interpolation.ApproxSpaces

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Besov spaces as interpolation spaces

Let `S` be a scheme of functions on `Ω`, `μ` a finite measure and `1 ≤ p ≤ ∞`.  The couple
`(B^{s₀}_{p,q₀}, B^{s₁}_{p,q₁})` (`FunctionScheme.besovCouple`) carries the dyadic quasi-norms of
the two Besov spaces, and the couple `(L_p, B^{s₁}_{p,q₁})` (`FunctionScheme.lpBesovCouple`) the
norm of `L_p` and the dyadic quasi-norm of `B^{s₁}_{p,q₁}`.  For `0 < s₀ < s₁`, `0 < η < 1` and
`1 ≤ q₀, q₁, q ≤ ∞` the real interpolation spaces of the continuous K-method are

`(B^{s₀}_{p,q₀}, B^{s₁}_{p,q₁})_{η,q} = B^{(1-η)s₀+ηs₁}_{p,q}`,
`(L_p, B^{s₁}_{p,q₁})_{η,q} = B^{ηs₁}_{p,q}`

(`FunctionScheme.memKMethod_besovCouple_iff`, `FunctionScheme.memKMethod_lpBesovCouple_iff`),
for every scheme.  Both are also equalities of subspaces of `L_p(μ)`
(`FunctionScheme.kMethodSpace_besovCouple`, `FunctionScheme.kMethodSpace_lpBesovCouple`).  Since
`B^s_{p,q}` is the approximation space `A^s_q(L_p(μ), S)`, they are the reiteration theorem for
approximation spaces and its endpoint case (`ApproximationScheme.memKMethod_approxCouple_iff`,
`ApproximationScheme.memKMethod_approxCouple_zero_iff`).  The same interpolation spaces arise
from the couples of Pietsch's quasi-norms `FunctionScheme.besovNorm`, which are equivalent to the
dyadic ones (`FunctionScheme.memKMethod_besovNormCouple_iff`,
`FunctionScheme.memKMethod_lpBesovNormCouple_iff`).
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace FunctionScheme

variable {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
  (S : FunctionScheme Ω) (μ : Measure Ω) [IsFiniteMeasure μ] (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- The **couple `(B^{s₀}_{p,q₀}, B^{s₁}_{p,q₁})`** of two Besov spaces of the scheme, on
`L_p(μ)`, with the dyadic quasi-norms of the approximation spaces `A^{s_i}_{q_i}(L_p(μ), S)`. -/
noncomputable abbrev besovCouple (s₀ : ℝ) (q₀ : ℝ≥0∞) (s₁ : ℝ) (q₁ : ℝ≥0∞) :
    InterpCouple (Lp ℂ p μ) :=
  (S.toLp μ p).approxCouple s₀ q₀ s₁ q₁

/-- The **couple `(L_p, B^{s₁}_{p,q₁})`** of the scheme: the norm of `L_p(μ)` and the dyadic
quasi-norm of the Besov space `B^{s₁}_{p,q₁}`. -/
noncomputable abbrev lpBesovCouple (s₁ : ℝ) (q₁ : ℝ≥0∞) : InterpCouple (Lp ℂ p μ) :=
  (S.toLp μ p).leftApproxCouple s₁ q₁

variable {S μ p} {s₀ s₁ η : ℝ} {q₀ q₁ q : ℝ≥0∞}

/-- **Besov spaces interpolate**: for every scheme of functions, `1 ≤ p ≤ ∞`, `0 < s₀ < s₁`,
`0 < η < 1` and `1 ≤ q₀, q₁, q ≤ ∞`, `(B^{s₀}_{p,q₀}, B^{s₁}_{p,q₁})_{η,q} = B^{(1-η)s₀+ηs₁}_{p,q}`
(DeVore–Popov, Trans. AMS 305 (1988), for the classical Besov spaces). -/
theorem memKMethod_besovCouple_iff (hs₀ : 0 < s₀) (hs : s₀ < s₁) (hη : 0 < η) (hη' : η < 1)
    (hq₀ : 1 ≤ q₀) (hq₁ : 1 ≤ q₁) (hq : 1 ≤ q) {f : Lp ℂ p μ} :
    (S.besovCouple μ p s₀ q₀ s₁ q₁).MemKMethod η q f ↔
      S.MemBesov μ p ((1 - η) * s₀ + η * s₁) q f :=
  ApproximationScheme.memKMethod_approxCouple_iff hs₀ hs hη hη' hq₀ hq₁ hq

/-- **`L_p` and a Besov space interpolate**: for every scheme of functions, `1 ≤ p ≤ ∞`,
`s₁ > 0`, `0 < η < 1` and `1 ≤ q₁, q ≤ ∞`, `(L_p, B^{s₁}_{p,q₁})_{η,q} = B^{ηs₁}_{p,q}`. -/
theorem memKMethod_lpBesovCouple_iff (hs₁ : 0 < s₁) (hη : 0 < η) (hη' : η < 1) (hq₁ : 1 ≤ q₁)
    (hq : 1 ≤ q) {f : Lp ℂ p μ} :
    (S.lpBesovCouple μ p s₁ q₁).MemKMethod η q f ↔ S.MemBesov μ p (η * s₁) q f :=
  ApproximationScheme.memKMethod_approxCouple_zero_iff hs₁ hη hη' hq₁ hq

/-- **Besov spaces interpolate**, as an equality of subspaces of `L_p(μ)`: for `0 < s₀ < s₁`,
`0 < η < 1` and `1 ≤ q₀, q₁, q ≤ ∞`, the real interpolation space
`(B^{s₀}_{p,q₀}, B^{s₁}_{p,q₁})_{η,q}` is `B^{(1-η)s₀+ηs₁}_{p,q}`. -/
theorem kMethodSpace_besovCouple (hs₀ : 0 < s₀) (hs : s₀ < s₁) (hη : 0 < η) (hη' : η < 1)
    (hq₀ : 1 ≤ q₀) (hq₁ : 1 ≤ q₁) (hq : 1 ≤ q) :
    InterpCouple.kMethodSpace
        (ApproximationScheme.isQuasiNormed_approxCouple (A := S.toLp μ p) hs₀.le
          (hs₀.trans hs).le hq₀ hq₁)
        ApproximationScheme.isHomogeneous_approxCouple η q =
      S.besovSpace μ p ((1 - η) * s₀ + η * s₁) q
        (ApproximationScheme.reiterationExponent_pos hs₀ hs hη hη').le hq :=
  ApproximationScheme.kMethodSpace_approxCouple hs₀ hs hη hη' hq₀ hq₁ hq

/-- **`L_p` and a Besov space interpolate**, as an equality of subspaces of `L_p(μ)`: for
`s₁ > 0`, `0 < η < 1` and `1 ≤ q₁, q ≤ ∞`, the real interpolation space
`(L_p, B^{s₁}_{p,q₁})_{η,q}` is `B^{ηs₁}_{p,q}`. -/
theorem kMethodSpace_lpBesovCouple (hs₁ : 0 < s₁) (hη : 0 < η) (hη' : η < 1) (hq₁ : 1 ≤ q₁)
    (hq : 1 ≤ q) :
    InterpCouple.kMethodSpace
        (ApproximationScheme.isQuasiNormed_leftApproxCouple (A := S.toLp μ p) hs₁.le hq₁)
        ApproximationScheme.isHomogeneous_leftApproxCouple η q =
      S.besovSpace μ p (η * s₁) q (mul_pos hη hs₁).le hq :=
  ApproximationScheme.kMethodSpace_approxCouple_zero hs₁ hη hη' hq₁ hq

/-- **Besov spaces interpolate, with Pietsch's quasi-norms**: for `0 < s₀ < s₁`, `0 < η < 1` and
`1 ≤ q₀, q₁, q ≤ ∞`, the real interpolation space of the couple of the Besov quasi-norms
`FunctionScheme.besovNorm` of `B^{s₀}_{p,q₀}` and `B^{s₁}_{p,q₁}` is `B^{(1-η)s₀+ηs₁}_{p,q}`.
Pietsch's quasi-norm is at most `2^s` times the dyadic one, and the dyadic one at most `4 · 2^s`
times Pietsch's (`ApproximationScheme.approxNorm_le_approxNormDyadic`,
`ApproximationScheme.approxNormDyadic_le_approxNorm`), so the sandwich principle applies. -/
theorem memKMethod_besovNormCouple_iff (hs₀ : 0 < s₀) (hs : s₀ < s₁) (hη : 0 < η) (hη' : η < 1)
    (hq₀ : 1 ≤ q₀) (hq₁ : 1 ≤ q₁) (hq : 1 ≤ q) {f : Lp ℂ p μ} :
    (⟨S.besovNorm μ p s₀ q₀, S.besovNorm μ p s₁ q₁⟩ : InterpCouple (Lp ℂ p μ)).MemKMethod η q f ↔
      S.MemBesov μ p ((1 - η) * s₀ + η * s₁) q f :=
  ApproximationScheme.memKMethod_iff_memApprox_of_two_sandwiches
    (ENNReal.two_rpow_ne_top s₀)
    (ENNReal.mul_ne_top (by norm_num) (ENNReal.two_rpow_ne_top s₀))
    (ENNReal.two_rpow_ne_top s₁)
    (ENNReal.mul_ne_top (by norm_num) (ENNReal.two_rpow_ne_top s₁))
    hq₀ hq₀ hq₁ hq₁ hs₀ hs hη hη' hq
    (ApproximationScheme.approxNorm_le_approxNormDyadic hq₀ hs₀.le)
    (ApproximationScheme.approxNormDyadic_le_approxNorm hq₀ hs₀.le)
    (ApproximationScheme.approxNorm_le_approxNormDyadic hq₁ (hs₀.trans hs).le)
    (ApproximationScheme.approxNormDyadic_le_approxNorm hq₁ (hs₀.trans hs).le)

/-- **`L_p` and a Besov space interpolate, with Pietsch's quasi-norm**: for `s₁ > 0`,
`0 < η < 1` and `1 ≤ q₁, q ≤ ∞`, the real interpolation space of the couple of the norm of
`L_p(μ)` and the Besov quasi-norm `FunctionScheme.besovNorm` of `B^{s₁}_{p,q₁}` is
`B^{ηs₁}_{p,q}`. -/
theorem memKMethod_lpBesovNormCouple_iff (hs₁ : 0 < s₁) (hη : 0 < η) (hη' : η < 1)
    (hq₁ : 1 ≤ q₁) (hq : 1 ≤ q) {f : Lp ℂ p μ} :
    (⟨fun f => ‖f‖ₑ, S.besovNorm μ p s₁ q₁⟩ : InterpCouple (Lp ℂ p μ)).MemKMethod η q f ↔
      S.MemBesov μ p (η * s₁) q f :=
  ApproximationScheme.memKMethod_iff_memApprox_of_sandwich
    (ENNReal.two_rpow_ne_top s₁)
    (ENNReal.mul_ne_top (by norm_num) (ENNReal.two_rpow_ne_top s₁))
    hq₁ hq₁ hs₁ hη hη' hq
    (ApproximationScheme.approxNorm_le_approxNormDyadic hq₁ hs₁.le)
    (ApproximationScheme.approxNormDyadic_le_approxNorm hq₁ hs₁.le)

end FunctionScheme
