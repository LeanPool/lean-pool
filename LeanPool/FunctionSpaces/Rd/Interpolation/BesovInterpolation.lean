/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Rd.Differences.BesovDifferences
public import LeanPool.FunctionSpaces.ApproximationSpaces.Interpolation.ApproxSpaces

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Besov spaces on `V` as interpolation spaces

Let `1 ≤ p < ∞`, `0 < η < 1` and `1 ≤ q₀, q₁, q ≤ ∞`.  For the band-limited scheme, the couple
of the dyadic quasi-norms of `A^{s₀}_{q₀}` and `A^{s₁}_{q₁}`, `0 < s₀ < s₁`, has the real
interpolation spaces `A^{(1-η)s₀+ηs₁}_q`, and `(L_p, A^{s₁}_{q₁})_{η,q} = A^{ηs₁}_q`
(`Rd.memKMethod_bandApproxCouple_iff`, `Rd.memKMethod_bandLeftApproxCouple_iff`).

For **Besov spaces by differences** of order `r` the couple carries the quasi-norms
`‖f‖_p + ‖(2^(ks_i) ω_r(f, 2^(-k))_p)_k‖_{ℓ_{q_i}}` (the couple
`ApproximationScheme.ModulusData.modCouple` of `Rd.bandModulusData`).  For `0 < s₀ < s₁ < r`
and `s = (1-η)s₀ + ηs₁`,

`f ∈ (B^{s₀}_{p,q₀}, B^{s₁}_{p,q₁})_{η,q} ↔ ‖f‖_p + ‖(2^(ks) ω_r(f, 2^(-k))_p)_k‖_{ℓ_q} < ∞`

(Bergh–Löfström, Theorem 6.4.5(1); Triebel 1978, Section 2.4; `Rd.memKMethod_modCouple_iff`),
and equivalently `‖(2^(js) ‖ψ_j ⋆ f‖_p)_j‖_{ℓ_q} < ∞`
(`Rd.memKMethod_modCouple_iff_littlewoodPaley`).  The endpoint
`(L_p, B^{s₁}_{p,q₁})_{η,q} = B^{ηs₁}_{p,q}` is `Rd.memKMethod_leftModCouple_iff`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace Rd

open ENNReal (lqNorm dyadicWeight)

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {p : ℝ≥0∞} [Fact (1 ≤ p)] {s₀ s₁ η : ℝ}
  {q₀ q₁ q : ℝ≥0∞}

/-- **Band-limited approximation spaces interpolate**: for `1 ≤ p < ∞`, `0 < s₀ < s₁`,
`0 < η < 1` and `1 ≤ q₀, q₁, q ≤ ∞`, the real interpolation space
`(A^{s₀}_{q₀}, A^{s₁}_{q₁})_{η,q}` of the band-limited scheme in `L_p(V)` is
`A^{(1-η)s₀+ηs₁}_q`. -/
theorem memKMethod_bandApproxCouple_iff (hp : p ≠ ∞) (hs₀ : 0 < s₀) (hs : s₀ < s₁) (hη : 0 < η)
    (hη' : η < 1) (hq₀ : 1 ≤ q₀) (hq₁ : 1 ≤ q₁) (hq : 1 ≤ q)
    {f : Lp ℂ p (volume : Measure V)} :
    ((bandScheme hp).approxCouple s₀ q₀ s₁ q₁).MemKMethod η q f ↔
      (bandScheme hp).MemApprox ((1 - η) * s₀ + η * s₁) q f :=
  ApproximationScheme.memKMethod_approxCouple_iff hs₀ hs hη hη' hq₀ hq₁ hq

/-- **`L_p` and a band-limited approximation space interpolate**: for `1 ≤ p < ∞`, `s₁ > 0`,
`0 < η < 1` and `1 ≤ q₁, q ≤ ∞`, the real interpolation space `(L_p, A^{s₁}_{q₁})_{η,q}` of the
band-limited scheme in `L_p(V)` is `A^{ηs₁}_q`. -/
theorem memKMethod_bandLeftApproxCouple_iff (hp : p ≠ ∞) (hs₁ : 0 < s₁) (hη : 0 < η)
    (hη' : η < 1) (hq₁ : 1 ≤ q₁) (hq : 1 ≤ q) {f : Lp ℂ p (volume : Measure V)} :
    ((bandScheme hp).leftApproxCouple s₁ q₁).MemKMethod η q f ↔
      (bandScheme hp).MemApprox (η * s₁) q f :=
  ApproximationScheme.memKMethod_approxCouple_zero_iff hs₁ hη hη' hq₁ hq

/-- **Besov spaces by differences interpolate** (Bergh–Löfström, Theorem 6.4.5(1); Triebel 1978,
Section 2.4): for `1 ≤ p < ∞`, an order `r`, `0 < s₀ < s₁ < r`, `0 < η < 1` and
`1 ≤ q₀, q₁, q ≤ ∞`, `f ∈ L_p(V)` lies in the real interpolation space of the couple of the
quasi-norms `‖f‖_p + ‖(2^(ks_i) ω_r(f, 2^(-k))_p)_k‖_{ℓ_{q_i}}` iff
`‖f‖_p + ‖(2^(ks) ω_r(f, 2^(-k))_p)_k‖_{ℓ_q} < ∞` with `s = (1-η)s₀ + ηs₁`. -/
theorem memKMethod_modCouple_iff (hp : p ≠ ∞) {r : ℕ} (hs₀ : 0 < s₀) (hs : s₀ < s₁)
    (hs₁ : s₁ < r) (hη : 0 < η) (hη' : η < 1) (hq₀ : 1 ≤ q₀) (hq₁ : 1 ≤ q₁) (hq : 1 ≤ q)
    {f : Lp ℂ p (volume : Measure V)} :
    ((bandModulusData hp r).modCouple s₀ q₀ s₁ q₁).MemKMethod η q f ↔
      ‖f‖ₑ + lqNorm q (fun k => dyadicWeight ((1 - η) * s₀ + η * s₁) k * lpModulus p r f k) < ∞ :=
  (bandModulusData hp r).memKMethod_modCouple_iff hs₀ hs hs₁ hη hη' hq₀ hq₁ hq

/-- **Besov spaces by differences interpolate, in Littlewood–Paley form**: for `1 ≤ p < ∞`, an
order `r`, `0 < s₀ < s₁ < r`, `0 < η < 1` and `1 ≤ q₀, q₁, q ≤ ∞`, `f ∈ L_p(V)` lies in the real
interpolation space of the couple of the quasi-norms
`‖f‖_p + ‖(2^(ks_i) ω_r(f, 2^(-k))_p)_k‖_{ℓ_{q_i}}` iff `‖(2^(js) ‖ψ_j ⋆ f‖_p)_j‖_{ℓ_q} < ∞`
with `s = (1-η)s₀ + ηs₁`. -/
theorem memKMethod_modCouple_iff_littlewoodPaley (hp : p ≠ ∞) {r : ℕ} (hs₀ : 0 < s₀)
    (hs : s₀ < s₁) (hs₁ : s₁ < r) (hη : 0 < η) (hη' : η < 1) (hq₀ : 1 ≤ q₀) (hq₁ : 1 ≤ q₁)
    (hq : 1 ≤ q) {f : Lp ℂ p (volume : Measure V)} :
    ((bandModulusData hp r).modCouple s₀ q₀ s₁ q₁).MemKMethod η q f ↔
      littlewoodPaleyNorm hp ((1 - η) * s₀ + η * s₁) q f < ∞ := by
  rw [memKMethod_modCouple_iff hp hs₀ hs hs₁ hη hη' hq₀ hq₁ hq,
    littlewoodPaleyNorm_lt_top_iff_modulus hp
      (ApproximationScheme.reiterationExponent_pos hs₀ hs hη hη')
      (ApproximationScheme.reiterationExponent_lt hs hs₁ hη') hq f]

/-- **`L_p` and a Besov space by differences interpolate**: for `1 ≤ p < ∞`, an order `r`,
`0 < s₁ < r`, `0 < η < 1` and `1 ≤ q₁, q ≤ ∞`, `f ∈ L_p(V)` lies in the real interpolation space
of the couple of `‖f‖_p` and `‖f‖_p + ‖(2^(ks₁) ω_r(f, 2^(-k))_p)_k‖_{ℓ_{q₁}}` iff
`‖f‖_p + ‖(2^(kηs₁) ω_r(f, 2^(-k))_p)_k‖_{ℓ_q} < ∞`. -/
theorem memKMethod_leftModCouple_iff (hp : p ≠ ∞) {r : ℕ} (hs₁ : 0 < s₁) (hs₁r : s₁ < r)
    (hη : 0 < η) (hη' : η < 1) (hq₁ : 1 ≤ q₁) (hq : 1 ≤ q) {f : Lp ℂ p (volume : Measure V)} :
    ((bandModulusData hp r).leftModCouple s₁ q₁).MemKMethod η q f ↔
      ‖f‖ₑ + lqNorm q (fun k => dyadicWeight (η * s₁) k * lpModulus p r f k) < ∞ :=
  (bandModulusData hp r).memKMethod_leftModCouple_iff hs₁ hs₁r hη hη' hq₁ hq

end Rd
