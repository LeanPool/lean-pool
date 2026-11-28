/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Wavelets.Examples.Daubechies.HolderRegularity
public import LeanPool.FunctionSpaces.Wavelets.Examples.Daubechies.MatrixMethodD4
public import LeanPool.FunctionSpaces.Wavelets.Examples.Daubechies.Projections

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# The Bernstein inequality for the Daubechies scaling spaces

For a Daubechies mask of order `N ≥ 2` with scaling function `φ` (`Daubechies.scalingFun`) and
`1 ≤ p < ∞`, let `V_j ⊆ L_p(ℝ)` be the scaling space of level `j` (`Daubechies.scalingSpace`),
the range of the projection `P_j f = ∑_k ⟨f, φ_{j,k}⟩ φ_{j,k}` with
`φ_{j,k}(x) = 2^(j/2) φ(2^j x - k)`. This file proves the inverse inequality of the Daubechies
scheme: the moduli of smoothness `ω_r(f, t)_p = sup_{|h| ≤ t} ‖Δ_h^r f‖_p` (`Rd.modulus`) of the
elements of `V_j` are controlled by those of `φ`. Here `Δ_h f(x) = f(x + h) - f(x)` is Mathlib's
`fwdDiff h f` and `Δ_h^r = (fwdDiff h)^[r]` its `r`-fold iterate.

* **Differences of expansions.** Differences commute with dilation and translation:
  `Δ_h^r g_{j,k} = (Δ_{2^j h}^r g)_{j,k}` for `g_{j,k}(x) = 2^(j/2) g(2^j x - k)`
  (`Daubechies.iterate_fwdDiff_scaledFun`). Hence, for a generator `g` vanishing outside a bounded
  interval, `Δ_h^r ∑_k c_k g_{j,k} = ∑_k c_k (Δ_{2^j h}^r g)_{j,k}` at every point
  (`Daubechies.iterate_fwdDiff_expand`).
* **The Bernstein inequality.** For `a ∈ V_j` and `2^j t ≤ 1`,
  `ω_r(a, t)_p ≤ C ω_r(φ, 2^j t)_p ‖a‖_p` with `C = (2N + 2r)^(1 - 1/p) (2N)^(1/p) ‖φ‖_{p'}`
  independent of `j`, `a` and `t` (`Daubechies.modulus_mem_scalingSpace_le`,
  `Daubechies.bernsteinConst`). The element `a` is the expansion `∑_k λ_k φ_{j,k}` of its
  coefficients `λ_k = ⟨a, φ_{j,k}⟩`, so `Δ_h^r a = ∑_k λ_k (Δ_{2^j h}^r φ)_{j,k}`. For
  `|2^j h| ≤ 1` the generator `Δ_{2^j h}^r φ` vanishes outside `[-r, 2N - 1 + r]`, and the upper
  stability of the expansions and the coefficient estimate of
  `FunctionSpaces.Wavelets.Examples.Daubechies.Expansion` give
  `‖Δ_h^r a‖_p ≤ (2N + 2r)^(1 - 1/p) ‖Δ_{2^j h}^r φ‖_p 2^(j(1/2 - 1/p)) ‖λ‖_{ℓ_p}`
  `≤ C ‖Δ_{2^j h}^r φ‖_p ‖a‖_p`.
* **Bernstein bounds.** A Bernstein bound of order `θ` is a bound `ω_r(φ, t)_p ≤ K t^θ` for
  `0 < t ≤ 1` with a finite constant `K` (`Daubechies.BernsteinBound`). The regularity theorems
  for `φ` provide them: for `p ≤ 2` of every order `s < N - log₄ λ` under a growth bound
  `T^n 1 ≤ C λ^n` for the transfer operator (`Daubechies.bernsteinBound_of_le_two`), for `p ≥ 2`
  of the interpolated order `(2/p) s + (1 - 2/p) a` with a Hölder exponent `a` of `φ`
  (`Daubechies.bernsteinBound_interp`, `Daubechies.bernsteinBound_interp_of_holder`), and
  explicitly for the orders two and three (`Daubechies.bernsteinBound_order_two`,
  `Daubechies.bernsteinBound_order_three`) and for D4 with its Hölder exponent
  `2 - log₂(1 + √3)` (`Daubechies.bernsteinBound_d4`).
* **The inverse inequality of the scheme.** Under a Bernstein bound of order `θ`, every
  approximant `a` of complexity `2^j` of the Daubechies scheme satisfies
  `ω_r(a, 2^(-k))_p ≤ C_B 2^(-(k-j)θ) ‖a‖_p` for all `k`, with `k - j` truncated at `0`
  (`Daubechies.inverse_scheme`): for `k ≥ j` by the Bernstein inequality at `t = 2^(-k)` and the
  bound `ω_r(φ, 2^(-(k-j)))_p ≤ K 2^(-(k-j)θ)`, for `k < j` by `ω_r(a, t)_p ≤ 2^r ‖a‖_p`. This is
  the inverse inequality of `ApproximationScheme.ModulusData`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal Real
open ENNReal (dyadicWeight)

namespace Daubechies

/-! ### Differences of expansions -/

section Generic

variable {g : ℝ → ℂ} {a b : ℝ}

/-- **Differences commute with dilation and translation**: for every `g : ℝ → ℂ`, level `j`,
position `k` and step `h`, `Δ_h g_{j,k} = (Δ_{2^j h} g)_{j,k}`, that is
`g_{j,k}(x + h) - g_{j,k}(x) = 2^(j/2) (g(2^j x - k + 2^j h) - g(2^j x - k))`, since
`2^j (x + h) - k = (2^j x - k) + 2^j h`. -/
theorem fwdDiff_scaledFun (g : ℝ → ℂ) (j : ℕ) (k : ℤ) (h : ℝ) :
    fwdDiff h (scaledFun g j k) = scaledFun (fwdDiff (2 ^ j * h) g) j k := by
  funext x
  simp only [fwdDiff, scaledFun]
  rw [← mul_sub, show (2 : ℝ) ^ j * (x + h) - k = 2 ^ j * x - k + 2 ^ j * h by ring]

/-- **Higher differences commute with dilation and translation**: for every `g : ℝ → ℂ`, order
`r`, level `j`, position `k` and step `h`, `Δ_h^r g_{j,k} = (Δ_{2^j h}^r g)_{j,k}`; that is, `Δ_h^r`
maps `x ↦ 2^(j/2) g(2^j x - k)` to `x ↦ 2^(j/2) (Δ_{2^j h}^r g)(2^j x - k)`. By induction on `r`
from `Daubechies.fwdDiff_scaledFun`. -/
theorem iterate_fwdDiff_scaledFun (g : ℝ → ℂ) (r j : ℕ) (k : ℤ) (h : ℝ) :
    (fwdDiff h)^[r] (scaledFun g j k) = scaledFun ((fwdDiff (2 ^ j * h))^[r] g) j k := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [Function.iterate_succ_apply', ih, fwdDiff_scaledFun,
      ← Function.iterate_succ_apply' (fwdDiff (2 ^ j * h)) r g]

/-- **A difference of an expansion**: if `g` vanishes outside `[a, b]`, then for every level `j`,
all coefficients `c : ℤ → ℂ` and every step `h`,
`Δ_h (∑_k c_k g_{j,k}) = ∑_k c_k (Δ_{2^j h} g)_{j,k}` at every point. At each point only finitely
many terms are nonzero (`Daubechies.summable_expand`), so the difference may be taken termwise
(`Daubechies.fwdDiff_scaledFun`). -/
theorem fwdDiff_expand (hsupp : ∀ x ∉ Set.Icc a b, g x = 0) (j : ℕ) (c : ℤ → ℂ) (h : ℝ) :
    fwdDiff h (expand g j c) = expand (fwdDiff (2 ^ j * h) g) j c := by
  funext x
  change expand g j c (x + h) - expand g j c x = _
  simp only [expand]
  rw [← (summable_expand hsupp j c (x + h)).tsum_sub (summable_expand hsupp j c x)]
  refine tsum_congr fun k => ?_
  rw [← mul_sub]
  exact congrArg (c k * ·) (congrFun (fwdDiff_scaledFun g j k h) x)

/-- **Higher differences of an expansion**: if `g` vanishes outside `[a, b]`, then for every
order `r`, level `j`, all coefficients `c : ℤ → ℂ` and every step `h`,
`Δ_h^r (∑_k c_k g_{j,k}) = ∑_k c_k (Δ_{2^j h}^r g)_{j,k}` at every point. By induction on `r`
from `Daubechies.fwdDiff_expand`; each generator `Δ_{2^j h}^i g` vanishes outside a bounded
interval (`Daubechies.iterate_fwdDiff_eq_zero_of_notMem`). -/
theorem iterate_fwdDiff_expand (hsupp : ∀ x ∉ Set.Icc a b, g x = 0) (r j : ℕ) (c : ℤ → ℂ)
    (h : ℝ) : (fwdDiff h)^[r] (expand g j c) = expand ((fwdDiff (2 ^ j * h))^[r] g) j c := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [Function.iterate_succ_apply', ih,
      fwdDiff_expand (fun x hx => iterate_fwdDiff_eq_zero_of_notMem hsupp r (2 ^ j * h) hx),
      ← Function.iterate_succ_apply' (fwdDiff (2 ^ j * h)) r g]

end Generic

/-! ### The Bernstein inequality for the scaling spaces -/

variable {N : ℕ} (m : Mask N)

/-- **The overlap number of the differences of `φ`**: for `N ≥ 1` and every `r ∈ ℕ`, the interval
`[-r, 2N - 1 + r]`, outside which the differences `Δ_H^r φ` with `|H| ≤ 1` vanish
(`Daubechies.higherDiff_scalingFun_eq_zero`), has the overlap number
`⌈(2N - 1 + r) - (-r)⌉ + 1 = 2N + 2r` of the upper estimate of expansions
(`Daubechies.eLpNorm_expand_le`). -/
theorem natCeil_higherDiff_support_add_one (hN : 1 ≤ N) (r : ℕ) :
    ⌈(2 * N - 1 + r : ℝ) - -(r : ℝ)⌉₊ + 1 = 2 * N + 2 * r := by
  have h : (2 * N - 1 + r : ℝ) - -(r : ℝ) = ((2 * N - 1 + 2 * r : ℕ) : ℝ) := by
    rw [Nat.cast_add, Nat.cast_sub (by omega)]
    push_cast
    ring
  rw [h, Nat.ceil_natCast]
  omega

/-- **The constant of the Bernstein inequality**: `(2N + 2r)^(1 - 1/p) (2N)^(1/p) ‖φ‖_{p'}` with
the conjugate exponent `p'`. The first factor is the overlap factor of the upper estimate of
expansions (`Daubechies.eLpNorm_expand_le`) for the generators `Δ_H^r φ`, `|H| ≤ 1`, which vanish
outside `[-r, 2N - 1 + r]` (`Daubechies.natCeil_higherDiff_support_add_one`); the second is the
constant of the coefficient estimate (`Daubechies.coeffConst` for `φ` and its support
`[0, 2N - 1]`). It is the same for every level and every scale. -/
noncomputable def bernsteinConst (p : ℝ≥0∞) (r : ℕ) : ℝ≥0∞ :=
  ((2 * N + 2 * r : ℕ) : ℝ≥0∞) ^ (1 - 1 / p.toReal) * coeffConst (scalingFun m) 0 (2 * N - 1) p

/-- The constant of the Bernstein inequality is finite for `N ≥ 2`, since `φ` lies in every
`L_p` (`Daubechies.coeffConst_ne_top`). -/
theorem bernsteinConst_ne_top (hN : 2 ≤ N) (p : ℝ≥0∞) (r : ℕ) : bernsteinConst m p r ≠ ∞ :=
  ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_ne_zero (Nat.cast_ne_zero.2 (by omega))
    (ENNReal.natCast_ne_top _)) (coeffConst_ne_top _ _ (memLp_scalingFun m hN _))

section Lp

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **The Bernstein inequality for the scaling spaces**: for `N ≥ 2`, `1 ≤ p < ∞`, every order
`r`, every level `j`, every `a ∈ V_j` (`Daubechies.scalingSpace`) and every `t` with `2^j t ≤ 1`,
`ω_r(a, t)_p ≤ C ω_r(φ, 2^j t)_p ‖a‖_p` with the constant `C = Daubechies.bernsteinConst m p r`,
which is finite (`Daubechies.bernsteinConst_ne_top`) and independent of `j`, `a` and `t`.

The element `a` is almost everywhere the expansion `∑_k λ_k φ_{j,k}` of its coefficients
`λ_k = ⟨a, φ_{j,k}⟩` (`Daubechies.proj_eq_self_of_mem`), so for `|h| ≤ t`,
`Δ_h^r a = ∑_k λ_k (Δ_{2^j h}^r φ)_{j,k}` (`Daubechies.iterate_fwdDiff_expand`). As `|2^j h| ≤ 1`,
the generator `Δ_{2^j h}^r φ` vanishes outside `[-r, 2N - 1 + r]`
(`Daubechies.higherDiff_scalingFun_eq_zero`), and the upper estimate of expansions
(`Daubechies.eLpNorm_expand_le`) and the coefficient estimate
(`Daubechies.dyadicWeight_mul_lqNorm_coeffFun_le`) give
`‖Δ_h^r a‖_p ≤ (2N + 2r)^(1 - 1/p) ‖Δ_{2^j h}^r φ‖_p 2^(j(1/2 - 1/p)) ‖λ‖_{ℓ_p}`
`≤ C ‖Δ_{2^j h}^r φ‖_p ‖a‖_p`, where the dyadic weights cancel. -/
theorem modulus_mem_scalingSpace_le (hN : 2 ≤ N) (hp : p ≠ ∞) (r : ℕ) {j : ℕ}
    {a : Lp ℂ p (volume : Measure ℝ)} (ha : a ∈ scalingSpace m p hN hp j) {t : ℝ}
    (ht : 2 ^ j * t ≤ 1) :
    Rd.modulus volume r p (a : ℝ → ℂ) t ≤
      bernsteinConst m p r * Rd.modulus volume r p (scalingFun m) (2 ^ j * t) * ‖a‖ₑ := by
  have hae : (a : ℝ → ℂ) =ᵐ[volume] projFun m j a := by
    have h := proj_apply_ae m hN hp j a
    rwa [proj_eq_self_of_mem m hN hp ha] at h
  rw [Rd.modulus_congr_ae hae]
  refine iSup₂_le fun h hh => ?_
  have h2 : (0 : ℝ) < 2 ^ j := by positivity
  have hHt : ‖(2 : ℝ) ^ j * h‖ ≤ 2 ^ j * t := by
    rw [norm_mul, Real.norm_of_nonneg h2.le]
    exact mul_le_mul_of_nonneg_left hh h2.le
  have hH : |(2 : ℝ) ^ j * h| ≤ 1 := (Real.norm_eq_abs _ ▸ hHt).trans ht
  have hexp := eLpNorm_expand_le
    (continuous_iterate_fwdDiff (continuous_scalingFun m hN) r
      ((2 : ℝ) ^ j * h)).aestronglyMeasurable
    (fun x hx => higherDiff_scalingFun_eq_zero m hN r hH hx) (Fact.out : 1 ≤ p) hp j
    (coeffFun (scalingFun m) j a)
  have hcoef := dyadicWeight_mul_lqNorm_coeffFun_le
    (continuous_scalingFun m hN).aestronglyMeasurable (fun _ hx => scalingFun_eq_zero m hN hx)
    (Fact.out : 1 ≤ p) hp (Lp.aestronglyMeasurable a) j
  rw [natCeil_higherDiff_support_add_one (by omega)] at hexp
  rw [projFun, iterate_fwdDiff_expand (fun _ hx => scalingFun_eq_zero m hN hx)]
  calc eLpNorm (expand ((fwdDiff (2 ^ j * h))^[r] (scalingFun m)) j
        (coeffFun (scalingFun m) j a)) p volume
      ≤ ((2 * N + 2 * r : ℕ) : ℝ≥0∞) ^ (1 - 1 / p.toReal) *
          eLpNorm ((fwdDiff (2 ^ j * h))^[r] (scalingFun m)) p volume *
          (dyadicWeight (1 / 2 - 1 / p.toReal) j *
            ENNReal.lqNorm p (fun k => ‖coeffFun (scalingFun m) j a k‖ₑ)) := by
        rw [← mul_assoc]
        exact hexp
    _ ≤ ((2 * N + 2 * r : ℕ) : ℝ≥0∞) ^ (1 - 1 / p.toReal) *
          Rd.modulus volume r p (scalingFun m) (2 ^ j * t) *
          (coeffConst (scalingFun m) 0 (2 * N - 1) p * ‖a‖ₑ) := by
        rw [Lp.eNorm_def]
        exact mul_le_mul' (mul_le_mul_right (Rd.eLpNorm_higherDiff_le_modulus hHt) _) hcoef
    _ = bernsteinConst m p r * Rd.modulus volume r p (scalingFun m) (2 ^ j * t) * ‖a‖ₑ := by
        rw [bernsteinConst]
        ring

end Lp

/-! ### Bernstein bounds for the scaling function -/

/-- **A Bernstein bound of order `θ`** for the scaling function `φ` in `L_p`, with differences
of order `r`: there is a finite constant `K` with `ω_r(φ, t)_p ≤ K t^θ` for all `0 < t ≤ 1`.
It is a hypothesis on the mask; the regularity theorems for `φ` prove it
(`Daubechies.bernsteinBound_of_le_two`, `Daubechies.bernsteinBound_interp`), for instance for
`N = 2` and `N = 3` with `p ≤ 2` and for D4 with `p ≥ 2` (`Daubechies.bernsteinBound_order_two`,
`Daubechies.bernsteinBound_order_three`, `Daubechies.bernsteinBound_d4`), and a Bernstein bound
gives the inverse inequality of the Daubechies scheme (`Daubechies.inverse_scheme`). -/
def BernsteinBound (p : ℝ≥0∞) (θ : ℝ) (r : ℕ) : Prop :=
  ∃ K : ℝ≥0∞, K ≠ ∞ ∧ ∀ t ∈ Set.Ioc (0 : ℝ) 1,
    Rd.modulus volume r p (scalingFun m) t ≤ K * ENNReal.ofReal (t ^ θ)

/-- **Lower orders**: a Bernstein bound of order `θ` is one of every order `θ₁ ≤ θ`, since
`t^θ ≤ t^θ₁` for `0 < t ≤ 1`. -/
theorem BernsteinBound.mono {p : ℝ≥0∞} {θ θ₁ : ℝ} {r : ℕ} (hB : BernsteinBound m p θ r)
    (hθ : θ₁ ≤ θ) : BernsteinBound m p θ₁ r := by
  obtain ⟨K, hK, hmod⟩ := hB
  exact ⟨K, hK, fun t ht => (hmod t ht).trans (mul_le_mul_right
    (ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_ge ht.1 ht.2 hθ)) K)⟩

/-- **Bernstein bounds for `p ≤ 2`**: let `N ≥ 2`, `p ≤ 2`, let `T^n 1 ≤ C λ^n` be a growth bound
for the transfer operator (`Daubechies.TransferGrowth`), and let `s ∈ ℝ`, `r ∈ ℕ` with
`0 ≤ s ≤ r` and `s < N - log₄ λ`. Then `φ` has a Bernstein bound of order `s` in `L_p` with
differences of order `r` (`Daubechies.modulus_scalingFun_le_two`). -/
theorem bernsteinBound_of_le_two (hN : 2 ≤ N) {p : ℝ≥0∞} (hp2 : p ≤ 2) {lam C s : ℝ} {r : ℕ}
    (hg : TransferGrowth N lam C) (hs0 : 0 ≤ s) (hs : s < N - Real.logb 4 lam) (hsr : s ≤ r) :
    BernsteinBound m p s r :=
  modulus_scalingFun_le_two m hN hp2 hg hs0 hs hsr

/-- **Bernstein bounds for `p ≥ 2`** (Fourier route): let `N ≥ 2`, `2 ≤ p ≤ ∞`, let
`T^n 1 ≤ C λ^n` be a growth bound for the transfer operator (`Daubechies.TransferGrowth`), and
let `s, a ∈ ℝ`, `r ∈ ℕ` with `0 ≤ s ≤ r`, `s < N - log₄ λ`, `0 ≤ a ≤ r` and
`a < N - log₄ λ - 1/2`. Then `φ` has a Bernstein bound of order `θ = (2/p) s + (1 - 2/p) a` in
`L_p` with differences of order `r` (`Daubechies.modulus_scalingFun_interp`). -/
theorem bernsteinBound_interp (hN : 2 ≤ N) {p : ℝ≥0∞} (hp2 : 2 ≤ p) {lam C s a : ℝ} {r : ℕ}
    (hg : TransferGrowth N lam C) (hs0 : 0 ≤ s) (hs : s < N - Real.logb 4 lam) (hsr : s ≤ r)
    (ha0 : 0 ≤ a) (har : a ≤ r) (ha : a < N - Real.logb 4 lam - 1 / 2) :
    BernsteinBound m p (2 / p.toReal * s + (1 - 2 / p.toReal) * a) r :=
  modulus_scalingFun_interp m hN hp2 hg hs0 hs hsr ha0 har ha

/-- **Bernstein bounds for `p ≥ 2` from a Hölder estimate**: let `N ≥ 2`, `2 ≤ p ≤ ∞`, let
`T^n 1 ≤ C λ^n` be a growth bound for the transfer operator (`Daubechies.TransferGrowth`), let
`s ∈ ℝ` and an order `r ≥ 1` with `0 ≤ s ≤ r` and `s < N - log₄ λ`, and suppose
`|φ(x) - φ(y)| ≤ K₀ |x - y|^a` for all `x, y ∈ ℝ`, with `a ≥ 0`. Then `φ` has a Bernstein bound
of order `θ = (2/p) s + (1 - 2/p) a` in `L_p` with differences of order `r`
(`Daubechies.modulus_scalingFun_interp_of_holder`). -/
theorem bernsteinBound_interp_of_holder (hN : 2 ≤ N) {p : ℝ≥0∞} (hp2 : 2 ≤ p)
    {lam C s a K₀ : ℝ} {r : ℕ} (hr : 1 ≤ r) (hg : TransferGrowth N lam C) (hs0 : 0 ≤ s)
    (hs : s < N - Real.logb 4 lam) (hsr : s ≤ r) (ha0 : 0 ≤ a)
    (hK : ∀ x y : ℝ, ‖scalingFun m x - scalingFun m y‖ ≤ K₀ * |x - y| ^ a) :
    BernsteinBound m p (2 / p.toReal * s + (1 - 2 / p.toReal) * a) r :=
  modulus_scalingFun_interp_of_holder m hN hp2 hr hg hs0 hs hsr ha0 hK

/-- **Bernstein bounds of order two, `p ≤ 2`**: for every Daubechies mask of order `N = 2`, every
`p ≤ 2`, every real `s` with `0 ≤ s < 1` and every order `r ≥ s`, `φ` has a Bernstein bound of
order `s` in `L_p` with differences of order `r`
(`Daubechies.modulus_scalingFun_le_two_order_two`). -/
theorem bernsteinBound_order_two (m : Mask 2) {p : ℝ≥0∞} (hp2 : p ≤ 2) {s : ℝ} {r : ℕ}
    (hs0 : 0 ≤ s) (hs : s < 1) (hsr : s ≤ r) : BernsteinBound m p s r :=
  modulus_scalingFun_le_two_order_two m hp2 hs0 hs hsr

/-- **Bernstein bounds of order three, `p ≤ 2`**: for every Daubechies mask of order `N = 3`,
every `p ≤ 2`, every real `s` with `0 ≤ s < 3 - log₂ 3 ≈ 1.415` and every order `r ≥ s`, `φ` has
a Bernstein bound of order `s` in `L_p` with differences of order `r`
(`Daubechies.modulus_scalingFun_le_two_order_three`). -/
theorem bernsteinBound_order_three (m : Mask 3) {p : ℝ≥0∞} (hp2 : p ≤ 2) {s : ℝ} {r : ℕ}
    (hs0 : 0 ≤ s) (hs : s < 3 - Real.logb 2 3) (hsr : s ≤ r) : BernsteinBound m p s r :=
  modulus_scalingFun_le_two_order_three m hp2 hs0 hs hsr

/-- **Bernstein bounds for D4, `p ≥ 2`**: for the mask D4 (`Daubechies.d4`), every
`2 ≤ p ≤ ∞`, all real `s, a` with `0 ≤ s < 1` and `0 ≤ a ≤ 2 - log₂(1 + √3) ≈ 0.5500`, and every
order `r ≥ 1` with `s ≤ r`, `φ` has a Bernstein bound of order `θ = (2/p) s + (1 - 2/p) a` in
`L_p` with differences of order `r`. The Hölder estimate is the one of the matrix method
(`Daubechies.holder_d4`), the `L²` bound comes from the growth bound `T^n 1 ≤ 4^n`
(`Daubechies.transferGrowth_two`, exponent `2 - log₄ 4 = 1`), and
`Daubechies.bernsteinBound_interp_of_holder` interpolates. -/
theorem bernsteinBound_d4 {p : ℝ≥0∞} (hp2 : 2 ≤ p) {s a : ℝ} {r : ℕ} (hr : 1 ≤ r)
    (hs0 : 0 ≤ s) (hs : s < 1) (hsr : s ≤ r) (ha0 : 0 ≤ a)
    (ha : a ≤ 2 - Real.logb 2 (1 + √3)) :
    BernsteinBound d4 p (2 / p.toReal * s + (1 - 2 / p.toReal) * a) r := by
  obtain ⟨K₀, hK⟩ := holder_d4 ha0 ha
  exact bernsteinBound_interp_of_holder d4 le_rfl hp2 hr transferGrowth_two hs0
    (by rw [Nat.cast_ofNat, two_sub_logb_four_four]; exact hs) hsr ha0 hK

/-! ### The inverse inequality of the Daubechies scheme -/

/-- **Dyadic scales of two levels**: `2^j 2^(-k) = 2^(-(k - j))` for `j ≤ k`. -/
theorem two_pow_mul_one_div_two_pow {j k : ℕ} (hjk : j ≤ k) :
    (2 : ℝ) ^ j * (1 / 2 ^ k) = 1 / 2 ^ (k - j) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hjk
  rw [Nat.add_sub_cancel_left, pow_add]
  field_simp

section Lp

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **The modulus of an element of `V_j` at the dyadic scales `2^(-k)`, `k ≥ j`**: let `N ≥ 2`,
`1 ≤ p < ∞`, and let `ω_r(φ, t)_p ≤ K t^θ` for all `0 < t ≤ 1`. Then for all levels `j ≤ k` and
every `a ∈ V_j` (`Daubechies.scalingSpace`), `ω_r(a, 2^(-k))_p ≤ C K 2^(-(k-j)θ) ‖a‖_p` with
`C = Daubechies.bernsteinConst m p r`. This is the Bernstein inequality
`Daubechies.modulus_mem_scalingSpace_le` at `t = 2^(-k)`, where `2^j t = 2^(-(k-j)) ∈ (0, 1]`. -/
theorem lpModulus_le_of_mem_scalingSpace (hN : 2 ≤ N) (hp : p ≠ ∞) {θ : ℝ} {r : ℕ}
    {K : ℝ≥0∞} (hK : ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      Rd.modulus volume r p (scalingFun m) t ≤ K * ENNReal.ofReal (t ^ θ))
    {j k : ℕ} (hjk : j ≤ k) {a : Lp ℂ p (volume : Measure ℝ)}
    (ha : a ∈ scalingSpace m p hN hp j) :
    Rd.lpModulus p r a k ≤ bernsteinConst m p r * K * dyadicWeight (-θ) (k - j) * ‖a‖ₑ := by
  have hmem : (2 : ℝ) ^ j * (1 / 2 ^ k) ∈ Set.Ioc (0 : ℝ) 1 := by
    rw [two_pow_mul_one_div_two_pow hjk]
    exact ⟨by positivity, (div_le_one (by positivity)).2 (one_le_pow₀ one_le_two)⟩
  calc Rd.lpModulus p r a k = Rd.modulus volume r p (a : ℝ → ℂ) (1 / 2 ^ k) := rfl
    _ ≤ bernsteinConst m p r * Rd.modulus volume r p (scalingFun m) (2 ^ j * (1 / 2 ^ k)) *
          ‖a‖ₑ := modulus_mem_scalingSpace_le m hN hp r ha hmem.2
    _ ≤ bernsteinConst m p r * (K * ENNReal.ofReal (((2 : ℝ) ^ j * (1 / 2 ^ k)) ^ θ)) *
          ‖a‖ₑ := by
        gcongr
        exact hK _ hmem
    _ = bernsteinConst m p r * K * dyadicWeight (-θ) (k - j) * ‖a‖ₑ := by
        rw [two_pow_mul_one_div_two_pow hjk, ENNReal.ofReal_one_div_two_pow_rpow]
        ring

/-- **The inverse inequality of the Daubechies scheme** (Bernstein): let `N ≥ 2`, `1 ≤ p < ∞`,
and let `φ` have a Bernstein bound of order `θ` with differences of order `r`
(`Daubechies.BernsteinBound`). Then there is a finite constant `C_B` with
`ω_r(a, 2^(-k))_p ≤ C_B 2^(-(k-j)θ) ‖a‖_p` for all `j, k ∈ ℕ` and every approximant `a` of
complexity `2^j` of the Daubechies scheme (`Daubechies.scheme`; these are the elements of
`V_j`), where `k - j` is truncated at `0`. For `k ≥ j` this is
`Daubechies.lpModulus_le_of_mem_scalingSpace`; for `k < j` the weight is `1` and
`ω_r(a, t)_p ≤ 2^r ‖a‖_p` (`Rd.lpModulus_le`). This is the inverse inequality of
`ApproximationScheme.ModulusData` for the modulus `Rd.lpModulus p r`. -/
theorem inverse_scheme (hN : 2 ≤ N) (hp : p ≠ ∞) {θ : ℝ} {r : ℕ}
    (hB : BernsteinBound m p θ r) :
    ∃ CB : ℝ≥0∞, CB ≠ ∞ ∧ ∀ j k : ℕ, ∀ a ∈ scheme m p hN hp (2 ^ j),
      Rd.lpModulus p r a k ≤ CB * dyadicWeight (-θ) (k - j) * ‖a‖ₑ := by
  obtain ⟨K, hK, hmod⟩ := hB
  refine ⟨bernsteinConst m p r * K + 2 ^ r,
    ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top (bernsteinConst_ne_top m hN p r) hK, by simp⟩,
    fun j k a ha => ?_⟩
  rcases lt_or_ge k j with hkj | hjk
  · rw [Nat.sub_eq_zero_of_le hkj.le, ENNReal.dyadicWeight_zero_right, mul_one]
    exact (Rd.lpModulus_le r a k).trans (by gcongr; exact le_add_self)
  · exact (lpModulus_le_of_mem_scalingSpace m hN hp hmod hjk
      ((mem_scheme_two_pow m).1 ha)).trans (by gcongr; exact le_self_add)

end Lp

end Daubechies
