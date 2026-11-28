/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Wavelets.Examples.Haar
public import LeanPool.FunctionSpaces.Domains.Interval.PiecewisePeriodic
public import LeanPool.FunctionSpaces.ApproximationSpaces.Transfer

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Haar coefficients and Besov spaces on the interval and on the circle

The Haar scheme of `FunctionSpaces.Wavelets.Examples.Haar` (step functions on the dyadic
intervals) and the scheme of dyadic piecewise polynomials of degree `< 1` (`Interval.ppScheme p 1`)
are the same scheme in `L_p[0, 1]` (`Haar.scheme_eq_ppScheme`): a function measurable for the
dyadic `σ`-algebra of level `j` is a step function on the dyadic intervals of level `j`, and
conversely. Hence the two schemes have the same approximation spaces
(`Haar.memApprox_ppScheme_one_iff`).

Together with the characterisations through moduli of smoothness this gives, for `1 ≤ p < ∞`,
`1 ≤ q ≤ ∞` and `0 < s < 1/p`, three equivalent descriptions of one space:

* `‖f‖_p + ‖(2^(ks) ω_1(f, 2^(-k), [0, 1])_p)_k‖_{ℓ_q} < ∞` (Besov space on the interval),
* `‖f‖_p + ‖(2^(ks) ω_1^per(f, 2^(-k))_p)_k‖_{ℓ_q} < ∞` (Besov space on the circle),
* `|∫_0^1 f| + ‖(2^(k(s+1/2-1/p)) ‖(⟨f, h_{k,m}⟩)_{m<2^k}‖_{ℓ_p})_k‖_{ℓ_q} < ∞` (Haar coefficients)

(`Haar.lqNorm_modulus_lt_top_iff_haarCoeff`, `Haar.lqNorm_perModulus_lt_top_iff_haarCoeff`).
-/

@[expose] public section

open MeasureTheory Set Polynomial
open scoped ENNReal
open ENNReal (dyadicWeight)

namespace Haar

open Interval

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A polynomial of degree `< 1` is constant. -/
theorem polyFun_of_mem_degreeLT_one {P : ℂ[X]} (hP : P ∈ degreeLT ℂ 1) (x : ℝ) :
    polyFun P x = P.coeff 0 := by
  rw [polyFun, eq_C_of_degree_le_zero (Nat.WithBot.lt_one_iff_le_zero.1 (mem_degreeLT.1 hP)),
    eval_C, coeff_C_zero]

/-- On `[0, 1)` the dyadic index is the floor of `2^j x`. -/
theorem dyadicIndex_eq_floor {j : ℕ} {x : ℝ} (hx : x ∈ Ico (0 : ℝ) 1) :
    dyadicIndex j x = (⌊2 ^ j * x⌋₊ : ℤ) :=
  (Int.natCast_floor_eq_floor (mul_nonneg (by positivity) hx.1)).symm

/-- The dyadic index of a left endpoint `n 2^(-j)` is `n`. -/
theorem dyadicIndex_natCast_div (j n : ℕ) : dyadicIndex j ((n : ℝ) / 2 ^ j) = n := by
  rw [dyadicIndex, mul_div_cancel₀ _ (by positivity), Int.floor_natCast]

/-- A piecewise constant function agrees almost everywhere on `[0, 1]` with its step
function. -/
theorem ppFun_ae_eq_stepFun {Q : ℕ → ℂ[X]} (hQ : ∀ n, Q n ∈ degreeLT ℂ 1) (j : ℕ) :
    ppFun j Q =ᵐ[vol] stepFun (ppFun j Q) j := by
  filter_upwards [ae_mem_Ico_unitVol] with x hx
  obtain ⟨hmem, hlt⟩ := mem_dyadicIco_floor (k := j) hx
  have hend : ((⌊2 ^ j * x⌋₊ : ℕ) : ℝ) / 2 ^ j ∈ dyadicIco j ⌊2 ^ j * x⌋₊ := by
    rw [mem_dyadicIco, mul_div_cancel₀ _ (by positivity)]
    exact ⟨le_rfl, lt_add_one _⟩
  rw [stepFun, dyadicIndex_eq_floor hx, Int.cast_natCast, ppFun_eq_of_mem Q hlt hmem,
    ppFun_eq_of_mem Q hlt hend, polyFun_of_mem_degreeLT_one (hQ _),
    polyFun_of_mem_degreeLT_one (hQ _)]

/-- A function measurable for the dyadic `σ`-algebra of level `j` is almost everywhere on
`[0, 1]` a piecewise constant function. -/
theorem ae_eq_ppFun_of_stronglyMeasurable {j : ℕ} {g : ℝ → ℂ}
    (hg : StronglyMeasurable[dyadicFiltration j] g) :
    g =ᵐ[vol] ppFun j (fun m => C (g ((m : ℝ) / 2 ^ j))) := by
  filter_upwards [ae_mem_Ico_unitVol] with x hx
  obtain ⟨hmem, hlt⟩ := mem_dyadicIco_floor (k := j) hx
  rw [ppFun_eq_of_mem _ hlt hmem, polyFun, eval_C]
  have hg' : StronglyMeasurable[MeasurableSpace.comap (dyadicIndex j) ⊤] g := hg
  refine (hg'.eq_of_comap_top ?_).symm
  rw [dyadicIndex_natCast_div, dyadicIndex_eq_floor hx]

/-- The piecewise constant approximants are Haar approximants: a piecewise constant function
of level `j` agrees almost everywhere with its step function. -/
theorem mem_scheme_of_mem_ppScheme {n : ℕ} {a : Lp ℂ p unitVol} (ha : a ∈ ppScheme p 1 n) :
    a ∈ scheme p n := by
  rcases eq_or_ne n 0 with rfl | hn
  · rw [mem_ppScheme_zero.1 ha]
    exact (scheme p).zero_mem 0
  · obtain ⟨Q, hQ, hae⟩ := (mem_ppScheme hn).1 ha
    rw [dyadicFiltration.mem_scheme hn, mem_lpMeas_iff_aestronglyMeasurable]
    exact ⟨stepFun (ppFun (Nat.log 2 n) Q) (Nat.log 2 n), stronglyMeasurable_stepFun _ _,
      hae.trans (ppFun_ae_eq_stepFun hQ _)⟩

/-- The Haar approximants are piecewise constant approximants: a function measurable for the
dyadic `σ`-algebra of level `j` is a piecewise constant function of level `j`. -/
theorem mem_ppScheme_of_mem_scheme {n : ℕ} {a : Lp ℂ p unitVol} (ha : a ∈ scheme p n) :
    a ∈ ppScheme p 1 n := by
  rcases eq_or_ne n 0 with rfl | hn
  · rw [mem_ppScheme_zero, ApproximationScheme.mem_ofMonotoneSubmodules_zero.1 ha]
  · rw [mem_ppScheme hn]
    rw [dyadicFiltration.mem_scheme hn, mem_lpMeas_iff_aestronglyMeasurable] at ha
    obtain ⟨g, hg, hag⟩ := ha
    exact ⟨fun m => C (g ((m : ℝ) / 2 ^ Nat.log 2 n)), fun m =>
      mem_degreeLT.2 (degree_C_le.trans_lt (by norm_num)),
      hag.trans (ae_eq_ppFun_of_stronglyMeasurable hg)⟩

/-- **The Haar scheme is the piecewise constant scheme** in `L_p[0, 1]`: both have the same
approximants of every complexity. -/
theorem scheme_eq_ppScheme : scheme p = ppScheme p 1 :=
  ApproximationScheme.ext fun _ => Subset.antisymm (fun _ => mem_ppScheme_of_mem_scheme)
    (fun _ => mem_scheme_of_mem_ppScheme)

/-- **The Haar scheme and the piecewise constant scheme have the same approximation spaces**:
`f ∈ A^s_q` for the piecewise constants in `L_p[0, 1]` iff `f ∈ A^s_q` for the Haar scheme
(`Haar.scheme_eq_ppScheme`). -/
theorem memApprox_ppScheme_one_iff {s : ℝ} {q : ℝ≥0∞} (f : Lp ℂ p unitVol) :
    (ppScheme p 1).MemApprox s q f ↔ (scheme p).MemApprox s q f := by
  rw [scheme_eq_ppScheme]

/-- **Besov spaces on the interval through Haar coefficients.** For `1 ≤ p < ∞`, `1 ≤ q ≤ ∞` and
`0 < s < 1/p`, the Besov quasi-norm `‖f‖_p + ‖(2^(ks) ω_1(f, 2^(-k), [0, 1])_p)_k‖_{ℓ_q}` of
`f ∈ L_p[0, 1]` is finite iff
`|∫_0^1 f| + ‖(2^(k(s+1/2-1/p)) ‖(⟨f, h_{k,m}⟩)_{m<2^k}‖_{ℓ_p})_k‖_{ℓ_q} < ∞`. -/
theorem lqNorm_modulus_lt_top_iff_haarCoeff (hp : p ≠ ∞) {s : ℝ} (hs : 0 < s)
    (hsp : s < 1 / p.toReal) {q : ℝ≥0∞} (hq : 1 ≤ q) (f : Lp ℂ p unitVol) :
    ‖f‖ₑ + ENNReal.lqNorm q (fun k => dyadicWeight s k * lpModulus p 1 f k) < ∞ ↔
      ‖∫ x, f x ∂vol‖ₑ + ENNReal.lqNorm q (fun k =>
        dyadicWeight (s + (1 / 2 - 1 / p.toReal)) k *
          ENNReal.lqNorm p (fun m : Fin (2 ^ k) => ‖haarCoeff f k ((m : ℕ) : ℤ)‖ₑ)) < ∞ := by
  rw [← memApprox_ppScheme_iff le_rfl hp hq hs.le hsp f, memApprox_ppScheme_one_iff,
    memApprox_iff_haarCoeff hp hs hq]

/-- **Besov spaces on the circle through Haar coefficients.** For `1 ≤ p < ∞`, `1 ≤ q ≤ ∞` and
`0 < s < 1/p`, the periodic Besov quasi-norm `‖f‖_p + ‖(2^(ks) ω_1^per(f, 2^(-k))_p)_k‖_{ℓ_q}`
of `f ∈ L_p(𝕋) = L_p[0, 1]` is finite iff
`|∫_0^1 f| + ‖(2^(k(s+1/2-1/p)) ‖(⟨f, h_{k,m}⟩)_{m<2^k}‖_{ℓ_p})_k‖_{ℓ_q} < ∞`. -/
theorem lqNorm_perModulus_lt_top_iff_haarCoeff (hp : p ≠ ∞) {s : ℝ} (hs : 0 < s)
    (hsp : s < 1 / p.toReal) {q : ℝ≥0∞} (hq : 1 ≤ q) (f : Lp ℂ p unitVol) :
    ‖f‖ₑ + ENNReal.lqNorm q (fun k => dyadicWeight s k * lpPerModulus p 1 f k) < ∞ ↔
      ‖∫ x, f x ∂vol‖ₑ + ENNReal.lqNorm q (fun k =>
        dyadicWeight (s + (1 / 2 - 1 / p.toReal)) k *
          ENNReal.lqNorm p (fun m : Fin (2 ^ k) => ‖haarCoeff f k ((m : ℕ) : ℤ)‖ₑ)) < ∞ := by
  rw [← memApprox_ppScheme_iff_per le_rfl hp hq hs.le hsp f, memApprox_ppScheme_one_iff,
    memApprox_iff_haarCoeff hp hs hq]

end Haar
