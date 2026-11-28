/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Domains.Interval.PolyDifferences
public import LeanPool.FunctionSpaces.Domains.Interval.SplineInverse
public import Mathlib.MeasureTheory.Function.Floor

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Differences of every order of piecewise polynomials and splines

The inverse inequalities of `FunctionSpaces.Domains.Interval.PiecewiseInverse` and
`FunctionSpaces.Domains.Interval.SplineInverse` bound the difference `Δ_h^r` whose order `r` is
the order of the pieces. The isotropic modulus on the cube needs differences of every order
`m ≤ r` in each variable, and these do not vanish inside the pieces.

* **Piecewise polynomials**, `1 ≤ m ≤ r`, `0 ≤ h ≤ 2^(-j)`:
  `‖Δ_h^m u‖_{L_p[0, 1 - mh]} ≤ C (2^j h)^(1/p) ‖u‖_p`
  (`Interval.exists_eLpNorm_higherDiff_ppFun_le`). On the strips of width `rh` left of the knots
  the difference is bounded by the neighbouring pieces, as for `m = r`
  (`Interval.enorm_higherDiff_le_of_isPiecewisePoly_of_le`); inside a piece the difference bound
  of the polynomials (`Interval.DiffBound`) gives the factor `(2^j h)^m ≤ 2^j h`.
* **Splines** of order `r`, `1 ≤ m ≤ r - 1`, `0 ≤ h ≤ 2^(-j)`:
  `‖Δ_h^m u‖_{L_p[0, 1 - mh]} ≤ C (2^j h)^m ‖u‖_p`
  (`Interval.exists_eLpNorm_higherDiff_spline_le_of_lt`). On `[x, x + mh]` the spline is the
  piece at `x` plus jumps `c (y - ξ)_+^(r-1)` at knots `ξ > x`
  (`Interval.higherDiff_eq_add_sum_jumps`); the piece contributes `(2^j h)^m` by the difference
  bound, and a jump `|c| 2^m (mh)^(r-1)`, which is of order `(2^j h)^(r-1) ≤ (2^j h)^m` by the
  bound of the jump terms of every order
  (`Interval.enorm_jumpCoeff_mul_higherDiff_truncPow_le_any_order` in
  `FunctionSpaces.Domains.Interval.SplineInverse`). So the bound holds at every point
  (`Interval.enorm_higherDiff_spline_le_of_lt`), not only on strips; this is the smoothness
  `C^(r-2)` of splines.

For steps `t` of either sign the difference lives on `{x ∈ [0, 1] : x + mt ∈ [0, 1]}`
(`Interval.stepRegion`), and its norm there depends only on `|t|`
(`Interval.eLpNorm_higherDiff_stepRegion_eq`), since `Δ_{-t}^m f(x) = (-1)^m Δ_t^m f(x - mt)`
(`Interval.higherDiff_neg`).
-/

@[expose] public section

open MeasureTheory Set Polynomial
open Rd (higherDiff higherDiff_def measurable_higherDiff)
open scoped ENNReal

namespace Interval

/-! ### Steps of either sign -/

/-- **Negative steps**: `Δ_{-t}^m f(x) = (-1)^m Δ_t^m f(x - mt)` (`Rd.higherDiff_neg` on `ℝ`). -/
theorem higherDiff_neg (m : ℕ) (t : ℝ) (f : ℝ → ℂ) (x : ℝ) :
    higherDiff m (-t) f x = (-1 : ℂ) ^ m * higherDiff m t f (x - m * t) := by
  rw [higherDiff_def, higherDiff_def, Rd.higherDiff_neg, nsmul_eq_mul]

/-- The **step region** of a difference of order `m` and step `t`: the points `x ∈ [0, 1]` with
`x + mt ∈ [0, 1]`, for `t` of either sign. -/
def stepRegion (m : ℕ) (t : ℝ) : Set ℝ := Icc (max 0 (-(m * t))) (min 1 (1 - m * t))

/-- `x` lies in the step region iff `x` and `x + mt` lie in `[0, 1]`. -/
theorem mem_stepRegion {m : ℕ} {t x : ℝ} :
    x ∈ stepRegion m t ↔ x ∈ Icc (0 : ℝ) 1 ∧ x + m * t ∈ Icc (0 : ℝ) 1 := by
  rw [stepRegion, mem_Icc, max_le_iff, le_min_iff, mem_Icc, mem_Icc]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨⟨h1, h3⟩, by linarith, by linarith⟩
  · rintro ⟨⟨h1, h3⟩, h5, h6⟩
    exact ⟨⟨h1, by linarith⟩, h3, by linarith⟩

/-- For `t ≥ 0` the step region is `[0, 1 - mt]`. -/
theorem stepRegion_of_nonneg (m : ℕ) {t : ℝ} (ht : 0 ≤ t) : stepRegion m t = Icc 0 (1 - m * t) := by
  have hmt : 0 ≤ (m : ℝ) * t := mul_nonneg (Nat.cast_nonneg m) ht
  rw [stepRegion, max_eq_left (by linarith), min_eq_right (by linarith)]

/-- For `t < 0` the step region is `[-mt, 1]`. -/
theorem stepRegion_of_neg (m : ℕ) {t : ℝ} (ht : t < 0) : stepRegion m t = Icc (-(m * t)) 1 := by
  have hmt : (m : ℝ) * t ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg m) ht.le
  rw [stepRegion, max_eq_right (by linarith), min_eq_left (by linarith)]

/-- **The step region is a step set**: `J(m, t) = [0, 1]_{mt}` (`Rd.stepSet`), since `x + lt`,
`l ≤ m`, lies between `x` and `x + mt`. -/
theorem stepRegion_eq_stepSet (m : ℕ) (t : ℝ) : stepRegion m t = Rd.stepSet (Icc 0 1) m t := by
  ext x
  rw [mem_stepRegion]
  simp only [Rd.stepSet, mem_ofPred_eq, smul_eq_mul]
  constructor
  · rintro ⟨⟨h0, h1⟩, h2, h3⟩ l hl
    have hl' : (l : ℝ) ≤ m := by exact_mod_cast hl
    rcases le_or_gt 0 t with ht | ht
    · exact ⟨by linarith [mul_nonneg (Nat.cast_nonneg l) ht],
        by linarith [mul_le_mul_of_nonneg_right hl' ht]⟩
    · exact ⟨by linarith [mul_le_mul_of_nonpos_right hl' ht.le],
        by linarith [mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg l) ht.le]⟩
  · intro hx
    exact ⟨by simpa using hx 0 (Nat.zero_le m), hx m le_rfl⟩

/-- **The norm of a difference depends only on the size of the step**:
`‖Δ_t^m u‖_{L_p(step region)} = ‖Δ_{|t|}^m u‖_{L_p[0, 1 - m|t|]}`
(`Rd.eLpNorm_indicator_stepSet_neg`). -/
theorem eLpNorm_higherDiff_stepRegion_eq (u : ℝ → ℂ) (p : ℝ≥0∞) (m : ℕ) (t : ℝ) :
    eLpNorm (higherDiff m t u) p (volume.restrict (stepRegion m t)) =
      eLpNorm (higherDiff m |t| u) p (volume.restrict (Icc 0 (1 - m * |t|))) := by
  rw [stepRegion_eq_stepSet, ← eLpNorm_indicator_eq_eLpNorm_restrict
      (Rd.measurableSet_stepSet measurableSet_Icc m t).nullMeasurableSet,
    ← eLpNorm_indicator_stepSet_Icc m (abs_nonneg t)]
  rcases le_or_gt 0 t with ht | ht
  · rw [abs_of_nonneg ht]
    rfl
  · rw [abs_of_neg ht, ← Rd.eLpNorm_indicator_stepSet_neg, neg_neg]
    rfl

/-! ### Tools for the local estimates -/

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **From an integral bound to an `L_p` bound**: `∫ |F|^p ≤ A^p σ B^p` gives
`‖F‖_p ≤ A σ^(1/p) B`. -/
theorem eLpNorm_le_of_lintegral_le_mul (hp : p ≠ ∞) {F : ℝ → ℂ} {μ : Measure ℝ}
    (hF : AEStronglyMeasurable F μ) {A σ B : ℝ≥0∞}
    (h : ∫⁻ x, ‖F x‖ₑ ^ p.toReal ∂μ ≤ A ^ p.toReal * σ * B ^ p.toReal) :
    eLpNorm F p μ ≤ A * σ ^ (1 / p.toReal) * B := by
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p)).ne'
  have hq : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  refine eLpNorm_le_of_lintegral_le hF hp0 hp (h.trans_eq ?_)
  rw [ENNReal.mul_rpow_of_nonneg _ _ hq.le, ENNReal.mul_rpow_of_nonneg _ _ hq.le,
    ← ENNReal.rpow_mul, one_div_mul_cancel hq.ne', ENNReal.rpow_one]

omit [Fact (1 ≤ p)] in
/-- `(G a^(1/p))^p = G^p a` for `p ≠ 0, ∞`. -/
theorem mul_rpow_one_div_rpow (hp0 : p ≠ 0) (hp : p ≠ ∞) (G a : ℝ≥0∞) :
    (G * a ^ (1 / p.toReal)) ^ p.toReal = G ^ p.toReal * a := by
  have hq : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  rw [ENNReal.mul_rpow_of_nonneg _ _ hq.le, ← ENNReal.rpow_mul, one_div_mul_cancel hq.ne',
    ENNReal.rpow_one]

/-- **Integral of a local bound**: `∫_{[0,1]} c M_{⌊2^j x⌋} dx ≤ c 2^(-j) ∑_{n < 2^j} M_n`. -/
theorem lintegral_localBound_le (j : ℕ) (c : ℝ≥0∞) (M : ℕ → ℝ≥0∞) :
    ∫⁻ x in Icc (0 : ℝ) 1, c * M ⌊2 ^ j * x⌋₊ ≤
      c * ENNReal.ofReal (1 / 2 ^ j) * ∑ n ∈ Finset.range (2 ^ j), M n := by
  refine (lintegral_Icc_le_sum_dyadicIco _ j).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun n _ => le_of_eq ?_
  calc ∫⁻ x in dyadicIco j n, c * M ⌊2 ^ j * x⌋₊ = ∫⁻ x in dyadicIco j n, c * M n :=
        setLIntegral_congr_fun (measurableSet_dyadicIco j n) fun x hx => by
          rw [floor_eq_of_mem_dyadicIco hx]
    _ = c * M n * volume (dyadicIco j n) := setLIntegral_const _ _
    _ = c * ENNReal.ofReal (1 / 2 ^ j) * M n := by
        rw [dyadicIco, Real.volume_Ico,
          show ((n : ℝ) + 1) / 2 ^ j - n / 2 ^ j = 1 / 2 ^ j by ring]
        ring

/-- The local masses of a piecewise polynomial of level `j`, summed over `n < 2^j`, are at most
`‖u‖_p^p`. -/
theorem sum_localMass_ppFun_le (hp : p ≠ ∞) (j : ℕ) (Q : ℕ → ℂ[X]) :
    ∑ n ∈ Finset.range (2 ^ j), localMass p j (ppFun j Q) n ≤
      eLpNorm (ppFun j Q) p unitVol ^ p.toReal :=
  (sum_le_tsum _).trans (tsum_localMass_ppFun_le hp j Q)

/-! ### Pointwise bounds -/

/-- **Differences inside a piece**: if `x, …, x + mh` lie in the dyadic interval `I_{k,n}` of `x`,
`n = ⌊2^k x⌋`, then `|Δ_h^m u(x)| ≤ K (2^k h)^m 2^(k/p) M_n^(1/p)`, by the difference bound of
the polynomial piece (`Interval.DiffBound`). -/
theorem enorm_higherDiff_le_of_mem_piece {r k m : ℕ} {u : ℝ → ℂ} (hu : IsPiecewisePoly r k u)
    {K : ℝ≥0∞} (hK : DiffBound p r m K) (hp : p ≠ ∞) {h x : ℝ} (hh0 : 0 ≤ h) (hx : 0 ≤ x)
    (hgood : x + m * h < ((⌊2 ^ k * x⌋₊ : ℝ) + 1) / 2 ^ k) :
    ‖higherDiff m h u x‖ₑ ≤ K * ENNReal.ofReal (2 ^ k * h) ^ m *
      ENNReal.ofReal (2 ^ k) ^ (1 / p.toReal) * localMass p k u ⌊2 ^ k * x⌋₊ ^ (1 / p.toReal) := by
  obtain ⟨P, hP, hPu⟩ := hu ⌊2 ^ k * x⌋₊
  have hpos : (0 : ℝ) < 2 ^ k := by positivity
  have hfl : (⌊2 ^ k * x⌋₊ : ℝ) ≤ 2 ^ k * x := Nat.floor_le (by positivity)
  have h1 := higherDiff_eq_of_mem_piece hPu hh0 hx hgood
  have hL : (0 : ℝ) < 1 / 2 ^ k := by positivity
  have hux : (⌊2 ^ k * x⌋₊ : ℝ) / 2 ^ k ≤ x := by rw [div_le_iff₀ hpos]; linarith
  have hxu : x + m * h ≤ (⌊2 ^ k * x⌋₊ : ℝ) / 2 ^ k + 2 * (1 / 2 ^ k) := by
    have : ((⌊2 ^ k * x⌋₊ : ℝ) + 1) / 2 ^ k = (⌊2 ^ k * x⌋₊ : ℝ) / 2 ^ k + 1 / 2 ^ k :=
      add_div _ _ _
    linarith
  have hb := hK P hP ((⌊2 ^ k * x⌋₊ : ℝ) / 2 ^ k) hL hh0 x hux hxu
  rw [h1]
  rwa [show h / (1 / 2 ^ k) = 2 ^ k * h by field_simp,
    show (1 / (2 : ℝ) ^ k)⁻¹ = 2 ^ k by rw [one_div, inv_inv],
    eLpNorm_piece_eq_localMass hp hPu] at hb

/-! ### Piecewise polynomials -/

/-- **The pointwise bound for differences of piecewise polynomials**: for `m ≤ r`,
`0 ≤ h ≤ 2^(-j)` and `x ∈ [0, 1 - mh]`, `|Δ_h^m u(x)|^p` is at most the strip bound of the
neighbouring masses `∑_{l ≤ r} M_{n+l}` (`Interval.enorm_higherDiff_le_of_isPiecewisePoly_of_le`)
plus `(K_m (2^j h)^m 2^(j/p))^p M_n` for the piece of `x`
(`Interval.enorm_higherDiff_le_of_mem_piece`), where `n = ⌊2^j x⌋`. -/
theorem enorm_higherDiff_rpow_le_strip_add_piece (hp : p ≠ ∞) {r j m : ℕ} (hmr : m ≤ r)
    {u : ℝ → ℂ} (hu : IsPiecewisePoly r j u) {K Km : ℝ≥0∞} (hK : NikolskiiBound p r K)
    (hKm : DiffBound p r m Km) {h : ℝ} (hh0 : 0 ≤ h) (hh : h ≤ 1 / 2 ^ j) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) (1 - m * h)) :
    ‖higherDiff m h u x‖ₑ ^ p.toReal ≤
      stripBound j r h ((2 ^ m * K * ENNReal.ofReal (2 ^ j) ^ (1 / p.toReal)) ^ p.toReal)
        (fun n => ∑ l ∈ Finset.range (r + 1), localMass p j u (n + l)) x +
      (Km * ENNReal.ofReal (2 ^ j * h) ^ m * ENNReal.ofReal (2 ^ j) ^ (1 / p.toReal)) ^
        p.toReal * localMass p j u ⌊2 ^ j * x⌋₊ := by
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p)).ne'
  have hq : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  by_cases hbad : ((⌊2 ^ j * x⌋₊ : ℝ) + 1) / 2 ^ j ≤ x + m * h
  · have hbad' : ((⌊2 ^ j * x⌋₊ : ℝ) + 1) / 2 ^ j ≤ x + r * h :=
      hbad.trans (by
        have : (m : ℝ) ≤ r := by exact_mod_cast hmr
        nlinarith)
    refine le_add_right ?_
    simp only [stripBound, hbad', ↓reduceIte]
    rw [← mul_rpow_one_div_rpow hp0 hp]
    refine ENNReal.rpow_le_rpow ?_ hq.le
    exact (enorm_higherDiff_le_of_isPiecewisePoly_of_le hmr hu hK hp hh0 hh hx.1).trans_eq
      (by ring)
  · push Not at hbad
    refine le_add_left ?_
    rw [← mul_rpow_one_div_rpow hp0 hp]
    exact ENNReal.rpow_le_rpow (enorm_higherDiff_le_of_mem_piece hu hKm hp hh0 hx.1 hbad) hq.le

omit [Fact (1 ≤ p)] in
/-- **The strip constant**: `(A 2^(j/p))^p (r h) = A^p r (2^j h)`. -/
theorem rpow_strip_mul_eq (hp0 : p ≠ 0) (hp : p ≠ ∞) (A : ℝ≥0∞) (r j : ℕ) (h : ℝ) :
    (A * ENNReal.ofReal (2 ^ j) ^ (1 / p.toReal)) ^ p.toReal * ENNReal.ofReal (r * h) =
      A ^ p.toReal * r * ENNReal.ofReal (2 ^ j * h) := by
  rw [mul_rpow_one_div_rpow hp0 hp, mul_assoc, ← ENNReal.ofReal_mul (by positivity),
    show (2 : ℝ) ^ j * (r * h) = r * (2 ^ j * h) by ring, ENNReal.ofReal_mul (Nat.cast_nonneg r),
    ENNReal.ofReal_natCast]
  ring

omit [Fact (1 ≤ p)] in
/-- **The gain inside the pieces**: for `σ = 2^j h ≤ 1` and `m ≥ 1`,
`(K σ^m 2^(j/p))^p 2^(-j) ≤ K^p σ`, since `σ^(mp) ≤ σ^p ≤ σ`. -/
theorem rpow_piece_mul_le (hp0 : p ≠ 0) (hp : p ≠ ∞) (hq1 : 1 ≤ p.toReal) (K : ℝ≥0∞) {m : ℕ}
    (hm : 1 ≤ m) (j : ℕ) {σ : ℝ≥0∞} (hσ1 : σ ≤ 1) :
    (K * σ ^ m * ENNReal.ofReal (2 ^ j) ^ (1 / p.toReal)) ^ p.toReal *
      ENNReal.ofReal (1 / 2 ^ j) ≤ K ^ p.toReal * σ := by
  have hq : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  rw [mul_rpow_one_div_rpow hp0 hp, mul_assoc, ← ENNReal.ofReal_mul (by positivity),
    show (2 : ℝ) ^ j * (1 / 2 ^ j) = 1 by field_simp, ENNReal.ofReal_one, mul_one,
    ENNReal.mul_rpow_of_nonneg _ _ hq.le]
  gcongr
  calc (σ ^ m) ^ p.toReal ≤ σ ^ p.toReal :=
        ENNReal.rpow_le_rpow (pow_le_of_le_one zero_le hσ1 (by omega)) hq.le
    _ ≤ σ := ENNReal.rpow_le_self_of_le_one hσ1 hq1

/-- **Differences of every positive order of piecewise polynomials**: for `1 ≤ m ≤ r` there is
`C` such that for every level `j`, every piecewise polynomial `u` of level `j` and degree `< r` and
`0 ≤ h ≤ 2^(-j)`, `‖Δ_h^m u‖_{L_p[0, 1 - mh]} ≤ C (2^j h)^(1/p) ‖u‖_p`. On the strips of width
`rh` left of the knots the difference is bounded by the neighbouring pieces
(`Interval.enorm_higherDiff_le_of_isPiecewisePoly_of_le`), inside a piece by `(2^j h)^m` times the
piece (`Interval.enorm_higherDiff_le_of_mem_piece`), and `(2^j h)^(mp) ≤ 2^j h`. -/
theorem exists_eLpNorm_higherDiff_ppFun_le {r m : ℕ} (hm : 1 ≤ m) (hmr : m ≤ r) (hp : p ≠ ∞) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ (j : ℕ) (Q : ℕ → ℂ[X]), (∀ n, Q n ∈ degreeLT ℂ r) → ∀ {h : ℝ},
      0 ≤ h → h ≤ 1 / 2 ^ j →
        eLpNorm (higherDiff m h (ppFun j Q)) p (volume.restrict (Icc 0 (1 - m * h))) ≤
          C * ENNReal.ofReal (2 ^ j * h) ^ (1 / p.toReal) * eLpNorm (ppFun j Q) p unitVol := by
  obtain ⟨K, hK, hKb⟩ := enorm_polyFun_le (p := p) r hp
  obtain ⟨Km, hKm, hKmb⟩ := exists_diffBound (p := p) r m hp
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p)).ne'
  have hq : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  have hq1 : 1 ≤ p.toReal := ENNReal.one_le_toReal_of_one_le Fact.out hp
  set C₀ : ℝ≥0∞ := (2 ^ m * K) ^ p.toReal * ((r : ℝ≥0∞) * (r + 1)) + Km ^ p.toReal
  have hC₀ : C₀ ≠ ∞ := by
    refine ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hq.le
      (ENNReal.mul_ne_top (by simp) hK)) (ENNReal.mul_ne_top (ENNReal.natCast_ne_top r)
        (ENNReal.add_ne_top.2 ⟨ENNReal.natCast_ne_top r, ENNReal.one_ne_top⟩)),
      ENNReal.rpow_ne_top_of_nonneg hq.le hKm⟩
  refine ⟨C₀ ^ (1 / p.toReal), ENNReal.rpow_ne_top_of_nonneg (by positivity) hC₀,
    fun j Q hQ h hh0 hh => ?_⟩
  set u := ppFun j Q
  have hu := isPiecewisePoly_ppFun hQ j
  set B := eLpNorm u p unitVol
  set σ := ENNReal.ofReal (2 ^ j * h)
  have hσ1 : σ ≤ 1 := by
    rw [← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [le_div_iff₀ (by positivity)] at hh
    linarith
  set Mw : ℕ → ℝ≥0∞ := fun n => ∑ l ∈ Finset.range (r + 1), localMass p j u (n + l)
  set G₁ := 2 ^ m * K * ENNReal.ofReal (2 ^ j) ^ (1 / p.toReal)
  set G₂ := Km * σ ^ m * ENNReal.ofReal (2 ^ j) ^ (1 / p.toReal)
  -- the pointwise bound: strip part plus interior part
  have hpt : ∀ x ∈ Icc (0 : ℝ) (1 - m * h), ‖higherDiff m h u x‖ₑ ^ p.toReal ≤
      stripBound j r h (G₁ ^ p.toReal) Mw x + G₂ ^ p.toReal * localMass p j u ⌊2 ^ j * x⌋₊ :=
    fun x hx => enorm_higherDiff_rpow_le_strip_add_piece hp hmr hu hKb hKmb hh0 hh hx
  -- the integral
  have hmeas : Measurable fun x : ℝ => G₂ ^ p.toReal * localMass p j u ⌊2 ^ j * x⌋₊ :=
    measurable_const.mul ((measurable_from_nat (f := localMass p j u)).comp
      (measurable_const_mul ((2 : ℝ) ^ j)).nat_floor)
  have hstrip := lintegral_stripBound_le j r h (G₁ ^ p.toReal) Mw
  have hloc := lintegral_localBound_le j (G₂ ^ p.toReal) (localMass p j u)
  have hsum1 : ∑ n ∈ Finset.range (2 ^ j), Mw n ≤ (r + 1) * B ^ p.toReal :=
    sum_sum_localMass_le hp j r Q
  have hsum2 := sum_localMass_ppFun_le hp j Q
  -- the constants
  have hG₁ : G₁ ^ p.toReal * ENNReal.ofReal (r * h) = (2 ^ m * K) ^ p.toReal * r * σ :=
    rpow_strip_mul_eq hp0 hp (2 ^ m * K) r j h
  have hG₂ : G₂ ^ p.toReal * ENNReal.ofReal (1 / 2 ^ j) ≤ Km ^ p.toReal * σ :=
    rpow_piece_mul_le hp0 hp hq1 Km hm j hσ1
  refine eLpNorm_le_of_lintegral_le_mul hp
    (measurable_higherDiff (measurable_ppFun j Q) m h).aestronglyMeasurable
    (A := C₀ ^ (1 / p.toReal)) ?_
  rw [← ENNReal.rpow_mul, one_div_mul_cancel hq.ne', ENNReal.rpow_one]
  calc ∫⁻ x in Icc (0 : ℝ) (1 - m * h), ‖higherDiff m h u x‖ₑ ^ p.toReal
      ≤ ∫⁻ x in Icc (0 : ℝ) (1 - m * h), (stripBound j r h (G₁ ^ p.toReal) Mw x +
          G₂ ^ p.toReal * localMass p j u ⌊2 ^ j * x⌋₊) := setLIntegral_mono' measurableSet_Icc hpt
    _ ≤ ∫⁻ x in Icc (0 : ℝ) 1, (stripBound j r h (G₁ ^ p.toReal) Mw x +
          G₂ ^ p.toReal * localMass p j u ⌊2 ^ j * x⌋₊) :=
        lintegral_mono_set (Icc_subset_Icc le_rfl (by
          linarith [mul_nonneg (Nat.cast_nonneg m) hh0]))
    _ = (∫⁻ x in Icc (0 : ℝ) 1, stripBound j r h (G₁ ^ p.toReal) Mw x) +
          ∫⁻ x in Icc (0 : ℝ) 1, G₂ ^ p.toReal * localMass p j u ⌊2 ^ j * x⌋₊ :=
        lintegral_add_right' _ hmeas.aemeasurable
    _ ≤ G₁ ^ p.toReal * ENNReal.ofReal (r * h) * ((r + 1) * B ^ p.toReal) +
          G₂ ^ p.toReal * ENNReal.ofReal (1 / 2 ^ j) * B ^ p.toReal := by
        gcongr
        · exact hstrip.trans (by gcongr)
        · exact hloc.trans (by gcongr)
    _ ≤ (2 ^ m * K) ^ p.toReal * r * σ * ((r + 1) * B ^ p.toReal) +
          Km ^ p.toReal * σ * B ^ p.toReal := by
        rw [hG₁]
        gcongr
    _ = C₀ * σ * B ^ p.toReal := by
        simp only [C₀]
        ring

/-! ### Splines -/

/-- **A jump term of a spline**: for `1 ≤ m < r`, `h ≥ 0` with `mh ≤ 2^(-j)`, `x ≥ 0` and a knot
`l 2^(-j)` with `n₀ < l ≤ n₀ + r`, `n₀ = ⌊2^j x⌋`, the term `c_l Δ_h^m (· - l 2^(-j))_+^(r-1)(x)`
is at most `2 · 2^m m^(r-1) K (2^j h)^m 2^(j/p) (∑_{l' ≤ r} M_{n₀+l'})^(1/p)`: the bound of every
order (`Interval.enorm_jumpCoeff_mul_higherDiff_truncPow_le_any_order`) with
`(2^j h)^(r-1) ≤ (2^j h)^m`, since `2^j h ≤ 1`. -/
theorem enorm_jumpCoeff_mul_higherDiff_truncPow_le {r j N m : ℕ} (hm : 1 ≤ m) (hmr : m < r)
    {P : ℕ → ℂ[X]} (hP : ∀ n, P n ∈ degreeLT ℂ r) (hJ : SplineJoinsBelow r j N P) {u : ℝ → ℂ}
    (hu : ∀ n < N, ∀ x ∈ dyadicIco j n, u x = polyFun (P n) x) {K : ℝ≥0∞}
    (hK : NikolskiiBound p r K) (hp : p ≠ ∞) {h x : ℝ} (hh0 : 0 ≤ h) (hmh : m * h ≤ 1 / 2 ^ j)
    {l : ℕ} (hl : l ∈ Finset.Ioc ⌊2 ^ j * x⌋₊ (⌊2 ^ j * x⌋₊ + r)) :
    ‖jumpCoeff r N P l * higherDiff m h (truncPow r ((l : ℝ) / 2 ^ j)) x‖ₑ ≤
      2 * 2 ^ m * (m : ℝ≥0∞) ^ (r - 1) * K * ENNReal.ofReal (2 ^ j * h) ^ m *
        ENNReal.ofReal (2 ^ j) ^ (1 / p.toReal) *
          (∑ l' ∈ Finset.range (r + 1), localMass p j u (⌊2 ^ j * x⌋₊ + l')) ^ (1 / p.toReal) := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hh : h ≤ 1 / 2 ^ j := le_trans (by nlinarith) hmh
  have hσ1 : ENNReal.ofReal (2 ^ j * h) ≤ 1 := by
    rw [← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [le_div_iff₀ (by positivity)] at hh
    linarith
  refine (enorm_jumpCoeff_mul_higherDiff_truncPow_le_any_order m hP hJ hu hK hp hh0
    hl).trans (mul_le_mul' (mul_le_mul' (mul_le_mul' le_rfl ?_) le_rfl) le_rfl)
  exact pow_le_pow_of_le_one zero_le hσ1 (by omega)

/-- **Pointwise bound for differences of lower order of splines**: for `1 ≤ m < r`, `h ≥ 0` with
`mh ≤ 2^(-j)`, `x ≥ 0` and `x + mh < N 2^(-j)`,
`|Δ_h^m u(x)| ≤ (K_m + 2 r 2^m m^(r-1) K) (2^j h)^m 2^(j/p) (∑_{l ≤ r} M_{n₀+l})^(1/p)`. The
piece contributes by the difference bound `K_m` of the polynomials, a jump
`c_l (· - ξ_l)_+^(r-1)` by `|c_l| 2^m (mh)^(r-1)` with
`|c_l| 2^(-j(r-1)) ≤ 2 K 2^(j/p) (…)^(1/p)`, and `(2^j h)^(r-1) ≤ (2^j h)^m`. -/
theorem enorm_higherDiff_spline_le_of_lt {r j N m : ℕ} (hm : 1 ≤ m) (hmr : m < r)
    {P : ℕ → ℂ[X]} (hP : ∀ n, P n ∈ degreeLT ℂ r) (hJ : SplineJoinsBelow r j N P) {u : ℝ → ℂ}
    (hu : ∀ n < N, ∀ x ∈ dyadicIco j n, u x = polyFun (P n) x) {K Km : ℝ≥0∞}
    (hK : NikolskiiBound p r K) (hKm : DiffBound p r m Km) (hp : p ≠ ∞) {h x : ℝ}
    (hh0 : 0 ≤ h) (hmh : m * h ≤ 1 / 2 ^ j) (hx : 0 ≤ x) (hxm : x + m * h < N / 2 ^ j) :
    ‖higherDiff m h u x‖ₑ ≤ (Km + 2 * r * 2 ^ m * (m : ℝ≥0∞) ^ (r - 1) * K) *
      ENNReal.ofReal (2 ^ j * h) ^ m * ENNReal.ofReal (2 ^ j) ^ (1 / p.toReal) *
        (∑ l ∈ Finset.range (r + 1), localMass p j u (⌊2 ^ j * x⌋₊ + l)) ^ (1 / p.toReal) := by
  have hpos : (0 : ℝ) < 2 ^ j := by positivity
  have hL : (0 : ℝ) < 1 / 2 ^ j := by positivity
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hh : h ≤ 1 / 2 ^ j := le_trans (by nlinarith) hmh
  set n₀ := ⌊2 ^ j * x⌋₊
  set S := ∑ l ∈ Finset.range (r + 1), localMass p j u (n₀ + l)
  set σ := ENNReal.ofReal (2 ^ j * h)
  have hfl : (n₀ : ℝ) ≤ 2 ^ j * x := Nat.floor_le (by positivity)
  have hfl' : 2 ^ j * x < (n₀ : ℝ) + 1 := Nat.lt_floor_add_one _
  have hn₀N : n₀ < N := by
    refine (Nat.floor_lt (by positivity)).2 ?_
    rw [lt_div_iff₀ hpos] at hxm
    nlinarith [mul_nonneg (Nat.cast_nonneg m) hh0]
  -- the piece
  have hpiece : ‖higherDiff m h (polyFun (P n₀)) x‖ₑ ≤
      Km * σ ^ m * ENNReal.ofReal (2 ^ j) ^ (1 / p.toReal) * S ^ (1 / p.toReal) := by
    have hux : (n₀ : ℝ) / 2 ^ j ≤ x := by rw [div_le_iff₀ hpos]; linarith
    have hxu : x + m * h ≤ (n₀ : ℝ) / 2 ^ j + 2 * (1 / 2 ^ j) := by
      have : x < (n₀ : ℝ) / 2 ^ j + 1 / 2 ^ j := by
        rw [← add_div, lt_div_iff₀ hpos]; linarith
      linarith
    have hb := hKm (P n₀) (hP n₀) ((n₀ : ℝ) / 2 ^ j) hL hh0 x hux hxu
    rw [show h / (1 / 2 ^ j) = 2 ^ j * h by field_simp,
      show (1 / (2 : ℝ) ^ j)⁻¹ = 2 ^ j by rw [one_div, inv_inv],
      eLpNorm_piece_eq_localMass hp (hu n₀ hn₀N)] at hb
    refine hb.trans ?_
    gcongr
    simpa using localMass_le_sum_range j u n₀ (Nat.zero_le r)
  -- the jumps
  have hterm : ∀ l ∈ Finset.Ioc n₀ (n₀ + r), ‖jumpCoeff r N P l *
      higherDiff m h (truncPow r ((l : ℝ) / 2 ^ j)) x‖ₑ ≤
        2 * 2 ^ m * (m : ℝ≥0∞) ^ (r - 1) * K * σ ^ m * ENNReal.ofReal (2 ^ j) ^ (1 / p.toReal) *
          S ^ (1 / p.toReal) := fun l hl =>
    enorm_jumpCoeff_mul_higherDiff_truncPow_le hm hmr hP hJ hu hK hp hh0 hmh hl
  rw [higherDiff_eq_add_sum_jumps hmr.le hJ hu hh0 hh hx hxm]
  refine (eNorm_add_le _ _).trans ((add_le_add hpiece ((eNorm_sum_le _ _).trans
    (Finset.sum_le_sum hterm))).trans ?_)
  rw [Finset.sum_const, Nat.card_Ioc, show n₀ + r - n₀ = r by omega, nsmul_eq_mul]
  exact le_of_eq (by ring)

/-- **Long steps**: for `mh > 2^(-j)`, `‖Δ_h^m u‖_{L_p[0, 1 - mh]} ≤ 2^m m^m (2^j h)^m ‖u‖_p`,
from `‖Δ_h^m u‖_p ≤ 2^m ‖u‖_p` and `1 < m 2^j h`. -/
theorem eLpNorm_higherDiff_le_of_lt_mul {u : ℝ → ℂ} (hu : Measurable u) {m j : ℕ} {h : ℝ}
    (hh0 : 0 ≤ h) (hmh : 1 / 2 ^ j < m * h) :
    eLpNorm (higherDiff m h u) p (volume.restrict (Icc 0 (1 - m * h))) ≤
      2 ^ m * (m : ℝ≥0∞) ^ m * ENNReal.ofReal (2 ^ j * h) ^ m * eLpNorm u p unitVol := by
  have hpos : (0 : ℝ) < 2 ^ j := by positivity
  have h1 := eLpNorm_higherDiff_le hu (Fact.out : 1 ≤ p) m hh0 0 1
  have hmσ : 1 ≤ (m : ℝ≥0∞) * ENNReal.ofReal (2 ^ j * h) := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
      ← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [div_lt_iff₀ hpos] at hmh
    nlinarith
  calc eLpNorm (higherDiff m h u) p (volume.restrict (Icc 0 (1 - m * h)))
      ≤ 2 ^ m * eLpNorm u p unitVol := h1
    _ ≤ 2 ^ m * ((m : ℝ≥0∞) * ENNReal.ofReal (2 ^ j * h)) ^ m * eLpNorm u p unitVol := by
        gcongr
        calc (2 : ℝ≥0∞) ^ m = 2 ^ m * 1 := (mul_one _).symm
          _ ≤ 2 ^ m * ((m : ℝ≥0∞) * ENNReal.ofReal (2 ^ j * h)) ^ m := by
              gcongr; exact one_le_pow₀ hmσ
    _ = _ := by rw [mul_pow]; ring

/-- **Differences of lower order of splines**: for `1 ≤ m < r` there is `C` such that for every
level `j`, every spline `u` of order `r` and level `j` and `0 ≤ h ≤ 2^(-j)`,
`‖Δ_h^m u‖_{L_p[0, 1 - mh]} ≤ C (2^j h)^m ‖u‖_p`. For `mh ≤ 2^(-j)` the pointwise bound
(`Interval.enorm_higherDiff_spline_le_of_lt`) holds at almost every point, and the local masses
of `r + 1` consecutive pieces add up to at most `(r + 1) ‖u‖_p^p`; for `mh > 2^(-j)` the trivial
bound `2^m ‖u‖_p ≤ 2^m (m 2^j h)^m ‖u‖_p` suffices. -/
theorem exists_eLpNorm_higherDiff_spline_le_of_lt {r m : ℕ} (hm : 1 ≤ m) (hmr : m < r)
    (hp : p ≠ ∞) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ (j : ℕ) (Q : ℕ → ℂ[X]), (∀ n, Q n ∈ degreeLT ℂ r) →
      SplineJoins r j Q → ∀ {h : ℝ}, 0 ≤ h → h ≤ 1 / 2 ^ j →
        eLpNorm (higherDiff m h (ppFun j Q)) p (volume.restrict (Icc 0 (1 - m * h))) ≤
          C * ENNReal.ofReal (2 ^ j * h) ^ m * eLpNorm (ppFun j Q) p unitVol := by
  obtain ⟨K, hK, hKb⟩ := enorm_polyFun_le (p := p) r hp
  obtain ⟨Km, hKm, hKmb⟩ := exists_diffBound (p := p) r m hp
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p)).ne'
  have hq : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  set C₁ := Km + 2 * r * 2 ^ m * (m : ℝ≥0∞) ^ (r - 1) * K
  have hC₁ : C₁ ≠ ∞ := ENNReal.add_ne_top.2 ⟨hKm, ENNReal.mul_ne_top (ENNReal.mul_ne_top
    (ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) (ENNReal.natCast_ne_top r)) (by simp))
    (ENNReal.pow_ne_top (ENNReal.natCast_ne_top m))) hK⟩
  refine ⟨C₁ * ((r : ℝ≥0∞) + 1) ^ (1 / p.toReal) + 2 ^ m * (m : ℝ≥0∞) ^ m,
    ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top hC₁ (ENNReal.rpow_ne_top_of_nonneg (by positivity)
      (ENNReal.add_ne_top.2 ⟨ENNReal.natCast_ne_top r, ENNReal.one_ne_top⟩)),
      ENNReal.mul_ne_top (by simp) (ENNReal.pow_ne_top (ENNReal.natCast_ne_top m))⟩,
    fun j Q hQ hJ h hh0 hh => ?_⟩
  set u := ppFun j Q
  set B := eLpNorm u p unitVol
  set σ := ENNReal.ofReal (2 ^ j * h)
  have hpos : (0 : ℝ) < 2 ^ j := by positivity
  rcases le_or_gt ((m : ℝ) * h) (1 / 2 ^ j) with hmh | hmh
  · have hu : ∀ n < 2 ^ j, ∀ x ∈ dyadicIco j n, u x = polyFun (Q n) x :=
      fun n hn x hx => ppFun_eq_of_mem Q hn hx
    set Mw : ℕ → ℝ≥0∞ := fun n => ∑ l ∈ Finset.range (r + 1), localMass p j u (n + l)
    set G := C₁ * σ ^ m * ENNReal.ofReal (2 ^ j) ^ (1 / p.toReal)
    have hae : ∀ᵐ x ∂volume.restrict (Icc (0 : ℝ) (1 - m * h)), x ∈ Ico 0 (1 - m * h) := by
      rw [← Measure.restrict_congr_set Ico_ae_eq_Icc]
      exact ae_restrict_mem measurableSet_Ico
    have hpt : ∀ᵐ x ∂volume.restrict (Icc (0 : ℝ) (1 - m * h)),
        ‖higherDiff m h u x‖ₑ ^ p.toReal ≤ G ^ p.toReal * Mw ⌊2 ^ j * x⌋₊ := by
      filter_upwards [hae] with x hx
      have hxm : x + m * h < ((2 ^ j : ℕ) : ℝ) / 2 ^ j := by
        rw [Nat.cast_pow, Nat.cast_ofNat, div_self hpos.ne']
        linarith [hx.2]
      rw [← mul_rpow_one_div_rpow hp0 hp]
      exact ENNReal.rpow_le_rpow (enorm_higherDiff_spline_le_of_lt hm hmr hQ hJ.below hu hKb hKmb
        hp hh0 hmh hx.1 hxm) hq.le
    have hG : G ^ p.toReal * ENNReal.ofReal (1 / 2 ^ j) = (C₁ * σ ^ m) ^ p.toReal := by
      simp only [G]
      rw [mul_rpow_one_div_rpow hp0 hp, mul_assoc, ← ENNReal.ofReal_mul (by positivity),
        show (2 : ℝ) ^ j * (1 / 2 ^ j) = 1 by field_simp, ENNReal.ofReal_one, mul_one]
    refine (eLpNorm_le_of_lintegral_le_mul hp
      (measurable_higherDiff (measurable_ppFun j Q) m h).aestronglyMeasurable
      (A := C₁ * σ ^ m) (σ := (r : ℝ≥0∞) + 1) (B := B) ?_).trans ?_
    · calc ∫⁻ x in Icc (0 : ℝ) (1 - m * h), ‖higherDiff m h u x‖ₑ ^ p.toReal
          ≤ ∫⁻ x in Icc (0 : ℝ) (1 - m * h), G ^ p.toReal * Mw ⌊2 ^ j * x⌋₊ :=
            lintegral_mono_ae hpt
        _ ≤ ∫⁻ x in Icc (0 : ℝ) 1, G ^ p.toReal * Mw ⌊2 ^ j * x⌋₊ :=
            lintegral_mono_set (Icc_subset_Icc le_rfl (by
              linarith [mul_nonneg (Nat.cast_nonneg m) hh0]))
        _ ≤ G ^ p.toReal * ENNReal.ofReal (1 / 2 ^ j) * ∑ n ∈ Finset.range (2 ^ j), Mw n :=
            lintegral_localBound_le j _ Mw
        _ ≤ G ^ p.toReal * ENNReal.ofReal (1 / 2 ^ j) * ((r + 1) * B ^ p.toReal) := by
            gcongr
            exact sum_sum_localMass_le hp j r Q
        _ = (C₁ * σ ^ m) ^ p.toReal * ((r : ℝ≥0∞) + 1) * B ^ p.toReal := by
            rw [hG]; ring
    · calc C₁ * σ ^ m * ((r : ℝ≥0∞) + 1) ^ (1 / p.toReal) * B
          = C₁ * ((r : ℝ≥0∞) + 1) ^ (1 / p.toReal) * σ ^ m * B := by ring
        _ ≤ (C₁ * ((r : ℝ≥0∞) + 1) ^ (1 / p.toReal) + 2 ^ m * (m : ℝ≥0∞) ^ m) * σ ^ m * B := by
            gcongr
            exact le_self_add
  · -- `mh > 2^(-j)`: the trivial bound
    calc eLpNorm (higherDiff m h u) p (volume.restrict (Icc 0 (1 - m * h)))
        ≤ 2 ^ m * (m : ℝ≥0∞) ^ m * σ ^ m * B :=
          eLpNorm_higherDiff_le_of_lt_mul (measurable_ppFun j Q) hh0 hmh
      _ ≤ (C₁ * ((r : ℝ≥0∞) + 1) ^ (1 / p.toReal) + 2 ^ m * (m : ℝ≥0∞) ^ m) * σ ^ m * B := by
          gcongr
          exact le_add_self

end Interval
