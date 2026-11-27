/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Domains.Interval.PiecewiseInverse
public import LeanPool.FunctionSpaces.Domains.Interval.Splines

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# The inverse inequality for dyadic splines

For a spline `a` of order `r` and level `j` and every `k`,
`ω_r(a, 2^(-k), [0, 1])_p ≤ C_B 2^(-(k-j)(r-1+1/p)) ‖a‖_p` (`k - j` truncated at `0`). The
order `r - 1 + 1/p` comes from the jumps of the `(r-1)`-th derivative at the knots.

For `0 ≤ h ≤ 2^(-k)` the difference `Δ_h^r a(x)` vanishes when `x, …, x + rh` lie in one
interval. Otherwise, on `[x, x + rh]` the spline is `Q(y) + ∑_m c_m (y - ξ_m)_+^(r-1)`, with `Q` the
piece at `x` and `ξ_m` the knots in reach (`Interval.polyFun_eq_add_sum_jumps`). The polynomial
part has `Δ_h^r Q = 0`, and `|Δ_h^r (· - ξ)_+^(r-1)(x)| ≤ 2^r (rh)^(r-1)` for `x < ξ`
(`Interval.enorm_higherDiff_truncPow_le`). The jump `c_m L^(r-1) = Q_m(ξ_m + L) - Q_{m-1}(ξ_m + L)`,
`L = 2^(-j)`, is bounded by Nikolskii's inequality on the two neighbouring pieces, which reaches
the doubled interval (`Interval.NikolskiiBound`, `Interval.enorm_jumpCoeff_le`). These steps hold
for differences of every order `m`, the piece then contributing `Δ_h^m Q`
(`Interval.enorm_higherDiff_truncPow_le_of_lt`, `Interval.higherDiff_eq_add_sum_jumps`,
`Interval.enorm_jumpCoeff_mul_higherDiff_truncPow_le_any_order`); the lower orders `m < r` use
them in `FunctionSpaces.Domains.Interval.LowerDifferences`. The strip integral of the piecewise
polynomials turns this pointwise bound into the `L_p` bound
(`Interval.eLpNorm_higherDiff_le_of_pointwise`).
-/

@[expose] public section

open MeasureTheory Set Polynomial
open Rd (higherDiff)
open scoped ENNReal
open ENNReal (dyadicWeight)

namespace Interval

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The **truncated power** `(y - ξ)_+^(r-1)`. -/
noncomputable def truncPow (r : ℕ) (ξ : ℝ) (y : ℝ) : ℂ :=
  if ξ ≤ y then (((y - ξ) ^ (r - 1) : ℝ) : ℂ) else 0

/-- **Differences of any order of a truncated power left of its knot**: for `x < ξ` and
`h ≥ 0`, `|Δ_h^m (· - ξ)_+^(r-1)(x)| ≤ 2^m (mh)^(r-1)`, since `0 ≤ (x + ih - ξ)_+ ≤ mh`. -/
theorem enorm_higherDiff_truncPow_le_of_lt (r m : ℕ) {ξ h x : ℝ} (hh : 0 ≤ h) (hx : x < ξ) :
    ‖higherDiff m h (truncPow r ξ) x‖ₑ ≤ 2 ^ m * ENNReal.ofReal (m * h) ^ (r - 1) := by
  refine enorm_higherDiff_le_of_forall fun i hi => ?_
  have hi' : (i : ℝ) ≤ m := by exact_mod_cast Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  unfold truncPow
  split_ifs with hξ
  · rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs, abs_pow,
      abs_of_nonneg (by linarith), ← ENNReal.ofReal_pow (by positivity)]
    refine ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (by linarith) ?_ _)
    nlinarith [mul_le_mul_of_nonneg_right hi' hh]
  · simp

/-- **Differences of a truncated power left of its knot**: for `x < ξ` and `h ≥ 0`,
`|Δ_h^r (· - ξ)_+^(r-1)(x)| ≤ 2^r (rh)^(r-1)`, since `0 ≤ (x + ih - ξ)_+ ≤ rh`. -/
theorem enorm_higherDiff_truncPow_le (r : ℕ) {ξ h x : ℝ} (hh : 0 ≤ h) (hx : x < ξ) :
    ‖higherDiff r h (truncPow r ξ) x‖ₑ ≤ 2 ^ r * ENNReal.ofReal (r * h) ^ (r - 1) :=
  enorm_higherDiff_truncPow_le_of_lt r r hh hx

/-! ### Splines across the knots -/

/-- **Telescoping**: `f b = f a + ∑_{a < m ≤ b} (f m - f (m - 1))` for `a ≤ b`. -/
theorem eq_add_sum_Ioc_sub {G : Type*} [AddCommGroup G] (f : ℕ → G) {a b : ℕ} (hab : a ≤ b) :
    f b = f a + ∑ m ∈ Finset.Ioc a b, (f m - f (m - 1)) := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    rw [Finset.sum_Ioc_succ_top hab, Nat.add_sub_cancel, ← add_assoc, ← ih]
    abel

/-- The **jump coefficients** of pieces `P`: the coefficient of `X^(r-1)` in `P_m - P_{m-1}` at
the knots `0 < m < N`, and `0` elsewhere. With spline joins below `N`,
`P_m - P_{m-1} = c_m (X - ξ_m)^(r-1)` (`Interval.sub_eq_jumpCoeff`). -/
noncomputable def jumpCoeff (r N : ℕ) (P : ℕ → ℂ[X]) (m : ℕ) : ℂ :=
  if 0 < m ∧ m < N then (P m - P (m - 1)).coeff (r - 1) else 0

/-- The jump at a knot: `P_m - P_{m-1} = c_m (X - ξ_m)^(r-1)`, since `(X - ξ)^(r-1)` is monic of
degree `r - 1`. -/
theorem sub_eq_jumpCoeff {r j N : ℕ} {P : ℕ → ℂ[X]} (hJ : SplineJoinsBelow r j N P) {m : ℕ}
    (h0 : 0 < m) (hm : m < N) :
    P m - P (m - 1) = C (jumpCoeff r N P m) * (X - C ((((m : ℝ) / 2 ^ j : ℝ)) : ℂ)) ^ (r - 1) := by
  obtain ⟨c, hc⟩ := hJ m h0 hm
  have hmon : ((X - C ((((m : ℝ) / 2 ^ j : ℝ)) : ℂ)) ^ (r - 1)).coeff (r - 1) = 1 := by
    have h := ((monic_X_sub_C ((((m : ℝ) / 2 ^ j : ℝ)) : ℂ)).pow (r - 1)).coeff_natDegree
    rwa [natDegree_pow, natDegree_X_sub_C, mul_one] at h
  have h : 0 < m ∧ m < N := ⟨h0, hm⟩
  simp only [jumpCoeff, h, and_self, ↓reduceIte]
  rw [hc, coeff_C_mul, hmon, mul_one]

/-- **A spline across the knots**: let `u` be the polynomial `P_m` on `I_{j,m}` for `m < N`, with
spline joins below `N`. For `0 ≤ x ≤ y < N 2^(-j)` with `⌊2^j y⌋ ≤ ⌊2^j x⌋ + r`,
`u(y) = P_{n₀}(y) + ∑_{n₀ < m ≤ n₀ + r} c_m (y - ξ_m)_+^(r-1)`, `n₀ = ⌊2^j x⌋`. -/
theorem polyFun_eq_add_sum_jumps {r j N : ℕ} {P : ℕ → ℂ[X]} (hJ : SplineJoinsBelow r j N P)
    {u : ℝ → ℂ} (hu : ∀ m < N, ∀ x ∈ dyadicIco j m, u x = polyFun (P m) x) {x y : ℝ}
    (hx : 0 ≤ x) (hxy : x ≤ y) (hyN : y < N / 2 ^ j) (hyr : ⌊2 ^ j * y⌋₊ ≤ ⌊2 ^ j * x⌋₊ + r) :
    u y = polyFun (P ⌊2 ^ j * x⌋₊) y + ∑ m ∈ Finset.Ioc ⌊2 ^ j * x⌋₊ (⌊2 ^ j * x⌋₊ + r),
      jumpCoeff r N P m * truncPow r ((m : ℝ) / 2 ^ j) y := by
  have hpos : (0 : ℝ) < 2 ^ j := by positivity
  have hy0 : 0 ≤ y := hx.trans hxy
  have hmem : y ∈ dyadicIco j ⌊2 ^ j * y⌋₊ :=
    mem_dyadicIco.2 ⟨Nat.floor_le (by positivity), Nat.lt_floor_add_one _⟩
  have hlt : ⌊2 ^ j * y⌋₊ < N := by
    refine (Nat.floor_lt (by positivity)).2 ?_
    rw [lt_div_iff₀ hpos] at hyN
    linarith
  have hnn : ⌊2 ^ j * x⌋₊ ≤ ⌊2 ^ j * y⌋₊ := Nat.floor_mono (by nlinarith)
  rw [hu _ hlt y hmem, eq_add_sum_Ioc_sub P hnn, polyFun_add,
    ← Finset.sum_Ioc_consecutive _ hnn hyr]
  have hzero : ∑ m ∈ Finset.Ioc ⌊2 ^ j * y⌋₊ (⌊2 ^ j * x⌋₊ + r),
      jumpCoeff r N P m * truncPow r ((m : ℝ) / 2 ^ j) y = 0 :=
    Finset.sum_eq_zero fun m hm => by
      have hm' := (Finset.mem_Ioc.1 hm).1
      have : y < (m : ℝ) / 2 ^ j := by
        rw [lt_div_iff₀ hpos]
        have h1 : (⌊2 ^ j * y⌋₊ : ℝ) + 1 ≤ m := by exact_mod_cast hm'
        linarith [Nat.lt_floor_add_one (2 ^ j * y)]
      simp [truncPow, not_le.2 this]
  rw [hzero, add_zero]
  congr 1
  rw [polyFun, eval_finsetSum]
  refine Finset.sum_congr rfl fun m hm => ?_
  obtain ⟨hm1, hm2⟩ := Finset.mem_Ioc.1 hm
  rw [sub_eq_jumpCoeff hJ (by omega) (by omega), eval_mul, eval_C, eval_pow, eval_sub, eval_X,
    eval_C]
  have hξ : (m : ℝ) / 2 ^ j ≤ y := by
    rw [div_le_iff₀ hpos]
    have : (m : ℝ) ≤ ⌊2 ^ j * y⌋₊ := by exact_mod_cast hm2
    nlinarith [Nat.floor_le (by positivity : (0 : ℝ) ≤ 2 ^ j * y)]
  simp only [truncPow, hξ, ↓reduceIte]
  push_cast
  ring

/-- **Differences of a spline: the piece plus the jumps**: for `m ≤ r`, `0 ≤ h ≤ 2^(-j)`,
`x ≥ 0` and `x + mh < N 2^(-j)`,
`Δ_h^m u(x) = Δ_h^m P_{n₀}(x) + ∑_{n₀ < l ≤ n₀ + r} c_l Δ_h^m (· - ξ_l)_+^(r-1)(x)`, with
`n₀ = ⌊2^j x⌋` (`Interval.polyFun_eq_add_sum_jumps` at every point `x + ih`). -/
theorem higherDiff_eq_add_sum_jumps {r j N m : ℕ} (hmr : m ≤ r) {P : ℕ → ℂ[X]}
    (hJ : SplineJoinsBelow r j N P) {u : ℝ → ℂ}
    (hu : ∀ n < N, ∀ x ∈ dyadicIco j n, u x = polyFun (P n) x) {h x : ℝ} (hh0 : 0 ≤ h)
    (hh : h ≤ 1 / 2 ^ j) (hx : 0 ≤ x) (hxm : x + m * h < N / 2 ^ j) :
    higherDiff m h u x = higherDiff m h (polyFun (P ⌊2 ^ j * x⌋₊)) x +
      ∑ l ∈ Finset.Ioc ⌊2 ^ j * x⌋₊ (⌊2 ^ j * x⌋₊ + r),
        jumpCoeff r N P l * higherDiff m h (truncPow r ((l : ℝ) / 2 ^ j)) x := by
  have hkh : (2 : ℝ) ^ j * h ≤ 1 := by
    rw [le_div_iff₀ (by positivity)] at hh
    linarith
  have hdec : ∀ i ∈ Finset.range (m + 1), u (x + i * h) =
      polyFun (P ⌊2 ^ j * x⌋₊) (x + i * h) + ∑ l ∈ Finset.Ioc ⌊2 ^ j * x⌋₊ (⌊2 ^ j * x⌋₊ + r),
        jumpCoeff r N P l * truncPow r ((l : ℝ) / 2 ^ j) (x + i * h) := fun i hi => by
    have hi' : i ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    have hih : (i : ℝ) * h ≤ m * h := mul_le_mul_of_nonneg_right (by exact_mod_cast hi') hh0
    exact polyFun_eq_add_sum_jumps hJ hu hx (le_add_of_nonneg_right (mul_nonneg
      (Nat.cast_nonneg i) hh0)) (by linarith) (floor_add_mul_le hx hh0 hkh (hi'.trans hmr))
  rw [higherDiff_apply, Finset.sum_congr rfl fun i hi => by rw [hdec i hi] ]
  simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  · exact (higherDiff_apply _ _ _ _).symm
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [higherDiff_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring

/-- **Differences of a spline are differences of its jumps**: on `[x, x + rh]` with
`x + rh < N 2^(-j)` and `h ≤ 2^(-j)`,
`Δ_h^r u(x) = ∑_{n₀ < m ≤ n₀ + r} c_m Δ_h^r (· - ξ_m)_+^(r-1)(x)`, since the piece has
`Δ_h^r P_{n₀} = 0` (`Interval.higherDiff_eq_add_sum_jumps` with `m = r`). -/
theorem higherDiff_eq_sum_jumps {r j N : ℕ} {P : ℕ → ℂ[X]} (hP : ∀ m, P m ∈ degreeLT ℂ r)
    (hJ : SplineJoinsBelow r j N P) {u : ℝ → ℂ}
    (hu : ∀ m < N, ∀ x ∈ dyadicIco j m, u x = polyFun (P m) x) {h x : ℝ} (hh0 : 0 ≤ h)
    (hh : h ≤ 1 / 2 ^ j) (hx : 0 ≤ x) (hxr : x + r * h < N / 2 ^ j) :
    higherDiff r h u x = ∑ m ∈ Finset.Ioc ⌊2 ^ j * x⌋₊ (⌊2 ^ j * x⌋₊ + r),
      jumpCoeff r N P m * higherDiff r h (truncPow r ((m : ℝ) / 2 ^ j)) x := by
  have hpoly : higherDiff r h (polyFun (P ⌊2 ^ j * x⌋₊)) x = 0 :=
    congrFun (higherDiff_polynomial (hP _) h) x
  rw [higherDiff_eq_add_sum_jumps le_rfl hJ hu hh0 hh hx hxr, hpoly, zero_add]

/-! ### The local estimate -/

/-- **The jumps are bounded by the neighbouring pieces**: for `0 < m < N` and `L = 2^(-j)`,
`|c_m| L^(r-1) ≤ K 2^(j/p) (m_m^(1/p) + m_{m-1}^(1/p))`, from
`c_m L^(r-1) = P_m(ξ_m + L) - P_{m-1}(ξ_m + L)` and Nikolskii's inequality, for `P_{m-1}` on the
doubled interval. -/
theorem enorm_jumpCoeff_le {r j N : ℕ} {P : ℕ → ℂ[X]} (hP : ∀ m, P m ∈ degreeLT ℂ r)
    (hJ : SplineJoinsBelow r j N P) {u : ℝ → ℂ}
    (hu : ∀ m < N, ∀ x ∈ dyadicIco j m, u x = polyFun (P m) x) {K : ℝ≥0∞}
    (hK : NikolskiiBound p r K) (hp : p ≠ ∞) {m : ℕ} (h0 : 0 < m) (hm : m < N) :
    ‖jumpCoeff r N P m‖ₑ * ENNReal.ofReal (1 / 2 ^ j) ^ (r - 1) ≤
      K * ENNReal.ofReal (2 ^ j) ^ (1 / p.toReal) * (localMass p j u m ^ (1 / p.toReal) +
        localMass p j u (m - 1) ^ (1 / p.toReal)) := by
  have hL : (0 : ℝ) < 1 / 2 ^ j := by positivity
  have hinv : (1 / (2 : ℝ) ^ j)⁻¹ = 2 ^ j := by rw [one_div, inv_inv]
  have hval : polyFun (P m) ((m : ℝ) / 2 ^ j + 1 / 2 ^ j) -
      polyFun (P (m - 1)) ((m : ℝ) / 2 ^ j + 1 / 2 ^ j) =
      jumpCoeff r N P m * (((1 / 2 ^ j : ℝ) ^ (r - 1) : ℝ) : ℂ) := by
    have h := congrArg (fun P => polyFun P ((m : ℝ) / 2 ^ j + 1 / 2 ^ j))
      (sub_eq_jumpCoeff hJ h0 hm)
    simp only [polyFun, eval_sub, eval_mul, eval_C, eval_pow, eval_X] at h ⊢
    rw [h]
    congr 1
    push_cast
    ring
  have h1 : ‖polyFun (P m) ((m : ℝ) / 2 ^ j + 1 / 2 ^ j)‖ₑ ≤
      K * ENNReal.ofReal (2 ^ j) ^ (1 / p.toReal) * localMass p j u m ^ (1 / p.toReal) := by
    have := hK.enorm_le (hP m) ((m : ℝ) / 2 ^ j) hL
      (x := (m : ℝ) / 2 ^ j + 1 / 2 ^ j) ⟨by linarith, le_rfl⟩
    rwa [hinv, eLpNorm_piece_eq_localMass hp (hu m hm)] at this
  have h2 : ‖polyFun (P (m - 1)) ((m : ℝ) / 2 ^ j + 1 / 2 ^ j)‖ₑ ≤
      K * ENNReal.ofReal (2 ^ j) ^ (1 / p.toReal) * localMass p j u (m - 1) ^ (1 / p.toReal) := by
    have hξ : (m : ℝ) / 2 ^ j - 1 / 2 ^ j = ((m - 1 : ℕ) : ℝ) / 2 ^ j := by
      rw [Nat.cast_sub h0, Nat.cast_one, sub_div]
    have := hK _ (hP (m - 1)) ((m : ℝ) / 2 ^ j - 1 / 2 ^ j) hL ((m : ℝ) / 2 ^ j + 1 / 2 ^ j)
      ⟨by linarith, by linarith⟩
    rwa [hinv, hξ, eLpNorm_piece_eq_localMass hp (hu (m - 1) (by omega))] at this
  calc ‖jumpCoeff r N P m‖ₑ * ENNReal.ofReal (1 / 2 ^ j) ^ (r - 1)
      = ‖polyFun (P m) ((m : ℝ) / 2 ^ j + 1 / 2 ^ j) -
          polyFun (P (m - 1)) ((m : ℝ) / 2 ^ j + 1 / 2 ^ j)‖ₑ := by
        rw [hval, eNorm_mul, ← ofReal_norm (((1 / 2 ^ j : ℝ) ^ (r - 1) : ℝ) : ℂ),
          Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity),
          ENNReal.ofReal_pow hL.le]
    _ ≤ ‖polyFun (P m) ((m : ℝ) / 2 ^ j + 1 / 2 ^ j)‖ₑ +
          ‖polyFun (P (m - 1)) ((m : ℝ) / 2 ^ j + 1 / 2 ^ j)‖ₑ :=
        eNorm_sub_le
    _ ≤ _ := by rw [mul_add]; exact add_le_add h1 h2

/-- **A jump term of a spline, for every order**: for `h ≥ 0` and a knot `l 2^(-j)` with
`n₀ < l ≤ n₀ + r`, `n₀ = ⌊2^j x⌋`, the term `c_l Δ_h^m (· - l 2^(-j))_+^(r-1)(x)` is at most
`2 · 2^m m^(r-1) K (2^j h)^(r-1) 2^(j/p) (∑_{l' ≤ r} M_{n₀+l'})^(1/p)`: the jump coefficient is
bounded by `Interval.enorm_jumpCoeff_le` and the difference of the truncated power by
`2^m (mh)^(r-1)`. -/
theorem enorm_jumpCoeff_mul_higherDiff_truncPow_le_any_order {r j N : ℕ} (m : ℕ) {P : ℕ → ℂ[X]}
    (hP : ∀ n, P n ∈ degreeLT ℂ r) (hJ : SplineJoinsBelow r j N P) {u : ℝ → ℂ}
    (hu : ∀ n < N, ∀ x ∈ dyadicIco j n, u x = polyFun (P n) x) {K : ℝ≥0∞}
    (hK : NikolskiiBound p r K) (hp : p ≠ ∞) {h x : ℝ} (hh0 : 0 ≤ h)
    {l : ℕ} (hl : l ∈ Finset.Ioc ⌊2 ^ j * x⌋₊ (⌊2 ^ j * x⌋₊ + r)) :
    ‖jumpCoeff r N P l * higherDiff m h (truncPow r ((l : ℝ) / 2 ^ j)) x‖ₑ ≤
      2 * 2 ^ m * (m : ℝ≥0∞) ^ (r - 1) * K * ENNReal.ofReal (2 ^ j * h) ^ (r - 1) *
        ENNReal.ofReal (2 ^ j) ^ (1 / p.toReal) *
          (∑ l' ∈ Finset.range (r + 1), localMass p j u (⌊2 ^ j * x⌋₊ + l')) ^ (1 / p.toReal) := by
  have hpos : (0 : ℝ) < 2 ^ j := by positivity
  have hL : (0 : ℝ) < 1 / 2 ^ j := by positivity
  set n₀ := ⌊2 ^ j * x⌋₊
  set S := ∑ l ∈ Finset.range (r + 1), localMass p j u (n₀ + l)
  set σ := ENNReal.ofReal (2 ^ j * h)
  have hmass : ∀ l ≤ r, localMass p j u (n₀ + l) ^ (1 / p.toReal) ≤ S ^ (1 / p.toReal) :=
    fun l hl => by
      gcongr
      exact localMass_le_sum_range j _ n₀ hl
  have hfl' : 2 ^ j * x < (n₀ : ℝ) + 1 := Nat.lt_floor_add_one _
  have hscale : ENNReal.ofReal (m * h) ^ (r - 1) =
      ENNReal.ofReal (1 / 2 ^ j) ^ (r - 1) * ((m : ℝ≥0∞) ^ (r - 1) * σ ^ (r - 1)) := by
    rw [← mul_pow, ← mul_pow, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
      ← ENNReal.ofReal_mul hL.le]
    congr 2
    field_simp
  obtain ⟨hl1, hl2⟩ := Finset.mem_Ioc.1 hl
  have hxl : x < (l : ℝ) / 2 ^ j := by
    rw [lt_div_iff₀ hpos]
    have : (n₀ : ℝ) + 1 ≤ l := by exact_mod_cast hl1
    linarith
  rw [eNorm_mul]
  refine (mul_le_mul' le_rfl (enorm_higherDiff_truncPow_le_of_lt r m hh0 hxl)).trans ?_
  rcases lt_or_ge l N with hlN | hlN
  · have hc := enorm_jumpCoeff_le hP hJ hu hK hp (by omega) hlN
    have hS : localMass p j u l ^ (1 / p.toReal) + localMass p j u (l - 1) ^ (1 / p.toReal) ≤
        2 * S ^ (1 / p.toReal) := by
      rw [two_mul]
      refine add_le_add ?_ ?_
      · rw [show l = n₀ + (l - n₀) by omega]; exact hmass _ (by omega)
      · rw [show l - 1 = n₀ + (l - 1 - n₀) by omega]; exact hmass _ (by omega)
    calc ‖jumpCoeff r N P l‖ₑ * (2 ^ m * ENNReal.ofReal (m * h) ^ (r - 1))
        = 2 ^ m * (m : ℝ≥0∞) ^ (r - 1) * σ ^ (r - 1) *
            (‖jumpCoeff r N P l‖ₑ * ENNReal.ofReal (1 / 2 ^ j) ^ (r - 1)) := by
          rw [hscale]; ring
      _ ≤ 2 ^ m * (m : ℝ≥0∞) ^ (r - 1) * σ ^ (r - 1) *
            (K * ENNReal.ofReal (2 ^ j) ^ (1 / p.toReal) * (2 * S ^ (1 / p.toReal))) :=
          mul_le_mul' le_rfl (hc.trans (mul_le_mul' le_rfl hS))
      _ = _ := by ring
  · have h0 : jumpCoeff r N P l = 0 := by
      simp only [jumpCoeff, show ¬ (0 < l ∧ l < N) by omega, ↓reduceIte]
    rw [h0, eNorm_zero, zero_mul]
    exact zero_le

/-- The constant of the pointwise bound,
`G = 2 r 2^r K (r 2^j h)^(r-1) 2^(j/p)`. -/
noncomputable def splineStripConst (r j : ℕ) (K : ℝ≥0∞) (h : ℝ) (p : ℝ≥0∞) : ℝ≥0∞ :=
  2 * r * 2 ^ r * K * ENNReal.ofReal (r * (2 ^ j * h)) ^ (r - 1) *
    ENNReal.ofReal (2 ^ j) ^ (1 / p.toReal)

/-- **Pointwise bound for differences of splines**: on the strips left of the knots,
`|Δ_h^r u(x)| ≤ G (∑_{l ≤ r} m_{n₀+l})^(1/p)` for `x + rh < N 2^(-j)`. -/
theorem enorm_higherDiff_spline_le {r j N : ℕ} {P : ℕ → ℂ[X]} (hP : ∀ m, P m ∈ degreeLT ℂ r)
    (hJ : SplineJoinsBelow r j N P) {u : ℝ → ℂ}
    (hu : ∀ m < N, ∀ x ∈ dyadicIco j m, u x = polyFun (P m) x) {K : ℝ≥0∞}
    (hK : NikolskiiBound p r K) (hp : p ≠ ∞) {h x : ℝ} (hh0 : 0 ≤ h) (hh : h ≤ 1 / 2 ^ j)
    (hx : 0 ≤ x) (hxr : x + r * h < N / 2 ^ j) :
    ‖higherDiff r h u x‖ₑ ≤ splineStripConst r j K h p *
      (∑ l ∈ Finset.range (r + 1), localMass p j u (⌊2 ^ j * x⌋₊ + l)) ^ (1 / p.toReal) := by
  -- each jump contributes at most `2 · 2^r K (r 2^j h)^(r-1) 2^(j/p)` times the local masses
  have hterm : ∀ m ∈ Finset.Ioc ⌊2 ^ j * x⌋₊ (⌊2 ^ j * x⌋₊ + r), ‖jumpCoeff r N P m *
      higherDiff r h (truncPow r ((m : ℝ) / 2 ^ j)) x‖ₑ ≤
        2 * 2 ^ r * K * ENNReal.ofReal (r * (2 ^ j * h)) ^ (r - 1) *
          ENNReal.ofReal (2 ^ j) ^ (1 / p.toReal) *
            (∑ l ∈ Finset.range (r + 1), localMass p j u (⌊2 ^ j * x⌋₊ + l)) ^ (1 / p.toReal) :=
    fun m hm => (enorm_jumpCoeff_mul_higherDiff_truncPow_le_any_order r hP hJ hu hK hp hh0
      hm).trans_eq
        (by rw [ENNReal.ofReal_mul (Nat.cast_nonneg r), ENNReal.ofReal_natCast, mul_pow]; ring)
  rw [higherDiff_eq_sum_jumps hP hJ hu hh0 hh hx hxr]
  refine (eNorm_sum_le _ _).trans ((Finset.sum_le_sum hterm).trans ?_)
  rw [Finset.sum_const, Nat.card_Ioc, Nat.add_sub_cancel_left, nsmul_eq_mul, splineStripConst]
  exact le_of_eq (by ring)

/-! ### The inverse inequality -/

/-- **The local inverse estimate for splines**: let `u` be a spline of level `j` below `N`, a
piecewise polynomial on `[0, ∞)`, and `0 ≤ h ≤ 2^(-j)`. On a measurable `S ⊆ [0, 1]` with
`x + rh < N 2^(-j)` for almost every `x ∈ S`, and if the local masses of `r + 1` consecutive
pieces add up to at most `(r + 1) B^p`, then `‖Δ_h^r u‖_{L_p(S)} ≤ G (rh (r + 1))^(1/p) B`. -/
theorem eLpNorm_higherDiff_spline_le {r j N : ℕ} {P : ℕ → ℂ[X]} (hP : ∀ m, P m ∈ degreeLT ℂ r)
    (hJ : SplineJoinsBelow r j N P) {u : ℝ → ℂ}
    (hu : ∀ m < N, ∀ x ∈ dyadicIco j m, u x = polyFun (P m) x) (hpp : IsPiecewisePoly r j u)
    (hum : Measurable u) {K : ℝ≥0∞} (hK : NikolskiiBound p r K) (hp : p ≠ ∞) {h : ℝ}
    (hh0 : 0 ≤ h) (hh : h ≤ 1 / 2 ^ j) {S : Set ℝ} (hSm : MeasurableSet S) (hS : S ⊆ Icc 0 1)
    (hSN : ∀ᵐ x ∂volume.restrict S, x + r * h < N / 2 ^ j) {B : ℝ≥0∞}
    (hB : ∑ n ∈ Finset.range (2 ^ j), ∑ l ∈ Finset.range (r + 1), localMass p j u (n + l) ≤
      (r + 1) * B ^ p.toReal) :
    eLpNorm (higherDiff r h u) p (volume.restrict S) ≤
      splineStripConst r j K h p * (ENNReal.ofReal (r * h) * (r + 1)) ^ (1 / p.toReal) * B := by
  refine eLpNorm_higherDiff_le_of_pointwise hp hpp hum hSm hS hh0 ?_ hB
  filter_upwards [hSN, ae_restrict_mem hSm] with x hxN hxS _
  exact enorm_higherDiff_spline_le hP hJ hu hK hp hh0 hh (hS hxS).1 hxN

/-- The constant of the inverse inequality for splines,
`2 r 2^r K r^(r-1) (r (r + 1))^(1/p)`. -/
noncomputable def splineInverseConst (r : ℕ) (K p : ℝ≥0∞) : ℝ≥0∞ :=
  2 * r * 2 ^ r * K * (r : ℝ≥0∞) ^ (r - 1) * ((r * (r + 1) : ℕ) : ℝ≥0∞) ^ (1 / p.toReal)

omit [Fact (1 ≤ p)] in
/-- The constant of the inverse inequality for splines is finite. -/
theorem splineInverseConst_ne_top (r : ℕ) {K : ℝ≥0∞} (hK : K ≠ ∞) :
    splineInverseConst r K p ≠ ∞ := by
  unfold splineInverseConst
  refine ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top
    (ENNReal.mul_ne_top (by simp) (ENNReal.natCast_ne_top r)) (by simp)) hK)
    (ENNReal.pow_ne_top (ENNReal.natCast_ne_top r))) ?_
  exact ENNReal.rpow_ne_top_of_nonneg (by positivity) (ENNReal.natCast_ne_top _)

omit [Fact (1 ≤ p)] in
/-- The bound of the local estimate in terms of `2^j h`:
`G (rh (r + 1))^(1/p) = C (2^j h)^(r - 1 + 1/p)`. -/
theorem splineStripConst_mul_eq (r j : ℕ) (K : ℝ≥0∞) (h : ℝ) :
    splineStripConst r j K h p * (ENNReal.ofReal (r * h) * (r + 1)) ^ (1 / p.toReal) =
      splineInverseConst r K p *
        ENNReal.ofReal (2 ^ j * h) ^ (((r - 1 : ℕ) : ℝ) + 1 / p.toReal) := by
  have hθ : (0 : ℝ) ≤ 1 / p.toReal := by positivity
  have h1 : ENNReal.ofReal (r * (2 ^ j * h)) = (r : ℝ≥0∞) * ENNReal.ofReal (2 ^ j * h) := by
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg r), ENNReal.ofReal_natCast]
  rw [ENNReal.rpow_add_of_nonneg _ _ (Nat.cast_nonneg _) hθ, ENNReal.rpow_natCast]
  calc splineStripConst r j K h p * (ENNReal.ofReal (r * h) * (r + 1)) ^ (1 / p.toReal)
      = 2 * r * 2 ^ r * K * ENNReal.ofReal (r * (2 ^ j * h)) ^ (r - 1) *
          (ENNReal.ofReal (2 ^ j) ^ (1 / p.toReal) *
            (ENNReal.ofReal (r * h) * (r + 1)) ^ (1 / p.toReal)) := by
        rw [splineStripConst]; ring
    _ = _ := by
        rw [ofReal_two_pow_rpow_mul_eq r j h hθ, ENNReal.mul_rpow_of_nonneg _ _ hθ, h1, mul_pow,
          splineInverseConst]
        ring

omit [Fact (1 ≤ p)] in
/-- The local estimate for splines in dyadic form: for `j ≤ k` and `0 ≤ h ≤ 2^(-k)`,
`G (rh (r + 1))^(1/p) B ≤ C 2^(-(k-j)(r - 1 + 1/p)) B`. -/
theorem splineStripConst_mul_le {r j k : ℕ} (hjk : j ≤ k) (K : ℝ≥0∞) {h : ℝ}
    (hh : h ≤ 1 / 2 ^ k) (B : ℝ≥0∞) :
    splineStripConst r j K h p * (ENNReal.ofReal (r * h) * (r + 1)) ^ (1 / p.toReal) * B ≤
      splineInverseConst r K p * dyadicWeight (-(((r - 1 : ℕ) : ℝ) + 1 / p.toReal)) (k - j) *
        B := by
  rw [splineStripConst_mul_eq r j K h]
  exact mul_le_mul' (mul_le_mul' le_rfl (ENNReal.ofReal_two_pow_mul_rpow_le hjk hh (by positivity)))
    le_rfl

omit [Fact (1 ≤ p)] in
/-- The constant of the inverse inequality is at least `2^r`. -/
theorem two_pow_le_two_pow_mul_one_add (r : ℕ) (c : ℝ≥0∞) : (2 : ℝ≥0∞) ^ r ≤ 2 ^ r * (1 + c) :=
  le_mul_of_one_le_right zero_le le_self_add

omit [Fact (1 ≤ p)] in
/-- The constant of the inverse inequality dominates the local constant. -/
theorem le_two_pow_mul_one_add (r : ℕ) (c : ℝ≥0∞) : c ≤ 2 ^ r * (1 + c) :=
  le_add_self.trans (le_mul_of_one_le_left zero_le (one_le_pow₀ one_le_two))

/-- **The local inverse estimate for splines on `[0, 1]`**: for the pieces `Q` of a spline of
level `j` and `0 ≤ h ≤ 2^(-j)`,
`‖Δ_h^r (ppFun j Q)‖_{L_p[0, 1 - rh]} ≤ S_j(h) (r h (r + 1))^(1/p) ‖ppFun j Q‖_{L_p[0,1]}` with the
strip constant `S_j(h)` of `Interval.splineStripConst`. -/
theorem eLpNorm_higherDiff_ppFun_spline_le {r j : ℕ} {Q : ℕ → ℂ[X]}
    (hQ : ∀ n, Q n ∈ degreeLT ℂ r) (hJ : SplineJoins r j Q) {K : ℝ≥0∞}
    (hKb : NikolskiiBound p r K) (hp : p ≠ ∞) {h : ℝ} (hh0 : 0 ≤ h) (hhj : h ≤ 1 / 2 ^ j) :
    eLpNorm (higherDiff r h (ppFun j Q)) p (volume.restrict (Icc 0 (1 - r * h))) ≤
      splineStripConst r j K h p * (ENNReal.ofReal (r * h) * (r + 1)) ^ (1 / p.toReal) *
        eLpNorm (ppFun j Q) p unitVol := by
  have hrh : (0 : ℝ) ≤ r * h := mul_nonneg (Nat.cast_nonneg r) hh0
  have hSN : ∀ᵐ x ∂volume.restrict (Icc 0 (1 - r * h)), x + r * h < (2 ^ j : ℕ) / 2 ^ j := by
    rw [← Measure.restrict_congr_set Ico_ae_eq_Icc]
    filter_upwards [ae_restrict_mem measurableSet_Ico] with x hx
    rw [show ((2 ^ j : ℕ) : ℝ) / 2 ^ j = 1 by push_cast; field_simp]
    linarith [hx.2]
  exact eLpNorm_higherDiff_spline_le hQ hJ.below (fun m hm x hx => ppFun_eq_of_mem Q hm hx)
    (isPiecewisePoly_ppFun hQ j) (measurable_ppFun j Q) hKb hp hh0 hhj measurableSet_Icc
    (Icc_subset_Icc le_rfl (by linarith)) hSN (sum_sum_localMass_le hp j r Q)

/-- **The inverse inequality for dyadic splines**, of order `θ = r - 1 + 1/p`: there is
`C_B < ∞` with `ω_r(a, 2^(-k), [0, 1])_p ≤ C_B 2^(-(k-j)θ) ‖a‖_p` for every spline `a` of order `r`
and level `j` (and `k - j` truncated at `0`). -/
theorem exists_inverse_splineScheme {r : ℕ} (hp : p ≠ ∞) :
    ∃ CB : ℝ≥0∞, CB ≠ ∞ ∧ ∀ j k : ℕ, ∀ a ∈ splineScheme p r (2 ^ j),
      lpModulus p r a k ≤
        CB * dyadicWeight (-(((r - 1 : ℕ) : ℝ) + 1 / p.toReal)) (k - j) * ‖a‖ₑ := by
  obtain ⟨K, hK, hKb⟩ := enorm_polyFun_le (p := p) r hp
  refine ⟨2 ^ r * (1 + splineInverseConst r K p),
    ENNReal.mul_ne_top (by simp) (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top,
      splineInverseConst_ne_top r hK⟩), fun j k a ha => ?_⟩
  obtain ⟨Q, hQ, hJ, hae⟩ := mem_splineScheme_two_pow.1 ha
  rcases lt_or_ge k j with hkj | hjk
  · rw [Nat.sub_eq_zero_of_le hkj.le, ENNReal.dyadicWeight_zero_right, mul_one]
    exact (lpModulus_le r a k).trans (by gcongr; exact two_pow_le_two_pow_mul_one_add r _)
  · have hnorm : ‖a‖ₑ = eLpNorm (ppFun j Q) p unitVol := by
      rw [Lp.eNorm_def]
      exact eLpNorm_congr_ae hae
    rw [lpModulus, modulus_congr_ae hae, hnorm, modulus_eq_iSup_nonneg]
    refine iSup₂_le fun h hh => ?_
    have hhj : h ≤ 1 / 2 ^ j := hh.2.trans (one_div_le_one_div_of_le (by positivity)
      (pow_le_pow_right₀ (by norm_num) hjk))
    calc eLpNorm (higherDiff r h (ppFun j Q)) p (volume.restrict (Icc 0 (1 - r * h)))
        ≤ splineStripConst r j K h p * (ENNReal.ofReal (r * h) * (r + 1)) ^
            (1 / p.toReal) * eLpNorm (ppFun j Q) p unitVol :=
          eLpNorm_higherDiff_ppFun_spline_le hQ hJ hKb hp hh.1 hhj
      _ ≤ splineInverseConst r K p * dyadicWeight (-(((r - 1 : ℕ) : ℝ) + 1 / p.toReal)) (k - j) *
            eLpNorm (ppFun j Q) p unitVol := splineStripConst_mul_le hjk K hh.2 _
      _ ≤ 2 ^ r * (1 + splineInverseConst r K p) *
            dyadicWeight (-(((r - 1 : ℕ) : ℝ) + 1 / p.toReal)) (k - j) *
            eLpNorm (ppFun j Q) p unitVol := by
          gcongr
          exact le_two_pow_mul_one_add r _

end Interval
