/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Orlicz.Maximum
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.MultiscaleEllipticity
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.MeasureTheory.Order.Group.Lattice

/-!
# GridWeights

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Grid weights, the triadic grid maximum, and the `e.maxy.bound` lift

## The tex objects

`Lambda_{s,q}(cu_m; a)` is `(c_{sq} sum_{k <= m} 3^{-sq(m-k)} max_{z in 3^k Z^d
cap cu_m} |b(z+cu_k;a)|^{q/2})^{2/q}`.  Two objects occur:

* the **grid maximum** `max_{z in 3^k Z^d cap cu_m} |b(z+cu_k; a)|`, which is
  exactly a supremum of absolute values over a finite index set --- here
  `gridSupAbs`, instantiated at `Homogenization.descendantsAtScale`, whose
  members are exactly the triadic subcubes `z + cu_k` of `cu_m`;
* the **grid weight** `3^{-rho(m-k)}` carrying the scale decay.  Following the
  proof's own indexing (the binder `n <= m-1` is printed, and in
  `p.bfA.multiscalebound` itself, so `m - n = k+1` for `k : ℕ`), `gridWeight
  rho k = (3^{-rho})^{k+1}`.  S: this family covers gaps `>= 1` only; the
  source sum's gap-`0` term (CoarseGraining's `LambdaSqFinite` at `n = 0`) is
  outside it, and the identification theorem below is likewise stated at scale
  `m-1-k` only.

The proof needs three quantitative facts about these:

1. **the polynomial-times-geometric sum**, because `e.maxy.bound` costs a factor
   `(3 log N)^{1/sigma}` at `N = 3^{d(m-n)}` cubes, i.e. a factor polynomial in
   `m - n` (`gridNetConst_rpow_eq`);
2. **the pole order** of that sum, which is what turns per-scale amplitudes into
   the printed `(2s - gamma)^{-p}` poles (`polyGridWeight_tsum_le`,
   `one_sub_rpow_neg_inv_le`);
3. **the collar absorption** `gridWeight a k * 3^{g(k+1)} = gridWeight (a-g) k`,
   which is how the per-scale factor `3^{gamma(m-n)}` of `e.bL.multiscale` moves
   the pole from `2s` to `2s - gamma`.

## Main results

* `gridWeight`, `gridWeight_summable`, `gridWeight_tsum_le`.
* `polyGridWeight_summable`, `polyGridWeight_tsum_le` --- the scale sum with the
  explicit constant `p ! * ((1 - 3^{-rho})^{-1})^{p+1}`.
* `one_sub_rpow_neg_inv_le` --- `(1 - 3^{-rho})^{-1} <= 1 + rho^{-1}`, the
  conversion of the geometric pole into the printed algebraic pole.
* `gridSupAbs` and its nonnegativity, measurability, and two-sided `sup'` A.
* `gridSupAbs_isBigOWith` --- `e.maxy.bound` for an arbitrary nonempty finite
  index set, using this repository's proved local implementation of `l.maximums.Gamma.s`.
* `card_descendantsAtScale_originCube` --- the grid has exactly `3^{d(k+1)}`
  members, the cardinality the source's `N` refers to.
* `gridSupAbs_descendants_isBigOWith` --- **the `e.maxy.bound` lift at the
  triadic grid**: a common per-cube `Gamma_sigma` bound over the grid
  `3^{m-1-k} Z^d cap cu_m` lifts to the grid maximum at the amplitude
  `gridNetConst d sigma * (k+1)^{1/sigma} * A`.

## Divergences from the source, disclosed

* The source writes `(3 log N)^{1/sigma}`; the proved `l.maximums.Gamma.s` of
  this repository (`Provider/Orlicz/Maximum.lean`) writes `(3 max 1 (log
  N))^{1/sigma}`, an enlargement that removes the source proof's `N >= 2`
  restriction.  On the triadic grid `N = 3^{d(k+1)} >= 3`, so `max 1 (log N) =
  log N` and the two agree; this is proved here (`gridNetConst_rpow_eq` is
  applied to the bare `log`).
* The `k`-independent constant `(3 d log 3)^{1/sigma}` is made explicit as
  `gridNetConst`; the source leaves it inside a generic `C`.
* S: `gridNetConst_rpow_eq` emits `((k:ℝ)+1) ^ (sigma⁻¹ : ℝ)` (`Real.rpow`)
  while `polyGridWeight_tsum_le` consumes `((k:ℝ)+1) ^ (p : ℕ)`
  (`Monoid.npow`); no bridge lemma is proved here.
* (CoarseGraining carries a second, Frobenius-normed `LambdaSqFinite` in
  `Deterministic/MultiscaleQuantities`; the identification here fully qualifies
  `Book.Ch02.*`, so it is unambiguous despite the `open Homogenization`.)

## References

* ABK26, `l.maximums.Gamma.s` (`e.maxy.bound`).
* ABK26, coarse-grained ellipticity constants.
* ABK26, `p.cg.ellipticity.bounds` proof from `p.bfA.multiscalebound`.
-/

namespace Algsuperdiff.Section3.Provider.CoarseEllipticity

open MeasureTheory
open HCPolySupport HCPolySupport.IndependentSums

noncomputable section

/-! ## 1. The grid weight -/

theorem one_lt_log_three : 1 < Real.log 3 := by
  have h3 : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  exact (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3)).2 h3


/-- The grid weight `3^{-rho(m-n)}` at `m - n = k + 1`.

The proof of `p.cg.ellipticity.bounds` sums over `n <= m - 1`, so the scale gap
`m - n` runs over the positive integers; `k` is the shifted index. -/
noncomputable def gridWeight (rho : ℝ) (k : ℕ) : ℝ :=
  ((3 : ℝ) ^ (-rho)) ^ (k + 1)

theorem rpow_neg_lt_one {rho : ℝ} (hrho : 0 < rho) : (3 : ℝ) ^ (-rho) < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_iff_pos.2 hrho)

theorem rpow_neg_nonneg (rho : ℝ) : (0 : ℝ) ≤ (3 : ℝ) ^ (-rho) :=
  Real.rpow_nonneg (by norm_num) _

theorem rpow_neg_pos (rho : ℝ) : (0 : ℝ) < (3 : ℝ) ^ (-rho) :=
  Real.rpow_pos_of_pos (by norm_num) _

theorem gridWeight_pos (rho : ℝ) (k : ℕ) : 0 < gridWeight rho k :=
  pow_pos (rpow_neg_pos rho) _

theorem gridWeight_nonneg (rho : ℝ) (k : ℕ) : 0 ≤ gridWeight rho k :=
  (gridWeight_pos rho k).le

theorem one_sub_rpow_neg_pos {rho : ℝ} (hrho : 0 < rho) :
    0 < 1 - (3 : ℝ) ^ (-rho) := by
  have := rpow_neg_lt_one hrho
  linarith

private theorem rpow_neg_mul_le_one_sub {rho : ℝ} (hrho : 0 < rho) :
    (3 : ℝ) ^ (-rho) * rho ≤ 1 - (3 : ℝ) ^ (-rho) := by
  have hkey : rho ≤ (3 : ℝ) ^ rho - 1 := by
    have hexp : (3 : ℝ) ^ rho = Real.exp (rho * Real.log 3) := by
      rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
      ring_nf
    have hlin : rho * Real.log 3 + 1 ≤ Real.exp (rho * Real.log 3) :=
      Real.add_one_le_exp _
    have hlog : 1 ≤ Real.log 3 := one_lt_log_three.le
    have hmono : rho * 1 ≤ rho * Real.log 3 :=
      mul_le_mul_of_nonneg_left hlog hrho.le
    rw [hexp]
    linarith
  have hself : (3 : ℝ) ^ (-rho) * (3 : ℝ) ^ rho = 1 := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    simp
  have hstep := mul_le_mul_of_nonneg_left hkey (rpow_neg_nonneg rho)
  rw [mul_sub, hself, mul_one] at hstep
  linarith

/-- The geometric pole is bounded by the printed algebraic pole:
`(1 - 3^{-rho})^{-1} <= 1 + rho^{-1}`.

This is the step that converts the summation constant into the source's
`(2s - gamma)^{-p}` shape. -/
theorem one_sub_rpow_neg_inv_le {rho : ℝ} (hrho : 0 < rho) :
    (1 - (3 : ℝ) ^ (-rho))⁻¹ ≤ 1 + rho⁻¹ := by
  have hpos : 0 < 1 - (3 : ℝ) ^ (-rho) := one_sub_rpow_neg_pos hrho
  have hmul := rpow_neg_mul_le_one_sub hrho
  have hrhoinv : 0 < rho⁻¹ := inv_pos.2 hrho
  rw [inv_le_iff_one_le_mul₀ hpos]
  have hexpand : (1 + rho⁻¹) * (1 - (3 : ℝ) ^ (-rho))
      = 1 - (3 : ℝ) ^ (-rho) + rho⁻¹ * (1 - (3 : ℝ) ^ (-rho)) := by ring
  have hstep : rho⁻¹ * ((3 : ℝ) ^ (-rho) * rho) ≤ rho⁻¹ * (1 - (3 : ℝ) ^ (-rho)) :=
    mul_le_mul_of_nonneg_left hmul hrhoinv.le
  have hsimp : rho⁻¹ * ((3 : ℝ) ^ (-rho) * rho) = (3 : ℝ) ^ (-rho) := by
    field_simp
  rw [hexpand]
  rw [hsimp] at hstep
  linarith

theorem gridWeight_summable {rho : ℝ} (hrho : 0 < rho) :
    Summable (gridWeight rho) := by
  have hgeom : Summable fun k : ℕ => ((3 : ℝ) ^ (-rho)) ^ k :=
    summable_geometric_of_lt_one (rpow_neg_nonneg rho) (rpow_neg_lt_one hrho)
  have hfun : gridWeight rho
      = fun k : ℕ => (3 : ℝ) ^ (-rho) * ((3 : ℝ) ^ (-rho)) ^ k := by
    funext k
    rw [gridWeight, pow_succ]
    ring
  rw [hfun]
  exact hgeom.mul_left _

/-- The deterministic lane's collapse: the full grid weight sums to at most
`rho^{-1}`. -/
theorem gridWeight_tsum_le {rho : ℝ} (hrho : 0 < rho) :
    ∑' k : ℕ, gridWeight rho k ≤ rho⁻¹ := by
  have hgeom : ∑' k : ℕ, ((3 : ℝ) ^ (-rho)) ^ k = (1 - (3 : ℝ) ^ (-rho))⁻¹ :=
    tsum_geometric_of_lt_one (rpow_neg_nonneg rho) (rpow_neg_lt_one hrho)
  have hfun : gridWeight rho
      = fun k : ℕ => (3 : ℝ) ^ (-rho) * ((3 : ℝ) ^ (-rho)) ^ k := by
    funext k
    rw [gridWeight, pow_succ]
    ring
  have hpos : 0 < 1 - (3 : ℝ) ^ (-rho) := one_sub_rpow_neg_pos hrho
  have hval : ∑' k : ℕ, gridWeight rho k
      = (3 : ℝ) ^ (-rho) * (1 - (3 : ℝ) ^ (-rho))⁻¹ := by
    rw [hfun, tsum_mul_left, hgeom]
  have hmul := rpow_neg_mul_le_one_sub hrho
  rw [hval, mul_inv_le_iff₀ hpos]
  calc (3 : ℝ) ^ (-rho)
      = rho⁻¹ * ((3 : ℝ) ^ (-rho) * rho) := by field_simp
    _ ≤ rho⁻¹ * (1 - (3 : ℝ) ^ (-rho)) :=
        mul_le_mul_of_nonneg_left hmul (inv_pos.2 hrho).le


/-! ## 2. The polynomial-times-geometric scale sum -/

private theorem pow_succ_le_factorial_mul_choose (p k : ℕ) :
    (k + 1) ^ p ≤ Nat.factorial p * (k + p).choose p := by
  have h := Nat.pow_sub_le_descFactorial (k + p) p
  have hidx : k + p + 1 - p = k + 1 := by omega
  rw [hidx, Nat.descFactorial_eq_factorial_mul_choose] at h
  exact h

private theorem cast_pow_succ_le (p k : ℕ) :
    ((k : ℝ) + 1) ^ p ≤ (Nat.factorial p : ℝ) * ((k + p).choose p : ℝ) := by
  have h := pow_succ_le_factorial_mul_choose p k
  have hcast : (((k + 1) ^ p : ℕ) : ℝ) ≤ ((Nat.factorial p * (k + p).choose p : ℕ) : ℝ) := by
    exact_mod_cast h
  push_cast at hcast
  exact hcast

theorem polyGridWeight_summable (p : ℕ) {rho : ℝ} (hrho : 0 < rho) :
    Summable fun k : ℕ => ((k : ℝ) + 1) ^ p * gridWeight rho k := by
  set r : ℝ := (3 : ℝ) ^ (-rho) with hr
  have hr0 : 0 ≤ r := rpow_neg_nonneg rho
  have hr1 : ‖r‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hr0]
    exact rpow_neg_lt_one hrho
  have hmaj : Summable fun k : ℕ => (Nat.factorial p : ℝ) * (((k + p).choose p : ℝ) * r ^ k) := by
    refine Summable.mul_left _ ?_
    simpa using (summable_choose_mul_geometric_of_norm_lt_one (R := ℝ) p hr1)
  refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) (hmaj.mul_left r)
  · exact mul_nonneg (pow_nonneg (by positivity) p) (gridWeight_nonneg rho k)
  · have hgw : gridWeight rho k = r * r ^ k := by
      rw [gridWeight, hr, pow_succ]; ring
    rw [hgw, ← mul_assoc, mul_comm (((k : ℝ) + 1) ^ p) r, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hr0
    calc ((k : ℝ) + 1) ^ p * r ^ k
        ≤ ((Nat.factorial p : ℝ) * ((k + p).choose p : ℝ)) * r ^ k :=
          mul_le_mul_of_nonneg_right (cast_pow_succ_le p k) (pow_nonneg hr0 k)
      _ = (Nat.factorial p : ℝ) * (((k + p).choose p : ℝ) * r ^ k) := by ring

/-- **The scale summation.**  The polynomial cost of `e.maxy.bound` against the
grid weight, with the explicit pole order `p + 1`. -/
theorem polyGridWeight_tsum_le (p : ℕ) {rho : ℝ} (hrho : 0 < rho) :
    ∑' k : ℕ, ((k : ℝ) + 1) ^ p * gridWeight rho k
      ≤ (Nat.factorial p : ℝ) * ((1 - (3 : ℝ) ^ (-rho))⁻¹) ^ (p + 1) := by
  set r : ℝ := (3 : ℝ) ^ (-rho) with hr
  have hr0 : 0 ≤ r := rpow_neg_nonneg rho
  have hrlt : r < 1 := rpow_neg_lt_one hrho
  have hr1 : ‖r‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hr0]
    exact hrlt
  have hchoose : ∑' k : ℕ, ((k + p).choose p : ℝ) * r ^ k = 1 / (1 - r) ^ (p + 1) := by
    simpa using (tsum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) p hr1)
  have hsum_choose : Summable fun k : ℕ => ((k + p).choose p : ℝ) * r ^ k := by
    simpa using (summable_choose_mul_geometric_of_norm_lt_one (R := ℝ) p hr1)
  have hle : ∀ k : ℕ, ((k : ℝ) + 1) ^ p * gridWeight rho k
      ≤ (Nat.factorial p : ℝ) * (((k + p).choose p : ℝ) * r ^ k) := by
    intro k
    have hgw : gridWeight rho k = r * r ^ k := by
      rw [gridWeight, hr, pow_succ]; ring
    rw [hgw, ← mul_assoc]
    calc ((k : ℝ) + 1) ^ p * r * r ^ k
        = (((k : ℝ) + 1) ^ p * r ^ k) * r := by ring
      _ ≤ ((Nat.factorial p : ℝ) * (((k + p).choose p : ℝ) * r ^ k)) * r := by
          refine mul_le_mul_of_nonneg_right ?_ hr0
          calc ((k : ℝ) + 1) ^ p * r ^ k
              ≤ ((Nat.factorial p : ℝ) * ((k + p).choose p : ℝ)) * r ^ k :=
                mul_le_mul_of_nonneg_right (cast_pow_succ_le p k) (pow_nonneg hr0 k)
            _ = (Nat.factorial p : ℝ) * (((k + p).choose p : ℝ) * r ^ k) := by ring
      _ ≤ ((Nat.factorial p : ℝ) * (((k + p).choose p : ℝ) * r ^ k)) * 1 := by
          refine mul_le_mul_of_nonneg_left hrlt.le ?_
          exact mul_nonneg (by positivity) (mul_nonneg (by positivity) (pow_nonneg hr0 k))
      _ = (Nat.factorial p : ℝ) * (((k + p).choose p : ℝ) * r ^ k) := by ring
  calc ∑' k : ℕ, ((k : ℝ) + 1) ^ p * gridWeight rho k
      ≤ ∑' k : ℕ, (Nat.factorial p : ℝ) * (((k + p).choose p : ℝ) * r ^ k) :=
        (polyGridWeight_summable p hrho).tsum_le_tsum hle (hsum_choose.mul_left _)
    _ = (Nat.factorial p : ℝ) * (1 / (1 - r) ^ (p + 1)) := by
        rw [tsum_mul_left, hchoose]
    _ = (Nat.factorial p : ℝ) * ((1 - r)⁻¹) ^ (p + 1) := by
        rw [one_div, inv_pow]

/-! ## 3. The grid net constant of `e.maxy.bound` -/

/-- The dimension-only constant of `e.maxy.bound` at a triadic grid: `(3 d log
3)^{1/sigma}`.  The source hides it inside a generic `C`. -/
noncomputable def gridNetConst (d : ℕ) (sigma : ℝ) : ℝ :=
  (3 * (d : ℝ) * Real.log 3) ^ sigma⁻¹

theorem gridNetConst_nonneg (d : ℕ) (sigma : ℝ) : 0 ≤ gridNetConst d sigma :=
  Real.rpow_nonneg (by positivity) _

/-- The `e.maxy.bound` factor at `N = 3^{d(k+1)}` cubes, split into the
`k`-independent net constant and the polynomial `(k+1)^{1/sigma}`. -/
theorem gridNetConst_rpow_eq (sigma : ℝ) (d k : ℕ) :
    (3 * Real.log ((3 : ℝ) ^ (d * (k + 1)))) ^ sigma⁻¹
      = gridNetConst d sigma * (((k : ℝ) + 1) ^ sigma⁻¹) := by
  have hlog : Real.log ((3 : ℝ) ^ (d * (k + 1))) = (d * (k + 1) : ℕ) * Real.log 3 :=
    Real.log_pow _ _
  have hsplit : 3 * Real.log ((3 : ℝ) ^ (d * (k + 1)))
      = (3 * (d : ℝ) * Real.log 3) * ((k : ℝ) + 1) := by
    rw [hlog]
    push_cast
    ring
  rw [hsplit, gridNetConst,
    Real.mul_rpow (by positivity) (by positivity)]

/-! ## 4. The triadic grid and its cardinality -/

/-- The grid `3^{m-1-k} Z^d cap cu_m` of the proof, represented as the finite set
of triadic subcubes of `cu_m` at scale `m - 1 - k`. -/
theorem card_descendantsAtScale_originCube (d : ℕ) (m : ℤ) (k : ℕ) :
    (descendantsAtScale (originCube d m) (m - 1 - (k : ℤ))).card = 3 ^ (d * (k + 1)) := by
  have hscale : (originCube d m).scale = m := rfl
  have hle : m - 1 - (k : ℤ) ≤ (originCube d m).scale := by
    rw [hscale]; omega
  rw [descendantsAtScale_eq_descendantsAtDepth (originCube d m) hle,
    descendantsAtDepth_card]
  have hdepth : Int.toNat ((originCube d m).scale - (m - 1 - (k : ℤ))) = k + 1 := by
    rw [hscale]
    omega
  rw [hdepth, ← pow_mul]

theorem descendantsAtScale_originCube_nonempty (d : ℕ) (m : ℤ) (k : ℕ) :
    (descendantsAtScale (originCube d m) (m - 1 - (k : ℤ))).Nonempty := by
  have hscale : (originCube d m).scale = m := rfl
  refine descendantsAtScale_nonempty (originCube d m) ?_
  rw [hscale]; omega

/-! ## 5. `gridSupAbs`: the grid maximum -/

variable {Omega ι : Type*}

/-- The grid maximum `max_{z in 3^k Z^d cap cu_m} |X_z|` of the coarse-grained
ellipticity definition, for an arbitrary nonempty finite index set. -/
noncomputable def gridSupAbs (sfin : Finset ι) (hs : sfin.Nonempty)
    (X : ι → Omega → ℝ) (omega : Omega) : ℝ :=
  sfin.sup' hs fun y => |X y omega|

theorem gridSupAbs_nonneg (sfin : Finset ι) (hs : sfin.Nonempty)
    (X : ι → Omega → ℝ) (omega : Omega) : 0 ≤ gridSupAbs sfin hs X omega := by
  obtain ⟨y0, hy0⟩ := hs
  exact le_trans (abs_nonneg _) (Finset.le_sup' (fun y => |X y omega|) hy0)

theorem le_gridSupAbs {sfin : Finset ι} (hs : sfin.Nonempty)
    {X : ι → Omega → ℝ} {y : ι} (hy : y ∈ sfin) (omega : Omega) :
    |X y omega| ≤ gridSupAbs sfin hs X omega :=
  Finset.le_sup' (fun z => |X z omega|) hy

theorem gridSupAbs_le {sfin : Finset ι} (hs : sfin.Nonempty)
    {X : ι → Omega → ℝ} {omega : Omega} {b : ℝ}
    (hb : ∀ y ∈ sfin, |X y omega| ≤ b) :
    gridSupAbs sfin hs X omega ≤ b :=
  Finset.sup'_le hs _ hb

theorem measurable_gridSupAbs [MeasurableSpace Omega] (sfin : Finset ι) (hs : sfin.Nonempty)
    {X : ι → Omega → ℝ} (hm : ∀ y, Measurable (X y)) :
    Measurable (gridSupAbs sfin hs X) := by
  have hfun : gridSupAbs sfin hs X = sfin.sup' hs fun y => fun omega => |X y omega| := by
    funext omega
    rw [gridSupAbs, Finset.sup'_apply]
  rw [hfun]
  exact Finset.measurable_sup' hs fun y _ => Measurable.abs (hm y)

/-- **`e.maxy.bound` for an arbitrary nonempty finite grid.**

The amplitude is the proved `l.maximums.Gamma.s` amplitude of this repository,
`(3 max 1 (log N))^{1/sigma} A`, which enlarges the source's `(3 log
N)^{1/sigma} A` only where the source proof does not apply (`N = 1`). -/
theorem gridSupAbs_isBigOWith [MeasurableSpace Omega] {mu : Measure Omega}
    [IsFiniteMeasure mu] (sfin : Finset ι)
    (hs : sfin.Nonempty) {X : ι → Omega → ℝ} {A sigma : ℝ}
    (hsigma : 0 < sigma) (hA : 0 ≤ A)
    (hX : ∀ y ∈ sfin, IsBigO mu (gammaSigma sigma) (X y) A) :
    IsBigOWith mu (gammaSigma sigma) (gridSupAbs sfin hs X)
      ((3 * max 1 (Real.log (sfin.card : ℝ))) ^ sigma⁻¹ * A) :=
  Provider.Orlicz.isBigOWith_gammaSigma_finset_sup'_of_nonempty
    (X := fun y omega => |X y omega|) sfin hs hsigma hA fun y hy => hX y hy

/-- **The `e.maxy.bound` lift at the triadic grid**.

A common `Gamma_sigma` bound at amplitude `A` for every one of the `3^{d(k+1)}`
translates `z + cu_{m-1-k}` of `cu_m` lifts to the grid maximum at amplitude
`gridNetConst d sigma * (k+1)^{1/sigma} * A`.  The `(k+1)^{1/sigma}` factor is
exactly the source's polynomial `(m - n + 1)^{1/sigma}` at `m - n = k + 1`, and
`gridNetConst` is the constant the source absorbs into `C`. -/
theorem gridSupAbs_descendants_isBigOWith [MeasurableSpace Omega]
    {mu : Measure Omega} [IsFiniteMeasure mu] {d : ℕ} (hd : 1 ≤ d)
    (m : ℤ) (k : ℕ) {X : TriadicCube d → Omega → ℝ} {A sigma : ℝ}
    (hsigma : 0 < sigma) (hA : 0 ≤ A)
    (hX : ∀ R ∈ descendantsAtScale (originCube d m) (m - 1 - (k : ℤ)),
      IsBigO mu (gammaSigma sigma) (X R) A) :
    IsBigOWith mu (gammaSigma sigma)
      (gridSupAbs (descendantsAtScale (originCube d m) (m - 1 - (k : ℤ)))
        (descendantsAtScale_originCube_nonempty d m k) X)
      (gridNetConst d sigma * (((k : ℝ) + 1) ^ sigma⁻¹) * A) := by
  have hcard := card_descendantsAtScale_originCube d m k
  have hcast : ((descendantsAtScale (originCube d m) (m - 1 - (k : ℤ))).card : ℝ)
      = (3 : ℝ) ^ (d * (k + 1)) := by
    rw [hcard]
    push_cast
    ring
  have hdR : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hlogpos : 1 ≤ Real.log ((3 : ℝ) ^ (d * (k + 1))) := by
    rw [Real.log_pow]
    have hfac : (1 : ℝ) ≤ ((d * (k + 1) : ℕ) : ℝ) := by
      have : 1 ≤ d * (k + 1) := Nat.one_le_iff_ne_zero.2 (by positivity)
      exact_mod_cast this
    nlinarith [one_lt_log_three]
  have hmax : max 1
      (Real.log ((descendantsAtScale (originCube d m) (m - 1 - (k : ℤ))).card : ℝ))
      = Real.log ((3 : ℝ) ^ (d * (k + 1))) := by
    rw [hcast]
    exact max_eq_right hlogpos
  have hbase := gridSupAbs_isBigOWith (mu := mu)
    (descendantsAtScale (originCube d m) (m - 1 - (k : ℤ)))
    (descendantsAtScale_originCube_nonempty d m k) hsigma hA hX
  rw [hmax] at hbase
  rwa [gridNetConst_rpow_eq sigma d k] at hbase

/-! ## 6. `gridSupAbs` is CoarseGraining's grid maximum -/

private theorem finsetSupReal_eq_sup' {alpha : Type*} (sfin : Finset alpha)
    (hs : sfin.Nonempty) (f : alpha → ℝ) :
    HCPolySupport.Book.Ch02.finsetSupReal sfin f = sfin.sup' hs f := by
  have hbdd : BddAbove (f '' (↑sfin : Set alpha)) :=
    ((Set.toFinite _).image f).bddAbove
  refine le_antisymm ?_ ?_
  · refine csSup_le (hs.to_set.image f) ?_
    rintro x ⟨y, hy, rfl⟩
    exact Finset.le_sup' f (by exact_mod_cast hy)
  · refine Finset.sup'_le hs f fun y hy => ?_
    exact le_csSup hbdd ⟨y, hy, rfl⟩

private theorem coarseBMatrixNorm_nonneg' {d : ℕ} (Q : TriadicCube d)
    (a : HCPolySupport.Book.Ch02.TriadicCoeffFamily d) :
    0 ≤ HCPolySupport.Book.Ch02.coarseBMatrixNorm Q a := by
  rw [HCPolySupport.Book.Ch02.coarseBMatrixNorm,
    HCPolySupport.Book.Ch02.matrixNorm]
  exact norm_nonneg _

/-- **The on-grid carrier identification.**  CoarseGraining's per-scale grid
maximum, the quantity `Ch02.LambdaSqFinite` is defined from, is exactly this
module's `gridSupAbs` applied to the one-cube coarse norms `|b(R; a)|`. -/
theorem maxDescendantBMatrixNormAtScale_eq_gridSupAbs {d : ℕ} (m : ℤ) (k : ℕ)
    (a : HCPolySupport.Book.Ch02.TriadicCoeffFamily d) :
    HCPolySupport.Book.Ch02.maxDescendantBMatrixNormAtScale (originCube d m)
        (m - 1 - (k : ℤ)) a
      = gridSupAbs (Omega := HCPolySupport.Book.Ch02.TriadicCoeffFamily d)
          (descendantsAtScale (originCube d m) (m - 1 - (k : ℤ)))
          (descendantsAtScale_originCube_nonempty d m k)
          (fun R b => HCPolySupport.Book.Ch02.coarseBMatrixNorm R b) a := by
  have hfun : (fun R : TriadicCube d =>
      |HCPolySupport.Book.Ch02.coarseBMatrixNorm R a|)
      = fun R : TriadicCube d =>
          HCPolySupport.Book.Ch02.coarseBMatrixNorm R a := by
    funext R
    exact abs_of_nonneg (coarseBMatrixNorm_nonneg' R a)
  rw [HCPolySupport.Book.Ch02.maxDescendantBMatrixNormAtScale, gridSupAbs, hfun,
    finsetSupReal_eq_sup' _ (descendantsAtScale_originCube_nonempty d m k)]

end

end Algsuperdiff.Section3.Provider.CoarseEllipticity
