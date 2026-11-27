/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Domains.Interval.SplineInverse
public import LeanPool.FunctionSpaces.Domains.Interval.PiecewisePeriodic

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Splines on the circle and their inverse inequality

On the circle `𝕋 = ℝ/ℤ`, identified with `[0, 1)` through the periodic extension
`fTilde(x) = f(x - ⌊x⌋)`, a **periodic spline of order `r` and level `k`** is a spline on `[0, 1]`
(`Interval.SplineJoins`) whose last piece also joins the first one across the point `0 = 1` of
the circle (`Interval.PerJoin`): the first piece moved to `[1, 1 + 2^(-k))` and the last piece
differ by a multiple of `(x - 1)^(r-1)`. The periodic splines form subspaces `S_k(𝕋)` of
`L_p(𝕋) = L_p[0, 1]` increasing in `k` (`Interval.perSplineSpace`), and the scheme
`Interval.perSplineScheme` has them as approximants of complexity `2^k`.

The periodic extension of a periodic spline is a spline on `[0, ∞)`, with spline joins at every
knot (`Interval.perPieces_join`). So the local estimate for splines of
`FunctionSpaces.Domains.Interval.SplineInverse` applies to it on `[0, 1]`, and its masses on `r + 1`
consecutive intervals are controlled by one period (`Interval.sum_sum_localMass_perExt_le`). This
gives the **inverse inequality** `ω_r^per(a, 2^(-k))_p ≤ C_B 2^(-(k-j)(r-1+1/p)) ‖a‖_p` for
`a ∈ S_j(𝕋)` (`Interval.exists_inverse_perSplineScheme`).
-/

@[expose] public section

open MeasureTheory Set Polynomial
open Rd (higherDiff)
open scoped ENNReal
open ENNReal (dyadicWeight)

namespace Interval

/-- The pieces `Q` of level `k` have a **spline join of order `r` across the point `0 = 1` of the
circle**: the first piece moved to `[1, 1 + 2^(-k))` and the last piece differ by a multiple of
`(x - 1)^(r-1)`. -/
def PerJoin (r k : ℕ) (Q : ℕ → ℂ[X]) : Prop :=
  ∃ c : ℂ, (Q 0).comp (X - C 1) - Q (2 ^ k - 1) = C c * (X - C 1) ^ (r - 1)

/-- The zero pieces join across `0 = 1`. -/
theorem perJoin_zero (r k : ℕ) : PerJoin r k 0 := ⟨0, by simp⟩

/-- Joins across `0 = 1` are preserved by sums. -/
theorem PerJoin.add {r k : ℕ} {Q Q' : ℕ → ℂ[X]} (h : PerJoin r k Q) (h' : PerJoin r k Q') :
    PerJoin r k (Q + Q') := by
  obtain ⟨c, hc⟩ := h
  obtain ⟨c', hc'⟩ := h'
  refine ⟨c + c', ?_⟩
  simp only [Pi.add_apply]
  rw [add_comp, show (Q 0).comp (X - C 1) + (Q' 0).comp (X - C 1) -
      (Q (2 ^ k - 1) + Q' (2 ^ k - 1)) = ((Q 0).comp (X - C 1) - Q (2 ^ k - 1)) +
        ((Q' 0).comp (X - C 1) - Q' (2 ^ k - 1)) by ring, hc, hc', C_add]
  ring

/-- Joins across `0 = 1` are preserved by constant multiples. -/
theorem PerJoin.const_mul {r k : ℕ} {Q : ℕ → ℂ[X]} (h : PerJoin r k Q) (a : ℂ) :
    PerJoin r k (fun n => C a * Q n) := by
  obtain ⟨c, hc⟩ := h
  refine ⟨a * c, ?_⟩
  rw [mul_comp, C_comp, ← mul_sub, hc, C_mul]
  ring

/-- Joins across `0 = 1` of level `k` are joins of level `k + 1`: the first and the last piece
stay the same. -/
theorem PerJoin.refine {r k : ℕ} {Q : ℕ → ℂ[X]} (h : PerJoin r k Q) :
    PerJoin r (k + 1) (fun m => Q (m / 2)) := by
  obtain ⟨c, hc⟩ := h
  refine ⟨c, ?_⟩
  have h1 : (2 ^ (k + 1) - 1) / 2 = 2 ^ k - 1 := by
    have := Nat.one_le_two_pow (n := k)
    rw [pow_succ]
    omega
  simp only [Nat.zero_div, h1]
  exact hc

/-! ### The periodic extension of a periodic spline -/

/-- **The periodic extension of a periodic spline is a spline on `[0, ∞)`**: its pieces have
spline joins at every knot `m 2^(-k)`, `m ≥ 1`, from the joins inside `[0, 1)` at the knots of a
period and from the join across `0 = 1` at the integers. -/
theorem perPieces_join {r k : ℕ} {Q : ℕ → ℂ[X]} (hJ : SplineJoins r k Q) (hP : PerJoin r k Q)
    {m : ℕ} (hm : 0 < m) :
    ∃ c : ℂ, perPieces k Q m - perPieces k Q (m - 1) =
      C c * (X - C ((((m : ℝ) / 2 ^ k : ℝ)) : ℂ)) ^ (r - 1) := by
  obtain ⟨d, e, he, rfl⟩ : ∃ d e : ℕ, e < 2 ^ k ∧ m = e + 2 ^ k * d :=
    ⟨m / 2 ^ k, m % 2 ^ k, Nat.mod_lt _ (by positivity), (Nat.mod_add_div m (2 ^ k)).symm⟩
  have hpos : (0 : ℝ) < 2 ^ k := by positivity
  rcases Nat.eq_zero_or_pos e with rfl | he0
  · -- an integer knot `d ≥ 1`: the join across `0 = 1`, shifted by `d - 1`
    have hd : 1 ≤ d := Nat.pos_of_ne_zero fun h => by simp [h] at hm
    obtain ⟨c, hc⟩ := hP
    refine ⟨c, ?_⟩
    have h1 : 0 + 2 ^ k * d - 1 = (2 ^ k - 1) + 2 ^ k * (d - 1) := by
      obtain ⟨d', rfl⟩ := Nat.exists_eq_add_of_le' hd
      have := Nat.one_le_two_pow (n := k)
      rw [Nat.add_sub_cancel, mul_add, mul_one]
      generalize 2 ^ k * d' = A
      omega
    have hshift : (X - C (((d : ℝ) : ℝ) : ℂ) : ℂ[X]) =
        (X - C 1 : ℂ[X]).comp (X - C ((((d - 1 : ℕ) : ℝ) : ℝ) : ℂ)) := by
      refine Polynomial.funext fun z => ?_
      simp only [eval_comp, eval_sub, eval_X, eval_C]
      push_cast [Nat.cast_sub hd]
      ring
    rw [h1, perPieces_eq k Q (by positivity) d,
      perPieces_eq k Q (Nat.sub_lt (by positivity) one_pos) (d - 1), hshift, ← comp_assoc,
      ← sub_comp, hc, mul_comp, C_comp]
    congr 1
    refine Polynomial.funext fun z => ?_
    simp only [eval_comp, eval_pow, eval_sub, eval_X, eval_C]
    congr 1
    push_cast [Nat.cast_sub hd]
    field_simp
    ring
  · -- a knot inside a period: the join inside `[0, 1)`, shifted by `d`
    obtain ⟨c, hc⟩ := hJ e he0 he
    refine ⟨c, ?_⟩
    have h1 : e + 2 ^ k * d - 1 = (e - 1) + 2 ^ k * d := by
      generalize 2 ^ k * d = A
      omega
    rw [h1, perPieces_eq k Q he d, perPieces_eq k Q (by omega) d, ← sub_comp, hc, mul_comp,
      C_comp]
    congr 1
    refine Polynomial.funext fun z => ?_
    simp only [eval_comp, eval_pow, eval_sub, eval_X, eval_C]
    congr 1
    push_cast
    field_simp
    ring

/-- The periodic extension of a periodic spline is a spline below every `N`. -/
theorem splineJoinsBelow_perPieces {r k : ℕ} {Q : ℕ → ℂ[X]} (hJ : SplineJoins r k Q)
    (hP : PerJoin r k Q) (N : ℕ) : SplineJoinsBelow r k N (perPieces k Q) :=
  fun _ hm _ => perPieces_join hJ hP hm

/-! ### The space and the scheme -/

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

variable (p) in
/-- The space `S_k(𝕋)` of **periodic splines of order `r`** on the dyadic grid of level `k` in
`L_p(𝕋) = L_p[0, 1]`: the classes of splines on `[0, 1]` whose pieces also join across
`0 = 1`. -/
noncomputable def perSplineSpace (r k : ℕ) : Submodule ℝ (Lp ℂ p unitVol) where
  carrier := {g | ∃ Q : ℕ → ℂ[X], (∀ n, Q n ∈ degreeLT ℂ r) ∧ SplineJoins r k Q ∧
    PerJoin r k Q ∧ (g : ℝ → ℂ) =ᵐ[unitVol] ppFun k Q}
  add_mem' := by
    rintro g g' ⟨Q, hQ, hj, hP, hg⟩ ⟨Q', hQ', hj', hP', hg'⟩
    refine ⟨Q + Q', fun n => Submodule.add_mem _ (hQ n) (hQ' n), hj.add hj', hP.add hP', ?_⟩
    filter_upwards [Lp.coeFn_add g g', hg, hg'] with x h1 h2 h3
    rw [h1, Pi.add_apply, h2, h3, ppFun_add, Pi.add_apply]
  zero_mem' := ⟨0, fun n => Submodule.zero_mem _, splineJoins_zero r k, perJoin_zero r k, by
    filter_upwards [Lp.coeFn_zero ℂ p unitVol] with x hx
    rw [hx, ppFun_zero]⟩
  smul_mem' := by
    rintro c g ⟨Q, hQ, hj, hP, hg⟩
    refine ⟨fun n => C (c : ℂ) * Q n, fun n => ?_, hj.const_mul _, hP.const_mul _, ?_⟩
    · change C (c : ℂ) * Q n ∈ degreeLT ℂ r
      rw [← smul_eq_C_mul]; exact Submodule.smul_mem _ _ (hQ n)
    · filter_upwards [Lp.coeFn_smul c g, hg] with x h1 h2
      rw [h1, Pi.smul_apply, h2, ppFun_const_mul, Complex.real_smul]

omit [Fact (1 ≤ p)] in
/-- Periodic splines are splines. -/
theorem perSplineSpace_le_splineSpace (r k : ℕ) : perSplineSpace p r k ≤ splineSpace p r k :=
  fun _ ⟨Q, hQ, hj, _, hg⟩ => ⟨Q, hQ, hj, hg⟩

omit [Fact (1 ≤ p)] in
/-- The periodic spline spaces increase with the level. -/
theorem perSplineSpace_mono (r : ℕ) : Monotone (perSplineSpace p r) := by
  refine monotone_nat_of_le_succ fun k g hg => ?_
  obtain ⟨Q, hQ, hj, hP, hgQ⟩ := hg
  exact ⟨fun n => Q (n / 2), fun n => hQ _, hj.refine, hP.refine,
    hgQ.trans (ppFun_refine k Q).symm⟩

variable (p) in
/-- The **scheme of periodic dyadic splines** of order `r` in `L_p(𝕋) = L_p[0, 1]`: `{0}` at
complexity `0` and `S_{⌊log₂ n⌋}(𝕋)` at complexity `n ≥ 1`. -/
noncomputable def perSplineScheme (r : ℕ) : ApproximationScheme (Lp ℂ p unitVol) :=
  ApproximationScheme.ofMonotoneSubmodules (perSplineSpace p r) (perSplineSpace_mono r)

/-- The approximants of complexity `0` are `{0}`. -/
theorem mem_perSplineScheme_zero {r : ℕ} {g : Lp ℂ p unitVol} :
    g ∈ perSplineScheme p r 0 ↔ g = 0 :=
  ApproximationScheme.mem_ofMonotoneSubmodules_zero

/-- The approximants of complexity `n ≥ 1` are the periodic splines of level `⌊log₂ n⌋`. -/
theorem mem_perSplineScheme {r n : ℕ} (hn : n ≠ 0) {g : Lp ℂ p unitVol} :
    g ∈ perSplineScheme p r n ↔ g ∈ perSplineSpace p r (Nat.log 2 n) :=
  ApproximationScheme.mem_ofMonotoneSubmodules hn

/-- The approximants of complexity `2^k` are the periodic splines of level `k`. -/
theorem mem_perSplineScheme_two_pow {r k : ℕ} {g : Lp ℂ p unitVol} :
    g ∈ perSplineScheme p r (2 ^ k) ↔ g ∈ perSplineSpace p r k :=
  ApproximationScheme.mem_ofMonotoneSubmodules_two_pow

/-- The periodic spline scheme is linear. -/
theorem perSplineScheme_isLinear (r : ℕ) : (perSplineScheme p r).IsLinear :=
  ApproximationScheme.isLinear_ofMonotoneSubmodules _ _

/-! ### The inverse inequality -/

/-- **The inverse inequality for periodic splines**, of order `θ = r - 1 + 1/p`: there is
`C_B < ∞` with `ω_r^per(a, 2^(-k))_p ≤ C_B 2^(-(k-j)θ) ‖a‖_p` for every periodic spline `a` of
order `r` and level `j` (and `k - j` truncated at `0`). The periodic extension is a spline below
`N = 2^j + r + 1`, and `[0, N 2^(-j))` contains `[0, 1 + rh]` for `h ≤ 2^(-j)`. -/
theorem exists_inverse_perSplineScheme {r : ℕ} (hp : p ≠ ∞) :
    ∃ CB : ℝ≥0∞, CB ≠ ∞ ∧ ∀ j k : ℕ, ∀ a ∈ perSplineScheme p r (2 ^ j),
      lpPerModulus p r a k ≤
        CB * dyadicWeight (-(((r - 1 : ℕ) : ℝ) + 1 / p.toReal)) (k - j) * ‖a‖ₑ := by
  obtain ⟨K, hK, hKb⟩ := enorm_polyFun_le (p := p) r hp
  refine ⟨2 ^ r * (1 + splineInverseConst r K p),
    ENNReal.mul_ne_top (by simp) (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top,
      splineInverseConst_ne_top r hK⟩), fun j k a ha => ?_⟩
  obtain ⟨Q, hQ, hJ, hP, hae⟩ := mem_perSplineScheme_two_pow.1 ha
  rcases lt_or_ge k j with hkj | hjk
  · rw [Nat.sub_eq_zero_of_le hkj.le, ENNReal.dyadicWeight_zero_right, mul_one]
    exact (lpPerModulus_le hp r a k).trans (by gcongr; exact two_pow_le_two_pow_mul_one_add r _)
  · have hnorm : ‖a‖ₑ = eLpNorm (ppFun j Q) p unitVol := by
      rw [Lp.eNorm_def]
      exact eLpNorm_congr_ae hae
    rw [lpPerModulus, perModulus_congr_ae hae, hnorm]
    refine iSup₂_le fun h hh => ?_
    have hhj : h ≤ 1 / 2 ^ j := hh.2.trans (one_div_le_one_div_of_le (by positivity)
      (pow_le_pow_right₀ (by norm_num) hjk))
    have hSN : ∀ᵐ x ∂volume.restrict (Icc (0 : ℝ) 1),
        x + r * h < ((2 ^ j + r + 1 : ℕ) : ℝ) / 2 ^ j := by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
      have hrh : (r : ℝ) * h ≤ r / 2 ^ j := by
        rw [div_eq_mul_one_div]
        exact mul_le_mul_of_nonneg_left hhj (Nat.cast_nonneg r)
      have hN : ((2 ^ j + r + 1 : ℕ) : ℝ) / 2 ^ j = 1 + r / 2 ^ j + 1 / 2 ^ j := by
        push_cast
        field_simp
      have h0 : (0 : ℝ) < 1 / 2 ^ j := by positivity
      rw [hN]
      linarith [hx.2]
    calc eLpNorm (higherDiff r h (perExt (ppFun j Q))) p (volume.restrict (Icc 0 1))
        ≤ splineStripConst r j K h p * (ENNReal.ofReal (r * h) * (r + 1)) ^
            (1 / p.toReal) * eLpNorm (ppFun j Q) p unitVol :=
          eLpNorm_higherDiff_spline_le (perPieces_mem hQ j) (splineJoinsBelow_perPieces hJ hP _)
            (fun _ _ _ hx => perExt_ppFun_eq j Q hx) (isPiecewisePoly_perExt_ppFun hQ j)
            (measurable_perExt (measurable_ppFun j Q)) hKb hp hh.1 hhj measurableSet_Icc
            subset_rfl hSN (sum_sum_localMass_perExt_le (measurable_ppFun j Q) hp j r)
      _ ≤ splineInverseConst r K p * dyadicWeight (-(((r - 1 : ℕ) : ℝ) + 1 / p.toReal)) (k - j) *
            eLpNorm (ppFun j Q) p unitVol := splineStripConst_mul_le hjk K hh.2 _
      _ ≤ 2 ^ r * (1 + splineInverseConst r K p) *
            dyadicWeight (-(((r - 1 : ℕ) : ℝ) + 1 / p.toReal)) (k - j) *
            eLpNorm (ppFun j Q) p unitVol := by
          gcongr
          exact le_two_pow_mul_one_add r _

end Interval
