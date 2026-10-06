/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Transport.DiscreteConvolution
public import LeanPool.HighContrastHomogenization.Provider.Persistence.TransferGauge

/-!
# High-contrast homogenization: Provider.Entry.AdapterSeries

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The geometric series of the adapted-to-Euclidean comparison

The proof of the comparison between adapted and Euclidean cubes splits the
boundary layers of a cross-grid filling at the comparison generation `k`.  The
layers at or above it are paid by the annealed mean order, whose total relative
volume is at most one; the layers below it are paid by the Euclidean cell bound
`E[𝐀(z+□_r)] ≤ (1 + 9K_{Ψ_S}^23^{-r})^g𝐄` against the cross-grid row weight
`C_d3^{r-n}`, and their total is the printed geometric-series calculation

`Σ_{r<k}3^{r-n}(1 + 9K^23^{-r})^g ≤ 20 Γ_{g,S}(k)3^{-(n-k)}`.

Two elementary facts carry it.  The power `x ↦ x^g` is subadditive for `g ≤ 1`,
which separates the constant layer from the source layer; and the geometric
series `ζ_g = (1-3^{-(1-g)})^{-1}` is at most `2(1-g)^{-1}`, because `t ↦ 3^{-t}`
is convex and therefore below its chord on `[0,1]`.  The second is what turns the
raw series into the printed gauge `Γ_{g,S}(k) = (1-g)^{-1}(1+K^23^{-k})^g`, whose
prefactor is exactly one power of `(1-g)^{-1}`: a comparison that spent two
powers of `(1-g)^{-1}` would not be the printed one.

The bound is uniform in the lower cutoff of the sum, which is what lets it
survive the limit the filling exhaustion takes.

There are no definitions in this file.
-/

namespace HCPolySupport
namespace HighContrast
namespace Entry

noncomputable section

/-- **The geometric series is at most `2(1-g)^{-1}`.**  The map `t ↦ 3^{-t}` is
convex, so on `[0,1]` it lies below its chord `1 - 2t/3`; hence
`1 - 3^{-(1-g)} ≥ 2(1-g)/3`, which is the one power of `(1-g)^{-1}` the printed
gauge carries. -/
theorem zetaG_le_two_div {g : ℝ} (hg0 : 0 ≤ g) (hg1 : g < 1) :
    zetaG g ≤ 2 / (1 - g) := by
  set t : ℝ := 1 - g with ht
  have ht0 : 0 < t := by rw [ht]; linarith only [hg1]
  have ht1 : t ≤ 1 := by rw [ht]; linarith only [hg0]
  have hexp3 : Real.exp (-Real.log 3) = 1 / 3 := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 3)]
    norm_num
  have hlhs : Real.exp ((1 - t) * 0 + t * (-Real.log 3)) = (3 : ℝ) ^ (-t) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3) (-t)]
    congr 1
    ring
  have hconv := convexOn_exp.2 (Set.mem_univ (0 : ℝ))
    (Set.mem_univ (-Real.log 3)) (by linarith only [ht1] : (0 : ℝ) ≤ 1 - t) ht0.le
    (by ring)
  simp only [smul_eq_mul, Real.exp_zero, mul_one] at hconv
  rw [hlhs, hexp3] at hconv
  have hchord : (3 : ℝ) ^ (-t) ≤ 1 - 2 * t / 3 := by linarith only [hconv]
  have hlow : 2 * t / 3 ≤ 1 - (3 : ℝ) ^ (-t) := by linarith only [hchord]
  have hpos : (0 : ℝ) < 2 * t / 3 := by positivity
  have hinv : (1 - (3 : ℝ) ^ (-t))⁻¹ ≤ (2 * t / 3)⁻¹ := by
    exact inv_anti₀ hpos hlow
  have hfin : (2 * t / 3)⁻¹ ≤ 2 / t := by
    rw [inv_eq_one_div, div_le_div_iff₀ (by positivity) ht0]
    ring_nf
    nlinarith only [ht0]
  rw [zetaG, ← ht]
  exact hinv.trans hfin

/-- **The below-split series of the comparison.**  The layers below the
comparison generation, weighted by the cross-grid row `3^{r-n}` and bounded by
the Euclidean cell bound, total at most twenty times the printed gauge times the
printed rate — uniformly in the lower cutoff of the sum. -/
theorem sum_belowSplit_le {g K : ℝ} (hg0 : 0 ≤ g) (hg1 : g < 1) (k n J : ℤ) :
    ∑ r ∈ Finset.Ico J k, (3 : ℝ) ^ (r - n) * (1 + 9 * K ^ 2 * (3 : ℝ) ^ (-r)) ^ g ≤
      20 * transferGauge g K k * (3 : ℝ) ^ (k - n) := by
  have h3pos : (0 : ℝ) < 3 := by norm_num
  have hrpow : ∀ e : ℤ, (3 : ℝ) ^ e = (3 : ℝ) ^ ((e : ℝ)) :=
    fun e => (Real.rpow_intCast 3 e).symm
  have hadd : ∀ a b : ℝ, (3 : ℝ) ^ a * (3 : ℝ) ^ b = (3 : ℝ) ^ (a + b) :=
    fun a b => (Real.rpow_add h3pos a b).symm
  -- termwise subadditivity of the power
  have hterm : ∀ r : ℤ,
      (3 : ℝ) ^ (r - n) * (1 + 9 * K ^ 2 * (3 : ℝ) ^ (-r)) ^ g ≤
        (3 : ℝ) ^ (r - n) + (3 : ℝ) ^ (r - n) * (9 * K ^ 2 * (3 : ℝ) ^ (-r)) ^ g := by
    intro r
    have hx : (0 : ℝ) ≤ 9 * K ^ 2 * (3 : ℝ) ^ (-r) := by positivity
    have hsub := Real.rpow_add_le_add_rpow zero_le_one hx hg0 hg1.le
    rw [Real.one_rpow] at hsub
    have h0 : (0 : ℝ) ≤ (3 : ℝ) ^ (r - n) := by positivity
    have := mul_le_mul_of_nonneg_left hsub h0
    linarith only [this]
  refine le_trans (Finset.sum_le_sum fun r _ => hterm r) ?_
  rw [Finset.sum_add_distrib]
  -- the plain geometric row
  have hT1 : ∑ r ∈ Finset.Ico J k, (3 : ℝ) ^ (r - n) ≤ (3 : ℝ) ^ (k - n) * (3 / 2) := by
    have hrw : ∀ r ∈ Finset.Ico J k,
        (3 : ℝ) ^ (r - n) = (3 : ℝ) ^ (k - n) * (3 : ℝ) ^ (-(1 : ℝ) * ((k : ℝ) - (r : ℝ))) := by
      intro r _
      rw [hrpow (r - n), hrpow (k - n), hadd]
      congr 1
      push_cast
      ring
    rw [Finset.sum_congr rfl hrw, ← Finset.mul_sum]
    have hser := Transport.sum_geom_below_le (c := (1 : ℝ)) one_pos k (Finset.Ico J k)
      (fun r hr => le_of_lt (Finset.mem_Ico.mp hr).2)
    have hval : (1 : ℝ) / (1 - (3 : ℝ) ^ (-(1 : ℝ))) = 3 / 2 := by
      rw [show (-(1 : ℝ)) = ((-1 : ℤ) : ℝ) by norm_num, ← hrpow]
      norm_num
    rw [hval] at hser
    exact mul_le_mul_of_nonneg_left hser (by positivity)
  -- the source row
  have hT2 : ∑ r ∈ Finset.Ico J k, (3 : ℝ) ^ (r - n) * (9 * K ^ 2 * (3 : ℝ) ^ (-r)) ^ g ≤
      (9 * K ^ 2 * (3 : ℝ) ^ (-k)) ^ g * (3 : ℝ) ^ (k - n) * zetaG g := by
    have hA : (0 : ℝ) ≤ 9 * K ^ 2 := by positivity
    have hrw : ∀ r ∈ Finset.Ico J k,
        (3 : ℝ) ^ (r - n) * (9 * K ^ 2 * (3 : ℝ) ^ (-r)) ^ g =
          ((9 * K ^ 2 * (3 : ℝ) ^ (-k)) ^ g * (3 : ℝ) ^ (k - n)) *
            (3 : ℝ) ^ (-(1 - g) * ((k : ℝ) - (r : ℝ))) := by
      intro r _
      rw [Real.mul_rpow hA (by positivity), Real.mul_rpow hA (by positivity),
        hrpow (-r), hrpow (-k), ← Real.rpow_mul h3pos.le, ← Real.rpow_mul h3pos.le,
        hrpow (r - n), hrpow (k - n)]
      rw [show (3 : ℝ) ^ (((r : ℤ) - n : ℤ) : ℝ) *
            ((9 * K ^ 2) ^ g * (3 : ℝ) ^ (((-r : ℤ) : ℝ) * g))
          = (9 * K ^ 2) ^ g * ((3 : ℝ) ^ (((r - n : ℤ) : ℝ)) *
            (3 : ℝ) ^ (((-r : ℤ) : ℝ) * g)) by ring,
        show (9 * K ^ 2) ^ g * (3 : ℝ) ^ (((-k : ℤ) : ℝ) * g) *
            (3 : ℝ) ^ (((k - n : ℤ) : ℝ)) * (3 : ℝ) ^ (-(1 - g) * ((k : ℝ) - (r : ℝ)))
          = (9 * K ^ 2) ^ g * ((3 : ℝ) ^ (((-k : ℤ) : ℝ) * g) *
            (3 : ℝ) ^ (((k - n : ℤ) : ℝ)) *
              (3 : ℝ) ^ (-(1 - g) * ((k : ℝ) - (r : ℝ)))) by ring,
        hadd, hadd, hadd]
      congr 2
      push_cast
      ring
    rw [Finset.sum_congr rfl hrw, ← Finset.mul_sum]
    have hser := Transport.sum_geom_below_le (c := 1 - g) (by linarith only [hg1]) k
      (Finset.Ico J k) (fun r hr => le_of_lt (Finset.mem_Ico.mp hr).2)
    have hz : (1 : ℝ) / (1 - (3 : ℝ) ^ (-(1 - g))) = zetaG g := by
      rw [zetaG, one_div]
    rw [hz] at hser
    refine mul_le_mul_of_nonneg_left hser ?_
    positivity
  -- the two closed forms against the gauge
  have hgauge1 : (1 : ℝ) ≤ transferGauge g K k := by
    rw [transferGauge]
    have hbase : (1 : ℝ) ≤ 1 + K ^ 2 * (3 : ℝ) ^ (-k) := by
      have : (0 : ℝ) ≤ K ^ 2 * (3 : ℝ) ^ (-k) := by positivity
      linarith only [this]
    have hpow : (1 : ℝ) ≤ (1 + K ^ 2 * (3 : ℝ) ^ (-k)) ^ g :=
      Real.one_le_rpow hbase hg0
    have hinv : (1 : ℝ) ≤ (1 - g)⁻¹ := by
      rw [le_inv_comm₀ one_pos (by linarith only [hg1])]
      linarith only [hg0]
    nlinarith only [hpow, hinv]
  have hnine : (9 * K ^ 2 * (3 : ℝ) ^ (-k)) ^ g ≤ 9 * (1 + K ^ 2 * (3 : ℝ) ^ (-k)) ^ g := by
    have hsp : (9 : ℝ) * K ^ 2 * (3 : ℝ) ^ (-k) = 9 * (K ^ 2 * (3 : ℝ) ^ (-k)) := by ring
    rw [hsp, Real.mul_rpow (by norm_num) (by positivity)]
    have h9 : (9 : ℝ) ^ g ≤ 9 := by
      have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 9) hg1.le
      rwa [Real.rpow_one] at this
    have hb : (K ^ 2 * (3 : ℝ) ^ (-k)) ^ g ≤ (1 + K ^ 2 * (3 : ℝ) ^ (-k)) ^ g :=
      Real.rpow_le_rpow (by positivity) (by linarith only []) hg0
    have h9pos : (0 : ℝ) ≤ (9 : ℝ) ^ g := Real.rpow_nonneg (by norm_num) g
    have hbpos : (0 : ℝ) ≤ (K ^ 2 * (3 : ℝ) ^ (-k)) ^ g := Real.rpow_nonneg (by positivity) g
    nlinarith only [h9, hb, h9pos, hbpos]
  have hzeta := zetaG_le_two_div hg0 hg1
  have hpow0 : (0 : ℝ) < (3 : ℝ) ^ (k - n) := by positivity
  have hbpow0 : (0 : ℝ) ≤ (1 + K ^ 2 * (3 : ℝ) ^ (-k)) ^ g :=
    Real.rpow_nonneg (by positivity) g
  have hzeta0 : (0 : ℝ) < zetaG g := Transport.zero_lt_zetaG hg1
  have hT2' : (9 * K ^ 2 * (3 : ℝ) ^ (-k)) ^ g * (3 : ℝ) ^ (k - n) * zetaG g ≤
      18 * transferGauge g K k * (3 : ℝ) ^ (k - n) := by
    have hstep : (9 * K ^ 2 * (3 : ℝ) ^ (-k)) ^ g * zetaG g ≤
        9 * (1 + K ^ 2 * (3 : ℝ) ^ (-k)) ^ g * (2 / (1 - g)) := by
      have h1 : (0 : ℝ) ≤ (9 * K ^ 2 * (3 : ℝ) ^ (-k)) ^ g := Real.rpow_nonneg (by positivity) g
      nlinarith only [hnine, hzeta, h1, hzeta0, hbpow0]
    have hval : 9 * (1 + K ^ 2 * (3 : ℝ) ^ (-k)) ^ g * (2 / (1 - g))
        = 18 * transferGauge g K k := by
      rw [transferGauge, div_eq_inv_mul]
      ring
    rw [hval] at hstep
    nlinarith only [hstep, hpow0]
  have hT1' : (3 : ℝ) ^ (k - n) * (3 / 2) ≤ 2 * transferGauge g K k * (3 : ℝ) ^ (k - n) := by
    nlinarith only [hgauge1, hpow0]
  linarith only [hT1, hT2, hT1', hT2']

end

end Entry
end HighContrast
end HCPolySupport
