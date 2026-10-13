/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Besov.JBoundByBesov
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Homogenization.CombineBadEvent

/-!
# CombineGoodEvent

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The good-event branch of Step 1 of the corrected combine proposition

Step 1 of Proposition `p.combine.under.S` splits the response of the ordinary
central child along the event `e.goodevent.combine`

`G = { sigmabar_L / 2 <= lambda_{1/4,1}(cu_m; a_L) <= Lambda_{1/4,1}(cu_m; a_L)
        <= 2 sigmabar_L }`

and estimates the `G`-part by the weak-norm chain, the `G^c`-part being the
separate bad-event branch.  This module carries the `G`-part, in the pointwise
form that precedes every expectation: the printed chain

* `l.J.bound.by.Besov`, consumed as the committed composite
  `Besov.exists_restrictionResponseJ_centralChild_le_jBoundByBesovDisplay`;
* the two prefactor facts, `(Lambda/lambda)^{1 + s/(1-2s)} 1_G <= C` and
  `Lambda 1_G <= 2 sigmabar_L`;
* `l.Besov.norms` at `r = 1`, consumed as the committed four-term display
  `Besov.centredMultiscaleAverageSum_le_fourTerm`;
* the square expansion of the four terms, with Cauchy--Schwarz in the scale sum
  converting the printed discount `3^{-(1-s)(m-n)}` of the defect term into the
  printed weight `3^{-(m-n)}` of `e.initial.JL.bound`;
* the reabsorption of the energy term through `e.Jenergyv.nosymm`, under the
  printed constraint `C 3^{-(1-s)(m-L)} <= 1/4`;
* the merge of the two constant tails (the centring tail of the `l.J.bound.by.Besov`
  display and the fourth printed term of `l.Besov.norms`), which are the same
  `|sigma_*^{-1}(cu_m)(q + kappa_L(cu_m)p) - p|^2`.

Everything here is a sample-by-sample inequality, so the reabsorbed energy term
appears as `1/2 J(cu_m)` on the right-hand side, exactly as in the printed proof
where `1/2 E[J(cu_m)]` sits on both sides of `e.initial.JL.bound`.

The subadditivity digging room `Sum_{R child of cu_m} 2 (J(R) - J(cu_m))` that
the `l.J.bound.by.Besov` composite carries is merged into the printed defect sum
at the single scale `n = m - 1`; the defect summands are nonnegative by
`e.subaddJ.nosymm`, so the merge only enlarges the right-hand side.

## Scale conventions

The printed discount is `s = 1/4` and the printed exponent is `q = 1`, which is
where `Provider/Homogenization/CombineBadEvent.lean` places the good/bad split.
At `s = 1/4` the printed prefactor exponent `s / (1 - 2s)` is `1/2` and the
printed discount `1 - s` is `3/4`.

## References

* ABK26, Section 3.5, proof of `p.combine.under.S`, Step 1.
-/

namespace Algsuperdiff.Section3.Provider.Homogenization

open Filter MeasureTheory
open _root_.HCPolySupport _root_.HCPolySupport.Book
open _root_.HCPolySupport.Book.Ch05.Section53
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Provider.Besov

noncomputable section

/-! ## Arithmetic cores over abstract reals -/

/-- Cauchy--Schwarz in the shape used by the squared multiscale sums: a weighted
sum of square roots, with the weight split as `f * g`, is controlled by the
`f`-series times the `g`-weighted sum of the radicands. -/
private theorem sq_sum_mul_sqrt_le {iota : Type*} (I : Finset iota) (f g A : iota → ℝ)
    (hf : ∀ i ∈ I, 0 ≤ f i) (hg : ∀ i ∈ I, 0 ≤ g i) (hA : ∀ i ∈ I, 0 ≤ A i) :
    (∑ i ∈ I, f i * (g i * Real.sqrt (A i))) ^ 2 ≤
      (∑ i ∈ I, f i ^ 2) * (∑ i ∈ I, g i ^ 2 * A i) := by
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt I f (fun i => g i * Real.sqrt (A i))
  have hgsq : ∀ i ∈ I, (g i * Real.sqrt (A i)) ^ 2 = g i ^ 2 * A i := by
    intro i hi
    rw [mul_pow, Real.sq_sqrt (hA i hi)]
  rw [Finset.sum_congr rfl hgsq] at hcs
  have hsumf : 0 ≤ ∑ i ∈ I, f i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hsumg : 0 ≤ ∑ i ∈ I, g i ^ 2 * A i :=
    Finset.sum_nonneg fun i hi => mul_nonneg (sq_nonneg _) (hA i hi)
  have hleft : 0 ≤ ∑ i ∈ I, f i * (g i * Real.sqrt (A i)) :=
    Finset.sum_nonneg fun i hi =>
      mul_nonneg (hf i hi) (mul_nonneg (hg i hi) (Real.sqrt_nonneg _))
  calc
    (∑ i ∈ I, f i * (g i * Real.sqrt (A i))) ^ 2 ≤
        (Real.sqrt (∑ i ∈ I, f i ^ 2) * Real.sqrt (∑ i ∈ I, g i ^ 2 * A i)) ^ 2 :=
      pow_le_pow_left₀ hleft hcs 2
    _ = (∑ i ∈ I, f i ^ 2) * (∑ i ∈ I, g i ^ 2 * A i) := by
        rw [mul_pow, Real.sq_sqrt hsumf, Real.sq_sqrt hsumg]

/-- Every truncated geometric series with ratio in `[0,1)` is below the value of
the full series. -/
private theorem geom_sum_le_inv_one_sub {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (K : ℕ) :
    ∑ j ∈ Finset.range K, r ^ j ≤ (1 - r)⁻¹ := by
  have hpos : (0 : ℝ) < 1 - r := by linarith
  have hmul := geom_sum_mul r K
  have hpow : (0 : ℝ) ≤ r ^ K := pow_nonneg hr0 K
  have hval : (∑ j ∈ Finset.range K, r ^ j) * (1 - r) = 1 - r ^ K := by
    linear_combination -hmul
  rw [← one_div, le_div_iff₀ hpos, hval]
  linarith

/-- The Euclidean expansion of a four-term sum. -/
private theorem sq_add_four_le (x y z w : ℝ) :
    (x + y + z + w) ^ 2 ≤ 4 * (x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2) := by
  linarith only [sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (x - w),
    sq_nonneg (y - z), sq_nonneg (y - w), sq_nonneg (z - w)]

/-- **The prefactor gate.**  On the printed good event the upper coarse ellipticity
times the printed power of the coarse ellipticity ratio is at most four times
the comparator.  The exponent `1/2` is the value of the printed `s / (1 - 2 s)`
at the printed discount `s = 1/4`. -/
private theorem upperEllipticity_mul_rpow_ratio_le {sigma lam Lam t : ℝ}
    (hsigma : 0 < sigma) (hLam0 : 0 ≤ Lam) (hlow : sigma / 2 ≤ lam)
    (hup : Lam ≤ 2 * sigma) (ht0 : 0 ≤ t) (ht : t ≤ 1 / 2) :
    Lam * (Lam / lam) ^ t ≤ 4 * sigma := by
  have hlam : 0 < lam := lt_of_lt_of_le (by linarith) hlow
  have hratio0 : 0 ≤ Lam / lam := div_nonneg hLam0 hlam.le
  have hratio : Lam / lam ≤ 4 := by
    rw [div_le_iff₀ hlam]
    linarith
  have hstep1 : (Lam / lam) ^ t ≤ (4 : ℝ) ^ t :=
    Real.rpow_le_rpow hratio0 hratio ht0
  have hstep2 : (4 : ℝ) ^ t ≤ (4 : ℝ) ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) ht
  have hhalf : (4 : ℝ) ^ (1 / 2 : ℝ) = 2 := by
    rw [← Real.sqrt_eq_rpow, show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  have hrpow : (Lam / lam) ^ t ≤ 2 := by
    rw [← hhalf]
    exact hstep1.trans hstep2
  calc Lam * (Lam / lam) ^ t ≤ Lam * 2 := mul_le_mul_of_nonneg_left hrpow hLam0
    _ ≤ 4 * sigma := by linarith only [hup]

/-! ## The two geometric scale series -/

/-- The nonnegative integer cast of a nonnegative integer difference. -/
private theorem toNat_sub_cast {m n : ℤ} (h : n ≤ m) :
    (((m - n).toNat : ℕ) : ℝ) = ((m - n : ℤ) : ℝ) := by
  have h0 : (0 : ℤ) ≤ m - n := by omega
  exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) (Int.toNat_of_nonneg h0)

/-- Every geometrically weighted power of `3` on the corridor is the
corresponding power of the one-step ratio. -/
private theorem rpow_three_mul_eq_pow (c : ℝ) {m n : ℤ} (h : n ≤ m) :
    (3 : ℝ) ^ (c * ((m - n : ℤ) : ℝ)) = ((3 : ℝ) ^ c) ^ (m - n).toNat := by
  rw [← toNat_sub_cast h, ← Real.rpow_natCast ((3 : ℝ) ^ c) ((m - n).toNat),
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]

/-- A geometric weight on the finite corridor `[L,m]` sums below the value of the
full geometric series. -/
private theorem sum_Icc_le_of_geometric {L m : ℤ} (hLm : L ≤ m) {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (w : ℤ → ℝ)
    (hw : ∀ n ∈ Finset.Icc L m, w n = r ^ (m - n).toNat) :
    ∑ n ∈ Finset.Icc L m, w n ≤ (1 - r)⁻¹ := by
  have hreindex :
      ∑ j ∈ Finset.range ((m - L).toNat + 1), r ^ j = ∑ n ∈ Finset.Icc L m, w n := by
    refine Finset.sum_nbij' (fun j : ℕ => m - (j : ℤ)) (fun n : ℤ => (m - n).toNat) ?_ ?_ ?_ ?_ ?_
    · intro j hj
      simp only [Finset.mem_range] at hj
      simp only [Finset.mem_Icc]
      omega
    · intro n hn
      simp only [Finset.mem_Icc] at hn
      simp only [Finset.mem_range]
      omega
    · intro j hj
      simp only [Finset.mem_range] at hj
      show (m - (m - (j : ℤ))).toNat = j
      omega
    · intro n hn
      simp only [Finset.mem_Icc] at hn
      show m - (((m - n).toNat : ℕ) : ℤ) = n
      omega
    · intro j hj
      simp only [Finset.mem_range] at hj
      have hmem : m - (j : ℤ) ∈ Finset.Icc L m := by
        simp only [Finset.mem_Icc]
        omega
      rw [hw _ hmem]
      congr 1
      omega
  rw [← hreindex]
  exact geom_sum_le_inv_one_sub hr0 hr1 _

/-- The printed weight `3^{-(m-n)}` sums to at most `3/2` on the corridor. -/
private theorem sum_Icc_three_neg_le {L m : ℤ} (hLm : L ≤ m) :
    ∑ n ∈ Finset.Icc L m, (3 : ℝ) ^ (-((m - n : ℤ) : ℝ)) ≤ 3 / 2 := by
  have hrv : (3 : ℝ) ^ (-1 : ℝ) = 3⁻¹ := by
    rw [show (-1 : ℝ) = ((-1 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]
    norm_num
  have hbound :
      ∑ n ∈ Finset.Icc L m, (3 : ℝ) ^ (-((m - n : ℤ) : ℝ)) ≤ (1 - (3 : ℝ) ^ (-1 : ℝ))⁻¹ := by
    refine sum_Icc_le_of_geometric hLm (Real.rpow_nonneg (by norm_num) _) ?_ _ ?_
    · rw [hrv]; norm_num
    · intro n hn
      simp only [Finset.mem_Icc] at hn
      rw [show -((m - n : ℤ) : ℝ) = (-1 : ℝ) * ((m - n : ℤ) : ℝ) by ring]
      exact rpow_three_mul_eq_pow (-1 : ℝ) hn.2
  have hval : ((1 : ℝ) - (3 : ℝ) ^ (-1 : ℝ))⁻¹ = 3 / 2 := by
    rw [hrv]; norm_num
  rw [hval] at hbound
  exact hbound

/-- The half-discount weight `3^{-(m-n)/2}` sums to at most `5/2` on the
corridor.  This is the Cauchy--Schwarz series that converts the discount
`3^{-(1-s)(m-n)}` of `l.Besov.norms` into the printed weight `3^{-(m-n)}`. -/
private theorem sum_Icc_three_neg_half_le {L m : ℤ} (hLm : L ≤ m) :
    ∑ n ∈ Finset.Icc L m, (3 : ℝ) ^ (-(1 / 2 : ℝ) * ((m - n : ℤ) : ℝ)) ≤ 5 / 2 := by
  have hr0 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(1 / 2) : ℝ) := Real.rpow_nonneg (by norm_num) _
  have hsqrtlow : (5 : ℝ) / 3 ≤ Real.sqrt 3 := by
    rw [show (5 / 3 : ℝ) = Real.sqrt ((5 / 3 : ℝ) ^ 2) by
      rw [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 5 / 3)]]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hprod : (3 : ℝ) ^ (-(1 / 2) : ℝ) * Real.sqrt 3 = 1 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    norm_num
  have hrle : (3 : ℝ) ^ (-(1 / 2) : ℝ) ≤ 3 / 5 := by
    have hmul := mul_le_mul_of_nonneg_left hsqrtlow hr0
    linarith only [hmul, hprod]
  have hr1 : (3 : ℝ) ^ (-(1 / 2) : ℝ) < 1 := by linarith
  have hbound : ∑ n ∈ Finset.Icc L m, (3 : ℝ) ^ (-(1 / 2 : ℝ) * ((m - n : ℤ) : ℝ)) ≤
      (1 - (3 : ℝ) ^ (-(1 / 2) : ℝ))⁻¹ := by
    refine sum_Icc_le_of_geometric hLm hr0 hr1 _ ?_
    intro n hn
    simp only [Finset.mem_Icc] at hn
    exact rpow_three_mul_eq_pow (-(1 / 2) : ℝ) hn.2
  have hpos : (0 : ℝ) < 1 - (3 : ℝ) ^ (-(1 / 2) : ℝ) := by linarith
  have hcancel : (1 - (3 : ℝ) ^ (-(1 / 2) : ℝ))⁻¹ * (1 - (3 : ℝ) ^ (-(1 / 2) : ℝ)) = 1 :=
    inv_mul_cancel₀ (ne_of_gt hpos)
  have hinvnn : (0 : ℝ) ≤ (1 - (3 : ℝ) ^ (-(1 / 2) : ℝ))⁻¹ := le_of_lt (inv_pos.mpr hpos)
  have hmul2 := mul_le_mul_of_nonneg_left
    (by linarith only [hrle] : (2 : ℝ) / 5 ≤ 1 - (3 : ℝ) ^ (-(1 / 2) : ℝ)) hinvnn
  linarith only [hbound, hmul2, hcancel]

/-- Cauchy--Schwarz on the corridor, in the form the two printed scale sums use:
the display weight is split as a product, the first factor supplies a summable
series and the second factor the printed weight `3^{-(m-n)}`. -/
private theorem sq_sum_le_of_split {L m : ℤ} (W F G A : ℤ → ℝ)
    (hsplit : ∀ n ∈ Finset.Icc L m, W n = F n * G n)
    (hF : ∀ n ∈ Finset.Icc L m, 0 ≤ F n) (hG : ∀ n ∈ Finset.Icc L m, 0 ≤ G n)
    (hA : ∀ n ∈ Finset.Icc L m, 0 ≤ A n) {S T : ℝ} (hS0 : 0 ≤ S)
    (hS : ∑ n ∈ Finset.Icc L m, F n ^ 2 ≤ S)
    (hT : ∑ n ∈ Finset.Icc L m, G n ^ 2 * A n ≤ T) :
    (∑ n ∈ Finset.Icc L m, W n * Real.sqrt (A n)) ^ 2 ≤ S * T := by
  have hcongr : ∀ n ∈ Finset.Icc L m,
      W n * Real.sqrt (A n) = F n * (G n * Real.sqrt (A n)) := by
    intro n hn
    rw [hsplit n hn]
    ring
  rw [Finset.sum_congr rfl hcongr]
  refine (sq_sum_mul_sqrt_le _ F G A hF hG hA).trans ?_
  have hTnn : 0 ≤ ∑ n ∈ Finset.Icc L m, G n ^ 2 * A n :=
    Finset.sum_nonneg fun n hn => mul_nonneg (sq_nonneg _) (hA n hn)
  calc
    (∑ n ∈ Finset.Icc L m, F n ^ 2) * (∑ n ∈ Finset.Icc L m, G n ^ 2 * A n) ≤
        S * ∑ n ∈ Finset.Icc L m, G n ^ 2 * A n := mul_le_mul_of_nonneg_right hS hTnn
    _ ≤ S * T := mul_le_mul_of_nonneg_left hT hS0

/-- **The assembly of Step 1 on the good event, over abstract reals.**  The
four-term display is squared, the energy term is reabsorbed, the digging room is
merged into the defect sum and the three surviving amplitudes are collected under
one constant. -/
private theorem stepOne_assembly {J1 Jm X T1 T2 T3 T4 pref C9 sigma Sd Sv Nc D w C : ℝ}
    (hC9 : 0 < C9) (hsigma : 0 < sigma)
    (hJ1 : J1 ≤ C9 * pref * X ^ 2 + D)
    (hpref : pref ≤ 4 * sigma)
    (hX0 : 0 ≤ X) (hX : X ≤ T1 + T2 + T3 + T4)
    (hsT1 : sigma * T1 ^ 2 ≤ 20 * Sd)
    (hsT2 : sigma * T2 ^ 2 ≤ 3 * (sigma * Sv))
    (hsT3 : 16 * C9 * (sigma * T3 ^ 2) ≤ 1 / 2 * Jm)
    (hsT4 : sigma * T4 ^ 2 ≤ 16 * (sigma * Nc))
    (hD : D ≤ 6 * w * Sd)
    (hSd0 : 0 ≤ Sd) (hSv0 : 0 ≤ sigma * Sv) (hNc0 : 0 ≤ sigma * Nc)
    (hC1 : 320 * C9 + 6 * w ≤ C) (hC2 : 48 * C9 ≤ C) (hC3 : 256 * C9 ≤ C) :
    J1 ≤ 1 / 2 * Jm + C * Sd + C * (sigma * Sv) + C * (sigma * Nc) := by
  have hXsq : X ^ 2 ≤ 4 * (T1 ^ 2 + T2 ^ 2 + T3 ^ 2 + T4 ^ 2) := by
    have hexp := sq_add_four_le T1 T2 T3 T4
    exact (pow_le_pow_left₀ hX0 hX 2).trans hexp
  have hstep1 : C9 * pref * X ^ 2 ≤ C9 * (4 * sigma) * X ^ 2 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpref hC9.le) (sq_nonneg X)
  have hstep2 : C9 * (4 * sigma) * X ^ 2 ≤
      C9 * (4 * sigma) * (4 * (T1 ^ 2 + T2 ^ 2 + T3 ^ 2 + T4 ^ 2)) :=
    mul_le_mul_of_nonneg_left hXsq (by positivity)
  have hexpand : C9 * (4 * sigma) * (4 * (T1 ^ 2 + T2 ^ 2 + T3 ^ 2 + T4 ^ 2)) =
      16 * C9 * (sigma * T1 ^ 2) + 16 * C9 * (sigma * T2 ^ 2) +
        16 * C9 * (sigma * T3 ^ 2) + 16 * C9 * (sigma * T4 ^ 2) := by
    ring
  have hb1 : 16 * C9 * (sigma * T1 ^ 2) ≤ 16 * C9 * (20 * Sd) :=
    mul_le_mul_of_nonneg_left hsT1 (by positivity)
  have hb2 : 16 * C9 * (sigma * T2 ^ 2) ≤ 16 * C9 * (3 * (sigma * Sv)) :=
    mul_le_mul_of_nonneg_left hsT2 (by positivity)
  have hb4 : 16 * C9 * (sigma * T4 ^ 2) ≤ 16 * C9 * (16 * (sigma * Nc)) :=
    mul_le_mul_of_nonneg_left hsT4 (by positivity)
  have hc1 : (320 * C9 + 6 * w) * Sd ≤ C * Sd := mul_le_mul_of_nonneg_right hC1 hSd0
  have hc2 : 48 * C9 * (sigma * Sv) ≤ C * (sigma * Sv) := mul_le_mul_of_nonneg_right hC2 hSv0
  have hc3 : 256 * C9 * (sigma * Nc) ≤ C * (sigma * Nc) := mul_le_mul_of_nonneg_right hC3 hNc0
  linarith

/-! ## The subadditivity digging room as a single defect scale -/

/-- The literal depth-one digging room of the `l.J.bound.by.Besov` composite is
the printed response defect at the single scale `n = m - 1`, times the
dimensional cardinality of the child family. -/
private theorem depthOneDiggingRoom_eq {d : ℕ} [NeZero d] (a : RegCoeffField d)
    (m : ℤ) (p q : Vec d) :
    ∑ R ∈ descendantsAtDepth (originCube d m) 1,
        2 * (Ch04.restrictionResponseJObservableCubeSet R p q a -
          Ch04.restrictionResponseJObservableCubeSet (originCube d m) p q a) =
      2 * ((3 : ℝ) ^ d) *
        WeakNormsMaximizer.responseDefectAverageAtScale m (m - 1) p q a := by
  have hcard : ((descendantsAtDepth (originCube d m) 1).card : ℝ) = (3 : ℝ) ^ d := by
    rw [descendantsAtDepth_card]
    push_cast
    ring
  have hone : (m - (m - 1)).toNat = 1 := by omega
  have hdef : WeakNormsMaximizer.responseDefectAverageAtScale m (m - 1) p q a =
      descendantsAverage (originCube d m) 1
          (fun R => Ch04.restrictionResponseJObservableCubeSet R p q a) -
        Ch04.restrictionResponseJObservableCubeSet (originCube d m) p q a := by
    show descendantsAverage (originCube d m) (m - (m - 1)).toNat
        (fun R => Ch04.restrictionResponseJObservableCubeSet R p q a) - _ = _
    rw [hone]
  have havg : descendantsAverage (originCube d m) 1
      (fun R => Ch04.restrictionResponseJObservableCubeSet R p q a) =
      (((descendantsAtDepth (originCube d m) 1).card : ℝ))⁻¹ *
        ∑ R ∈ descendantsAtDepth (originCube d m) 1,
          Ch04.restrictionResponseJObservableCubeSet R p q a := rfl
  have hsum : ∑ R ∈ descendantsAtDepth (originCube d m) 1,
      2 * (Ch04.restrictionResponseJObservableCubeSet R p q a -
        Ch04.restrictionResponseJObservableCubeSet (originCube d m) p q a) =
      2 * (∑ R ∈ descendantsAtDepth (originCube d m) 1,
          Ch04.restrictionResponseJObservableCubeSet R p q a) -
        2 * ((3 : ℝ) ^ d) *
          Ch04.restrictionResponseJObservableCubeSet (originCube d m) p q a := by
    rw [Finset.sum_congr rfl
      (fun R _ => mul_sub 2 (Ch04.restrictionResponseJObservableCubeSet R p q a)
        (Ch04.restrictionResponseJObservableCubeSet (originCube d m) p q a)),
      Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, hcard]
    ring
  rw [hsum, hdef, havg, hcard]
  have h3 : ((3 : ℝ) ^ d) ≠ 0 := by positivity
  field_simp

/-! ## The good-event branch of Step 1 -/

/-- **The good-event branch of Step 1 of `p.combine.under.S`**, sample by sample
and on the actual coefficient field.

On the printed good event `e.goodevent.combine` at the printed discount
`s = 1/4` and printed exponent `q = 1`, that is under the two clauses

`sigma / 2 <= lambda_{1/4,1}(cu_m; a)` and `Lambda_{1/4,1}(cu_m; a) <= 2 sigma`,

and under the printed smallness constraint `C 3^{-(1-s)(m-L)} <= 1/4`, the response
of the ordinary central child obeys the display the printed proof reaches: the
maximizing energy term has been reabsorbed through `e.Jenergyv.nosymm`, so half
the response at the parent scale sits on the right-hand side, and the remaining
three amplitudes are the printed defect sum with the printed weight
`3^{-(m-n)}` over the finite corridor `L <= n <= m`, the printed coarse-matrix
variation in its `avsum` form, and the printed constant tail, each carrying a
single power of the comparator.

This is NOT the labelled display `e.initial.JL.bound`, whose second and third
blocks are the variances and whose comparator prefactor is `sigmabar_L^2` after
the normalization `|q|^2 = sigmabar_L`, `|p|^2 = sigmabar_L^{-1}` of
`e.pq.normed` and the sandwich `sigmabar_{L,*}(cu_m) <= sigmabar_L <= 2
sigmabar_{L,*}(cu_m)`.  The variance split, that normalization, the expectation
lane and stationarity are not performed here.  The middle printed clause
`lambda_{1/4,1} <= Lambda_{1/4,1}` of `e.goodevent.combine` is not assumed: the
estimate holds from the two outer clauses alone, so the hypothesis set here is
weaker than the printed event.

The constant depends only on `d`, and on nothing else: it is quantified before
the field, the scales, the comparator and the loads.

This is a local Provider theorem and makes no source-node status claim. -/
theorem exists_goodEvent_restrictionResponseJ_centralChild_le_preVarianceSplitDisplay
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (a : RegCoeffField d) (ha : Ch04.AELocallyUniformlyEllipticField a) (m L : ℤ),
        L ≤ m - 1 →
        C * (3 : ℝ) ^ (-(3 / 4 : ℝ) * ((m - L : ℤ) : ℝ)) ≤ 1 / 4 →
        ∀ sigma : ℝ, 0 < sigma →
          sigma / 2 ≤ Ch02.lambdaSq (originCube d m) (1 / 4)
              (Ch02.MultiscaleExponent.finite 1)
              (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha) →
          Ch02.LambdaSq (originCube d m) (1 / 4) (Ch02.MultiscaleExponent.finite 1)
              (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha) ≤ 2 * sigma →
          ∀ p q : Vec d,
            Ch04.restrictionResponseJObservableCubeSet (originCube d (m - 1)) p q a ≤
              1 / 2 * Ch04.restrictionResponseJObservableCubeSet (originCube d m) p q a +
                C * (∑ n ∈ Finset.Icc L m, (3 : ℝ) ^ (-((m - n : ℤ) : ℝ)) *
                      WeakNormsMaximizer.responseDefectAverageAtScale m n p q a) +
                C * (sigma * ∑ n ∈ Finset.Icc L m, (3 : ℝ) ^ (-((m - n : ℤ) : ℝ)) *
                      descendantsAverage (originCube d m) (m - n).toNat
                        (coarseMatrixVariationSq a ha (originCube d m) p q)) +
                C * (sigma * vecNormSq (coarseScaleSeparation a ha (originCube d m) p q)) := by
  obtain ⟨C9, hC9, hJbound⟩ :=
    exists_restrictionResponseJ_centralChild_le_jBoundByBesovDisplay d
  have hdimPow : (1 : ℝ) ≤ (3 : ℝ) ^ d := one_le_pow₀ (by norm_num)
  refine ⟨320 * C9 + 6 * (3 : ℝ) ^ d + 1, by linarith only [hC9, hdimPow], ?_⟩
  intro a ha m L hLm1 hcons sigma hsigma hlow hup p q
  have hLm : L ≤ m := by omega
  -- the two consumed inputs
  have hJ := hJbound a ha m p q (s := 1 / 4) (by norm_num) (by norm_num)
  have hfour := centredMultiscaleAverageSum_le_fourTerm a ha hLm (s := 1 / 4)
    (by norm_num) (by norm_num) (r := Ch02.MultiscaleExponent.finite 1) (le_refl (1 : ℝ)) p q
  have hlamField : Ch04.lambdaSqCoeffField (originCube d m) (1 / 4 : ℝ)
      (Ch02.MultiscaleExponent.finite 1) a =
      Ch02.lambdaSq (originCube d m) (1 / 4) (Ch02.MultiscaleExponent.finite 1)
        (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha) := by
    rw [Ch04.lambdaSqCoeffField]
    simp only [dite_eq_left ha]
  rw [hlamField] at hfour
  -- names
  set C : ℝ := 320 * C9 + 6 * (3 : ℝ) ^ d + 1 with hCdef
  set Fam := Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha with hFam
  set lamv : ℝ := Ch02.lambdaSq (originCube d m) (1 / 4)
    (Ch02.MultiscaleExponent.finite 1) Fam with hlamv
  set Lamv : ℝ := Ch02.LambdaSq (originCube d m) (1 / 4)
    (Ch02.MultiscaleExponent.finite 1) Fam with hLamv
  set Nc : ℝ := vecNormSq (coarseScaleSeparation a ha (originCube d m) p q) with hNc
  set Jm : ℝ := Ch04.restrictionResponseJObservableCubeSet (originCube d m) p q a with hJm
  set Sd : ℝ := ∑ n ∈ Finset.Icc L m, (3 : ℝ) ^ (-((m - n : ℤ) : ℝ)) *
    WeakNormsMaximizer.responseDefectAverageAtScale m n p q a with hSd
  set Sv : ℝ := ∑ n ∈ Finset.Icc L m, (3 : ℝ) ^ (-((m - n : ℤ) : ℝ)) *
    descendantsAverage (originCube d m) (m - n).toNat
      (coarseMatrixVariationSq a ha (originCube d m) p q) with hSv
  set Aser : ℝ := ∑ n ∈ Finset.Icc L m, (3 : ℝ) ^ (-(1 - 1 / 4 : ℝ) * ((m - n : ℤ) : ℝ)) *
    Real.sqrt (WeakNormsMaximizer.responseDefectAverageAtScale m n p q a) with hAser
  set Bser : ℝ := ∑ n ∈ Finset.Icc L m, (3 : ℝ) ^ (-((m - n : ℤ) : ℝ)) *
    Real.sqrt (descendantsAverage (originCube d m) (m - n).toNat
      (coarseMatrixVariationSq a ha (originCube d m) p q)) with hBser
  set wL : ℝ := (3 : ℝ) ^ (-(1 - 1 / 4 : ℝ) * ((m - L : ℤ) : ℝ)) with hwL
  set uL : ℝ := (3 : ℝ) ^ (-((m - L : ℤ) : ℝ)) with huL
  set Ev : ℝ := maximizerEnergyL2Norm a ha (originCube d m) p q with hEv
  -- the prefactor
  have hLamS : Ch02.LambdaS (originCube d m) (1 / 4 : ℝ) Fam = Lamv := rfl
  have hThetaEq : Ch02.ThetaRatio (originCube d m) (1 / 4 : ℝ) (1 / 4) Fam = Lamv / lamv := rfl
  rw [hLamS, hThetaEq] at hJ
  set theta : ℝ := Real.rpow (Lamv / lamv) ((1 / 4 : ℝ) / (1 - 2 * (1 / 4))) with htheta
  -- the four terms of `l.Besov.norms`
  set T1 : ℝ := 2 * Real.sqrt lamv⁻¹ * Aser with hT1
  set T2 : ℝ := Real.sqrt 2 * Bser with hT2
  set T3 : ℝ := 2 * Real.sqrt 2 * (wL * Real.sqrt lamv⁻¹ * Ev) with hT3
  set T4 : ℝ := 4 * Real.sqrt Nc with hT4
  set Xv : ℝ := centredMultiscaleAverageSum a ha m p q + Real.sqrt Nc with hXv
  -- the facts that need the definitional bodies
  have hlamPos : 0 < lamv := lt_of_lt_of_le (by linarith) hlow
  have hLamNonneg : 0 ≤ Lamv :=
    Ch02.LambdaSq_finite_nonneg (originCube d m) Fam (by norm_num) le_rfl
  have hNc0 : 0 ≤ Nc := vecNormSq_nonneg _
  have hJm0 : 0 ≤ Jm := Ch04.restrictionResponseJObservableCubeSet_nonneg _ p q a
  have hdefNonneg : ∀ n : ℤ, 0 ≤ WeakNormsMaximizer.responseDefectAverageAtScale m n p q a :=
    fun n => WeakNormsMaximizer.responseDefectAverageAtScale_nonneg_of_aelocallyUniformlyEllipticField
      a ha m n p q
  have hvarNonneg : ∀ n : ℤ, 0 ≤ descendantsAverage (originCube d m) (m - n).toNat
      (coarseMatrixVariationSq a ha (originCube d m) p q) := fun n =>
    descendantsAverage_nonneg _ _ _ fun R _ => coarseMatrixVariationSq_nonneg a ha _ p q R
  have hSd0 : 0 ≤ Sd := by
    rw [hSd]
    exact Finset.sum_nonneg fun n _ =>
      mul_nonneg (Real.rpow_nonneg (by norm_num) _) (hdefNonneg n)
  have hSv0 : 0 ≤ Sv := by
    rw [hSv]
    exact Finset.sum_nonneg fun n _ =>
      mul_nonneg (Real.rpow_nonneg (by norm_num) _) (hvarNonneg n)
  have hML0 : (0 : ℝ) ≤ ((m - L : ℤ) : ℝ) := by
    exact_mod_cast (by omega : (0 : ℤ) ≤ m - L)
  have hwL0 : 0 ≤ wL := by
    rw [hwL]; exact Real.rpow_nonneg (by norm_num) _
  have huL0 : 0 ≤ uL := by
    rw [huL]; exact Real.rpow_nonneg (by norm_num) _
  have huL1 : uL ≤ 1 := by
    rw [huL]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
  have hwL1 : wL ≤ 1 := by
    rw [hwL]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
  clear_value Xv T4 T3 T2 T1 theta Ev uL wL Bser Aser Sv Sd Jm Nc Lamv lamv Fam C
  have hsiglam : sigma * lamv⁻¹ ≤ 2 := by
    rw [mul_inv_le_iff₀ hlamPos]
    linarith
  have hpref : Lamv * theta ≤ 4 * sigma := by
    rw [htheta]
    exact upperEllipticity_mul_rpow_ratio_le hsigma hLamNonneg hlow hup (by norm_num)
      (by norm_num)
  have hsqrt2le : Real.sqrt 2 ≤ 3 / 2 := by
    rw [show (3 / 2 : ℝ) = Real.sqrt ((3 / 2 : ℝ) ^ 2) by
      rw [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 3 / 2)]]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hsqlam : Real.sqrt lamv⁻¹ ^ 2 = lamv⁻¹ :=
    Real.sq_sqrt (le_of_lt (inv_pos.mpr hlamPos))
  have hsq2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsqNc : Real.sqrt Nc ^ 2 = Nc := Real.sq_sqrt hNc0
  -- Cauchy--Schwarz on the two printed scale sums
  have hAsq : Aser ^ 2 ≤ 5 / 2 * Sd := by
    rw [hAser, hSd]
    refine sq_sum_le_of_split _ (fun n => (3 : ℝ) ^ (-(1 / 4 : ℝ) * ((m - n : ℤ) : ℝ)))
      (fun n => (3 : ℝ) ^ (-(1 / 2 : ℝ) * ((m - n : ℤ) : ℝ)))
      (fun n => WeakNormsMaximizer.responseDefectAverageAtScale m n p q a)
      (fun n _ => ?_) (fun n _ => Real.rpow_nonneg (by norm_num) _)
      (fun n _ => Real.rpow_nonneg (by norm_num) _) (fun n _ => hdefNonneg n)
      (by norm_num) ?_ ?_
    · rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      congr 1
      ring
    · refine le_trans (le_of_eq (Finset.sum_congr rfl fun n _ => ?_))
        (sum_Icc_three_neg_half_le hLm)
      rw [← Real.rpow_natCast ((3 : ℝ) ^ (-(1 / 4 : ℝ) * ((m - n : ℤ) : ℝ))) 2,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
      congr 1
      push_cast
      ring
    · refine le_of_eq (Finset.sum_congr rfl fun n _ => ?_)
      congr 1
      rw [← Real.rpow_natCast ((3 : ℝ) ^ (-(1 / 2 : ℝ) * ((m - n : ℤ) : ℝ))) 2,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
      congr 1
      push_cast
      ring
  have hBsq : Bser ^ 2 ≤ 3 / 2 * Sv := by
    rw [hBser, hSv]
    refine sq_sum_le_of_split _ (fun n => (3 : ℝ) ^ (-(1 / 2 : ℝ) * ((m - n : ℤ) : ℝ)))
      (fun n => (3 : ℝ) ^ (-(1 / 2 : ℝ) * ((m - n : ℤ) : ℝ)))
      (fun n => descendantsAverage (originCube d m) (m - n).toNat
        (coarseMatrixVariationSq a ha (originCube d m) p q))
      (fun n _ => ?_) (fun n _ => Real.rpow_nonneg (by norm_num) _)
      (fun n _ => Real.rpow_nonneg (by norm_num) _) (fun n _ => hvarNonneg n)
      (by norm_num) ?_ ?_
    · rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      congr 1
      ring
    · refine le_trans (le_of_eq (Finset.sum_congr rfl fun n _ => ?_))
        (sum_Icc_three_neg_le hLm)
      rw [← Real.rpow_natCast ((3 : ℝ) ^ (-(1 / 2 : ℝ) * ((m - n : ℤ) : ℝ))) 2,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
      congr 1
      push_cast
      ring
    · refine le_of_eq (Finset.sum_congr rfl fun n _ => ?_)
      congr 1
      rw [← Real.rpow_natCast ((3 : ℝ) ^ (-(1 / 2 : ℝ) * ((m - n : ℤ) : ℝ))) 2,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
      congr 1
      push_cast
      ring
  -- the four squared amplitudes
  have hT1sq : sigma * T1 ^ 2 ≤ 20 * Sd := by
    have hexp : sigma * T1 ^ 2 = 4 * (sigma * lamv⁻¹) * Aser ^ 2 := by
      rw [hT1, show (2 * Real.sqrt lamv⁻¹ * Aser) ^ 2 =
        4 * Real.sqrt lamv⁻¹ ^ 2 * Aser ^ 2 by ring, hsqlam]
      ring
    rw [hexp]
    have hgap : 0 ≤ (2 - sigma * lamv⁻¹) * Aser ^ 2 :=
      mul_nonneg (by linarith only [hsiglam]) (sq_nonneg Aser)
    linarith only [hgap, hAsq]
  have hT2sq : sigma * T2 ^ 2 ≤ 3 * (sigma * Sv) := by
    have hexp : sigma * T2 ^ 2 = 2 * sigma * Bser ^ 2 := by
      rw [hT2, show (Real.sqrt 2 * Bser) ^ 2 = Real.sqrt 2 ^ 2 * Bser ^ 2 by ring, hsq2]
      ring
    rw [hexp]
    linarith only [mul_nonneg hsigma.le (sub_nonneg.mpr hBsq)]
  have hT4sq : sigma * T4 ^ 2 ≤ 16 * (sigma * Nc) := by
    rw [hT4, show (4 * Real.sqrt Nc) ^ 2 = 16 * Real.sqrt Nc ^ 2 by ring, hsqNc]
    exact le_of_eq (by ring)
  have hT3sq : 16 * C9 * (sigma * T3 ^ 2) ≤ 1 / 2 * Jm := by
    have hEsq : Ev ^ 2 = 2 * Jm := by
      rw [hEv, hJm, sq_maximizerEnergyL2Norm,
        maximizerEnergyL2NormSq_eq_two_mul_restrictionResponseJObservableCubeSet]
    have hexp : sigma * T3 ^ 2 = 16 * wL ^ 2 * (sigma * lamv⁻¹) * Jm := by
      rw [hT3, show (2 * Real.sqrt 2 * (wL * Real.sqrt lamv⁻¹ * Ev)) ^ 2 =
        4 * Real.sqrt 2 ^ 2 * wL ^ 2 * Real.sqrt lamv⁻¹ ^ 2 * Ev ^ 2 by ring, hsq2, hsqlam,
        hEsq]
      ring
    have hwLcons : C * wL ≤ 1 / 4 := by
      rw [hwL, show (-(1 - 1 / 4 : ℝ)) * ((m - L : ℤ) : ℝ) =
        (-(3 / 4 : ℝ)) * ((m - L : ℤ) : ℝ) by ring]
      exact hcons
    have h256 : 256 * C9 ≤ C := by
      rw [hCdef]
      linarith only [hC9, hdimPow]
    have hC9wL : C9 * wL ≤ 1 / 1024 := by
      linarith only [hwLcons,
        mul_nonneg (by linarith only [h256] : (0 : ℝ) ≤ C - 256 * C9) hwL0]
    have hwLsq : wL ^ 2 ≤ wL := by nlinarith only [hwL0, hwL1]
    have hfac : (0 : ℝ) ≤ 256 * C9 * wL ^ 2 * Jm :=
      mul_nonneg (mul_nonneg (by linarith only [hC9]) (sq_nonneg wL)) hJm0
    have h1 : 256 * C9 * wL ^ 2 * (sigma * lamv⁻¹) * Jm ≤ 512 * C9 * wL ^ 2 * Jm :=
      by linarith only [mul_nonneg (by linarith only [hsiglam] :
        (0 : ℝ) ≤ 2 - sigma * lamv⁻¹) hfac]
    have h2 : 512 * C9 * wL ^ 2 * Jm ≤ 512 * C9 * wL * Jm :=
      by linarith only [mul_nonneg (mul_nonneg hC9.le (sub_nonneg.mpr hwLsq)) hJm0]
    have hstep : 16 * C9 * (sigma * T3 ^ 2) ≤ 512 * (C9 * wL) * Jm := by
      rw [hexp]
      linarith only [h1, h2]
    linarith only [hstep, mul_nonneg (sub_nonneg.mpr hC9wL) hJm0]
  -- the digging room
  have hDefectSingle : WeakNormsMaximizer.responseDefectAverageAtScale m (m - 1) p q a ≤
      3 * Sd := by
    have hmem : m - 1 ∈ Finset.Icc L m := by
      simp only [Finset.mem_Icc]
      omega
    have hsingle : (3 : ℝ) ^ (-((m - (m - 1) : ℤ) : ℝ)) *
        WeakNormsMaximizer.responseDefectAverageAtScale m (m - 1) p q a ≤
        ∑ n ∈ Finset.Icc L m, (3 : ℝ) ^ (-((m - n : ℤ) : ℝ)) *
          WeakNormsMaximizer.responseDefectAverageAtScale m n p q a :=
      Finset.single_le_sum
        (f := fun n : ℤ => (3 : ℝ) ^ (-((m - n : ℤ) : ℝ)) *
          WeakNormsMaximizer.responseDefectAverageAtScale m n p q a)
        (fun n _ => mul_nonneg (Real.rpow_nonneg (by norm_num) _) (hdefNonneg n)) hmem
    have hmm : ((m - (m - 1) : ℤ) : ℝ) = 1 := by push_cast; ring
    have hval : (3 : ℝ) ^ (-((m - (m - 1) : ℤ) : ℝ)) = 3⁻¹ := by
      rw [hmm, show (-1 : ℝ) = ((-1 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]
      norm_num
    rw [hval, ← hSd] at hsingle
    linarith only [hsingle]
  have hD : (∑ R ∈ descendantsAtDepth (originCube d m) 1,
      2 * (Ch04.restrictionResponseJObservableCubeSet R p q a - Jm)) ≤
      6 * (3 : ℝ) ^ d * Sd := by
    rw [hJm, depthOneDiggingRoom_eq a m p q]
    linarith only [mul_nonneg (by linarith only [hdimPow] : (0 : ℝ) ≤ (3 : ℝ) ^ d)
      (by linarith only [hDefectSingle] :
        (0 : ℝ) ≤ 3 * Sd - WeakNormsMaximizer.responseDefectAverageAtScale m (m - 1) p q a)]
  -- the comparison of the multiscale sum with the four terms
  have hX : Xv ≤ T1 + T2 + T3 + T4 := by
    have hT4bound : 2 * Real.sqrt 2 * (uL * Real.sqrt Nc) + Real.sqrt Nc ≤ T4 := by
      rw [hT4]
      have h1 : 2 * Real.sqrt 2 * uL ≤ 3 := by
        nlinarith only [hsqrt2le, huL0, huL1, Real.sqrt_nonneg 2]
      linarith only [mul_le_mul_of_nonneg_right h1 (Real.sqrt_nonneg Nc),
        Real.sqrt_nonneg Nc]
    rw [hXv]
    linarith only [hfour, hT4bound]
  have hX0 : 0 ≤ Xv := by
    rw [hXv]
    exact add_nonneg (centredMultiscaleAverageSum_nonneg a ha m p q) (Real.sqrt_nonneg _)
  -- the composite, with the prefactor factored
  have hJ1 : Ch04.restrictionResponseJObservableCubeSet (originCube d (m - 1)) p q a ≤
      C9 * (Lamv * theta) * Xv ^ 2 +
        ∑ R ∈ descendantsAtDepth (originCube d m) 1,
          2 * (Ch04.restrictionResponseJObservableCubeSet R p q a - Jm) :=
    hJ.trans (le_of_eq (by rw [hXv]; ring))
  refine stepOne_assembly hC9 hsigma hJ1 hpref hX0 hX hT1sq hT2sq hT3sq hT4sq hD hSd0
    (mul_nonneg hsigma.le hSv0) (mul_nonneg hsigma.le hNc0) ?_ ?_ ?_
  · rw [hCdef]; linarith only []
  · rw [hCdef]; linarith only [hC9, hdimPow]
  · rw [hCdef]; linarith only [hC9, hdimPow]

/-- **The good-event branch of Step 1 on the Section 3 cutoff carrier.**

The good event is the complement of `observationScaleBadEvent M L m`, which
`mem_observationScaleBadEvent_iff` identifies with the printed
`e.goodevent.combine` at `s = 1/4`, `q = 1`, on the genuine cutoff family; the
comparator is the running diffusivity `sigmabar_L` and the loads are the
manuscript ones, `p = sigmabar_L^{-1/2} e` and `q = sigmabar_L^{1/2} e`.

The two response scales are read through the one common measurable
representative, so the estimate holds off a single null set.  The response
defect, the coarse-matrix variation and the constant tail are still the
deterministic field quantities: taking expectations of them, through stationarity
and the annealed identities, is the next step of the printed proof and is not
performed here.

This is a local Provider theorem and makes no source-node status claim. -/
theorem exists_cutoffGoodEvent_cutoffResponseJ_le_preVarianceSplitDisplay (d : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (M : ABKModel d) (m L : ℤ), L ≤ m - 1 →
        C * (3 : ℝ) ^ (-(3 / 4 : ℝ) * ((m - L : ℤ) : ℝ)) ≤ 1 / 4 →
        ∀ e : Vec d,
          ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
            omega ∉ observationScaleBadEvent M L m →
              Observable.cutoffResponseJ M (m - 1) L e omega ≤
                1 / 2 * Observable.cutoffResponseJ M m L e omega +
                  C * (∑ n ∈ Finset.Icc L m, (3 : ℝ) ^ (-((m - n : ℤ) : ℝ)) *
                        WeakNormsMaximizer.responseDefectAverageAtScale m n
                          (Observable.inverseSqrtLoad (Annealed.sigmaBar M L) e)
                          (Observable.sqrtLoad (Annealed.sigmaBar M L) e)
                          (Cutoff.coefficientCutoff M.nu L omega)) +
                  C * ((Annealed.sigmaBar M L : ℝ) *
                        ∑ n ∈ Finset.Icc L m, (3 : ℝ) ^ (-((m - n : ℤ) : ℝ)) *
                          descendantsAverage (originCube d m) (m - n).toNat
                            (coarseMatrixVariationSq (Cutoff.coefficientCutoff M.nu L omega)
                              (Cutoff.coefficientCutoff_aeLocallyUniformlyEllipticField M L omega)
                              (originCube d m)
                              (Observable.inverseSqrtLoad (Annealed.sigmaBar M L) e)
                              (Observable.sqrtLoad (Annealed.sigmaBar M L) e))) +
                  C * ((Annealed.sigmaBar M L : ℝ) *
                        vecNormSq (coarseScaleSeparation (Cutoff.coefficientCutoff M.nu L omega)
                          (Cutoff.coefficientCutoff_aeLocallyUniformlyEllipticField M L omega)
                          (originCube d m)
                          (Observable.inverseSqrtLoad (Annealed.sigmaBar M L) e)
                          (Observable.sqrtLoad (Annealed.sigmaBar M L) e))) := by
  classical
  by_cases hd : d = 0
  · exact ⟨1, le_rfl, fun M => absurd M.shellPrefix.dimension (by omega)⟩
  let : NeZero d := ⟨hd⟩
  obtain ⟨C, hC, hbound⟩ :=
    exists_goodEvent_restrictionResponseJ_centralChild_le_preVarianceSplitDisplay d
  refine ⟨C, hC, ?_⟩
  intro M m L hLm1 hcons e
  filter_upwards [Observable.ae_forall_cutoffResponseJ_eq_literal M (m - 1) L,
    Observable.ae_forall_cutoffResponseJ_eq_literal M m L] with omega hlit1 hlit2 hgood
  have hcut := Cutoff.coefficientCutoff_aeLocallyUniformlyEllipticField M L omega
  have hclauses := not_not.mp
    (fun hn => hgood ((mem_observationScaleBadEvent_iff M L m omega).mpr hn))
  obtain ⟨hlow, -, hup⟩ := hclauses
  have haeeq : Ch02.TriadicCoeffFamily.AEEq
      (Cutoff.coefficientCutoffTriadicCoeffFamily M L omega)
      (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField
        (Cutoff.coefficientCutoff M.nu L omega) hcut) := fun _ => Filter.EventuallyEq.rfl
  rw [Ch02.lambdaSq_eq_ofAEEq haeeq] at hlow
  rw [Ch02.LambdaSq_eq_ofAEEq haeeq] at hup
  have hmain := hbound (Cutoff.coefficientCutoff M.nu L omega) hcut m L hLm1 hcons
    ((Annealed.sigmaBar M L : ℝ)) (Annealed.sigmaBar M L).2 hlow hup
    (Observable.inverseSqrtLoad (Annealed.sigmaBar M L) e)
    (Observable.sqrtLoad (Annealed.sigmaBar M L) e)
  rw [hlit1 e, hlit2 e]
  simpa only [Ch04.restrictionResponseJObservableCubeSet_apply] using hmain

end

end Algsuperdiff.Section3.Provider.Homogenization
