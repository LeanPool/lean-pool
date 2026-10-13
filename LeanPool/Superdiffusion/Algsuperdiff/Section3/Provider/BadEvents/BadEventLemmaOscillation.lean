/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.BadEvents.AdmissibleGates
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.BadEvents.GoodLocalEvents

/-!
# BadEventLemmaOscillation

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The oscillation branch of `l.bad.event.lemma`

ABK26's Lemma `l.bad.event.lemma` bounds the failure probability of the good
local sensitivity event `Q(m,n,z)` of `e.good.local.events`.  Its proof splits
`not Q(m,n,z)` into a coarse-ellipticity failure and the *oscillation* event

```
B_osc(m,n) = { sup_{L >= n} 3^{2m} ||grad (k_L - k_n)||_{W^{1,infinity}(z+square_m)}
                 > c c_star^{1/2} gamma^{-1/2} 3^{gamma n} 3^{-(1/2)(n-m)_+} } ,
```

and claims for the latter the displayed bound `e.oscillation.bound`

```
P[ B_osc(m,n) ]  <=  exp( - c c_star gamma^{-1} 3^{-5 (m-n)_+} 3^{(n-m)_+} ) .
```

This module proves the corresponding estimate **on the branch `m <= n`**
(`Q.scale <= n`) for the internal event `goodLocalSensitivityFailure` of
`GoodLocalEvents.lean`.  That event is a stricter, unrelaxed subset of the
printed oscillation event, not an identification with it.  The result is a
useful branch input to the umbrella proof, but it does not by itself realize or
close the printed oscillation node.  The induction-state comparison
`sqrt_cstar_mul_inv_sqrt_gamma_mul_rpow_le_two_mul_sigmaBar` is used internally
to price this stricter event.

## The route

The manuscript decomposes `B_osc(m,n)` into the waves below scale `m` and the
shells `L in [m, infinity)`.  On the branch `m <= n` the increment `k_L - k_n`
consists of shells `k > n >= m` only: the wave term `k_m - k_{n and m}` is
identically zero, and every shell that occurs sits at or above the cube scale.
The local proof therefore decomposes over the shells `k > n` (rather than over
`L >= m`), which is what the manuscript's own displays need — see the
implementation note at the end of this docstring.

1. `shellSensitivityThreshold` splits the event's threshold geometrically over
   the shells `k > n`, with ratio `3^{-1/5}` and prefactor `1/5`, exactly as
   `e.Bosc.decomp` splits the `e.Bosc.def` threshold.  The arithmetic `(1/5)
   sum_{i >= 1} 3^{-i/5} <= 1` is `sum_range_shellSensitivityThreshold_le`.
2. `goodLocalSensitivityFailure_subset_iUnion` is the resulting containment: it
   uses only the `W^{1,infinity}` triangle inequality
   `incrementOscGauge₂_le_sum_shellOscGauge` of `IncrementGaugeTwoIndex.lean`.
3. `measureReal_shellSensitivityFailure_le` prices one shell against the proved
   translated `e.nabla.jk.O` tail `isBigOWith_gammaSigma_shellOscGauge`, after
   converting the event's `sigmabar_{n-1}` threshold into the `c_star`--`gamma`
   amplitude by the induction state.
4. `measureReal_goodLocalSensitivityFailure_le` sums the shells.

## The gate

The weak-Orlicz tail of `e.nabla.jk.O` is available only above its amplitude,
so each shell may be priced only when its threshold-to-amplitude ratio is at
least one; and the geometric summation of `exp(-kappa 3^i)` over `i >= 1` is
below `exp(-kappa)` only for `kappa >= 1`.  Both are exactly `1 <= rate`, where
`rate` is `badEventOscRate`, the exponent of the displayed bound.  This is the
same gate as `unitGate` in `OscillationProbability.lean`, and on this branch it
is discharged from the manuscript's own admissibility
`e.bad.event.admissibility` by `one_le_badEventOscRate_of_admissible`, using
the absolute bound
`Algsuperdiff.Section3.Provider.Disorder.cstar_le_three_halves`; nothing beyond
the printed display is assumed by
`measureReal_goodLocalSensitivityFailure_le_of_admissible`.

## Implementation notes (not manuscript defects, except where flagged)

* **This file treats only `m ≤ n`.**  The later provider
  `OscillationBranchLow.lean` supplies the other internal branch `n < m`.
  Having both internal branch estimates does not identify
  `goodLocalSensitivityFailure` with the printed `B_osc`, so it still does not
  confer source-node status.
* **The constant.**  `c` of the display is chosen as `badEventOscConst d Ccg =
  (1/3600) C_sens(d)^{-2} Ccg^{-2}`, where `Ccg` is the explicit parameter
  carrying `C_{(e.cg.ellip.lower)}` (the now-proved frozen
  `coarse_ellipticity_bounds` supplies such a dimension-only constant to a
  downstream consumer; this conditional A remains parametrized, exactly as in
  `GoodLocalEllipticity.lean`) and `C_sens(d) = sensitivityConstMax d` is the
  dimension-only joint sensitivity constant.  The manuscript's requirement `c depends only
  on d` is respected: both factors are dimension-only.

## Main definitions

* `shellSensitivityThreshold`, `shellSensitivityFailure`: the geometric split of
  the event's threshold over the shells above `n`.
* `badEventOscConst`, `badEventOscRate`: the constant and the exponent of
  `e.oscillation.bound`.
* `badEventOscAdmissibleConst`: the dimension-only constant at which the printed
  admissibility discharges the gate.

## Main results

* `goodLocalSensitivityFailure_subset_iUnion`.
* `measureReal_shellSensitivityFailure_le`.
* `measureReal_goodLocalSensitivityFailure_le`.

## References

* ABK26, `l.bad.event.lemma`; `e.oscillation.bound`; the wave decomposition.
* ABK26, `e.good.local.events`.
* ABK26, `e.nabla.jk.O`; `e.Bosc.decomp`.
-/

namespace Algsuperdiff.Section3.Provider.BadEvents

open MeasureTheory
open HCPolySupport HCPolySupport.Book
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.Stream

noncomputable section

variable {d : ℕ}

/-! ## Elementary numerics -/

private theorem three_rpow_pos (x : ℝ) : (0 : ℝ) < (3 : ℝ) ^ x :=
  Real.rpow_pos_of_pos (by norm_num) x

private theorem three_rpow_add (x y : ℝ) :
    (3 : ℝ) ^ x * (3 : ℝ) ^ y = (3 : ℝ) ^ (x + y) :=
  (Real.rpow_add (by norm_num) x y).symm

private theorem three_rpow_half_sq (x : ℝ) :
    ((3 : ℝ) ^ ((1 / 2 : ℝ) * x)) ^ 2 = (3 : ℝ) ^ x := by
  rw [← Real.rpow_natCast ((3 : ℝ) ^ ((1 / 2 : ℝ) * x)) 2,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
  congr 1
  push_cast
  ring

private theorem three_rpow_neg_fifth_pos : (0 : ℝ) < (3 : ℝ) ^ (-(1 / 5 : ℝ)) :=
  three_rpow_pos _

private theorem three_rpow_neg_fifth_lt_one : (3 : ℝ) ^ (-(1 / 5 : ℝ)) < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)

private theorem three_rpow_neg_fifth_le : (3 : ℝ) ^ (-(1 / 5 : ℝ)) ≤ 5 / 6 := by
  have hbase : (0 : ℝ) ≤ (6 : ℝ) / 5 := by norm_num
  have hpow : ((6 : ℝ) / 5) ^ (5 : ℕ) ≤ 3 := by norm_num
  have hmono : (((6 : ℝ) / 5) ^ (5 : ℕ)) ^ (1 / 5 : ℝ) ≤ (3 : ℝ) ^ (1 / 5 : ℝ) :=
    Real.rpow_le_rpow (by positivity) hpow (by norm_num)
  have hleft : (((6 : ℝ) / 5) ^ (5 : ℕ)) ^ (1 / 5 : ℝ) = (6 : ℝ) / 5 := by
    rw [← Real.rpow_natCast ((6 : ℝ) / 5) 5, ← Real.rpow_mul hbase]
    norm_num
  rw [hleft] at hmono
  have hposr : (0 : ℝ) < (3 : ℝ) ^ (1 / 5 : ℝ) := three_rpow_pos _
  have hinv : (3 : ℝ) ^ (-(1 / 5 : ℝ)) = ((3 : ℝ) ^ (1 / 5 : ℝ))⁻¹ :=
    Real.rpow_neg (by norm_num) _
  rw [hinv, inv_le_iff_one_le_mul₀ hposr]
  nlinarith [hmono, hposr]

/-- The geometric split of a nonnegative budget over the shells above `n`:
`(1/5) sum_{i = 1}^{N} 3^{-i/5} <= 1`, the arithmetic of `e.Bosc.decomp`. -/
private theorem sum_range_geometric_fifth_le {T : ℝ} (hT : 0 ≤ T) (N : ℕ) :
    ∑ w ∈ Finset.range N,
        (1 / 5 : ℝ) * T * (3 : ℝ) ^ (-(1 / 5 : ℝ) * ((w : ℝ) + 1)) ≤ T := by
  set r : ℝ := (3 : ℝ) ^ (-(1 / 5 : ℝ)) with hr
  have hr0 : 0 < r := three_rpow_neg_fifth_pos
  have hr1 : r < 1 := three_rpow_neg_fifth_lt_one
  have hrle : r ≤ 5 / 6 := three_rpow_neg_fifth_le
  have hterm : ∀ w : ℕ,
      (1 / 5 : ℝ) * T * (3 : ℝ) ^ (-(1 / 5 : ℝ) * ((w : ℝ) + 1)) =
        (1 / 5 : ℝ) * T * (r * r ^ w) := by
    intro w
    have hpow : r ^ w = (3 : ℝ) ^ (-(1 / 5 : ℝ) * (w : ℝ)) := by
      rw [hr, ← Real.rpow_natCast ((3 : ℝ) ^ (-(1 / 5 : ℝ))) w,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    have hmul : r * r ^ w = (3 : ℝ) ^ (-(1 / 5 : ℝ) * ((w : ℝ) + 1)) := by
      rw [hpow, hr, three_rpow_add]
      congr 1
      ring
    rw [hmul]
  have hsum : ∑ w ∈ Finset.range N,
      (1 / 5 : ℝ) * T * (3 : ℝ) ^ (-(1 / 5 : ℝ) * ((w : ℝ) + 1)) =
      (1 / 5 : ℝ) * T * r * ∑ w ∈ Finset.range N, r ^ w := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [hterm w]
    ring
  have hgeom : ∑ w ∈ Finset.range N, r ^ w ≤ (1 - r)⁻¹ := by
    have hsummable : Summable fun w : ℕ => r ^ w :=
      summable_geometric_of_lt_one hr0.le hr1
    have hle := hsummable.sum_le_tsum (Finset.range N) fun w _ => pow_nonneg hr0.le w
    rwa [tsum_geometric_of_lt_one hr0.le hr1] at hle
  have hpos : (0 : ℝ) < 1 - r := by linarith
  have hcoef : (1 / 5 : ℝ) * r * (1 - r)⁻¹ ≤ 1 := by
    rw [mul_inv_le_iff₀ hpos]
    nlinarith [hrle, hr0]
  calc ∑ w ∈ Finset.range N,
        (1 / 5 : ℝ) * T * (3 : ℝ) ^ (-(1 / 5 : ℝ) * ((w : ℝ) + 1))
      = (1 / 5 : ℝ) * T * r * ∑ w ∈ Finset.range N, r ^ w := hsum
    _ ≤ (1 / 5 : ℝ) * T * r * (1 - r)⁻¹ := by
        refine mul_le_mul_of_nonneg_left hgeom ?_
        positivity
    _ = T * ((1 / 5 : ℝ) * r * (1 - r)⁻¹) := by ring
    _ ≤ T * 1 := mul_le_mul_of_nonneg_left hcoef hT
    _ = T := mul_one _

/-- Ascending reindexing of `(n, L]` by an initial block of naturals. -/
private theorem ioc_eq_range_map_asc {n L : ℤ} (hnL : n ≤ L) :
    Finset.Ioc n L =
      (Finset.range (L - n).toNat).map
        ⟨fun w : ℕ => n + 1 + (w : ℤ), by
          intro a b hab
          have hab' : n + 1 + (a : ℤ) = n + 1 + (b : ℤ) := hab
          have hcast : (a : ℤ) = (b : ℤ) := by omega
          exact_mod_cast hcast⟩ := by
  ext k
  simp only [Finset.mem_Ioc, Finset.mem_map, Finset.mem_range]
  constructor
  · rintro ⟨hlo, hhi⟩
    refine ⟨(k - n - 1).toNat, by omega, ?_⟩
    show n + 1 + ((k - n - 1).toNat : ℤ) = k
    have h1 : (0 : ℤ) ≤ k - n - 1 := by omega
    rw [Int.toNat_of_nonneg h1]
    omega
  · rintro ⟨w, hw, rfl⟩
    show n < n + 1 + (w : ℤ) ∧ n + 1 + (w : ℤ) ≤ L
    have h2 : (0 : ℤ) ≤ L - n := by omega
    have hw' : (w : ℤ) < ((L - n).toNat : ℤ) := by exact_mod_cast hw
    rw [Int.toNat_of_nonneg h2] at hw'
    omega

private theorem three_mul_succ_le_three_pow (w : ℕ) : 3 * (w + 1) ≤ 3 ^ (w + 1) := by
  induction w with
  | zero => norm_num
  | succ k ih =>
      have h3 : (3 : ℕ) ^ (k + 1 + 1) = 3 * 3 ^ (k + 1) := by ring
      omega

private theorem exp_pow_eq (x : ℝ) (w : ℕ) :
    Real.exp x ^ w = Real.exp ((w : ℝ) * x) := by
  induction w with
  | zero => simp
  | succ k ih =>
      have hcast : ((k + 1 : ℕ) : ℝ) * x = (k : ℝ) * x + x := by push_cast; ring
      rw [pow_succ, ih, hcast, Real.exp_add]

private theorem two_le_exp_one : (2 : ℝ) ≤ Real.exp 1 := by
  linarith [Real.add_one_le_exp (1 : ℝ)]

/-- The geometric summation `sum_{i >= 1} exp(-3 kappa)^i <= exp(-kappa)` for
`kappa >= 1`. -/
private theorem tsum_exp_pow_le {kappa : ℝ} (hk : 1 ≤ kappa) :
    ∑' w : ℕ, Real.exp (-(3 * kappa)) ^ (w + 1) ≤ Real.exp (-kappa) := by
  have ha0 : (0 : ℝ) < Real.exp (-kappa) := Real.exp_pos _
  have hahalf : Real.exp (-kappa) ≤ 1 / 2 := by
    have h1 : Real.exp 1 ≤ Real.exp kappa := Real.exp_le_exp.2 hk
    have h2 : (2 : ℝ) ≤ Real.exp kappa := le_trans two_le_exp_one h1
    rw [Real.exp_neg, inv_le_iff_one_le_mul₀ (Real.exp_pos kappa)]
    linarith
  have hcube : Real.exp (-(3 * kappa)) = Real.exp (-kappa) ^ 3 := by
    rw [exp_pow_eq]
    congr 1
    push_cast
    ring
  have hq0 : (0 : ℝ) ≤ Real.exp (-(3 * kappa)) := (Real.exp_pos _).le
  have hq1 : Real.exp (-(3 * kappa)) < 1 := by
    have hlt : Real.exp (-(3 * kappa)) < Real.exp 0 := Real.exp_lt_exp.2 (by linarith)
    simpa using hlt
  have hsum : ∑' w : ℕ, Real.exp (-(3 * kappa)) ^ (w + 1) =
      (1 - Real.exp (-(3 * kappa)))⁻¹ * Real.exp (-(3 * kappa)) := by
    have hpow : ∀ w : ℕ, Real.exp (-(3 * kappa)) ^ (w + 1) =
        Real.exp (-(3 * kappa)) ^ w * Real.exp (-(3 * kappa)) := fun w => pow_succ _ w
    rw [tsum_congr hpow, tsum_mul_right, tsum_geometric_of_lt_one hq0 hq1]
  have hden : (0 : ℝ) < 1 - Real.exp (-kappa) ^ 3 := by
    rw [hcube] at hq1
    linarith
  have ha2 : Real.exp (-kappa) ^ 2 ≤ 1 / 4 := by nlinarith [ha0, hahalf]
  have ha3 : Real.exp (-kappa) ^ 3 ≤ 1 / 8 := by nlinarith [ha0, hahalf, ha2]
  rw [hsum, hcube, inv_mul_eq_div, div_le_iff₀ hden]
  nlinarith [ha0, ha2, ha3, mul_le_mul_of_nonneg_left ha2 ha0.le,
    mul_le_mul_of_nonneg_left ha3 ha0.le]

/-- The algebraic core of the per-shell comparison, over abstract reals: with
`pm, pn, pk` the cube, cutoff and shell scales, the exponent of the shell
threshold beats the exponent of the `e.nabla.jk.O` amplitude by at most one. -/
private theorem oscillation_exponent_le {gamma pm pn pk : ℝ} (hgq : gamma ≤ 1 / 4)
    (hnk : pn + 1 ≤ pk) :
    (1 / 2 : ℝ) * (pn - pm) + (1 / 2 : ℝ) * (pk - pn) + pm + (gamma - 1) * pk ≤
      1 + (-(1 / 2 : ℝ) * (pn - pm) + gamma * (pn - 1) +
        -(1 / 5 : ℝ) * (pk - pn)) := by
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ pk - pn - 1)
    (by linarith : (0 : ℝ) ≤ 3 / 10 - gamma)]

/-! ## The geometric split of the event's threshold over shells -/

/-- The share of the `e.good.local.events` threshold allotted to the shell `j_k`
in the decomposition of `l.bad.event.lemma`: the total budget
`C_sens^{-1} (1/2) Ccg^{-1} 3^{-(1/2)(n-m)_+} sigmabar_{n-1}` split with ratio
`3^{-1/5}` and prefactor `1/5`, exactly as `e.Bosc.decomp` splits the
`e.Bosc.def` threshold. -/
def shellSensitivityThreshold (M : ABKModel d) (Ccg : ℝ) (m n k : ℤ) : ℝ :=
  (1 / 5 : ℝ) * ((sensitivityConstMax d)⁻¹ * goodLocalThreshold M Ccg m n) *
    (3 : ℝ) ^ (-(1 / 5 : ℝ) * ((k : ℝ) - (n : ℝ)))

/-- The shell `j_k` exceeds its share of the `e.good.local.events` threshold.
This is the manuscript's `B_{osc,k}`, stated at the event's own threshold rather
than at its `sigmabar_{n-1}` relaxation. -/
def shellSensitivityFailure (M : ABKModel d) (Ccg : ℝ) (Q : TriadicCube d)
    (n k : ℤ) : Set (CutoffSample d) :=
  {omega | shellSensitivityThreshold M Ccg Q.scale n k < shellOscGauge Q k omega}

/-- The partial sums of the shell shares stay below the total budget. -/
theorem sum_range_shellSensitivityThreshold_le (M : ABKModel d) {Ccg : ℝ}
    (hCcg : 0 < Ccg) (m n : ℤ) (N : ℕ) :
    ∑ w ∈ Finset.range N,
        shellSensitivityThreshold M Ccg m n (n + 1 + (w : ℤ)) ≤
      (sensitivityConstMax d)⁻¹ * goodLocalThreshold M Ccg m n := by
  have hT : (0 : ℝ) ≤ (sensitivityConstMax d)⁻¹ * goodLocalThreshold M Ccg m n :=
    mul_nonneg (inv_nonneg.2 (sensitivityConstMax_pos d).le)
      (goodLocalThreshold_pos M hCcg m n).le
  refine le_trans (le_of_eq ?_) (sum_range_geometric_fifth_le hT N)
  refine Finset.sum_congr rfl fun w _ => ?_
  have hcast : (((n + 1 + (w : ℤ) : ℤ) : ℝ) - (n : ℝ)) = (w : ℝ) + 1 := by
    push_cast
    ring
  rw [shellSensitivityThreshold, hcast]

/-- **The shell decomposition of the sensitivity failure** (ABK26, on the branch
`m <= n` where the wave term of vanishes): if every shell above `n` respects its
share of the threshold, then so does the whole increment `k_L - k_n`, for every
`L >= n`. -/
theorem goodLocalSensitivityFailure_subset_iUnion (M : ABKModel d) {Ccg : ℝ}
    (hCcg : 0 < Ccg) (Q : TriadicCube d) (n : ℤ) :
    goodLocalSensitivityFailure M Ccg Q n ⊆
      ⋃ w : ℕ, shellSensitivityFailure M Ccg Q n (n + 1 + (w : ℤ)) := by
  intro omega homega
  by_contra hcon
  have hshell : ∀ w : ℕ,
      shellOscGauge Q (n + 1 + (w : ℤ)) omega ≤
        shellSensitivityThreshold M Ccg Q.scale n (n + 1 + (w : ℤ)) := by
    intro w
    by_contra hlt
    exact hcon (Set.mem_iUnion.2 ⟨w, not_le.1 hlt⟩)
  obtain ⟨L, hL, hLmem⟩ := Set.mem_iUnion₂.1 homega
  have hC : (0 : ℝ) < sensitivityConstMax d := sensitivityConstMax_pos d
  have hsum : ∑ k ∈ Finset.Ioc n L, shellOscGauge Q k omega ≤
      (sensitivityConstMax d)⁻¹ * goodLocalThreshold M Ccg Q.scale n := by
    rw [ioc_eq_range_map_asc hL, Finset.sum_map]
    refine le_trans (Finset.sum_le_sum fun w _ => hshell w) ?_
    exact sum_range_shellSensitivityThreshold_le M hCcg Q.scale n (L - n).toNat
  have hgauge : sensitivityConstMax d * incrementOscGauge₂ Q n L omega ≤
      goodLocalThreshold M Ccg Q.scale n := by
    have hstep := (incrementOscGauge₂_le_sum_shellOscGauge Q n L omega).trans hsum
    calc sensitivityConstMax d * incrementOscGauge₂ Q n L omega
        ≤ sensitivityConstMax d *
            ((sensitivityConstMax d)⁻¹ * goodLocalThreshold M Ccg Q.scale n) :=
          mul_le_mul_of_nonneg_left hstep hC.le
      _ = goodLocalThreshold M Ccg Q.scale n := by
          rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hC), one_mul]
  exact absurd hLmem (not_lt.2 hgauge)

/-! ## The constant and the exponent of `e.oscillation.bound` -/

/-- The local choice of the manuscript's `c` in `e.oscillation.bound`:
`(1/3600) C_sens(d)^{-2} Ccg^{-2}`, where `Ccg` carries
`C_{(e.cg.ellip.lower)}`. -/
def badEventOscConst (d : ℕ) (Ccg : ℝ) : ℝ :=
  (1 / 3600 : ℝ) * ((sensitivityConstMax d)⁻¹) ^ 2 * (Ccg⁻¹) ^ 2

/-- The exponent of `e.oscillation.bound` on the branch `m <= n`:
`c c_star gamma^{-1} 3^{(n-m)_+}`. -/
def badEventOscRate (M : ABKModel d) (Ccg : ℝ) (Q : TriadicCube d) (n : ℤ) : ℝ :=
  badEventOscConst d Ccg * Algsuperdiff.Section3.Disorder.cstar M * M.gamma⁻¹ *
    (3 : ℝ) ^ scaleGapPos Q.scale n

/-! ## Abstract endgames

Both probabilistic endgames are stated over abstract reals so that no
arithmetic tactic ever meets a power of three or an exponential. -/

private theorem one_le_mul_one_le {a b : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    1 ≤ a * b := by nlinarith

private theorem one_le_of_one_le_sq {B : ℝ} (hB : 0 < B) (h : 1 ≤ B ^ 2) :
    1 ≤ B := by nlinarith

/-- The weak-Orlicz tail, read at the threshold-to-amplitude ratio: if the
threshold dominates `B` times the amplitude and `B^2` is the claimed rate, then
the upper-tail event at the threshold has probability at most `exp(-rate)`. -/
private theorem measureReal_upperTail_le_exp {Omega : Type*}
    [MeasurableSpace Omega] {mu : Measure Omega} {X : Omega → ℝ}
    {A B thr rate : ℝ} (hA : 0 < A) (hB : 0 < B) (hBA : B * A ≤ thr)
    (hBsq : B ^ 2 = rate) (hrate : 1 ≤ rate)
    (htail : HCPolySupport.IndependentSums.IsBigOWith mu
      (HCPolySupport.IndependentSums.gammaSigma 2) X A) :
    mu.real {omega | thr < X omega} ≤ Real.exp (-rate) := by
  have hB1 : 1 ≤ B := one_le_of_one_le_sq hB (by rw [hBsq]; exact hrate)
  have hBt : B ≤ thr / A := (le_div_iff₀ hA).2 hBA
  have ht1 : (1 : ℝ) ≤ thr / A := le_trans hB1 hBt
  have h := htail ht1
  have hAt : A * (thr / A) = thr := by
    field_simp
  rw [hAt] at h
  refine le_trans h ?_
  rw [HCPolySupport.IndependentSums.gammaSigma_inv]
  refine Real.exp_le_exp.2 (neg_le_neg ?_)
  have htt : (thr / A) ^ (2 : ℝ) = (thr / A) ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast (thr / A) 2]
    norm_num
  rw [htt, ← hBsq]
  nlinarith [hBt, hB]

/-- The geometric union bound: a set covered by events whose probabilities decay
like `exp(-kappa 3^{i})` has probability at most `exp(-kappa)`, for `kappa >= 1`. -/
private theorem measureReal_le_exp_of_iUnion {Omega : Type*}
    [MeasurableSpace Omega] (mu : Measure Omega) [IsFiniteMeasure mu]
    {S : Set Omega} {T : ℕ → Set Omega} {kappa : ℝ} (hk : 1 ≤ kappa)
    (hsub : S ⊆ ⋃ w : ℕ, T w)
    (hterm : ∀ w : ℕ,
      mu.real (T w) ≤ Real.exp (-(kappa * (3 : ℝ) ^ ((w : ℝ) + 1)))) :
    mu.real S ≤ Real.exp (-kappa) := by
  classical
  have hk0 : (0 : ℝ) < kappa := lt_of_lt_of_le zero_lt_one hk
  have hgeom : ∀ w : ℕ,
      mu.real (T w) ≤ Real.exp (-(3 * kappa)) ^ (w + 1) := by
    intro w
    refine le_trans (hterm w) ?_
    rw [exp_pow_eq]
    refine Real.exp_le_exp.2 ?_
    have hN : (3 * (w + 1) : ℕ) ≤ 3 ^ (w + 1) := three_mul_succ_le_three_pow w
    have hR : ((3 * (w + 1) : ℕ) : ℝ) ≤ ((3 ^ (w + 1) : ℕ) : ℝ) := by
      exact_mod_cast hN
    have hid : (3 : ℝ) ^ ((w : ℝ) + 1) = (3 : ℝ) ^ (w + 1 : ℕ) := by
      rw [show ((w : ℝ) + 1) = ((w + 1 : ℕ) : ℝ) by push_cast; ring,
        Real.rpow_natCast]
    have hpow : (3 : ℝ) * ((w : ℝ) + 1) ≤ (3 : ℝ) ^ ((w : ℝ) + 1) := by
      rw [hid]
      push_cast at hR
      linarith
    have hmul : 3 * kappa * ((w : ℝ) + 1) ≤ kappa * (3 : ℝ) ^ ((w : ℝ) + 1) := by
      calc 3 * kappa * ((w : ℝ) + 1) = kappa * (3 * ((w : ℝ) + 1)) := by ring
        _ ≤ kappa * (3 : ℝ) ^ ((w : ℝ) + 1) :=
            mul_le_mul_of_nonneg_left hpow hk0.le
    push_cast
    linarith
  have hsummable : Summable fun w : ℕ => Real.exp (-(3 * kappa)) ^ (w + 1) := by
    have hq1 : Real.exp (-(3 * kappa)) < 1 := by
      have hlt : Real.exp (-(3 * kappa)) < Real.exp 0 :=
        Real.exp_lt_exp.2 (by linarith)
      simpa using hlt
    exact ((summable_geometric_of_lt_one (Real.exp_pos _).le hq1).mul_right _).congr
      fun w => (pow_succ _ w).symm
  have hbound : mu S ≤
      ENNReal.ofReal (∑' w : ℕ, Real.exp (-(3 * kappa)) ^ (w + 1)) := by
    rw [ENNReal.ofReal_tsum_of_nonneg
      (fun w => pow_nonneg (Real.exp_pos _).le _) hsummable]
    refine le_trans (measure_mono hsub) ?_
    refine le_trans (measure_iUnion_le _) (ENNReal.tsum_le_tsum fun w => ?_)
    have hfin : mu (T w) ≠ ⊤ := measure_ne_top _ _
    rw [← ENNReal.ofReal_toReal hfin]
    exact ENNReal.ofReal_le_ofReal (hgeom w)
  calc mu.real S = (mu S).toReal := rfl
    _ ≤ (ENNReal.ofReal (∑' w : ℕ, Real.exp (-(3 * kappa)) ^ (w + 1))).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
    _ = ∑' w : ℕ, Real.exp (-(3 * kappa)) ^ (w + 1) :=
        ENNReal.toReal_ofReal
          (tsum_nonneg fun w => pow_nonneg (Real.exp_pos _).le _)
    _ ≤ Real.exp (-kappa) := tsum_exp_pow_le hk

/-! ## The per-shell probability bound -/

/-- **One shell of the oscillation branch.**  For a shell `k > n` at or above
the cube scale, the probability that `j_k` exceeds its share of the
`e.good.local.events` threshold is at most `exp(- rate 3^{k-n})`, where `rate`
is the exponent of `e.oscillation.bound`.

The input is the proved translated `e.nabla.jk.O` tail
`isBigOWith_gammaSigma_shellOscGauge`; the induction state enters only through
the lower bound `c_star^{1/2} gamma^{-1/2} 3^{gamma (n-1)} <= 2 sigmabar_{n-1}`
of `e.shom.h.bounds`, which is the manuscript's own relaxation of the
`e.good.local.events` threshold. -/
theorem measureReal_shellSensitivityFailure_le (M : ABKModel d) {Ccg : ℝ}
    (hCcg : 0 < Ccg) (Q : TriadicCube d) {n k m0 : ℤ} {E : {E : ℝ // 1 ≤ E}}
    (hS : Algsuperdiff.Frozen.Section3.inductionState M (m0 - 1) E)
    (hn : n ≤ m0 - 1) (hmn : Q.scale ≤ n) (hnk : n < k)
    (hgate : 1 ≤ badEventOscRate M Ccg Q n) :
    (cutoffSampleLaw M).toMeasure.real (shellSensitivityFailure M Ccg Q n k) ≤
      Real.exp (-(badEventOscRate M Ccg Q n * (3 : ℝ) ^ ((k : ℝ) - (n : ℝ)))) := by
  have hC : (0 : ℝ) < sensitivityConstMax d := sensitivityConstMax_pos d
  have hc : (0 : ℝ) < Algsuperdiff.Section3.Disorder.cstar M :=
    (Algsuperdiff.Section3.Disorder.cstar_characterization M).1
  have hg : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hgq : M.gamma ≤ 1 / 4 := M.shellPrefix.gamma_le_quarter
  have hnkR : (n : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast hnk
  have hpgap : scaleGapPos Q.scale n = (n : ℝ) - (Q.scale : ℝ) :=
    scaleGapPos_of_le hmn
  have hsqc : (0 : ℝ) < Real.sqrt (Algsuperdiff.Section3.Disorder.cstar M) :=
    Real.sqrt_pos.2 hc
  have hsqg : (0 : ℝ) < (Real.sqrt M.gamma)⁻¹ := inv_pos.2 (Real.sqrt_pos.2 hg)
  -- the amplitude of `e.nabla.jk.O` at the cube, and the square root of the rate
  have hApos : (0 : ℝ) <
      (3 : ℝ) ^ (Q.scale : ℝ) * (3 : ℝ) ^ ((M.gamma - 1) * (k : ℝ)) :=
    mul_pos (three_rpow_pos _) (three_rpow_pos _)
  have hBpos : (0 : ℝ) < (1 / 60 : ℝ) *
      ((sensitivityConstMax d)⁻¹ * Ccg⁻¹ *
        Real.sqrt (Algsuperdiff.Section3.Disorder.cstar M) *
        (Real.sqrt M.gamma)⁻¹) *
      (3 : ℝ) ^ ((1 / 2 : ℝ) * scaleGapPos Q.scale n) *
      (3 : ℝ) ^ ((1 / 2 : ℝ) * ((k : ℝ) - (n : ℝ))) := by
    have h1 := three_rpow_pos ((1 / 2 : ℝ) * scaleGapPos Q.scale n)
    have h2 := three_rpow_pos ((1 / 2 : ℝ) * ((k : ℝ) - (n : ℝ)))
    positivity
  -- the square of `B` is the displayed rate at this shell
  have hBsq : ((1 / 60 : ℝ) *
      ((sensitivityConstMax d)⁻¹ * Ccg⁻¹ *
        Real.sqrt (Algsuperdiff.Section3.Disorder.cstar M) *
        (Real.sqrt M.gamma)⁻¹) *
      (3 : ℝ) ^ ((1 / 2 : ℝ) * scaleGapPos Q.scale n) *
      (3 : ℝ) ^ ((1 / 2 : ℝ) * ((k : ℝ) - (n : ℝ)))) ^ 2 =
      badEventOscRate M Ccg Q n * (3 : ℝ) ^ ((k : ℝ) - (n : ℝ)) := by
    have hcs : Real.sqrt (Algsuperdiff.Section3.Disorder.cstar M) ^ 2 =
        Algsuperdiff.Section3.Disorder.cstar M := Real.sq_sqrt hc.le
    have hgs : Real.sqrt M.gamma ^ 2 = M.gamma := Real.sq_sqrt hg.le
    have hexpand : ((1 / 60 : ℝ) *
        ((sensitivityConstMax d)⁻¹ * Ccg⁻¹ *
          Real.sqrt (Algsuperdiff.Section3.Disorder.cstar M) *
          (Real.sqrt M.gamma)⁻¹) *
        (3 : ℝ) ^ ((1 / 2 : ℝ) * scaleGapPos Q.scale n) *
        (3 : ℝ) ^ ((1 / 2 : ℝ) * ((k : ℝ) - (n : ℝ)))) ^ 2 =
        (1 / 3600 : ℝ) * ((sensitivityConstMax d)⁻¹) ^ 2 * (Ccg⁻¹) ^ 2 *
          (Real.sqrt (Algsuperdiff.Section3.Disorder.cstar M) ^ 2) *
          ((Real.sqrt M.gamma) ^ 2)⁻¹ *
          (((3 : ℝ) ^ ((1 / 2 : ℝ) * scaleGapPos Q.scale n)) ^ 2) *
          (((3 : ℝ) ^ ((1 / 2 : ℝ) * ((k : ℝ) - (n : ℝ)))) ^ 2) := by
      rw [← inv_pow]
      ring
    rw [hexpand, hcs, hgs, three_rpow_half_sq, three_rpow_half_sq,
      badEventOscRate, badEventOscConst]
  -- the shell threshold dominates `B` times the amplitude
  have hthr : (1 / 60 : ℝ) *
      ((sensitivityConstMax d)⁻¹ * Ccg⁻¹ *
        Real.sqrt (Algsuperdiff.Section3.Disorder.cstar M) *
        (Real.sqrt M.gamma)⁻¹) *
      (3 : ℝ) ^ ((1 / 2 : ℝ) * scaleGapPos Q.scale n) *
      (3 : ℝ) ^ ((1 / 2 : ℝ) * ((k : ℝ) - (n : ℝ))) *
      ((3 : ℝ) ^ (Q.scale : ℝ) * (3 : ℝ) ^ ((M.gamma - 1) * (k : ℝ))) ≤
      shellSensitivityThreshold M Ccg Q.scale n k := by
    have hsigma := sqrt_cstar_mul_inv_sqrt_gamma_mul_rpow_le_two_mul_sigmaBar M hS
      (m := n - 1) (by omega)
    have hcast : (((n - 1 : ℤ) : ℝ)) = (n : ℝ) - 1 := by push_cast; ring
    rw [hcast] at hsigma
    have hfacpos : (0 : ℝ) ≤ (1 / 20 : ℝ) * ((sensitivityConstMax d)⁻¹ * Ccg⁻¹) *
        ((3 : ℝ) ^ (-(1 / 2 : ℝ) * scaleGapPos Q.scale n) *
          (3 : ℝ) ^ (-(1 / 5 : ℝ) * ((k : ℝ) - (n : ℝ)))) := by
      have h1 := three_rpow_pos (-(1 / 2 : ℝ) * scaleGapPos Q.scale n)
      have h2 := three_rpow_pos (-(1 / 5 : ℝ) * ((k : ℝ) - (n : ℝ)))
      have h3 : (0 : ℝ) < (sensitivityConstMax d)⁻¹ * Ccg⁻¹ := by positivity
      positivity
    -- the induction-state relaxation of the threshold
    have hlow : (1 / 20 : ℝ) *
        ((sensitivityConstMax d)⁻¹ * Ccg⁻¹ *
          Real.sqrt (Algsuperdiff.Section3.Disorder.cstar M) *
          (Real.sqrt M.gamma)⁻¹) *
        ((3 : ℝ) ^ (-(1 / 2 : ℝ) * scaleGapPos Q.scale n) *
          ((3 : ℝ) ^ (M.gamma * ((n : ℝ) - 1)) *
            (3 : ℝ) ^ (-(1 / 5 : ℝ) * ((k : ℝ) - (n : ℝ))))) ≤
        shellSensitivityThreshold M Ccg Q.scale n k := by
      rw [shellSensitivityThreshold, goodLocalThreshold]
      calc (1 / 20 : ℝ) *
            ((sensitivityConstMax d)⁻¹ * Ccg⁻¹ *
              Real.sqrt (Algsuperdiff.Section3.Disorder.cstar M) *
              (Real.sqrt M.gamma)⁻¹) *
            ((3 : ℝ) ^ (-(1 / 2 : ℝ) * scaleGapPos Q.scale n) *
              ((3 : ℝ) ^ (M.gamma * ((n : ℝ) - 1)) *
                (3 : ℝ) ^ (-(1 / 5 : ℝ) * ((k : ℝ) - (n : ℝ)))))
          = (1 / 20 : ℝ) * ((sensitivityConstMax d)⁻¹ * Ccg⁻¹) *
              ((3 : ℝ) ^ (-(1 / 2 : ℝ) * scaleGapPos Q.scale n) *
                (3 : ℝ) ^ (-(1 / 5 : ℝ) * ((k : ℝ) - (n : ℝ)))) *
              (Real.sqrt (Algsuperdiff.Section3.Disorder.cstar M) *
                (Real.sqrt M.gamma)⁻¹ *
                (3 : ℝ) ^ (M.gamma * ((n : ℝ) - 1))) := by ring
        _ ≤ (1 / 20 : ℝ) * ((sensitivityConstMax d)⁻¹ * Ccg⁻¹) *
              ((3 : ℝ) ^ (-(1 / 2 : ℝ) * scaleGapPos Q.scale n) *
                (3 : ℝ) ^ (-(1 / 5 : ℝ) * ((k : ℝ) - (n : ℝ)))) *
              (2 * (Algsuperdiff.Section3.Annealed.sigmaBar M (n - 1) : ℝ)) :=
            mul_le_mul_of_nonneg_left hsigma hfacpos
        _ = (1 / 5 : ℝ) *
              ((sensitivityConstMax d)⁻¹ *
                ((1 / 2 : ℝ) * Ccg⁻¹ *
                  (3 : ℝ) ^ (-(1 / 2 : ℝ) * scaleGapPos Q.scale n) *
                  ((Algsuperdiff.Section3.Annealed.sigmaBar M (n - 1) : ℝ)))) *
              (3 : ℝ) ^ (-(1 / 5 : ℝ) * ((k : ℝ) - (n : ℝ))) := by ring
    refine le_trans ?_ hlow
    · -- compare the two exponents
      have hcollect : ∀ x y z : ℝ,
          (3 : ℝ) ^ x * (3 : ℝ) ^ y * (3 : ℝ) ^ z = (3 : ℝ) ^ (x + y + z) := by
        intro x y z
        rw [three_rpow_add, three_rpow_add]
      have hleft : (1 / 60 : ℝ) *
          ((sensitivityConstMax d)⁻¹ * Ccg⁻¹ *
            Real.sqrt (Algsuperdiff.Section3.Disorder.cstar M) *
            (Real.sqrt M.gamma)⁻¹) *
          (3 : ℝ) ^ ((1 / 2 : ℝ) * scaleGapPos Q.scale n) *
          (3 : ℝ) ^ ((1 / 2 : ℝ) * ((k : ℝ) - (n : ℝ))) *
          ((3 : ℝ) ^ (Q.scale : ℝ) * (3 : ℝ) ^ ((M.gamma - 1) * (k : ℝ))) =
          (1 / 60 : ℝ) *
            ((sensitivityConstMax d)⁻¹ * Ccg⁻¹ *
              Real.sqrt (Algsuperdiff.Section3.Disorder.cstar M) *
              (Real.sqrt M.gamma)⁻¹) *
            ((3 : ℝ) ^ ((1 / 2 : ℝ) * scaleGapPos Q.scale n +
              (1 / 2 : ℝ) * ((k : ℝ) - (n : ℝ)) + (Q.scale : ℝ)) *
              (3 : ℝ) ^ ((M.gamma - 1) * (k : ℝ))) := by
        rw [← hcollect]
        ring
      have hright : (1 / 20 : ℝ) *
          ((sensitivityConstMax d)⁻¹ * Ccg⁻¹ *
            Real.sqrt (Algsuperdiff.Section3.Disorder.cstar M) *
            (Real.sqrt M.gamma)⁻¹) *
          ((3 : ℝ) ^ (-(1 / 2 : ℝ) * scaleGapPos Q.scale n) *
            ((3 : ℝ) ^ (M.gamma * ((n : ℝ) - 1)) *
              (3 : ℝ) ^ (-(1 / 5 : ℝ) * ((k : ℝ) - (n : ℝ))))) =
          (1 / 20 : ℝ) *
            ((sensitivityConstMax d)⁻¹ * Ccg⁻¹ *
              Real.sqrt (Algsuperdiff.Section3.Disorder.cstar M) *
              (Real.sqrt M.gamma)⁻¹) *
            (3 : ℝ) ^ (-(1 / 2 : ℝ) * scaleGapPos Q.scale n +
              M.gamma * ((n : ℝ) - 1) +
              -(1 / 5 : ℝ) * ((k : ℝ) - (n : ℝ))) := by
        rw [← hcollect]
        ring
      rw [hleft, hright, three_rpow_add]
      have hexpineq : (1 / 2 : ℝ) * scaleGapPos Q.scale n +
            (1 / 2 : ℝ) * ((k : ℝ) - (n : ℝ)) + (Q.scale : ℝ) +
            (M.gamma - 1) * (k : ℝ) ≤
          1 + (-(1 / 2 : ℝ) * scaleGapPos Q.scale n +
            M.gamma * ((n : ℝ) - 1) + -(1 / 5 : ℝ) * ((k : ℝ) - (n : ℝ))) := by
        rw [hpgap]
        exact oscillation_exponent_le hgq hnkR
      have hstep : (3 : ℝ) ^ ((1 / 2 : ℝ) * scaleGapPos Q.scale n +
            (1 / 2 : ℝ) * ((k : ℝ) - (n : ℝ)) + (Q.scale : ℝ) +
            (M.gamma - 1) * (k : ℝ)) ≤
          3 * (3 : ℝ) ^ (-(1 / 2 : ℝ) * scaleGapPos Q.scale n +
            M.gamma * ((n : ℝ) - 1) + -(1 / 5 : ℝ) * ((k : ℝ) - (n : ℝ))) := by
        have hmerge : (3 : ℝ) * (3 : ℝ) ^ (-(1 / 2 : ℝ) * scaleGapPos Q.scale n +
            M.gamma * ((n : ℝ) - 1) + -(1 / 5 : ℝ) * ((k : ℝ) - (n : ℝ))) =
            (3 : ℝ) ^ (1 + (-(1 / 2 : ℝ) * scaleGapPos Q.scale n +
              M.gamma * ((n : ℝ) - 1) +
              -(1 / 5 : ℝ) * ((k : ℝ) - (n : ℝ)))) := by
          have hone := three_rpow_add (1 : ℝ)
            (-(1 / 2 : ℝ) * scaleGapPos Q.scale n + M.gamma * ((n : ℝ) - 1) +
              -(1 / 5 : ℝ) * ((k : ℝ) - (n : ℝ)))
          rwa [Real.rpow_one] at hone
        rw [hmerge]
        exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hexpineq
      have hknn : (0 : ℝ) ≤ (1 / 60 : ℝ) *
          ((sensitivityConstMax d)⁻¹ * Ccg⁻¹ *
            Real.sqrt (Algsuperdiff.Section3.Disorder.cstar M) *
            (Real.sqrt M.gamma)⁻¹) := by positivity
      calc (1 / 60 : ℝ) *
            ((sensitivityConstMax d)⁻¹ * Ccg⁻¹ *
              Real.sqrt (Algsuperdiff.Section3.Disorder.cstar M) *
              (Real.sqrt M.gamma)⁻¹) *
            (3 : ℝ) ^ ((1 / 2 : ℝ) * scaleGapPos Q.scale n +
              (1 / 2 : ℝ) * ((k : ℝ) - (n : ℝ)) + (Q.scale : ℝ) +
              (M.gamma - 1) * (k : ℝ))
          ≤ (1 / 60 : ℝ) *
            ((sensitivityConstMax d)⁻¹ * Ccg⁻¹ *
              Real.sqrt (Algsuperdiff.Section3.Disorder.cstar M) *
              (Real.sqrt M.gamma)⁻¹) *
            (3 * (3 : ℝ) ^ (-(1 / 2 : ℝ) * scaleGapPos Q.scale n +
              M.gamma * ((n : ℝ) - 1) +
              -(1 / 5 : ℝ) * ((k : ℝ) - (n : ℝ)))) :=
            mul_le_mul_of_nonneg_left hstep hknn
        _ = (1 / 20 : ℝ) *
            ((sensitivityConstMax d)⁻¹ * Ccg⁻¹ *
              Real.sqrt (Algsuperdiff.Section3.Disorder.cstar M) *
              (Real.sqrt M.gamma)⁻¹) *
            (3 : ℝ) ^ (-(1 / 2 : ℝ) * scaleGapPos Q.scale n +
              M.gamma * ((n : ℝ) - 1) +
              -(1 / 5 : ℝ) * ((k : ℝ) - (n : ℝ))) := by ring
  -- the rate at this shell is at least one
  have hrate3 : (1 : ℝ) ≤
      badEventOscRate M Ccg Q n * (3 : ℝ) ^ ((k : ℝ) - (n : ℝ)) :=
    one_le_mul_one_le hgate (Real.one_le_rpow (by norm_num) (by linarith))
  have htail := isBigOWith_gammaSigma_shellOscGauge M Q (le_trans hmn hnk.le)
  show (cutoffSampleLaw M).toMeasure.real
      {omega | shellSensitivityThreshold M Ccg Q.scale n k <
        shellOscGauge Q k omega} ≤ _
  exact measureReal_upperTail_le_exp hApos hBpos hthr hBsq hrate3 htail

/-! ## The oscillation branch of `l.bad.event.lemma` -/

/-- **The oscillation branch of `l.bad.event.lemma`** (ABK26,
`e.oscillation.bound`), on the branch `m <= n` where `(m-n)_+ = 0`:

```
P[ sensitivity clause of Q(m,n,z) fails ]
  <= exp( - c c_star gamma^{-1} 3^{(n-m)_+} ) ,
```

with `c = badEventOscConst d Ccg`.  The gate `hgate` is the threshold-to-
amplitude condition of the weak-Orlicz tail, discharged from the manuscript's
own admissibility by `measureReal_goodLocalSensitivityFailure_le_of_admissible`
below. -/
theorem measureReal_goodLocalSensitivityFailure_le (M : ABKModel d) {Ccg : ℝ}
    (hCcg : 0 < Ccg) (Q : TriadicCube d) {n m0 : ℤ} {E : {E : ℝ // 1 ≤ E}}
    (hS : Algsuperdiff.Frozen.Section3.inductionState M (m0 - 1) E)
    (hn : n ≤ m0 - 1) (hmn : Q.scale ≤ n)
    (hgate : 1 ≤ badEventOscRate M Ccg Q n) :
    (cutoffSampleLaw M).toMeasure.real (goodLocalSensitivityFailure M Ccg Q n) ≤
      Real.exp (-(badEventOscRate M Ccg Q n)) := by
  refine measureReal_le_exp_of_iUnion _ hgate
    (goodLocalSensitivityFailure_subset_iUnion M hCcg Q n) fun w => ?_
  have hle := measureReal_shellSensitivityFailure_le M hCcg Q hS hn hmn
    (k := n + 1 + (w : ℤ)) (by omega) hgate
  have hcast : (((n + 1 + (w : ℤ) : ℤ) : ℝ) - (n : ℝ)) = (w : ℝ) + 1 := by
    push_cast
    ring
  rwa [hcast] at hle

/-! ## Discharging the gate from the printed admissibility -/

/-- The dimension-only constant at which the manuscript's admissibility display
`e.bad.event.admissibility` (`c^{-1} c_star^{-1} <= E <= gamma^{-1/5}`)
discharges the gate of `measureReal_goodLocalSensitivityFailure_le`.  As in
`GoodLocalEllipticity.lean`, `Ccg` carries the still-parametrized
`C_{(e.cg.ellip.lower)}`. -/
def badEventOscAdmissibleConst (d : ℕ) (Ccg : ℝ) : ℝ :=
  max 3 (3600 * (sensitivityConstMax d) ^ 2 * Ccg ^ 2)

end

end Algsuperdiff.Section3.Provider.BadEvents
