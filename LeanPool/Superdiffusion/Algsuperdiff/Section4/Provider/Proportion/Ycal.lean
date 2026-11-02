/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Proportion.AtomTail
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Proportion.LatticeCount

/-!
# Ycal

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The `𝒢₀` score field `𝒴_n` and its `Γ_{1/3}` tail

ABK26, §4.1, steps
`l.good.scales.ratio.lambda`, the per-annulus atom tail, display (b), and
the `𝒴` tail:

```
max_{z ∈ 3^{k−2}ℤ^d ∩ (□_n∖□_{n−1})} (σ_{k−3}λ_{γ,2}^{-1}(z+□_{k−2};𝐚_{k−2}) − C_cg)_+
  ≤ 𝒪_{Γ_{1/3}} ( C(n−k+1)³ exp(−C^{−1}c⋆²γ^{−1}) ) ,

𝒴_n := γ^{-4} Σ_{k ≤ n} 3^{−¼γ(n−k)} (that maximum)
     ≤ 𝒪_{Γ_{1/3}} ( exp(−C^{−1}c⋆²γ^{−1}) ) .
```

Both are assembled here from three proved pieces: the per-atom tail
(`AtomTail.isBigOWith_cgExcess_of_state`), the union bound
(`SeriesTail.isBigOWith_fmax`) with the machine-computed lattice count
(`LatticeCount`), and the countable generalized triangle inequality
(`SeriesTail.isBigOWith_wsum`).

## Deviations from the printed display

* The normalization `γ^{-4}` and the weight rate `¼γ` are *free
  parameters* here: `sprime` is the rate, and the normalization is deliberately
  not baked into `Ycal`, because it is a lane prefactor of the downstream
  threshold, not a rescaling of the score field.  The manuscript's instance is
  `sprime = γ/4` and the normalization `γ^{-4} ≍ Σ_j 3^{-¼γ j}(j+3)³`, which is
  the value of the tsum appearing in the tail scale below.  Establishing the
  closed form `≍ γ^{-4}` for that sum is arithmetic, not structure, and is not
  done here.
* The `k`-series is formed in `ℝ≥0∞` (`YcalE`), hence total, and `Ycal`
  is its `.toReal`.  No `a.s.` finiteness is needed before `𝒴_n` may be used,
  and the tail proved below is a statement about the total object.
* The summand reads the field at the inner scale `𝐚_{k−2}`, a
  per-inner-scale truncation; this is the proved `Localize.cgExcess` at index
  `k − 2`, so the convention is the manuscript's.

## References

* ABK26, `l.good.scales.ratio.lambda`.
-/

namespace Algsuperdiff.Section4.Provider.Proportion

open Algsuperdiff.Section3
open HCPolySupport HCPolySupport.IndependentSums MeasureTheory
open Algsuperdiff.Section4.Support
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The per-annulus maximum -/

/-- **The lattice maximum of the `𝒢₀` bracket over the annulus `□_n ∖ □_{n−1}`,
read at spacing `3^{k−2}`**.  `0`-floored, so total. -/
def annMax (M : ABKModel d) (Ccg : ℝ) (n k : ℤ) (omega : Cutoff.CutoffSample d) : ℝ :=
  fmax (latticeAnnulusFinset d (k - 2) n (n - 1))
    (fun v => Localize.cgExcess M Ccg (k - 2) (Support.triadicLatticePoint (k - 2) v) omega)

theorem annMax_nonneg (M : ABKModel d) (Ccg : ℝ) (n k : ℤ)
    (omega : Cutoff.CutoffSample d) : 0 ≤ annMax M Ccg n k omega :=
  fmax_nonneg _ _

/-- The `𝒢₀` bracket at a fixed centre is measurable. -/
theorem measurable_cgExcess (M : ABKModel d) (Ccg : ℝ) (k : ℤ) (z : Vec d) :
    Measurable fun omega => Localize.cgExcess M Ccg (k - 2) z omega := by
  have hrw : (fun omega => Localize.cgExcess M Ccg (k - 2) z omega)
      = fun omega => max ((Annealed.sigmaBar M (k - 3) : ℝ) *
          Support.lambdaAnnulusAtom M k z omega - Ccg) 0 :=
    funext fun omega => Localize.cgExcess_sub_two M Ccg k z omega
  rw [hrw]
  exact (((Support.measurable_lambdaAnnulusAtom M k z).const_mul _).sub_const _).max
    measurable_const

theorem measurable_annMax (M : ABKModel d) (Ccg : ℝ) (n k : ℤ) :
    Measurable (annMax M Ccg n k) :=
  measurable_fmax _ fun _v => measurable_cgExcess M Ccg k _

/-- **`e.maxy.bound` at the `𝒢₀` annulus**.  The per-atom `Γ_σ` tail lifts through
the lattice maximum at the machine-computed penalty `annulusPenalty d σ (n − k
+ 2)`, which at `σ = 1/3` is a cubic in `n − k`: the manuscript's `C(n−k+1)³`. -/
theorem isBigOWith_annMax (M : ABKModel d) (Ccg : ℝ) {A sigma : ℝ}
    (hsigma : 0 < sigma) (hA : 0 ≤ A)
    (hatom : ∀ (k : ℤ) (z : Vec d),
      IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure (gammaSigma sigma)
        (fun omega => Localize.cgExcess M Ccg (k - 2) z omega) A)
    (n k : ℤ) :
    IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure (gammaSigma sigma)
      (annMax M Ccg n k) (annulusPenalty d sigma (n - (k - 2)).toNat * A) :=
  isBigOWith_fmax _ hsigma hA (one_le_annulusPenalty d hsigma _)
    (log_card_le_annulusPenalty_rpow_sub_one d hsigma (k - 2) n (n - 1))
    (fun _v _ => hatom k _)

/-! ## 2. The penalty at the manuscript's index `σ = 1/3`, in closed form -/

/-- The `σ = 1/3` lattice penalty as a natural cube — the manuscript's
`C(n−k+1)³`. -/
def annulusPenaltyThird (d : ℕ) (p : ℕ) : ℝ :=
  (1 + (d : ℝ) * ((p : ℝ) + 1) * Real.log 3) ^ (3 : ℕ)

theorem annulusPenalty_third (d : ℕ) (p : ℕ) :
    annulusPenalty d (1 / 3 : ℝ) p = annulusPenaltyThird d p := by
  rw [annulusPenalty, annulusPenaltyThird]
  rw [show ((1 / 3 : ℝ))⁻¹ = ((3 : ℕ) : ℝ) by norm_num]
  exact Real.rpow_natCast _ 3

theorem annulusPenaltyThird_pos (d : ℕ) (p : ℕ) : 0 < annulusPenaltyThird d p := by
  have hlog : (0 : ℝ) ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hbase : (0 : ℝ) < 1 + (d : ℝ) * ((p : ℝ) + 1) * Real.log 3 := by positivity
  exact pow_pos hbase 3

/-! ## 3. The geometric weight -/

/-- The manuscript's discount `3^{−s'(n−k)}`, written as a geometric power of
`3^{−s'}` in the offset `j = n − k`. -/
def weightThird (sprime : ℝ) (j : ℕ) : ℝ := ((3 : ℝ) ^ (-sprime)) ^ j

theorem weightThird_pos {sprime : ℝ} (j : ℕ) : 0 < weightThird sprime j :=
  pow_pos (Real.rpow_pos_of_pos (by norm_num) _) j

/-- The weight is the printed `3^{−s'(n−k)}` at `j = n − k`. -/
theorem weightThird_eq (sprime : ℝ) (j : ℕ) :
    weightThird sprime j = (3 : ℝ) ^ (-(sprime * (j : ℝ))) := by
  rw [weightThird, ← Real.rpow_natCast ((3 : ℝ) ^ (-sprime)) j,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
  congr 1
  ring

/-! ## 4. Summability of the weighted penalties -/

private theorem summable_cubic_geometric {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable fun j : ℕ => ((j : ℝ) + 1) ^ (3 : ℕ) * r ^ j := by
  have hnorm : ‖r‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg hr0]
  have h3 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 3 hnorm
  have h2 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 2 hnorm
  have h1 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hnorm
  have h0 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 0 hnorm
  have hs := ((h3.add (h2.mul_left 3)).add (h1.mul_left 3)).add h0
  refine hs.congr fun j => ?_
  ring

/-- The annular penalty at a shifted index is bounded by a cubic polynomial. -/
theorem annulusPenaltyThird_le (d : ℕ) (j : ℕ) :
    annulusPenaltyThird d (j + 2)
      ≤ (1 + 3 * (d : ℝ) * Real.log 3) ^ (3 : ℕ) * (((j : ℝ) + 1) ^ (3 : ℕ)) := by
  have hlog : (0 : ℝ) ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hbase : 1 + (d : ℝ) * (((j + 2 : ℕ) : ℝ) + 1) * Real.log 3
      ≤ (1 + 3 * (d : ℝ) * Real.log 3) * ((j : ℝ) + 1) := by
    have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    have hcast : ((j + 2 : ℕ) : ℝ) = (j : ℝ) + 2 := by push_cast; ring
    rw [hcast]
    have hprod : (0 : ℝ) ≤ (d : ℝ) * Real.log 3 * (j : ℝ) := by positivity
    linarith only [hprod, hj]
  have hnn : (0 : ℝ) ≤ 1 + (d : ℝ) * (((j + 2 : ℕ) : ℝ) + 1) * Real.log 3 := by positivity
  calc annulusPenaltyThird d (j + 2)
      ≤ ((1 + 3 * (d : ℝ) * Real.log 3) * ((j : ℝ) + 1)) ^ (3 : ℕ) :=
        pow_le_pow_left₀ hnn hbase 3
    _ = (1 + 3 * (d : ℝ) * Real.log 3) ^ (3 : ℕ) * (((j : ℝ) + 1) ^ (3 : ℕ)) := by
        rw [mul_pow]

/-- **The canonical summability**: the weighted lattice penalties are summable
for every positive rate.  This is what makes the `𝒴`-series tail available; the
manuscript performs the same estimate implicitly when it writes `γ^{-4}`. -/
theorem summable_weight_mul_annulusPenaltyThird (d : ℕ) {sprime A : ℝ}
    (hsprime : 0 < sprime) (hA : 0 ≤ A) :
    Summable fun j : ℕ => weightThird sprime j * (A * annulusPenaltyThird d (j + 2)) := by
  set r : ℝ := (3 : ℝ) ^ (-sprime) with hr
  have hr0 : 0 < r := Real.rpow_pos_of_pos (by norm_num) _
  have hr1 : r < 1 := by
    rw [hr, show (1 : ℝ) = (3 : ℝ) ^ (0 : ℝ) by norm_num]
    exact (Real.rpow_lt_rpow_left_iff (by norm_num)).2 (by linarith only [hsprime])
  set B : ℝ := (1 + 3 * (d : ℝ) * Real.log 3) ^ (3 : ℕ) with hB
  have hB0 : 0 ≤ B := by
    have hlog : (0 : ℝ) ≤ Real.log 3 := Real.log_nonneg (by norm_num)
    rw [hB]
    positivity
  have hmaj : Summable fun j : ℕ => A * B * (((j : ℝ) + 1) ^ (3 : ℕ) * r ^ j) :=
    (summable_cubic_geometric hr0.le hr1).mul_left (A * B)
  refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_) hmaj
  · exact mul_nonneg (weightThird_pos j).le
      (mul_nonneg hA (annulusPenaltyThird_pos d (j + 2)).le)
  · have hpen := annulusPenaltyThird_le d j
    have hstep : A * annulusPenaltyThird d (j + 2) ≤ A * (B * ((j : ℝ) + 1) ^ (3 : ℕ)) :=
      mul_le_mul_of_nonneg_left hpen hA
    calc weightThird sprime j * (A * annulusPenaltyThird d (j + 2))
        ≤ weightThird sprime j * (A * (B * ((j : ℝ) + 1) ^ (3 : ℕ))) :=
          mul_le_mul_of_nonneg_left hstep (weightThird_pos j).le
      _ = A * B * (((j : ℝ) + 1) ^ (3 : ℕ) * r ^ j) := by
          rw [weightThird, ← hr]
          ring

/-! ## 5. The score field `𝒴_n` -/

/-- **The `𝒢₀` score field `𝒴_n`, formed in `ℝ≥0∞`.**  The manuscript's
normalization `γ^{-4}` is deliberately not included; the rate `s'` is the
manuscript's `¼γ`. -/
def YcalE (M : ABKModel d) (Ccg sprime : ℝ) (n : ℤ) (omega : Cutoff.CutoffSample d) : ℝ≥0∞ :=
  wsumE (fun j omega => annMax M Ccg n (n - (j : ℤ)) omega) (weightThird sprime) omega

/-- The real-valued score field. -/
def Ycal (M : ABKModel d) (Ccg sprime : ℝ) (n : ℤ) (omega : Cutoff.CutoffSample d) : ℝ :=
  wsum (fun j omega => annMax M Ccg n (n - (j : ℤ)) omega) (weightThird sprime) omega

theorem Ycal_nonneg (M : ABKModel d) (Ccg sprime : ℝ) (n : ℤ)
    (omega : Cutoff.CutoffSample d) : 0 ≤ Ycal M Ccg sprime n omega :=
  wsum_nonneg _ _ _

theorem measurable_Ycal (M : ABKModel d) (Ccg sprime : ℝ) (n : ℤ) :
    Measurable (Ycal M Ccg sprime n) :=
  measurable_wsum fun j => measurable_annMax M Ccg n (n - (j : ℤ))

/-- **Every single weighted annulus maximum is below `𝒴_n`** — unconditionally, in
`ℝ≥0∞`.  This is the `hatom` half of the domination chain, available with no
summability hypothesis. -/
theorem le_YcalE (M : ABKModel d) (Ccg sprime : ℝ) (n : ℤ)
    (omega : Cutoff.CutoffSample d) (j : ℕ) :
    ENNReal.ofReal (weightThird sprime j * annMax M Ccg n (n - (j : ℤ)) omega)
      ≤ YcalE M Ccg sprime n omega :=
  le_wsumE (fun j omega => annMax M Ccg n (n - (j : ℤ)) omega) (weightThird sprime) omega j

/-- **The `𝒴`-tail.**

```
𝒴_n ≤ 𝒪_{Γ_σ} ( gammaTriangleConst σ · Σ_j 3^{−s'j} a_j )
```

from the per-atom tail alone.  `a` is any sequence of positive scales dominating
the penalised atom scales `annulusPenalty d σ (j+2) · A`, with the weighted
series summable; the canonical choice `a_j = A · annulusPenaltyThird d (j+2)` at
`σ = 1/3` is admissible by `annulusPenalty_third` and
`summable_weight_mul_annulusPenaltyThird`.

The bound is uniform in `n`: the manuscript's `𝒴_n ≤ 𝒪_{Γ_{1/3}}(exp(−C^{−1}c⋆²γ^{−1}))`
is this statement with `A = exp(−(C_cg^{−1}E^{−2}γ^{−1}))` factored out of the
tsum. -/
theorem isBigOWith_Ycal (M : ABKModel d) (Ccg : ℝ) {sigma sprime A : ℝ} {a : ℕ → ℝ}
    (hsigma : 0 < sigma) (hA : 0 ≤ A)
    (hatom : ∀ (k : ℤ) (z : Vec d),
      IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure (gammaSigma sigma)
        (fun omega => Localize.cgExcess M Ccg (k - 2) z omega) A)
    (hapos : ∀ j : ℕ, 0 < a j)
    (hdom : ∀ j : ℕ, annulusPenalty d sigma (j + 2) * A ≤ a j)
    (hsum : Summable fun j : ℕ => weightThird sprime j * a j)
    (n : ℤ) :
    IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure (gammaSigma sigma)
      (Ycal M Ccg sprime n)
      (gammaTriangleConst sigma * ∑' j : ℕ, weightThird sprime j * a j) := by
  refine isBigOWith_wsum hsigma (fun j omega => annMax_nonneg M Ccg n _ omega)
    (fun j => measurable_annMax M Ccg n (n - (j : ℤ)))
    (fun j => weightThird_pos j) hapos hsum fun j => ?_
  have hidx : (n - (n - (j : ℤ) - 2)).toNat = j + 2 := by omega
  have hbase := isBigOWith_annMax M Ccg hsigma hA hatom n (n - (j : ℤ))
  rw [hidx] at hbase
  exact hbase.mono_scale (hdom j)

end

end Algsuperdiff.Section4.Provider.Proportion
