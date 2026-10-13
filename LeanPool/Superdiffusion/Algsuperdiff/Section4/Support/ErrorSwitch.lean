/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Support.ErrorRepresentative22
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.ErrorComparison.InftyToQ
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Homogenization.ObservationScaleFiniteCoverDepth
public import LeanPool.HighContrastHomogenization.Support.Besov.Poincare.Projection

/-!
# ErrorSwitch

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Subadditivity of `𝓔` at the exponent pair `(2,2)`: lifting the domain scale

ABK26, §4.1, `e.mathcalE.squared.max.bound`.  Step 1 of
`l.ratio.of.good.scales.for.mathcal.E` cites, verbatim,

> By Proposition `p.induction.bounds`, subadditivity of `𝓔`, `e.powerofGammasigma`
> and `e.maxy.bound` …

This module supplies the second of those four inputs, in the only form in which
it is true: at the *finite* spatial exponent.

## The statement

For every triadic cube `Q`, coefficient family `F` and comparator `a₀`,

```
𝓔_{s,2,2}(Q; F, a₀)²  ≤  3 · max_{R ∈ descendantsAtScale Q (Q.scale − 2)}
                              𝓔_{s,∞,2}(R; F, a₀)² .
```

The offset `2` is the one the `𝒢₂` atom needs; nothing in the argument is
special to it.

## Why the finite spatial exponent

At `p = 2` the shells are descendant *averages*, and averages factor through an
intermediate generation **exactly**, `descendantsAverage Q (2+k) =
descendantsAverage Q 2 (descendantsAverage · k)` (CoarseGraining's
`descendantsAverage_add_eq_descendantsAverage_descendantsAverage`), so the
finite average commutes with the infinite shell sum and no cardinality is paid.
This is the structural reason the manuscript's `X_j` is built from `𝓔_{s,2,2}`
rather than from `𝓔_{s,∞,2}`.

Only the two shallowest shells (`l = 0, 1`) need `e.subaddJ.nosymm` itself;
they are discharged by the proved average form
`normalizedBlockResponseMax_le_descendantsAverage`, which is exponent-free.

## Main results

* `finsetAverageReal_descendantsAtScale_eq_descendantsAverage` — the shell
  bridge between the `(2,2)` identity's scale indexing and CoarseGraining's
  depth indexing.
* `homogenizationErrorOnCube_two_two_sq_le_infinity_two_sq` — descendant average
  below descendant supremum, at a fixed cube.
* `homogenizationErrorOnCube_two_two_sq_le_descendant_sup` — the domain lift.
* `homogenizationErrorOnCube_two_two_le_sqrt_three_mul` — its square-root form
  against a uniform bound on the descendants.

## Scope

Deterministic Provider material: proved local helpers, carrier-generic in `F`
and `a₀`.

## References

* ABK26, `d.mathcal.E`, `e.subaddJ.nosymm`, `e.mathcalE.squared.max.bound`.
-/

namespace Algsuperdiff.Section4.Support

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02

noncomputable section

variable {d : ℕ} [NeZero d]

/-! ## The shell bridge -/

omit [NeZero d] in
/-- The `(2,2)` squared identity indexes its shells by `descendantsAtScale Q
(Q.scale − l)`; CoarseGraining's iterated-average calculus indexes them by
depth.  The two agree. -/
theorem finsetAverageReal_descendantsAtScale_eq_descendantsAverage
    (Q : TriadicCube d) (l : ℕ) (g : TriadicCube d → ℝ) :
    finsetAverageReal (descendantsAtScale Q (Q.scale - (l : ℤ))) g =
      descendantsAverage Q l g := by
  have hk : Q.scale - (l : ℤ) ≤ Q.scale :=
    sub_le_self _ (by exact_mod_cast Nat.zero_le l)
  have hdepth : Int.toNat (Q.scale - (Q.scale - (l : ℤ))) = l := by
    rw [sub_sub_cancel]
    exact Int.toNat_natCast l
  rw [descendantsAtScale_eq_descendantsAtDepth Q hk, hdepth]
  rfl

/-- Every value on a `Finset` sits below its `finsetSupReal`. -/
private theorem le_finsetSupReal' {alpha : Type*} (S : Finset alpha) (f : alpha → ℝ)
    {x : alpha} (hx : x ∈ S) : f x ≤ finsetSupReal S f := by
  unfold finsetSupReal
  exact le_csSup ((Set.toFinite _).image f).bddAbove ⟨x, hx, rfl⟩

/-! ## Nonnegativity of the two gauges -/

private theorem geometricWeight_two_nonneg {s : ℝ} (hs : 0 < s) (l : ℕ) :
    0 ≤ Ch02.geometricWeight s 2 l := by
  simpa only [Ch02.geometricWeight_eq_old] using
    HCPolySupport.geometricWeight_nonneg (s := s) (q := 2) l
      (by linarith only [hs.le])

private theorem scaleResponse_finite_two_nonneg (Q : TriadicCube d) (k : ℤ)
    (F : TriadicCoeffFamily d) (a0 : Mat d) :
    0 ≤ scaleResponseAtScale Q k (.finite 2) F a0 :=
  Real.rpow_nonneg
    (Section3.Provider.ErrorComparison.finsetAverageReal_nonneg _
      (fun R _ => Real.rpow_nonneg (normalizedBlockResponseMax_nonneg R F a0) _)) _

private theorem scaleResponse_infinity_nonneg (Q : TriadicCube d) {k : ℤ}
    (hk : k ≤ Q.scale) (F : TriadicCoeffFamily d) (a0 : Mat d) :
    0 ≤ scaleResponseAtScale Q k .infinity F a0 :=
  Real.rpow_nonneg
    (maxDescendantNormalizedBlockResponseAtScale_nonneg Q hk F a0) _

private theorem error_finite_two_nonneg (Q : TriadicCube d) {s : ℝ} (hs : 0 < s)
    (p : Ch02.MultiscaleExponent) (F : TriadicCoeffFamily d) (a0 : Mat d)
    (hp : ∀ l : ℕ, 0 ≤ scaleResponseAtScale Q (Q.scale - (l : ℤ)) p F a0) :
    0 ≤ HomogenizationErrorOnCube Q s p (.finite 2) F a0 :=
  Real.rpow_nonneg
    (tsum_nonneg fun l => mul_nonneg (geometricWeight_two_nonneg hs l)
      (Real.rpow_nonneg (hp l) _)) _

/-- The `(2,2)` error is nonnegative. -/
theorem homogenizationErrorOnCube_two_two_nonneg' (Q : TriadicCube d) {s : ℝ}
    (hs : 0 < s) (F : TriadicCoeffFamily d) (a0 : Mat d) :
    0 ≤ HomogenizationErrorOnCube Q s (.finite 2) (.finite 2) F a0 :=
  error_finite_two_nonneg Q hs _ F a0
    (fun _ => scaleResponse_finite_two_nonneg Q _ F a0)

/-- The `(∞,2)` error is nonnegative. -/
theorem homogenizationErrorOnCube_infinity_two_nonneg' (Q : TriadicCube d) {s : ℝ}
    (hs : 0 < s) (F : TriadicCoeffFamily d) (a0 : Mat d) :
    0 ≤ HomogenizationErrorOnCube Q s .infinity (.finite 2) F a0 :=
  error_finite_two_nonneg Q hs _ F a0 fun l =>
    scaleResponse_infinity_nonneg Q
      (sub_le_self _ (Int.natCast_nonneg l)) F a0

/-! ## The shells of the `(2,2)` square -/

/-- The `l`-th shell of `𝓔_{s,2,2}(Q)²`: the depth-`l` descendant average of the
normalized block-response maxima. -/
def shellAvg (Q : TriadicCube d) (F : TriadicCoeffFamily d) (a0 : Mat d)
    (l : ℕ) : ℝ :=
  finsetAverageReal (descendantsAtScale Q (Q.scale - (l : ℤ)))
    (fun R => normalizedBlockResponseMax R F a0)

private theorem shellAvg_eq_descendantsAverage (Q : TriadicCube d)
    (F : TriadicCoeffFamily d) (a0 : Mat d) (l : ℕ) :
    shellAvg Q F a0 l =
      descendantsAverage Q l (fun R => normalizedBlockResponseMax R F a0) :=
  finsetAverageReal_descendantsAtScale_eq_descendantsAverage Q l _

private theorem shellAvg_two_eq (Q : TriadicCube d) (F : TriadicCoeffFamily d)
    (a0 : Mat d) :
    shellAvg Q F a0 2 =
      finsetAverageReal (descendantsAtScale Q (Q.scale - (2 : ℤ)))
        (fun R => normalizedBlockResponseMax R F a0) := by
  simp only [shellAvg, Nat.cast_ofNat]

private theorem shellAvg_nonneg (Q : TriadicCube d) (F : TriadicCoeffFamily d)
    (a0 : Mat d) (l : ℕ) : 0 ≤ shellAvg Q F a0 l :=
  Section3.Provider.ErrorComparison.finsetAverageReal_nonneg _
    (fun R _ => normalizedBlockResponseMax_nonneg R F a0)

private theorem uniformBound_nonneg (Q : TriadicCube d) (F : TriadicCoeffFamily d)
    (a0 : Mat d) : 0 ≤ normalizedBlockResponseUniformBound Q F a0 := by
  have hQ : Q ∈ descendantsAtScale Q Q.scale := by
    rw [descendantsAtScale_self]
    exact Finset.mem_singleton_self Q
  exact le_trans (normalizedBlockResponseMax_nonneg Q F a0)
    (normalizedBlockResponseMax_le_uniform_of_mem_descendantsAtScale F a0 hQ)

private theorem shellAvg_le_uniform (Q : TriadicCube d) (F : TriadicCoeffFamily d)
    (a0 : Mat d) (l : ℕ) :
    shellAvg Q F a0 l ≤ normalizedBlockResponseUniformBound Q F a0 :=
  Section3.Provider.ErrorComparison.finsetAverageReal_le _
    (uniformBound_nonneg Q F a0)
    (fun _ hR => normalizedBlockResponseMax_le_uniform_of_mem_descendantsAtScale F a0 hR)

/-- The `(2,2)` shell series is summable: every shell sits below the one-cube
uniform response bound and the geometric weights sum. -/
private theorem summable_shellAvg (Q : TriadicCube d) (F : TriadicCoeffFamily d)
    (a0 : Mat d) {s : ℝ} (hs : 0 < s) :
    Summable (fun l : ℕ => Ch02.geometricWeight s 2 l * shellAvg Q F a0 l) := by
  simp only [Ch02.geometricWeight_eq_old]
  exact HCPolySupport.summable_geometricWeight_mul_of_nonneg_of_le
    (s := s) (q := 2) (C := normalizedBlockResponseUniformBound Q F a0)
    (by linarith only [hs]) (fun l => shellAvg_nonneg Q F a0 l)
    (fun l => shellAvg_le_uniform Q F a0 l)

private theorem sq_eq_tsum_shellAvg (Q : TriadicCube d) {s : ℝ} (hs : 0 < s)
    (F : TriadicCoeffFamily d) (a0 : Mat d) :
    (HomogenizationErrorOnCube Q s (.finite 2) (.finite 2) F a0) ^ 2 =
      ∑' l : ℕ, Ch02.geometricWeight s 2 l * shellAvg Q F a0 l :=
  homogenizationErrorOnCube_two_two_sq_eq_tsum Q hs F a0

/-! ## `(2,2)` below `(∞,2)` at a fixed cube -/

/-- **The descendant average sits below the descendant supremum, shell by
shell.**  Both series converge — the shared witness is the one-cube uniform
response bound — so the comparison survives the infinite sum. -/
theorem homogenizationErrorOnCube_two_two_sq_le_infinity_two_sq
    (Q : TriadicCube d) {s : ℝ} (hs : 0 < s) (F : TriadicCoeffFamily d)
    (a0 : Mat d) :
    (HomogenizationErrorOnCube Q s (.finite 2) (.finite 2) F a0) ^ 2 ≤
      (HomogenizationErrorOnCube Q s .infinity (.finite 2) F a0) ^ 2 := by
  rw [sq_eq_tsum_shellAvg Q hs F a0,
    homogenizationErrorOnCube_infinity_two_sq_eq_tsum Q hs F a0]
  refine Summable.tsum_le_tsum (fun l => ?_) (summable_shellAvg Q F a0 hs)
    (summable_geometricWeight_two_mul_maxDescendantNormalizedBlockResponseAtScale
      Q F a0 hs)
  refine mul_le_mul_of_nonneg_left ?_ (geometricWeight_two_nonneg hs l)
  refine Section3.Provider.ErrorComparison.finsetAverageReal_le _ ?_ ?_
  · exact finsetSupReal_nonneg _ _ fun R _ => normalizedBlockResponseMax_nonneg R F a0
  · intro R hR
    exact le_finsetSupReal' _ (fun T => normalizedBlockResponseMax T F a0) hR

/-! ## The two shallow shells -/

omit [NeZero d] in
private theorem descendantsAverage_mono (Q : TriadicCube d) (l : ℕ)
    {f g : TriadicCube d → ℝ} (h : ∀ R ∈ descendantsAtDepth Q l, f R ≤ g R) :
    descendantsAverage Q l f ≤ descendantsAverage Q l g := by
  unfold descendantsAverage
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum h) ?_
  positivity

omit [NeZero d] in
private theorem descendantsAverage_zero (Q : TriadicCube d)
    (f : TriadicCube d → ℝ) : descendantsAverage Q 0 f = f Q := by
  simp [descendantsAverage, descendantsAtDepth]

/-- Shell `0` sits below shell `2`: `e.subaddJ.nosymm` in average form at
depth `2`. -/
private theorem shellAvg_zero_le_two (Q : TriadicCube d) (F : TriadicCoeffFamily d)
    (a0 : Mat d) : shellAvg Q F a0 0 ≤ shellAvg Q F a0 2 := by
  rw [shellAvg_eq_descendantsAverage, shellAvg_eq_descendantsAverage,
    descendantsAverage_zero]
  exact Section3.Provider.Homogenization.ObservationScaleFiniteCoverInternal.normalizedBlockResponseMax_le_descendantsAverage
    Q 2 F a0

/-- Shell `1` sits below shell `2`: `e.subaddJ.nosymm` applied inside the
depth-`1` average, reassembled by the iterated-average identity. -/
private theorem shellAvg_one_le_two (Q : TriadicCube d) (F : TriadicCoeffFamily d)
    (a0 : Mat d) : shellAvg Q F a0 1 ≤ shellAvg Q F a0 2 := by
  rw [shellAvg_eq_descendantsAverage, shellAvg_eq_descendantsAverage]
  have hsplit :
      descendantsAverage Q 2 (fun R => normalizedBlockResponseMax R F a0) =
        descendantsAverage Q 1
          (fun T => descendantsAverage T 1
            (fun R => normalizedBlockResponseMax R F a0)) := by
    exact descendantsAverage_add_eq_descendantsAverage_descendantsAverage Q 1 1
      (fun R => normalizedBlockResponseMax R F a0)
  rw [hsplit]
  refine descendantsAverage_mono Q 1 fun T _ => ?_
  exact Section3.Provider.Homogenization.ObservationScaleFiniteCoverInternal.normalizedBlockResponseMax_le_descendantsAverage
    T 1 F a0

/-! ## The deep shells -/

/-- **The exact factorization.**  The depth-`(k+2)` shell of `Q` is the depth-`2`
average of the depth-`k` shells of the depth-`2` descendants.  This is what the
`p = ∞` gauge does not have. -/
private theorem shellAvg_add_two (Q : TriadicCube d) (F : TriadicCoeffFamily d)
    (a0 : Mat d) (k : ℕ) :
    shellAvg Q F a0 (k + 2) =
      finsetAverageReal (descendantsAtScale Q (Q.scale - (2 : ℤ)))
        (fun R => shellAvg R F a0 k) := by
  have hbridge :
      finsetAverageReal (descendantsAtScale Q (Q.scale - (2 : ℤ)))
          (fun R => shellAvg R F a0 k) =
        descendantsAverage Q 2 (fun R => shellAvg R F a0 k) := by
    simpa only [Nat.cast_ofNat] using
      finsetAverageReal_descendantsAtScale_eq_descendantsAverage Q 2
        (fun R => shellAvg R F a0 k)
  rw [hbridge, shellAvg_eq_descendantsAverage, show k + 2 = 2 + k from by omega,
    descendantsAverage_add_eq_descendantsAverage_descendantsAverage Q 2 k]
  refine congrArg (descendantsAverage Q 2) ?_
  funext R
  exact (shellAvg_eq_descendantsAverage R F a0 k).symm

private theorem geometricWeight_two_antitone {s : ℝ} (hs : 0 < s) {j k : ℕ}
    (hjk : j ≤ k) : Ch02.geometricWeight s 2 k ≤ Ch02.geometricWeight s 2 j := by
  have hdisc : 0 ≤ Ch02.geometricDiscount s 2 := by
    simpa only [Ch02.geometricDiscount_eq_old] using
      HCPolySupport.geometricDiscount_nonneg (s := s) (q := 2)
        (by linarith only [hs.le])
  have hcast : (j : ℝ) ≤ (k : ℝ) := by exact_mod_cast hjk
  have hexp : Real.rpow (3 : ℝ) (-s * 2 * (k : ℝ)) ≤
      Real.rpow (3 : ℝ) (-s * 2 * (j : ℝ)) := by
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    have hkey : -s * 2 * (k : ℝ) - (-s * 2 * (j : ℝ)) =
        (-(2 * s)) * ((k : ℝ) - (j : ℝ)) := by ring
    have hprod : 0 ≤ (2 * s) * ((k : ℝ) - (j : ℝ)) := by
      have h1 : (0 : ℝ) ≤ 2 * s := by linarith only [hs.le]
      have h2 : (0 : ℝ) ≤ (k : ℝ) - (j : ℝ) := by linarith only [hcast]
      exact mul_nonneg h1 h2
    linarith only [hkey, hprod]
  exact mul_le_mul_of_nonneg_left hexp hdisc

/-- The deep half of the shell series is dominated by the depth-`2` average of
the full `(2,2)` squares of the depth-`2` descendants. -/
private theorem tsum_deep_le (Q : TriadicCube d) {s : ℝ} (hs : 0 < s)
    (F : TriadicCoeffFamily d) (a0 : Mat d) :
    ∑' k : ℕ, Ch02.geometricWeight s 2 (k + 2) * shellAvg Q F a0 (k + 2) ≤
      finsetAverageReal (descendantsAtScale Q (Q.scale - (2 : ℤ)))
        (fun R => (HomogenizationErrorOnCube R s (.finite 2) (.finite 2) F a0) ^ 2) := by
  classical
  set S := descendantsAtScale Q (Q.scale - (2 : ℤ)) with hS
  have hsummableQ : Summable
      (fun k : ℕ => Ch02.geometricWeight s 2 (k + 2) * shellAvg Q F a0 (k + 2)) :=
    (summable_nat_add_iff 2).2 (summable_shellAvg Q F a0 hs)
  have hmemS : ∀ R ∈ S, ∀ (k : ℕ), ∀ T ∈ descendantsAtScale R (R.scale - (k : ℤ)),
      normalizedBlockResponseMax T F a0 ≤ normalizedBlockResponseUniformBound Q F a0 := by
    intro R hR k T hT
    exact normalizedBlockResponseMax_le_uniform_of_mem_descendantsAtScale F a0
      (mem_descendantsAtScale_trans hR hT)
  have hinner : Summable
      (fun k : ℕ => Ch02.geometricWeight s 2 k *
        finsetAverageReal S (fun R => shellAvg R F a0 k)) := by
    simp only [Ch02.geometricWeight_eq_old]
    refine HCPolySupport.summable_geometricWeight_mul_of_nonneg_of_le
      (s := s) (q := 2) (C := normalizedBlockResponseUniformBound Q F a0)
      (by linarith only [hs]) (fun k => ?_) (fun k => ?_)
    · exact Section3.Provider.ErrorComparison.finsetAverageReal_nonneg _
        (fun R _ => shellAvg_nonneg R F a0 k)
    · refine Section3.Provider.ErrorComparison.finsetAverageReal_le _
        (uniformBound_nonneg Q F a0) fun R hR => ?_
      exact Section3.Provider.ErrorComparison.finsetAverageReal_le _
        (uniformBound_nonneg Q F a0) fun T hT => hmemS R hR k T hT
  have hstep : ∑' k : ℕ, Ch02.geometricWeight s 2 (k + 2) * shellAvg Q F a0 (k + 2) ≤
      ∑' k : ℕ, Ch02.geometricWeight s 2 k *
        finsetAverageReal S (fun R => shellAvg R F a0 k) := by
    refine Summable.tsum_le_tsum (fun k => ?_) hsummableQ hinner
    rw [shellAvg_add_two Q F a0 k, ← hS]
    refine mul_le_mul_of_nonneg_right
      (geometricWeight_two_antitone hs (Nat.le_add_right k 2)) ?_
    exact Section3.Provider.ErrorComparison.finsetAverageReal_nonneg _
      (fun R _ => shellAvg_nonneg R F a0 k)
  refine hstep.trans_eq ?_
  have hexchange : ∀ k : ℕ,
      Ch02.geometricWeight s 2 k * finsetAverageReal S (fun R => shellAvg R F a0 k) =
        ((S.card : ℝ)⁻¹) * ∑ R ∈ S, Ch02.geometricWeight s 2 k * shellAvg R F a0 k := by
    intro k
    simp only [finsetAverageReal, Finset.mul_sum]
    exact Finset.sum_congr rfl fun R _ => by ring
  have hA : ∑' k : ℕ, Ch02.geometricWeight s 2 k *
        finsetAverageReal S (fun R => shellAvg R F a0 k) =
      ∑' k : ℕ, ((S.card : ℝ)⁻¹) *
        ∑ R ∈ S, Ch02.geometricWeight s 2 k * shellAvg R F a0 k := by
    exact tsum_congr hexchange
  have hB : ∑' k : ℕ, ((S.card : ℝ)⁻¹) *
        ∑ R ∈ S, Ch02.geometricWeight s 2 k * shellAvg R F a0 k =
      ((S.card : ℝ)⁻¹) *
        ∑' k : ℕ, ∑ R ∈ S, Ch02.geometricWeight s 2 k * shellAvg R F a0 k := by
    exact tsum_mul_left
  have hC : ∑' k : ℕ, ∑ R ∈ S, Ch02.geometricWeight s 2 k * shellAvg R F a0 k =
      ∑ R ∈ S, ∑' k : ℕ, Ch02.geometricWeight s 2 k * shellAvg R F a0 k :=
    Summable.tsum_finsetSum fun R _ => summable_shellAvg R F a0 hs
  have hD : ∑ R ∈ S, ∑' k : ℕ, Ch02.geometricWeight s 2 k * shellAvg R F a0 k =
      ∑ R ∈ S, (HomogenizationErrorOnCube R s (.finite 2) (.finite 2) F a0) ^ 2 :=
    Finset.sum_congr rfl fun R _ => (sq_eq_tsum_shellAvg R hs F a0).symm
  rw [hA, hB, hC, hD, finsetAverageReal]

/-! ## The domain lift -/

/-- **Subadditivity of `𝓔` at `(2,2)`, two triadic scales up.**  The manuscript's
"subadditivity of `𝓔`", read in the direction it is used there: the functional
on `Q` is controlled by the functionals on the descendants of `Q` two scales
down, at a purely numerical cost.

The right-hand side is read at the endpoint spatial exponent, which is the
exponent the Section 3 anchor supplies. -/
theorem homogenizationErrorOnCube_two_two_sq_le_descendant_sup
    (Q : TriadicCube d) {s : ℝ} (hs : 0 < s) (F : TriadicCoeffFamily d)
    (a0 : Mat d) :
    (HomogenizationErrorOnCube Q s (.finite 2) (.finite 2) F a0) ^ 2 ≤
      3 * finsetSupReal (descendantsAtScale Q (Q.scale - (2 : ℤ)))
        (fun R => (HomogenizationErrorOnCube R s .infinity (.finite 2) F a0) ^ 2) := by
  classical
  set S := descendantsAtScale Q (Q.scale - (2 : ℤ)) with hS
  set G := finsetSupReal S
    (fun R => (HomogenizationErrorOnCube R s .infinity (.finite 2) F a0) ^ 2) with hG
  have hG0 : 0 ≤ G := finsetSupReal_nonneg _ _ fun _ _ => sq_nonneg _
  have hRle : ∀ R ∈ S,
      (HomogenizationErrorOnCube R s (.finite 2) (.finite 2) F a0) ^ 2 ≤ G := by
    intro R hR
    exact (homogenizationErrorOnCube_two_two_sq_le_infinity_two_sq R hs F a0).trans
      (le_finsetSupReal' S
        (fun T => (HomogenizationErrorOnCube T s .infinity (.finite 2) F a0) ^ 2) hR)
  have hw0 : 0 ≤ Ch02.geometricWeight s 2 0 := geometricWeight_two_nonneg hs 0
  have hshell2 : Ch02.geometricWeight s 2 0 * shellAvg Q F a0 2 ≤ G := by
    have hkey : ∀ R ∈ S,
        Ch02.geometricWeight s 2 0 * normalizedBlockResponseMax R F a0 ≤ G := by
      intro R hR
      refine le_trans ?_ (hRle R hR)
      rw [sq_eq_tsum_shellAvg R hs F a0]
      have h0 : shellAvg R F a0 0 = normalizedBlockResponseMax R F a0 := by
        rw [shellAvg_eq_descendantsAverage, descendantsAverage_zero]
      rw [← h0]
      have hsingle := (summable_shellAvg R F a0 hs).sum_le_tsum ({0} : Finset ℕ)
        (fun k _ => mul_nonneg (geometricWeight_two_nonneg hs k)
          (shellAvg_nonneg R F a0 k))
      simpa only [Finset.sum_singleton] using hsingle
    have hcalc : Ch02.geometricWeight s 2 0 * shellAvg Q F a0 2 =
        finsetAverageReal S
          (fun R => Ch02.geometricWeight s 2 0 * normalizedBlockResponseMax R F a0) := by
      rw [shellAvg_two_eq, ← hS]
      simp only [finsetAverageReal, Finset.mul_sum]
      exact Finset.sum_congr rfl fun R _ => by ring
    rw [hcalc]
    exact Section3.Provider.ErrorComparison.finsetAverageReal_le _ hG0 hkey
  rw [sq_eq_tsum_shellAvg Q hs F a0]
  have hsum := summable_shellAvg Q F a0 hs
  have hsplit :
      (∑ l ∈ Finset.range 2, Ch02.geometricWeight s 2 l * shellAvg Q F a0 l) +
        ∑' k : ℕ, Ch02.geometricWeight s 2 (k + 2) * shellAvg Q F a0 (k + 2) =
      ∑' l : ℕ, Ch02.geometricWeight s 2 l * shellAvg Q F a0 l :=
    hsum.sum_add_tsum_nat_add 2
  rw [← hsplit]
  have hhead :
      (∑ l ∈ Finset.range 2, Ch02.geometricWeight s 2 l * shellAvg Q F a0 l) ≤ 2 * G := by
    have hexpand : (∑ l ∈ Finset.range 2, Ch02.geometricWeight s 2 l * shellAvg Q F a0 l) =
        Ch02.geometricWeight s 2 0 * shellAvg Q F a0 0 +
          Ch02.geometricWeight s 2 1 * shellAvg Q F a0 1 := by
      simp [Finset.sum_range_succ]
    rw [hexpand]
    have h0 : Ch02.geometricWeight s 2 0 * shellAvg Q F a0 0 ≤ G :=
      le_trans (mul_le_mul_of_nonneg_left (shellAvg_zero_le_two Q F a0) hw0) hshell2
    have h1 : Ch02.geometricWeight s 2 1 * shellAvg Q F a0 1 ≤ G := by
      refine le_trans ?_ hshell2
      exact mul_le_mul (geometricWeight_two_antitone hs (Nat.zero_le 1))
        (shellAvg_one_le_two Q F a0) (shellAvg_nonneg Q F a0 1) hw0
    linarith only [h0, h1]
  have hdeep : ∑' k : ℕ, Ch02.geometricWeight s 2 (k + 2) * shellAvg Q F a0 (k + 2) ≤ G := by
    refine (tsum_deep_le Q hs F a0).trans ?_
    rw [← hS]
    exact Section3.Provider.ErrorComparison.finsetAverageReal_le _ hG0 hRle
  linarith only [hhead, hdeep]

/-- The square-root form: a uniform bound `B` on the `(∞,2)` errors of the
depth-`2` descendants bounds the `(2,2)` error of `Q` by `√3 · B`. -/
theorem homogenizationErrorOnCube_two_two_le_sqrt_three_mul
    (Q : TriadicCube d) {s : ℝ} (hs : 0 < s) (F : TriadicCoeffFamily d)
    (a0 : Mat d) {B : ℝ} (hB : 0 ≤ B)
    (hbd : ∀ R ∈ descendantsAtScale Q (Q.scale - (2 : ℤ)),
      HomogenizationErrorOnCube R s .infinity (.finite 2) F a0 ≤ B) :
    HomogenizationErrorOnCube Q s (.finite 2) (.finite 2) F a0 ≤ Real.sqrt 3 * B := by
  classical
  have hQ0 : 0 ≤ HomogenizationErrorOnCube Q s (.finite 2) (.finite 2) F a0 :=
    homogenizationErrorOnCube_two_two_nonneg' Q hs F a0
  have hSne : (descendantsAtScale Q (Q.scale - (2 : ℤ))).Nonempty :=
    descendantsAtScale_nonempty Q (by omega)
  have hsup : finsetSupReal (descendantsAtScale Q (Q.scale - (2 : ℤ)))
      (fun R => (HomogenizationErrorOnCube R s .infinity (.finite 2) F a0) ^ 2) ≤
        B ^ 2 := by
    refine finsetSupReal_le _ hSne fun R hR => ?_
    exact pow_le_pow_left₀
      (homogenizationErrorOnCube_infinity_two_nonneg' R hs F a0) (hbd R hR) 2
  have hkey : (HomogenizationErrorOnCube Q s (.finite 2) (.finite 2) F a0) ^ 2 ≤
      3 * B ^ 2 := by
    refine (homogenizationErrorOnCube_two_two_sq_le_descendant_sup Q hs F a0).trans ?_
    exact mul_le_mul_of_nonneg_left hsup (by norm_num)
  have hsqrt := Real.sqrt_le_sqrt hkey
  rw [Real.sqrt_sq hQ0] at hsqrt
  refine hsqrt.trans_eq ?_
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_sq hB]

end

end Algsuperdiff.Section4.Support
