/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Percolation.BadClusterDiameter

/-!
# MinimalScaleSeparation

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# `p.minimal.scale.separation`: the minimal scale separation for bad clusters

This module provides the threshold and tail ingredients used toward ABK26's
Proposition `p.minimal.scale.separation`: the function `hsep` above which both
deterministic bad-cluster bounds hold, its defining characterizations, and its
`Gamma`-tail.

## The carrier of `hsep`

The manuscript defines `hsep` as the infimum of the set of `j in N_0` above
which both deterministic bounds hold at every scale `h >= j`, with the value
`infinity` when no such `j` exists.  Here:

```
hsepSet omega := { j : 1 <= j and every h >= j is good } ,
hsep omega    := sInf (hsepSet omega) .
```

`hsepSet` is upward closed, so `hsep` is the manuscript's threshold and the
conclusion "every `h >= hsep` is good" is correct *by construction* — this is
`badClusterDiam_lt_of_hsep_le` and `badExtendedDensity_le_of_hsep_le`.  Two
disclosures come with the carrier.

* The manuscript's `hsep` ranges over `N_0`; ours is `>= 1` whenever it is
  meaningful, because the proved per-scale conclusions are stated for `h >= 1`
  (the manuscript's own `h in N` convention in `l.percolation.bad.clusters`).
  Both consumers use `hsep` additively (`e.hn.def`), so the shift is
  immaterial.
* On the event where *no* `j` works, `sInf empty = 0` is a junk value.  That
  event is exactly `{omega : not (hsepSet omega).Nonempty}`, it is carried
  explicitly in every probabilistic statement (through
  `scaleSeparationFail_eq`), and it is *null*
  (`measureReal_hsepSet_not_nonempty_of_gates`).

## Units

Everything is in the cube-side units of `BadClusters.lean` and
`BadClusterDiameter.lean`: the lattice `3^{m-h} Z^d cap cu_m` is `cubeFinset h`
through `z = 3^{m-h} u`, and the printed diameter threshold `3^{bh} 3^{m-h}`
is `3^{bh}`.

## The tail constant

The manuscript's proof bounds `P[hsep >= j]` by a union bound over `h >= j` and
then writes `<= C exp(-3^{(1-sigma) b j})`.  The geometric constant of that
union bound is `(1 - exp(-(1-sigma) b log 3))^{-1}`, which is **not** bounded
by any `C(d)`: it blows up as `(1-sigma) b -> 0`.  It is carried here
explicitly as `hsepTailConst sigma b`, and the amplitude of the resulting
`Gamma_{1-sigma}` bound is `hsepAmplitude sigma b`, the paper's own
`C(sigma, b)`.

## Main results

* `hsep`, `hsepSet`: the definition, with `hsepSet_upward`, `one_le_hsep_iff`,
  `hsep_le_of_mem`, `mem_hsepSet_iff_hsep_le`.
* `badClusterDiam_lt_of_hsep_le`: `e.diameter.deterministic`.
* `badExtendedDensity_le_of_hsep_le`: `e.density.deterministic`.
* `measureReal_scaleSeparationFail_le_of_gates`: the union bound of the proof
  from the exact raw probability gates.
* `measureReal_hsepSet_not_nonempty_of_gates`: `hsep` is a.s. well defined from
  the same gates.
* `isBigOWith_gammaSigma_three_rpow_hsep_of_gates`: `e.hsep.tails` at the
  explicit amplitude (departing from the printed `1`, the escalation;: the
  amplitude `C(σ,b)` is adopted).
* The names without `_of_gates` are compatibility wrappers for the packaged
  preliminary admissibility.

## Measurability and downstream use

The tex asserts `hsep` is a *random variable*.  No `Measurable` statement is
proved in this file.  Every probability statement here goes through
`measure_mono` / `measure_iUnion_le` / `measure_union_le`, which hold for
arbitrary sets, so all proved bounds are valid (outer-measure bounds, if
anything stronger) regardless.  The downstream consumer
`Multiscale/BfaPerCube.lean` supplies `measurable_hsep` before integrating
functions of this threshold.  This separation of providers is not a claim that
the exact source proposition has been frozen and proved.

## References

* ABK26, `p.minimal.scale.separation`.
-/

namespace Algsuperdiff.Section3.Provider.Percolation

open MeasureTheory ProbabilityTheory
open Algsuperdiff.Section3.Cutoff

noncomputable section

variable {d : ℕ}

/-! ## Elementary numerics -/

private theorem log_three_pos : (0 : ℝ) < Real.log 3 :=
  lt_of_lt_of_le zero_lt_one one_le_log_three

/-- `1 + x log 3 <= 3^x`: the elementary linearization of the exponential. -/
private theorem one_add_mul_log_three_le (x : ℝ) : 1 + Real.log 3 * x ≤ (3 : ℝ) ^ x := by
  rw [Real.rpow_def_of_pos (show (0 : ℝ) < 3 by norm_num)]
  linarith [Real.add_one_le_exp (Real.log 3 * x)]

private theorem exp_neg_lt_one {x : ℝ} (hx : 0 < x) : Real.exp (-x) < 1 := by
  calc Real.exp (-x) < Real.exp 0 := Real.exp_lt_exp.2 (by linarith)
    _ = 1 := Real.exp_zero

private theorem one_sub_exp_neg_pos {x : ℝ} (hx : 0 < x) : (0 : ℝ) < 1 - Real.exp (-x) := by
  linarith [exp_neg_lt_one hx]

private theorem one_le_inv_one_sub_exp_neg {x : ℝ} (hx : 0 < x) :
    (1 : ℝ) ≤ (1 - Real.exp (-x))⁻¹ := by
  have hpos : (0 : ℝ) < 1 - Real.exp (-x) := one_sub_exp_neg_pos hx
  have hinvpos : (0 : ℝ) < (1 - Real.exp (-x))⁻¹ := inv_pos.2 hpos
  have hmul : (1 - Real.exp (-x)) * (1 - Real.exp (-x))⁻¹ = 1 :=
    mul_inv_cancel₀ (ne_of_gt hpos)
  have hle : (1 - Real.exp (-x)) * (1 - Real.exp (-x))⁻¹ ≤
      1 * (1 - Real.exp (-x))⁻¹ :=
    mul_le_mul_of_nonneg_right (by linarith [Real.exp_pos (-x)]) hinvpos.le
  rw [hmul, one_mul] at hle
  exact hle

/-! ## The geometric tail sum

The doubly exponential per-scale bounds `exp(-3^{alpha h})` are summed over
`h >= j` against the geometric ratio `exp(-alpha log 3)`. -/

/-- The per-term geometric domination behind the union bound over `h >= j`. -/
private theorem exp_neg_three_rpow_le_geom {alpha : ℝ} (halpha : 0 < alpha) (j k : ℕ) :
    Real.exp (-(3 : ℝ) ^ (alpha * ((j : ℝ) + (k : ℝ)))) ≤
      Real.exp (-(3 : ℝ) ^ (alpha * (j : ℝ))) *
        Real.exp (-(alpha * Real.log 3)) ^ k := by
  have h3 : (0 : ℝ) < 3 := by norm_num
  have hs1 : (1 : ℝ) ≤ (3 : ℝ) ^ (alpha * (j : ℝ)) :=
    Real.one_le_rpow (by norm_num) (by positivity)
  have hsplit : (3 : ℝ) ^ (alpha * ((j : ℝ) + (k : ℝ))) =
      (3 : ℝ) ^ (alpha * (j : ℝ)) * (3 : ℝ) ^ (alpha * (k : ℝ)) := by
    rw [← Real.rpow_add h3]
    ring_nf
  have hk := one_add_mul_log_three_le (alpha * (k : ℝ))
  have hknn : (0 : ℝ) ≤ Real.log 3 * (alpha * (k : ℝ)) := by
    have := log_three_pos
    positivity
  have h1 : (3 : ℝ) ^ (alpha * (j : ℝ)) * (1 + Real.log 3 * (alpha * (k : ℝ))) ≤
      (3 : ℝ) ^ (alpha * (j : ℝ)) * (3 : ℝ) ^ (alpha * (k : ℝ)) :=
    mul_le_mul_of_nonneg_left hk (by linarith)
  have h2 : Real.log 3 * (alpha * (k : ℝ)) ≤
      (3 : ℝ) ^ (alpha * (j : ℝ)) * (Real.log 3 * (alpha * (k : ℝ))) :=
    le_mul_of_one_le_left hknn hs1
  have hge : (3 : ℝ) ^ (alpha * (j : ℝ)) + Real.log 3 * (alpha * (k : ℝ)) ≤
      (3 : ℝ) ^ (alpha * ((j : ℝ) + (k : ℝ))) := by
    rw [hsplit]
    nlinarith [h1, h2]
  calc Real.exp (-(3 : ℝ) ^ (alpha * ((j : ℝ) + (k : ℝ))))
      ≤ Real.exp (-((3 : ℝ) ^ (alpha * (j : ℝ)) +
          Real.log 3 * (alpha * (k : ℝ)))) := Real.exp_le_exp.2 (by linarith)
    _ = Real.exp (-(3 : ℝ) ^ (alpha * (j : ℝ))) *
          Real.exp (-(alpha * Real.log 3)) ^ k := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]
        congr 1
        ring

private theorem summable_exp_neg_three_rpow {alpha : ℝ} (halpha : 0 < alpha) (j : ℕ) :
    Summable fun k : ℕ => Real.exp (-(3 : ℝ) ^ (alpha * ((j : ℝ) + (k : ℝ)))) := by
  have hr0 : (0 : ℝ) ≤ Real.exp (-(alpha * Real.log 3)) := (Real.exp_pos _).le
  have hr1 : Real.exp (-(alpha * Real.log 3)) < 1 :=
    exp_neg_lt_one (mul_pos halpha log_three_pos)
  exact Summable.of_nonneg_of_le (fun k => (Real.exp_pos _).le)
    (fun k => exp_neg_three_rpow_le_geom halpha j k)
    ((summable_geometric_of_lt_one hr0 hr1).mul_left _)

private theorem tsum_exp_neg_three_rpow_le {alpha : ℝ} (halpha : 0 < alpha) (j : ℕ) :
    (∑' k : ℕ, Real.exp (-(3 : ℝ) ^ (alpha * ((j : ℝ) + (k : ℝ))))) ≤
      (1 - Real.exp (-(alpha * Real.log 3)))⁻¹ *
        Real.exp (-(3 : ℝ) ^ (alpha * (j : ℝ))) := by
  have hr0 : (0 : ℝ) ≤ Real.exp (-(alpha * Real.log 3)) := (Real.exp_pos _).le
  have hr1 : Real.exp (-(alpha * Real.log 3)) < 1 :=
    exp_neg_lt_one (mul_pos halpha log_three_pos)
  have hgeom : Summable fun k : ℕ =>
      Real.exp (-(3 : ℝ) ^ (alpha * (j : ℝ))) *
        Real.exp (-(alpha * Real.log 3)) ^ k :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left _
  refine le_trans (Summable.tsum_le_tsum (fun k => exp_neg_three_rpow_le_geom halpha j k)
    (summable_exp_neg_three_rpow halpha j) hgeom) ?_
  rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1, mul_comm]

/-! ## The good-scale predicate -/

/-- The threshold of `e.density.deterministic` at separation `h`, with the
dimension-only witness `c(d) = siteRateBase d / 2` supplied by the proved
density conclusion `measureReal_badExtendedDensity_gt_le_exp`. -/
def scaleSeparationDensityThreshold (M : ABKModel d) (E : ℝ) (h : ℕ) : ℝ :=
  Real.exp (-(siteRateBase d / 2 * (E⁻¹ ^ 2 * M.gamma⁻¹))) + (3 : ℝ) ^ (-(h : ℝ) / 2)

/-- A scale separation `h` is *good* for `omega` when both deterministic bounds of
`p.minimal.scale.separation` hold at `h`: the diameter bound
`e.diameter.deterministic` (in cube-side units) and the density bound
`e.density.deterministic`. -/
def scaleSeparationGood (M : ABKModel d) (m : ℤ) (E b : ℝ) (h : ℕ)
    (omega : CutoffSample d) : Prop :=
  (∀ u ∈ cubeFinset (d := d) h,
      (badClusterDiam M m h omega u : ℝ) < (3 : ℝ) ^ (b * (h : ℝ))) ∧
    badExtendedDensity M m h omega ≤ scaleSeparationDensityThreshold M E h

/-- The event of `e.diameter.bound.bad.clusters`: the diameter bound fails at
separation `h`. -/
def badClusterDiamFail (M : ABKModel d) (m : ℤ) (b : ℝ) (h : ℕ) :
    Set (CutoffSample d) :=
  {omega | ∃ u ∈ cubeFinset (d := d) h,
    (3 : ℝ) ^ (b * (h : ℝ)) ≤ (badClusterDiam M m h omega u : ℝ)}

/-- The event of `e.density.bound.bad.clusters`: the density bound fails at
separation `h`. -/
def badExtendedDensityFail (M : ABKModel d) (m : ℤ) (E : ℝ) (h : ℕ) :
    Set (CutoffSample d) :=
  {omega | scaleSeparationDensityThreshold M E h < badExtendedDensity M m h omega}

theorem notGood_subset_union (M : ABKModel d) (m : ℤ) (E b : ℝ) (h : ℕ) :
    {omega | ¬ scaleSeparationGood M m E b h omega} ⊆
      badClusterDiamFail M m b h ∪ badExtendedDensityFail M m E h := by
  intro omega homega
  by_cases hdiam : ∀ u ∈ cubeFinset (d := d) h,
      (badClusterDiam M m h omega u : ℝ) < (3 : ℝ) ^ (b * (h : ℝ))
  · refine Or.inr ?_
    show scaleSeparationDensityThreshold M E h < badExtendedDensity M m h omega
    by_contra hdens
    exact homega ⟨hdiam, not_lt.1 hdens⟩
  · refine Or.inl ?_
    push Not at hdiam
    exact hdiam

/-! ## The minimal scale separation -/

/-- The set of admissible scale separations for `omega`: those `j >= 1` above
which every scale is good.  It is upward closed (`hsepSet_upward`). -/
def hsepSet (M : ABKModel d) (m : ℤ) (E b : ℝ) (omega : CutoffSample d) : Set ℕ :=
  {j : ℕ | 1 ≤ j ∧ ∀ h : ℕ, j ≤ h → scaleSeparationGood M m E b h omega}

/-- On the null event where no such separation exists the `sInf` of the empty set
gives the junk value `0`; see `measureReal_hsepSet_not_nonempty_of_gates`. -/
def hsep (M : ABKModel d) (m : ℤ) (E b : ℝ) (omega : CutoffSample d) : ℕ :=
  sInf (hsepSet M m E b omega)

theorem mem_hsepSet_iff {M : ABKModel d} {m : ℤ} {E b : ℝ} {omega : CutoffSample d}
    {j : ℕ} :
    j ∈ hsepSet M m E b omega ↔
      1 ≤ j ∧ ∀ h : ℕ, j ≤ h → scaleSeparationGood M m E b h omega :=
  Iff.rfl

theorem hsepSet_upward {M : ABKModel d} {m : ℤ} {E b : ℝ} {omega : CutoffSample d}
    {j k : ℕ} (hj : j ∈ hsepSet M m E b omega) (hjk : j ≤ k) :
    k ∈ hsepSet M m E b omega :=
  ⟨le_trans hj.1 hjk, fun h hh => hj.2 h (le_trans hjk hh)⟩

theorem hsep_le_of_mem {M : ABKModel d} {m : ℤ} {E b : ℝ} {omega : CutoffSample d}
    {j : ℕ} (hj : j ∈ hsepSet M m E b omega) :
    hsep M m E b omega ≤ j :=
  Nat.sInf_le hj

theorem hsep_mem {M : ABKModel d} {m : ℤ} {E b : ℝ} {omega : CutoffSample d}
    (hne : (hsepSet M m E b omega).Nonempty) :
    hsep M m E b omega ∈ hsepSet M m E b omega :=
  Nat.sInf_mem hne

/-- `hsep` is meaningful exactly where it is positive. -/
theorem one_le_hsep_iff {M : ABKModel d} {m : ℤ} {E b : ℝ} {omega : CutoffSample d} :
    1 ≤ hsep M m E b omega ↔ (hsepSet M m E b omega).Nonempty := by
  constructor
  · intro h1
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hsep, hne, Nat.sInf_empty] at h1
    omega
  · intro hne
    exact (hsep_mem hne).1

/-- The defining characterization: for `j >= 1`, membership of `j` in the
admissible set is exactly the assertion that `hsep` is meaningful and at most
`j`. -/
theorem mem_hsepSet_iff_hsep_le {M : ABKModel d} {m : ℤ} {E b : ℝ}
    {omega : CutoffSample d} {j : ℕ} :
    j ∈ hsepSet M m E b omega ↔
      (1 ≤ hsep M m E b omega ∧ hsep M m E b omega ≤ j) := by
  constructor
  · intro hmem
    exact ⟨one_le_hsep_iff.2 ⟨j, hmem⟩, hsep_le_of_mem hmem⟩
  · rintro ⟨h1, h2⟩
    exact hsepSet_upward (hsep_mem (one_le_hsep_iff.1 h1)) h2

/-- **ABK26 `e.diameter.deterministic`**, in cube-side units: `max_{z}
diam(B^*_{m-h}(z;2)) < 3^{bh}` for every `h >= hsep`. -/
theorem badClusterDiam_lt_of_hsep_le {M : ABKModel d} {m : ℤ} {E b : ℝ}
    {omega : CutoffSample d} (hne : (hsepSet M m E b omega).Nonempty) {h : ℕ}
    (hh : hsep M m E b omega ≤ h) {u : Fin d → ℤ} (hu : u ∈ cubeFinset (d := d) h) :
    (badClusterDiam M m h omega u : ℝ) < (3 : ℝ) ^ (b * (h : ℝ)) :=
  ((hsep_mem hne).2 h hh).1 u hu

/-- **ABK26 `e.density.deterministic`**: `avsum_{z} 1_{B^*(z + cu_{m-h})} <= exp(-c
E^{-2} gamma^{-1}) + 3^{-h/2}` for every `h >= hsep`. -/
theorem badExtendedDensity_le_of_hsep_le {M : ABKModel d} {m : ℤ} {E b : ℝ}
    {omega : CutoffSample d} (hne : (hsepSet M m E b omega).Nonempty) {h : ℕ}
    (hh : hsep M m E b omega ≤ h) :
    badExtendedDensity M m h omega ≤ scaleSeparationDensityThreshold M E h :=
  ((hsep_mem hne).2 h hh).2

/-! ## The tail of `hsep` -/

/-- The failure event at level `j`: some scale `h >= j` is not good.  For
`j >= 1` this is exactly the complement of `{hsep is meaningful and <= j}`
(`scaleSeparationFail_eq`). -/
def scaleSeparationFail (M : ABKModel d) (m : ℤ) (E b : ℝ) (j : ℕ) :
    Set (CutoffSample d) :=
  {omega | ∃ h : ℕ, j ≤ h ∧ ¬ scaleSeparationGood M m E b h omega}

theorem scaleSeparationFail_eq (M : ABKModel d) (m : ℤ) (E b : ℝ) {j : ℕ}
    (hj : 1 ≤ j) :
    scaleSeparationFail M m E b j =
      {omega | ¬ (1 ≤ hsep M m E b omega ∧ hsep M m E b omega ≤ j)} := by
  ext omega
  simp only [scaleSeparationFail, Set.mem_ofPred_eq]
  rw [← mem_hsepSet_iff_hsep_le (M := M) (m := m) (E := E) (b := b) (omega := omega)]
  constructor
  · rintro ⟨h, hh, hbad⟩ hmem
    exact hbad (hmem.2 h hh)
  · intro hmem
    by_contra hcon
    push Not at hcon
    exact hmem ⟨hj, hcon⟩

/-- The geometric constant of the union bound over `h >= j`.  It is **not**
dimension-only: it diverges as `(1-sigma) b -> 0`. -/
def hsepTailConst (sigma b : ℝ) : ℝ :=
  (1 - Real.exp (-((1 - sigma) * b * Real.log 3)))⁻¹ +
    (1 - Real.exp (-((1 / 2 : ℝ) * Real.log 3)))⁻¹

theorem two_le_hsepTailConst {sigma b : ℝ} (hsigma : sigma ≤ 1 / 2) (hb0 : 0 < b) :
    2 ≤ hsepTailConst sigma b := by
  have h1 : (0 : ℝ) < (1 - sigma) * b * Real.log 3 := by
    have : (0 : ℝ) < 1 - sigma := by linarith
    have := log_three_pos
    positivity
  have h2 : (0 : ℝ) < (1 / 2 : ℝ) * Real.log 3 := by
    have := log_three_pos
    positivity
  have := one_le_inv_one_sub_exp_neg h1
  have := one_le_inv_one_sub_exp_neg h2
  rw [hsepTailConst]
  linarith

/-- **The tail of the minimal scale separation** (ABK26).  The union bound over `h
>= j` of the two conclusions of `l.percolation.bad.clusters`:

```
P[ some scale h >= j fails ]  <=  C(sigma,b) exp(-3^{(1-sigma) b j}) ,
```

and, by `scaleSeparationFail_eq`, the left-hand side is exactly
`P[ not (hsep is meaningful and hsep <= j) ]`. -/
theorem measureReal_scaleSeparationFail_le_of_gates (M : ABKModel d) {m : ℤ}
    {E sigma b : ℝ} (hd : 2 ≤ d) (hE : 1 ≤ E)
    (hS : Algsuperdiff.Frozen.Section3.inductionState M (m - 1) ⟨E, hE⟩)
    (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2) (hb0 : 0 < b) (hb1 : b ≤ 1 / 8)
    (hEexp : Real.exp (badClustersConst d / sigma) ≤ E)
    (hE4 : 4 ≤ E) (hunit : BadEvents.unitGate M) (hgamma20 : M.gamma ≤ 1 / 20)
    (hinvSq : E⁻¹ ^ 2 ≤ Algsuperdiff.Section3.Disorder.cstar M)
    (hEb : badClustersConst d / b ≤ E)
    (hgamma : M.gamma ≤ E ^ (-5 : ℤ)) {j : ℕ} (hj : 1 ≤ j) :
    (cutoffSampleLaw M).toMeasure.real (scaleSeparationFail M m E b j) ≤
      hsepTailConst sigma b * Real.exp (-((3 : ℝ) ^ ((1 - sigma) * b * (j : ℝ)))) := by
  classical
  have hsigma1 : (0 : ℝ) < 1 - sigma := by linarith
  have halpha : (0 : ℝ) < (1 - sigma) * b := mul_pos hsigma1 hb0
  have hhalf : (0 : ℝ) < (1 / 2 : ℝ) := by norm_num
  -- the two per-scale conclusions of `l.percolation.bad.clusters`
  have hdiam : ∀ k : ℕ,
      (cutoffSampleLaw M).toMeasure.real (badClusterDiamFail M m b (j + k)) ≤
        Real.exp (-(3 : ℝ) ^ ((1 - sigma) * b * ((j : ℝ) + (k : ℝ)))) := by
    intro k
    refine le_trans (measureReal_maxBadClusterDiam_le_exp_of_gates M (j + k) hd
      (by omega) hE hS hsigma0 hsigma hb0 hb1 hEexp hE4 hunit hgamma20 hinvSq hEb hgamma)
      (le_of_eq ?_)
    push_cast
    ring_nf
  have hdens : ∀ k : ℕ,
      (cutoffSampleLaw M).toMeasure.real (badExtendedDensityFail M m E (j + k)) ≤
        Real.exp (-(3 : ℝ) ^ ((1 / 2 : ℝ) * ((j : ℝ) + (k : ℝ)))) := by
    intro k
    refine le_trans (measureReal_badExtendedDensity_gt_le_exp_of_gates M (j + k) hd
      (by omega) hE hS hsigma0 hsigma hb0 hb1 hEexp hE4 hunit hgamma20 hinvSq hEb hgamma)
      (le_of_eq ?_)
    push_cast
    ring_nf
  have hsum1 := summable_exp_neg_three_rpow halpha j
  have hsum2 := summable_exp_neg_three_rpow hhalf j
  have hsum : Summable fun k : ℕ =>
      Real.exp (-(3 : ℝ) ^ ((1 - sigma) * b * ((j : ℝ) + (k : ℝ)))) +
        Real.exp (-(3 : ℝ) ^ ((1 / 2 : ℝ) * ((j : ℝ) + (k : ℝ)))) :=
    hsum1.add hsum2
  have hcover : scaleSeparationFail M m E b j ⊆
      ⋃ k : ℕ, (badClusterDiamFail M m b (j + k) ∪
        badExtendedDensityFail M m E (j + k)) := by
    rintro omega ⟨h, hh, hbad⟩
    refine Set.mem_iUnion.2 ⟨h - j, ?_⟩
    have hjk : j + (h - j) = h := by omega
    rw [hjk]
    exact notGood_subset_union M m E b h hbad
  have hbound : (cutoffSampleLaw M).toMeasure (scaleSeparationFail M m E b j) ≤
      ENNReal.ofReal (∑' k : ℕ,
        (Real.exp (-(3 : ℝ) ^ ((1 - sigma) * b * ((j : ℝ) + (k : ℝ)))) +
          Real.exp (-(3 : ℝ) ^ ((1 / 2 : ℝ) * ((j : ℝ) + (k : ℝ)))))) := by
    refine le_trans (measure_mono hcover) ?_
    rw [ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) hsum]
    refine le_trans (measure_iUnion_le _) (ENNReal.tsum_le_tsum fun k => ?_)
    refine le_trans (measure_union_le _ _) ?_
    have hfin1 : (cutoffSampleLaw M).toMeasure (badClusterDiamFail M m b (j + k)) ≠ ⊤ :=
      measure_ne_top _ _
    have hfin2 : (cutoffSampleLaw M).toMeasure (badExtendedDensityFail M m E (j + k)) ≠ ⊤ :=
      measure_ne_top _ _
    rw [← ENNReal.ofReal_toReal hfin1, ← ENNReal.ofReal_toReal hfin2,
      ← ENNReal.ofReal_add ENNReal.toReal_nonneg ENNReal.toReal_nonneg]
    exact ENNReal.ofReal_le_ofReal (add_le_add (hdiam k) (hdens k))
  have hmono : (3 : ℝ) ^ ((1 - sigma) * b * (j : ℝ)) ≤ (3 : ℝ) ^ ((1 / 2 : ℝ) * (j : ℝ)) := by
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    have hjn : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    have hab : (1 - sigma) * b ≤ (1 / 2 : ℝ) := by
      nlinarith [mul_le_mul_of_nonneg_right (show (1 : ℝ) - sigma ≤ 1 by linarith) hb0.le]
    exact mul_le_mul_of_nonneg_right hab hjn
  have hfinal : (∑' k : ℕ,
      (Real.exp (-(3 : ℝ) ^ ((1 - sigma) * b * ((j : ℝ) + (k : ℝ)))) +
        Real.exp (-(3 : ℝ) ^ ((1 / 2 : ℝ) * ((j : ℝ) + (k : ℝ)))))) ≤
      hsepTailConst sigma b * Real.exp (-((3 : ℝ) ^ ((1 - sigma) * b * (j : ℝ)))) := by
    rw [hsum1.tsum_add hsum2]
    have h1 := tsum_exp_neg_three_rpow_le halpha j
    have h2 := tsum_exp_neg_three_rpow_le hhalf j
    have h3 : Real.exp (-(3 : ℝ) ^ ((1 / 2 : ℝ) * (j : ℝ))) ≤
        Real.exp (-(3 : ℝ) ^ ((1 - sigma) * b * (j : ℝ))) :=
      Real.exp_le_exp.2 (by linarith)
    have h4 : (0 : ℝ) ≤ (1 - Real.exp (-((1 / 2 : ℝ) * Real.log 3)))⁻¹ := by
      have := one_le_inv_one_sub_exp_neg (mul_pos hhalf log_three_pos)
      linarith
    rw [hsepTailConst]
    nlinarith [h1, h2, h3, h4, Real.exp_pos (-(3 : ℝ) ^ ((1 - sigma) * b * (j : ℝ)))]
  calc (cutoffSampleLaw M).toMeasure.real (scaleSeparationFail M m E b j)
      = ((cutoffSampleLaw M).toMeasure (scaleSeparationFail M m E b j)).toReal := rfl
    _ ≤ (ENNReal.ofReal (∑' k : ℕ,
          (Real.exp (-(3 : ℝ) ^ ((1 - sigma) * b * ((j : ℝ) + (k : ℝ)))) +
            Real.exp (-(3 : ℝ) ^ ((1 / 2 : ℝ) * ((j : ℝ) + (k : ℝ))))))).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
    _ = ∑' k : ℕ,
          (Real.exp (-(3 : ℝ) ^ ((1 - sigma) * b * ((j : ℝ) + (k : ℝ)))) +
            Real.exp (-(3 : ℝ) ^ ((1 / 2 : ℝ) * ((j : ℝ) + (k : ℝ))))) :=
        ENNReal.toReal_ofReal (tsum_nonneg fun k => by positivity)
    _ ≤ hsepTailConst sigma b * Real.exp (-((3 : ℝ) ^ ((1 - sigma) * b * (j : ℝ)))) := hfinal


/-- **`hsep` is almost surely well defined.**  The event on which no admissible
scale separation exists — the event carrying the junk value `sInf empty = 0` —
is null.  This is the well-definedness that the manuscript's `max` convention
silently assumes. -/
theorem measureReal_hsepSet_not_nonempty_of_gates (M : ABKModel d) {m : ℤ}
    {E sigma b : ℝ} (hd : 2 ≤ d) (hE : 1 ≤ E)
    (hS : Algsuperdiff.Frozen.Section3.inductionState M (m - 1) ⟨E, hE⟩)
    (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2) (hb0 : 0 < b) (hb1 : b ≤ 1 / 8)
    (hEexp : Real.exp (badClustersConst d / sigma) ≤ E)
    (hE4 : 4 ≤ E) (hunit : BadEvents.unitGate M) (hgamma20 : M.gamma ≤ 1 / 20)
    (hinvSq : E⁻¹ ^ 2 ≤ Algsuperdiff.Section3.Disorder.cstar M)
    (hEb : badClustersConst d / b ≤ E)
    (hgamma : M.gamma ≤ E ^ (-5 : ℤ)) :
    (cutoffSampleLaw M).toMeasure.real
      {omega | ¬ (hsepSet M m E b omega).Nonempty} = 0 := by
  classical
  have hsigma1 : (0 : ℝ) < 1 - sigma := by linarith
  have halpha : (0 : ℝ) < (1 - sigma) * b := mul_pos hsigma1 hb0
  have hr0 : (0 : ℝ) ≤ Real.exp (-((1 - sigma) * b * Real.log 3)) := (Real.exp_pos _).le
  have hr1 : Real.exp (-((1 - sigma) * b * Real.log 3)) < 1 :=
    exp_neg_lt_one (mul_pos halpha log_three_pos)
  have hnonneg : (0 : ℝ) ≤ (cutoffSampleLaw M).toMeasure.real
      {omega | ¬ (hsepSet M m E b omega).Nonempty} := measureReal_nonneg
  have hstep : ∀ j : ℕ, 1 ≤ j →
      (cutoffSampleLaw M).toMeasure.real {omega | ¬ (hsepSet M m E b omega).Nonempty} ≤
        hsepTailConst sigma b * Real.exp (-1) *
          Real.exp (-((1 - sigma) * b * Real.log 3)) ^ j := by
    intro j hjj
    have hsub : {omega : CutoffSample d | ¬ (hsepSet M m E b omega).Nonempty} ⊆
        scaleSeparationFail M m E b j := by
      intro omega homega
      rw [scaleSeparationFail_eq M m E b hjj]
      intro hcon
      exact homega (one_le_hsep_iff.1 hcon.1)
    refine le_trans (measureReal_mono hsub) ?_
    refine le_trans (measureReal_scaleSeparationFail_le_of_gates M hd hE hS hsigma0 hsigma
      hb0 hb1 hEexp hE4 hunit hgamma20 hinvSq hEb hgamma hjj) ?_
    have hgeom := exp_neg_three_rpow_le_geom halpha 0 j
    have hzero : ((0 : ℕ) : ℝ) = 0 := by norm_num
    rw [hzero] at hgeom
    have hone : (3 : ℝ) ^ ((1 - sigma) * b * (0 : ℝ)) = 1 := by
      rw [mul_zero, Real.rpow_zero]
    rw [hone] at hgeom
    have hcast : (0 : ℝ) + (j : ℝ) = (j : ℝ) := by ring
    rw [hcast] at hgeom
    have hCpos : (0 : ℝ) ≤ hsepTailConst sigma b := by
      have := two_le_hsepTailConst hsigma hb0
      linarith
    calc hsepTailConst sigma b * Real.exp (-((3 : ℝ) ^ ((1 - sigma) * b * (j : ℝ))))
        ≤ hsepTailConst sigma b * (Real.exp (-1) *
            Real.exp (-((1 - sigma) * b * Real.log 3)) ^ j) :=
          mul_le_mul_of_nonneg_left hgeom hCpos
      _ = hsepTailConst sigma b * Real.exp (-1) *
            Real.exp (-((1 - sigma) * b * Real.log 3)) ^ j := by ring
  have hlim : Filter.Tendsto
      (fun j : ℕ => hsepTailConst sigma b * Real.exp (-1) *
        Real.exp (-((1 - sigma) * b * Real.log 3)) ^ j) Filter.atTop (nhds 0) := by
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).const_mul
      (hsepTailConst sigma b * Real.exp (-1))
    simpa using h
  have hle : (cutoffSampleLaw M).toMeasure.real
      {omega | ¬ (hsepSet M m E b omega).Nonempty} ≤ 0 := by
    refine ge_of_tendsto hlim ?_
    filter_upwards [Filter.eventually_ge_atTop 1] with j hjj
    exact hstep j hjj
  linarith


/-! ## `e.hsep.tails` -/

/-- The amplitude of the `Gamma_{1-sigma}` bound of `e.hsep.tails`.  The manuscript
prints the amplitude `1`; the union bound of its own proof supports only a
constant absorbing `hsepTailConst`. -/
def hsepAmplitude (sigma b : ℝ) : ℝ :=
  3 + 2 * (1 + Real.log (hsepTailConst sigma b)) ^ 2

/-! ### The amplitude arithmetic

Two purely real-analytic steps, isolated so that neither elaboration exceeds the
default heartbeat budget. -/

/-- The gain of the union bound at the level `j` attached to `t`: with
`A = hsepAmplitude sigma b` and `j` the floor of `log(A t) / (b log 3)`,

```
(1 + log C) t^{1-sigma}  <=  3^{(1-sigma) b j} ,      C = hsepTailConst sigma b .
```
-/
private theorem le_three_rpow_gain {sigma b t : ℝ} {j : ℕ}
    (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2) (hb0 : 0 < b) (hb1 : b ≤ 1 / 8)
    (ht : 1 ≤ t)
    (hj : Real.log (hsepAmplitude sigma b * t) / (b * Real.log 3) < (j : ℝ) + 1) :
    (1 + Real.log (hsepTailConst sigma b)) * t ^ (1 - sigma) ≤
      (3 : ℝ) ^ ((1 - sigma) * b * (j : ℝ)) := by
  have hlog3 := log_three_pos
  have hsigma1 : (0 : ℝ) < 1 - sigma := by linarith
  have hC2 : 2 ≤ hsepTailConst sigma b := two_le_hsepTailConst hsigma hb0
  have hlogC : (0 : ℝ) ≤ Real.log (hsepTailConst sigma b) :=
    Real.log_nonneg (by linarith)
  have hu1 : (1 : ℝ) ≤ 1 + Real.log (hsepTailConst sigma b) := by linarith
  have hA : hsepAmplitude sigma b =
      3 + 2 * (1 + Real.log (hsepTailConst sigma b)) ^ 2 := rfl
  have hA3 : (3 : ℝ) ≤ hsepAmplitude sigma b := by
    rw [hA]; nlinarith [sq_nonneg (1 + Real.log (hsepTailConst sigma b))]
  have hA1 : (1 : ℝ) ≤ hsepAmplitude sigma b := by linarith
  have hApos : (0 : ℝ) < hsepAmplitude sigma b := by linarith
  have ht0 : (0 : ℝ) < t := by linarith
  have hAtpos : (0 : ℝ) < hsepAmplitude sigma b * t := mul_pos hApos ht0
  have hbj : Real.log (hsepAmplitude sigma b * t) / Real.log 3 - b ≤ b * (j : ℝ) := by
    have hmul : b * (Real.log (hsepAmplitude sigma b * t) / (b * Real.log 3)) <
        b * ((j : ℝ) + 1) := mul_lt_mul_of_pos_left hj hb0
    have hid : b * (Real.log (hsepAmplitude sigma b * t) / (b * Real.log 3)) =
        Real.log (hsepAmplitude sigma b * t) / Real.log 3 := by
      field_simp
    rw [hid] at hmul
    linarith
  have hlow : Real.exp ((1 - sigma) *
      (Real.log (hsepAmplitude sigma b * t) - b * Real.log 3)) ≤
      (3 : ℝ) ^ ((1 - sigma) * b * (j : ℝ)) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
    refine Real.exp_le_exp.2 ?_
    have hmul := mul_le_mul_of_nonneg_left hbj (mul_pos hsigma1 hlog3).le
    have hid : (1 - sigma) * Real.log 3 *
        (Real.log (hsepAmplitude sigma b * t) / Real.log 3 - b) =
        (1 - sigma) * (Real.log (hsepAmplitude sigma b * t) - b * Real.log 3) := by
      field_simp
    rw [hid] at hmul
    linarith
  have hsplit : Real.exp ((1 - sigma) *
      (Real.log (hsepAmplitude sigma b * t) - b * Real.log 3)) =
      (hsepAmplitude sigma b * t) ^ (1 - sigma) *
        Real.exp (-((1 - sigma) * (b * Real.log 3))) := by
    rw [Real.rpow_def_of_pos hAtpos, ← Real.exp_add]
    congr 1
    ring
  have hquart : (3 : ℝ) / 4 ≤ Real.exp (-((1 - sigma) * (b * Real.log 3))) := by
    have hsmall : (1 - sigma) * (b * Real.log 3) ≤ 1 / 4 := by
      have h1 : b * Real.log 3 ≤ (1 / 8 : ℝ) * 2 :=
        mul_le_mul hb1 log_three_le_two hlog3.le (by norm_num)
      have h2 : (1 - sigma) * (b * Real.log 3) ≤ 1 * (b * Real.log 3) :=
        mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hb0.le hlog3.le)
      linarith
    linarith [Real.add_one_le_exp (-((1 - sigma) * (b * Real.log 3)))]
  have hmulrpow : (hsepAmplitude sigma b * t) ^ (1 - sigma) =
      hsepAmplitude sigma b ^ (1 - sigma) * t ^ (1 - sigma) :=
    Real.mul_rpow hApos.le ht0.le
  have ht1 : (1 : ℝ) ≤ t ^ (1 - sigma) := Real.one_le_rpow ht (by linarith)
  have hsq : ((4 / 3 : ℝ) * (1 + Real.log (hsepTailConst sigma b))) ^ (2 : ℝ) ≤
      hsepAmplitude sigma b := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, hA]
    nlinarith [hu1]
  have hroot : (4 / 3 : ℝ) * (1 + Real.log (hsepTailConst sigma b)) ≤
      hsepAmplitude sigma b ^ ((1 : ℝ) / 2) := by
    have h0 : (0 : ℝ) ≤ (4 / 3 : ℝ) * (1 + Real.log (hsepTailConst sigma b)) := by
      linarith
    have h := Real.rpow_le_rpow (by positivity) hsq (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 2)
    rwa [← Real.rpow_mul h0, show (2 : ℝ) * ((1 : ℝ) / 2) = 1 by norm_num,
      Real.rpow_one] at h
  have hexpo : hsepAmplitude sigma b ^ ((1 : ℝ) / 2) ≤
      hsepAmplitude sigma b ^ (1 - sigma) :=
    Real.rpow_le_rpow_of_exponent_le hA1 (by linarith)
  have hAge : (4 / 3 : ℝ) * (1 + Real.log (hsepTailConst sigma b)) ≤
      hsepAmplitude sigma b ^ (1 - sigma) := le_trans hroot hexpo
  have hApow : (0 : ℝ) ≤ hsepAmplitude sigma b ^ (1 - sigma) :=
    Real.rpow_nonneg hApos.le _
  have hstep1 : (4 / 3 : ℝ) * (1 + Real.log (hsepTailConst sigma b)) * t ^ (1 - sigma) ≤
      hsepAmplitude sigma b ^ (1 - sigma) * t ^ (1 - sigma) :=
    mul_le_mul_of_nonneg_right hAge (by linarith)
  have hstep2 : ((4 / 3 : ℝ) * (1 + Real.log (hsepTailConst sigma b)) *
        t ^ (1 - sigma)) * ((3 : ℝ) / 4) ≤
      (hsepAmplitude sigma b ^ (1 - sigma) * t ^ (1 - sigma)) *
        Real.exp (-((1 - sigma) * (b * Real.log 3))) :=
    mul_le_mul hstep1 hquart (by norm_num) (by positivity)
  rw [hsplit, hmulrpow] at hlow
  linarith

/-- The closing step: the tail constant is absorbed by the amplitude gain. -/
private theorem const_mul_exp_le_exp {sigma b t : ℝ} {j : ℕ}
    (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2) (hb0 : 0 < b) (ht : 1 ≤ t)
    (hgain : (1 + Real.log (hsepTailConst sigma b)) * t ^ (1 - sigma) ≤
      (3 : ℝ) ^ ((1 - sigma) * b * (j : ℝ))) :
    hsepTailConst sigma b * Real.exp (-((3 : ℝ) ^ ((1 - sigma) * b * (j : ℝ)))) ≤
      Real.exp (-(t ^ (1 - sigma))) := by
  have hC2 : 2 ≤ hsepTailConst sigma b := two_le_hsepTailConst hsigma hb0
  have hCpos : (0 : ℝ) < hsepTailConst sigma b := by linarith
  have hlogC : (0 : ℝ) ≤ Real.log (hsepTailConst sigma b) :=
    Real.log_nonneg (by linarith)
  have ht1 : (1 : ℝ) ≤ t ^ (1 - sigma) := Real.one_le_rpow ht (by linarith)
  have hmul : Real.log (hsepTailConst sigma b) * 1 ≤
      Real.log (hsepTailConst sigma b) * t ^ (1 - sigma) :=
    mul_le_mul_of_nonneg_left ht1 hlogC
  have hstep : t ^ (1 - sigma) + Real.log (hsepTailConst sigma b) ≤
      (3 : ℝ) ^ ((1 - sigma) * b * (j : ℝ)) := by linarith
  have hmono : Real.exp (-((3 : ℝ) ^ ((1 - sigma) * b * (j : ℝ)))) ≤
      Real.exp (-(t ^ (1 - sigma) + Real.log (hsepTailConst sigma b))) :=
    Real.exp_le_exp.2 (by linarith)
  have hCne : hsepTailConst sigma b ≠ 0 := ne_of_gt hCpos
  have hid : hsepTailConst sigma b *
      Real.exp (-(t ^ (1 - sigma) + Real.log (hsepTailConst sigma b))) =
      Real.exp (-(t ^ (1 - sigma))) := by
    have hsplit : Real.exp (-(t ^ (1 - sigma) + Real.log (hsepTailConst sigma b))) =
        Real.exp (-(t ^ (1 - sigma))) * (hsepTailConst sigma b)⁻¹ := by
      rw [show -(t ^ (1 - sigma) + Real.log (hsepTailConst sigma b)) =
        -(t ^ (1 - sigma)) + -Real.log (hsepTailConst sigma b) by ring, Real.exp_add]
      congr 1
      rw [Real.exp_neg, Real.exp_log hCpos]
    rw [hsplit, mul_comm (Real.exp (-(t ^ (1 - sigma)))) (hsepTailConst sigma b)⁻¹,
      ← mul_assoc, mul_inv_cancel₀ hCne, one_mul]
  calc hsepTailConst sigma b * Real.exp (-((3 : ℝ) ^ ((1 - sigma) * b * (j : ℝ))))
      ≤ hsepTailConst sigma b *
          Real.exp (-(t ^ (1 - sigma) + Real.log (hsepTailConst sigma b))) :=
        mul_le_mul_of_nonneg_left hmono hCpos.le
    _ = Real.exp (-(t ^ (1 - sigma))) := hid

/-- **ABK26 `e.hsep.tails`** at the explicit amplitude:

```
3^{b hsep}  <=  O_{Gamma_{1-sigma}}( hsepAmplitude sigma b ) ,
```

i.e. `P[ 3^{b hsep} > hsepAmplitude sigma b * s ] <= exp(-s^{1-sigma})` for
every `s >= 1`. -/
theorem isBigOWith_gammaSigma_three_rpow_hsep_of_gates (M : ABKModel d) {m : ℤ}
    {E sigma b : ℝ} (hd : 2 ≤ d) (hE : 1 ≤ E)
    (hS : Algsuperdiff.Frozen.Section3.inductionState M (m - 1) ⟨E, hE⟩)
    (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2) (hb0 : 0 < b) (hb1 : b ≤ 1 / 8)
    (hEexp : Real.exp (badClustersConst d / sigma) ≤ E)
    (hE4 : 4 ≤ E) (hunit : BadEvents.unitGate M) (hgamma20 : M.gamma ≤ 1 / 20)
    (hinvSq : E⁻¹ ^ 2 ≤ Algsuperdiff.Section3.Disorder.cstar M)
    (hEb : badClustersConst d / b ≤ E)
    (hgamma : M.gamma ≤ E ^ (-5 : ℤ)) :
    HCPolySupport.IndependentSums.IsBigOWith (cutoffSampleLaw M).toMeasure
      (HCPolySupport.IndependentSums.gammaSigma (1 - sigma))
      (fun omega => (3 : ℝ) ^ (b * (hsep M m E b omega : ℝ)))
      (hsepAmplitude sigma b) := by
  classical
  intro t ht
  have hlog3 := log_three_pos
  have hC2 : 2 ≤ hsepTailConst sigma b := two_le_hsepTailConst hsigma hb0
  have hlogC : (0 : ℝ) ≤ Real.log (hsepTailConst sigma b) :=
    Real.log_nonneg (by linarith)
  have hA : hsepAmplitude sigma b =
      3 + 2 * (1 + Real.log (hsepTailConst sigma b)) ^ 2 := rfl
  have hA3 : (3 : ℝ) ≤ hsepAmplitude sigma b := by
    rw [hA]; nlinarith [sq_nonneg (1 + Real.log (hsepTailConst sigma b))]
  have hApos : (0 : ℝ) < hsepAmplitude sigma b := by linarith
  have ht0 : (0 : ℝ) < t := by linarith
  have hAt : (3 : ℝ) ≤ hsepAmplitude sigma b * t := by nlinarith
  have hAtpos : (0 : ℝ) < hsepAmplitude sigma b * t := by linarith
  have hden : (0 : ℝ) < b * Real.log 3 := mul_pos hb0 hlog3
  obtain ⟨L, hL⟩ : ∃ L : ℝ,
      L = Real.log (hsepAmplitude sigma b * t) / (b * Real.log 3) := ⟨_, rfl⟩
  have hlogAt : Real.log 3 ≤ Real.log (hsepAmplitude sigma b * t) :=
    Real.log_le_log (by norm_num) hAt
  have hL1 : (1 : ℝ) ≤ L := by
    rw [hL, le_div_iff₀ hden]
    nlinarith [mul_le_mul_of_nonneg_right hb1 hlog3.le, hlogAt]
  have hL0 : (0 : ℝ) ≤ L := by linarith
  obtain ⟨j, hjdef⟩ : ∃ j : ℕ, j = ⌊L⌋₊ := ⟨_, rfl⟩
  have hj1 : 1 ≤ j := by
    rw [hjdef]
    exact Nat.le_floor (by exact_mod_cast hL1)
  have hjle : (j : ℝ) ≤ L := by rw [hjdef]; exact Nat.floor_le hL0
  have hjgt : L < (j : ℝ) + 1 := by rw [hjdef]; exact Nat.lt_floor_add_one L
  have hsub : HCPolySupport.IndependentSums.upperTailEvent
      (fun omega => (3 : ℝ) ^ (b * (hsep M m E b omega : ℝ)))
      (hsepAmplitude sigma b * t) ⊆ scaleSeparationFail M m E b j := by
    intro omega homega
    have hlt : hsepAmplitude sigma b * t <
        (3 : ℝ) ^ (b * (hsep M m E b omega : ℝ)) := homega
    have hlog : Real.log (hsepAmplitude sigma b * t) <
        b * (hsep M m E b omega : ℝ) * Real.log 3 := by
      have h := Real.log_lt_log hAtpos hlt
      rwa [Real.log_rpow (by norm_num : (0 : ℝ) < 3)] at h
    have hLlt : L < (hsep M m E b omega : ℝ) := by
      rw [hL, div_lt_iff₀ hden]
      linarith
    have hjlt : j < hsep M m E b omega := by
      have hcast : (j : ℝ) < (hsep M m E b omega : ℝ) := lt_of_le_of_lt hjle hLlt
      exact_mod_cast hcast
    rw [scaleSeparationFail_eq M m E b hj1]
    intro hcon
    omega
  have hbound := measureReal_scaleSeparationFail_le_of_gates M hd hE hS hsigma0 hsigma hb0
    hb1 hEexp hE4 hunit hgamma20 hinvSq hEb hgamma hj1
  have hgain : (1 + Real.log (hsepTailConst sigma b)) * t ^ (1 - sigma) ≤
      (3 : ℝ) ^ ((1 - sigma) * b * (j : ℝ)) :=
    le_three_rpow_gain hsigma0 hsigma hb0 hb1 ht (by rw [← hL]; exact hjgt)
  rw [HCPolySupport.IndependentSums.gammaSigma_inv]
  exact le_trans (le_trans (measureReal_mono hsub) hbound)
    (const_mul_exp_le_exp hsigma0 hsigma hb0 ht hgain)


end

end Algsuperdiff.Section3.Provider.Percolation
