/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Probability.ShellActiveSigma
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Support.Events

/-!
# AnnulusSeparation

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The annulus-separation count of ABK26's per-scale atoms

ABK26 asserts three times that a family of per-scale atoms is `2`-dependent,
with no argument.  This module supplies the count, over this repository's
carriers and at this repository's separation predicate `SeparatedBy` (Euclidean
`vecNorm`), in the form the varying-level independence producer
`iIndepFun_of_local_cutoffSample` consumes.

## The geometry

The `G_0` atom `Y_n` reads the field on the annulus `Box_n \ Box_{n-1}` through
the truncation `a_{n-2}`, so its truncation level is `Lidx n = n - 2`.  Two
indices `n' < n` share only the shells `i <= n' - 2`, whose range of dependence
is `sqrt d * 3 ^ (n' - 2) = sqrt d * 3 ^ (min (Lidx n) (Lidx n'))` -- exactly
the threshold at which `iIndep_lowerShellLocalSigma_of_varyingLevel` and its
observable consequence are stated.  The `G_2` atom `X_j` reads cubes `z +
Box_n` at the field `a_{n-2}` with `n <= j - 1`, i.e. at truncation level `<= j
- 3`; the same count runs at that offset.  Both offsets are covered here by the
free integer parameter `c` of `separatedBy_annulusRegion_of_gap`.

## The count

```
dist(annulus n, annulus n') >= 1/2 * 3^(n-1) - 1/2 * 3^(n')     (coordinate gap)
1/2 * 3^(n-1) - 1/2 * 3^(n') >= sqrt d * 3^(n'-c)
                                        <== 3 + 2*3^(1-c)*sqrt d <= 3^(n-n')
```

so the atoms are `r`-dependent for every `r >= 1` with
`3 + 2*3^(1-c)*sqrt d <= 3 ^ r`, i.e. for
`r(d) = max {2, ceil (log_3 (3 + 2*3^(1-c)*sqrt d))}`.

## The metric: Euclidean versus sup, and the honest constants

This repository's `SeparatedBy` is stated at the **Euclidean**
`Homogenization.Book.Ch02.vecNorm`, because that is the spelling of
`Frozen.Assumptions.ShellLawJ1.range_dependence`.  **The constants do not
change.**  The lower bound used here is the single-coordinate bound `|x i - y
i| <= vecNorm (x - y)`, which is the sup-metric gap; and the gap is *attained*
in the Euclidean metric as well (take `x`, `y` on a common coordinate axis), so
no Euclidean improvement of `3 + 2*3^(1-c)*sqrt d` is available from the
annuli's geometry.  The count is therefore identical to the sup-metric one, and
it is sharp for this argument.

## The dimension caveat

At the offset `c = 2` of the `G_0` lane, `r = 2` requires
`3 + (2/3) sqrt d <= 9`, i.e. `sqrt d <= 9`, i.e. **`d <= 81`**.
Beyond that dimension the count is not
`r = 2` but `r(d)` above, which `separatedBy_annulusRegion_of_gap` delivers at
every `r`.  This dimension caveat comes entirely from the `sqrt d` in the
shells' range of dependence, which the manuscript's per-scale display drops.

## Main definitions

* `annulusRegion d n` -- the closed sup-norm annulus
  `{x : 1/2*3^(n-1) <= |x|_inf <= 1/2*3^n}`, the region read by the per-scale
  atom at index `n`.

## Main results

* `separatedBy_of_coordinate_gap` -- the workhorse: a coordinate gap between
  two regions is a `SeparatedBy` bound.
* `separatedBy_annulusRegion_of_gap` -- the `r(d)` count at a free truncation
  offset `c`.
* `mem_annulusRegion_of_le_triadicLatticePoint` -- the *no-enlargement* fact:
  a cube `z + Box_j` centred at a triadic lattice point `z` of the open annulus,
  with `j <= n - 1`, is still contained in `annulusRegion d n`.  This is what
  makes the count above consumable with no fattening of the annuli.
-/

namespace Algsuperdiff.Section4.Probability

open MeasureTheory
open HCPolySupport
open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

/-! ## Coordinate bounds for the Euclidean norm -/

/-- Every coordinate is dominated by the Euclidean norm. -/
private theorem abs_apply_le_vecNorm (x : Vec d) (i : Fin d) :
    |x i| ≤ Book.Ch02.vecNorm x := by
  have h1 : x i ^ (2 : ℕ) ≤ vecNormSq x := sq_apply_le_vecNormSq x i
  have h2 : Book.Ch02.vecNorm x ^ 2 = vecNormSq x := Book.Ch02.vecNorm_sq_eq_vecNormSq x
  have hle : x i ^ 2 ≤ Book.Ch02.vecNorm x ^ 2 := by rw [h2]; exact h1
  calc |x i| = Real.sqrt (x i ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (Book.Ch02.vecNorm x ^ 2) := Real.sqrt_le_sqrt hle
    _ = Book.Ch02.vecNorm x := Real.sqrt_sq (Book.Ch02.vecNorm_nonneg x)

/-- The coordinate form of the previous bound on a difference. -/
private theorem abs_sub_apply_le_vecNorm_sub (x y : Vec d) (i : Fin d) :
    |x i - y i| ≤ Book.Ch02.vecNorm (x - y) := by
  simpa only [Pi.sub_apply] using abs_apply_le_vecNorm (x - y) i

/-- The Euclidean norm of a difference is symmetric. -/
theorem vecNorm_sub_comm (x y : Vec d) :
    Book.Ch02.vecNorm (x - y) = Book.Ch02.vecNorm (y - x) := by
  have hsq : vecNormSq (x - y) = vecNormSq (y - x) := by
    simp only [vecNormSq, vecDot]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.sub_apply]
    ring
  have h1 : Book.Ch02.vecNorm (x - y) ^ 2 = Book.Ch02.vecNorm (y - x) ^ 2 := by
    rw [Book.Ch02.vecNorm_sq_eq_vecNormSq, Book.Ch02.vecNorm_sq_eq_vecNormSq, hsq]
  calc Book.Ch02.vecNorm (x - y)
      = Real.sqrt (Book.Ch02.vecNorm (x - y) ^ 2) :=
        (Real.sqrt_sq (Book.Ch02.vecNorm_nonneg _)).symm
    _ = Real.sqrt (Book.Ch02.vecNorm (y - x) ^ 2) := by rw [h1]
    _ = Book.Ch02.vecNorm (y - x) := Real.sqrt_sq (Book.Ch02.vecNorm_nonneg _)

/-- Separation is symmetric. -/
theorem SeparatedBy.symm {r : ℝ} {U V : Set (Vec d)} (h : SeparatedBy r U V) :
    SeparatedBy r V U := by
  intro x y hx hy
  rw [vecNorm_sub_comm]
  exact h hy hx

/-- **Separation from a coordinate gap.**  If every point of `U` has some
coordinate of size at least `a`, and every point of `V` has all coordinates of
size at most `b`, then `U` and `V` are `(a - b)`-separated.  The bound used is
the sup-metric gap, which the Euclidean norm dominates. -/
theorem separatedBy_of_coordinate_gap {a b : ℝ} {U V : Set (Vec d)}
    (hU : ∀ x ∈ U, ∃ i, a ≤ |x i|) (hV : ∀ y ∈ V, ∀ i, |y i| ≤ b) :
    SeparatedBy (a - b) U V := by
  intro x y hx hy
  obtain ⟨i, hi⟩ := hU x hx
  have hyi : |y i| ≤ b := hV y hy i
  have hgap : |x i| - |y i| ≤ |x i - y i| := abs_sub_abs_le_abs_sub _ _
  have hcoord : |x i - y i| ≤ Book.Ch02.vecNorm (x - y) :=
    abs_sub_apply_le_vecNorm_sub x y i
  linarith only [hi, hyi, hgap, hcoord]

/-! ## The annulus -/

/-- **The annulus `closure(Box_n) \ Box_{n-1}`** in the sup norm of `Vec d`: the
region the per-scale atom at index `n` reads.  It is written in coordinates,
matching the coordinate definition of the triadic cubes. -/
def annulusRegion (d : ℕ) (n : ℤ) : Set (Vec d) :=
  {x | (∃ i, (1 / 2 : ℝ) * (3 : ℝ) ^ (n - 1) ≤ |x i|) ∧
    ∀ i, |x i| ≤ (1 / 2 : ℝ) * (3 : ℝ) ^ n}

theorem measurableSet_annulusRegion (d : ℕ) (n : ℤ) :
    MeasurableSet (annulusRegion d n) := by
  have hinner : ∀ i : Fin d, Measurable fun x : Vec d => |x i| := by
    intro i
    have hrw : (fun x : Vec d => |x i|) = fun x : Vec d => max (x i) (-(x i)) := by
      funext x
      exact abs_eq_max_neg
    rw [hrw]
    exact (measurable_pi_apply i).max (measurable_pi_apply i).neg
  have h1 : MeasurableSet
      {x : Vec d | ∃ i, (1 / 2 : ℝ) * (3 : ℝ) ^ (n - 1) ≤ |x i|} := by
    have hset : {x : Vec d | ∃ i, (1 / 2 : ℝ) * (3 : ℝ) ^ (n - 1) ≤ |x i|}
        = ⋃ i : Fin d, {x : Vec d | (1 / 2 : ℝ) * (3 : ℝ) ^ (n - 1) ≤ |x i|} := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    rw [hset]
    exact MeasurableSet.iUnion fun i => measurableSet_le measurable_const (hinner i)
  have h2 : MeasurableSet
      {x : Vec d | ∀ i, |x i| ≤ (1 / 2 : ℝ) * (3 : ℝ) ^ n} := by
    have hset : {x : Vec d | ∀ i, |x i| ≤ (1 / 2 : ℝ) * (3 : ℝ) ^ n}
        = ⋂ i : Fin d, {x : Vec d | |x i| ≤ (1 / 2 : ℝ) * (3 : ℝ) ^ n} := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    rw [hset]
    exact MeasurableSet.iInter fun i => measurableSet_le (hinner i) measurable_const
  exact h1.inter h2

/-! ## The `r(d)` arithmetic -/

/-- The pure-algebra core, over abstract reals: no `zpow` and no `Real.sqrt`
term is ever entered by a numeric tactic. -/
private theorem gap_algebra {s t w q : ℝ} (ht : 0 < t)
    (hgap : 3 + 6 * w * s ≤ q) :
    s * (t * w) ≤ 1 / 2 * (t * (q / 3)) - 1 / 2 * t := by
  have h := mul_le_mul_of_nonneg_left hgap ht.le
  linarith only [h]

/-- **The arithmetic core of the count.**  Under the gap condition
`3 + 2*3^(1-c)*sqrt d <= 3^(n-n')`, the annuli's coordinate gap
`1/2*3^(n-1) - 1/2*3^(n')` dominates the range of dependence
`sqrt d * 3^(n'-c)` of the coarsest **shared** shell. -/
theorem sqrt_mul_zpow_le_annulus_gap {c n n' : ℤ}
    (hgap : 3 + 2 * (3 : ℝ) ^ (1 - c) * Real.sqrt (d : ℝ) ≤ (3 : ℝ) ^ (n - n')) :
    Real.sqrt (d : ℝ) * (3 : ℝ) ^ (n' - c)
      ≤ (1 / 2 : ℝ) * (3 : ℝ) ^ (n - 1) - (1 / 2 : ℝ) * (3 : ℝ) ^ n' := by
  have h3 : (3 : ℝ) ≠ 0 := by norm_num
  have ht : (0 : ℝ) < (3 : ℝ) ^ n' := zpow_pos (by norm_num) n'
  have e1 : (3 : ℝ) ^ (n - 1) = (3 : ℝ) ^ n' * ((3 : ℝ) ^ (n - n') / 3) := by
    have h : (3 : ℝ) ^ (n - n' - 1) = (3 : ℝ) ^ (n - n') / 3 := by
      rw [zpow_sub₀ h3]; norm_num
    rw [← h, ← zpow_add₀ h3]
    congr 1
    ring
  have e2 : (3 : ℝ) ^ (n' - c) = (3 : ℝ) ^ n' * (3 : ℝ) ^ (-c) := by
    rw [← zpow_add₀ h3, sub_eq_add_neg]
  have e3 : (2 : ℝ) * (3 : ℝ) ^ (1 - c) = 6 * (3 : ℝ) ^ (-c) := by
    have h : (3 : ℝ) ^ (1 - c) = 3 * (3 : ℝ) ^ (-c) := by
      rw [show (1 : ℤ) - c = 1 + -c by ring, zpow_add₀ h3]
      norm_num
    rw [h]
    ring
  rw [e1, e2]
  refine gap_algebra ht ?_
  rw [← e3]
  exact hgap

/-! ## The separation of the annuli -/

/-- **The count, ordered form.**  For `n' < n` satisfying the gap condition, the
annuli are separated at the shared-shell threshold
`sqrt d * 3 ^ (min (n - c) (n' - c))` -- exactly the threshold consumed by
`iIndepFun_of_local_cutoffSample` at `Lidx m = m - c`. -/
theorem separatedBy_annulusRegion_of_lt {c n n' : ℤ} (hlt : n' < n)
    (hgap : 3 + 2 * (3 : ℝ) ^ (1 - c) * Real.sqrt (d : ℝ) ≤ (3 : ℝ) ^ (n - n')) :
    SeparatedBy (Real.sqrt (d : ℝ) * (3 : ℝ) ^ (min (n - c) (n' - c)))
      (annulusRegion d n) (annulusRegion d n') := by
  have hmin : min (n - c) (n' - c) = n' - c := min_eq_right (by omega)
  rw [hmin]
  intro x y hx hy
  refine le_trans (sqrt_mul_zpow_le_annulus_gap (d := d) hgap) ?_
  exact separatedBy_of_coordinate_gap (U := annulusRegion d n) (V := annulusRegion d n')
    (fun _ hx => hx.1) (fun _ hy => hy.2) hx hy

/-- **The `r(d)` count.**  If `r >= 1` and `3 + 2*3^(1-c)*sqrt d <= 3^r`, then
annuli whose indices differ by at least `r` are separated at the shared-shell
threshold `sqrt d * 3 ^ (min (n - c) (n' - c))`.  This is the honest form of
"the per-scale atoms are `r`-dependent", and it is exactly the `hsep` hypothesis
of `iIndepFun_of_local_cutoffSample` at `Lidx m = m - c`. -/
theorem separatedBy_annulusRegion_of_gap {c : ℤ} {r : ℕ} (hr1 : 1 ≤ r)
    (hr : 3 + 2 * (3 : ℝ) ^ (1 - c) * Real.sqrt (d : ℝ) ≤ (3 : ℝ) ^ (r : ℕ))
    {n n' : ℤ} (hgap : (r : ℤ) ≤ |n - n'|) :
    SeparatedBy (Real.sqrt (d : ℝ) * (3 : ℝ) ^ (min (n - c) (n' - c)))
      (annulusRegion d n) (annulusRegion d n') := by
  have hr1' : (1 : ℤ) ≤ (r : ℤ) := by exact_mod_cast hr1
  have key : ∀ m m' : ℤ, (r : ℤ) ≤ m - m' →
      3 + 2 * (3 : ℝ) ^ (1 - c) * Real.sqrt (d : ℝ) ≤ (3 : ℝ) ^ (m - m') := by
    intro m m' h
    refine le_trans hr ?_
    rw [← zpow_natCast (3 : ℝ) r]
    exact zpow_le_zpow_right₀ (by norm_num) h
  rcases lt_trichotomy n n' with hlt | heq | hgt
  · have hle : (r : ℤ) ≤ n' - n := by
      rw [abs_of_nonpos (by omega)] at hgap; omega
    have hs := SeparatedBy.symm
      (separatedBy_annulusRegion_of_lt (d := d) (c := c) hlt (key n' n hle))
    rwa [min_comm (n' - c) (n - c)] at hs
  · exfalso
    rw [heq] at hgap
    simp only [sub_self, abs_zero] at hgap
    omega
  · have hle : (r : ℤ) ≤ n - n' := by
      rw [abs_of_nonneg (by omega)] at hgap; omega
    exact separatedBy_annulusRegion_of_lt (d := d) (c := c) hgt (key n n' hle)

/-! ## The events' triadic geometry -/

/-- The integrality step behind the *no-enlargement* fact, upper half: a
multiple of `3^j` that lies strictly inside `Box_n` (`j <= n`) is at distance at
least `1/2 * 3^j` from `Box_n`'s boundary. -/
private theorem three_zpow_mul_le_of_lt {j n : ℤ} (hj : j ≤ n) {b : ℤ}
    (h : (3 : ℝ) ^ j * (b : ℝ) < (1 / 2 : ℝ) * (3 : ℝ) ^ n) :
    (3 : ℝ) ^ j * (b : ℝ) ≤ (1 / 2 : ℝ) * (3 : ℝ) ^ n - (1 / 2 : ℝ) * (3 : ℝ) ^ j := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, n = j + (k : ℤ) := ⟨(n - j).toNat, by omega⟩
  have h3j : (0 : ℝ) < (3 : ℝ) ^ j := zpow_pos (by norm_num) j
  have hn : (3 : ℝ) ^ n = (3 : ℝ) ^ j * (3 : ℝ) ^ (k : ℕ) := by
    rw [hk, zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_natCast]
  rw [hn] at h ⊢
  have hb : (2 : ℝ) * (b : ℝ) < (3 : ℝ) ^ (k : ℕ) :=
    lt_of_mul_lt_mul_left (a := (3 : ℝ) ^ j) (by linarith only [h]) h3j.le
  have hbz : 2 * b < (3 : ℤ) ^ k := by exact_mod_cast hb
  have hbz' : 2 * b ≤ (3 : ℤ) ^ k - 1 := by omega
  have hbr : (2 : ℝ) * (b : ℝ) ≤ (3 : ℝ) ^ (k : ℕ) - 1 := by exact_mod_cast hbz'
  have hscaled := mul_le_mul_of_nonneg_left hbr h3j.le
  linarith only [hscaled]

/-- The integrality step behind the *no-enlargement* fact, lower half: a
multiple of `3^j` outside `Box_n` (`j <= n`) is at distance at least
`1/2 * 3^j` from `Box_n`'s boundary, because `3^(n-j)` is odd. -/
private theorem le_three_zpow_mul_of_le {j n : ℤ} (hj : j ≤ n) {b : ℤ}
    (h : (1 / 2 : ℝ) * (3 : ℝ) ^ n ≤ (3 : ℝ) ^ j * (b : ℝ)) :
    (1 / 2 : ℝ) * (3 : ℝ) ^ n + (1 / 2 : ℝ) * (3 : ℝ) ^ j ≤ (3 : ℝ) ^ j * (b : ℝ) := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, n = j + (k : ℤ) := ⟨(n - j).toNat, by omega⟩
  have h3j : (0 : ℝ) < (3 : ℝ) ^ j := zpow_pos (by norm_num) j
  have hn : (3 : ℝ) ^ n = (3 : ℝ) ^ j * (3 : ℝ) ^ (k : ℕ) := by
    rw [hk, zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_natCast]
  rw [hn] at h ⊢
  have hb : (3 : ℝ) ^ (k : ℕ) ≤ (2 : ℝ) * (b : ℝ) :=
    le_of_mul_le_mul_left (a := (3 : ℝ) ^ j) (by linarith only [h]) h3j
  have hbz : (3 : ℤ) ^ k ≤ 2 * b := by exact_mod_cast hb
  obtain ⟨t, ht⟩ : Odd ((3 : ℤ) ^ k) := Odd.pow ⟨1, by norm_num⟩
  have hne : (3 : ℤ) ^ k ≠ 2 * b := by rw [ht]; omega
  have hbz' : (3 : ℤ) ^ k + 1 ≤ 2 * b :=
    Int.add_one_le_iff.mpr (lt_of_le_of_ne hbz hne)
  have hbr : (3 : ℝ) ^ (k : ℕ) + 1 ≤ (2 : ℝ) * (b : ℝ) := by exact_mod_cast hbz'
  have hscaled := mul_le_mul_of_nonneg_left hbr h3j.le
  linarith only [hscaled]

/-- **No enlargement of the annulus (the decisive geometric input).**  Let `z` be
a triadic lattice point of spacing `3^j` lying in the open annulus
`Box_n \ Box_{n-1}`, with `j <= n - 1`.  Then every point of the closed cube
`z + Box_j` is still in `annulusRegion d n`: the read cubes of the per-scale
atom *tile* the annulus and do not stick out of it.

This is the fact that lets `separatedBy_annulusRegion_of_gap` be applied to the
regions the `G_0` and `G_2` atoms actually read, with no fattening (and hence no
degradation of the `d`-range). -/
theorem mem_annulusRegion_of_le_triadicLatticePoint {j n : ℤ} (hj : j ≤ n - 1)
    {v : Fin d → ℤ}
    (hv : triadicLatticePoint j v ∈
      openCubeSet (originCube d n) \ openCubeSet (originCube d (n - 1)))
    {x : Vec d}
    (hx : ∀ i, |x i - triadicLatticePoint j v i| ≤ (1 / 2 : ℝ) * (3 : ℝ) ^ j) :
    x ∈ annulusRegion d n := by
  have h3j : (0 : ℝ) < (3 : ℝ) ^ j := zpow_pos (by norm_num) j
  have habs : ∀ i, |triadicLatticePoint j v i| = (3 : ℝ) ^ j * ((|v i| : ℤ) : ℝ) := by
    intro i
    rw [triadicLatticePoint, abs_mul, abs_of_pos h3j, Int.cast_abs]
  refine ⟨?_, ?_⟩
  · obtain ⟨i, hi⟩ : ∃ i, (1 / 2 : ℝ) * (3 : ℝ) ^ (n - 1)
        ≤ |triadicLatticePoint j v i| := by
      by_contra hcon
      push Not at hcon
      refine hv.2 ?_
      rw [mem_openCubeSet_originCube_iff]
      intro i
      have hii := hcon i
      rw [abs_lt] at hii
      exact ⟨by linarith only [hii.1], by linarith only [hii.2]⟩
    refine ⟨i, ?_⟩
    rw [habs i] at hi
    have hbig := le_three_zpow_mul_of_le (j := j) (n := n - 1) hj hi
    have hxi := hx i
    rw [abs_le] at hxi
    rw [le_abs]
    rcases le_or_gt 0 (triadicLatticePoint j v i) with hsign | hsign
    · left
      have hz : triadicLatticePoint j v i = (3 : ℝ) ^ j * ((|v i| : ℤ) : ℝ) := by
        rw [← abs_of_nonneg hsign, habs i]
      linarith only [hbig, hxi.1, hz]
    · right
      have hz : triadicLatticePoint j v i = -((3 : ℝ) ^ j * ((|v i| : ℤ) : ℝ)) := by
        rw [← habs i, abs_of_neg hsign, neg_neg]
      linarith only [hbig, hxi.2, hz]
  · intro i
    have hin := (mem_openCubeSet_originCube_iff.mp hv.1) i
    have hlt : (3 : ℝ) ^ j * ((|v i| : ℤ) : ℝ) < (1 / 2 : ℝ) * (3 : ℝ) ^ n := by
      rw [← habs i, abs_lt]
      exact ⟨by linarith only [hin.1], by linarith only [hin.2]⟩
    have hsmall := three_zpow_mul_le_of_lt (j := j) (n := n) (by omega) hlt
    have hxi := hx i
    rw [abs_le] at hxi ⊢
    have hzabs : |triadicLatticePoint j v i| ≤
        (1 / 2 : ℝ) * (3 : ℝ) ^ n - (1 / 2 : ℝ) * (3 : ℝ) ^ j := by
      rw [habs i]
      exact hsmall
    rw [abs_le] at hzabs
    exact ⟨by linarith only [hxi.1, hzabs.1], by linarith only [hxi.2, hzabs.2]⟩

end

end Algsuperdiff.Section4.Probability
