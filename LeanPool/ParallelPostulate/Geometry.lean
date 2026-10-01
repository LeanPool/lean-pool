/-
Copyright (c) 2026 Richard Sutton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Richard Sutton
-/
module
public import Mathlib.Algebra.Ring.Prod
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Interval.Set.Infinite
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Coordinate incidence, order, and parallels

`ParallelPostulate.Pairs` develops dimensions and figures over commutative rings and fields.
`ParallelPostulate.HyperbolicPlane` develops bounded affine planes, line incidence, Pasch
order, and the number of parallels over ordered fields. This module uses no calculus,
curvature, or path-distance imports. Analytic geometry and the concrete Hilbert models are
in `LeanPool/ParallelPostulate.lean`; the synthetic axiom bundle is in `Hilbert.lean`.
-/

public section

/-!
# Dimensions laid among the pairs of numbers

A dimension is a number line with its own zero and its own 1, laid among the pairs of numbers
of a ring `K`: `Dim`, with its direction `Dim.dir`, its pairs `Dim.pt` and `Dim.points`, and the
side `Dim.side` of a pair. `cross` is the cross product of two directions. A figure, `Figure`,
is three dimensions `a`, `b`, `c` with the two constraints

    a0 = b0        a1 = c0

so that `a` is the line that falls on the two others. The entry module and the bounded-plane
section build on these,
in the namespace `ParallelPostulate.Pairs`.

## Contents

* a dimension, its direction, its pairs, its sides: `Dim`, `Dim.dir`, `Dim.pt`, `Dim.points`,
  `Dim.side`, `cross`
* a dimension with its zero moved: `Dim.rebase`, `Dim.rebase_dir`, `Dim.rebase_points`,
  `Dim.rebase_zero_ne_one`, `Dim.cross_rebase`
* small facts about a dimension: `Dim.pt_zero`, `Dim.pt_one`, `Dim.zero_mem`, `Dim.one_mem`,
  `Dim.dir_ne_zero`, `Dim.zero_ne_one_of_dir`, `Dim.side_eq_zero_of_mem`, `Dim.side_through`,
  `Dim.through_subset`
* the figure, with the two constraints: `Figure`, `Figure.a0_eq_b0`, `Figure.a1_eq_c0`,
  `Figure.a_meets_b`, `Figure.a_meets_c`, `Figure.side_b_one`, `Figure.side_c_one`,
  `Figure.side_b_pt`
* two right angles, and the figure with `a` run backwards:
  `Figure.never_meet_of_two_right_angles`, `Figure.reverse`, `Figure.reverse_side`,
  `Figure.reverse_dir`, `Figure.reverse_cross`
* with fractions: `cramer_aux`, `Figure.meet_eq`, `Figure.meet_unique`,
  `exists_mul_of_cross_eq_zero`, `Dim.pt_injective`, `Dim.mem_points_of_side_eq_zero`,
  `Dim.points_eq_through`
-/

namespace ParallelPostulate

namespace Pairs

section Ring

variable {K : Type*} [CommRing K]

/-- A dimension laid in the plane: a number line with its own zero and its own 1. -/
structure Dim (K : Type*) where
  /-- The point where the dimension has its zero. -/
  zero : K × K
  /-- The point where the dimension has its 1. -/
  one : K × K

/-- The cross product of two directions. It is positive when the second is a turn to the left
of the first, by less than two right angles. -/
@[expose] def cross (u v : K × K) : K := u.1 * v.2 - u.2 * v.1

namespace Dim

/-- The direction of a dimension, from its zero to its 1. -/
@[expose] def dir (L : Dim K) : K × K := (L.one.1 - L.zero.1, L.one.2 - L.zero.2)

/-- The point of the dimension at the number `t`. -/
@[expose] def pt (L : Dim K) (t : K) : K × K :=
  (L.zero.1 + t * (L.one.1 - L.zero.1), L.zero.2 + t * (L.one.2 - L.zero.2))

/-- The side of the dimension on which a point lies: positive on its left, negative on its
right, and zero on the dimension itself. -/
@[expose] def side (L : Dim K) (P : K × K) : K := cross L.dir (P.1 - L.zero.1, P.2 - L.zero.2)

/-- The points of a dimension. -/
@[expose] def points (L : Dim K) : Set (K × K) := Set.range L.pt

/-- The dimension `M` with its zero moved to the point `P`. It keeps its direction. -/
@[expose] def rebase (M : Dim K) (P : K × K) : Dim K :=
  ⟨P, (P.1 + (M.one.1 - M.zero.1), P.2 + (M.one.2 - M.zero.2))⟩

theorem pt_zero (L : Dim K) : L.pt 0 = L.zero := by
  apply Prod.ext <;> simp [pt]

theorem pt_one (L : Dim K) : L.pt 1 = L.one := by
  apply Prod.ext <;> simp [pt]

theorem zero_mem (L : Dim K) : L.zero ∈ L.points := ⟨0, L.pt_zero⟩

theorem one_mem (L : Dim K) : L.one ∈ L.points := ⟨1, L.pt_one⟩

theorem dir_ne_zero (L : Dim K) (hL : L.zero ≠ L.one) : L.dir ≠ (0, 0) := by
  intro h0
  apply hL
  have h1 := congrArg Prod.fst h0
  have h2 := congrArg Prod.snd h0
  simp only [dir] at h1 h2
  exact Prod.ext (sub_eq_zero.mp h1).symm (sub_eq_zero.mp h2).symm

theorem zero_ne_one_of_dir (L : Dim K) (h : L.dir ≠ (0, 0)) : L.zero ≠ L.one := by
  intro e
  apply h
  simp only [dir, e, sub_self]

theorem rebase_dir (M : Dim K) (P : K × K) : (M.rebase P).dir = M.dir := by
  apply Prod.ext <;> simp [rebase, dir]

/-- A dimension can be given its zero at any of its points: it keeps its points. -/
theorem rebase_points (M : Dim K) {P : K × K} (hP : P ∈ M.points) :
    (M.rebase P).points = M.points := by
  obtain ⟨s, rfl⟩ := hP
  apply Set.Subset.antisymm
  · rintro _ ⟨t, rfl⟩
    refine ⟨s + t, ?_⟩
    apply Prod.ext
    · simp only [pt, rebase]
      ring
    · simp only [pt, rebase]
      ring
  · rintro _ ⟨t, rfl⟩
    refine ⟨t - s, ?_⟩
    apply Prod.ext
    · simp only [pt, rebase]
      ring
    · simp only [pt, rebase]
      ring

theorem rebase_zero_ne_one (L : Dim K) (hL : L.zero ≠ L.one) (P : K × K) :
    (L.rebase P).zero ≠ (L.rebase P).one := by
  intro h
  apply hL
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  simp only [rebase] at h1 h2
  apply Prod.ext
  · linear_combination h1
  · linear_combination h2

/-- The moved dimension has the direction of the dimension it was made from. -/
theorem cross_rebase (L : Dim K) (P : K × K) : cross L.dir (L.rebase P).dir = 0 := by
  simp only [cross, dir, rebase]
  ring

/-- The side of a pair of the dimension is zero. -/
theorem side_eq_zero_of_mem (L : Dim K) {P : K × K} (hP : P ∈ L.points) : L.side P = 0 := by
  obtain ⟨t, rfl⟩ := hP
  simp only [side, dir, pt, cross]
  ring

/-- Along the dimension from `A` to `C`, the side changes evenly from the side of `A` to the
side of `C`. -/
theorem side_through (L : Dim K) (A C : K × K) (u : K) :
    L.side ((Dim.mk A C).pt u) = (1 - u) * L.side A + u * L.side C := by
  simp only [side, dir, pt, cross]
  ring

/-- The dimension through two pairs of `L` has its pairs among those of `L`. -/
theorem through_subset (L : Dim K) {A B : K × K} (hA : A ∈ L.points) (hB : B ∈ L.points) :
    (Dim.mk A B).points ⊆ L.points := by
  obtain ⟨s, rfl⟩ := hA
  obtain ⟨s', rfl⟩ := hB
  rintro _ ⟨u, rfl⟩
  refine ⟨s + u * (s' - s), ?_⟩
  apply Prod.ext
  · simp only [pt]
    ring
  · simp only [pt]
    ring

end Dim

/-- The figure: three dimensions with `a0 = b0` and `a1 = c0`, read as points. -/
structure Figure (K : Type*) where
  /-- The straight line that falls on the two others. -/
  a : Dim K
  /-- The line that leaves `a` at `a0`. -/
  b : Dim K
  /-- The line that leaves `a` at `a1`. -/
  c : Dim K
  /-- The first constraint. -/
  a0_eq_b0 : a.zero = b.zero
  /-- The second constraint. -/
  a1_eq_c0 : a.one = c.zero

namespace Figure

/-- `a` meets `b` where `a` has its zero. -/
theorem a_meets_b (F : Figure K) : F.a.pt 0 = F.b.pt 0 := by
  rw [Dim.pt_zero, Dim.pt_zero]; exact F.a0_eq_b0

/-- `a` meets `c` where `a` has its 1. -/
theorem a_meets_c (F : Figure K) : F.a.pt 1 = F.c.pt 0 := by
  rw [Dim.pt_one, Dim.pt_zero]; exact F.a1_eq_c0

theorem side_b_one (F : Figure K) : F.a.side F.b.one = cross F.a.dir F.b.dir := by
  simp only [Dim.side, Dim.dir, F.a0_eq_b0]

theorem side_c_one (F : Figure K) : F.a.side F.c.one = cross F.a.dir F.c.dir := by
  simp only [Dim.side, Dim.dir, cross, ← F.a1_eq_c0]
  ring

theorem side_b_pt (F : Figure K) (t : K) :
    F.a.side (F.b.pt t) = t * cross F.a.dir F.b.dir := by
  simp only [Dim.side, Dim.dir, Dim.pt, cross, ← F.a0_eq_b0]
  ring

/-- **Two right angles: the lines never meet.** If the side of `c1` is not zero, and the cross
product of the directions of `b` and `c` is zero, the two lines have no point in common. -/
theorem never_meet_of_two_right_angles (F : Figure K)
    (hc : F.a.side F.c.one ≠ 0) (hsum : cross F.b.dir F.c.dir = 0) (t u : K) :
    F.b.pt t ≠ F.c.pt u := by
  intro heq
  apply hc
  rw [F.side_c_one]
  have hb0 : F.b.zero = F.a.zero := F.a0_eq_b0.symm
  have hc0 : F.c.zero = F.a.one := F.a1_eq_c0.symm
  have e1 := congrArg Prod.fst heq
  have e2 := congrArg Prod.snd heq
  simp only [Dim.pt, Dim.dir, cross, hb0, hc0] at e1 e2 hsum ⊢
  linear_combination (-(F.c.one.2 - F.a.one.2)) * e1 + (F.c.one.1 - F.a.one.1) * e2 + t * hsum

/-- The same figure with `a` run backwards. It starts at `a1` and ends at `a0`, so the line
that leaves its zero is `c` and the line that leaves its 1 is `b`. Left and right of `a` change
places. -/
@[expose] def reverse (F : Figure K) : Figure K where
  a := ⟨F.a.one, F.a.zero⟩
  b := F.c
  c := F.b
  a0_eq_b0 := F.a1_eq_c0
  a1_eq_c0 := F.a0_eq_b0

theorem reverse_side (F : Figure K) (P : K × K) : F.reverse.a.side P = -F.a.side P := by
  simp only [reverse, Dim.side, Dim.dir, cross]
  ring

theorem reverse_dir (F : Figure K) : F.reverse.a.dir = -F.a.dir := by
  apply Prod.ext <;> simp [reverse, Dim.dir]

theorem reverse_cross (F : Figure K) :
    cross F.reverse.b.dir F.reverse.c.dir = -cross F.b.dir F.c.dir := by
  simp only [reverse, cross]
  ring

end Figure

end Ring

section Field

variable {K : Type*} [Field K]

/-- The one step that divides. If `(a' - o) D = p n - x m`, the point at `n / D` along `p` from
`o` is the point at `m / D` along `x` from `a'`. -/
theorem cramer_aux (o a' p x n m D : K) (hD : D ≠ 0)
    (h : (a' - o) * D = p * n - x * m) : o + n / D * p = a' + m / D * x := by
  have hn : n / D * D = n := div_mul_cancel₀ _ hD
  have hm : m / D * D = m := div_mul_cancel₀ _ hD
  apply mul_right_cancel₀ hD
  linear_combination p * hn - x * hm - h

/-- Where `b` and `c` meet, when the cross product of their directions is not zero. -/
theorem Figure.meet_eq (F : Figure K) (hne : cross F.b.dir F.c.dir ≠ 0) :
    F.b.pt (cross F.a.dir F.c.dir / cross F.b.dir F.c.dir)
      = F.c.pt (cross F.a.dir F.b.dir / cross F.b.dir F.c.dir) := by
  have hb0 : F.b.zero = F.a.zero := F.a0_eq_b0.symm
  have hc0 : F.c.zero = F.a.one := F.a1_eq_c0.symm
  apply Prod.ext
  · simp only [Dim.pt, Dim.dir, cross, hb0, hc0] at hne ⊢
    exact cramer_aux _ _ _ _ _ _ _ hne (by ring)
  · simp only [Dim.pt, Dim.dir, cross, hb0, hc0] at hne ⊢
    exact cramer_aux _ _ _ _ _ _ _ hne (by ring)

/-- And they meet at one point only. -/
theorem Figure.meet_unique (F : Figure K) (hne : cross F.b.dir F.c.dir ≠ 0) {t u t' u' : K}
    (h : F.b.pt t = F.c.pt u) (h' : F.b.pt t' = F.c.pt u') : t = t' ∧ u = u' := by
  have hb0 : F.b.zero = F.a.zero := F.a0_eq_b0.symm
  have hc0 : F.c.zero = F.a.one := F.a1_eq_c0.symm
  have e1 := congrArg Prod.fst h
  have e2 := congrArg Prod.snd h
  have e1' := congrArg Prod.fst h'
  have e2' := congrArg Prod.snd h'
  simp only [Dim.pt, Dim.dir, cross, hb0, hc0] at e1 e2 e1' e2' hne
  have ht : (t - t') * ((F.b.one.1 - F.a.zero.1) * (F.c.one.2 - F.a.one.2)
      - (F.b.one.2 - F.a.zero.2) * (F.c.one.1 - F.a.one.1)) = 0 := by
    linear_combination (F.c.one.2 - F.a.one.2) * e1 - (F.c.one.2 - F.a.one.2) * e1'
      - (F.c.one.1 - F.a.one.1) * e2 + (F.c.one.1 - F.a.one.1) * e2'
  have hu : (u - u') * ((F.b.one.1 - F.a.zero.1) * (F.c.one.2 - F.a.one.2)
      - (F.b.one.2 - F.a.zero.2) * (F.c.one.1 - F.a.one.1)) = 0 := by
    linear_combination (F.b.one.2 - F.a.zero.2) * e1 - (F.b.one.2 - F.a.zero.2) * e1'
      - (F.b.one.1 - F.a.zero.1) * e2 + (F.b.one.1 - F.a.zero.1) * e2'
  exact ⟨sub_eq_zero.mp ((mul_eq_zero.mp ht).resolve_right hne),
    sub_eq_zero.mp ((mul_eq_zero.mp hu).resolve_right hne)⟩

/-- A direction with cross product zero against `v` is a multiple of `v`. -/
theorem exists_mul_of_cross_eq_zero {v w : K × K} (hv : v ≠ (0, 0)) (h : cross v w = 0) :
    ∃ l : K, w = (l * v.1, l * v.2) := by
  simp only [cross] at h
  by_cases h1 : v.1 = 0
  · have h2 : v.2 ≠ 0 := fun h2 => hv (Prod.ext h1 h2)
    have hw : w.1 = 0 := by
      have h3 : v.2 * w.1 = 0 := by linear_combination w.2 * h1 - h
      rcases mul_eq_zero.mp h3 with h4 | h4
      · exact absurd h4 h2
      · exact h4
    refine ⟨w.2 / v.2, Prod.ext ?_ ?_⟩
    · simp only [h1, hw, mul_zero]
    · simp only [div_mul_cancel₀ _ h2]
  · refine ⟨w.1 / v.1, Prod.ext ?_ ?_⟩
    · simp only [div_mul_cancel₀ _ h1]
    · have h3 : w.2 * v.1 = w.1 * v.2 := by linear_combination h
      have h4 : w.1 / v.1 * v.1 = w.1 := div_mul_cancel₀ _ h1
      simp only []
      apply mul_right_cancel₀ h1
      linear_combination h3 - v.2 * h4

/-- A dimension is a number line: different numbers are at different pairs. -/
theorem Dim.pt_injective (M : Dim K) (hM : M.zero ≠ M.one) : Function.Injective M.pt := by
  intro s s' h
  have e1 := congrArg Prod.fst h
  have e2 := congrArg Prod.snd h
  simp only [Dim.pt] at e1 e2
  by_contra hne
  have hs : s - s' ≠ 0 := sub_ne_zero.mpr hne
  have h1 : (s - s') * (M.one.1 - M.zero.1) = 0 := by linear_combination e1
  have h2 : (s - s') * (M.one.2 - M.zero.2) = 0 := by linear_combination e2
  exact M.dir_ne_zero hM
    (Prod.ext ((mul_eq_zero.mp h1).resolve_left hs) ((mul_eq_zero.mp h2).resolve_left hs))

/-- A pair whose side is zero is a pair of the dimension. -/
theorem Dim.mem_points_of_side_eq_zero (L : Dim K) (hL : L.zero ≠ L.one) (P : K × K)
    (h : L.side P = 0) : P ∈ L.points := by
  obtain ⟨l, hl⟩ := exists_mul_of_cross_eq_zero (L.dir_ne_zero hL) h
  refine ⟨l, ?_⟩
  have l1 := congrArg Prod.fst hl
  have l2 := congrArg Prod.snd hl
  simp only [Dim.dir] at l1 l2
  apply Prod.ext
  · simp only [Dim.pt]
    linear_combination -l1
  · simp only [Dim.pt]
    linear_combination -l2

/-- Two different pairs of a dimension give the dimension: it has the pairs of the dimension
from the one to the other. -/
theorem Dim.points_eq_through (L : Dim K) {A B : K × K} (hA : A ∈ L.points)
    (hB : B ∈ L.points) (hAB : A ≠ B) : L.points = (Dim.mk A B).points := by
  apply Set.Subset.antisymm
  · obtain ⟨s, rfl⟩ := hA
    obtain ⟨s', rfl⟩ := hB
    have hs : s' - s ≠ 0 := by
      intro h
      apply hAB
      rw [sub_eq_zero.mp h]
    rintro _ ⟨x, rfl⟩
    refine ⟨(x - s) / (s' - s), ?_⟩
    have hx : (x - s) / (s' - s) * (s' - s) = x - s := div_mul_cancel₀ _ hs
    apply Prod.ext
    · simp only [Dim.pt]
      linear_combination (L.one.1 - L.zero.1) * hx
    · simp only [Dim.pt]
      linear_combination (L.one.2 - L.zero.2) * hx
  · exact L.through_subset hA hB

end Field

end Pairs

end ParallelPostulate

/-!
# The plane of a bound: lines, order and parallels

A plane is a set of pairs of numbers, and a line of a plane is what a dimension has in it. The
plane of the bound `κ`, `plane κ`, has the pairs `(x, y)` with `0 < 1 + κ (x² + y²)`. This file
proves Hilbert's statements on incidence and on order for it (Proposition H4 and
`between_trichotomy`), and counts the parallels: one exactly when the bound is not negative, and
infinitely many under a negative bound.

## Contents

* a plane: any `Set (K × K)`
* what two dimensions have in common: `common_of_cross_ne_zero`, `points_eq_of_two_common`,
  `no_common_of_cross_eq_zero`, `points_subset_of_cross_eq_zero`, `points_eq_of_cross_eq_zero`
* a line of a plane, a plane open along the dimensions: `IsLine`, `OpenAlong`
* a line through `P` that does not meet `L`: `Misses`
* Euclid's line, the line toward a number of `L`: `euclid`, `toward`
* Theorem H1, the lines through `P` that do not meet `L`: `miss_iff`, `misses_iff`,
  `euclid_misses`, `toward_misses`, `one_parallel_of_all_within`
* Theorem H2, one parallel exactly when: `toward_injective`, `euclid_ne_toward`,
  `one_parallel_iff`, `two_parallels_of_beyond`, `infinitely_many_parallels`
* the choice, the bound: `plane`, `mem_plane`
* Proposition H3, the plane of a bound: `plane_eq_univ`, `plane_zero`, `plane_stretch`,
  `plane_beyond`, `plane_beyond_infinite`, `zero_mem_plane`, `plane_mono`, `mem_plane_scale`,
  `plane_open_forward`, `plane_openAlong`, `plane_convex`, `bound_along`, `quad_pos`, `quad_nonpos`
* a sum of two squares: `sq_add_sq_pos`
* Proposition H4, points, lines and order: `line_through`, `IsLine.two_points`,
  `IsLine.exists_within`, `exists_three_points`, `exists_line_and_point`,
  `plane_exists_line_and_point`, `Between`, `Between.symm`, `Between.mem`, `Between.ne`,
  `Between.not_left`, `Between.not_right`, `exists_beyond`, `crosses`, `pasch`
* Theorem H5, the parallels under a negative bound: `hyperbolic_parallel_property`,
  `hyperbolic_two_parallels`, `hyperbolic_parallels`
* Theorem H6, the plane of the three-dimensions section from the same choice: `euclid_one_parallel`,
  `fifth_postulate_of_nonneg_bound`
* Theorem H7, exactly when: `one_parallel_iff_bound`
* three points on a line: `between_trichotomy`, `ne_of_side_ne_zero`, `IsLine.subset_plane`,
  `IsLine.eq_through`
* the order of the numbers of a dimension: `StrictBetween`, `between_pt_of_strictBetween`,
  `strictBetween_of_between_pt`, `pt_mem_plane_of_le`
-/

namespace ParallelPostulate

namespace HyperbolicPlane

open Pairs

/-! ## With fractions: what two dimensions have in common -/

section Fractions

variable {K : Type*} [Field K]

/-- Two dimensions have a pair in common if the cross product of their directions is not
zero. -/
theorem common_of_cross_ne_zero (L M : Dim K) (h : cross L.dir M.dir ≠ 0) :
    ∃ Q, Q ∈ L.points ∧ Q ∈ M.points := by
  refine ⟨L.pt (cross (M.zero.1 - L.zero.1, M.zero.2 - L.zero.2) M.dir / cross L.dir M.dir),
    ⟨_, rfl⟩,
    cross (M.zero.1 - L.zero.1, M.zero.2 - L.zero.2) L.dir / cross L.dir M.dir, Eq.symm ?_⟩
  apply Prod.ext
  · simp only [Dim.pt, Dim.dir, cross] at h ⊢
    exact cramer_aux _ _ _ _ _ _ _ h (by ring)
  · simp only [Dim.pt, Dim.dir, cross] at h ⊢
    exact cramer_aux _ _ _ _ _ _ _ h (by ring)

/-- Two dimensions with two different pairs in common have the same pairs. -/
theorem points_eq_of_two_common (L M : Dim K) {A B : K × K} (hAB : A ≠ B)
    (hA : A ∈ L.points) (hB : B ∈ L.points) (hA' : A ∈ M.points) (hB' : B ∈ M.points) :
    L.points = M.points := by
  rw [L.points_eq_through hA hB hAB, M.points_eq_through hA' hB' hAB]

/-- If the direction of `M` is a multiple of the direction of `L`, and `M` has a pair that is
not a pair of `L`, the two have no pair in common. -/
theorem no_common_of_cross_eq_zero (L M : Dim K) (hL : L.zero ≠ L.one)
    (h : cross L.dir M.dir = 0) {P : K × K} (hP : P ∈ M.points) (hPL : P ∉ L.points)
    {Q : K × K} (hQL : Q ∈ L.points) (hQM : Q ∈ M.points) : False := by
  obtain ⟨l, hl⟩ := exists_mul_of_cross_eq_zero (L.dir_ne_zero hL) h
  obtain ⟨p, rfl⟩ := hP
  obtain ⟨t, rfl⟩ := hQL
  obtain ⟨u, hu⟩ := hQM
  apply hPL
  refine ⟨t + (p - u) * l, ?_⟩
  have e1 := congrArg Prod.fst hu
  have e2 := congrArg Prod.snd hu
  have l1 := congrArg Prod.fst hl
  have l2 := congrArg Prod.snd hl
  simp only [Dim.pt, Dim.dir] at e1 e2 l1 l2
  apply Prod.ext
  · simp only [Dim.pt]
    linear_combination -e1 - (p - u) * l1
  · simp only [Dim.pt]
    linear_combination -e2 - (p - u) * l2

/-- Let two dimensions pass through one pair, each with a direction that is a multiple of the
direction of `L`. Then the pairs of the first are pairs of the second. -/
theorem points_subset_of_cross_eq_zero (L M M' : Dim K) (hL : L.zero ≠ L.one)
    (hM' : M'.zero ≠ M'.one) (h : cross L.dir M.dir = 0) (h' : cross L.dir M'.dir = 0)
    {P : K × K} (hP : P ∈ M.points) (hP' : P ∈ M'.points) : M.points ⊆ M'.points := by
  obtain ⟨l, hl⟩ := exists_mul_of_cross_eq_zero (L.dir_ne_zero hL) h
  obtain ⟨l', hl'⟩ := exists_mul_of_cross_eq_zero (L.dir_ne_zero hL) h'
  have hl'0 : l' ≠ 0 := by
    rintro rfl
    apply M'.dir_ne_zero hM'
    rw [hl']
    simp
  obtain ⟨p, rfl⟩ := hP
  obtain ⟨p', hp'⟩ := hP'
  rintro _ ⟨x, rfl⟩
  refine ⟨p' + (x - p) * l / l', ?_⟩
  have hy : (x - p) * l / l' * l' = (x - p) * l := div_mul_cancel₀ _ hl'0
  have e1 := congrArg Prod.fst hp'
  have e2 := congrArg Prod.snd hp'
  have l1 := congrArg Prod.fst hl
  have l2 := congrArg Prod.snd hl
  have l1' := congrArg Prod.fst hl'
  have l2' := congrArg Prod.snd hl'
  simp only [Dim.pt, Dim.dir] at e1 e2 l1 l2 l1' l2'
  apply Prod.ext
  · simp only [Dim.pt]
    linear_combination e1 - (x - p) * l1 + (x - p) * l / l' * l1'
      + (L.one.1 - L.zero.1) * hy
  · simp only [Dim.pt]
    linear_combination e2 - (x - p) * l2 + (x - p) * l / l' * l2'
      + (L.one.2 - L.zero.2) * hy

/-- Two dimensions through one pair, each with a direction that is a multiple of the direction
of `L`, have the same pairs. -/
theorem points_eq_of_cross_eq_zero (L M M' : Dim K) (hL : L.zero ≠ L.one)
    (hM : M.zero ≠ M.one) (hM' : M'.zero ≠ M'.one) (h : cross L.dir M.dir = 0)
    (h' : cross L.dir M'.dir = 0) {P : K × K} (hP : P ∈ M.points) (hP' : P ∈ M'.points) :
    M.points = M'.points :=
  Set.Subset.antisymm (points_subset_of_cross_eq_zero L M M' hL hM' h h' hP hP')
    (points_subset_of_cross_eq_zero L M' M hL hM h' h hP' hP)

end Fractions

/-! ## A plane, its lines, and the lines through a point that miss a line

A plane is any set of pairs: the pairs that are taken for points. Nothing is asked of it here,
and no order of the numbers is used. -/

section Planes

variable {K : Type*} [Field K]

/-- A line of the plane `Pl`: what a dimension has in the plane, if it has anything there. -/
@[expose] def IsLine (Pl S : Set (K × K)) : Prop :=
  ∃ M : Dim K, M.zero ≠ M.one ∧ S = M.points ∩ Pl ∧ S.Nonempty

/-- `S` is a line of the plane through `P` that does not meet the line of `L`. -/
@[expose] def Misses (Pl : Set (K × K)) (L : Dim K) (P : K × K) (S : Set (K × K)) : Prop :=
  IsLine Pl S ∧ P ∈ S ∧ S ∩ (L.points ∩ Pl) = ∅

/-- Euclid's line: what the dimension through `P` with the direction of `L` has in the
plane. -/
@[expose] def euclid (Pl : Set (K × K)) (L : Dim K) (P : K × K) : Set (K × K) :=
  (L.rebase P).points ∩ Pl

/-- What the dimension from `P` to the pair of `L` at the number `t` has in the plane. -/
@[expose] def toward (Pl : Set (K × K)) (L : Dim K) (P : K × K) (t : K) : Set (K × K) :=
  (Dim.mk P (L.pt t)).points ∩ Pl

/-- The plane is open along the dimensions: a dimension with its zero in the plane has
another of its numbers in the plane. -/
@[expose] def OpenAlong (Pl : Set (K × K)) : Prop :=
  ∀ M : Dim K, M.zero ∈ Pl → ∃ t : K, t ≠ 0 ∧ M.pt t ∈ Pl

/-- **Two points are on one line, and on one only.** -/
theorem line_through (Pl : Set (K × K)) {A B : K × K} (hA : A ∈ Pl) (hB : B ∈ Pl)
    (hAB : A ≠ B) : ∃! S, IsLine Pl S ∧ A ∈ S ∧ B ∈ S := by
  have hAm : A ∈ (Dim.mk A B).points := (Dim.mk A B).zero_mem
  have hBm : B ∈ (Dim.mk A B).points := (Dim.mk A B).one_mem
  refine ⟨(Dim.mk A B).points ∩ Pl,
    ⟨⟨⟨A, B⟩, hAB, rfl, A, hAm, hA⟩, ⟨hAm, hA⟩, ⟨hBm, hB⟩⟩, ?_⟩
  rintro S ⟨⟨M, -, rfl, -⟩, hAS, hBS⟩
  rw [M.points_eq_through hAS.1 hBS.1 hAB]

/-- **Every line of the plane is a dimension with its zero and its 1 in the plane**, as far as
it lies in the plane. -/
theorem IsLine.exists_within {Pl S : Set (K × K)} (hopen : OpenAlong Pl) (hS : IsLine Pl S) :
    ∃ M : Dim K, M.zero ∈ Pl ∧ M.one ∈ Pl ∧ M.zero ≠ M.one ∧ S = M.points ∩ Pl := by
  obtain ⟨M, hM, rfl, A, hAM, hA⟩ := hS
  obtain ⟨r, hr, hB⟩ := hopen (M.rebase A) hA
  have hN := M.rebase_zero_ne_one hM A
  have hAB : A ≠ (M.rebase A).pt r := fun h =>
    hr ((M.rebase A).pt_injective hN ((M.rebase A).pt_zero.trans h)).symm
  have hBM : (M.rebase A).pt r ∈ M.points := by
    obtain ⟨s, rfl⟩ := hAM
    refine ⟨s + r, ?_⟩
    apply Prod.ext
    · simp only [Dim.pt, Dim.rebase]
      ring
    · simp only [Dim.pt, Dim.rebase]
      ring
  exact ⟨⟨A, (M.rebase A).pt r⟩, hA, hB, hAB, by rw [M.points_eq_through hAM hBM hAB]⟩

/-- A line of the plane has two different points. -/
theorem IsLine.two_points {Pl S : Set (K × K)} (hopen : OpenAlong Pl) (hS : IsLine Pl S) :
    ∃ A B : K × K, A ≠ B ∧ A ∈ S ∧ B ∈ S := by
  obtain ⟨M, h0, h1, hne, rfl⟩ := hS.exists_within hopen
  exact ⟨M.zero, M.one, hne, ⟨M.zero_mem, h0⟩, ⟨M.one_mem, h1⟩⟩

/-- **A plane that is open along the dimensions, and has a point, has a line and a point
that is not on it.** -/
theorem exists_line_and_point {Pl : Set (K × K)} (hopen : OpenAlong Pl) {A : K × K}
    (hA : A ∈ Pl) : ∃ (S : Set (K × K)) (P : K × K), IsLine Pl S ∧ P ∈ Pl ∧ P ∉ S := by
  obtain ⟨t, ht, hB⟩ := hopen ⟨A, (A.1 + 1, A.2)⟩ hA
  obtain ⟨u, hu, hC⟩ := hopen ⟨A, (A.1, A.2 + 1)⟩ hA
  have hAB : A ≠ (Dim.mk A (A.1 + 1, A.2)).pt t := by
    intro h
    have h1 := congrArg Prod.fst h
    simp only [Dim.pt] at h1
    apply ht
    linear_combination -h1
  refine ⟨(Dim.mk A ((Dim.mk A (A.1 + 1, A.2)).pt t)).points ∩ Pl, _,
    ⟨⟨A, (Dim.mk A (A.1 + 1, A.2)).pt t⟩, hAB, rfl, A, (Dim.mk A _).zero_mem, hA⟩, hC, ?_⟩
  rintro ⟨⟨s, hs⟩, -⟩
  have h2 := congrArg Prod.snd hs
  simp only [Dim.pt] at h2
  apply hu
  linear_combination -h2

/-- **When two lines of the plane do not meet.** Let `M` pass through a pair that is not a
pair of `L`. What `M` and `L` have in the plane has no point in common exactly when `M` has the
direction of `L`, or the two dimensions meet at a pair that is not a point of the plane. -/
theorem miss_iff (Pl : Set (K × K)) (L M : Dim K) (hL : L.zero ≠ L.one) {P : K × K}
    (hP : P ∈ M.points) (hPL : P ∉ L.points) :
    (M.points ∩ Pl) ∩ (L.points ∩ Pl) = ∅ ↔
      cross L.dir M.dir = 0 ∨ ∃ Q, Q ∈ L.points ∧ Q ∈ M.points ∧ Q ∉ Pl := by
  constructor
  · intro h
    by_cases hc : cross L.dir M.dir = 0
    · exact Or.inl hc
    · right
      obtain ⟨Q, hQL, hQM⟩ := common_of_cross_ne_zero L M hc
      refine ⟨Q, hQL, hQM, fun hQ => ?_⟩
      have hmem : Q ∈ (M.points ∩ Pl) ∩ (L.points ∩ Pl) := ⟨⟨hQM, hQ⟩, ⟨hQL, hQ⟩⟩
      rw [h] at hmem
      exact hmem
  · rintro (hc | ⟨Q, hQL, hQM, hQ⟩)
    · apply Set.eq_empty_of_forall_notMem
      rintro X ⟨⟨hXM, -⟩, ⟨hXL, -⟩⟩
      exact no_common_of_cross_eq_zero L M hL hc hP hPL hXL hXM
    · apply Set.eq_empty_of_forall_notMem
      rintro X ⟨⟨hXM, hX⟩, ⟨hXL, -⟩⟩
      by_cases hXQ : X = Q
      · exact hQ (hXQ ▸ hX)
      · apply hPL
        rw [points_eq_of_two_common L M hXQ hXL hQL hXM hQM]
        exact hP

/-- Euclid's line passes through `P` and does not meet `L`, in any plane. -/
theorem euclid_misses (Pl : Set (K × K)) (L : Dim K) (hL : L.zero ≠ L.one) {P : K × K}
    (hP : P ∈ Pl) (hPL : P ∉ L.points) : Misses Pl L P (euclid Pl L P) := by
  have hzero : P ∈ (L.rebase P).points := (L.rebase P).zero_mem
  refine ⟨⟨L.rebase P, L.rebase_zero_ne_one hL P, rfl, P, hzero, hP⟩, ⟨hzero, hP⟩, ?_⟩
  exact (miss_iff Pl L (L.rebase P) hL hzero hPL).mpr (Or.inl (L.cross_rebase P))

/-- The line from `P` toward a pair of `L` that is not a point of the plane passes through `P`
and does not meet `L`. -/
theorem toward_misses (Pl : Set (K × K)) (L : Dim K) (hL : L.zero ≠ L.one) {P : K × K}
    (hP : P ∈ Pl) (hPL : P ∉ L.points) {t : K} (ht : L.pt t ∉ Pl) :
    Misses Pl L P (toward Pl L P t) := by
  have hzero : P ∈ (Dim.mk P (L.pt t)).points := (Dim.mk P (L.pt t)).zero_mem
  have hone : L.pt t ∈ (Dim.mk P (L.pt t)).points := (Dim.mk P (L.pt t)).one_mem
  have hne : P ≠ L.pt t := fun h => ht (h ▸ hP)
  refine ⟨⟨⟨P, L.pt t⟩, hne, rfl, P, hzero, hP⟩, ⟨hzero, hP⟩, ?_⟩
  exact (miss_iff Pl L _ hL hzero hPL).mpr (Or.inr ⟨L.pt t, ⟨t, rfl⟩, hone, ht⟩)

/-- **The lines through `P` that do not meet `L`.** They are Euclid's line, and one line for
each number of `L` whose pair is not a point of the plane. There are no others. -/
theorem misses_iff (Pl : Set (K × K)) (L : Dim K) (hL : L.zero ≠ L.one) {P : K × K}
    (hP : P ∈ Pl) (hPL : P ∉ L.points) (S : Set (K × K)) :
    Misses Pl L P S ↔ S = euclid Pl L P ∨ ∃ t : K, L.pt t ∉ Pl ∧ S = toward Pl L P t := by
  constructor
  · rintro ⟨⟨M, hM, rfl, -⟩, hPS, hmiss⟩
    rcases (miss_iff Pl L M hL hPS.1 hPL).mp hmiss with hc | ⟨Q, ⟨t, rfl⟩, hQM, hQ⟩
    · left
      unfold euclid
      rw [points_eq_of_cross_eq_zero L M (L.rebase P) hL hM (L.rebase_zero_ne_one hL P) hc
        (L.cross_rebase P) hPS.1 (L.rebase P).zero_mem]
    · right
      refine ⟨t, hQ, ?_⟩
      have hne : P ≠ L.pt t := fun h => hQ (h ▸ hP)
      unfold toward
      rw [M.points_eq_through hPS.1 hQM hne]
  · rintro (rfl | ⟨t, ht, rfl⟩)
    · exact euclid_misses Pl L hL hP hPL
    · exact toward_misses Pl L hL hP hPL ht

/-- Lines from `P` toward different numbers of `L` are different lines of the plane. -/
theorem toward_injective (Pl : Set (K × K)) (hopen : OpenAlong Pl) (L : Dim K)
    (hL : L.zero ≠ L.one) {P : K × K} (hP : P ∈ Pl) (hPL : P ∉ L.points) :
    Function.Injective (toward Pl L P) := by
  intro t t' h
  obtain ⟨r, hr, hX⟩ := hopen ⟨P, L.pt t⟩ hP
  have hmem : (Dim.mk P (L.pt t)).pt r ∈ toward Pl L P t' := by
    rw [← h]
    exact ⟨⟨r, rfl⟩, hX⟩
  obtain ⟨⟨r', hr'⟩, -⟩ := hmem
  have e1 := congrArg Prod.fst hr'
  have e2 := congrArg Prod.snd hr'
  simp only [Dim.pt] at e1 e2
  have hside : L.side P ≠ 0 := fun h0 => hPL (L.mem_points_of_side_eq_zero hL P h0)
  simp only [Dim.side, cross, Dim.dir] at hside
  have hrr : r = r' := by
    have h0 : (r - r') * ((L.one.1 - L.zero.1) * (P.2 - L.zero.2)
        - (L.one.2 - L.zero.2) * (P.1 - L.zero.1)) = 0 := by
      linear_combination (L.one.1 - L.zero.1) * e2 - (L.one.2 - L.zero.2) * e1
    exact sub_eq_zero.mp ((mul_eq_zero.mp h0).resolve_right hside)
  rw [← hrr] at e1 e2
  have h1 : r * (t - t') * (L.one.1 - L.zero.1) = 0 := by linear_combination -e1
  have h2 : r * (t - t') * (L.one.2 - L.zero.2) = 0 := by linear_combination -e2
  by_contra hne
  have hrt : r * (t - t') ≠ 0 := mul_ne_zero hr (sub_ne_zero.mpr hne)
  exact L.dir_ne_zero hL
    (Prod.ext ((mul_eq_zero.mp h1).resolve_left hrt) ((mul_eq_zero.mp h2).resolve_left hrt))

/-- Euclid's line is none of the lines toward a pair of `L`. -/
theorem euclid_ne_toward (Pl : Set (K × K)) (hopen : OpenAlong Pl) (L : Dim K)
    (hL : L.zero ≠ L.one) {P : K × K} (hP : P ∈ Pl) (hPL : P ∉ L.points) (t : K) :
    euclid Pl L P ≠ toward Pl L P t := by
  intro h
  obtain ⟨r, hr, hX⟩ := hopen (L.rebase P) hP
  have hN := L.rebase_zero_ne_one hL P
  have hX' : (L.rebase P).pt r ∈ toward Pl L P t := by
    rw [← h]
    exact ⟨⟨r, rfl⟩, hX⟩
  have hPX : P ≠ (L.rebase P).pt r := fun h' =>
    hr ((L.rebase P).pt_injective hN ((L.rebase P).pt_zero.trans h')).symm
  have hsame : (L.rebase P).points = (Dim.mk P (L.pt t)).points :=
    points_eq_of_two_common _ _ hPX (L.rebase P).zero_mem ⟨r, rfl⟩
      (Dim.mk P (L.pt t)).zero_mem hX'.1
  have hQ : L.pt t ∈ (L.rebase P).points := by
    rw [hsame]
    exact (Dim.mk P (L.pt t)).one_mem
  exact no_common_of_cross_eq_zero L (L.rebase P) hL (L.cross_rebase P)
    (L.rebase P).zero_mem hPL ⟨t, rfl⟩ hQ

/-- **If every number of `L` is a point of the plane, one line through `P` does not meet `L`,
and only one.** -/
theorem one_parallel_of_all_within (Pl : Set (K × K)) (L : Dim K) (hL : L.zero ≠ L.one)
    {P : K × K} (hP : P ∈ Pl) (hPL : P ∉ L.points) (hall : ∀ t : K, L.pt t ∈ Pl) :
    ∃! S, Misses Pl L P S := by
  refine ⟨euclid Pl L P, euclid_misses Pl L hL hP hPL, ?_⟩
  intro S hS
  rcases (misses_iff Pl L hL hP hPL S).mp hS with h | ⟨t, ht, -⟩
  · exact h
  · exact absurd (hall t) ht

/-- **If a number of `L` is not a point of the plane, two different lines through `P` do not
meet `L`.** -/
theorem two_parallels_of_beyond (Pl : Set (K × K)) (hopen : OpenAlong Pl) (L : Dim K)
    (hL : L.zero ≠ L.one) {P : K × K} (hP : P ∈ Pl) (hPL : P ∉ L.points) {t : K}
    (ht : L.pt t ∉ Pl) :
    ∃ S₁ S₂ : Set (K × K), S₁ ≠ S₂ ∧ Misses Pl L P S₁ ∧ Misses Pl L P S₂ :=
  ⟨euclid Pl L P, toward Pl L P t, euclid_ne_toward Pl hopen L hL hP hPL t,
    euclid_misses Pl L hL hP hPL, toward_misses Pl L hL hP hPL ht⟩

/-- **Playfair's postulate holds for `L` exactly when every number of `L` is a point of the
plane.** -/
theorem one_parallel_iff (Pl : Set (K × K)) (hopen : OpenAlong Pl) (L : Dim K)
    (hL : L.zero ≠ L.one) {P : K × K} (hP : P ∈ Pl) (hPL : P ∉ L.points) :
    (∃! S, Misses Pl L P S) ↔ ∀ t : K, L.pt t ∈ Pl := by
  constructor
  · intro h t
    by_contra ht
    obtain ⟨S₁, S₂, hne, h₁, h₂⟩ := two_parallels_of_beyond Pl hopen L hL hP hPL ht
    exact hne (h.unique h₁ h₂)
  · exact one_parallel_of_all_within Pl L hL hP hPL

/-- **If infinitely many numbers of `L` are not points of the plane, infinitely many lines
through `P` do not meet `L`.** -/
theorem infinitely_many_parallels (Pl : Set (K × K)) (hopen : OpenAlong Pl) (L : Dim K)
    (hL : L.zero ≠ L.one) {P : K × K} (hP : P ∈ Pl) (hPL : P ∉ L.points)
    (hbeyond : {t : K | L.pt t ∉ Pl}.Infinite) : {S | Misses Pl L P S}.Infinite :=
  Set.infinite_of_injOn_mapsTo (toward_injective Pl hopen L hL hP hPL).injOn
    (fun _ ht => toward_misses Pl L hL hP hPL ht) hbeyond

end Planes

/-! ## Identities that need no order -/

section Identities

variable {K : Type*} [CommRing K]

/-- The bound along a dimension is a quadratic in the number. -/
theorem bound_along (κ : K) (M : Dim K) (t : K) :
    1 + κ * ((M.pt t).1 ^ 2 + (M.pt t).2 ^ 2)
      = (1 + κ * (M.zero.1 ^ 2 + M.zero.2 ^ 2))
        + (2 * κ * (M.zero.1 * M.dir.1 + M.zero.2 * M.dir.2)) * t
        - (-κ * (M.dir.1 ^ 2 + M.dir.2 ^ 2)) * t ^ 2 := by
  simp only [Dim.pt, Dim.dir]
  ring

end Identities

/-! ## The choice: the bound -/

section Bound

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Near its zero a quadratic is positive, if it is positive at its zero. -/
theorem quad_pos (α β γ : K) (hα : 0 < α) (hγ : 0 ≤ γ) :
    ∃ t : K, 0 < t ∧ 0 < α + β * t - γ * t ^ 2 := by
  have hD : 0 < α + β ^ 2 + 1 + γ := by nlinarith [sq_nonneg β]
  obtain ⟨t, ht⟩ : ∃ t : K, t * (α + β ^ 2 + 1 + γ) = α := ⟨_, div_mul_cancel₀ _ hD.ne'⟩
  have ht0 : 0 < t := by
    have h : 0 < t * (α + β ^ 2 + 1 + γ) := by
      rw [ht]
      exact hα
    exact (mul_pos_iff_of_pos_right hD).mp h
  refine ⟨t, ht0, ?_⟩
  have hβ : 0 < β ^ 2 + β + 1 := by nlinarith [sq_nonneg (β + 1), sq_nonneg β]
  have h1 : 0 < (α + β ^ 2 + 1) * (α + β ^ 2 + 1 + γ + β) :=
    mul_pos (by nlinarith [sq_nonneg β]) (by linarith)
  have h2 : 0 ≤ γ * (β ^ 2 + β + 1 + γ) := mul_nonneg hγ (by linarith)
  have hX : (α + β ^ 2 + 1 + γ) ^ 2 * (α + β * t - γ * t ^ 2)
      = α * ((α + β ^ 2 + 1) * (α + β ^ 2 + 1 + γ + β) + γ * (β ^ 2 + β + 1 + γ)) := by
    linear_combination
      (β * (α + β ^ 2 + 1 + γ) - γ * (t * (α + β ^ 2 + 1 + γ) + α)) * ht
  have hpos : 0 < (α + β ^ 2 + 1 + γ) ^ 2 * (α + β * t - γ * t ^ 2) := by
    rw [hX]
    exact mul_pos hα (by linarith)
  exact (mul_pos_iff_of_pos_left (pow_pos hD 2)).mp hpos

/-- Far enough along, a quadratic that opens downward is not positive. -/
theorem quad_nonpos (α β γ : K) (hγ : 0 < γ) :
    ∃ T : K, ∀ t : K, T ≤ t → α + β * t - γ * t ^ 2 ≤ 0 := by
  obtain ⟨c, hc⟩ : ∃ c : K, c * γ = α ^ 2 + β ^ 2 + 2 := ⟨_, div_mul_cancel₀ _ hγ.ne'⟩
  have hc0 : 0 < c := by
    have h : 0 < c * γ := by
      rw [hc]
      positivity
    exact (mul_pos_iff_of_pos_right hγ).mp h
  refine ⟨c + 1, fun t ht => ?_⟩
  have h1 : 1 ≤ t := by linarith
  have h2 : α ^ 2 + β ^ 2 + 2 ≤ t * γ := by
    have h := mul_le_mul_of_nonneg_right (show c ≤ t by linarith) hγ.le
    linarith
  have h3 : (α ^ 2 + β ^ 2 + 2) * t ≤ t * γ * t := mul_le_mul_of_nonneg_right h2 (by linarith)
  have h4 : 0 ≤ (α ^ 2 + 1) * (t - 1) := mul_nonneg (by positivity) (by linarith)
  have h5 : 0 ≤ (β ^ 2 - β + 1) * t :=
    mul_nonneg (by nlinarith [sq_nonneg (β - 1), sq_nonneg β]) (by linarith)
  have h6 : α ≤ α ^ 2 + 1 := by nlinarith [sq_nonneg (α - 1), sq_nonneg α]
  nlinarith only [h3, h4, h5, h6]

theorem sq_add_sq_pos {v : K × K} (hv : v ≠ (0, 0)) : 0 < v.1 ^ 2 + v.2 ^ 2 := by
  by_contra h
  have hle : v.1 ^ 2 + v.2 ^ 2 ≤ 0 := not_lt.mp h
  have h1 : v.1 ^ 2 = 0 := by linarith [sq_nonneg v.1, sq_nonneg v.2]
  have h2 : v.2 ^ 2 = 0 := by linarith [sq_nonneg v.1, sq_nonneg v.2]
  exact hv (Prod.ext ((pow_eq_zero_iff two_ne_zero).mp h1) ((pow_eq_zero_iff two_ne_zero).mp h2))

/-- **The choice.** The plane of the bound `κ`: the pairs `(x, y)` with
`0 < 1 + κ (x² + y²)`. -/
@[expose] def plane (κ : K) : Set (K × K) := {p | 0 < 1 + κ * (p.1 ^ 2 + p.2 ^ 2)}

omit [IsStrictOrderedRing K] in
theorem mem_plane {κ : K} {p : K × K} : p ∈ plane κ ↔ 0 < 1 + κ * (p.1 ^ 2 + p.2 ^ 2) :=
  Iff.rfl

/-- **With the bound 0, or any bound that is not negative, every pair is a point.** This is
the plane of the three-dimensions section. -/
theorem plane_eq_univ {κ : K} (hκ : 0 ≤ κ) : plane κ = Set.univ := by
  apply Set.eq_univ_of_forall
  intro p
  have h : 0 ≤ κ * (p.1 ^ 2 + p.2 ^ 2) := mul_nonneg hκ (by positivity)
  rw [mem_plane]
  linarith

theorem plane_zero : plane (0 : K) = Set.univ := plane_eq_univ le_rfl

/-- The pair `(0, 0)` is a point, whatever the bound. -/
theorem zero_mem_plane (κ : K) : ((0 : K), (0 : K)) ∈ plane κ := by
  rw [mem_plane]
  simp

/-- A smaller bound gives a smaller plane. -/
theorem plane_mono {κ κ' : K} (h : κ ≤ κ') : plane κ ⊆ plane κ' := by
  intro p hp
  rw [mem_plane] at hp ⊢
  have h' : κ * (p.1 ^ 2 + p.2 ^ 2) ≤ κ' * (p.1 ^ 2 + p.2 ^ 2) :=
    mul_le_mul_of_nonneg_right h (by positivity)
  linarith

omit [IsStrictOrderedRing K] in
/-- The bound `κ s²` is the bound `κ` with every pair made `s` times as large. -/
theorem mem_plane_scale (κ s : K) (p : K × K) :
    p ∈ plane (κ * s ^ 2) ↔ (s * p.1, s * p.2) ∈ plane κ := by
  rw [mem_plane, mem_plane]
  have e : 1 + κ * s ^ 2 * (p.1 ^ 2 + p.2 ^ 2) = 1 + κ * ((s * p.1) ^ 2 + (s * p.2) ^ 2) := by
    ring
  rw [e]

/-- From a point of the plane, every dimension has a further number in the plane. -/
theorem plane_open_forward (κ : K) (M : Dim K) (hM : M.zero ∈ plane κ) :
    ∃ t : K, 0 < t ∧ M.pt t ∈ plane κ := by
  rcases le_or_gt 0 κ with hκ | hκ
  · exact ⟨1, one_pos, by rw [plane_eq_univ hκ]; trivial⟩
  · obtain ⟨t, ht, h⟩ := quad_pos (1 + κ * (M.zero.1 ^ 2 + M.zero.2 ^ 2))
      (2 * κ * (M.zero.1 * M.dir.1 + M.zero.2 * M.dir.2))
      (-κ * (M.dir.1 ^ 2 + M.dir.2 ^ 2)) hM
      (mul_nonneg (by linarith) (by positivity))
    refine ⟨t, ht, ?_⟩
    rw [mem_plane, bound_along]
    exact h

/-- The plane of a bound is open along the dimensions. -/
theorem plane_openAlong (κ : K) : OpenAlong (plane κ) := by
  intro M hM
  obtain ⟨t, ht, h⟩ := plane_open_forward κ M hM
  exact ⟨t, ht.ne', h⟩

/-- **Under a negative bound every dimension leaves the plane.** From some number on, none of
its numbers is a point. -/
theorem plane_beyond {κ : K} (hκ : κ < 0) (L : Dim K) (hL : L.zero ≠ L.one) :
    ∃ T : K, ∀ t : K, T ≤ t → L.pt t ∉ plane κ := by
  obtain ⟨T, hT⟩ := quad_nonpos (1 + κ * (L.zero.1 ^ 2 + L.zero.2 ^ 2))
    (2 * κ * (L.zero.1 * L.dir.1 + L.zero.2 * L.dir.2)) (-κ * (L.dir.1 ^ 2 + L.dir.2 ^ 2))
    (mul_pos (by linarith) (sq_add_sq_pos (L.dir_ne_zero hL)))
  refine ⟨T, fun t ht hmem => ?_⟩
  have h := hT t ht
  rw [← bound_along] at h
  exact absurd (mem_plane.mp hmem) (not_lt.mpr h)

theorem plane_beyond_infinite {κ : K} (hκ : κ < 0) (L : Dim K) (hL : L.zero ≠ L.one) :
    {t : K | L.pt t ∉ plane κ}.Infinite := by
  obtain ⟨T, hT⟩ := plane_beyond hκ L hL
  exact (Set.Ici_infinite T).mono (fun t ht => hT t ht)

/-- **Under a negative bound a dimension has a bounded stretch of its numbers in the
plane.** -/
theorem plane_stretch {κ : K} (hκ : κ < 0) (L : Dim K) (hL : L.zero ≠ L.one) :
    ∃ T : K, ∀ t : K, L.pt t ∈ plane κ → -T < t ∧ t < T := by
  have hγ : 0 < -κ * (L.dir.1 ^ 2 + L.dir.2 ^ 2) :=
    mul_pos (by linarith) (sq_add_sq_pos (L.dir_ne_zero hL))
  obtain ⟨T₁, h₁⟩ := quad_nonpos (1 + κ * (L.zero.1 ^ 2 + L.zero.2 ^ 2))
    (2 * κ * (L.zero.1 * L.dir.1 + L.zero.2 * L.dir.2)) _ hγ
  obtain ⟨T₂, h₂⟩ := quad_nonpos (1 + κ * (L.zero.1 ^ 2 + L.zero.2 ^ 2))
    (-(2 * κ * (L.zero.1 * L.dir.1 + L.zero.2 * L.dir.2))) _ hγ
  refine ⟨max T₁ T₂, fun t ht => ?_⟩
  rw [mem_plane, bound_along] at ht
  constructor
  · by_contra h
    have h' : T₂ ≤ -t := by
      have := not_lt.mp h
      linarith [le_max_right T₁ T₂]
    have h'' := h₂ (-t) h'
    have e : (1 + κ * (L.zero.1 ^ 2 + L.zero.2 ^ 2))
        + -(2 * κ * (L.zero.1 * L.dir.1 + L.zero.2 * L.dir.2)) * -t
        - -κ * (L.dir.1 ^ 2 + L.dir.2 ^ 2) * (-t) ^ 2
        = (1 + κ * (L.zero.1 ^ 2 + L.zero.2 ^ 2))
        + (2 * κ * (L.zero.1 * L.dir.1 + L.zero.2 * L.dir.2)) * t
        - -κ * (L.dir.1 ^ 2 + L.dir.2 ^ 2) * t ^ 2 := by ring
    rw [e] at h''
    linarith
  · by_contra h
    have h' : T₁ ≤ t := le_trans (le_max_left _ _) (not_lt.mp h)
    linarith [h₁ t h']

/-- **The plane of a bound is in one piece along every dimension.** Between two points of the
plane, every number of the dimension from the one to the other is a point of the plane. -/
theorem plane_convex (κ : K) {A B : K × K} (hA : A ∈ plane κ) (hB : B ∈ plane κ) {u : K}
    (h0 : 0 ≤ u) (h1 : u ≤ 1) : (Dim.mk A B).pt u ∈ plane κ := by
  rcases le_or_gt 0 κ with hκ | hκ
  · rw [plane_eq_univ hκ]
    trivial
  · rw [mem_plane] at hA hB ⊢
    have e : 1 + κ * (((Dim.mk A B).pt u).1 ^ 2 + ((Dim.mk A B).pt u).2 ^ 2)
        = (1 - u) * (1 + κ * (A.1 ^ 2 + A.2 ^ 2)) + u * (1 + κ * (B.1 ^ 2 + B.2 ^ 2))
          + -κ * (u * (1 - u)) * ((B.1 - A.1) ^ 2 + (B.2 - A.2) ^ 2) := by
      simp only [Dim.pt]
      ring
    rw [e]
    have hlast : 0 ≤ -κ * (u * (1 - u)) * ((B.1 - A.1) ^ 2 + (B.2 - A.2) ^ 2) :=
      mul_nonneg (mul_nonneg (by linarith) (mul_nonneg h0 (by linarith))) (by positivity)
    have hB' : 0 ≤ u * (1 + κ * (B.1 ^ 2 + B.2 ^ 2)) := mul_nonneg h0 hB.le
    rcases h1.eq_or_lt with hu | hu
    · rw [hu] at hlast ⊢
      linarith
    · have hA' : 0 < (1 - u) * (1 + κ * (A.1 ^ 2 + A.2 ^ 2)) := mul_pos (by linarith) hA
      linarith

/-! ### Points and lines -/

/-- **There are three points of the plane that are not on one line.** -/
theorem exists_three_points (κ : K) :
    ∃ A B C : K × K, A ∈ plane κ ∧ B ∈ plane κ ∧ C ∈ plane κ ∧
      ∀ S, IsLine (plane κ) S → ¬ (A ∈ S ∧ B ∈ S ∧ C ∈ S) := by
  obtain ⟨t, ht, hB⟩ := plane_openAlong κ ⟨(0, 0), (1, 0)⟩ (zero_mem_plane κ)
  obtain ⟨u, hu, hC⟩ := plane_openAlong κ ⟨(0, 0), (0, 1)⟩ (zero_mem_plane κ)
  refine ⟨(0, 0), _, _, zero_mem_plane κ, hB, hC, ?_⟩
  rintro S ⟨M, -, rfl, -⟩ ⟨hA', hB', hC'⟩
  have hAB : ((0 : K), (0 : K)) ≠ (Dim.mk ((0 : K), (0 : K)) (1, 0)).pt t := by
    intro h
    have h1 := congrArg Prod.fst h
    simp only [Dim.pt] at h1
    apply ht
    linear_combination -h1
  rw [M.points_eq_through hA'.1 hB'.1 hAB] at hC'
  obtain ⟨⟨s, hs⟩, -⟩ := hC'
  have h2 := congrArg Prod.snd hs
  simp only [Dim.pt] at h2
  apply hu
  linear_combination -h2

/-- The plane of a bound has a line and a point that is not on it. -/
theorem plane_exists_line_and_point (κ : K) :
    ∃ (S : Set (K × K)) (P : K × K), IsLine (plane κ) S ∧ P ∈ plane κ ∧ P ∉ S :=
  exists_line_and_point (plane_openAlong κ) (zero_mem_plane κ)

/-- `B` is between `A` and `C`: the two are different, and `B` is at a number between 0 and 1
of the dimension from `A` to `C`. -/
@[expose] def Between (A B C : K × K) : Prop :=
  A ≠ C ∧ ∃ u : K, 0 < u ∧ u < 1 ∧ (Dim.mk A C).pt u = B

/-- If `B` is between `A` and `C`, it is between `C` and `A`. -/
theorem Between.symm {A B C : K × K} (h : Between A B C) : Between C B A := by
  obtain ⟨hAC, u, h0, h1, rfl⟩ := h
  refine ⟨hAC.symm, 1 - u, by linarith, by linarith, ?_⟩
  apply Prod.ext
  · simp only [Dim.pt]
    ring
  · simp only [Dim.pt]
    ring

omit [IsStrictOrderedRing K] in
/-- A pair between `A` and `C` is a pair of the dimension from `A` to `C`. -/
theorem Between.mem {A B C : K × K} (h : Between A B C) : B ∈ (Dim.mk A C).points := by
  obtain ⟨-, u, -, -, rfl⟩ := h
  exact ⟨u, rfl⟩

/-- If `B` is between `A` and `C`, the three are different. -/
theorem Between.ne {A B C : K × K} (h : Between A B C) : A ≠ B ∧ B ≠ C ∧ A ≠ C := by
  obtain ⟨hAC, u, h0, h1, rfl⟩ := h
  have hinj := (Dim.mk A C).pt_injective hAC
  refine ⟨?_, ?_, hAC⟩
  · intro h'
    have h2 := hinj ((Dim.mk A C).pt_zero.trans h')
    linarith
  · intro h'
    have h2 := hinj (h'.trans (Dim.mk A C).pt_one.symm)
    linarith

/-- **Of three pairs of a dimension, one only is between the other two.** If `B` is between
`A` and `C`, then `A` is not between `B` and `C`. -/
theorem Between.not_left {A B C : K × K} (h : Between A B C) : ¬ Between B A C := by
  obtain ⟨hAC, u, hu0, hu1, rfl⟩ := h
  rintro ⟨-, v, hv0, hv1, hv⟩
  have e1 := congrArg Prod.fst hv
  have e2 := congrArg Prod.snd hv
  simp only [Dim.pt] at e1 e2
  have hk : 0 < u + v * (1 - u) := by
    have h' := mul_pos hv0 (sub_pos.mpr hu1)
    linarith
  have h1 : (u + v * (1 - u)) * (C.1 - A.1) = 0 := by linear_combination e1
  have h2 : (u + v * (1 - u)) * (C.2 - A.2) = 0 := by linear_combination e2
  apply hAC
  apply Prod.ext
  · have h3 := (mul_eq_zero.mp h1).resolve_left hk.ne'
    linarith
  · have h3 := (mul_eq_zero.mp h2).resolve_left hk.ne'
    linarith

/-- And `C` is not between `A` and `B`. -/
theorem Between.not_right {A B C : K × K} (h : Between A B C) : ¬ Between A C B := by
  obtain ⟨hAC, u, hu0, hu1, rfl⟩ := h
  rintro ⟨-, v, hv0, hv1, hv⟩
  have e1 := congrArg Prod.fst hv
  have e2 := congrArg Prod.snd hv
  simp only [Dim.pt] at e1 e2
  have hk : 0 < 1 - v * u := by
    have h' := mul_pos hv0 (sub_pos.mpr hu1)
    nlinarith
  have h1 : (1 - v * u) * (C.1 - A.1) = 0 := by linear_combination -e1
  have h2 : (1 - v * u) * (C.2 - A.2) = 0 := by linear_combination -e2
  apply hAC
  apply Prod.ext
  · have h3 := (mul_eq_zero.mp h1).resolve_left hk.ne'
    linarith
  · have h3 := (mul_eq_zero.mp h2).resolve_left hk.ne'
    linarith

/-- **A line can be produced.** Beyond a point `C` of the plane, as seen from another pair `A`,
there is a point of the plane. -/
theorem exists_beyond (κ : K) {A C : K × K} (hAC : A ≠ C) (hC : C ∈ plane κ) :
    ∃ B : K × K, B ∈ plane κ ∧ Between A C B := by
  obtain ⟨s, hs, hB⟩ :=
    plane_open_forward κ ⟨C, (C.1 + (C.1 - A.1), C.2 + (C.2 - A.2))⟩ hC
  have hs1 : 0 < 1 + s := by linarith
  have h1 : 1 / (1 + s) * (1 + s) = 1 := div_mul_cancel₀ _ hs1.ne'
  refine ⟨_, hB, ?_, 1 / (1 + s), div_pos one_pos hs1, ?_, ?_⟩
  · intro h
    apply hAC
    have e1 := congrArg Prod.fst h
    have e2 := congrArg Prod.snd h
    simp only [Dim.pt] at e1 e2
    have k1 : (1 + s) * (C.1 - A.1) = 0 := by linear_combination -e1
    have k2 : (1 + s) * (C.2 - A.2) = 0 := by linear_combination -e2
    apply Prod.ext
    · have h3 := (mul_eq_zero.mp k1).resolve_left hs1.ne'
      linarith
    · have h3 := (mul_eq_zero.mp k2).resolve_left hs1.ne'
      linarith
  · rw [div_lt_one hs1]
    linarith
  · apply Prod.ext
    · simp only [Dim.pt]
      linear_combination (C.1 - A.1) * h1
    · simp only [Dim.pt]
      linear_combination (C.2 - A.2) * h1

/-- Two points of the plane on opposite sides of a dimension: between them the dimension has
a point of the plane. -/
theorem crosses (κ : K) (M : Dim K) (hM : M.zero ≠ M.one) {P Q : K × K} (hP : P ∈ plane κ)
    (hQ : Q ∈ plane κ) (h : M.side P * M.side Q < 0) :
    ∃ Y : K × K, Y ∈ M.points ∧ Y ∈ plane κ ∧ Between P Y Q := by
  have hf0 : M.side P ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h
    exact lt_irrefl _ h
  have hf2 : 0 < M.side P ^ 2 := lt_of_le_of_ne (sq_nonneg _) (pow_ne_zero 2 hf0).symm
  have hden : 0 < M.side P ^ 2 - M.side P * M.side Q := by linarith
  obtain ⟨v, hv⟩ : ∃ v : K, v * (M.side P ^ 2 - M.side P * M.side Q) = M.side P ^ 2 :=
    ⟨_, div_mul_cancel₀ _ hden.ne'⟩
  have hv0 : 0 < v := by
    have h' : 0 < v * (M.side P ^ 2 - M.side P * M.side Q) := by
      rw [hv]
      exact hf2
    exact (mul_pos_iff_of_pos_right hden).mp h'
  have hv1 : v < 1 := by
    by_contra hcon
    have h' := mul_le_mul_of_nonneg_right (not_lt.mp hcon) hden.le
    linarith
  have hPQ : P ≠ Q := by
    intro h'
    rw [h'] at h
    exact absurd h (not_lt.mpr (mul_self_nonneg _))
  refine ⟨(Dim.mk P Q).pt v, ?_, plane_convex κ hP hQ hv0.le hv1.le, hPQ, v, hv0, hv1, rfl⟩
  apply M.mem_points_of_side_eq_zero hM
  rw [M.side_through]
  have h0 : M.side P * ((1 - v) * M.side P + v * M.side Q) = 0 := by
    linear_combination -hv
  exact (mul_eq_zero.mp h0).resolve_left hf0

/-- **Pasch's axiom.** Let `A`, `B` and `C` be points of the plane, and let a dimension pass
through none of them. If it has a pair between `A` and `B`, it has a point of the plane between
`A` and `C`, or between `B` and `C`. -/
theorem pasch (κ : K) {A B C : K × K} (hA : A ∈ plane κ) (hB : B ∈ plane κ)
    (hC : C ∈ plane κ) (M : Dim K) (hM : M.zero ≠ M.one) (hAM : A ∉ M.points)
    (hBM : B ∉ M.points) (hCM : C ∉ M.points) {X : K × K} (hX : X ∈ M.points)
    (hAXB : Between A X B) :
    ∃ Y : K × K, Y ∈ M.points ∧ Y ∈ plane κ ∧ (Between A Y C ∨ Between B Y C) := by
  have fA : M.side A ≠ 0 := fun h => hAM (M.mem_points_of_side_eq_zero hM A h)
  have fB : M.side B ≠ 0 := fun h => hBM (M.mem_points_of_side_eq_zero hM B h)
  have fC : M.side C ≠ 0 := fun h => hCM (M.mem_points_of_side_eq_zero hM C h)
  have fA2 : 0 < M.side A ^ 2 := lt_of_le_of_ne (sq_nonneg _) (pow_ne_zero 2 fA).symm
  have fB2 : 0 < M.side B ^ 2 := lt_of_le_of_ne (sq_nonneg _) (pow_ne_zero 2 fB).symm
  obtain ⟨-, u, hu0, hu1, rfl⟩ := hAXB
  have hX0 := M.side_eq_zero_of_mem hX
  rw [M.side_through] at hX0
  have hAB : M.side A * M.side B < 0 := by
    have h1 : (1 - u) * (M.side A * M.side B) = -(u * M.side B ^ 2) := by
      linear_combination M.side B * hX0
    have h2 : 0 < u * M.side B ^ 2 := mul_pos hu0 fB2
    by_contra hcon
    have h3 := mul_nonneg (show (0 : K) ≤ 1 - u by linarith) (not_lt.mp hcon)
    linarith
  rcases lt_or_gt_of_ne (mul_ne_zero fA fC) with h | h
  · obtain ⟨Y, h1, h2, h3⟩ := crosses κ M hM hA hC h
    exact ⟨Y, h1, h2, Or.inl h3⟩
  · have hBC : M.side B * M.side C < 0 := by
      have h1 : M.side A ^ 2 * (M.side B * M.side C)
          = (M.side A * M.side B) * (M.side A * M.side C) := by ring
      have h2 : (M.side A * M.side B) * (M.side A * M.side C) < 0 :=
        mul_neg_of_neg_of_pos hAB h
      by_contra hcon
      have h3 := mul_nonneg fA2.le (not_lt.mp hcon)
      linarith
    obtain ⟨Y, h1, h2, h3⟩ := crosses κ M hM hB hC hBC
    exact ⟨Y, h1, h2, Or.inr h3⟩

/-! ### The parallels -/

/-- **Under a negative bound, through a point that is not on a line there are infinitely many
lines that do not meet the line.** -/
theorem hyperbolic_parallels {κ : K} (hκ : κ < 0) {S : Set (K × K)} (hS : IsLine (plane κ) S)
    {P : K × K} (hP : P ∈ plane κ) (hPS : P ∉ S) :
    {M : Set (K × K) | IsLine (plane κ) M ∧ P ∈ M ∧ M ∩ S = ∅}.Infinite := by
  obtain ⟨L, hL, rfl, -⟩ := hS
  have hPL : P ∉ L.points := fun h => hPS ⟨h, hP⟩
  exact infinitely_many_parallels (plane κ) (plane_openAlong κ) L hL hP hPL
    (plane_beyond_infinite hκ L hL)

/-- **Under a negative bound, through a point that is not on a line there are two different
lines that do not meet the line.** -/
theorem hyperbolic_two_parallels {κ : K} (hκ : κ < 0) {S : Set (K × K)}
    (hS : IsLine (plane κ) S) {P : K × K} (hP : P ∈ plane κ) (hPS : P ∉ S) :
    ∃ M₁ M₂ : Set (K × K), M₁ ≠ M₂ ∧ (IsLine (plane κ) M₁ ∧ P ∈ M₁ ∧ M₁ ∩ S = ∅) ∧
      (IsLine (plane κ) M₂ ∧ P ∈ M₂ ∧ M₂ ∩ S = ∅) := by
  obtain ⟨M₁, h₁, M₂, h₂, hne⟩ := (hyperbolic_parallels hκ hS hP hPS).nontrivial
  exact ⟨M₁, M₂, hne, h₁, h₂⟩

/-- **The parallels under a negative bound.** Under a negative bound, through a given point
that is not on a line there are at least two different lines, and in fact infinitely many,
that do not meet the given line. -/
theorem hyperbolic_parallel_property {κ : K} (hκ : κ < 0) {S : Set (K × K)}
    (hS : IsLine (plane κ) S) {P : K × K} (hP : P ∈ plane κ) (hPS : P ∉ S) :
    (∃ M₁ M₂ : Set (K × K), M₁ ≠ M₂ ∧ (IsLine (plane κ) M₁ ∧ P ∈ M₁ ∧ M₁ ∩ S = ∅) ∧
      (IsLine (plane κ) M₂ ∧ P ∈ M₂ ∧ M₂ ∩ S = ∅)) ∧
    {M : Set (K × K) | IsLine (plane κ) M ∧ P ∈ M ∧ M ∩ S = ∅}.Infinite :=
  ⟨hyperbolic_two_parallels hκ hS hP hPS, hyperbolic_parallels hκ hS hP hPS⟩

/-- **With the bound 0, or any bound that is not negative, the plane is that of
the three-dimensions section:** through a point that is not on a line there is one line that does
not
meet the line, and only one. -/
theorem euclid_one_parallel {κ : K} (hκ : 0 ≤ κ) {S : Set (K × K)} (hS : IsLine (plane κ) S)
    {P : K × K} (hPS : P ∉ S) : ∃! M, IsLine (plane κ) M ∧ P ∈ M ∧ M ∩ S = ∅ := by
  obtain ⟨L, hL, rfl, -⟩ := hS
  have hP : P ∈ plane κ := by
    rw [plane_eq_univ hκ]
    trivial
  have hPL : P ∉ L.points := fun h => hPS ⟨h, hP⟩
  exact one_parallel_of_all_within (plane κ) L hL hP hPL
    (fun t => by rw [plane_eq_univ hκ]; trivial)

/-- **Theorem E4 (the three-dimensions section) holds in the plane of a bound that is not
negative.** In a
figure,
let `b1` and `c1` lie on the left of `a`, and let the cross product of the directions of `b`
and `c` be positive. Then `b` and `c` meet at a point of the plane, on the left of `a`. -/
theorem fifth_postulate_of_nonneg_bound {κ : K} (hκ : 0 ≤ κ) (F : Figure K)
    (hb : 0 < F.a.side F.b.one) (hc : 0 < F.a.side F.c.one)
    (hsum : 0 < cross F.b.dir F.c.dir) :
    ∃ t u : K, 0 < t ∧ 0 < u ∧ F.b.pt t = F.c.pt u ∧ F.b.pt t ∈ plane κ ∧
      0 < F.a.side (F.b.pt t) := by
  rw [F.side_b_one] at hb
  rw [F.side_c_one] at hc
  have ht : 0 < cross F.a.dir F.c.dir / cross F.b.dir F.c.dir := div_pos hc hsum
  refine ⟨_, _, ht, div_pos hb hsum, F.meet_eq hsum.ne', ?_, ?_⟩
  · rw [plane_eq_univ hκ]
    trivial
  · rw [F.side_b_pt]
    exact mul_pos ht hb

/-- **One parallel exactly when the bound is not negative.** -/
theorem one_parallel_iff_bound {κ : K} {S : Set (K × K)} (hS : IsLine (plane κ) S)
    {P : K × K} (hP : P ∈ plane κ) (hPS : P ∉ S) :
    (∃! M, IsLine (plane κ) M ∧ P ∈ M ∧ M ∩ S = ∅) ↔ 0 ≤ κ := by
  constructor
  · intro h
    by_contra hκ
    obtain ⟨M₁, M₂, hne, h₁, h₂⟩ := hyperbolic_two_parallels (not_le.mp hκ) hS hP hPS
    exact hne (h.unique h₁ h₂)
  · intro hκ
    exact euclid_one_parallel hκ hS hPS

end Bound

/-! ## Three points on a line, and the numbers of a dimension -/

/-- **Of three different points on a line, one is between the two others.** -/
theorem between_trichotomy {A B C : ℝ × ℝ} (hAB : A ≠ B) (hBC : B ≠ C) (hAC : A ≠ C)
    (hB : B ∈ (Dim.mk A C).points) : Between A B C ∨ Between B A C ∨ Between A C B := by
  obtain ⟨s, rfl⟩ := hB
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact hAB (Dim.pt_zero (Dim.mk A C)).symm
  have hs1 : s ≠ 1 := by
    rintro rfl
    exact hBC (Dim.pt_one (Dim.mk A C))
  rcases lt_or_gt_of_ne hs0 with hneg | hpos
  · have h1s : 0 < 1 - s := by linarith
    refine Or.inr (Or.inl ⟨hBC, -s / (1 - s), div_pos (by linarith) h1s,
      (div_lt_one h1s).mpr (by linarith), ?_⟩)
    apply Prod.ext
    · simp only [Dim.pt]
      field_simp
      ring
    · simp only [Dim.pt]
      field_simp
      ring
  · rcases lt_or_gt_of_ne hs1 with hlt | hgt
    · exact Or.inl ⟨hAC, s, hpos, hlt, rfl⟩
    · refine Or.inr (Or.inr ⟨hAB, 1 / s, by positivity, (div_lt_one hpos).mpr hgt, ?_⟩)
      apply Prod.ext
      · simp only [Dim.pt]
        field_simp
        ring
      · simp only [Dim.pt]
        field_simp
        ring

/-- A pair of the plane off a line has a side that is not 0, and the three points that make
the side not 0 are different. -/
theorem ne_of_side_ne_zero {X Y Z : ℝ × ℝ} (h : (Dim.mk X Y).side Z ≠ 0) :
    X ≠ Y ∧ Z ≠ X ∧ Z ≠ Y := by
  refine ⟨?_, ?_, ?_⟩
  · rintro rfl
    apply h
    simp [Dim.side, Dim.dir, cross]
  · rintro rfl
    apply h
    simp [Dim.side, Dim.dir, cross]
  · rintro rfl
    apply h
    simp only [Dim.side, Dim.dir, cross]
    ring

/-- A line of the plane is a set of points of the plane. -/
theorem IsLine.subset_plane {κ : ℝ} {S : Set (ℝ × ℝ)} (hS : IsLine (plane κ) S) :
    S ⊆ plane κ := by
  obtain ⟨M, -, rfl, -⟩ := hS
  exact fun _ hx => hx.2

/-- A line of the plane through two different points of it is what the dimension through them
has in the plane. -/
theorem IsLine.eq_through {κ : ℝ} {S : Set (ℝ × ℝ)} (hS : IsLine (plane κ) S) {D F : ℝ × ℝ}
    (hD : D ∈ S) (hF : F ∈ S) (hDF : D ≠ F) : S = (Dim.mk D F).points ∩ plane κ := by
  obtain ⟨M, -, rfl, -⟩ := hS
  rw [M.points_eq_through hD.1 hF.1 hDF]

/-- `c` is strictly between `a` and `b`, on either side. -/
@[expose] def StrictBetween (a c b : ℝ) : Prop := (a < c ∧ c < b) ∨ (b < c ∧ c < a)

/-- **Numbers in order give pairs in order.** -/
theorem between_pt_of_strictBetween (M : Dim ℝ) (hM : M.zero ≠ M.one) {a b c : ℝ}
    (h : StrictBetween a c b) : Between (M.pt a) (M.pt c) (M.pt b) := by
  have hab : a ≠ b := by
    rintro rfl
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith
  refine ⟨fun e => hab (M.pt_injective hM e), (c - a) / (b - a), ?_, ?_, ?_⟩
  · rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact div_pos (by linarith) (by linarith)
    · exact div_pos_of_neg_of_neg (by linarith) (by linarith)
  · rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact (div_lt_one (by linarith)).mpr (by linarith)
    · exact (div_lt_one_of_neg (by linarith)).mpr (by linarith)
  · have hba : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
    apply Prod.ext
    · simp only [Dim.pt]
      field_simp
      ring
    · simp only [Dim.pt]
      field_simp
      ring

/-- **Pairs in order come from numbers in order.** -/
theorem strictBetween_of_between_pt (M : Dim ℝ) (hM : M.zero ≠ M.one) {a b c : ℝ}
    (h : Between (M.pt a) (M.pt c) (M.pt b)) : StrictBetween a c b := by
  obtain ⟨hne, u, hu0, hu1, hu⟩ := h
  have hc : c = a + u * (b - a) := by
    apply M.pt_injective hM
    rw [← hu]
    apply Prod.ext
    · simp only [Dim.pt]
      ring
    · simp only [Dim.pt]
      ring
  have hab : a ≠ b := fun e => hne (by rw [e])
  rcases lt_or_gt_of_ne hab with h | h
  · left
    constructor <;> nlinarith
  · right
    constructor <;> nlinarith

/-- The numbers of a dimension whose pairs are points of the plane make an interval. -/
theorem pt_mem_plane_of_le {κ : ℝ} (M : Dim ℝ) {a b c : ℝ} (ha : M.pt a ∈ plane κ)
    (hb : M.pt b ∈ plane κ) (hac : a ≤ c) (hcb : c ≤ b) : M.pt c ∈ plane κ := by
  rcases hac.eq_or_lt with rfl | hac'
  · exact ha
  have hab : 0 < b - a := by linarith
  have e : M.pt c = (Dim.mk (M.pt a) (M.pt b)).pt ((c - a) / (b - a)) := by
    apply Prod.ext
    · simp only [Dim.pt]
      field_simp
      ring
    · simp only [Dim.pt]
      field_simp
      ring
  rw [e]
  exact plane_convex κ ha hb (div_nonneg (by linarith) hab.le)
    ((div_le_one hab).mpr (by linarith))

end HyperbolicPlane

end ParallelPostulate
