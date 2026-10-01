/-
Copyright (c) 2026 Richard Sutton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Richard Sutton
-/
module
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.LineDeriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Arsinh
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Coordinate Euclidean and Klein geometry

Coordinate infrastructure for the models in `Hilbert.lean`. The dimensions section develops
lines over commutative rings and fields. The three-dimensions section proves Euclid's fifth
postulate and its angle formulation over ordered fields and the real numbers, respectively.
The bounded-plane sections use the domain `0 < 1 + κ * (x² + y²)`: nonnegative bounds give the
whole affine plane, while negative bounds give Klein domains with infinitely many parallels.

The real-coordinate development constructs projective motions, invariant angles and metric,
Brioschi curvature, smooth-path distance, and Hilbert congruence constructions. Algebraic and
incidence/order results retain their upstream field generality. The explicit leaning figure
at bound `-1` has interior angles summing to less than `π`, yet its two lines do not meet.

## Scope

* The model is a set of coordinate pairs with lines obtained by intersecting affine lines
  with the domain. Its identification with other constructions of hyperbolic space is not
  formalized. Pasch order, congruence, Archimedes continuity, and Dedekind continuity are
  verified by the constructions in `Hilbert.lean`.
* `kleinAngle` agrees with Mathlib's Euclidean angle at the origin under every bound, and
  everywhere at bound zero. Its invariance and uniqueness under the projective motions are
  proved. Degenerate rays use Mathlib's totalized angle convention.
* `kleinMetric` is the coordinate bilinear form. Motion invariance uses Mathlib's actual
  Fréchet derivatives. `gaussCurvature` is Brioschi's coordinate formula; its identification
  with connection curvature or surface curvature is not formalized. The formula gives `κ`
  throughout the domain and gives `-1` for the upper-half-plane metric.
* `kleinDist` is the infimum of lengths of C1 paths on `[0, 1]`. Piecewise smooth paths and
  its identification with Mathlib's Riemannian distance are not formalized. Its closed form
  and relation to `apart` are proved for negative bounds.
* The angle counterexample is proved at bound `-1`; its rescaling to other negative bounds
  is not formalized. Positive bounds still have the whole affine coordinate plane; the
  interpretation as a half sphere is not formalized.
* Lean's division is totalized. `step_comm`, `apart_comm`, `apart_centre`, and `rot_apart`
  have identical quotients on both sides even at zero denominators. `step_neg`, `apart_self`,
  and `shift_axis` use division by zero at boundary points. Geometric model results supply
  domain and nonzero-denominator hypotheses where they are needed.

The upstream labels H11 and H12 concern a larger project and are absent from this development.
-/

public section

/-!
# Dimensions laid among the pairs of numbers

A dimension is a number line with its own zero and its own 1, laid among the pairs of numbers
of a ring `K`: `Dim`, with its direction `Dim.dir`, its pairs `Dim.pt` and `Dim.points`, and the
side `Dim.side` of a pair. `cross` is the cross product of two directions. A figure, `Figure`,
is three dimensions `a`, `b`, `c` with the two constraints

    a0 = b0        a1 = c0

so that `a` is the line that falls on the two others. the three-dimensions section and the files of
`HyperbolicPlane` both build on these, in the namespace `Pairs`.

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
# Three dimensions and the parallel postulate

Three dimensions `a`, `b`, `c`, each a number line with its own zero, and two constraints:

    a0 = b0        a1 = c0

So `a` is the straight line that falls on the two other lines: it meets `b` where `a` has its
zero, and `c` where `a` has its 1.

Checked with Lean `v4.35.0-rc3` and Mathlib at the matching tag (September 2026). Every theorem
uses only Lean's standard axioms `propext`, `Classical.choice` and `Quot.sound`.

The dimensions, the cross product and the figure, with their small facts, are in
the dimensions section, in the namespace `Pairs`. Some of the names below are there.

## Contents

* Lemma E1, read as numbers `a1 = c0` collapses `a`: `collapse`
* a dimension, its direction, its points, its sides: `Dim`, `Dim.dir`, `Dim.pt`, `Dim.points`,
  `Dim.side`
* the cross product: `cross`
* the figure, with the two constraints: `Figure`, `Figure.a0_eq_b0`, `Figure.a1_eq_c0`
* Lemma E2, three independent dimensions: `skew_of_independent`
* Example E3, whole numbers and fractions: `wholeFigure_hypotheses`, `whole_numbers_never_meet`,
  `exampleFigure_meets`
* Theorem E4, the postulate with no angle: `Figure.meet_eq`, `fifth_postulate`, and
  `fifth_postulate_right` on the right of `a`
* Theorem E5, the two other cases: `Figure.never_meet_of_two_right_angles`,
  `meet_on_the_other_side`, `meet_on_the_other_side_right`
* Theorem E6, exactly when: `Figure.meet_unique`, `meet_on_side_iff`, `meet_on_side_iff_right`
* Theorem E7, Playfair: `meet_of_cross_ne_zero`, `not_meet_of_cross_eq_zero`, `playfair_exists`,
  `playfair_unique`, `playfair_unique_through`
* a dimension with its zero moved: `Dim.rebase`, `Dim.rebase_points`, `meet_iff_common_point`
* Lemma E8, the sine of the two angles together: `sin_angle_sum`, `angle_pos_and_lt_pi`
* Theorem E9, the postulate as Euclid states it: `euclid_fifth_either_side`,
  `never_meet_either_side`, `other_side_either_side`, `meet_iff_angles_either_side`
* the same on the left of `a` only: `euclid_fifth_general`, `never_meet_general`,
  `other_side_general`, `meet_on_side_iff_angles`
* the figure with `a` run backwards: `Figure.reverse`, `Figure.reverse_side`,
  `Figure.reverse_angles`
* Proposition E10, the figure with given angles: `angleFigure`, `angle_at_a0`, `angle_at_a1`,
  `angleFigure_cross`, `law_of_sines`, `euclid_fifth`, `never_meet_of_sum_eq_pi`

## What is assumed, and what is not formalised

* **The postulate is not proved from Euclid's other postulates.** That cannot be done: the
  hyperbolic plane meets the others and fails this one. What is proved is that the plane of
  pairs of numbers of a field meets the postulate. It does so because of how it is made: adding
  moves a line to any point without turning it, and two lines of one plane meet if neither
  direction is a multiple of the other, because the numbers can be divided.
* **That this plane meets Euclid's other postulates** is not formalised.
* **That the plane is built from dimensions** is a reading, and is not in Lean. In this file
  the plane is `K × K`, and a dimension is any line in it with a zero and a 1.

-/

namespace ParallelPostulate

namespace ThreeDimensions

open Pairs

/-! ## Read as numbers, `a1 = c0` collapses the dimension `a` -/

/-- `ι n` is the number `n` of the plus world of `a`. The zero of a dimension is its own double:
`c0 + c0 = c0`. So if `a1` is `c0`, then `a1 + a1 = a1`. Every number of `a` is then `a0`. -/
theorem collapse {N : Type*} [Add N] (ι : ℤ → N)
    (hadd : ∀ m n : ℤ, ι (m + n) = ι m + ι n) (hidem : ι 1 + ι 1 = ι 1) (n : ℤ) :
    ι n = ι 0 := by
  have h2 : ι 2 = ι 1 := by
    have h := hadd 1 1
    rw [hidem] at h
    simpa using h
  have h10 : ι 1 = ι 0 := by
    have h := hadd 2 (-1)
    have h' := hadd 1 (-1)
    rw [h2] at h
    rw [← h'] at h
    simpa using h
  have hstep : ∀ m : ℤ, ι (m + 1) = ι m := by
    intro m
    have h := hadd m 1
    have h' := hadd m 0
    rw [h10, ← h'] at h
    simpa using h
  induction n using Int.induction_on with
  | zero => rfl
  | succ k ih => rw [hstep]; exact ih
  | pred k ih =>
    have h := hstep (-(k : ℤ) - 1)
    rw [sub_add_cancel] at h
    rw [← h]; exact ih

/-! ## Three independent dimensions: the two lines never meet -/

/-- `a` runs from `O` to `O + a`. The line `b` leaves `O` and the line `c` leaves `O + a`. If the
three directions are independent, the two lines have no point in common. -/
theorem skew_of_independent {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (O a b c : V) (h : LinearIndependent K ![a, b, c]) (t u : K) :
    O + t • b ≠ O + a + u • c := by
  intro heq
  have h2 : t • b = a + u • c := by
    have h1 : O + t • b = O + (a + u • c) := by rw [heq, add_assoc]
    exact add_left_cancel h1
  have h0 : ∑ i : Fin 3, ![1, -t, u] i • ![a, b, c] i = 0 := by
    have h3 : (1 : K) • a + (-t) • b + u • c = 0 := by
      rw [one_smul, neg_smul, h2]; abel
    simpa [Fin.sum_univ_three] using h3
  have h4 := Fintype.linearIndependent_iff.mp h ![1, -t, u] h0 0
  simp at h4

/-! ## The plane -/

section Plane

variable {K : Type*} [CommRing K]

/-- Two dimensions meet. -/
@[expose] def Meet (L M : Dim K) : Prop := ∃ t u : K, L.pt t = M.pt u

/-- Two dimensions meet exactly when they have a point in common. -/
theorem meet_iff_common_point (L M : Dim K) :
    Meet L M ↔ ∃ Q, Q ∈ L.points ∧ Q ∈ M.points := by
  constructor
  · rintro ⟨t, u, h⟩
    exact ⟨L.pt t, ⟨t, rfl⟩, ⟨u, h.symm⟩⟩
  · rintro ⟨Q, ⟨t, ht⟩, ⟨u, hu⟩⟩
    exact ⟨t, u, ht.trans hu.symm⟩

end Plane

/-! ## With whole numbers the postulate is false -/

/-- A figure with whole numbers: `a` from `(0, 0)` to `(1, 0)`, `b` towards `(1, 1)`, and `c`
from `(1, 0)` towards `(0, 1)`. -/
@[expose] def wholeFigure : Figure ℤ where
  a := ⟨(0, 0), (1, 0)⟩
  b := ⟨(0, 0), (1, 1)⟩
  c := ⟨(1, 0), (0, 1)⟩
  a0_eq_b0 := rfl
  a1_eq_c0 := rfl

/-- It meets every hypothesis of the postulate. -/
theorem wholeFigure_hypotheses :
    0 < wholeFigure.a.side wholeFigure.b.one ∧ 0 < wholeFigure.a.side wholeFigure.c.one ∧
      0 < cross wholeFigure.b.dir wholeFigure.c.dir := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [wholeFigure, Dim.side, Dim.dir, cross]

/-- **And its two lines never meet.** They cross at `(1/2, 1/2)`, between their points. -/
theorem whole_numbers_never_meet (t u : ℤ) : wholeFigure.b.pt t ≠ wholeFigure.c.pt u := by
  intro h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  simp [wholeFigure, Dim.pt] at h1 h2
  omega

/-! ## With fractions -/

section Fractions

variable {K : Type*} [Field K]

/-! ### The postulate as Playfair states it -/

/-- Two dimensions meet if the cross product of their directions is not zero. -/
theorem meet_of_cross_ne_zero (L M : Dim K) (h : cross L.dir M.dir ≠ 0) : Meet L M := by
  refine ⟨cross (M.zero.1 - L.zero.1, M.zero.2 - L.zero.2) M.dir / cross L.dir M.dir,
    cross (M.zero.1 - L.zero.1, M.zero.2 - L.zero.2) L.dir / cross L.dir M.dir, ?_⟩
  apply Prod.ext
  · simp only [Dim.pt, Dim.dir, cross] at h ⊢
    exact cramer_aux _ _ _ _ _ _ _ h (by ring)
  · simp only [Dim.pt, Dim.dir, cross] at h ⊢
    exact cramer_aux _ _ _ _ _ _ _ h (by ring)

/-- A dimension with the direction of `L`, through a point that is not on `L`, never meets
`L`. -/
theorem not_meet_of_cross_eq_zero (L M : Dim K) (hL : L.zero ≠ L.one)
    (h : cross L.dir M.dir = 0) (hP : M.zero ∉ L.points) : ¬ Meet L M := by
  rintro ⟨t, u, heq⟩
  obtain ⟨l, hl⟩ := exists_mul_of_cross_eq_zero (L.dir_ne_zero hL) h
  apply hP
  refine ⟨t - u * l, ?_⟩
  have e1 := congrArg Prod.fst heq
  have e2 := congrArg Prod.snd heq
  have l1 := congrArg Prod.fst hl
  have l2 := congrArg Prod.snd hl
  simp only [Dim.pt, Dim.dir] at e1 e2 l1 l2
  apply Prod.ext
  · simp only [Dim.pt]
    linear_combination e1 + u * l1
  · simp only [Dim.pt]
    linear_combination e2 + u * l2

/-- **Playfair, first half.** Through a point that is not on `L` there is a line that never
meets `L`. -/
theorem playfair_exists (L : Dim K) (hL : L.zero ≠ L.one) (P : K × K) (hP : P ∉ L.points) :
    ∃ M : Dim K, M.zero = P ∧ M.zero ≠ M.one ∧ ¬ Meet L M := by
  refine ⟨⟨P, (P.1 + (L.one.1 - L.zero.1), P.2 + (L.one.2 - L.zero.2))⟩, rfl, ?_,
    not_meet_of_cross_eq_zero L ⟨P, (P.1 + (L.one.1 - L.zero.1), P.2 + (L.one.2 - L.zero.2))⟩
      hL ?_ hP⟩
  · intro h
    apply hL
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    simp only [] at h1 h2
    apply Prod.ext
    · linear_combination h1
    · linear_combination h2
  · simp only [cross, Dim.dir]
    ring

/-- If the direction of `M` is a multiple of the direction of `M'`, and they leave the same
point, every point of `M` is a point of `M'`. -/
theorem points_subset (M M' : Dim K) (hP : M.zero = M'.zero) (k : K)
    (hk : M.dir = (k * M'.dir.1, k * M'.dir.2)) : M.points ⊆ M'.points := by
  rintro _ ⟨t, rfl⟩
  refine ⟨t * k, ?_⟩
  have k1 := congrArg Prod.fst hk
  have k2 := congrArg Prod.snd hk
  have p1 := congrArg Prod.fst hP
  have p2 := congrArg Prod.snd hP
  simp only [Dim.dir] at k1 k2
  apply Prod.ext
  · simp only [Dim.pt]
    linear_combination -p1 - t * k1
  · simp only [Dim.pt]
    linear_combination -p2 - t * k2

/-- **Playfair, second half.** Two lines through the same point that never meet `L` are the
same line. -/
theorem playfair_unique (L M M' : Dim K) (hL : L.zero ≠ L.one) (hM : M.zero ≠ M.one)
    (hM' : M'.zero ≠ M'.one) (hP : M.zero = M'.zero)
    (h : ¬ Meet L M) (h' : ¬ Meet L M') : M.points = M'.points := by
  have c1 : cross L.dir M.dir = 0 := by
    by_contra hne
    exact h (meet_of_cross_ne_zero L M hne)
  have c2 : cross L.dir M'.dir = 0 := by
    by_contra hne
    exact h' (meet_of_cross_ne_zero L M' hne)
  obtain ⟨l, hl⟩ := exists_mul_of_cross_eq_zero (L.dir_ne_zero hL) c1
  obtain ⟨l', hl'⟩ := exists_mul_of_cross_eq_zero (L.dir_ne_zero hL) c2
  have hl0 : l ≠ 0 := by
    rintro rfl
    apply M.dir_ne_zero hM
    rw [hl]
    simp
  have hl'0 : l' ≠ 0 := by
    rintro rfl
    apply M'.dir_ne_zero hM'
    rw [hl']
    simp
  apply Set.Subset.antisymm
  · apply points_subset M M' hP (l / l')
    rw [hl, hl']
    apply Prod.ext
    · simp only []
      rw [← mul_assoc, div_mul_cancel₀ _ hl'0]
    · simp only []
      rw [← mul_assoc, div_mul_cancel₀ _ hl'0]
  · apply points_subset M' M hP.symm (l' / l)
    rw [hl, hl']
    apply Prod.ext
    · simp only []
      rw [← mul_assoc, div_mul_cancel₀ _ hl0]
    · simp only []
      rw [← mul_assoc, div_mul_cancel₀ _ hl0]

/-- **Playfair, second half, for lines through a point.** Two lines through the point `P` that
never meet `L` are the same line, wherever they have their zeros. -/
theorem playfair_unique_through (L M M' : Dim K) (hL : L.zero ≠ L.one) (hM : M.zero ≠ M.one)
    (hM' : M'.zero ≠ M'.one) {P : K × K} (hP : P ∈ M.points) (hP' : P ∈ M'.points)
    (h : ¬ Meet L M) (h' : ¬ Meet L M') : M.points = M'.points := by
  have hN : (M.rebase P).zero ≠ (M.rebase P).one :=
    (M.rebase P).zero_ne_one_of_dir (by rw [M.rebase_dir]; exact M.dir_ne_zero hM)
  have hN' : (M'.rebase P).zero ≠ (M'.rebase P).one :=
    (M'.rebase P).zero_ne_one_of_dir (by rw [M'.rebase_dir]; exact M'.dir_ne_zero hM')
  have hmeet : ¬ Meet L (M.rebase P) := by
    rw [meet_iff_common_point, M.rebase_points hP, ← meet_iff_common_point]
    exact h
  have hmeet' : ¬ Meet L (M'.rebase P) := by
    rw [meet_iff_common_point, M'.rebase_points hP', ← meet_iff_common_point]
    exact h'
  have hsame := playfair_unique L (M.rebase P) (M'.rebase P) hL hN hN' rfl hmeet hmeet'
  rwa [M.rebase_points hP, M'.rebase_points hP'] at hsame

end Fractions

/-! ## The postulate, in the plane over an ordered field -/

section Ordered

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- **The parallel postulate, in the plane of the three dimensions.**

`a` falls on `b` and `c`. Let `b1` and `c1` lie on the left of `a`, and let the two interior
angles on that side be together less than two right angles: `c` is a turn to the left of `b`.
Then `b` and `c`, produced on that side, meet on that side. For the right of `a` see
`fifth_postulate_right`. -/
theorem fifth_postulate (F : Figure K)
    (hb : 0 < F.a.side F.b.one) (hc : 0 < F.a.side F.c.one)
    (hsum : 0 < cross F.b.dir F.c.dir) :
    ∃ t u : K, 0 < t ∧ 0 < u ∧ F.b.pt t = F.c.pt u ∧ 0 < F.a.side (F.b.pt t) := by
  rw [F.side_b_one] at hb
  rw [F.side_c_one] at hc
  have ht : 0 < cross F.a.dir F.c.dir / cross F.b.dir F.c.dir := div_pos hc hsum
  refine ⟨_, _, ht, div_pos hb hsum, F.meet_eq hsum.ne', ?_⟩
  rw [F.side_b_pt]
  exact mul_pos ht hb

/-- **More than two right angles: the lines meet on the other side.** -/
theorem meet_on_the_other_side (F : Figure K)
    (hb : 0 < F.a.side F.b.one) (hc : 0 < F.a.side F.c.one)
    (hsum : cross F.b.dir F.c.dir < 0) :
    ∃ t u : K, t < 0 ∧ u < 0 ∧ F.b.pt t = F.c.pt u ∧ F.a.side (F.b.pt t) < 0 := by
  rw [F.side_b_one] at hb
  rw [F.side_c_one] at hc
  have ht : cross F.a.dir F.c.dir / cross F.b.dir F.c.dir < 0 := div_neg_of_pos_of_neg hc hsum
  refine ⟨_, _, ht, div_neg_of_pos_of_neg hb hsum, F.meet_eq hsum.ne, ?_⟩
  rw [F.side_b_pt]
  exact mul_neg_of_neg_of_pos ht hb

/-- **Exactly when.** The lines `b` and `c` meet on the side of `b1` and `c1` exactly when `c`
is a turn to the left of `b`. -/
theorem meet_on_side_iff (F : Figure K)
    (hb : 0 < F.a.side F.b.one) (hc : 0 < F.a.side F.c.one) :
    (∃ t u : K, 0 < t ∧ 0 < u ∧ F.b.pt t = F.c.pt u) ↔ 0 < cross F.b.dir F.c.dir := by
  constructor
  · rintro ⟨t, u, ht, -, h⟩
    rcases lt_trichotomy (cross F.b.dir F.c.dir) 0 with hneg | hzero | hpos
    · obtain ⟨t', u', ht', -, h', -⟩ := meet_on_the_other_side F hb hc hneg
      have htt := (F.meet_unique hneg.ne h h').1
      rw [htt] at ht
      exact absurd ht (lt_asymm ht')
    · exact absurd h (F.never_meet_of_two_right_angles hc.ne' hzero t u)
    · exact hpos
  · intro hsum
    obtain ⟨t, u, ht, hu, h, -⟩ := fifth_postulate F hb hc hsum
    exact ⟨t, u, ht, hu, h⟩

/-- **The postulate on the other side of `a`.** If `b1` and `c1` lie on the right of `a`, and
`c` is a turn to the right of `b`, the lines meet on the right of `a`. -/
theorem fifth_postulate_right (F : Figure K)
    (hb : F.a.side F.b.one < 0) (hc : F.a.side F.c.one < 0)
    (hsum : cross F.b.dir F.c.dir < 0) :
    ∃ t u : K, 0 < t ∧ 0 < u ∧ F.b.pt t = F.c.pt u ∧ F.a.side (F.b.pt t) < 0 := by
  rw [F.side_b_one] at hb
  rw [F.side_c_one] at hc
  have ht : 0 < cross F.a.dir F.c.dir / cross F.b.dir F.c.dir := div_pos_of_neg_of_neg hc hsum
  refine ⟨_, _, ht, div_pos_of_neg_of_neg hb hsum, F.meet_eq hsum.ne, ?_⟩
  rw [F.side_b_pt]
  exact mul_neg_of_pos_of_neg ht hb

/-- **More than two right angles, on the right of `a`: the lines meet on the left of `a`.** -/
theorem meet_on_the_other_side_right (F : Figure K)
    (hb : F.a.side F.b.one < 0) (hc : F.a.side F.c.one < 0)
    (hsum : 0 < cross F.b.dir F.c.dir) :
    ∃ t u : K, t < 0 ∧ u < 0 ∧ F.b.pt t = F.c.pt u ∧ 0 < F.a.side (F.b.pt t) := by
  rw [F.side_b_one] at hb
  rw [F.side_c_one] at hc
  have ht : cross F.a.dir F.c.dir / cross F.b.dir F.c.dir < 0 := div_neg_of_neg_of_pos hc hsum
  refine ⟨_, _, ht, div_neg_of_neg_of_pos hb hsum, F.meet_eq hsum.ne', ?_⟩
  rw [F.side_b_pt]
  exact mul_pos_of_neg_of_neg ht hb

/-- **Exactly when, on the other side.** -/
theorem meet_on_side_iff_right (F : Figure K)
    (hb : F.a.side F.b.one < 0) (hc : F.a.side F.c.one < 0) :
    (∃ t u : K, 0 < t ∧ 0 < u ∧ F.b.pt t = F.c.pt u) ↔ cross F.b.dir F.c.dir < 0 := by
  have hb' : 0 < F.reverse.a.side F.reverse.b.one := by
    rw [F.reverse_side]; exact neg_pos.mpr hc
  have hc' : 0 < F.reverse.a.side F.reverse.c.one := by
    rw [F.reverse_side]; exact neg_pos.mpr hb
  have h := meet_on_side_iff F.reverse hb' hc'
  rw [F.reverse_cross, neg_pos] at h
  rw [← h]
  constructor
  · rintro ⟨t, u, ht, hu, e⟩
    exact ⟨u, t, hu, ht, e.symm⟩
  · rintro ⟨t, u, ht, hu, e⟩
    exact ⟨u, t, hu, ht, e.symm⟩

end Ordered

/-- The figure of `wholeFigure`, with fractions in the dimensions. -/
@[expose] def exampleFigure : Figure ℚ where
  a := ⟨(0, 0), (1, 0)⟩
  b := ⟨(0, 0), (1, 1)⟩
  c := ⟨(1, 0), (0, 1)⟩
  a0_eq_b0 := rfl
  a1_eq_c0 := rfl

/-- It meets every hypothesis of the postulate, and its two lines meet at `(1/2, 1/2)`. -/
theorem exampleFigure_meets :
    0 < exampleFigure.a.side exampleFigure.b.one ∧
      0 < exampleFigure.a.side exampleFigure.c.one ∧
      0 < cross exampleFigure.b.dir exampleFigure.c.dir ∧
      exampleFigure.b.pt (1 / 2) = (1 / 2, 1 / 2) ∧
      exampleFigure.c.pt (1 / 2) = (1 / 2, 1 / 2) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [exampleFigure, Dim.side, Dim.dir, Dim.pt, cross]

/-! ## The figure with given angles -/

section Angles

open Real

/-- The figure with `a` from `(0, 0)` to `(1, 0)`. The line `b` leaves `a0` at the angle `β` to
`a`. The line `c` leaves `a1` at the angle `γ` to `a` run backwards. So `β` and `γ` are the two
interior angles on the upper side of `a`. -/
@[expose] noncomputable def angleFigure (β γ : ℝ) : Figure ℝ where
  a := ⟨(0, 0), (1, 0)⟩
  b := ⟨(0, 0), (cos β, sin β)⟩
  c := ⟨(1, 0), (1 - cos γ, sin γ)⟩
  a0_eq_b0 := rfl
  a1_eq_c0 := rfl

theorem angleFigure_side_b (β γ : ℝ) :
    (angleFigure β γ).a.side (angleFigure β γ).b.one = sin β := by
  simp [angleFigure, Dim.side, Dim.dir, cross]

theorem angleFigure_side_c (β γ : ℝ) :
    (angleFigure β γ).a.side (angleFigure β γ).c.one = sin γ := by
  simp [angleFigure, Dim.side, Dim.dir, cross]

theorem angleFigure_cross (β γ : ℝ) :
    cross (angleFigure β γ).b.dir (angleFigure β γ).c.dir = sin (β + γ) := by
  simp only [angleFigure, Dim.dir, cross, sin_add]
  ring

/-- **Euclid's fifth postulate, for the figure with the angles `β` and `γ`.** If the two
interior angles on the upper side of `a` are together less than two right angles, the lines `b`
and `c`, produced on that side, meet on that side. -/
theorem euclid_fifth (β γ : ℝ) (hβ : 0 < β) (hγ : 0 < γ) (h : β + γ < π) :
    ∃ t u : ℝ, 0 < t ∧ 0 < u ∧
      (angleFigure β γ).b.pt t = (angleFigure β γ).c.pt u ∧
      0 < (angleFigure β γ).a.side ((angleFigure β γ).b.pt t) := by
  apply fifth_postulate
  · rw [angleFigure_side_b]
    exact sin_pos_of_pos_of_lt_pi hβ (by linarith)
  · rw [angleFigure_side_c]
    exact sin_pos_of_pos_of_lt_pi hγ (by linarith)
  · rw [angleFigure_cross]
    exact sin_pos_of_pos_of_lt_pi (by linarith) h

/-- **Where they meet: the law of sines.** The point is at the number `sin γ / sin (β + γ)` of
`b`, and at the number `sin β / sin (β + γ)` of `c`. -/
theorem law_of_sines (β γ : ℝ) (h : sin (β + γ) ≠ 0) :
    (angleFigure β γ).b.pt (sin γ / sin (β + γ))
      = (angleFigure β γ).c.pt (sin β / sin (β + γ)) := by
  have hc : cross (angleFigure β γ).a.dir (angleFigure β γ).c.dir = sin γ := by
    rw [← Figure.side_c_one, angleFigure_side_c]
  have hb : cross (angleFigure β γ).a.dir (angleFigure β γ).b.dir = sin β := by
    rw [← Figure.side_b_one, angleFigure_side_b]
  have hne : cross (angleFigure β γ).b.dir (angleFigure β γ).c.dir ≠ 0 := by
    rw [angleFigure_cross]; exact h
  have hmeet := (angleFigure β γ).meet_eq hne
  rw [hc, hb, angleFigure_cross] at hmeet
  exact hmeet

/-- **Two right angles: the lines never meet.** -/
theorem never_meet_of_sum_eq_pi (β γ : ℝ) (hγ : 0 < γ) (hγ' : γ < π) (h : β + γ = π)
    (t u : ℝ) : (angleFigure β γ).b.pt t ≠ (angleFigure β γ).c.pt u := by
  apply Figure.never_meet_of_two_right_angles
  · rw [angleFigure_side_c]
    exact (sin_pos_of_pos_of_lt_pi hγ hγ').ne'
  · rw [angleFigure_cross, h, sin_pi]

end Angles

/-! ## The angles are angles in Mathlib's sense -/

section MathlibAngles

open Real InnerProductGeometry

/-- A direction of the plane of the three dimensions, as a vector of Mathlib's Euclidean
plane. -/
@[expose] noncomputable def toE (p : ℝ × ℝ) : EuclideanSpace ℝ (Fin 2) := !₂[p.1, p.2]

theorem inner_toE (p q : ℝ × ℝ) : inner ℝ (toE p) (toE q) = p.1 * q.1 + p.2 * q.2 := by
  simp [toE, PiLp.inner_apply, Fin.sum_univ_two]
  ring

theorem norm_toE (p : ℝ × ℝ) : ‖toE p‖ = √(p.1 ^ 2 + p.2 ^ 2) := by
  simp [toE, EuclideanSpace.norm_eq, Fin.sum_univ_two]

theorem norm_toE_sq (p : ℝ × ℝ) : ‖toE p‖ ^ 2 = p.1 ^ 2 + p.2 ^ 2 := by
  rw [norm_toE, sq_sqrt (by positivity)]

theorem norm_toE_neg (p : ℝ × ℝ) : ‖toE (-p)‖ = ‖toE p‖ := by
  rw [norm_toE, norm_toE]
  simp

/-- The interior angle at `a0`, between `a` and `b`, is `β`. -/
theorem angle_at_a0 (β γ : ℝ) (h0 : 0 ≤ β) (hπ : β ≤ π) :
    angle (toE (angleFigure β γ).a.dir) (toE (angleFigure β γ).b.dir) = β := by
  rw [angle, inner_toE, norm_toE, norm_toE]
  simp [angleFigure, Dim.dir, arccos_cos h0 hπ]

/-- The interior angle at `a1`, between `a` run backwards and `c`, is `γ`. -/
theorem angle_at_a1 (β γ : ℝ) (h0 : 0 ≤ γ) (hπ : γ ≤ π) :
    angle (toE (-(angleFigure β γ).a.dir)) (toE (angleFigure β γ).c.dir) = γ := by
  rw [angle, inner_toE, norm_toE, norm_toE]
  simp [angleFigure, Dim.dir, arccos_cos h0 hπ]

/-! ### Any figure in the real plane -/

theorem cos_angle_toE (p q : ℝ × ℝ) :
    cos (angle (toE p) (toE q)) * (‖toE p‖ * ‖toE q‖) = p.1 * q.1 + p.2 * q.2 := by
  rw [cos_angle_mul_norm_mul_norm, inner_toE]

theorem sin_angle_toE (p q : ℝ × ℝ) :
    sin (angle (toE p) (toE q)) * (‖toE p‖ * ‖toE q‖) = |cross p q| := by
  rw [sin_angle_mul_norm_mul_norm, inner_toE, inner_toE, inner_toE, ← sqrt_sq_eq_abs]
  congr 1
  simp only [cross]
  ring

theorem normSq_pos_left {p q : ℝ × ℝ} (h : cross p q ≠ 0) : 0 < p.1 ^ 2 + p.2 ^ 2 := by
  by_contra hn
  push Not at hn
  have h1 : p.1 ^ 2 = 0 := by linarith [sq_nonneg p.1, sq_nonneg p.2]
  have h2 : p.2 ^ 2 = 0 := by linarith [sq_nonneg p.1, sq_nonneg p.2]
  have h3 : p.1 = 0 := (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp h1
  have h4 : p.2 = 0 := (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp h2
  apply h
  simp [cross, h3, h4]

theorem normSq_pos_right {p q : ℝ × ℝ} (h : cross p q ≠ 0) : 0 < q.1 ^ 2 + q.2 ^ 2 := by
  by_contra hn
  push Not at hn
  have h1 : q.1 ^ 2 = 0 := by linarith [sq_nonneg q.1, sq_nonneg q.2]
  have h2 : q.2 ^ 2 = 0 := by linarith [sq_nonneg q.1, sq_nonneg q.2]
  have h3 : q.1 = 0 := (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp h1
  have h4 : q.2 = 0 := (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp h2
  apply h
  simp [cross, h3, h4]

theorem norm_toE_pos_left {p q : ℝ × ℝ} (h : cross p q ≠ 0) : 0 < ‖toE p‖ := by
  rw [norm_toE]
  exact sqrt_pos.mpr (normSq_pos_left h)

theorem norm_toE_pos_right {p q : ℝ × ℝ} (h : cross p q ≠ 0) : 0 < ‖toE q‖ := by
  rw [norm_toE]
  exact sqrt_pos.mpr (normSq_pos_right h)

/-- Two directions whose cross product is not zero make an angle that is more than nothing
and less than two right angles. -/
theorem angle_pos_and_lt_pi {p q : ℝ × ℝ} (h : cross p q ≠ 0) :
    0 < angle (toE p) (toE q) ∧ angle (toE p) (toE q) < π := by
  have hN : 0 < ‖toE p‖ * ‖toE q‖ := mul_pos (norm_toE_pos_left h) (norm_toE_pos_right h)
  have hs := sin_angle_toE p q
  have habs : 0 < |cross p q| := abs_pos.mpr h
  have hsin : 0 < sin (angle (toE p) (toE q)) := by
    by_contra hn
    push Not at hn
    have h5 := mul_nonpos_of_nonpos_of_nonneg hn hN.le
    linarith
  constructor
  · rcases (angle_nonneg (toE p) (toE q)).eq_or_lt with h0 | h0
    · rw [← h0, sin_zero] at hsin
      exact absurd hsin (lt_irrefl 0)
    · exact h0
  · rcases (angle_le_pi (toE p) (toE q)).eq_or_lt with h0 | h0
    · rw [h0, sin_pi] at hsin
      exact absurd hsin (lt_irrefl 0)
    · exact h0

/-- **The sine of the two interior angles together.** `a` is the direction of the line that
falls on the two others, and `b` and `c` are the directions of the two others, both to the left
of `a`. With `β` the angle from `a` to `b`, and `γ` the angle from `a` run backwards to `c`:

    sin (β + γ) · |b| · |c| = cross b c . -/
theorem sin_angle_sum (a b c : ℝ × ℝ) (hab : 0 < cross a b) (hac : 0 < cross a c) :
    sin (angle (toE a) (toE b) + angle (toE (-a)) (toE c)) * (‖toE b‖ * ‖toE c‖)
      = cross b c := by
  have hA : 0 < ‖toE a‖ := norm_toE_pos_left hab.ne'
  have hA2 := norm_toE_sq a
  have hsβ := sin_angle_toE a b
  have hcβ := cos_angle_toE a b
  have hsγ := sin_angle_toE (-a) c
  have hcγ := cos_angle_toE (-a) c
  have hac' : cross (-a) c = -cross a c := by
    simp only [cross, Prod.fst_neg, Prod.snd_neg]; ring
  rw [abs_of_pos hab] at hsβ
  rw [hac', abs_neg, abs_of_pos hac, norm_toE_neg] at hsγ
  rw [norm_toE_neg] at hcγ
  simp only [Prod.fst_neg, Prod.snd_neg] at hcγ
  simp only [cross] at hsβ hsγ ⊢
  generalize angle (toE a) (toE b) = β at *
  generalize angle (toE (-a)) (toE c) = γ at *
  generalize ‖toE a‖ = A at *
  generalize ‖toE b‖ = B at *
  generalize ‖toE c‖ = C at *
  have hA2' : A ^ 2 ≠ 0 := by positivity
  apply mul_left_cancel₀ hA2'
  rw [sin_add]
  linear_combination (cos γ * (A * C)) * hsβ + (a.1 * b.2 - a.2 * b.1) * hcγ
    + (sin γ * (A * C)) * hcβ + (a.1 * b.1 + a.2 * b.2) * hsγ
    - (b.1 * c.2 - b.2 * c.1) * hA2

/-- What the two interior angles of a figure say, gathered. -/
theorem _root_.ParallelPostulate.Pairs.Figure.angle_facts (F : Figure ℝ)
    (hb : 0 < F.a.side F.b.one) (hc : 0 < F.a.side F.c.one) :
    sin (angle (toE F.a.dir) (toE F.b.dir) + angle (toE (-F.a.dir)) (toE F.c.dir))
        * (‖toE F.b.dir‖ * ‖toE F.c.dir‖) = cross F.b.dir F.c.dir ∧
      0 < ‖toE F.b.dir‖ * ‖toE F.c.dir‖ ∧
      0 < angle (toE F.a.dir) (toE F.b.dir) ∧ angle (toE F.a.dir) (toE F.b.dir) < π ∧
      0 < angle (toE (-F.a.dir)) (toE F.c.dir) ∧ angle (toE (-F.a.dir)) (toE F.c.dir) < π := by
  rw [F.side_b_one] at hb
  rw [F.side_c_one] at hc
  have hc' : cross (-F.a.dir) F.c.dir ≠ 0 := by
    have hneg : cross (-F.a.dir) F.c.dir = -cross F.a.dir F.c.dir := by
      simp only [cross, Prod.fst_neg, Prod.snd_neg]; ring
    rw [hneg]
    exact neg_ne_zero.mpr hc.ne'
  obtain ⟨hβ0, hβπ⟩ := angle_pos_and_lt_pi hb.ne'
  obtain ⟨hγ0, hγπ⟩ := angle_pos_and_lt_pi hc'
  exact ⟨sin_angle_sum _ _ _ hb hc,
    mul_pos (norm_toE_pos_right hb.ne') (norm_toE_pos_right hc.ne'), hβ0, hβπ, hγ0, hγπ⟩

/-- Less than two right angles: `c` is a turn to the left of `b`. -/
theorem cross_pos_of_angles (F : Figure ℝ)
    (hb : 0 < F.a.side F.b.one) (hc : 0 < F.a.side F.c.one)
    (hang : angle (toE F.a.dir) (toE F.b.dir) + angle (toE (-F.a.dir)) (toE F.c.dir) < π) :
    0 < cross F.b.dir F.c.dir := by
  obtain ⟨hsin, hN, hβ0, -, hγ0, -⟩ := F.angle_facts hb hc
  rw [← hsin]
  exact mul_pos (sin_pos_of_pos_of_lt_pi (by linarith) hang) hN

/-- Two right angles: the cross product of the directions of `b` and `c` is zero. -/
theorem cross_eq_zero_of_angles (F : Figure ℝ)
    (hb : 0 < F.a.side F.b.one) (hc : 0 < F.a.side F.c.one)
    (hang : angle (toE F.a.dir) (toE F.b.dir) + angle (toE (-F.a.dir)) (toE F.c.dir) = π) :
    cross F.b.dir F.c.dir = 0 := by
  obtain ⟨hsin, -, -, -, -, -⟩ := F.angle_facts hb hc
  rw [← hsin, hang, sin_pi, zero_mul]

/-- More than two right angles: `c` is a turn to the right of `b`. -/
theorem cross_neg_of_angles (F : Figure ℝ)
    (hb : 0 < F.a.side F.b.one) (hc : 0 < F.a.side F.c.one)
    (hang : π < angle (toE F.a.dir) (toE F.b.dir) + angle (toE (-F.a.dir)) (toE F.c.dir)) :
    cross F.b.dir F.c.dir < 0 := by
  obtain ⟨hsin, hN, -, hβπ, -, hγπ⟩ := F.angle_facts hb hc
  rw [← hsin]
  have hneg : sin (angle (toE F.a.dir) (toE F.b.dir)
      + angle (toE (-F.a.dir)) (toE F.c.dir)) < 0 := by
    rw [← sin_sub_two_pi]
    exact sin_neg_of_neg_of_neg_pi_lt (by linarith) (by linarith)
  exact mul_neg_of_neg_of_pos hneg hN

/-- **Euclid's fifth postulate, on the left of `a`, for any figure in the real plane.** The
angles are angles in Mathlib's sense. If `b1` and `c1` lie on the left of `a`, and the two
interior angles on that side are together less than two right angles, then `b` and `c` meet on
that side. For either side see `euclid_fifth_either_side`. -/
theorem euclid_fifth_general (F : Figure ℝ)
    (hb : 0 < F.a.side F.b.one) (hc : 0 < F.a.side F.c.one)
    (hang : angle (toE F.a.dir) (toE F.b.dir) + angle (toE (-F.a.dir)) (toE F.c.dir) < π) :
    ∃ t u : ℝ, 0 < t ∧ 0 < u ∧ F.b.pt t = F.c.pt u ∧ 0 < F.a.side (F.b.pt t) :=
  fifth_postulate F hb hc (cross_pos_of_angles F hb hc hang)

/-- **Two right angles, with `b1` and `c1` on the left of `a`, for any figure in the real
plane: the lines never meet.** For either side see `never_meet_either_side`. -/
theorem never_meet_general (F : Figure ℝ)
    (hb : 0 < F.a.side F.b.one) (hc : 0 < F.a.side F.c.one)
    (hang : angle (toE F.a.dir) (toE F.b.dir) + angle (toE (-F.a.dir)) (toE F.c.dir) = π)
    (t u : ℝ) : F.b.pt t ≠ F.c.pt u :=
  F.never_meet_of_two_right_angles hc.ne' (cross_eq_zero_of_angles F hb hc hang) t u

/-- **More than two right angles, with `b1` and `c1` on the left of `a`, for any figure in the
real plane: the lines meet on the right of `a`.** For either side see
`other_side_either_side`. -/
theorem other_side_general (F : Figure ℝ)
    (hb : 0 < F.a.side F.b.one) (hc : 0 < F.a.side F.c.one)
    (hang : π < angle (toE F.a.dir) (toE F.b.dir) + angle (toE (-F.a.dir)) (toE F.c.dir)) :
    ∃ t u : ℝ, t < 0 ∧ u < 0 ∧ F.b.pt t = F.c.pt u ∧ F.a.side (F.b.pt t) < 0 :=
  meet_on_the_other_side F hb hc (cross_neg_of_angles F hb hc hang)

/-- **The postulate and its converse.** In the real plane, the lines `b` and `c` meet on the
side of `b1` and `c1` exactly when the two interior angles on that side are together less than
two right angles. -/
theorem meet_on_side_iff_angles (F : Figure ℝ)
    (hb : 0 < F.a.side F.b.one) (hc : 0 < F.a.side F.c.one) :
    (∃ t u : ℝ, 0 < t ∧ 0 < u ∧ F.b.pt t = F.c.pt u) ↔
      angle (toE F.a.dir) (toE F.b.dir) + angle (toE (-F.a.dir)) (toE F.c.dir) < π := by
  rw [meet_on_side_iff F hb hc]
  constructor
  · intro hpos
    rcases lt_trichotomy
        (angle (toE F.a.dir) (toE F.b.dir) + angle (toE (-F.a.dir)) (toE F.c.dir)) π
      with h | h | h
    · exact h
    · have h0 := cross_eq_zero_of_angles F hb hc h
      rw [h0] at hpos
      exact absurd hpos (lt_irrefl 0)
    · exact absurd hpos (lt_asymm (cross_neg_of_angles F hb hc h))
  · exact cross_pos_of_angles F hb hc

/-! ### Either side of `a` -/

/-- The two interior angles of the figure with `a` run backwards are the two interior angles
of the figure, in the other order. -/
theorem _root_.ParallelPostulate.Pairs.Figure.reverse_angles (F : Figure ℝ) :
    angle (toE F.reverse.a.dir) (toE F.reverse.b.dir)
        + angle (toE (-F.reverse.a.dir)) (toE F.reverse.c.dir)
      = angle (toE F.a.dir) (toE F.b.dir) + angle (toE (-F.a.dir)) (toE F.c.dir) := by
  rw [F.reverse_dir, neg_neg]
  change angle (toE (-F.a.dir)) (toE F.c.dir) + angle (toE F.a.dir) (toE F.b.dir)
    = angle (toE F.a.dir) (toE F.b.dir) + angle (toE (-F.a.dir)) (toE F.c.dir)
  ring

/-- **Euclid's fifth postulate on the right of `a`.** -/
theorem euclid_fifth_right (F : Figure ℝ)
    (hb : F.a.side F.b.one < 0) (hc : F.a.side F.c.one < 0)
    (hang : angle (toE F.a.dir) (toE F.b.dir) + angle (toE (-F.a.dir)) (toE F.c.dir) < π) :
    ∃ t u : ℝ, 0 < t ∧ 0 < u ∧ F.b.pt t = F.c.pt u ∧ F.a.side (F.b.pt t) < 0 := by
  have hb' : 0 < F.reverse.a.side F.reverse.b.one := by
    rw [F.reverse_side]; exact neg_pos.mpr hc
  have hc' : 0 < F.reverse.a.side F.reverse.c.one := by
    rw [F.reverse_side]; exact neg_pos.mpr hb
  have hang' := hang
  rw [← F.reverse_angles] at hang'
  obtain ⟨t, u, ht, hu, e, hs⟩ := euclid_fifth_general F.reverse hb' hc' hang'
  have e' : F.b.pt u = F.c.pt t := e.symm
  refine ⟨u, t, hu, ht, e', ?_⟩
  rw [F.reverse_side] at hs
  rw [e']
  exact neg_pos.mp hs

/-- **Euclid's fifth postulate, in the real plane, on either side.** If `b1` and `c1` lie on
the same side of `a`, and the two interior angles on that side are together less than two right
angles, then `b` and `c` meet on that side. -/
theorem euclid_fifth_either_side (F : Figure ℝ)
    (hside : 0 < F.a.side F.b.one * F.a.side F.c.one)
    (hang : angle (toE F.a.dir) (toE F.b.dir) + angle (toE (-F.a.dir)) (toE F.c.dir) < π) :
    ∃ t u : ℝ, 0 < t ∧ 0 < u ∧ F.b.pt t = F.c.pt u ∧
      0 < F.a.side (F.b.pt t) * F.a.side F.b.one := by
  rcases mul_pos_iff.mp hside with ⟨hb, hc⟩ | ⟨hb, hc⟩
  · obtain ⟨t, u, ht, hu, e, hs⟩ := euclid_fifth_general F hb hc hang
    exact ⟨t, u, ht, hu, e, mul_pos hs hb⟩
  · obtain ⟨t, u, ht, hu, e, hs⟩ := euclid_fifth_right F hb hc hang
    exact ⟨t, u, ht, hu, e, mul_pos_of_neg_of_neg hs hb⟩

/-- **Two right angles, on either side: the lines never meet.** -/
theorem never_meet_either_side (F : Figure ℝ)
    (hside : 0 < F.a.side F.b.one * F.a.side F.c.one)
    (hang : angle (toE F.a.dir) (toE F.b.dir) + angle (toE (-F.a.dir)) (toE F.c.dir) = π)
    (t u : ℝ) : F.b.pt t ≠ F.c.pt u := by
  rcases mul_pos_iff.mp hside with ⟨hb, hc⟩ | ⟨hb, hc⟩
  · exact never_meet_general F hb hc hang t u
  · have hb' : 0 < F.reverse.a.side F.reverse.b.one := by
      rw [F.reverse_side]; exact neg_pos.mpr hc
    have hc' : 0 < F.reverse.a.side F.reverse.c.one := by
      rw [F.reverse_side]; exact neg_pos.mpr hb
    have hang' := hang
    rw [← F.reverse_angles] at hang'
    intro e
    exact never_meet_general F.reverse hb' hc' hang' u t e.symm

/-- **More than two right angles, on either side: the lines meet on the other side.** -/
theorem other_side_either_side (F : Figure ℝ)
    (hside : 0 < F.a.side F.b.one * F.a.side F.c.one)
    (hang : π < angle (toE F.a.dir) (toE F.b.dir) + angle (toE (-F.a.dir)) (toE F.c.dir)) :
    ∃ t u : ℝ, t < 0 ∧ u < 0 ∧ F.b.pt t = F.c.pt u ∧
      F.a.side (F.b.pt t) * F.a.side F.b.one < 0 := by
  rcases mul_pos_iff.mp hside with ⟨hb, hc⟩ | ⟨hb, hc⟩
  · obtain ⟨t, u, ht, hu, e, hs⟩ := other_side_general F hb hc hang
    exact ⟨t, u, ht, hu, e, mul_neg_of_neg_of_pos hs hb⟩
  · have hb' : 0 < F.reverse.a.side F.reverse.b.one := by
      rw [F.reverse_side]; exact neg_pos.mpr hc
    have hc' : 0 < F.reverse.a.side F.reverse.c.one := by
      rw [F.reverse_side]; exact neg_pos.mpr hb
    have hang' := hang
    rw [← F.reverse_angles] at hang'
    obtain ⟨t, u, ht, hu, e, hs⟩ := other_side_general F.reverse hb' hc' hang'
    have e' : F.b.pt u = F.c.pt t := e.symm
    refine ⟨u, t, hu, ht, e', ?_⟩
    rw [F.reverse_side] at hs
    rw [e']
    exact mul_neg_of_pos_of_neg (neg_lt_zero.mp hs) hb

/-- **The postulate and its converse, on either side.** In the real plane, let `b1` and `c1`
lie on the same side of `a`. The lines `b` and `c`, produced towards `b1` and `c1`, meet exactly
when the two interior angles on that side are together less than two right angles. -/
theorem meet_iff_angles_either_side (F : Figure ℝ)
    (hside : 0 < F.a.side F.b.one * F.a.side F.c.one) :
    (∃ t u : ℝ, 0 < t ∧ 0 < u ∧ F.b.pt t = F.c.pt u) ↔
      angle (toE F.a.dir) (toE F.b.dir) + angle (toE (-F.a.dir)) (toE F.c.dir) < π := by
  rcases mul_pos_iff.mp hside with ⟨hb, hc⟩ | ⟨hb, hc⟩
  · exact meet_on_side_iff_angles F hb hc
  · have hb' : 0 < F.reverse.a.side F.reverse.b.one := by
      rw [F.reverse_side]; exact neg_pos.mpr hc
    have hc' : 0 < F.reverse.a.side F.reverse.c.one := by
      rw [F.reverse_side]; exact neg_pos.mpr hb
    have h := meet_on_side_iff_angles F.reverse hb' hc'
    rw [F.reverse_angles] at h
    rw [← h]
    constructor
    · rintro ⟨t, u, ht, hu, e⟩
      exact ⟨u, t, hu, ht, e.symm⟩
    · rintro ⟨t, u, ht, hu, e⟩
      exact ⟨u, t, hu, ht, e.symm⟩

end MathlibAngles

end ThreeDimensions

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
the three-dimensions section:** through a point outside a line there is exactly one line
that does not meet it. -/
theorem euclid_one_parallel {κ : K} (hκ : 0 ≤ κ) {S : Set (K × K)} (hS : IsLine (plane κ) S)
    {P : K × K} (hPS : P ∉ S) : ∃! M, IsLine (plane κ) M ∧ P ∈ M ∧ M ∩ S = ∅ := by
  obtain ⟨L, hL, rfl, -⟩ := hS
  have hP : P ∈ plane κ := by
    rw [plane_eq_univ hκ]
    trivial
  have hPL : P ∉ L.points := fun h => hPS ⟨h, hP⟩
  exact one_parallel_of_all_within (plane κ) L hL hP hPL
    (fun t => by rw [plane_eq_univ hκ]; trivial)

/-- **Theorem E4 holds in the plane of a bound that is not negative.** In a
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

/-!
# Steps and motions

What becomes of adding under a bound: the step `step κ t u = (t + u) / (1 - κ t u)`, the motion
along the first axis `shift`, turning `rot`, and `apart`, a number that both motions keep.

## Contents

* Proposition H8, steps: `step`, `step_zero_bound`, `step_comm`, `step_zero_right`, `step_neg`,
  `within_zero`, `within_neg`, `step_den_pos`, `step_within`, `step_assoc`, `step_bound`,
  `step_edge`, `step_edge_self`
* Theorem H9, the motion along the first axis: `shift`, `shift_zero_bound`, `shift_centre`,
  `shift_axis`, `shift_den_pos`, `shift_bound`, `shift_mem_plane`, `shift_shift_neg`,
  `shift_neg_shift`, `shift_bijOn`, `shift_cross`, `shift_isLine`, `shift_keeps_left`,
  `shift_apart`, `shift_apart_plane`
* Theorem H9, turning: `rot`, `rot_rot_neg`, `rot_bound`, `rot_mem_plane`, `rot_bijOn`, `rot_pt`,
  `rot_isLine`, `rot_cross`, `rot_apart`
* Theorem H9, how far apart: `apart`, `apart_zero_bound`, `apart_self`, `apart_comm`,
  `apart_centre`, `apart_pos`
* the algebra of the motions, with the divisions taken out: `cross_aux`, `apart_aux`, `apart_aux'`
-/

namespace ParallelPostulate

namespace HyperbolicPlane

open Pairs

/-! ## What becomes of adding: steps and motions -/

section StepsAlgebra

variable {K : Type*} [Field K]

/-- **The step.** Under the bound `κ`, the number `t` and then the number `u`, along a
dimension through `(0, 0)`. -/
@[expose] def step (κ t u : K) : K := (t + u) / (1 - κ * t * u)

/-- With the bound 0 a step is a sum. -/
theorem step_zero_bound (t u : K) : step 0 t u = t + u := by
  simp [step]

theorem step_comm (κ t u : K) : step κ t u = step κ u t := by
  simp only [step]
  rw [add_comm t u, mul_assoc κ t u, mul_comm t u, ← mul_assoc]

theorem step_zero_right (κ t : K) : step κ t 0 = t := by
  simp [step]

theorem step_neg (κ t : K) : step κ t (-t) = 0 := by
  simp [step]

/-- The bound at a step. -/
theorem step_bound {κ t u : K} (h : 1 - κ * t * u ≠ 0) :
    1 + κ * step κ t u ^ 2 = (1 + κ * t ^ 2) * (1 + κ * u ^ 2) / (1 - κ * t * u) ^ 2 := by
  have hX : step κ t u * (1 - κ * t * u) = t + u := div_mul_cancel₀ _ h
  rw [eq_div_iff (pow_ne_zero 2 h)]
  linear_combination κ * (step κ t u * (1 - κ * t * u) + (t + u)) * hX

/-- **A number on the edge swallows every step.** -/
theorem step_edge {κ e t : K} (he : 1 + κ * e ^ 2 = 0) (h : 1 - κ * e * t ≠ 0) :
    step κ e t = e := by
  simp only [step]
  rw [div_eq_iff h]
  linear_combination t * he

/-- **The motion along the first axis** that takes `(0, 0)` to the number `a` of that axis.
Here `w` is a number with `w² = 1 + κ a²`. -/
@[expose] def shift (κ a w : K) (p : K × K) : K × K :=
  ((p.1 + a) / (1 - κ * a * p.1), w * p.2 / (1 - κ * a * p.1))

/-- With the bound 0 the motion is adding. -/
theorem shift_zero_bound (a : K) (p : K × K) : shift 0 a 1 p = (p.1 + a, p.2) := by
  simp [shift]

theorem shift_centre (κ a w : K) : shift κ a w (0, 0) = (a, 0) := by
  simp [shift]

/-- On the first axis the motion is the step. -/
theorem shift_axis (κ a w t : K) : shift κ a w (t, 0) = (step κ t a, 0) := by
  simp only [shift, step, mul_zero, zero_div]
  rw [mul_assoc κ a t, mul_comm a t, ← mul_assoc]

/-- The bound at the pair to which a pair is moved. -/
theorem shift_bound {κ a w : K} (hw : w ^ 2 = 1 + κ * a ^ 2) {p : K × K}
    (hD : 1 - κ * a * p.1 ≠ 0) :
    1 + κ * ((shift κ a w p).1 ^ 2 + (shift κ a w p).2 ^ 2)
      = w ^ 2 * (1 + κ * (p.1 ^ 2 + p.2 ^ 2)) / (1 - κ * a * p.1) ^ 2 := by
  have hX : (p.1 + a) / (1 - κ * a * p.1) * (1 - κ * a * p.1) = p.1 + a :=
    div_mul_cancel₀ _ hD
  have hY : w * p.2 / (1 - κ * a * p.1) * (1 - κ * a * p.1) = w * p.2 :=
    div_mul_cancel₀ _ hD
  rw [eq_div_iff (pow_ne_zero 2 hD)]
  simp only [shift]
  linear_combination
    κ * ((p.1 + a) / (1 - κ * a * p.1) * (1 - κ * a * p.1) + (p.1 + a)) * hX
    + κ * (w * p.2 / (1 - κ * a * p.1) * (1 - κ * a * p.1) + w * p.2) * hY
    - (1 + κ * p.1 ^ 2) * hw

/-- The motion back. -/
theorem shift_shift_neg {κ a w : K} (hw : w ^ 2 = 1 + κ * a ^ 2) (hw0 : w ≠ 0) {p : K × K}
    (hD : 1 - κ * a * p.1 ≠ 0) : shift κ (-a) w (shift κ a w p) = p := by
  have hX : (p.1 + a) / (1 - κ * a * p.1) * (1 - κ * a * p.1) = p.1 + a :=
    div_mul_cancel₀ _ hD
  have hY : w * p.2 / (1 - κ * a * p.1) * (1 - κ * a * p.1) = w * p.2 :=
    div_mul_cancel₀ _ hD
  have hw2 : w ^ 2 ≠ 0 := pow_ne_zero 2 hw0
  have hDD : (1 - κ * -a * ((p.1 + a) / (1 - κ * a * p.1))) * (1 - κ * a * p.1) = w ^ 2 := by
    linear_combination κ * a * hX - hw
  have hD' : 1 - κ * -a * ((p.1 + a) / (1 - κ * a * p.1)) ≠ 0 := by
    intro h
    rw [h, zero_mul] at hDD
    exact hw2 hDD.symm
  apply Prod.ext
  · simp only [shift]
    rw [div_eq_iff hD']
    apply mul_right_cancel₀ hD
    linear_combination hX - p.1 * hDD - p.1 * hw
  · simp only [shift]
    rw [div_eq_iff hD']
    apply mul_right_cancel₀ hD
    linear_combination w * hY - p.2 * hDD

/-- The algebra of the next theorem, with the divisions taken out. -/
theorem cross_aux (κ a w xA yA xB yB xC yC XA YA XB YB XC YC : K)
    (hXA : XA * (1 - κ * a * xA) = xA + a) (hYA : YA * (1 - κ * a * xA) = w * yA)
    (hXB : XB * (1 - κ * a * xB) = xB + a) (hYB : YB * (1 - κ * a * xB) = w * yB)
    (hXC : XC * (1 - κ * a * xC) = xC + a) (hYC : YC * (1 - κ * a * xC) = w * yC) :
    ((XB - XA) * (YC - YA) - (YB - YA) * (XC - XA))
        * ((1 - κ * a * xA) * (1 - κ * a * xB) * (1 - κ * a * xC))
      = w * (1 + κ * a ^ 2) * ((xB - xA) * (yC - yA) - (yB - yA) * (xC - xA)) := by
  linear_combination
    ((1 - κ * a * xA) * (YC * (1 - κ * a * xC))
      - (1 - κ * a * xC) * (YA * (1 - κ * a * xA))) * hXB
    + (-(1 - κ * a * xB) * (YC * (1 - κ * a * xC))
      + (1 - κ * a * xC) * (YB * (1 - κ * a * xB))) * hXA
    + (-(1 - κ * a * xA) * (YB * (1 - κ * a * xB))
      + (1 - κ * a * xB) * (YA * (1 - κ * a * xA))) * hXC
    + ((1 - κ * a * xA) * (xB + a) - (1 - κ * a * xB) * (xA + a)) * hYC
    + (-(1 - κ * a * xC) * (xB + a) + (1 - κ * a * xB) * (xC + a)) * hYA
    + (-(1 - κ * a * xA) * (xC + a) + (1 - κ * a * xC) * (xA + a)) * hYB

/-- **A motion keeps three pairs of a dimension on a dimension.** If `w (1 + κ a²)` is not
zero, it keeps three pairs that are not on one dimension off it as well. -/
theorem shift_cross (κ a w : K) {A B C : K × K} (hA : 1 - κ * a * A.1 ≠ 0)
    (hB : 1 - κ * a * B.1 ≠ 0) (hC : 1 - κ * a * C.1 ≠ 0) :
    cross ((shift κ a w B).1 - (shift κ a w A).1, (shift κ a w B).2 - (shift κ a w A).2)
        ((shift κ a w C).1 - (shift κ a w A).1, (shift κ a w C).2 - (shift κ a w A).2)
      = w * (1 + κ * a ^ 2) * cross (B.1 - A.1, B.2 - A.2) (C.1 - A.1, C.2 - A.2)
          / ((1 - κ * a * A.1) * (1 - κ * a * B.1) * (1 - κ * a * C.1)) := by
  rw [eq_div_iff (mul_ne_zero (mul_ne_zero hA hB) hC)]
  have h := cross_aux κ a w A.1 A.2 B.1 B.2 C.1 C.2 _ _ _ _ _ _
    (div_mul_cancel₀ (A.1 + a) hA) (div_mul_cancel₀ (w * A.2) hA)
    (div_mul_cancel₀ (B.1 + a) hB) (div_mul_cancel₀ (w * B.2) hB)
    (div_mul_cancel₀ (C.1 + a) hC) (div_mul_cancel₀ (w * C.2) hC)
  simp only [shift, cross]
  linear_combination h

/-- **How far apart two pairs are**, under the bound `κ`. -/
@[expose] def apart (κ : K) (P Q : K × K) : K :=
  ((P.1 - Q.1) ^ 2 + (P.2 - Q.2) ^ 2 + κ * (P.1 * Q.2 - P.2 * Q.1) ^ 2)
    / ((1 + κ * (P.1 ^ 2 + P.2 ^ 2)) * (1 + κ * (Q.1 ^ 2 + Q.2 ^ 2)))

/-- With the bound 0 it is the square of Euclid's distance. -/
theorem apart_zero_bound (P Q : K × K) :
    apart 0 P Q = (P.1 - Q.1) ^ 2 + (P.2 - Q.2) ^ 2 := by
  simp [apart]

theorem apart_self (κ : K) (P : K × K) : apart κ P P = 0 := by
  have h : (P.1 - P.1) ^ 2 + (P.2 - P.2) ^ 2 + κ * (P.1 * P.2 - P.2 * P.1) ^ 2 = 0 := by ring
  simp only [apart, h, zero_div]

theorem apart_comm (κ : K) (P Q : K × K) : apart κ P Q = apart κ Q P := by
  have h : (P.1 - Q.1) ^ 2 + (P.2 - Q.2) ^ 2 + κ * (P.1 * Q.2 - P.2 * Q.1) ^ 2
      = (Q.1 - P.1) ^ 2 + (Q.2 - P.2) ^ 2 + κ * (Q.1 * P.2 - Q.2 * P.1) ^ 2 := by ring
  simp only [apart]
  rw [h, mul_comm (1 + κ * (P.1 ^ 2 + P.2 ^ 2))]

/-- From `(0, 0)` to the number `t` of the first axis. -/
theorem apart_centre (κ t : K) : apart κ (0, 0) (t, 0) = t ^ 2 / (1 + κ * t ^ 2) := by
  simp [apart]

/-- The algebra of the next theorem, with the divisions taken out. -/
theorem apart_aux (κ a w xP yP xQ yQ XP YP XQ YQ : K) (hw : w ^ 2 = 1 + κ * a ^ 2)
    (hXP : XP * (1 - κ * a * xP) = xP + a) (hYP : YP * (1 - κ * a * xP) = w * yP)
    (hXQ : XQ * (1 - κ * a * xQ) = xQ + a) (hYQ : YQ * (1 - κ * a * xQ) = w * yQ) :
    ((XP - XQ) ^ 2 + (YP - YQ) ^ 2 + κ * (XP * YQ - YP * XQ) ^ 2)
        * ((1 - κ * a * xP) ^ 2 * (1 - κ * a * xQ) ^ 2)
      = w ^ 4 * ((xP - xQ) ^ 2 + (yP - yQ) ^ 2 + κ * (xP * yQ - yP * xQ) ^ 2) := by
  have e1 : (XP - XQ) * ((1 - κ * a * xP) * (1 - κ * a * xQ)) = w ^ 2 * (xP - xQ) := by
    linear_combination (1 - κ * a * xQ) * hXP - (1 - κ * a * xP) * hXQ - (xP - xQ) * hw
  have e2 : (YP - YQ) * ((1 - κ * a * xP) * (1 - κ * a * xQ))
      = w * ((yP - yQ) + κ * a * (xP * yQ - yP * xQ)) := by
    linear_combination (1 - κ * a * xQ) * hYP - (1 - κ * a * xP) * hYQ
  have e3 : (XP * YQ - YP * XQ) * ((1 - κ * a * xP) * (1 - κ * a * xQ))
      = w * ((xP * yQ - yP * xQ) - a * (yP - yQ)) := by
    linear_combination (YQ * (1 - κ * a * xQ)) * hXP + (xP + a) * hYQ
      - (XQ * (1 - κ * a * xQ)) * hYP - (w * yP) * hXQ
  have e : ((XP - XQ) ^ 2 + (YP - YQ) ^ 2 + κ * (XP * YQ - YP * XQ) ^ 2)
        * ((1 - κ * a * xP) ^ 2 * (1 - κ * a * xQ) ^ 2)
      = ((XP - XQ) * ((1 - κ * a * xP) * (1 - κ * a * xQ))) ^ 2
        + ((YP - YQ) * ((1 - κ * a * xP) * (1 - κ * a * xQ))) ^ 2
        + κ * ((XP * YQ - YP * XQ) * ((1 - κ * a * xP) * (1 - κ * a * xQ))) ^ 2 := by ring
  rw [e, e1, e2, e3]
  linear_combination (-(w ^ 2 * ((yP - yQ) ^ 2 + κ * (xP * yQ - yP * xQ) ^ 2))) * hw

/-- The last step of the next theorem. -/
theorem apart_aux' (N N' BP BQ VP VQ DP DQ w : K) (hw : w ≠ 0) (hDP : DP ≠ 0) (hDQ : DQ ≠ 0)
    (hBP : BP ≠ 0) (hBQ : BQ ≠ 0) (hN : N' * (DP ^ 2 * DQ ^ 2) = w ^ 4 * N)
    (hVP : VP * DP ^ 2 = w ^ 2 * BP) (hVQ : VQ * DQ ^ 2 = w ^ 2 * BQ) :
    N' / (VP * VQ) = N / (BP * BQ) := by
  have hw2 : w ^ 2 ≠ 0 := pow_ne_zero 2 hw
  have hVP0 : VP ≠ 0 := by
    intro h
    rw [h, zero_mul] at hVP
    exact mul_ne_zero hw2 hBP hVP.symm
  have hVQ0 : VQ ≠ 0 := by
    intro h
    rw [h, zero_mul] at hVQ
    exact mul_ne_zero hw2 hBQ hVQ.symm
  rw [div_eq_div_iff (mul_ne_zero hVP0 hVQ0) (mul_ne_zero hBP hBQ)]
  apply mul_right_cancel₀ (mul_ne_zero (pow_ne_zero 2 hDP) (pow_ne_zero 2 hDQ))
  linear_combination (BP * BQ) * hN - N * (VQ * DQ ^ 2) * hVP - N * (w ^ 2 * BP) * hVQ

/-- **The motion along the first axis keeps how far apart two pairs are.** -/
theorem shift_apart {κ a w : K} (hw : w ^ 2 = 1 + κ * a ^ 2) (hw0 : w ≠ 0) {P Q : K × K}
    (hDP : 1 - κ * a * P.1 ≠ 0) (hDQ : 1 - κ * a * Q.1 ≠ 0)
    (hP : 1 + κ * (P.1 ^ 2 + P.2 ^ 2) ≠ 0) (hQ : 1 + κ * (Q.1 ^ 2 + Q.2 ^ 2) ≠ 0) :
    apart κ (shift κ a w P) (shift κ a w Q) = apart κ P Q := by
  have hN : (((shift κ a w P).1 - (shift κ a w Q).1) ^ 2
      + ((shift κ a w P).2 - (shift κ a w Q).2) ^ 2
      + κ * ((shift κ a w P).1 * (shift κ a w Q).2
        - (shift κ a w P).2 * (shift κ a w Q).1) ^ 2)
        * ((1 - κ * a * P.1) ^ 2 * (1 - κ * a * Q.1) ^ 2)
      = w ^ 4 * ((P.1 - Q.1) ^ 2 + (P.2 - Q.2) ^ 2 + κ * (P.1 * Q.2 - P.2 * Q.1) ^ 2) :=
    apart_aux κ a w P.1 P.2 Q.1 Q.2 _ _ _ _ hw
      (div_mul_cancel₀ (P.1 + a) hDP) (div_mul_cancel₀ (w * P.2) hDP)
      (div_mul_cancel₀ (Q.1 + a) hDQ) (div_mul_cancel₀ (w * Q.2) hDQ)
  unfold apart
  exact apart_aux' _ _ _ _ _ _ _ _ w hw0 hDP hDQ hP hQ hN
    ((eq_div_iff (pow_ne_zero 2 hDP)).mp (shift_bound hw hDP))
    ((eq_div_iff (pow_ne_zero 2 hDQ)).mp (shift_bound hw hDQ))

/-- **Turning about `(0, 0)`.** Here `c` and `s` are numbers with `c² + s² = 1`. -/
@[expose] def rot (c s : K) (p : K × K) : K × K := (c * p.1 - s * p.2, s * p.1 + c * p.2)

/-- Turning back. -/
theorem rot_rot_neg {c s : K} (h : c ^ 2 + s ^ 2 = 1) (p : K × K) :
    rot c (-s) (rot c s p) = p := by
  apply Prod.ext
  · simp only [rot]
    linear_combination p.1 * h
  · simp only [rot]
    linear_combination p.2 * h

/-- Turning keeps the bound of a pair. -/
theorem rot_bound {c s : K} (h : c ^ 2 + s ^ 2 = 1) (κ : K) (p : K × K) :
    1 + κ * ((rot c s p).1 ^ 2 + (rot c s p).2 ^ 2) = 1 + κ * (p.1 ^ 2 + p.2 ^ 2) := by
  simp only [rot]
  linear_combination κ * (p.1 ^ 2 + p.2 ^ 2) * h

/-- **Turning keeps how far apart two pairs are.** -/
theorem rot_apart {c s : K} (h : c ^ 2 + s ^ 2 = 1) (κ : K) (P Q : K × K) :
    apart κ (rot c s P) (rot c s Q) = apart κ P Q := by
  have hN : ((rot c s P).1 - (rot c s Q).1) ^ 2 + ((rot c s P).2 - (rot c s Q).2) ^ 2
      + κ * ((rot c s P).1 * (rot c s Q).2 - (rot c s P).2 * (rot c s Q).1) ^ 2
      = (P.1 - Q.1) ^ 2 + (P.2 - Q.2) ^ 2 + κ * (P.1 * Q.2 - P.2 * Q.1) ^ 2 := by
    simp only [rot]
    linear_combination ((P.1 - Q.1) ^ 2 + (P.2 - Q.2) ^ 2
      + κ * (P.1 * Q.2 - P.2 * Q.1) ^ 2 * (c ^ 2 + s ^ 2 + 1)) * h
  simp only [apart]
  rw [hN, rot_bound h, rot_bound h]

/-- **Turning keeps left and right**: it keeps the cross product. -/
theorem rot_cross {c s : K} (h : c ^ 2 + s ^ 2 = 1) (A B C : K × K) :
    cross ((rot c s B).1 - (rot c s A).1, (rot c s B).2 - (rot c s A).2)
        ((rot c s C).1 - (rot c s A).1, (rot c s C).2 - (rot c s A).2)
      = cross (B.1 - A.1, B.2 - A.2) (C.1 - A.1, C.2 - A.2) := by
  simp only [rot, cross]
  linear_combination ((B.1 - A.1) * (C.2 - A.2) - (B.2 - A.2) * (C.1 - A.1)) * h

/-- Turning takes the numbers of a dimension to the numbers of a dimension. -/
theorem rot_pt (c s : K) (M : Dim K) (t : K) :
    rot c s (M.pt t) = (Dim.mk (rot c s M.zero) (rot c s M.one)).pt t := by
  apply Prod.ext
  · simp only [rot, Dim.pt]
    ring
  · simp only [rot, Dim.pt]
    ring

end StepsAlgebra

section StepsOrder

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Under a bound that is not positive, two numbers within the bound have a step. -/
theorem step_den_pos {κ t u : K} (hκ : κ ≤ 0) (ht : 0 < 1 + κ * t ^ 2)
    (hu : 0 < 1 + κ * u ^ 2) : 0 < 1 - κ * t * u := by
  nlinarith [mul_nonneg (neg_nonneg.mpr hκ) (sq_nonneg (t + u))]

/-- **The step of two numbers within the bound is within the bound.** -/
theorem step_within {κ t u : K} (hκ : κ ≤ 0) (ht : 0 < 1 + κ * t ^ 2)
    (hu : 0 < 1 + κ * u ^ 2) : 0 < 1 + κ * step κ t u ^ 2 := by
  have h := step_den_pos hκ ht hu
  rw [step_bound h.ne']
  exact div_pos (mul_pos ht hu) (pow_pos h 2)

omit [IsStrictOrderedRing K] in
/-- The step back of a number within the bound is within the bound. -/
theorem within_neg {κ t : K} (ht : 0 < 1 + κ * t ^ 2) : 0 < 1 + κ * (-t) ^ 2 := by
  have h : 1 + κ * (-t) ^ 2 = 1 + κ * t ^ 2 := by ring
  rw [h]
  exact ht

/-- The zero is within the bound. -/
theorem within_zero (κ : K) : 0 < 1 + κ * (0 : K) ^ 2 := by
  have h : 1 + κ * (0 : K) ^ 2 = 1 := by ring
  rw [h]
  exact one_pos

/-- **Steps can be taken in any grouping.** -/
theorem step_assoc {κ t u v : K} (hκ : κ ≤ 0) (ht : 0 < 1 + κ * t ^ 2)
    (hu : 0 < 1 + κ * u ^ 2) (hv : 0 < 1 + κ * v ^ 2) :
    step κ (step κ t u) v = step κ t (step κ u v) := by
  have h1 := (step_den_pos hκ ht hu).ne'
  have h2 := (step_den_pos hκ hu hv).ne'
  have h3 := (step_den_pos hκ (step_within hκ ht hu) hv).ne'
  have h4 := (step_den_pos hκ ht (step_within hκ hu hv)).ne'
  have hX : step κ t u * (1 - κ * t * u) = t + u := div_mul_cancel₀ _ h1
  have hY : step κ u v * (1 - κ * u * v) = u + v := div_mul_cancel₀ _ h2
  have hL : step κ (step κ t u) v * (1 - κ * step κ t u * v) = step κ t u + v :=
    div_mul_cancel₀ _ h3
  have hR : step κ t (step κ u v) * (1 - κ * t * step κ u v) = t + step κ u v :=
    div_mul_cancel₀ _ h4
  have e3 : (1 - κ * step κ t u * v) * (1 - κ * t * u)
      = 1 - κ * (t * u + t * v + u * v) := by
    linear_combination -κ * v * hX
  have e4 : (1 - κ * t * step κ u v) * (1 - κ * u * v)
      = 1 - κ * (t * u + t * v + u * v) := by
    linear_combination -κ * t * hY
  have eL : step κ (step κ t u) v * (1 - κ * (t * u + t * v + u * v))
      = t + u + v - κ * t * u * v := by
    rw [← e3]
    linear_combination (1 - κ * t * u) * hL + hX
  have eR : step κ t (step κ u v) * (1 - κ * (t * u + t * v + u * v))
      = t + u + v - κ * t * u * v := by
    rw [← e4]
    linear_combination (1 - κ * u * v) * hR + hY
  have hE : 1 - κ * (t * u + t * v + u * v) ≠ 0 := by
    rw [← e3]
    exact mul_ne_zero h3 h1
  exact mul_right_cancel₀ hE (eL.trans eR.symm)

/-- **A number on the edge is its own double.** -/
theorem step_edge_self {κ e : K} (he : 1 + κ * e ^ 2 = 0) : step κ e e = e := by
  apply step_edge he
  have h : 1 - κ * e * e = 2 := by linear_combination -he
  rw [h]
  exact two_ne_zero

/-- **Two different points of the plane are apart.** -/
theorem apart_pos {κ : K} {P Q : K × K} (hP : P ∈ plane κ) (hQ : Q ∈ plane κ) (hPQ : P ≠ Q) :
    0 < apart κ P Q := by
  have hv : (P.1 - Q.1, P.2 - Q.2) ≠ ((0 : K), (0 : K)) := by
    intro h
    apply hPQ
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    simp only [] at h1 h2
    exact Prod.ext (sub_eq_zero.mp h1) (sub_eq_zero.mp h2)
  have hd : 0 < (P.1 - Q.1) ^ 2 + (P.2 - Q.2) ^ 2 := sq_add_sq_pos hv
  apply div_pos _ (mul_pos (mem_plane.mp hP) (mem_plane.mp hQ))
  rcases le_or_gt 0 κ with hκ | hκ
  · have h := mul_nonneg hκ (sq_nonneg (P.1 * Q.2 - P.2 * Q.1))
    linarith
  · have e : (P.1 - Q.1) ^ 2 + (P.2 - Q.2) ^ 2 + κ * (P.1 * Q.2 - P.2 * Q.1) ^ 2
        = ((P.1 - Q.1) ^ 2 + (P.2 - Q.2) ^ 2) * (1 + κ * (P.1 ^ 2 + P.2 ^ 2))
          + -κ * (P.1 * (Q.1 - P.1) + P.2 * (Q.2 - P.2)) ^ 2 := by ring
    rw [e]
    have h1 := mul_pos hd (mem_plane.mp hP)
    have h2 := mul_nonneg (neg_nonneg.mpr hκ.le)
      (sq_nonneg (P.1 * (Q.1 - P.1) + P.2 * (Q.2 - P.2)))
    linarith

/-- Under a bound that is not positive, the motion is defined at every point of the plane. -/
theorem shift_den_pos {κ a : K} (hκ : κ ≤ 0) (ha : 0 < 1 + κ * a ^ 2) {p : K × K}
    (hp : p ∈ plane κ) : 0 < 1 - κ * a * p.1 := by
  have hx : 0 < 1 + κ * p.1 ^ 2 := by
    have h := mem_plane.mp hp
    nlinarith [mul_nonneg (neg_nonneg.mpr hκ) (sq_nonneg p.2)]
  exact step_den_pos hκ ha hx

/-- **The motion takes points of the plane to points of the plane.** -/
theorem shift_mem_plane {κ a w : K} (hκ : κ ≤ 0) (hw : w ^ 2 = 1 + κ * a ^ 2) (hw0 : w ≠ 0)
    {p : K × K} (hp : p ∈ plane κ) : shift κ a w p ∈ plane κ := by
  have hw2 : 0 < w ^ 2 := lt_of_le_of_ne (sq_nonneg w) (pow_ne_zero 2 hw0).symm
  have hD := shift_den_pos hκ (hw ▸ hw2) hp
  rw [mem_plane, shift_bound hw hD.ne']
  exact div_pos (mul_pos hw2 (mem_plane.mp hp)) (pow_pos hD 2)

/-- The motion back, at a point of the plane. -/
theorem shift_neg_shift {κ a w : K} (hκ : κ ≤ 0) (hw : w ^ 2 = 1 + κ * a ^ 2) (hw0 : w ≠ 0)
    {p : K × K} (hp : p ∈ plane κ) : shift κ (-a) w (shift κ a w p) = p := by
  have hw2 : 0 < w ^ 2 := lt_of_le_of_ne (sq_nonneg w) (pow_ne_zero 2 hw0).symm
  exact shift_shift_neg hw hw0 (shift_den_pos hκ (hw ▸ hw2) hp).ne'

/-- **The motion takes the plane onto itself, and different points to different points.** -/
theorem shift_bijOn {κ a w : K} (hκ : κ ≤ 0) (hw : w ^ 2 = 1 + κ * a ^ 2) (hw0 : w ≠ 0) :
    Set.BijOn (shift κ a w) (plane κ) (plane κ) := by
  have hw' : w ^ 2 = 1 + κ * (-a) ^ 2 := by
    rw [hw]
    ring
  refine ⟨fun p hp => shift_mem_plane hκ hw hw0 hp, ?_, ?_⟩
  · intro p hp q hq h
    have h' := congrArg (shift κ (-a) w) h
    rwa [shift_neg_shift hκ hw hw0 hp, shift_neg_shift hκ hw hw0 hq] at h'
  · intro q hq
    refine ⟨shift κ (-a) w q, shift_mem_plane hκ hw' hw0 hq, ?_⟩
    have h := shift_neg_shift hκ hw' hw0 hq
    rwa [neg_neg] at h

/-- **With `w` positive the motion keeps left and right.** For three points of the plane, the
cross product is positive, negative or zero after the motion as it was before. -/
theorem shift_keeps_left {κ a w : K} (hκ : κ ≤ 0) (hw : w ^ 2 = 1 + κ * a ^ 2) (hw0 : 0 < w)
    {A B C : K × K} (hA : A ∈ plane κ) (hB : B ∈ plane κ) (hC : C ∈ plane κ) :
    (0 < cross ((shift κ a w B).1 - (shift κ a w A).1, (shift κ a w B).2 - (shift κ a w A).2)
        ((shift κ a w C).1 - (shift κ a w A).1, (shift κ a w C).2 - (shift κ a w A).2) ↔
      0 < cross (B.1 - A.1, B.2 - A.2) (C.1 - A.1, C.2 - A.2)) ∧
    (cross ((shift κ a w B).1 - (shift κ a w A).1, (shift κ a w B).2 - (shift κ a w A).2)
        ((shift κ a w C).1 - (shift κ a w A).1, (shift κ a w C).2 - (shift κ a w A).2) < 0 ↔
      cross (B.1 - A.1, B.2 - A.2) (C.1 - A.1, C.2 - A.2) < 0) ∧
    (cross ((shift κ a w B).1 - (shift κ a w A).1, (shift κ a w B).2 - (shift κ a w A).2)
        ((shift κ a w C).1 - (shift κ a w A).1, (shift κ a w C).2 - (shift κ a w A).2) = 0 ↔
      cross (B.1 - A.1, B.2 - A.2) (C.1 - A.1, C.2 - A.2) = 0) := by
  have ha : 0 < 1 + κ * a ^ 2 := by
    rw [← hw]
    exact pow_pos hw0 2
  have hDA := shift_den_pos hκ ha hA
  have hDB := shift_den_pos hκ ha hB
  have hDC := shift_den_pos hκ ha hC
  have hden : 0 < (1 - κ * a * A.1) * (1 - κ * a * B.1) * (1 - κ * a * C.1) :=
    mul_pos (mul_pos hDA hDB) hDC
  have hfac : 0 < w * (1 + κ * a ^ 2) := mul_pos hw0 ha
  have hr : 0 < w * (1 + κ * a ^ 2)
      / ((1 - κ * a * A.1) * (1 - κ * a * B.1) * (1 - κ * a * C.1)) := div_pos hfac hden
  rw [shift_cross κ a w hDA.ne' hDB.ne' hDC.ne', mul_div_right_comm]
  refine ⟨mul_pos_iff_of_pos_left hr, ?_, ?_⟩
  · constructor
    · intro h
      by_contra hcon
      exact absurd h (not_lt.mpr (mul_nonneg hr.le (not_lt.mp hcon)))
    · intro h
      exact mul_neg_of_pos_of_neg hr h
  · constructor
    · intro h
      exact (mul_eq_zero.mp h).resolve_left hr.ne'
    · intro h
      rw [h, mul_zero]

/-- The motion along the first axis keeps how far apart two points of the plane are. -/
theorem shift_apart_plane {κ a w : K} (hκ : κ ≤ 0) (hw : w ^ 2 = 1 + κ * a ^ 2) (hw0 : w ≠ 0)
    {P Q : K × K} (hP : P ∈ plane κ) (hQ : Q ∈ plane κ) :
    apart κ (shift κ a w P) (shift κ a w Q) = apart κ P Q := by
  have hw2 : 0 < w ^ 2 := lt_of_le_of_ne (sq_nonneg w) (pow_ne_zero 2 hw0).symm
  have ha : 0 < 1 + κ * a ^ 2 := hw ▸ hw2
  exact shift_apart hw hw0 (shift_den_pos hκ ha hP).ne' (shift_den_pos hκ ha hQ).ne'
    (mem_plane.mp hP).ne' (mem_plane.mp hQ).ne'

/-- **The motion takes lines of the plane to lines of the plane.** -/
theorem shift_isLine {κ a w : K} (hκ : κ ≤ 0) (hw : w ^ 2 = 1 + κ * a ^ 2) (hw0 : w ≠ 0)
    {S : Set (K × K)} (hS : IsLine (plane κ) S) :
    IsLine (plane κ) (shift κ a w '' S) := by
  have hw2 : 0 < w ^ 2 := lt_of_le_of_ne (sq_nonneg w) (pow_ne_zero 2 hw0).symm
  have ha : 0 < 1 + κ * a ^ 2 := hw ▸ hw2
  have hw' : w ^ 2 = 1 + κ * (-a) ^ 2 := by
    rw [hw]
    ring
  have ha' : 0 < 1 + κ * (-a) ^ 2 := hw' ▸ hw2
  obtain ⟨M, hA, hB, hAB, rfl⟩ := hS.exists_within (plane_openAlong κ)
  have hDA := (shift_den_pos hκ ha hA).ne'
  have hDB := (shift_den_pos hκ ha hB).ne'
  have hτA : shift κ a w M.zero ∈ plane κ := shift_mem_plane hκ hw hw0 hA
  have hne : shift κ a w M.zero ≠ shift κ a w M.one := by
    intro h
    apply hAB
    have h' := congrArg (shift κ (-a) w) h
    rwa [shift_shift_neg hw hw0 hDA, shift_shift_neg hw hw0 hDB] at h'
  have hfactor : w * (1 + κ * a ^ 2) ≠ 0 := mul_ne_zero hw0 ha.ne'
  refine ⟨⟨shift κ a w M.zero, shift κ a w M.one⟩, hne, ?_,
    ⟨shift κ a w M.zero, M.zero, ⟨M.zero_mem, hA⟩, rfl⟩⟩
  apply Set.Subset.antisymm
  · rintro _ ⟨X, ⟨hXM, hX⟩, rfl⟩
    refine ⟨?_, shift_mem_plane hκ hw hw0 hX⟩
    apply Dim.mem_points_of_side_eq_zero _ hne
    have hDX := (shift_den_pos hκ ha hX).ne'
    have hside := M.side_eq_zero_of_mem hXM
    simp only [Dim.side, Dim.dir] at hside ⊢
    rw [shift_cross κ a w hDA hDB hDX, hside, mul_zero, zero_div]
  · rintro Y ⟨hYN, hY⟩
    have hDY := (shift_den_pos hκ ha' hY).ne'
    have hX : shift κ (-a) w Y ∈ plane κ := shift_mem_plane hκ hw' hw0 hY
    have hback : shift κ a w (shift κ (-a) w Y) = Y := by
      have h := shift_shift_neg hw' hw0 hDY
      rwa [neg_neg] at h
    have hDX := (shift_den_pos hκ ha hX).ne'
    refine ⟨shift κ (-a) w Y, ⟨?_, hX⟩, hback⟩
    apply Dim.mem_points_of_side_eq_zero _ hAB
    have hside := Dim.side_eq_zero_of_mem _ hYN
    rw [← hback] at hside
    simp only [Dim.side, Dim.dir] at hside ⊢
    rw [shift_cross κ a w hDA hDB hDX] at hside
    have hden : (1 - κ * a * M.zero.1) * (1 - κ * a * M.one.1)
        * (1 - κ * a * (shift κ (-a) w Y).1) ≠ 0 :=
      mul_ne_zero (mul_ne_zero hDA hDB) hDX
    rcases div_eq_zero_iff.mp hside with h | h
    · exact (mul_eq_zero.mp h).resolve_left hfactor
    · exact absurd h hden

omit [IsStrictOrderedRing K] in
/-- **Turning takes points of the plane to points of the plane**, and no others. -/
theorem rot_mem_plane {c s : K} (h : c ^ 2 + s ^ 2 = 1) {κ : K} {p : K × K} :
    rot c s p ∈ plane κ ↔ p ∈ plane κ := by
  rw [mem_plane, mem_plane, rot_bound h]

omit [IsStrictOrderedRing K] in
/-- **Turning takes the plane onto itself, and different points to different points.** -/
theorem rot_bijOn {c s : K} (h : c ^ 2 + s ^ 2 = 1) (κ : K) :
    Set.BijOn (rot c s) (plane κ) (plane κ) := by
  have h' : c ^ 2 + (-s) ^ 2 = 1 := by
    rw [← h]
    ring
  refine ⟨fun p hp => (rot_mem_plane h).mpr hp, ?_, ?_⟩
  · intro p _ q _ hpq
    have h2 := congrArg (rot c (-s)) hpq
    rwa [rot_rot_neg h, rot_rot_neg h] at h2
  · intro q hq
    refine ⟨rot c (-s) q, (rot_mem_plane h').mpr hq, ?_⟩
    have h2 := rot_rot_neg h' q
    rwa [neg_neg] at h2

omit [IsStrictOrderedRing K] in
/-- **Turning takes lines of the plane to lines of the plane.** -/
theorem rot_isLine {c s : K} (h : c ^ 2 + s ^ 2 = 1) {κ : K} {S : Set (K × K)}
    (hS : IsLine (plane κ) S) : IsLine (plane κ) (rot c s '' S) := by
  obtain ⟨M, hM, rfl, A, hAM, hA⟩ := hS
  have hne : rot c s M.zero ≠ rot c s M.one := by
    intro h'
    apply hM
    have h'' := congrArg (rot c (-s)) h'
    rwa [rot_rot_neg h, rot_rot_neg h] at h''
  refine ⟨⟨rot c s M.zero, rot c s M.one⟩, hne, ?_, ⟨rot c s A, A, ⟨hAM, hA⟩, rfl⟩⟩
  apply Set.Subset.antisymm
  · rintro _ ⟨X, ⟨⟨t, rfl⟩, hX⟩, rfl⟩
    exact ⟨⟨t, (rot_pt c s M t).symm⟩, (rot_mem_plane h).mpr hX⟩
  · rintro Y ⟨⟨t, rfl⟩, hY⟩
    rw [← rot_pt] at hY
    exact ⟨M.pt t, ⟨⟨t, rfl⟩, (rot_mem_plane h).mp hY⟩, rot_pt c s M t⟩

end StepsOrder

end HyperbolicPlane

end ParallelPostulate

/-!
# Angles in the plane of a bound

The inner product at a pair, `kleinInner`, and the angle it gives, `kleinAngle`. The motions
keep it (Theorem H13). They take every point to `(0, 0)`, where it is the angle of Euclid, so it
is the only angle with these two properties (Theorem H15).

## Contents

* Theorem H13, the motions keep angles: `kleinInner`, `kleinInner_zero_bound`,
  `kleinInner_centre`, `kleinInner_self_pos`, `shift_kleinInner`, `rot_kleinInner`, `kleinAngle`,
  `kleinAngle_zero_bound`, `kleinAngle_centre`, `shift_kleinAngle`, `rot_kleinAngle`
* Theorem H15, the motions take every point to `(0, 0)`, and the angle they keep:
  `exists_motion_to_centre`, `kleinAngle_unique`
* steps of the proofs: `kleinInner_aux`, `kleinAngle_aux`
-/

namespace ParallelPostulate

namespace HyperbolicPlane

open Pairs

/-! ## The inner product at a pair -/

section InnerAlgebra

variable {K : Type*} [Field K]

/-- **The inner product at a pair**, under the bound `κ`: at the pair `P`, of the direction from
`P` to `A` and the direction from `P` to `B`. It is the inner product of Euclid and one more
term, `κ` times two cross products. With the bound 0, or at `(0, 0)`, that term is zero.
Divided by `(1 + κ (P.1² + P.2²))²` it is Klein's metric at `P`, on the directions `A - P` and
`B - P`: `kleinMetric_sub`. -/
@[expose] def kleinInner (κ : K) (P A B : K × K) : K :=
  (A.1 - P.1) * (B.1 - P.1) + (A.2 - P.2) * (B.2 - P.2) + κ * cross P A * cross P B

/-- With the bound 0 it is the inner product of Euclid. -/
theorem kleinInner_zero_bound (P A B : K × K) :
    kleinInner 0 P A B = (A.1 - P.1) * (B.1 - P.1) + (A.2 - P.2) * (B.2 - P.2) := by
  simp [kleinInner]

/-- At `(0, 0)` it is the inner product of Euclid, under any bound. -/
theorem kleinInner_centre (κ : K) (A B : K × K) :
    kleinInner κ (0, 0) A B = A.1 * B.1 + A.2 * B.2 := by
  simp [kleinInner, cross]

/-- The algebra of the next theorem, with the divisions taken out. -/
theorem kleinInner_aux (κ a w xP yP xA yA xB yB XP YP XA YA XB YB : K)
    (hw : w ^ 2 = 1 + κ * a ^ 2)
    (hXP : XP * (1 - κ * a * xP) = xP + a) (hYP : YP * (1 - κ * a * xP) = w * yP)
    (hXA : XA * (1 - κ * a * xA) = xA + a) (hYA : YA * (1 - κ * a * xA) = w * yA)
    (hXB : XB * (1 - κ * a * xB) = xB + a) (hYB : YB * (1 - κ * a * xB) = w * yB) :
    ((XA - XP) * (XB - XP) + (YA - YP) * (YB - YP)
        + κ * (XP * YA - YP * XA) * (XP * YB - YP * XB))
        * ((1 - κ * a * xP) ^ 2 * (1 - κ * a * xA) * (1 - κ * a * xB))
      = w ^ 4 * ((xA - xP) * (xB - xP) + (yA - yP) * (yB - yP)
        + κ * (xP * yA - yP * xA) * (xP * yB - yP * xB)) := by
  have e1 : (XA - XP) * ((1 - κ * a * xA) * (1 - κ * a * xP))
      = (xA + a) * (1 - κ * a * xP) - (xP + a) * (1 - κ * a * xA) := by
    linear_combination (1 - κ * a * xP) * hXA - (1 - κ * a * xA) * hXP
  have e2 : (XB - XP) * ((1 - κ * a * xB) * (1 - κ * a * xP))
      = (xB + a) * (1 - κ * a * xP) - (xP + a) * (1 - κ * a * xB) := by
    linear_combination (1 - κ * a * xP) * hXB - (1 - κ * a * xB) * hXP
  have e3 : (YA - YP) * ((1 - κ * a * xA) * (1 - κ * a * xP))
      = w * (yA * (1 - κ * a * xP) - yP * (1 - κ * a * xA)) := by
    linear_combination (1 - κ * a * xP) * hYA - (1 - κ * a * xA) * hYP
  have e4 : (YB - YP) * ((1 - κ * a * xB) * (1 - κ * a * xP))
      = w * (yB * (1 - κ * a * xP) - yP * (1 - κ * a * xB)) := by
    linear_combination (1 - κ * a * xP) * hYB - (1 - κ * a * xB) * hYP
  have e5 : (XP * YA - YP * XA) * ((1 - κ * a * xP) * (1 - κ * a * xA))
      = w * ((xP + a) * yA - yP * (xA + a)) := by
    linear_combination (YA * (1 - κ * a * xA)) * hXP + (xP + a) * hYA
      - (XA * (1 - κ * a * xA)) * hYP - (w * yP) * hXA
  have e6 : (XP * YB - YP * XB) * ((1 - κ * a * xP) * (1 - κ * a * xB))
      = w * ((xP + a) * yB - yP * (xB + a)) := by
    linear_combination (YB * (1 - κ * a * xB)) * hXP + (xP + a) * hYB
      - (XB * (1 - κ * a * xB)) * hYP - (w * yP) * hXB
  have e : ((XA - XP) * (XB - XP) + (YA - YP) * (YB - YP)
        + κ * (XP * YA - YP * XA) * (XP * YB - YP * XB))
        * ((1 - κ * a * xP) ^ 2 * (1 - κ * a * xA) * (1 - κ * a * xB))
      = (XA - XP) * ((1 - κ * a * xA) * (1 - κ * a * xP))
          * ((XB - XP) * ((1 - κ * a * xB) * (1 - κ * a * xP)))
        + (YA - YP) * ((1 - κ * a * xA) * (1 - κ * a * xP))
          * ((YB - YP) * ((1 - κ * a * xB) * (1 - κ * a * xP)))
        + κ * ((XP * YA - YP * XA) * ((1 - κ * a * xP) * (1 - κ * a * xA)))
          * ((XP * YB - YP * XB) * ((1 - κ * a * xP) * (1 - κ * a * xB))) := by ring
  rw [e, e1, e2, e3, e4, e5, e6]
  linear_combination
    ((yA * (1 - κ * a * xP) - yP * (1 - κ * a * xA))
        * (yB * (1 - κ * a * xP) - yP * (1 - κ * a * xB))
      + κ * ((xP + a) * yA - yP * (xA + a)) * ((xP + a) * yB - yP * (xB + a))
      - (w ^ 2 + 1 + κ * a ^ 2) * ((xA - xP) * (xB - xP) + (yA - yP) * (yB - yP)
        + κ * (xP * yA - yP * xA) * (xP * yB - yP * xB))) * hw

/-- **The motion along the first axis keeps the inner product at a pair**, up to a factor. The
factor is the same for every direction from the pair once each direction is divided by its
own denominator, and so the motion keeps angles: see `shift_kleinAngle`. -/
theorem shift_kleinInner {κ a w : K} (hw : w ^ 2 = 1 + κ * a ^ 2) {P A B : K × K}
    (hP : 1 - κ * a * P.1 ≠ 0) (hA : 1 - κ * a * A.1 ≠ 0) (hB : 1 - κ * a * B.1 ≠ 0) :
    kleinInner κ (shift κ a w P) (shift κ a w A) (shift κ a w B)
      = w ^ 4 * kleinInner κ P A B
          / ((1 - κ * a * P.1) ^ 2 * (1 - κ * a * A.1) * (1 - κ * a * B.1)) := by
  rw [eq_div_iff (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hP) hA) hB)]
  have h := kleinInner_aux κ a w P.1 P.2 A.1 A.2 B.1 B.2 _ _ _ _ _ _ hw
    (div_mul_cancel₀ (P.1 + a) hP) (div_mul_cancel₀ (w * P.2) hP)
    (div_mul_cancel₀ (A.1 + a) hA) (div_mul_cancel₀ (w * A.2) hA)
    (div_mul_cancel₀ (B.1 + a) hB) (div_mul_cancel₀ (w * B.2) hB)
  simp only [kleinInner, shift, cross]
  linear_combination h

/-- **Turning keeps the inner product at a pair.** -/
theorem rot_kleinInner {c s : K} (h : c ^ 2 + s ^ 2 = 1) (κ : K) (P A B : K × K) :
    kleinInner κ (rot c s P) (rot c s A) (rot c s B) = kleinInner κ P A B := by
  simp only [kleinInner, rot, cross]
  linear_combination ((A.1 - P.1) * (B.1 - P.1) + (A.2 - P.2) * (B.2 - P.2)
    + κ * (P.1 * A.2 - P.2 * A.1) * (P.1 * B.2 - P.2 * B.1) * (c ^ 2 + s ^ 2 + 1)) * h

end InnerAlgebra

section InnerOrder

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- **At a point of the plane the inner product is positive** on every direction that is not
zero. So it is an inner product, under any bound. -/
theorem kleinInner_self_pos {κ : K} {P A : K × K} (hP : P ∈ plane κ) (hA : A ≠ P) :
    0 < kleinInner κ P A A := by
  have hv : (A.1 - P.1, A.2 - P.2) ≠ ((0 : K), (0 : K)) := by
    intro h
    apply hA
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    simp only [] at h1 h2
    exact Prod.ext (sub_eq_zero.mp h1) (sub_eq_zero.mp h2)
  have hd : 0 < (A.1 - P.1) ^ 2 + (A.2 - P.2) ^ 2 := sq_add_sq_pos hv
  rcases le_or_gt 0 κ with hκ | hκ
  · have e : kleinInner κ P A A = (A.1 - P.1) ^ 2 + (A.2 - P.2) ^ 2 + κ * cross P A ^ 2 := by
      simp only [kleinInner]
      ring
    rw [e]
    have h := mul_nonneg hκ (sq_nonneg (cross P A))
    linarith
  · have e : kleinInner κ P A A
        = ((A.1 - P.1) ^ 2 + (A.2 - P.2) ^ 2) * (1 + κ * (P.1 ^ 2 + P.2 ^ 2))
          + -κ * (P.1 * (A.1 - P.1) + P.2 * (A.2 - P.2)) ^ 2 := by
      simp only [kleinInner, cross]
      ring
    rw [e]
    have h1 := mul_pos hd (mem_plane.mp hP)
    have h2 := mul_nonneg (neg_nonneg.mpr hκ.le)
      (sq_nonneg (P.1 * (A.1 - P.1) + P.2 * (A.2 - P.2)))
    linarith

end InnerOrder

/-! ## Angles

With the real numbers for numbers, the inner product at a pair gives an angle, as the inner
product of Euclid gives the angle of Mathlib. -/

section Angles

open Real

/-- **The angle at a pair**, under the bound `κ`: the angle at `P` between the direction from
`P` to `A` and the direction from `P` to `B`. It is made from `kleinInner` as Mathlib makes the
angle of Euclid from the inner product. -/
@[expose] noncomputable def kleinAngle (κ : ℝ) (P A B : ℝ × ℝ) : ℝ :=
  arccos (kleinInner κ P A B / (√(kleinInner κ P A A) * √(kleinInner κ P B B)))

/-- **With the bound 0 it is the angle of Euclid**, in Mathlib's sense. -/
theorem kleinAngle_zero_bound (P A B : ℝ × ℝ) :
    kleinAngle 0 P A B
      = InnerProductGeometry.angle (!₂[A.1 - P.1, A.2 - P.2] : EuclideanSpace ℝ (Fin 2))
          !₂[B.1 - P.1, B.2 - P.2] := by
  have hi : inner ℝ (!₂[A.1 - P.1, A.2 - P.2] : EuclideanSpace ℝ (Fin 2))
      !₂[B.1 - P.1, B.2 - P.2] = kleinInner 0 P A B := by
    rw [kleinInner_zero_bound]
    simp [PiLp.inner_apply, Fin.sum_univ_two]
    ring
  have hn : ∀ X : ℝ × ℝ, ‖(!₂[X.1 - P.1, X.2 - P.2] : EuclideanSpace ℝ (Fin 2))‖
      = √(kleinInner 0 P X X) := by
    intro X
    rw [kleinInner_zero_bound]
    simp [EuclideanSpace.norm_eq, Fin.sum_univ_two, sq]
  rw [InnerProductGeometry.angle, hi, hn, hn]
  rfl

/-- **At `(0, 0)` it is the angle of Euclid, under any bound.** -/
theorem kleinAngle_centre (κ : ℝ) (A B : ℝ × ℝ) :
    kleinAngle κ (0, 0) A B
      = InnerProductGeometry.angle (!₂[A.1, A.2] : EuclideanSpace ℝ (Fin 2)) !₂[B.1, B.2] := by
  have h : kleinAngle κ (0, 0) A B = kleinAngle 0 (0, 0) A B := by
    simp only [kleinAngle, kleinInner_centre]
  rw [h, kleinAngle_zero_bound]
  simp

/-- The last step of the next theorem: an angle does not change when the inner products are
multiplied as a motion multiplies them. -/
theorem kleinAngle_aux {g g₁ g₂ m u v : ℝ} (hm : 0 < m) (huv : 0 < u * v) :
    arccos (m * u * v * g / (√(m * u ^ 2 * g₁) * √(m * v ^ 2 * g₂)))
      = arccos (g / (√g₁ * √g₂)) := by
  have hsq : √m * √m = m := mul_self_sqrt hm.le
  have habs : |u| * |v| = u * v := by rw [← abs_mul, abs_of_pos huv]
  have h1 : √(m * u ^ 2 * g₁) = √m * |u| * √g₁ := by
    rw [sqrt_mul (by positivity : (0 : ℝ) ≤ m * u ^ 2), sqrt_mul hm.le, sqrt_sq_eq_abs]
  have h2 : √(m * v ^ 2 * g₂) = √m * |v| * √g₂ := by
    rw [sqrt_mul (by positivity : (0 : ℝ) ≤ m * v ^ 2), sqrt_mul hm.le, sqrt_sq_eq_abs]
  have hden : √(m * u ^ 2 * g₁) * √(m * v ^ 2 * g₂) = m * u * v * (√g₁ * √g₂) := by
    rw [h1, h2]
    linear_combination (|u| * |v| * √g₁ * √g₂) * hsq + (m * √g₁ * √g₂) * habs
  have hmuv : m * u * v ≠ 0 := by
    rw [mul_assoc]
    exact (mul_pos hm huv).ne'
  rw [hden, mul_div_mul_left _ _ hmuv]

/-- **Theorem H13. The motion along the first axis keeps angles.** For three points of the
plane, the angle at the first between the two others is the same after the motion. -/
theorem shift_kleinAngle {κ a w : ℝ} (hκ : κ ≤ 0) (hw : w ^ 2 = 1 + κ * a ^ 2) (hw0 : w ≠ 0)
    {P A B : ℝ × ℝ} (hP : P ∈ plane κ) (hA : A ∈ plane κ) (hB : B ∈ plane κ) :
    kleinAngle κ (shift κ a w P) (shift κ a w A) (shift κ a w B) = kleinAngle κ P A B := by
  have hw2 : 0 < w ^ 2 := lt_of_le_of_ne (sq_nonneg w) (pow_ne_zero 2 hw0).symm
  have ha : 0 < 1 + κ * a ^ 2 := hw ▸ hw2
  have hDP := shift_den_pos hκ ha hP
  have hDA := shift_den_pos hκ ha hA
  have hDB := shift_den_pos hκ ha hB
  have hw4 : 0 < w ^ 4 := by
    rw [show w ^ 4 = (w ^ 2) ^ 2 by ring]
    exact pow_pos hw2 2
  have hm : 0 < w ^ 4 / (1 - κ * a * P.1) ^ 2 := div_pos hw4 (pow_pos hDP 2)
  have huv : 0 < 1 / (1 - κ * a * A.1) * (1 / (1 - κ * a * B.1)) :=
    mul_pos (one_div_pos.mpr hDA) (one_div_pos.mpr hDB)
  have e1 : kleinInner κ (shift κ a w P) (shift κ a w A) (shift κ a w B)
      = w ^ 4 / (1 - κ * a * P.1) ^ 2 * (1 / (1 - κ * a * A.1)) * (1 / (1 - κ * a * B.1))
        * kleinInner κ P A B := by
    rw [shift_kleinInner hw hDP.ne' hDA.ne' hDB.ne']
    field_simp
  have e2 : kleinInner κ (shift κ a w P) (shift κ a w A) (shift κ a w A)
      = w ^ 4 / (1 - κ * a * P.1) ^ 2 * (1 / (1 - κ * a * A.1)) ^ 2 * kleinInner κ P A A := by
    rw [shift_kleinInner hw hDP.ne' hDA.ne' hDA.ne']
    field_simp
  have e3 : kleinInner κ (shift κ a w P) (shift κ a w B) (shift κ a w B)
      = w ^ 4 / (1 - κ * a * P.1) ^ 2 * (1 / (1 - κ * a * B.1)) ^ 2 * kleinInner κ P B B := by
    rw [shift_kleinInner hw hDP.ne' hDB.ne' hDB.ne']
    field_simp
  unfold kleinAngle
  rw [e1, e2, e3]
  exact kleinAngle_aux hm huv

/-- **Theorem H13. Turning keeps angles.** -/
theorem rot_kleinAngle {c s : ℝ} (h : c ^ 2 + s ^ 2 = 1) (κ : ℝ) (P A B : ℝ × ℝ) :
    kleinAngle κ (rot c s P) (rot c s A) (rot c s B) = kleinAngle κ P A B := by
  simp only [kleinAngle, rot_kleinInner h]

/-- **Theorem H15. The motions take every point of the plane to `(0, 0)`.** A turn takes the
point to the number `r` of the first axis, where `r` is its distance from `(0, 0)` in Euclid's
sense, and the motion along the first axis with `a = -r` takes it on to `(0, 0)`. -/
theorem exists_motion_to_centre {κ : ℝ} {P : ℝ × ℝ} (hP : P ∈ plane κ) :
    ∃ c s a w : ℝ, c ^ 2 + s ^ 2 = 1 ∧ w ^ 2 = 1 + κ * a ^ 2 ∧ 0 < w ∧
      shift κ a w (rot c s P) = (0, 0) := by
  by_cases h0 : P.1 ^ 2 + P.2 ^ 2 = 0
  · have h1 : P.1 = 0 := pow_eq_zero_iff two_ne_zero |>.mp (by nlinarith [sq_nonneg P.2])
    have h2 : P.2 = 0 := pow_eq_zero_iff two_ne_zero |>.mp (by nlinarith [sq_nonneg P.1])
    refine ⟨1, 0, 0, 1, by norm_num, by ring, one_pos, ?_⟩
    apply Prod.ext <;> simp [shift, rot, h1, h2]
  · have hpos : 0 < P.1 ^ 2 + P.2 ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm h0)
    obtain ⟨r, hr0, hr2⟩ : ∃ r : ℝ, 0 < r ∧ r ^ 2 = P.1 ^ 2 + P.2 ^ 2 :=
      ⟨√(P.1 ^ 2 + P.2 ^ 2), sqrt_pos.mpr hpos, sq_sqrt hpos.le⟩
    have hw : 0 < 1 + κ * r ^ 2 := by
      rw [hr2]
      exact mem_plane.mp hP
    have hrot : rot (P.1 / r) (-P.2 / r) P = (r, 0) := by
      apply Prod.ext
      · simp only [rot]
        field_simp
        linear_combination -hr2
      · simp only [rot]
        ring
    refine ⟨P.1 / r, -P.2 / r, -r, √(1 + κ * r ^ 2), ?_, ?_, sqrt_pos.mpr hw, ?_⟩
    · field_simp
      linear_combination -hr2
    · rw [sq_sqrt hw.le]
      ring
    · rw [hrot]
      apply Prod.ext <;> simp [shift]

/-- **`kleinAngle` is the only angle that the motions keep and that is the angle of Euclid at
`(0, 0)`.** Let `θ` give a number to three points of the plane. If turning and the motion along
the first axis keep `θ`, and at `(0, 0)` it is the angle of Euclid in Mathlib's sense, then it
is `kleinAngle`. The proof moves the vertex to `(0, 0)` with Theorem H15. -/
theorem kleinAngle_unique {κ : ℝ} (hκ : κ ≤ 0) (θ : ℝ × ℝ → ℝ × ℝ → ℝ × ℝ → ℝ)
    (hshift : ∀ a w : ℝ, w ^ 2 = 1 + κ * a ^ 2 → 0 < w → ∀ P A B : ℝ × ℝ,
      P ∈ plane κ → A ∈ plane κ → B ∈ plane κ →
        θ (shift κ a w P) (shift κ a w A) (shift κ a w B) = θ P A B)
    (hrot : ∀ c s : ℝ, c ^ 2 + s ^ 2 = 1 → ∀ P A B : ℝ × ℝ,
      P ∈ plane κ → A ∈ plane κ → B ∈ plane κ →
        θ (rot c s P) (rot c s A) (rot c s B) = θ P A B)
    (hcentre : ∀ A B : ℝ × ℝ, A ∈ plane κ → B ∈ plane κ →
      θ (0, 0) A B
        = InnerProductGeometry.angle (!₂[A.1, A.2] : EuclideanSpace ℝ (Fin 2)) !₂[B.1, B.2])
    {P A B : ℝ × ℝ} (hP : P ∈ plane κ) (hA : A ∈ plane κ) (hB : B ∈ plane κ) :
    θ P A B = kleinAngle κ P A B := by
  obtain ⟨c, s, a, w, hcs, hw, hw0, hPc⟩ := exists_motion_to_centre hP
  have hr : ∀ X : ℝ × ℝ, X ∈ plane κ → rot c s X ∈ plane κ :=
    fun X hX => (rot_mem_plane hcs).mpr hX
  have hm : ∀ X : ℝ × ℝ, X ∈ plane κ → shift κ a w (rot c s X) ∈ plane κ :=
    fun X hX => shift_mem_plane hκ hw hw0.ne' (hr X hX)
  calc θ P A B = θ (rot c s P) (rot c s A) (rot c s B) := (hrot c s hcs P A B hP hA hB).symm
    _ = θ (shift κ a w (rot c s P)) (shift κ a w (rot c s A)) (shift κ a w (rot c s B)) :=
      (hshift a w hw hw0 _ _ _ (hr P hP) (hr A hA) (hr B hB)).symm
    _ = θ (0, 0) (shift κ a w (rot c s A)) (shift κ a w (rot c s B)) := by rw [hPc]
    _ = kleinAngle κ (0, 0) (shift κ a w (rot c s A)) (shift κ a w (rot c s B)) := by
      rw [hcentre _ _ (hm A hA) (hm B hB), kleinAngle_centre]
    _ = kleinAngle κ (shift κ a w (rot c s P)) (shift κ a w (rot c s A))
          (shift κ a w (rot c s B)) := by rw [hPc]
    _ = kleinAngle κ (rot c s P) (rot c s A) (rot c s B) :=
      shift_kleinAngle hκ hw hw0.ne' (hr P hP) (hr A hA) (hr B hB)
    _ = kleinAngle κ P A B := rot_kleinAngle hcs κ P A B

end Angles

end HyperbolicPlane

end ParallelPostulate

/-!
# Klein's metric

`kleinMetric` is the metric of Klein's model, as the books write it. The two motions keep it:
moved by the derivative of a motion, in Mathlib's sense, two directions have the metric they had
before (Theorem H16). `kleinAngle` is the angle of this metric.

## Contents

* Theorem H16, Klein's metric, and the motions keep it: `kleinMetric`, `kleinMetric_zero_bound`,
  `kleinMetric_sub`, `kleinMetric_pos`, `shiftDeriv`, `shift_kleinMetric`, `rot_kleinMetric`,
  `shift_differentiableAt`, `shift_hasLineDerivAt`, `fderiv_shift`, `fderiv_rot`,
  `shift_kleinMetric_fderiv`, `rot_kleinMetric_fderiv`, `kleinAngle_eq_metric`
* a step of the proofs: `kleinMetric_aux`
-/

namespace ParallelPostulate

namespace HyperbolicPlane

open Pairs

/-! ## The metric -/

section MetricAlgebra

variable {K : Type*} [Field K]

/-- **Klein's metric**, under the bound `κ`: at the pair `P`, of the directions `u` and `v`.
It is the metric of Klein's model as the books write it: under the bound `-1`,
`ds² = (|dx|² (1 - |x|²) + (x · dx)²) / (1 - |x|²)²`. With the bound 0 it is the inner product
of Euclid. -/
@[expose] def kleinMetric (κ : K) (P u v : K × K) : K :=
  (u.1 * v.1 + u.2 * v.2 + κ * cross P u * cross P v) / (1 + κ * (P.1 ^ 2 + P.2 ^ 2)) ^ 2

/-- With the bound 0 it is the inner product of Euclid, at every pair. -/
theorem kleinMetric_zero_bound (P u v : K × K) : kleinMetric 0 P u v = u.1 * v.1 + u.2 * v.2 := by
  simp [kleinMetric]

/-- On the directions from `P` to `A` and from `P` to `B`, it is the inner product at `P`,
divided by the square of the bound at `P`. -/
theorem kleinMetric_sub (κ : K) (P A B : K × K) :
    kleinMetric κ P (A - P) (B - P)
      = kleinInner κ P A B / (1 + κ * (P.1 ^ 2 + P.2 ^ 2)) ^ 2 := by
  simp only [kleinMetric, kleinInner, cross, Prod.fst_sub, Prod.snd_sub]
  ring

/-- **The derivative of the motion along the first axis** at the pair `P`, on the direction
`u`. That it is the derivative in Mathlib's sense is `fderiv_shift`. -/
@[expose] def shiftDeriv (κ a w : K) (P u : K × K) : K × K :=
  ((1 + κ * a ^ 2) * u.1 / (1 - κ * a * P.1) ^ 2,
    w * (κ * a * P.2 * u.1 + (1 - κ * a * P.1) * u.2) / (1 - κ * a * P.1) ^ 2)

/-- The algebra of the next theorem, with the divisions taken out. -/
theorem kleinMetric_aux (κ a w x y u1 u2 v1 v2 : K) (hw : w ^ 2 = 1 + κ * a ^ 2) :
    (1 + κ * a ^ 2) ^ 2 * (u1 * v1)
        + w ^ 2 * ((κ * a * y * u1 + (1 - κ * a * x) * u2)
          * (κ * a * y * v1 + (1 - κ * a * x) * v2))
        + κ * w ^ 2 * (((x + a) * u2 - y * u1) * ((x + a) * v2 - y * v1))
      = w ^ 4 * (u1 * v1 + u2 * v2 + κ * (x * u2 - y * u1) * (x * v2 - y * v1)) := by
  rw [show w ^ 4 = (w ^ 2) ^ 2 by ring, hw]
  ring

/-- **The motion along the first axis keeps Klein's metric.** At the pair to which it moves
`P`, the metric of the two directions to which its derivative moves `u` and `v` is the metric
of `u` and `v` at `P`. -/
theorem shift_kleinMetric {κ a w : K} (hw : w ^ 2 = 1 + κ * a ^ 2) (hw0 : w ≠ 0) {P : K × K}
    (hD : 1 - κ * a * P.1 ≠ 0) (hP : 1 + κ * (P.1 ^ 2 + P.2 ^ 2) ≠ 0) (u v : K × K) :
    kleinMetric κ (shift κ a w P) (shiftDeriv κ a w P u) (shiftDeriv κ a w P v)
      = kleinMetric κ P u v := by
  have h1 : ((shiftDeriv κ a w P u).1 * (shiftDeriv κ a w P v).1
        + (shiftDeriv κ a w P u).2 * (shiftDeriv κ a w P v).2
        + κ * cross (shift κ a w P) (shiftDeriv κ a w P u)
          * cross (shift κ a w P) (shiftDeriv κ a w P v)) * (1 - κ * a * P.1) ^ 4
      = (1 + κ * a ^ 2) ^ 2 * (u.1 * v.1)
        + w ^ 2 * ((κ * a * P.2 * u.1 + (1 - κ * a * P.1) * u.2)
          * (κ * a * P.2 * v.1 + (1 - κ * a * P.1) * v.2))
        + κ * w ^ 2 * (((P.1 + a) * u.2 - P.2 * u.1) * ((P.1 + a) * v.2 - P.2 * v.1)) := by
    simp only [shift, shiftDeriv, cross]
    field_simp
    ring
  have h2 : (shiftDeriv κ a w P u).1 * (shiftDeriv κ a w P v).1
        + (shiftDeriv κ a w P u).2 * (shiftDeriv κ a w P v).2
        + κ * cross (shift κ a w P) (shiftDeriv κ a w P u)
          * cross (shift κ a w P) (shiftDeriv κ a w P v)
      = w ^ 4 * (u.1 * v.1 + u.2 * v.2 + κ * cross P u * cross P v) / (1 - κ * a * P.1) ^ 4 := by
    rw [eq_div_iff (pow_ne_zero 4 hD), h1, kleinMetric_aux κ a w P.1 P.2 u.1 u.2 v.1 v.2 hw]
    simp only [cross]
  unfold kleinMetric
  rw [h2, shift_bound hw hD]
  field_simp

/-- **Turning keeps Klein's metric.** Turning is its own derivative. -/
theorem rot_kleinMetric {c s : K} (h : c ^ 2 + s ^ 2 = 1) (κ : K) (P u v : K × K) :
    kleinMetric κ (rot c s P) (rot c s u) (rot c s v) = kleinMetric κ P u v := by
  unfold kleinMetric
  rw [rot_bound h]
  congr 1
  simp only [rot, cross]
  linear_combination (u.1 * v.1 + u.2 * v.2
    + κ * (P.1 * u.2 - P.2 * u.1) * (P.1 * v.2 - P.2 * v.1) * (c ^ 2 + s ^ 2 + 1)) * h

end MetricAlgebra

section MetricOrder

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- **At a point of the plane Klein's metric is positive** on every direction that is not
zero. -/
theorem kleinMetric_pos {κ : K} {P u : K × K} (hP : P ∈ plane κ) (hu : u ≠ 0) :
    0 < kleinMetric κ P u u := by
  have hA : P + u ≠ P := fun h => hu (add_eq_left.mp h)
  have e : kleinMetric κ P u u = kleinMetric κ P (P + u - P) (P + u - P) := by
    rw [add_sub_cancel_left]
  rw [e, kleinMetric_sub]
  exact div_pos (kleinInner_self_pos hP hA) (pow_pos (mem_plane.mp hP) 2)

end MetricOrder

/-! ## The motions keep Klein's metric

With the real numbers for numbers, the derivatives of the two motions are derivatives in
Mathlib's sense, and the motions keep Klein's metric. -/

section Metric

open Real

/-- The motion along the first axis has a derivative wherever it is defined. -/
theorem shift_differentiableAt {κ a w : ℝ} {P : ℝ × ℝ} (hD : 1 - κ * a * P.1 ≠ 0) :
    DifferentiableAt ℝ (shift κ a w) P := by
  unfold shift
  simp only [div_eq_mul_inv]
  fun_prop (disch := exact hD)

/-- Along the direction `u` from `P`, the motion along the first axis has the derivative
`shiftDeriv`. -/
theorem shift_hasLineDerivAt {κ a w : ℝ} {P : ℝ × ℝ} (hD : 1 - κ * a * P.1 ≠ 0) (u : ℝ × ℝ) :
    HasLineDerivAt ℝ (shift κ a w) (shiftDeriv κ a w P u) P u := by
  have e : (fun t : ℝ => shift κ a w (P + t • u)) = fun t : ℝ =>
      ((P.1 + t * u.1 + a) / (1 - κ * a * (P.1 + t * u.1)),
        w * (P.2 + t * u.2) / (1 - κ * a * (P.1 + t * u.1))) := by
    funext t
    simp [shift]
  have hx : HasDerivAt (fun t : ℝ => P.1 + t * u.1) u.1 0 := by
    simpa using ((hasDerivAt_id' (0 : ℝ)).mul_const u.1).const_add P.1
  have hy : HasDerivAt (fun t : ℝ => P.2 + t * u.2) u.2 0 := by
    simpa using ((hasDerivAt_id' (0 : ℝ)).mul_const u.2).const_add P.2
  have hd : HasDerivAt (fun t : ℝ => 1 - κ * a * (P.1 + t * u.1)) (-(κ * a * u.1)) 0 :=
    (hx.const_mul (κ * a)).const_sub 1
  have hD0 : 1 - κ * a * (P.1 + 0 * u.1) ≠ 0 := by simpa using hD
  have h := ((hx.add_const a).div hd hD0).prodMk ((hy.const_mul w).div hd hD0)
  unfold HasLineDerivAt
  rw [e]
  convert h using 1
  simp only [shiftDeriv, zero_mul, add_zero]
  apply Prod.ext
  · field_simp
    ring
  · field_simp
    ring

/-- **`shiftDeriv` is the derivative of the motion along the first axis**, in Mathlib's
sense. -/
theorem fderiv_shift {κ a w : ℝ} {P : ℝ × ℝ} (hD : 1 - κ * a * P.1 ≠ 0) (u : ℝ × ℝ) :
    fderiv ℝ (shift κ a w) P u = shiftDeriv κ a w P u := by
  rw [← (shift_differentiableAt hD).lineDeriv_eq_fderiv]
  exact (shift_hasLineDerivAt hD u).lineDeriv

/-- **Turning is its own derivative**, in Mathlib's sense. -/
theorem fderiv_rot (c s : ℝ) (P u : ℝ × ℝ) : fderiv ℝ (rot c s) P u = rot c s u := by
  have hdiff : DifferentiableAt ℝ (rot c s) P := by
    unfold rot
    fun_prop
  have e : (fun t : ℝ => rot c s (P + t • u)) = fun t : ℝ =>
      (c * (P.1 + t * u.1) - s * (P.2 + t * u.2), s * (P.1 + t * u.1) + c * (P.2 + t * u.2)) := by
    funext t
    simp [rot]
  have hx : HasDerivAt (fun t : ℝ => P.1 + t * u.1) u.1 0 := by
    simpa using ((hasDerivAt_id' (0 : ℝ)).mul_const u.1).const_add P.1
  have hy : HasDerivAt (fun t : ℝ => P.2 + t * u.2) u.2 0 := by
    simpa using ((hasDerivAt_id' (0 : ℝ)).mul_const u.2).const_add P.2
  have h : HasLineDerivAt ℝ (rot c s) (rot c s u) P u := by
    unfold HasLineDerivAt
    rw [e]
    exact ((hx.const_mul c).sub (hy.const_mul s)).prodMk ((hx.const_mul s).add (hy.const_mul c))
  rw [← hdiff.lineDeriv_eq_fderiv]
  exact h.lineDeriv

/-- **Theorem H16. The motion along the first axis keeps Klein's metric.** At every point of
the plane, the metric of two directions after the motion, moved by the derivative of the
motion in Mathlib's sense, is their metric before it. -/
theorem shift_kleinMetric_fderiv {κ a w : ℝ} (hκ : κ ≤ 0) (hw : w ^ 2 = 1 + κ * a ^ 2)
    (hw0 : w ≠ 0) {P : ℝ × ℝ} (hP : P ∈ plane κ) (u v : ℝ × ℝ) :
    kleinMetric κ (shift κ a w P) (fderiv ℝ (shift κ a w) P u) (fderiv ℝ (shift κ a w) P v)
      = kleinMetric κ P u v := by
  have hw2 : 0 < w ^ 2 := lt_of_le_of_ne (sq_nonneg w) (pow_ne_zero 2 hw0).symm
  have hD := (shift_den_pos hκ (hw ▸ hw2) hP).ne'
  rw [fderiv_shift hD, fderiv_shift hD]
  exact shift_kleinMetric hw hw0 hD (mem_plane.mp hP).ne' u v

/-- **Theorem H16. Turning keeps Klein's metric.** -/
theorem rot_kleinMetric_fderiv {c s : ℝ} (h : c ^ 2 + s ^ 2 = 1) (κ : ℝ) (P u v : ℝ × ℝ) :
    kleinMetric κ (rot c s P) (fderiv ℝ (rot c s) P u) (fderiv ℝ (rot c s) P v)
      = kleinMetric κ P u v := by
  rw [fderiv_rot, fderiv_rot]
  exact rot_kleinMetric h κ P u v

/-- **`kleinAngle` is the angle of Klein's metric.** At a point of the plane, the angle
between the directions to `A` and to `B` is made from `kleinMetric` as Mathlib makes the angle
of Euclid from the inner product. -/
theorem kleinAngle_eq_metric {κ : ℝ} {P : ℝ × ℝ} (hP : P ∈ plane κ) (A B : ℝ × ℝ) :
    kleinAngle κ P A B = arccos (kleinMetric κ P (A - P) (B - P)
      / (√(kleinMetric κ P (A - P) (A - P)) * √(kleinMetric κ P (B - P) (B - P)))) := by
  have hm : 0 < 1 / (1 + κ * (P.1 ^ 2 + P.2 ^ 2)) ^ 2 :=
    one_div_pos.mpr (pow_pos (mem_plane.mp hP) 2)
  have e1 : kleinMetric κ P (A - P) (B - P)
      = 1 / (1 + κ * (P.1 ^ 2 + P.2 ^ 2)) ^ 2 * 1 * 1 * kleinInner κ P A B := by
    rw [kleinMetric_sub]
    ring
  have e2 : kleinMetric κ P (A - P) (A - P)
      = 1 / (1 + κ * (P.1 ^ 2 + P.2 ^ 2)) ^ 2 * 1 ^ 2 * kleinInner κ P A A := by
    rw [kleinMetric_sub]
    ring
  have e3 : kleinMetric κ P (B - P) (B - P)
      = 1 / (1 + κ * (P.1 ^ 2 + P.2 ^ 2)) ^ 2 * 1 ^ 2 * kleinInner κ P B B := by
    rw [kleinMetric_sub]
    ring
  rw [kleinAngle, e1, e2, e3, kleinAngle_aux hm (by norm_num : (0 : ℝ) < 1 * 1)]

end Metric

end HyperbolicPlane

end ParallelPostulate

/-!
# The curvature of Klein's metric

`gaussCurvature` is Brioschi's coordinate formula, with Mathlib's derivatives along the two axes.
For Klein's metric it is `κ`
at every point of the plane, under every bound (Theorem H17); for the upper half plane of
Poincaré it is `-1`, a check of the formula.

## Contents

* Theorem H17, the curvature of Klein's metric is `κ`: `partialX`, `partialY`, `gaussCurvature`,
  `kleinE`, `kleinF`, `kleinG`, `kleinMetric_coords`, `kleinMetric_curvature`,
  `halfPlane_curvature`
* derivatives and determinants: `hasDerivAt_cubic`, `hasDerivAt_div_sq`, `hasDerivAt_div_cube`,
  `det_three`
-/

namespace ParallelPostulate

namespace HyperbolicPlane

open Pairs

/-! ## The curvature of Klein's metric

The curvature here is Brioschi's coordinate formula, with Mathlib's derivatives along the two
axes. -/

section Curvature

open Filter Topology

/-- The derivative of `f` along the first axis at `p`. -/
@[expose] noncomputable def partialX (f : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  deriv (fun t => f (t, p.2)) p.1

/-- The derivative of `f` along the second axis at `p`. -/
@[expose] noncomputable def partialY (f : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  deriv (fun t => f (p.1, t)) p.2

/-- **The curvature of a metric**, `E dx² + 2 F dx dy + G dy²`, at `p`, by Brioschi's formula,
with the derivatives of Mathlib. -/
@[expose] noncomputable def gaussCurvature (E F G : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  (Matrix.det !![-partialY (partialY E) p / 2 + partialX (partialY F) p
          - partialX (partialX G) p / 2, partialX E p / 2, partialX F p - partialY E p / 2;
        partialY F p - partialX G p / 2, E p, F p;
        partialY G p / 2, F p, G p]
    - Matrix.det !![0, partialY E p / 2, partialX G p / 2;
        partialY E p / 2, E p, F p;
        partialX G p / 2, F p, G p]) / (E p * G p - F p ^ 2) ^ 2

/-- The coefficient of `dx²` in Klein's metric. -/
@[expose] noncomputable def kleinE (κ : ℝ) (p : ℝ × ℝ) : ℝ :=
  (1 + κ * p.2 ^ 2) / (1 + κ * (p.1 ^ 2 + p.2 ^ 2)) ^ 2
/-- The coefficient of `dx dy` in Klein's metric, taken twice. -/
@[expose] noncomputable def kleinF (κ : ℝ) (p : ℝ × ℝ) : ℝ :=
  -κ * p.1 * p.2 / (1 + κ * (p.1 ^ 2 + p.2 ^ 2)) ^ 2
/-- The coefficient of `dy²` in Klein's metric. -/
@[expose] noncomputable def kleinG (κ : ℝ) (p : ℝ × ℝ) : ℝ :=
  (1 + κ * p.1 ^ 2) / (1 + κ * (p.1 ^ 2 + p.2 ^ 2)) ^ 2

/-- **Klein's metric is `E dx² + 2 F dx dy + G dy²`**, with `kleinE`, `kleinF` and `kleinG`. -/
theorem kleinMetric_coords (κ : ℝ) (p u v : ℝ × ℝ) :
    kleinMetric κ p u v
      = kleinE κ p * u.1 * v.1 + kleinF κ p * (u.1 * v.2 + u.2 * v.1) + kleinG κ p * u.2 * v.2 := by
  simp only [kleinMetric, kleinE, kleinF, kleinG, cross]
  ring

/-- The derivative of a polynomial of degree at most 3. -/
theorem hasDerivAt_cubic (c0 c1 c2 c3 : ℝ) {f : ℝ → ℝ}
    (hf : ∀ s, f s = c0 + c1 * s + c2 * s ^ 2 + c3 * s ^ 3) (t : ℝ) :
    HasDerivAt f (c1 + 2 * c2 * t + 3 * c3 * t ^ 2) t := by
  have e : f = fun s => c0 + c1 * s + c2 * s ^ 2 + c3 * s ^ 3 := funext hf
  subst e
  have h1 : HasDerivAt (fun s : ℝ => c1 * s) (c1 * 1) t :=
    HasDerivAt.const_mul c1 (hasDerivAt_id' t)
  have h2 : HasDerivAt (fun s : ℝ => c2 * s ^ 2) (c2 * (↑2 * t ^ (2 - 1))) t :=
    HasDerivAt.const_mul c2 (hasDerivAt_pow 2 t)
  have h3 : HasDerivAt (fun s : ℝ => c3 * s ^ 3) (c3 * (↑3 * t ^ (3 - 1))) t :=
    HasDerivAt.const_mul c3 (hasDerivAt_pow 3 t)
  have h := HasDerivAt.add (HasDerivAt.add (HasDerivAt.add (hasDerivAt_const t c0) h1) h2) h3
  exact HasDerivAt.congr_deriv h (by norm_num; ring)

/-- The derivative of a quotient by a square. -/
theorem hasDerivAt_div_sq {f b : ℝ → ℝ} {f' b' t : ℝ} (hf : HasDerivAt f f' t)
    (hb : HasDerivAt b b' t) (h : b t ≠ 0) :
    HasDerivAt (fun s => f s / b s ^ 2) ((f' * b t - 2 * f t * b') / b t ^ 3) t := by
  convert hf.div (hb.pow 2) (pow_ne_zero 2 h) using 1
  simp only [Pi.pow_apply]
  field_simp
  ring

/-- The derivative of a quotient by a cube. -/
theorem hasDerivAt_div_cube {f b : ℝ → ℝ} {f' b' t : ℝ} (hf : HasDerivAt f f' t)
    (hb : HasDerivAt b b' t) (h : b t ≠ 0) :
    HasDerivAt (fun s => f s / b s ^ 3) ((f' * b t - 3 * f t * b') / b t ^ 4) t := by
  convert hf.div (hb.pow 3) (pow_ne_zero 3 h) using 1
  simp only [Pi.pow_apply]
  field_simp
  ring

/-- The determinant of a 3 × 3 matrix. -/
theorem det_three (a b c d e f g h i : ℝ) :
    Matrix.det !![a, b, c; d, e, f; g, h, i]
      = a * e * i - a * f * h - b * d * i + b * f * g + c * d * h - c * e * g := by
  rw [Matrix.det_fin_three]
  simp

/-- **Theorem H17. The curvature of Klein's metric is `κ`**, at every point of the plane, and
under every bound: negative, 0 or positive. -/
theorem kleinMetric_curvature {κ : ℝ} {P : ℝ × ℝ} (hP : P ∈ plane κ) :
    gaussCurvature (kleinE κ) (kleinF κ) (kleinG κ) P = κ := by
  obtain ⟨x, y⟩ := P
  replace hP := mem_plane.mp hP
  simp only at hP
  have hB : 1 + κ * (x ^ 2 + y ^ 2) ≠ 0 := hP.ne'
  have bX : ∀ c t : ℝ,
      HasDerivAt (fun s => 1 + κ * (s ^ 2 + c ^ 2)) (0 + 2 * κ * t + 3 * 0 * t ^ 2) t :=
    fun c t => hasDerivAt_cubic (1 + κ * c ^ 2) 0 κ 0 (fun s => by ring) t
  have bY : ∀ c t : ℝ,
      HasDerivAt (fun s => 1 + κ * (c ^ 2 + s ^ 2)) (0 + 2 * κ * t + 3 * 0 * t ^ 2) t :=
    fun c t => hasDerivAt_cubic (1 + κ * c ^ 2) 0 κ 0 (fun s => by ring) t
  have hEx : partialX (kleinE κ) (x, y)
      = -4 * κ * x * (1 + κ * y ^ 2) / (1 + κ * (x ^ 2 + y ^ 2)) ^ 3 := by
    unfold partialX kleinE
    refine ((hasDerivAt_div_sq (f := fun _ => 1 + κ * y ^ 2)
      (hasDerivAt_cubic (1 + κ * y ^ 2) 0 0 0 (fun s => by ring) x) (bX y x) hB).deriv).trans ?_
    field_simp
    ring
  have hEy : partialY (kleinE κ) (x, y)
      = 2 * κ * y * (κ * x ^ 2 - κ * y ^ 2 - 1) / (1 + κ * (x ^ 2 + y ^ 2)) ^ 3 := by
    unfold partialY kleinE
    refine ((hasDerivAt_div_sq (f := fun s => 1 + κ * s ^ 2)
      (hasDerivAt_cubic 1 0 κ 0 (fun s => by ring) y) (bY x y) hB).deriv).trans ?_
    field_simp
    ring
  have hFx : partialX (kleinF κ) (x, y)
      = κ * y * (3 * κ * x ^ 2 - κ * y ^ 2 - 1) / (1 + κ * (x ^ 2 + y ^ 2)) ^ 3 := by
    unfold partialX kleinF
    refine ((hasDerivAt_div_sq (f := fun s => -κ * s * y)
      (hasDerivAt_cubic 0 (-κ * y) 0 0 (fun s => by ring) x) (bX y x) hB).deriv).trans ?_
    field_simp
    ring
  have hFy : partialY (kleinF κ) (x, y)
      = κ * x * (3 * κ * y ^ 2 - κ * x ^ 2 - 1) / (1 + κ * (x ^ 2 + y ^ 2)) ^ 3 := by
    unfold partialY kleinF
    refine ((hasDerivAt_div_sq (f := fun s => -κ * x * s)
      (hasDerivAt_cubic 0 (-κ * x) 0 0 (fun s => by ring) y) (bY x y) hB).deriv).trans ?_
    field_simp
    ring
  have hGx : partialX (kleinG κ) (x, y)
      = 2 * κ * x * (κ * y ^ 2 - κ * x ^ 2 - 1) / (1 + κ * (x ^ 2 + y ^ 2)) ^ 3 := by
    unfold partialX kleinG
    refine ((hasDerivAt_div_sq (f := fun s => 1 + κ * s ^ 2)
      (hasDerivAt_cubic 1 0 κ 0 (fun s => by ring) x) (bX y x) hB).deriv).trans ?_
    field_simp
    ring
  have hGy : partialY (kleinG κ) (x, y)
      = -4 * κ * y * (1 + κ * x ^ 2) / (1 + κ * (x ^ 2 + y ^ 2)) ^ 3 := by
    unfold partialY kleinG
    refine ((hasDerivAt_div_sq (f := fun _ => 1 + κ * x ^ 2)
      (hasDerivAt_cubic (1 + κ * x ^ 2) 0 0 0 (fun s => by ring) y) (bY x y) hB).deriv).trans ?_
    field_simp
    ring
  have nX : ∀ᶠ t in 𝓝 x, 1 + κ * (t ^ 2 + y ^ 2) ≠ 0 :=
    (show Continuous fun t : ℝ => 1 + κ * (t ^ 2 + y ^ 2) by fun_prop).continuousAt.eventually_ne hB
  have nY : ∀ᶠ t in 𝓝 y, 1 + κ * (x ^ 2 + t ^ 2) ≠ 0 :=
    (show Continuous fun t : ℝ => 1 + κ * (x ^ 2 + t ^ 2) by fun_prop).continuousAt.eventually_ne hB
  have hEyy : partialY (partialY (kleinE κ)) (x, y)
      = ((2 * κ ^ 2 * x ^ 2 - 2 * κ - 6 * κ ^ 2 * y ^ 2) * (1 + κ * (x ^ 2 + y ^ 2))
        - 6 * κ * y * ((2 * κ ^ 2 * x ^ 2 - 2 * κ) * y - 2 * κ ^ 2 * y ^ 3))
          / (1 + κ * (x ^ 2 + y ^ 2)) ^ 4 := by
    have e : (fun t => partialY (kleinE κ) (x, t)) =ᶠ[𝓝 y]
        fun t => ((2 * κ ^ 2 * x ^ 2 - 2 * κ) * t - 2 * κ ^ 2 * t ^ 3)
          / (1 + κ * (x ^ 2 + t ^ 2)) ^ 3 := by
      filter_upwards [nY] with t ht
      unfold partialY kleinE
      refine ((hasDerivAt_div_sq (f := fun s => 1 + κ * s ^ 2)
        (hasDerivAt_cubic 1 0 κ 0 (fun s => by ring) t) (bY x t) ht).deriv).trans ?_
      ring
    unfold partialY at e ⊢
    rw [e.deriv_eq]
    refine ((hasDerivAt_div_cube
      (hasDerivAt_cubic 0 (2 * κ ^ 2 * x ^ 2 - 2 * κ) 0 (-2 * κ ^ 2) (fun s => by ring) y)
      (bY x y) hB).deriv).trans ?_
    ring
  have hGxx : partialX (partialX (kleinG κ)) (x, y)
      = ((2 * κ ^ 2 * y ^ 2 - 2 * κ - 6 * κ ^ 2 * x ^ 2) * (1 + κ * (x ^ 2 + y ^ 2))
        - 6 * κ * x * ((2 * κ ^ 2 * y ^ 2 - 2 * κ) * x - 2 * κ ^ 2 * x ^ 3))
          / (1 + κ * (x ^ 2 + y ^ 2)) ^ 4 := by
    have e : (fun t => partialX (kleinG κ) (t, y)) =ᶠ[𝓝 x]
        fun t => ((2 * κ ^ 2 * y ^ 2 - 2 * κ) * t - 2 * κ ^ 2 * t ^ 3)
          / (1 + κ * (t ^ 2 + y ^ 2)) ^ 3 := by
      filter_upwards [nX] with t ht
      unfold partialX kleinG
      refine ((hasDerivAt_div_sq (f := fun s => 1 + κ * s ^ 2)
        (hasDerivAt_cubic 1 0 κ 0 (fun s => by ring) t) (bX y t) ht).deriv).trans ?_
      ring
    unfold partialX at e ⊢
    rw [e.deriv_eq]
    refine ((hasDerivAt_div_cube
      (hasDerivAt_cubic 0 (2 * κ ^ 2 * y ^ 2 - 2 * κ) 0 (-2 * κ ^ 2) (fun s => by ring) x)
      (bX y x) hB).deriv).trans ?_
    ring
  have hFxy : partialX (partialY (kleinF κ)) (x, y)
      = ((3 * κ ^ 2 * y ^ 2 - κ - 3 * κ ^ 2 * x ^ 2) * (1 + κ * (x ^ 2 + y ^ 2))
        - 6 * κ * x * ((3 * κ ^ 2 * y ^ 2 - κ) * x - κ ^ 2 * x ^ 3))
          / (1 + κ * (x ^ 2 + y ^ 2)) ^ 4 := by
    have e : (fun t => partialY (kleinF κ) (t, y)) =ᶠ[𝓝 x]
        fun t => ((3 * κ ^ 2 * y ^ 2 - κ) * t - κ ^ 2 * t ^ 3)
          / (1 + κ * (t ^ 2 + y ^ 2)) ^ 3 := by
      filter_upwards [nX] with t ht
      unfold partialY kleinF
      refine ((hasDerivAt_div_sq (f := fun s => -κ * t * s)
        (hasDerivAt_cubic 0 (-κ * t) 0 0 (fun s => by ring) y) (bY t y) ht).deriv).trans ?_
      ring
    unfold partialX
    rw [e.deriv_eq]
    refine ((hasDerivAt_div_cube
      (hasDerivAt_cubic 0 (3 * κ ^ 2 * y ^ 2 - κ) 0 (-κ ^ 2) (fun s => by ring) x)
      (bX y x) hB).deriv).trans ?_
    ring
  have hdet : kleinE κ (x, y) * kleinG κ (x, y) - kleinF κ (x, y) ^ 2
      = 1 / (1 + κ * (x ^ 2 + y ^ 2)) ^ 3 := by
    simp only [kleinE, kleinF, kleinG]
    field_simp
    ring
  unfold gaussCurvature
  rw [hdet, hEx, hEy, hFx, hFy, hGx, hGy, hEyy, hGxx, hFxy, det_three, det_three]
  simp only [kleinE, kleinF, kleinG]
  field_simp
  ring

/-- **A check of `gaussCurvature`: the upper half plane of Poincaré has the curvature `-1`.**
Its metric is `(dx² + dy²) / y²`, and its curvature is known to be `-1`. -/
theorem halfPlane_curvature {p : ℝ × ℝ} (hp : 0 < p.2) :
    gaussCurvature (fun q => 1 / q.2 ^ 2) (fun _ => 0) (fun q => 1 / q.2 ^ 2) p = -1 := by
  obtain ⟨x, y⟩ := p
  simp only at hp
  have hEx : partialX (fun q : ℝ × ℝ => 1 / q.2 ^ 2) (x, y) = 0 := by
    simp [partialX]
  have hEy : partialY (fun q : ℝ × ℝ => 1 / q.2 ^ 2) (x, y) = -2 / y ^ 3 := by
    unfold partialY
    refine ((hasDerivAt_div_sq (f := fun _ => 1) (hasDerivAt_const y 1) (hasDerivAt_id' y)
      hp.ne').deriv).trans ?_
    ring
  have hExx : partialX (partialX (fun q : ℝ × ℝ => 1 / q.2 ^ 2)) (x, y) = 0 := by
    simp [partialX]
  have hEyy : partialY (partialY (fun q : ℝ × ℝ => 1 / q.2 ^ 2)) (x, y) = 6 / y ^ 4 := by
    have e : (fun t => partialY (fun q : ℝ × ℝ => 1 / q.2 ^ 2) (x, t)) =ᶠ[𝓝 y]
        fun t => -2 / t ^ 3 := by
      filter_upwards [eventually_gt_nhds hp] with t ht
      unfold partialY
      refine ((hasDerivAt_div_sq (f := fun _ => 1) (hasDerivAt_const t 1) (hasDerivAt_id' t)
        ht.ne').deriv).trans ?_
      ring
    unfold partialY at e ⊢
    rw [e.deriv_eq]
    refine ((hasDerivAt_div_cube (f := fun _ => -2) (hasDerivAt_const y (-2)) (hasDerivAt_id' y)
      hp.ne').deriv).trans ?_
    ring
  have hF : ∀ q : ℝ × ℝ, partialX (fun _ : ℝ × ℝ => (0 : ℝ)) q = 0 ∧
      partialY (fun _ : ℝ × ℝ => (0 : ℝ)) q = 0 := fun q => by simp [partialX, partialY]
  have hFxy : partialX (partialY (fun _ : ℝ × ℝ => (0 : ℝ))) (x, y) = 0 := by
    simp [partialX, partialY]
  unfold gaussCurvature
  rw [hEx, hEy, hExx, hEyy, (hF _).1, (hF _).2, hFxy, det_three, det_three]
  field_simp
  ring

end Curvature

end HyperbolicPlane

end ParallelPostulate

/-!
# Klein's distance

`kleinDist` is the least length of a path between two points, the length measured with Klein's
metric: the infimum of the lengths of the maps of `[0, 1]` into the plane with a continuous
derivative. The two motions keep it, and under a negative bound `apart` is
`sinh² (√(-κ) d) / (-κ)`, where `d` is the distance (Theorem H18).

## Contents

* Theorem H18, Klein's distance, and `apart` as a function of it: `IsKleinPath`, `kleinLength`,
  `kleinDist`, `kleinLength_nonneg`, `segment_isKleinPath`, `kleinDist_nonempty`,
  `kleinDist_bddBelow`, `kleinLength_integrand_continuousOn`, `isKleinPath_map`,
  `kleinDist_map_le`, `shift_contDiffOn`, `shift_kleinDist`, `rot_kleinDist`, `axisDist`,
  `axisDist_zero`, `hasDerivAt_axisDist`, `axis_le_metric`, `axisDist_sub_le_kleinLength`,
  `axis_isKleinPath`, `axis_kleinLength`, `kleinDist_axis`, `exists_rot_to_axis`,
  `kleinDist_eq_arsinh`, `apart_eq_sinh_kleinDist`
-/

namespace ParallelPostulate

namespace HyperbolicPlane

open Pairs

/-! ## Klein's distance

Klein's distance is the least length of a path, the length measured with Klein's metric. Under
a negative bound, `apart` is a function of it. -/

section Distance

open Set Filter Topology Real

/-- **A path of the plane from `P` to `Q`**: a map of `[0, 1]` into the plane, with a continuous
derivative, from `P` to `Q`. -/
@[expose] def IsKleinPath (κ : ℝ) (γ : ℝ → ℝ × ℝ) (P Q : ℝ × ℝ) : Prop :=
  ContDiffOn ℝ 1 γ (Icc 0 1) ∧ MapsTo γ (Icc 0 1) (plane κ) ∧ γ 0 = P ∧ γ 1 = Q

/-- **The length of a path** in Klein's metric: the integral, over `[0, 1]`, of the square root
of the metric of its derivative. -/
@[expose] noncomputable def kleinLength (κ : ℝ) (γ : ℝ → ℝ × ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1,
    √(kleinMetric κ (γ t) (derivWithin γ (Icc 0 1) t) (derivWithin γ (Icc 0 1) t))

/-- **Klein's distance** between two points: the least length of a path from the one to the
other, as an infimum. -/
@[expose] noncomputable def kleinDist (κ : ℝ) (P Q : ℝ × ℝ) : ℝ :=
  sInf (kleinLength κ '' {γ | IsKleinPath κ γ P Q})

/-- A length is not negative. -/
theorem kleinLength_nonneg (κ : ℝ) (γ : ℝ → ℝ × ℝ) : 0 ≤ kleinLength κ γ :=
  intervalIntegral.integral_nonneg zero_le_one (fun _ _ => sqrt_nonneg _)

/-- The segment from `P` to `Q` is a path of the plane. -/
theorem segment_isKleinPath {κ : ℝ} {P Q : ℝ × ℝ} (hP : P ∈ plane κ) (hQ : Q ∈ plane κ) :
    IsKleinPath κ (Dim.mk P Q).pt P Q := by
  refine ⟨?_, fun t ht => plane_convex κ hP hQ ht.1 ht.2, Dim.pt_zero _, Dim.pt_one _⟩
  have : ContDiff ℝ 1 (Dim.mk P Q).pt := by
    unfold Dim.pt
    fun_prop
  exact this.contDiffOn

/-- Two points of the plane have a path between them. -/
theorem kleinDist_nonempty {κ : ℝ} {P Q : ℝ × ℝ} (hP : P ∈ plane κ) (hQ : Q ∈ plane κ) :
    (kleinLength κ '' {γ | IsKleinPath κ γ P Q}).Nonempty :=
  ⟨_, _, segment_isKleinPath hP hQ, rfl⟩

/-- The lengths are bounded below, by 0. -/
theorem kleinDist_bddBelow (κ : ℝ) (P Q : ℝ × ℝ) :
    BddBelow (kleinLength κ '' {γ | IsKleinPath κ γ P Q}) :=
  ⟨0, by rintro _ ⟨γ, -, rfl⟩; exact kleinLength_nonneg κ γ⟩

/-- The integrand of the length is continuous. -/
theorem kleinLength_integrand_continuousOn {κ : ℝ} {γ : ℝ → ℝ × ℝ} {P Q : ℝ × ℝ}
    (h : IsKleinPath κ γ P Q) :
    ContinuousOn (fun t => √(kleinMetric κ (γ t) (derivWithin γ (Icc 0 1) t)
      (derivWithin γ (Icc 0 1) t))) (Icc 0 1) := by
  have hγ : ContinuousOn γ (Icc 0 1) := h.1.continuousOn
  have hv : ContinuousOn (derivWithin γ (Icc 0 1)) (Icc 0 1) :=
    h.1.continuousOn_derivWithin uniqueDiffOn_Icc_zero_one le_rfl
  have hB : ∀ t ∈ Icc (0 : ℝ) 1, (1 + κ * ((γ t).1 ^ 2 + (γ t).2 ^ 2)) ^ 2 ≠ 0 :=
    fun t ht => pow_ne_zero 2 (mem_plane.mp (h.2.1 ht)).ne'
  unfold kleinMetric cross
  apply ContinuousOn.sqrt
  apply ContinuousOn.div _ _ hB
  · fun_prop
  · fun_prop

/-- **A motion that keeps the plane and Klein's metric keeps paths and their lengths.** -/
theorem isKleinPath_map {κ : ℝ} {M : ℝ × ℝ → ℝ × ℝ} (hM : ContDiffOn ℝ 1 M (plane κ))
    (hMp : MapsTo M (plane κ) (plane κ)) (hMd : ∀ p ∈ plane κ, DifferentiableAt ℝ M p)
    (hMg : ∀ p ∈ plane κ, ∀ v, kleinMetric κ (M p) (fderiv ℝ M p v) (fderiv ℝ M p v)
      = kleinMetric κ p v v)
    {γ : ℝ → ℝ × ℝ} {P Q : ℝ × ℝ} (h : IsKleinPath κ γ P Q) :
    IsKleinPath κ (M ∘ γ) (M P) (M Q) ∧ kleinLength κ (M ∘ γ) = kleinLength κ γ := by
  obtain ⟨hγ, hmaps, h0, h1⟩ := h
  refine ⟨⟨hM.comp hγ hmaps, hMp.comp hmaps, by simp [h0], by simp [h1]⟩, ?_⟩
  unfold kleinLength
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le zero_le_one] at ht
  have hd : derivWithin (M ∘ γ) (Icc 0 1) t = fderiv ℝ M (γ t) (derivWithin γ (Icc 0 1) t) :=
    ((hMd _ (hmaps ht)).hasFDerivAt.comp_hasDerivWithinAt t
      ((hγ.differentiableOn one_ne_zero t ht).hasDerivWithinAt)).derivWithin
      (uniqueDiffOn_Icc_zero_one t ht)
  simp only [Function.comp_apply, hd, hMg _ (hmaps ht)]

/-- **A motion that keeps the plane and Klein's metric does not make distances longer.** -/
theorem kleinDist_map_le {κ : ℝ} {M : ℝ × ℝ → ℝ × ℝ} (hM : ContDiffOn ℝ 1 M (plane κ))
    (hMp : MapsTo M (plane κ) (plane κ)) (hMd : ∀ p ∈ plane κ, DifferentiableAt ℝ M p)
    (hMg : ∀ p ∈ plane κ, ∀ v, kleinMetric κ (M p) (fderiv ℝ M p v) (fderiv ℝ M p v)
      = kleinMetric κ p v v)
    {P Q : ℝ × ℝ} (hP : P ∈ plane κ) (hQ : Q ∈ plane κ) :
    kleinDist κ (M P) (M Q) ≤ kleinDist κ P Q := by
  apply csInf_le_csInf (kleinDist_bddBelow κ _ _) (kleinDist_nonempty hP hQ)
  rintro _ ⟨γ, hγ, rfl⟩
  obtain ⟨hpath, hlen⟩ := isKleinPath_map hM hMp hMd hMg hγ
  exact ⟨M ∘ γ, hpath, hlen⟩

/-- The motion along the first axis has a continuous derivative on the plane. -/
theorem shift_contDiffOn {κ a w : ℝ} (hκ : κ ≤ 0) (ha : 0 < 1 + κ * a ^ 2) :
    ContDiffOn ℝ 1 (shift κ a w) (plane κ) := by
  unfold shift
  simp only [div_eq_mul_inv]
  have hD : ∀ p ∈ plane κ, 1 - κ * a * p.1 ≠ 0 := fun p hp => (shift_den_pos hκ ha hp).ne'
  apply ContDiffOn.prodMk
  · exact ContDiffOn.mul (by fun_prop) (ContDiffOn.inv (by fun_prop) hD)
  · exact ContDiffOn.mul (by fun_prop) (ContDiffOn.inv (by fun_prop) hD)

/-- **The motion along the first axis keeps Klein's distance.** -/
theorem shift_kleinDist {κ a w : ℝ} (hκ : κ ≤ 0) (hw : w ^ 2 = 1 + κ * a ^ 2) (hw0 : w ≠ 0)
    {P Q : ℝ × ℝ} (hP : P ∈ plane κ) (hQ : Q ∈ plane κ) :
    kleinDist κ (shift κ a w P) (shift κ a w Q) = kleinDist κ P Q := by
  have hw2 : 0 < w ^ 2 := lt_of_le_of_ne (sq_nonneg w) (pow_ne_zero 2 hw0).symm
  have ha : 0 < 1 + κ * a ^ 2 := hw ▸ hw2
  have hw' : w ^ 2 = 1 + κ * (-a) ^ 2 := by rw [hw]; ring
  have ha' : 0 < 1 + κ * (-a) ^ 2 := hw' ▸ hw2
  have key : ∀ b : ℝ, w ^ 2 = 1 + κ * b ^ 2 → 0 < 1 + κ * b ^ 2 → ∀ X Y : ℝ × ℝ,
      X ∈ plane κ → Y ∈ plane κ → kleinDist κ (shift κ b w X) (shift κ b w Y) ≤ kleinDist κ X Y :=
    fun b hb hb' X Y hX hY => kleinDist_map_le (shift_contDiffOn hκ hb')
      (fun p hp => shift_mem_plane hκ hb hw0 hp)
      (fun p hp => shift_differentiableAt (shift_den_pos hκ hb' hp).ne')
      (fun p hp v => shift_kleinMetric_fderiv hκ hb hw0 hp v v) hX hY
  apply le_antisymm (key a hw ha P Q hP hQ)
  have h := key (-a) hw' ha' _ _ (shift_mem_plane hκ hw hw0 hP) (shift_mem_plane hκ hw hw0 hQ)
  rwa [shift_neg_shift hκ hw hw0 hP, shift_neg_shift hκ hw hw0 hQ] at h

/-- **Turning keeps Klein's distance.** -/
theorem rot_kleinDist {κ c s : ℝ} (h : c ^ 2 + s ^ 2 = 1) {P Q : ℝ × ℝ} (hP : P ∈ plane κ)
    (hQ : Q ∈ plane κ) : kleinDist κ (rot c s P) (rot c s Q) = kleinDist κ P Q := by
  have h' : c ^ 2 + (-s) ^ 2 = 1 := by rw [← h]; ring
  have key : ∀ s' : ℝ, c ^ 2 + s' ^ 2 = 1 → ∀ X Y : ℝ × ℝ,
      X ∈ plane κ → Y ∈ plane κ → kleinDist κ (rot c s' X) (rot c s' Y) ≤ kleinDist κ X Y := by
    intro s' hs' X Y hX hY
    have hrot : ContDiff ℝ 1 (rot c s') := by
      unfold rot
      fun_prop
    exact kleinDist_map_le hrot.contDiffOn (fun p hp => (rot_mem_plane hs').mpr hp)
      (fun p _ => hrot.differentiable one_ne_zero p)
      (fun p _ v => rot_kleinMetric_fderiv hs' κ p v v) hX hY
  apply le_antisymm (key s h P Q hP hQ)
  have hh := key (-s) h' _ _ ((rot_mem_plane h).mpr hP) ((rot_mem_plane h).mpr hQ)
  rwa [rot_rot_neg h, rot_rot_neg h] at hh

/-- Klein's distance from `(0, 0)` to the number `x` of the first axis, under a negative
bound. -/
@[expose] noncomputable def axisDist (κ x : ℝ) : ℝ := arsinh (√(-κ) * x / √(1 + κ * x ^ 2)) / √(-κ)

/-- The distance from `(0, 0)` to itself is 0. -/
theorem axisDist_zero (κ : ℝ) : axisDist κ 0 = 0 := by
  simp [axisDist]

/-- The derivative of `axisDist` is `1 / (1 + κ x²)`. -/
theorem hasDerivAt_axisDist {κ x : ℝ} (hκ : κ < 0) (hx : 0 < 1 + κ * x ^ 2) :
    HasDerivAt (axisDist κ) (1 / (1 + κ * x ^ 2)) x := by
  have hs : 0 < √(-κ) := sqrt_pos.mpr (neg_pos.mpr hκ)
  have hs2 : √(-κ) ^ 2 = -κ := sq_sqrt (neg_nonneg.mpr hκ.le)
  have hq : 0 < √(1 + κ * x ^ 2) := sqrt_pos.mpr hx
  have hq2 : √(1 + κ * x ^ 2) ^ 2 = 1 + κ * x ^ 2 := sq_sqrt hx.le
  have hb : HasDerivAt (fun y : ℝ => 1 + κ * y ^ 2) (2 * κ * x) x := by
    have := ((hasDerivAt_pow 2 x).const_mul κ).const_add 1
    convert this using 1
    norm_num
    ring
  have hu := ((hasDerivAt_id' x).const_mul (√(-κ))).fun_div (hb.sqrt hx.ne') hq.ne'
  have ha := hu.arsinh.div_const (√(-κ))
  have h1u : 1 + (√(-κ) * x / √(1 + κ * x ^ 2)) ^ 2 = (1 / √(1 + κ * x ^ 2)) ^ 2 := by
    rw [div_pow, div_pow, mul_pow, hs2, hq2]
    field_simp
    ring
  have hsq1 : √(1 + (√(-κ) * x / √(1 + κ * x ^ 2)) ^ 2) = 1 / √(1 + κ * x ^ 2) := by
    rw [h1u, sqrt_sq (by positivity)]
  unfold axisDist
  convert ha using 1
  rw [hsq1, smul_eq_mul]
  field_simp
  rw [hq2]
  ring

/-- **Along the first axis, a direction is no longer in Klein's metric than its first
entry, divided by `1 + κ x²`.** The proof is the identity
`c N - B v₁² = (κ x y v₁ - c v₂)²`, where `c = 1 + κ x²`, `B` is the bound at the point and
`N` is the numerator of the metric. -/
theorem axis_le_metric {κ : ℝ} (hκ : κ ≤ 0) {p : ℝ × ℝ} (hp : p ∈ plane κ) (v : ℝ × ℝ) :
    1 / (1 + κ * p.1 ^ 2) * v.1 ≤ √(kleinMetric κ p v v) := by
  have hB := mem_plane.mp hp
  have hBc : 1 + κ * (p.1 ^ 2 + p.2 ^ 2) ≤ 1 + κ * p.1 ^ 2 := by
    nlinarith [mul_nonpos_of_nonpos_of_nonneg hκ (sq_nonneg p.2)]
  have hc : 0 < 1 + κ * p.1 ^ 2 := lt_of_lt_of_le hB hBc
  have key : (1 + κ * p.1 ^ 2) * (v.1 * v.1 + v.2 * v.2 + κ * cross p v * cross p v)
      - (1 + κ * (p.1 ^ 2 + p.2 ^ 2)) * v.1 ^ 2
      = (κ * p.1 * p.2 * v.1 - (1 + κ * p.1 ^ 2) * v.2) ^ 2 := by
    simp only [cross]
    ring
  have hcN : (1 + κ * (p.1 ^ 2 + p.2 ^ 2)) * v.1 ^ 2
      ≤ (1 + κ * p.1 ^ 2) * (v.1 * v.1 + v.2 * v.2 + κ * cross p v * cross p v) := by
    nlinarith [sq_nonneg (κ * p.1 * p.2 * v.1 - (1 + κ * p.1 ^ 2) * v.2)]
  have hN : 0 ≤ (1 + κ * p.1 ^ 2) * (v.1 * v.1 + v.2 * v.2 + κ * cross p v * cross p v) :=
    le_trans (mul_nonneg hB.le (sq_nonneg _)) hcN
  have hsq : (1 / (1 + κ * p.1 ^ 2) * v.1) ^ 2 ≤ kleinMetric κ p v v := by
    unfold kleinMetric
    rw [show (1 / (1 + κ * p.1 ^ 2) * v.1) ^ 2 = v.1 ^ 2 / (1 + κ * p.1 ^ 2) ^ 2 by
        rw [mul_pow, div_pow, one_pow, one_div, inv_mul_eq_div],
      div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hcN hB.le, mul_le_mul_of_nonneg_right hBc hN]
  exact (le_abs_self _).trans (abs_le_sqrt hsq)

/-- **Every path is at least as long as the distance along the first axis between the first
entries of its ends.** -/
theorem axisDist_sub_le_kleinLength {κ : ℝ} (hκ : κ < 0) {γ : ℝ → ℝ × ℝ} {P Q : ℝ × ℝ}
    (h : IsKleinPath κ γ P Q) : axisDist κ Q.1 - axisDist κ P.1 ≤ kleinLength κ γ := by
  obtain ⟨hγ, hmaps, h0, h1⟩ := h
  have hx : ∀ t ∈ Icc (0 : ℝ) 1, 0 < 1 + κ * (γ t).1 ^ 2 := fun t ht => by
    have := mem_plane.mp (hmaps ht)
    nlinarith [mul_nonpos_of_nonpos_of_nonneg hκ.le (sq_nonneg (γ t).2)]
  have hcont : ContinuousOn (fun t => axisDist κ (γ t).1) (Icc 0 1) := fun t ht =>
    ContinuousAt.comp_continuousWithinAt (f := fun t => (γ t).1)
      (hasDerivAt_axisDist hκ (hx t ht)).continuousAt (hγ.continuousOn t ht).fst
  have hderiv : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivWithinAt (fun t => axisDist κ (γ t).1)
      (1 / (1 + κ * (γ t).1 ^ 2) * (derivWithin γ (Icc 0 1) t).1) (Ioi t) t := by
    intro t ht
    have hmem : Icc (0 : ℝ) 1 ∈ 𝓝 t := Icc_mem_nhds ht.1 ht.2
    have hd : HasDerivAt γ (derivWithin γ (Icc 0 1) t) t := by
      rw [derivWithin_of_mem_nhds hmem]
      exact ((hγ.differentiableOn one_ne_zero t (Ioo_subset_Icc_self ht)).differentiableAt
        hmem).hasDerivAt
    have hd1 : HasDerivAt (fun t => (γ t).1) (derivWithin γ (Icc 0 1) t).1 t := by
      have := (hasFDerivAt_fst (𝕜 := ℝ) (p := γ t)).comp_hasDerivAt t hd
      exact this
    exact ((hasDerivAt_axisDist hκ (hx t (Ioo_subset_Icc_self ht))).comp t hd1).hasDerivWithinAt
  have hint := (kleinLength_integrand_continuousOn ⟨hγ, hmaps, h0, h1⟩).integrableOn_Icc
    (μ := MeasureTheory.volume)
  have hle : ∀ t ∈ Ioo (0 : ℝ) 1, 1 / (1 + κ * (γ t).1 ^ 2) * (derivWithin γ (Icc 0 1) t).1
      ≤ √(kleinMetric κ (γ t) (derivWithin γ (Icc 0 1) t) (derivWithin γ (Icc 0 1) t)) :=
    fun t ht => axis_le_metric hκ.le (hmaps (Ioo_subset_Icc_self ht)) _
  have := intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le zero_le_one hcont hderiv hint hle
  simp only [h0, h1] at this
  exact this

/-- The path along the first axis from `(0, 0)` to `(r, 0)`. -/
theorem axis_isKleinPath {κ r : ℝ} (hκ : κ ≤ 0) (hr : (r, (0 : ℝ)) ∈ plane κ) :
    IsKleinPath κ (fun t => (t * r, 0)) (0, 0) (r, 0) := by
  refine ⟨(by fun_prop : ContDiff ℝ 1 fun t : ℝ => (t * r, (0 : ℝ))).contDiffOn, ?_, by simp,
    by simp⟩
  intro t ht
  have hr' := mem_plane.mp hr
  simp only at hr'
  rw [mem_plane]
  simp only
  have ht2 : t ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
  nlinarith [mul_le_mul_of_nonneg_right ht2 (sq_nonneg r), mul_nonpos_of_nonpos_of_nonneg hκ
    (sq_nonneg r)]

/-- **The path along the first axis has the length `axisDist`.** -/
theorem axis_kleinLength {κ r : ℝ} (hκ : κ < 0) (hr0 : 0 ≤ r) (hr : (r, (0 : ℝ)) ∈ plane κ) :
    kleinLength κ (fun t => (t * r, 0)) = axisDist κ r := by
  have hpos : ∀ t ∈ Icc (0 : ℝ) 1, 0 < 1 + κ * (t * r) ^ 2 := fun t ht => by
    have := mem_plane.mp ((axis_isKleinPath hκ.le hr).2.1 ht)
    simp only at this
    linarith
  have hderiv : ∀ t ∈ Icc (0 : ℝ) 1,
      derivWithin (fun t => (t * r, (0 : ℝ))) (Icc 0 1) t = (r, 0) := fun t ht =>
    (((hasDerivAt_mul_const r).prodMk (hasDerivAt_const t (0 : ℝ))).hasDerivWithinAt).derivWithin
      (uniqueDiffOn_Icc_zero_one t ht)
  have hint : ∀ t ∈ uIcc (0 : ℝ) 1,
      √(kleinMetric κ (t * r, 0) (derivWithin (fun t => (t * r, (0 : ℝ))) (Icc 0 1) t)
        (derivWithin (fun t => (t * r, (0 : ℝ))) (Icc 0 1) t))
      = 1 / (1 + κ * (t * r) ^ 2) * r := by
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    rw [hderiv t ht]
    have hp := hpos t ht
    have e : kleinMetric κ (t * r, 0) (r, 0) (r, 0) = (1 / (1 + κ * (t * r) ^ 2) * r) ^ 2 := by
      simp only [kleinMetric, cross]
      field_simp
      ring
    rw [e, sqrt_sq (by positivity)]
  unfold kleinLength
  rw [intervalIntegral.integral_congr hint,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t => axisDist κ (t * r))]
  · simp [axisDist_zero]
  · intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    exact (hasDerivAt_axisDist hκ (hpos t ht)).comp t (hasDerivAt_mul_const r)
  · apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le zero_le_one]
    apply ContinuousOn.mul _ continuousOn_const
    exact ContinuousOn.div continuousOn_const (by fun_prop) (fun t ht => (hpos t ht).ne')

/-- **Klein's distance from `(0, 0)` to `(r, 0)` is `axisDist`.** -/
theorem kleinDist_axis {κ r : ℝ} (hκ : κ < 0) (hr0 : 0 ≤ r) (hr : (r, (0 : ℝ)) ∈ plane κ) :
    kleinDist κ (0, 0) (r, 0) = axisDist κ r := by
  apply le_antisymm
  · rw [← axis_kleinLength hκ hr0 hr]
    exact csInf_le (kleinDist_bddBelow κ _ _) ⟨_, axis_isKleinPath hκ.le hr, rfl⟩
  · apply le_csInf (kleinDist_nonempty (zero_mem_plane κ) hr)
    rintro _ ⟨γ, hγ, rfl⟩
    have := axisDist_sub_le_kleinLength hκ hγ
    simpa [axisDist_zero] using this

/-- A turn takes every pair to the first axis, on the side of the positive numbers. -/
theorem exists_rot_to_axis (Q : ℝ × ℝ) :
    ∃ c s r : ℝ, c ^ 2 + s ^ 2 = 1 ∧ 0 ≤ r ∧ rot c s Q = (r, 0) := by
  by_cases h0 : Q.1 ^ 2 + Q.2 ^ 2 = 0
  · have h1 : Q.1 = 0 := pow_eq_zero_iff two_ne_zero |>.mp (by nlinarith [sq_nonneg Q.2])
    have h2 : Q.2 = 0 := pow_eq_zero_iff two_ne_zero |>.mp (by nlinarith [sq_nonneg Q.1])
    exact ⟨1, 0, 0, by norm_num, le_rfl, by simp [rot, h1, h2]⟩
  · have hpos : 0 < Q.1 ^ 2 + Q.2 ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm h0)
    obtain ⟨r, hr0, hr2⟩ : ∃ r : ℝ, 0 < r ∧ r ^ 2 = Q.1 ^ 2 + Q.2 ^ 2 :=
      ⟨√(Q.1 ^ 2 + Q.2 ^ 2), sqrt_pos.mpr hpos, sq_sqrt hpos.le⟩
    refine ⟨Q.1 / r, -Q.2 / r, r, ?_, hr0.le, ?_⟩
    · field_simp
      linear_combination -hr2
    · apply Prod.ext
      · simp only [rot]
        field_simp
        linear_combination -hr2
      · simp only [rot]
        ring

/-- **Theorem H18. Klein's distance**, under a negative bound, between two points of the
plane: `arsinh √(-κ apart) / √(-κ)`. -/
theorem kleinDist_eq_arsinh {κ : ℝ} (hκ : κ < 0) {P Q : ℝ × ℝ} (hP : P ∈ plane κ)
    (hQ : Q ∈ plane κ) : kleinDist κ P Q = arsinh (√(-κ * apart κ P Q)) / √(-κ) := by
  obtain ⟨c, s, a, w, hcs, hw, hw0, hPc⟩ := exists_motion_to_centre hP
  have hrP : rot c s P ∈ plane κ := (rot_mem_plane hcs).mpr hP
  have hrQ : rot c s Q ∈ plane κ := (rot_mem_plane hcs).mpr hQ
  have hQ1 : shift κ a w (rot c s Q) ∈ plane κ := shift_mem_plane hκ.le hw hw0.ne' hrQ
  obtain ⟨c2, s2, r, hcs2, hr0, hQ2⟩ := exists_rot_to_axis (shift κ a w (rot c s Q))
  have hr : (r, (0 : ℝ)) ∈ plane κ := hQ2 ▸ (rot_mem_plane hcs2).mpr hQ1
  have hrot0 : rot c2 s2 ((0 : ℝ), (0 : ℝ)) = (0, 0) := by simp [rot]
  have hd : kleinDist κ P Q = kleinDist κ (0, 0) (r, 0) :=
    calc kleinDist κ P Q = kleinDist κ (rot c s P) (rot c s Q) := (rot_kleinDist hcs hP hQ).symm
      _ = kleinDist κ (shift κ a w (rot c s P)) (shift κ a w (rot c s Q)) :=
        (shift_kleinDist hκ.le hw hw0.ne' hrP hrQ).symm
      _ = kleinDist κ (rot c2 s2 (0, 0)) (rot c2 s2 (shift κ a w (rot c s Q))) := by
        rw [hPc, rot_kleinDist hcs2 (zero_mem_plane κ) hQ1]
      _ = kleinDist κ (0, 0) (r, 0) := by rw [hrot0, hQ2]
  have ha : apart κ P Q = r ^ 2 / (1 + κ * r ^ 2) :=
    calc apart κ P Q = apart κ (rot c s P) (rot c s Q) := (rot_apart hcs κ P Q).symm
      _ = apart κ (shift κ a w (rot c s P)) (shift κ a w (rot c s Q)) :=
        (shift_apart_plane hκ.le hw hw0.ne' hrP hrQ).symm
      _ = apart κ (rot c2 s2 (0, 0)) (rot c2 s2 (shift κ a w (rot c s Q))) := by
        rw [hPc, rot_apart hcs2]
      _ = r ^ 2 / (1 + κ * r ^ 2) := by rw [hrot0, hQ2, apart_centre]
  have hr1 : 0 < 1 + κ * r ^ 2 := by
    have := mem_plane.mp hr
    simp only at this
    linarith
  rw [hd, kleinDist_axis hκ hr0 hr, ha, axisDist, sqrt_mul (neg_nonneg.mpr hκ.le),
    sqrt_div' _ hr1.le, sqrt_sq hr0, mul_div_assoc]

/-- **Theorem H18. `apart` is a function of Klein's distance**:
`apart = sinh² (√(-κ) d) / (-κ)`, under a negative bound. -/
theorem apart_eq_sinh_kleinDist {κ : ℝ} (hκ : κ < 0) {P Q : ℝ × ℝ} (hP : P ∈ plane κ)
    (hQ : Q ∈ plane κ) : apart κ P Q = sinh (√(-κ) * kleinDist κ P Q) ^ 2 / (-κ) := by
  have hs : √(-κ) ≠ 0 := (sqrt_pos.mpr (neg_pos.mpr hκ)).ne'
  have ha : 0 ≤ apart κ P Q := by
    rcases eq_or_ne P Q with rfl | h
    · rw [apart_self]
    · exact (apart_pos hP hQ h).le
  have e : √(-κ) * (arsinh (√(-κ * apart κ P Q)) / √(-κ)) = arsinh (√(-κ * apart κ P Q)) := by
    field_simp
  rw [kleinDist_eq_arsinh hκ hP hQ, e, sinh_arsinh, sq_sqrt (mul_nonneg (neg_nonneg.mpr hκ.le) ha)]
  field_simp [hκ.ne]

end Distance

end HyperbolicPlane

end ParallelPostulate

/-!
# Hilbert's axioms of congruence in the plane of a bound

With the real numbers and a negative bound, a segment is measured by Klein's distance and an
angle by `kleinAngle`, and two segments, or two angles, are congruent when their measures are
equal. This file proves Hilbert's six axioms of congruence, C1 to C6 (Theorem H19). It also
proves C1, C3 and C6 with `apart` for the bound 0, and so for every bound that is not positive,
for the Hilbert planes of `Hilbert.lean`.

## Contents

* Theorem H19, Hilbert's axioms of congruence: `OnRay`, `SameSide`, `segment_construction` (C1),
  `segment_congruence_trans` (C2), `segment_addition` (C3), `angle_construction` (C4),
  `angle_congruence_trans` (C5), `side_angle_side` (C6), `kleinDist_comm`, `kleinAngle_comm`,
  `kleinAngle_onRay`, `kleinDist_nonneg`, `kleinDist_pos`, `sinh_kleinDist`, `cosh_kleinDist`,
  `cos_kleinAngle`, `law_of_cosines`, `kleinDist_add_of_between`
* steps of the proofs of congruence: `apart_eq_kleinInner`, `one_add_dot_pos`, `kleinInner_gram`,
  `kleinAngle_eq_arccos_cos`, `apart_ray`, `apart_ray_lt`, `exists_onRay_apart`,
  `sin_kleinAngle_pos`
* a ray, as Hilbert has it: `onRay_of_between`, `between_of_onRay`
* Euclid's plane, with `apart`: `mem_plane_zero`, `apart_zero_nonneg`, `apart_zero_eq_kleinInner`,
  `euclid_segment_construction`, `euclid_sqrt_apart_add`, `euclid_segment_addition`,
  `euclid_law_of_cosines`, `euclid_sas`
* C1, C3 and C6 with `apart`, under a bound that is not positive: `apart_eq_iff_kleinDist_eq`,
  `segment_construction_apart`, `segment_addition_apart`, `sas_apart`
-/

namespace ParallelPostulate

namespace HyperbolicPlane

open Pairs

/-! ## Hilbert's axioms of congruence

With the real numbers and a negative bound, a segment is measured by Klein's distance and an
angle by `kleinAngle`, and two segments, or two angles, are congruent when their measures are
equal. This section proves Hilbert's six axioms of congruence, C1 to C6, for the plane. -/

section Congruence

open Set Real

/-- `apart` is the inner product at `P` of the direction to `Q` with itself, divided by the
bounds at the two pairs. -/
theorem apart_eq_kleinInner (κ : ℝ) (P Q : ℝ × ℝ) :
    apart κ P Q = kleinInner κ P Q Q
      / ((1 + κ * (P.1 ^ 2 + P.2 ^ 2)) * (1 + κ * (Q.1 ^ 2 + Q.2 ^ 2))) := by
  simp only [apart, kleinInner, cross]
  ring

/-- Under a bound that is not positive, two points of the plane have `1 + κ (P · Q)` positive. -/
theorem one_add_dot_pos {κ : ℝ} (hκ : κ ≤ 0) {P Q : ℝ × ℝ} (hP : P ∈ plane κ)
    (hQ : Q ∈ plane κ) : 0 < 1 + κ * (P.1 * Q.1 + P.2 * Q.2) := by
  have hP' := mem_plane.mp hP
  have hQ' := mem_plane.mp hQ
  have hcs : (P.1 * Q.1 + P.2 * Q.2) ^ 2 ≤ (P.1 ^ 2 + P.2 ^ 2) * (Q.1 ^ 2 + Q.2 ^ 2) := by
    nlinarith [sq_nonneg (P.1 * Q.2 - P.2 * Q.1)]
  have h1 : 0 ≤ -κ * (P.1 ^ 2 + P.2 ^ 2) := mul_nonneg (neg_nonneg.mpr hκ) (by positivity)
  have h2 : 0 ≤ -κ * (Q.1 ^ 2 + Q.2 ^ 2) := mul_nonneg (neg_nonneg.mpr hκ) (by positivity)
  have hlt : (κ * (P.1 * Q.1 + P.2 * Q.2)) ^ 2 < 1 := by
    calc (κ * (P.1 * Q.1 + P.2 * Q.2)) ^ 2 = κ ^ 2 * (P.1 * Q.1 + P.2 * Q.2) ^ 2 := by ring
      _ ≤ κ ^ 2 * ((P.1 ^ 2 + P.2 ^ 2) * (Q.1 ^ 2 + Q.2 ^ 2)) :=
        mul_le_mul_of_nonneg_left hcs (sq_nonneg κ)
      _ = (-κ * (P.1 ^ 2 + P.2 ^ 2)) * (-κ * (Q.1 ^ 2 + Q.2 ^ 2)) := by ring
      _ < 1 * 1 := by
        apply mul_lt_mul'' _ _ h1 h2 <;> linarith
      _ = 1 := one_mul 1
  nlinarith [hlt]

/-- Klein's distance is not negative. -/
theorem kleinDist_nonneg {κ : ℝ} {P Q : ℝ × ℝ} (hP : P ∈ plane κ) (hQ : Q ∈ plane κ) :
    0 ≤ kleinDist κ P Q :=
  le_csInf (kleinDist_nonempty hP hQ) (by rintro _ ⟨γ, -, rfl⟩; exact kleinLength_nonneg κ γ)

/-- **Klein's distance does not depend on the order of the two points.** -/
theorem kleinDist_comm {κ : ℝ} (hκ : κ < 0) {P Q : ℝ × ℝ} (hP : P ∈ plane κ)
    (hQ : Q ∈ plane κ) : kleinDist κ P Q = kleinDist κ Q P := by
  rw [kleinDist_eq_arsinh hκ hP hQ, kleinDist_eq_arsinh hκ hQ hP, apart_comm]

/-- Two different points of the plane are a positive distance apart. -/
theorem kleinDist_pos {κ : ℝ} (hκ : κ < 0) {P Q : ℝ × ℝ} (hP : P ∈ plane κ)
    (hQ : Q ∈ plane κ) (hPQ : P ≠ Q) : 0 < kleinDist κ P Q := by
  rw [kleinDist_eq_arsinh hκ hP hQ]
  apply div_pos _ (sqrt_pos.mpr (neg_pos.mpr hκ))
  rw [arsinh_pos_iff, sqrt_pos]
  exact mul_pos (neg_pos.mpr hκ) (apart_pos hP hQ hPQ)

/-- **The hyperbolic sine of Klein's distance.** -/
theorem sinh_kleinDist {κ : ℝ} (hκ : κ < 0) {P Q : ℝ × ℝ} (hP : P ∈ plane κ)
    (hQ : Q ∈ plane κ) :
    sinh (√(-κ) * kleinDist κ P Q) = √(-κ) * √(kleinInner κ P Q Q)
      / (√(1 + κ * (P.1 ^ 2 + P.2 ^ 2)) * √(1 + κ * (Q.1 ^ 2 + Q.2 ^ 2))) := by
  have hs : √(-κ) ≠ 0 := (sqrt_pos.mpr (neg_pos.mpr hκ)).ne'
  have e : √(-κ) * (arsinh (√(-κ * apart κ P Q)) / √(-κ)) = arsinh (√(-κ * apart κ P Q)) := by
    field_simp
  rw [kleinDist_eq_arsinh hκ hP hQ, e, sinh_arsinh, apart_eq_kleinInner,
    sqrt_mul (neg_nonneg.mpr hκ.le),
    sqrt_div' _ (mul_nonneg (mem_plane.mp hP).le (mem_plane.mp hQ).le),
    sqrt_mul (mem_plane.mp hP).le, mul_div_assoc]

/-- **The hyperbolic cosine of Klein's distance.** -/
theorem cosh_kleinDist {κ : ℝ} (hκ : κ < 0) {P Q : ℝ × ℝ} (hP : P ∈ plane κ)
    (hQ : Q ∈ plane κ) :
    cosh (√(-κ) * kleinDist κ P Q) = (1 + κ * (P.1 * Q.1 + P.2 * Q.2))
      / (√(1 + κ * (P.1 ^ 2 + P.2 ^ 2)) * √(1 + κ * (Q.1 ^ 2 + Q.2 ^ 2))) := by
  have hBP := mem_plane.mp hP
  have hBQ := mem_plane.mp hQ
  have hsP : 0 < √(1 + κ * (P.1 ^ 2 + P.2 ^ 2)) := sqrt_pos.mpr hBP
  have hsQ : 0 < √(1 + κ * (Q.1 ^ 2 + Q.2 ^ 2)) := sqrt_pos.mpr hBQ
  have hk : √(-κ) ^ 2 = -κ := sq_sqrt (neg_nonneg.mpr hκ.le)
  have hg : √(kleinInner κ P Q Q) ^ 2 = kleinInner κ P Q Q := by
    rcases eq_or_ne Q P with rfl | h
    · have h0 : kleinInner κ Q Q Q = 0 := by
        simp only [kleinInner, cross]
        ring
      rw [h0]
      simp
    · exact sq_sqrt (kleinInner_self_pos hP h).le
  have hP2 : √(1 + κ * (P.1 ^ 2 + P.2 ^ 2)) ^ 2 = 1 + κ * (P.1 ^ 2 + P.2 ^ 2) := sq_sqrt hBP.le
  have hQ2 : √(1 + κ * (Q.1 ^ 2 + Q.2 ^ 2)) ^ 2 = 1 + κ * (Q.1 ^ 2 + Q.2 ^ 2) := sq_sqrt hBQ.le
  have hpos : 0 < (1 + κ * (P.1 * Q.1 + P.2 * Q.2))
      / (√(1 + κ * (P.1 ^ 2 + P.2 ^ 2)) * √(1 + κ * (Q.1 ^ 2 + Q.2 ^ 2))) :=
    div_pos (one_add_dot_pos hκ.le hP hQ) (mul_pos hsP hsQ)
  rw [← pow_left_inj₀ (cosh_pos _).le hpos.le two_ne_zero, cosh_sq, sinh_kleinDist hκ hP hQ]
  have e1 : (√(-κ) * √(kleinInner κ P Q Q)
        / (√(1 + κ * (P.1 ^ 2 + P.2 ^ 2)) * √(1 + κ * (Q.1 ^ 2 + Q.2 ^ 2)))) ^ 2 + 1
      = (√(-κ) ^ 2 * √(kleinInner κ P Q Q) ^ 2
        + √(1 + κ * (P.1 ^ 2 + P.2 ^ 2)) ^ 2 * √(1 + κ * (Q.1 ^ 2 + Q.2 ^ 2)) ^ 2)
          / (√(1 + κ * (P.1 ^ 2 + P.2 ^ 2)) ^ 2 * √(1 + κ * (Q.1 ^ 2 + Q.2 ^ 2)) ^ 2) := by
    field_simp
  have e2 : ((1 + κ * (P.1 * Q.1 + P.2 * Q.2))
        / (√(1 + κ * (P.1 ^ 2 + P.2 ^ 2)) * √(1 + κ * (Q.1 ^ 2 + Q.2 ^ 2)))) ^ 2
      = (1 + κ * (P.1 * Q.1 + P.2 * Q.2)) ^ 2
          / (√(1 + κ * (P.1 ^ 2 + P.2 ^ 2)) ^ 2 * √(1 + κ * (Q.1 ^ 2 + Q.2 ^ 2)) ^ 2) := by
    rw [div_pow, mul_pow]
  rw [e1, e2, hk, hg, hP2, hQ2]
  congr 1
  simp only [kleinInner, cross]
  ring

/-- **The Gram identity** for the inner product at a pair. -/
theorem kleinInner_gram (κ : ℝ) (P A B : ℝ × ℝ) :
    kleinInner κ P A A * kleinInner κ P B B - kleinInner κ P A B ^ 2
      = (1 + κ * (P.1 ^ 2 + P.2 ^ 2)) * (Dim.mk P A).side B ^ 2 := by
  simp only [kleinInner, Dim.side, Dim.dir, cross]
  ring

/-- **The cosine of `kleinAngle`.** At a point of the plane the quotient is between `-1` and
`1`, and `kleinAngle` is its arccosine. -/
theorem cos_kleinAngle {κ : ℝ} {P A B : ℝ × ℝ} (hP : P ∈ plane κ) (hA : A ≠ P) (hB : B ≠ P) :
    cos (kleinAngle κ P A B)
      = kleinInner κ P A B / (√(kleinInner κ P A A) * √(kleinInner κ P B B)) := by
  have hgA := kleinInner_self_pos hP hA
  have hgB := kleinInner_self_pos hP hB
  have hd : 0 < √(kleinInner κ P A A) * √(kleinInner κ P B B) :=
    mul_pos (sqrt_pos.mpr hgA) (sqrt_pos.mpr hgB)
  have habs : |kleinInner κ P A B| ≤ √(kleinInner κ P A A) * √(kleinInner κ P B B) := by
    rw [← sqrt_mul hgA.le]
    apply abs_le_sqrt
    have := kleinInner_gram κ P A B
    nlinarith [mul_nonneg (mem_plane.mp hP).le (sq_nonneg ((Dim.mk P A).side B))]
  have hx : |kleinInner κ P A B / (√(kleinInner κ P A A) * √(kleinInner κ P B B))| ≤ 1 := by
    rw [abs_div, abs_of_pos hd, div_le_one hd]
    exact habs
  have h1 := abs_le.mp hx
  rw [kleinAngle, cos_arccos h1.1 h1.2]

/-- `kleinAngle` is between 0 and `π`, so it is the arccosine of its cosine. -/
theorem kleinAngle_eq_arccos_cos (κ : ℝ) (P A B : ℝ × ℝ) :
    kleinAngle κ P A B = arccos (cos (kleinAngle κ P A B)) :=
  (arccos_cos (arccos_nonneg _) (arccos_le_pi _)).symm

/-- **The law of cosines** in the plane of a negative bound, with Klein's distance and
`kleinAngle`, at the vertex `P`. -/
theorem law_of_cosines {κ : ℝ} (hκ : κ < 0) {P A B : ℝ × ℝ} (hP : P ∈ plane κ)
    (hA : A ∈ plane κ) (hB : B ∈ plane κ) (hAP : A ≠ P) (hBP : B ≠ P) :
    cosh (√(-κ) * kleinDist κ P A) * cosh (√(-κ) * kleinDist κ P B)
        - cosh (√(-κ) * kleinDist κ A B)
      = sinh (√(-κ) * kleinDist κ P A) * sinh (√(-κ) * kleinDist κ P B)
        * cos (kleinAngle κ P A B) := by
  have hsP := sqrt_pos.mpr (mem_plane.mp hP)
  have hsA := sqrt_pos.mpr (mem_plane.mp hA)
  have hsB := sqrt_pos.mpr (mem_plane.mp hB)
  have hgA := sqrt_pos.mpr (kleinInner_self_pos hP hAP)
  have hgB := sqrt_pos.mpr (kleinInner_self_pos hP hBP)
  have hL : cosh (√(-κ) * kleinDist κ P A) * cosh (√(-κ) * kleinDist κ P B)
        - cosh (√(-κ) * kleinDist κ A B)
      = ((1 + κ * (P.1 * A.1 + P.2 * A.2)) * (1 + κ * (P.1 * B.1 + P.2 * B.2))
          - √(1 + κ * (P.1 ^ 2 + P.2 ^ 2)) ^ 2 * (1 + κ * (A.1 * B.1 + A.2 * B.2)))
        / (√(1 + κ * (P.1 ^ 2 + P.2 ^ 2)) ^ 2 * √(1 + κ * (A.1 ^ 2 + A.2 ^ 2))
          * √(1 + κ * (B.1 ^ 2 + B.2 ^ 2))) := by
    rw [cosh_kleinDist hκ hP hA, cosh_kleinDist hκ hP hB, cosh_kleinDist hκ hA hB]
    field_simp
  have hR : sinh (√(-κ) * kleinDist κ P A) * sinh (√(-κ) * kleinDist κ P B)
        * cos (kleinAngle κ P A B)
      = √(-κ) ^ 2 * kleinInner κ P A B
        / (√(1 + κ * (P.1 ^ 2 + P.2 ^ 2)) ^ 2 * √(1 + κ * (A.1 ^ 2 + A.2 ^ 2))
          * √(1 + κ * (B.1 ^ 2 + B.2 ^ 2))) := by
    rw [sinh_kleinDist hκ hP hA, sinh_kleinDist hκ hP hB, cos_kleinAngle hP hAP hBP]
    field_simp
  rw [hL, hR, sq_sqrt (neg_nonneg.mpr hκ.le), sq_sqrt (mem_plane.mp hP).le]
  congr 1
  simp only [kleinInner, cross]
  ring

/-- `X` is on the ray from `O` through `A`: `X = O + t (A - O)` with `t` positive. -/
@[expose] def OnRay (O A X : ℝ × ℝ) : Prop := ∃ t : ℝ, 0 < t ∧ X = (Dim.mk O A).pt t

/-- `X` and `Y` are on the same side of the line through `O` and `A`. -/
@[expose] def SameSide (O A X Y : ℝ × ℝ) : Prop := 0 < (Dim.mk O A).side X * (Dim.mk O A).side Y

/-- **An angle does not depend on the order of its two rays.** -/
theorem kleinAngle_comm (κ : ℝ) (P A B : ℝ × ℝ) : kleinAngle κ P A B = kleinAngle κ P B A := by
  have h : kleinInner κ P A B = kleinInner κ P B A := by
    simp only [kleinInner]
    ring
  rw [kleinAngle, kleinAngle, h, mul_comm (√(kleinInner κ P A A))]

/-- **An angle depends only on its two rays.** -/
theorem kleinAngle_onRay {κ : ℝ} {P A B A' B' : ℝ × ℝ} (hA : OnRay P A A') (hB : OnRay P B B') :
    kleinAngle κ P A' B' = kleinAngle κ P A B := by
  obtain ⟨s, hs, rfl⟩ := hA
  obtain ⟨t, ht, rfl⟩ := hB
  have e1 : kleinInner κ P ((Dim.mk P A).pt s) ((Dim.mk P B).pt t)
      = 1 * s * t * kleinInner κ P A B := by
    simp only [kleinInner, cross, Dim.pt]
    ring
  have e2 : kleinInner κ P ((Dim.mk P A).pt s) ((Dim.mk P A).pt s)
      = 1 * s ^ 2 * kleinInner κ P A A := by
    simp only [kleinInner, cross, Dim.pt]
    ring
  have e3 : kleinInner κ P ((Dim.mk P B).pt t) ((Dim.mk P B).pt t)
      = 1 * t ^ 2 * kleinInner κ P B B := by
    simp only [kleinInner, cross, Dim.pt]
    ring
  rw [kleinAngle, e1, e2, e3, kleinAngle_aux one_pos (mul_pos hs ht)]
  rfl

/-- **Theorem H19, C6: side, angle, side.** Let two triangles have two sides and the angle
between them congruent. Then the third sides are congruent, and so are the two other pairs of
angles. -/
theorem side_angle_side {κ : ℝ} (hκ : κ < 0) {A B C D E F : ℝ × ℝ} (hA : A ∈ plane κ)
    (hB : B ∈ plane κ) (hC : C ∈ plane κ) (hD : D ∈ plane κ) (hE : E ∈ plane κ)
    (hF : F ∈ plane κ) (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C) (hDE : D ≠ E) (hDF : D ≠ F)
    (hEF : E ≠ F) (h1 : kleinDist κ A B = kleinDist κ D E)
    (h2 : kleinDist κ A C = kleinDist κ D F) (h3 : kleinAngle κ A B C = kleinAngle κ D E F) :
    kleinDist κ B C = kleinDist κ E F ∧ kleinAngle κ B A C = kleinAngle κ E D F ∧
      kleinAngle κ C A B = kleinAngle κ F D E := by
  have hk : 0 < √(-κ) := sqrt_pos.mpr (neg_pos.mpr hκ)
  have lA := law_of_cosines hκ hA hB hC hAB.symm hAC.symm
  have lD := law_of_cosines hκ hD hE hF hDE.symm hDF.symm
  rw [h1, h2, h3] at lA
  have hcosh : cosh (√(-κ) * kleinDist κ B C) = cosh (√(-κ) * kleinDist κ E F) := by linarith
  have hnn : ∀ {X Y : ℝ × ℝ}, X ∈ plane κ → Y ∈ plane κ → 0 ≤ √(-κ) * kleinDist κ X Y :=
    fun hX hY => mul_nonneg hk.le (kleinDist_nonneg hX hY)
  have hBCEF : kleinDist κ B C = kleinDist κ E F := by
    have h := le_antisymm (cosh_le_cosh.mp hcosh.le) (cosh_le_cosh.mp hcosh.ge)
    rw [abs_of_nonneg (hnn hB hC), abs_of_nonneg (hnn hE hF)] at h
    exact mul_left_cancel₀ hk.ne' h
  have hsinh : ∀ {X Y : ℝ × ℝ}, X ∈ plane κ → Y ∈ plane κ → X ≠ Y →
      0 < sinh (√(-κ) * kleinDist κ X Y) :=
    fun hX hY hXY => sinh_pos_iff.mpr (mul_pos hk (kleinDist_pos hκ hX hY hXY))
  have angle_eq : ∀ {P Q R P' Q' R' : ℝ × ℝ}, P ∈ plane κ → Q ∈ plane κ → R ∈ plane κ →
      P' ∈ plane κ → Q' ∈ plane κ → R' ∈ plane κ → Q ≠ P → R ≠ P → Q' ≠ P' → R' ≠ P' →
      kleinDist κ P Q = kleinDist κ P' Q' → kleinDist κ P R = kleinDist κ P' R' →
      kleinDist κ Q R = kleinDist κ Q' R' → kleinAngle κ P Q R = kleinAngle κ P' Q' R' := by
    intro P Q R P' Q' R' hP hQ hR hP' hQ' hR' hQP hRP hQP' hRP' e1 e2 e3
    have l := law_of_cosines hκ hP hQ hR hQP hRP
    have l' := law_of_cosines hκ hP' hQ' hR' hQP' hRP'
    rw [e1, e2, e3] at l
    have hpos := mul_pos (hsinh hP' hQ' hQP'.symm) (hsinh hP' hR' hRP'.symm)
    have hcos : cos (kleinAngle κ P Q R) = cos (kleinAngle κ P' Q' R') :=
      mul_left_cancel₀ hpos.ne' (by linarith)
    rw [kleinAngle_eq_arccos_cos κ P Q R, kleinAngle_eq_arccos_cos κ P' Q' R', hcos]
  refine ⟨hBCEF, ?_, ?_⟩
  · exact angle_eq hB hA hC hE hD hF hAB hBC.symm hDE hEF.symm
      (by rw [kleinDist_comm hκ hB hA, kleinDist_comm hκ hE hD, h1]) hBCEF h2
  · exact angle_eq hC hA hB hF hD hE hAC hBC hDF hEF
      (by rw [kleinDist_comm hκ hC hA, kleinDist_comm hκ hF hD, h2])
      (by rw [kleinDist_comm hκ hC hB, kleinDist_comm hκ hF hE, hBCEF]) h1

/-- **Klein's distance adds along a segment.** If `B` is between `A` and `C`, it is a point of
the plane, and the distance from `A` to `C` is the sum of the distances from `A` to `B` and from
`B` to `C`. -/
theorem kleinDist_add_of_between {κ : ℝ} (hκ : κ < 0) {A B C : ℝ × ℝ} (hA : A ∈ plane κ)
    (hC : C ∈ plane κ) (h : Between A B C) :
    B ∈ plane κ ∧ kleinDist κ A C = kleinDist κ A B + kleinDist κ B C := by
  obtain ⟨-, u, hu0, hu1, rfl⟩ := h
  have hB : (Dim.mk A C).pt u ∈ plane κ := plane_convex κ hA hC hu0.le hu1.le
  refine ⟨hB, ?_⟩
  have hk : 0 < √(-κ) := sqrt_pos.mpr (neg_pos.mpr hκ)
  have hsA := sqrt_pos.mpr (mem_plane.mp hA)
  have hsB := sqrt_pos.mpr (mem_plane.mp hB)
  have hsC := sqrt_pos.mpr (mem_plane.mp hC)
  have hgAB : kleinInner κ A ((Dim.mk A C).pt u) ((Dim.mk A C).pt u)
      = u ^ 2 * kleinInner κ A C C := by
    simp only [kleinInner, cross, Dim.pt]
    ring
  have hgBC : kleinInner κ ((Dim.mk A C).pt u) C C = (1 - u) ^ 2 * kleinInner κ A C C := by
    simp only [kleinInner, cross, Dim.pt]
    ring
  have hcB : u * (1 + κ * (((Dim.mk A C).pt u).1 * C.1 + ((Dim.mk A C).pt u).2 * C.2))
      + (1 - u) * (1 + κ * (A.1 * ((Dim.mk A C).pt u).1 + A.2 * ((Dim.mk A C).pt u).2))
      = 1 + κ * (((Dim.mk A C).pt u).1 ^ 2 + ((Dim.mk A C).pt u).2 ^ 2) := by
    simp only [Dim.pt]
    ring
  have hL : sinh (√(-κ) * kleinDist κ A ((Dim.mk A C).pt u))
        * cosh (√(-κ) * kleinDist κ ((Dim.mk A C).pt u) C)
      + cosh (√(-κ) * kleinDist κ A ((Dim.mk A C).pt u))
        * sinh (√(-κ) * kleinDist κ ((Dim.mk A C).pt u) C)
      = √(-κ) * √(kleinInner κ A C C)
        * (u * (1 + κ * (((Dim.mk A C).pt u).1 * C.1 + ((Dim.mk A C).pt u).2 * C.2))
          + (1 - u) * (1 + κ * (A.1 * ((Dim.mk A C).pt u).1 + A.2 * ((Dim.mk A C).pt u).2)))
        / (√(1 + κ * (A.1 ^ 2 + A.2 ^ 2))
          * √(1 + κ * (((Dim.mk A C).pt u).1 ^ 2 + ((Dim.mk A C).pt u).2 ^ 2)) ^ 2
          * √(1 + κ * (C.1 ^ 2 + C.2 ^ 2))) := by
    rw [sinh_kleinDist hκ hA hB, cosh_kleinDist hκ hB hC, cosh_kleinDist hκ hA hB,
      sinh_kleinDist hκ hB hC, hgAB, hgBC, sqrt_mul (sq_nonneg _), sqrt_mul (sq_nonneg _),
      sqrt_sq hu0.le, sqrt_sq (by linarith)]
    field_simp
  have hsum : sinh (√(-κ) * kleinDist κ A C) = sinh (√(-κ) * kleinDist κ A ((Dim.mk A C).pt u)
      + √(-κ) * kleinDist κ ((Dim.mk A C).pt u) C) := by
    have hBB := (mem_plane.mp hB).ne'
    rw [sinh_add, hL, hcB, sq_sqrt (mem_plane.mp hB).le, sinh_kleinDist hκ hA hC]
    field_simp
  have := sinh_injective hsum
  rw [← mul_add] at this
  exact mul_left_cancel₀ hk.ne' this

/-- **Theorem H19, C3: addition of segments.** -/
theorem segment_addition {κ : ℝ} (hκ : κ < 0) {A B C D E F : ℝ × ℝ} (hA : A ∈ plane κ)
    (hC : C ∈ plane κ) (hD : D ∈ plane κ) (hF : F ∈ plane κ) (hABC : Between A B C)
    (hDEF : Between D E F) (h1 : kleinDist κ A B = kleinDist κ D E)
    (h2 : kleinDist κ B C = kleinDist κ E F) : kleinDist κ A C = kleinDist κ D F := by
  rw [(kleinDist_add_of_between hκ hA hC hABC).2, (kleinDist_add_of_between hκ hD hF hDEF).2,
    h1, h2]

/-- **Theorem H19, C2.** Two segments congruent to a third are congruent to each other. -/
theorem segment_congruence_trans {κ : ℝ} {A B C D E F : ℝ × ℝ}
    (h1 : kleinDist κ A B = kleinDist κ C D) (h2 : kleinDist κ A B = kleinDist κ E F) :
    kleinDist κ C D = kleinDist κ E F :=
  h1.symm.trans h2

/-- **Theorem H19, C5.** Two angles congruent to a third are congruent to each other. -/
theorem angle_congruence_trans {κ : ℝ} {A B C D E F P Q R : ℝ × ℝ}
    (h1 : kleinAngle κ A B C = kleinAngle κ D E F) (h2 : kleinAngle κ A B C = kleinAngle κ P Q R) :
    kleinAngle κ D E F = kleinAngle κ P Q R :=
  h1.symm.trans h2

/-- Along the ray from `O` through `D`, `apart` from `O`. -/
theorem apart_ray (κ : ℝ) (O D : ℝ × ℝ) (t : ℝ) :
    apart κ O ((Dim.mk O D).pt t) = t ^ 2 * kleinInner κ O D D
      / ((1 + κ * (O.1 ^ 2 + O.2 ^ 2))
        * (1 + κ * (((Dim.mk O D).pt t).1 ^ 2 + ((Dim.mk O D).pt t).2 ^ 2))) := by
  rw [apart_eq_kleinInner]
  congr 1
  simp only [kleinInner, cross, Dim.pt]
  ring

/-- **Along a ray, `apart` from its origin grows.** -/
theorem apart_ray_lt {κ : ℝ} (hκ : κ < 0) {O D : ℝ × ℝ} (hO : O ∈ plane κ) (hOD : O ≠ D)
    {s t : ℝ} (hs : 0 < s) (hst : s < t) (hXs : (Dim.mk O D).pt s ∈ plane κ)
    (hXt : (Dim.mk O D).pt t ∈ plane κ) :
    apart κ O ((Dim.mk O D).pt s) < apart κ O ((Dim.mk O D).pt t) := by
  have hG := kleinInner_self_pos hO hOD.symm
  have hBO := mem_plane.mp hO
  have hBs := mem_plane.mp hXs
  have hBt := mem_plane.mp hXt
  have h1 := one_add_dot_pos hκ.le hO hXs
  have h2 := one_add_dot_pos hκ.le hO hXt
  rw [apart_ray, apart_ray, div_lt_div_iff₀ (mul_pos hBO hBs) (mul_pos hBO hBt)]
  have key : t ^ 2 * kleinInner κ O D D * ((1 + κ * (O.1 ^ 2 + O.2 ^ 2))
        * (1 + κ * (((Dim.mk O D).pt s).1 ^ 2 + ((Dim.mk O D).pt s).2 ^ 2)))
      - s ^ 2 * kleinInner κ O D D * ((1 + κ * (O.1 ^ 2 + O.2 ^ 2))
        * (1 + κ * (((Dim.mk O D).pt t).1 ^ 2 + ((Dim.mk O D).pt t).2 ^ 2)))
      = kleinInner κ O D D * (1 + κ * (O.1 ^ 2 + O.2 ^ 2)) * ((t - s)
        * (s * (1 + κ * (O.1 * ((Dim.mk O D).pt t).1 + O.2 * ((Dim.mk O D).pt t).2))
          + t * (1 + κ * (O.1 * ((Dim.mk O D).pt s).1 + O.2 * ((Dim.mk O D).pt s).2)))) := by
    simp only [Dim.pt]
    ring
  have hpos := mul_pos (mul_pos hG hBO) (mul_pos (sub_pos.mpr hst)
    (add_pos (mul_pos hs h2) (mul_pos (hs.trans hst) h1)))
  linarith

/-- **On a ray from a point of the plane, `apart` from the origin takes every positive value.**
Under a negative bound. -/
theorem exists_onRay_apart {κ : ℝ} (hκ : κ < 0) {O D : ℝ × ℝ} (hO : O ∈ plane κ) (hOD : O ≠ D)
    {α : ℝ} (hα : 0 < α) :
    ∃ t : ℝ, 0 < t ∧ (Dim.mk O D).pt t ∈ plane κ ∧ apart κ O ((Dim.mk O D).pt t) = α := by
  have hG := kleinInner_self_pos hO hOD.symm
  have hBO := mem_plane.mp hO
  have hnk : 0 < -κ := neg_pos.mpr hκ
  have hV : 0 < (D.1 - O.1) ^ 2 + (D.2 - O.2) ^ 2 := by
    have hne : ((D.1 - O.1, D.2 - O.2) : ℝ × ℝ) ≠ (0, 0) := by
      intro h
      apply hOD
      have h1 := congrArg Prod.fst h
      have h2 := congrArg Prod.snd h
      simp only [] at h1 h2
      exact Prod.ext (by linarith) (by linarith)
    exact sq_add_sq_pos hne
  set V := (D.1 - O.1) ^ 2 + (D.2 - O.2) ^ 2 with hVdef
  set W := O.1 * (D.1 - O.1) + O.2 * (D.2 - O.2) with hWdef
  set T := (2 * |W| + 1) / V + 1 / (-κ) with hTdef
  have hT1 : 1 / (-κ) ≤ T := by
    have : 0 ≤ (2 * |W| + 1) / V := div_nonneg (by positivity) hV.le
    linarith
  have hT0 : 0 ≤ T := le_trans (one_div_pos.mpr hnk).le hT1
  have hTV : 2 * |W| + 1 ≤ T * V := by
    rw [hTdef, add_mul, div_mul_cancel₀ _ hV.ne']
    have : 0 ≤ 1 / (-κ) * V := mul_nonneg (one_div_pos.mpr hnk).le hV.le
    linarith
  have hXT : 1 / (-κ) ≤ ((Dim.mk O D).pt T).1 ^ 2 + ((Dim.mk O D).pt T).2 ^ 2 := by
    have e : ((Dim.mk O D).pt T).1 ^ 2 + ((Dim.mk O D).pt T).2 ^ 2
        = (O.1 ^ 2 + O.2 ^ 2) + 2 * (T * W) + T * (T * V) := by
      simp only [Dim.pt, hWdef, hVdef]
      ring
    rw [e]
    have ha : -(T * |W|) ≤ T * W := by
      have := mul_le_mul_of_nonneg_left (neg_abs_le W) hT0
      linarith
    have hb : 0 ≤ T * (T * V - 2 * |W| - 1) := mul_nonneg hT0 (by linarith)
    nlinarith only [ha, hb, hT1, sq_nonneg O.1, sq_nonneg O.2]
  have hBT : 1 + κ * (((Dim.mk O D).pt T).1 ^ 2 + ((Dim.mk O D).pt T).2 ^ 2) ≤ 0 := by
    have h := mul_le_mul_of_nonpos_left hXT hκ.le
    have e : κ * (1 / (-κ)) = -1 := by
      rw [mul_one_div, div_neg, div_self hκ.ne]
    linarith
  set f : ℝ → ℝ := fun t => t ^ 2 * kleinInner κ O D D - α
    * (1 + κ * (O.1 ^ 2 + O.2 ^ 2))
    * (1 + κ * (((Dim.mk O D).pt t).1 ^ 2 + ((Dim.mk O D).pt t).2 ^ 2)) with hf
  have hfc : Continuous f := by
    simp only [hf, Dim.pt]
    fun_prop
  have hf0 : f 0 < 0 := by
    have e : f 0 = -(α * (1 + κ * (O.1 ^ 2 + O.2 ^ 2)) ^ 2) := by
      simp only [hf, Dim.pt]
      ring
    rw [e]
    have := mul_pos hα (pow_pos hBO 2)
    linarith
  have hfT : 0 ≤ f T := by
    simp only [hf]
    have := mul_nonneg (mul_nonneg hα.le hBO.le) (neg_nonneg.mpr hBT)
    nlinarith only [this, mul_nonneg (sq_nonneg T) hG.le]
  obtain ⟨t, ht, hft⟩ := intermediate_value_Icc hT0 hfc.continuousOn ⟨hf0.le, hfT⟩
  have ht0 : 0 < t := by
    rcases ht.1.eq_or_lt with h | h
    · rw [← h] at hft
      linarith
    · exact h
  simp only [hf] at hft
  have hBt : 0 < 1 + κ * (((Dim.mk O D).pt t).1 ^ 2 + ((Dim.mk O D).pt t).2 ^ 2) := by
    by_contra h
    have h := not_lt.mp h
    have := mul_nonpos_of_nonneg_of_nonpos (mul_pos hα hBO).le h
    nlinarith only [hft, this, mul_pos (pow_pos ht0 2) hG]
  have hXt : (Dim.mk O D).pt t ∈ plane κ := mem_plane.mpr hBt
  have hap : apart κ O ((Dim.mk O D).pt t) = α := by
    rw [apart_ray, div_eq_iff (mul_pos hBO hBt).ne']
    linear_combination hft
  exact ⟨t, ht0, hXt, hap⟩

/-- **Theorem H19, C1: construction of segments.** On a ray from `O` there is one point, and
only one, whose distance from `O` is the length of a given segment. -/
theorem segment_construction {κ : ℝ} (hκ : κ < 0) {A B O D : ℝ × ℝ} (hA : A ∈ plane κ)
    (hB : B ∈ plane κ) (hO : O ∈ plane κ) (hAB : A ≠ B) (hOD : O ≠ D) :
    ∃! X, X ∈ plane κ ∧ OnRay O D X ∧ kleinDist κ A B = kleinDist κ O X := by
  obtain ⟨t, ht0, hXt, hap⟩ := exists_onRay_apart hκ hO hOD (apart_pos hA hB hAB)
  refine ⟨(Dim.mk O D).pt t, ⟨hXt, ⟨t, ht0, rfl⟩, ?_⟩, ?_⟩
  · rw [kleinDist_eq_arsinh hκ hA hB, kleinDist_eq_arsinh hκ hO hXt, hap]
  · rintro Y ⟨hY, ⟨s, hs, rfl⟩, hYd⟩
    have hapY : apart κ O ((Dim.mk O D).pt s) = apart κ A B := by
      rw [apart_eq_sinh_kleinDist hκ hO hY, ← hYd, ← apart_eq_sinh_kleinDist hκ hA hB]
    rcases lt_trichotomy s t with h | rfl | h
    · exact absurd (hapY.trans hap.symm) (apart_ray_lt hκ hO hOD hs h hY hXt).ne
    · rfl
    · exact absurd (hap.trans hapY.symm) (apart_ray_lt hκ hO hOD ht0 h hXt hY).ne

/-- **An angle with two rays that are not on one line is strictly between 0 and `π`**, so its
sine is positive. -/
theorem sin_kleinAngle_pos {κ : ℝ} {A B C : ℝ × ℝ} (hA : A ∈ plane κ)
    (hABC : (Dim.mk A B).side C ≠ 0) : 0 < sin (kleinAngle κ A B C) := by
  have hBA : B ≠ A := by
    rintro rfl
    apply hABC
    simp [Dim.side, Dim.dir, cross]
  have hCA : C ≠ A := by
    rintro rfl
    apply hABC
    simp [Dim.side, Dim.dir, cross]
  have hgB := kleinInner_self_pos hA hBA
  have hgC := kleinInner_self_pos hA hCA
  have h0 : 0 ≤ sin (kleinAngle κ A B C) :=
    sin_nonneg_of_nonneg_of_le_pi (arccos_nonneg _) (arccos_le_pi _)
  have hc2 : cos (kleinAngle κ A B C) ^ 2 < 1 := by
    rw [cos_kleinAngle hA hBA hCA, div_pow, mul_pow, sq_sqrt hgB.le, sq_sqrt hgC.le,
      div_lt_one (mul_pos hgB hgC)]
    have := kleinInner_gram κ A B C
    have : 0 < (1 + κ * (A.1 ^ 2 + A.2 ^ 2)) * (Dim.mk A B).side C ^ 2 :=
      mul_pos (mem_plane.mp hA) (by positivity)
    linarith
  have hs := sin_sq_add_cos_sq (kleinAngle κ A B C)
  rcases h0.eq_or_lt with h | h
  · rw [← h] at hs
    linarith
  · exact h

/-- **Theorem H19, C4: construction of angles.** Given an angle, a ray from `D` through `F`,
and a side of the line `DF`, there is a ray from `D` on that side that makes the given angle
with the ray `DF`, and only one. This holds under any bound. -/
theorem angle_construction {κ : ℝ} {A B C D F G : ℝ × ℝ} (hA : A ∈ plane κ)
    (hD : D ∈ plane κ) (hABC : (Dim.mk A B).side C ≠ 0) (hDF : D ≠ F)
    (hG : (Dim.mk D F).side G ≠ 0) :
    (∃ E, E ∈ plane κ ∧ SameSide D F E G ∧ kleinAngle κ D F E = kleinAngle κ A B C) ∧
    ∀ E E', E ∈ plane κ → SameSide D F E G → kleinAngle κ D F E = kleinAngle κ A B C →
      E' ∈ plane κ → SameSide D F E' G → kleinAngle κ D F E' = kleinAngle κ A B C →
      OnRay D E E' := by
  have hsin := sin_kleinAngle_pos hA hABC
  have hgU := kleinInner_self_pos hD hDF.symm
  have hBD := mem_plane.mp hD
  refine ⟨?_, ?_⟩
  · -- the direction perpendicular to `DF` in Klein's metric, and the side of `G`
    set θ := kleinAngle κ A B C with hθ
    set sG := (Dim.mk D F).side G with hsG
    set σ := sG / |sG| with hσ
    have hσ2 : σ ^ 2 = 1 := by
      rw [hσ, div_pow, sq_abs, div_self (pow_ne_zero 2 hG)]
    have hσG : 0 < σ * sG := by
      rw [hσ, div_mul_eq_mul_div, ← sq, ← sq_abs, sq, mul_self_div_self]
      exact abs_pos.mpr hG
    set sB := √(1 + κ * (D.1 ^ 2 + D.2 ^ 2)) with hsB
    have hsB2 : sB ^ 2 = 1 + κ * (D.1 ^ 2 + D.2 ^ 2) := sq_sqrt hBD.le
    have hsBp : 0 < sB := sqrt_pos.mpr hBD
    set c := D.1 * F.2 - D.2 * F.1 with hc
    set v : ℝ × ℝ := (cos θ * sB * (F.1 - D.1) + σ * sin θ * (-(F.2 - D.2) - κ * c * D.1),
      cos θ * sB * (F.2 - D.2) + σ * sin θ * ((F.1 - D.1) - κ * c * D.2)) with hv
    obtain ⟨ε, hε, hE⟩ := plane_open_forward κ (Dim.mk D (D.1 + v.1, D.2 + v.2)) hD
    set E := (Dim.mk D (D.1 + v.1, D.2 + v.2)).pt ε with hEdef
    have hN : kleinInner κ D F E = ε * cos θ * sB * kleinInner κ D F F := by
      simp only [hEdef, hv, hc, kleinInner, cross, Dim.pt]
      ring
    have hNN : kleinInner κ D E E = ε ^ 2 * (cos θ ^ 2 * sB ^ 2
        + σ ^ 2 * sin θ ^ 2 * (1 + κ * (D.1 ^ 2 + D.2 ^ 2))) * kleinInner κ D F F := by
      simp only [hEdef, hv, hc, kleinInner, cross, Dim.pt]
      ring
    have hside : (Dim.mk D F).side E = ε * σ * sin θ * kleinInner κ D F F := by
      simp only [hEdef, hv, hc, kleinInner, Dim.side, Dim.dir, cross, Dim.pt]
      ring
    have hNN' : kleinInner κ D E E
        = ε ^ 2 * (1 + κ * (D.1 ^ 2 + D.2 ^ 2)) * kleinInner κ D F F := by
      rw [hNN, hsB2, hσ2]
      linear_combination (ε ^ 2 * (1 + κ * (D.1 ^ 2 + D.2 ^ 2)) * kleinInner κ D F F)
        * sin_sq_add_cos_sq θ
    have hsq : √(ε ^ 2 * (1 + κ * (D.1 ^ 2 + D.2 ^ 2)) * kleinInner κ D F F)
        = ε * sB * √(kleinInner κ D F F) := by
      rw [sqrt_mul (by positivity), sqrt_mul (by positivity), sqrt_sq hε.le]
    have hg2 : √(kleinInner κ D F F) * √(kleinInner κ D F F) = kleinInner κ D F F :=
      mul_self_sqrt hgU.le
    have hx : ε * cos θ * sB * kleinInner κ D F F
        / (√(kleinInner κ D F F) * (ε * sB * √(kleinInner κ D F F))) = cos θ := by
      rw [div_eq_iff (by positivity)]
      linear_combination (-(ε * cos θ * sB)) * hg2
    refine ⟨E, hE, ?_, ?_⟩
    · change 0 < (Dim.mk D F).side E * sG
      rw [hside]
      have := mul_pos (mul_pos (mul_pos hε hsin) hgU) hσG
      linarith [this]
    · have hθ0 : 0 ≤ θ := arccos_nonneg _
      have hθπ : θ ≤ π := arccos_le_pi _
      rw [kleinAngle, hN, hNN', hsq, hx, arccos_cos hθ0 hθπ]
  · intro E₁ E₂ hE₁ hs₁ ha₁ hE₂ hs₂ ha₂
    have hs12 : 0 < (Dim.mk D F).side E₁ * (Dim.mk D F).side E₂ := by
      have h := mul_pos hs₁ hs₂
      have e : (Dim.mk D F).side E₁ * (Dim.mk D F).side G
          * ((Dim.mk D F).side E₂ * (Dim.mk D F).side G)
          = (Dim.mk D F).side E₁ * (Dim.mk D F).side E₂ * (Dim.mk D F).side G ^ 2 := by ring
      rw [e] at h
      exact (mul_pos_iff_of_pos_right (by positivity)).mp h
    have hs1 : (Dim.mk D F).side E₁ ≠ 0 := by
      intro h
      rw [h, zero_mul] at hs12
      exact lt_irrefl 0 hs12
    have hE1D : E₁ ≠ D := by
      rintro rfl
      apply hs1
      simp [Dim.side, Dim.dir, cross]
    have hE2D : E₂ ≠ D := by
      rintro rfl
      apply (lt_irrefl (0 : ℝ))
      convert hs12 using 1
      simp [Dim.side, Dim.dir, cross]
    have hg1 := kleinInner_self_pos hD hE1D
    have hg2 := kleinInner_self_pos hD hE2D
    have hx : kleinInner κ D F E₁ / (√(kleinInner κ D F F) * √(kleinInner κ D E₁ E₁))
        = kleinInner κ D F E₂ / (√(kleinInner κ D F F) * √(kleinInner κ D E₂ E₂)) := by
      rw [← cos_kleinAngle hD hDF.symm hE1D, ← cos_kleinAngle hD hDF.symm hE2D, ha₁, ha₂]
    rw [div_eq_div_iff (by positivity) (by positivity)] at hx
    have hN : kleinInner κ D F E₁ * √(kleinInner κ D E₂ E₂)
        = kleinInner κ D F E₂ * √(kleinInner κ D E₁ E₁) := by
      apply mul_left_cancel₀ (sqrt_pos.mpr hgU).ne'
      linear_combination hx
    have hsq : kleinInner κ D F E₁ ^ 2 * kleinInner κ D E₂ E₂
        = kleinInner κ D F E₂ ^ 2 * kleinInner κ D E₁ E₁ := by
      have h := congrArg (· ^ 2) hN
      simp only [mul_pow, sq_sqrt hg1.le, sq_sqrt hg2.le] at h
      exact h
    have hNN : 0 ≤ kleinInner κ D F E₁ * kleinInner κ D F E₂ := by
      have h : kleinInner κ D F E₁ * kleinInner κ D F E₂ * √(kleinInner κ D E₂ E₂)
          = kleinInner κ D F E₂ ^ 2 * √(kleinInner κ D E₁ E₁) := by
        linear_combination (kleinInner κ D F E₂) * hN
      have h' : 0 ≤ kleinInner κ D F E₁ * kleinInner κ D F E₂ * √(kleinInner κ D E₂ E₂) := by
        rw [h]
        positivity
      exact (mul_nonneg_iff_of_pos_right (sqrt_pos.mpr hg2)).mp h'
    have gram1 := kleinInner_gram κ D F E₁
    have gram2 := kleinInner_gram κ D F E₂
    have hmain : (kleinInner κ D F E₁ * (Dim.mk D F).side E₂) ^ 2
        = (kleinInner κ D F E₂ * (Dim.mk D F).side E₁) ^ 2 := by
      apply mul_left_cancel₀ hBD.ne'
      linear_combination kleinInner κ D F F * hsq - kleinInner κ D F E₁ ^ 2 * gram2
        + kleinInner κ D F E₂ ^ 2 * gram1
    have hprod : 0 ≤ (kleinInner κ D F E₁ * (Dim.mk D F).side E₂)
        * (kleinInner κ D F E₂ * (Dim.mk D F).side E₁) := by
      have e : (kleinInner κ D F E₁ * (Dim.mk D F).side E₂)
          * (kleinInner κ D F E₂ * (Dim.mk D F).side E₁)
          = kleinInner κ D F E₁ * kleinInner κ D F E₂
            * ((Dim.mk D F).side E₁ * (Dim.mk D F).side E₂) := by ring
      rw [e]
      exact mul_nonneg hNN hs12.le
    have heq : kleinInner κ D F E₁ * (Dim.mk D F).side E₂
        = kleinInner κ D F E₂ * (Dim.mk D F).side E₁ := by
      have h1 : (kleinInner κ D F E₁ * (Dim.mk D F).side E₂
          - kleinInner κ D F E₂ * (Dim.mk D F).side E₁)
          * (kleinInner κ D F E₁ * (Dim.mk D F).side E₂
            + kleinInner κ D F E₂ * (Dim.mk D F).side E₁) = 0 := by
        linear_combination hmain
      rcases mul_eq_zero.mp h1 with h | h
      · linarith
      · have ha : kleinInner κ D F E₁ * (Dim.mk D F).side E₂
            = -(kleinInner κ D F E₂ * (Dim.mk D F).side E₁) := by linarith
        rw [ha] at hprod
        have hb : kleinInner κ D F E₂ * (Dim.mk D F).side E₁ = 0 := by
          nlinarith only [hprod, sq_nonneg (kleinInner κ D F E₂ * (Dim.mk D F).side E₁)]
        rw [ha, hb]
        ring
    have hplucker : kleinInner κ D F F * (Dim.mk D E₁).side E₂
        = kleinInner κ D F E₁ * (Dim.mk D F).side E₂
          - kleinInner κ D F E₂ * (Dim.mk D F).side E₁ := by
      simp only [kleinInner, Dim.side, Dim.dir, cross]
      ring
    have hcross : (Dim.mk D E₁).side E₂ = 0 := by
      have h : kleinInner κ D F F * (Dim.mk D E₁).side E₂ = 0 := by
        rw [hplucker, heq, sub_self]
      exact (mul_eq_zero.mp h).resolve_left hgU.ne'
    have hv1 : ((E₁.1 - D.1, E₁.2 - D.2) : ℝ × ℝ) ≠ (0, 0) := by
      intro h
      apply hE1D
      have h1 := congrArg Prod.fst h
      have h2 := congrArg Prod.snd h
      simp only [] at h1 h2
      exact Prod.ext (by linarith) (by linarith)
    obtain ⟨l, hl⟩ := exists_mul_of_cross_eq_zero hv1 hcross
    have h1 := congrArg Prod.fst hl
    have h2 := congrArg Prod.snd hl
    simp only [] at h1 h2
    have hs2l : (Dim.mk D F).side E₂ = l * (Dim.mk D F).side E₁ := by
      simp only [Dim.side, Dim.dir, cross]
      linear_combination (F.1 - D.1) * h2 - (F.2 - D.2) * h1
    have hl0 : 0 < l := by
      have h : 0 < l * (Dim.mk D F).side E₁ ^ 2 := by
        have e : l * (Dim.mk D F).side E₁ ^ 2
            = (Dim.mk D F).side E₁ * (Dim.mk D F).side E₂ := by
          rw [hs2l]
          ring
        rw [e]
        exact hs12
      exact (mul_pos_iff_of_pos_right (by positivity)).mp h
    refine ⟨l, hl0, Prod.ext ?_ ?_⟩
    · simp only [Dim.pt]
      linarith
    · simp only [Dim.pt]
      linarith

end Congruence

section Apart

open Real

/-! ## A ray, as Hilbert has it -/

/-- A point on the ray, as Hilbert has it, is on the ray as `OnRay` has it. -/
theorem onRay_of_between {O A X : ℝ × ℝ} (h : X = A ∨ Between O X A ∨ Between O A X) :
    OnRay O A X := by
  rcases h with rfl | ⟨-, u, hu0, -, hu⟩ | ⟨-, u, hu0, -, hu⟩
  · exact ⟨1, one_pos, (Dim.pt_one (Dim.mk O X)).symm⟩
  · exact ⟨u, hu0, hu.symm⟩
  · refine ⟨1 / u, by positivity, ?_⟩
    have h1 := congrArg Prod.fst hu
    have h2 := congrArg Prod.snd hu
    simp only [Dim.pt] at h1 h2
    apply Prod.ext
    · simp only [Dim.pt]
      rw [← h1]
      field_simp
      ring
    · simp only [Dim.pt]
      rw [← h2]
      field_simp
      ring

/-- A point on the ray as `OnRay` has it is on the ray, as Hilbert has it. -/
theorem between_of_onRay {O A X : ℝ × ℝ} (hOA : O ≠ A) (h : OnRay O A X) :
    X = A ∨ Between O X A ∨ Between O A X := by
  obtain ⟨t, ht, rfl⟩ := h
  rcases lt_trichotomy t 1 with h1 | rfl | h1
  · exact Or.inr (Or.inl ⟨hOA, t, ht, h1, rfl⟩)
  · exact Or.inl (Dim.pt_one (Dim.mk O A))
  · refine Or.inr (Or.inr ⟨?_, 1 / t, by positivity, (div_lt_one ht).mpr h1, ?_⟩)
    · intro h
      apply hOA
      have e1 := congrArg Prod.fst h
      have e2 := congrArg Prod.snd h
      simp only [Dim.pt] at e1 e2
      have k1 : t * (A.1 - O.1) = 0 := by linarith
      have k2 : t * (A.2 - O.2) = 0 := by linarith
      apply Prod.ext
      · linarith [(mul_eq_zero.mp k1).resolve_left ht.ne']
      · linarith [(mul_eq_zero.mp k2).resolve_left ht.ne']
    · apply Prod.ext
      · simp only [Dim.pt]
        field_simp
        ring
      · simp only [Dim.pt]
        field_simp
        ring

/-! ## Euclid's plane: congruence with `apart` under the bound 0 -/

theorem mem_plane_zero (p : ℝ × ℝ) : p ∈ plane (0 : ℝ) := by
  rw [plane_zero]
  trivial

theorem apart_zero_nonneg (P Q : ℝ × ℝ) : 0 ≤ apart 0 P Q := by
  rw [apart_zero_bound]
  positivity

theorem apart_zero_eq_kleinInner (P Q : ℝ × ℝ) : apart 0 P Q = kleinInner 0 P Q Q := by
  rw [apart_zero_bound]
  simp only [kleinInner, zero_mul, add_zero]
  ring

/-- Under the bound 0, on a ray there is one point at a given `apart` from its origin. -/
theorem euclid_segment_construction {A B O D : ℝ × ℝ} (hAB : A ≠ B) (hOD : O ≠ D) :
    ∃! X, X ∈ plane (0 : ℝ) ∧ OnRay O D X ∧ apart 0 A B = apart 0 O X := by
  have hα : 0 < apart 0 A B := apart_pos (mem_plane_zero A) (mem_plane_zero B) hAB
  have hV : 0 < (D.1 - O.1) ^ 2 + (D.2 - O.2) ^ 2 := by
    have hne : ((D.1 - O.1, D.2 - O.2) : ℝ × ℝ) ≠ (0, 0) := by
      intro h
      apply hOD
      have h1 := congrArg Prod.fst h
      have h2 := congrArg Prod.snd h
      simp only [] at h1 h2
      exact Prod.ext (by linarith) (by linarith)
    exact sq_add_sq_pos hne
  have hray : ∀ t : ℝ, apart 0 O ((Dim.mk O D).pt t)
      = t ^ 2 * ((D.1 - O.1) ^ 2 + (D.2 - O.2) ^ 2) := by
    intro t
    rw [apart_zero_bound]
    simp only [Dim.pt]
    ring
  have ht0 : 0 < √(apart 0 A B / ((D.1 - O.1) ^ 2 + (D.2 - O.2) ^ 2)) :=
    sqrt_pos.mpr (div_pos hα hV)
  have ht2 : √(apart 0 A B / ((D.1 - O.1) ^ 2 + (D.2 - O.2) ^ 2)) ^ 2
      = apart 0 A B / ((D.1 - O.1) ^ 2 + (D.2 - O.2) ^ 2) := sq_sqrt (div_pos hα hV).le
  refine ⟨(Dim.mk O D).pt (√(apart 0 A B / ((D.1 - O.1) ^ 2 + (D.2 - O.2) ^ 2))),
    ⟨mem_plane_zero _, ⟨_, ht0, rfl⟩, ?_⟩, ?_⟩
  · rw [hray, ht2, div_mul_cancel₀ _ hV.ne']
  · rintro Y ⟨-, ⟨s, hs, rfl⟩, hY⟩
    rw [hray] at hY
    have hs2 : s ^ 2 = √(apart 0 A B / ((D.1 - O.1) ^ 2 + (D.2 - O.2) ^ 2)) ^ 2 := by
      rw [ht2, eq_div_iff hV.ne']
      linarith
    rw [(pow_left_inj₀ hs.le ht0.le two_ne_zero).mp hs2]

/-- Under the bound 0, the square roots of `apart` add along a segment. -/
theorem euclid_sqrt_apart_add {A B C : ℝ × ℝ} (h : Between A B C) :
    √(apart 0 A C) = √(apart 0 A B) + √(apart 0 B C) := by
  obtain ⟨-, u, hu0, hu1, rfl⟩ := h
  have e1 : apart 0 A ((Dim.mk A C).pt u) = u ^ 2 * apart 0 A C := by
    rw [apart_zero_bound, apart_zero_bound]
    simp only [Dim.pt]
    ring
  have e2 : apart 0 ((Dim.mk A C).pt u) C = (1 - u) ^ 2 * apart 0 A C := by
    rw [apart_zero_bound, apart_zero_bound]
    simp only [Dim.pt]
    ring
  rw [e1, e2, sqrt_mul (sq_nonneg _), sqrt_mul (sq_nonneg _), sqrt_sq hu0.le,
    sqrt_sq (by linarith)]
  ring

/-- Addition of segments under the bound 0. -/
theorem euclid_segment_addition {A B C D E F : ℝ × ℝ} (hABC : Between A B C)
    (hDEF : Between D E F) (h1 : apart 0 A B = apart 0 D E) (h2 : apart 0 B C = apart 0 E F) :
    apart 0 A C = apart 0 D F := by
  have h := euclid_sqrt_apart_add hABC
  rw [h1, h2, ← euclid_sqrt_apart_add hDEF] at h
  exact (sqrt_inj (apart_zero_nonneg _ _) (apart_zero_nonneg _ _)).mp h

/-- The law of cosines under the bound 0. -/
theorem euclid_law_of_cosines {A B C : ℝ × ℝ} (hB : B ≠ A) (hC : C ≠ A) :
    apart 0 B C = apart 0 A B + apart 0 A C
      - 2 * (√(apart 0 A B) * √(apart 0 A C)) * cos (kleinAngle 0 A B C) := by
  have hgB := sqrt_pos.mpr (kleinInner_self_pos (mem_plane_zero A) hB)
  have hgC := sqrt_pos.mpr (kleinInner_self_pos (mem_plane_zero A) hC)
  have e : apart 0 B C = kleinInner 0 A B B + kleinInner 0 A C C - 2 * kleinInner 0 A B C := by
    rw [apart_zero_bound]
    simp only [kleinInner, zero_mul, add_zero]
    ring
  rw [e, apart_zero_eq_kleinInner A B, apart_zero_eq_kleinInner A C,
    cos_kleinAngle (mem_plane_zero A) hB hC]
  field_simp

/-- Side, angle, side under the bound 0. -/
theorem euclid_sas {A B C D E F : ℝ × ℝ} (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C)
    (hDE : D ≠ E) (hDF : D ≠ F) (hEF : E ≠ F) (h1 : apart 0 A B = apart 0 D E)
    (h2 : apart 0 A C = apart 0 D F) (h3 : kleinAngle 0 A B C = kleinAngle 0 D E F) :
    apart 0 B C = apart 0 E F ∧ kleinAngle 0 B A C = kleinAngle 0 E D F ∧
      kleinAngle 0 C A B = kleinAngle 0 F D E := by
  have hBCEF : apart 0 B C = apart 0 E F := by
    rw [euclid_law_of_cosines hAB.symm hAC.symm, euclid_law_of_cosines hDE.symm hDF.symm, h1, h2,
      h3]
  have angle_eq : ∀ {P Q R P' Q' R' : ℝ × ℝ}, Q ≠ P → R ≠ P → Q' ≠ P' → R' ≠ P' →
      apart 0 P Q = apart 0 P' Q' → apart 0 P R = apart 0 P' R' →
      apart 0 Q R = apart 0 Q' R' → kleinAngle 0 P Q R = kleinAngle 0 P' Q' R' := by
    intro P Q R P' Q' R' hQ hR hQ' hR' e1 e2 e3
    have l := euclid_law_of_cosines hQ hR
    have l' := euclid_law_of_cosines hQ' hR'
    rw [e1, e2, e3] at l
    have hpos : 0 < 2 * (√(apart 0 P' Q') * √(apart 0 P' R')) := by
      have := sqrt_pos.mpr (apart_pos (mem_plane_zero P') (mem_plane_zero Q') hQ'.symm)
      have := sqrt_pos.mpr (apart_pos (mem_plane_zero P') (mem_plane_zero R') hR'.symm)
      positivity
    have hcos : cos (kleinAngle 0 P Q R) = cos (kleinAngle 0 P' Q' R') :=
      mul_left_cancel₀ hpos.ne' (by linarith)
    rw [kleinAngle_eq_arccos_cos 0 P Q R, kleinAngle_eq_arccos_cos 0 P' Q' R', hcos]
  refine ⟨hBCEF, ?_, ?_⟩
  · exact angle_eq hAB hBC.symm hDE hEF.symm (by rw [apart_comm, h1, apart_comm]) hBCEF h2
  · exact angle_eq hAC hBC hDF hEF (by rw [apart_comm, h2, apart_comm])
      (by rw [apart_comm, hBCEF, apart_comm]) h1

/-! ## The plane of a bound that is not positive: congruence with `apart` -/

theorem apart_eq_iff_kleinDist_eq {κ : ℝ} (hκ : κ < 0) {A B C D : ℝ × ℝ} (hA : A ∈ plane κ)
    (hB : B ∈ plane κ) (hC : C ∈ plane κ) (hD : D ∈ plane κ) :
    apart κ A B = apart κ C D ↔ kleinDist κ A B = kleinDist κ C D := by
  constructor
  · intro h
    rw [kleinDist_eq_arsinh hκ hA hB, kleinDist_eq_arsinh hκ hC hD, h]
  · intro h
    rw [apart_eq_sinh_kleinDist hκ hA hB, apart_eq_sinh_kleinDist hκ hC hD, h]

/-- C1 with `apart`, under a bound that is not positive. -/
theorem segment_construction_apart {κ : ℝ} (hκ : κ ≤ 0) {A B O D : ℝ × ℝ} (hA : A ∈ plane κ)
    (hB : B ∈ plane κ) (hO : O ∈ plane κ) (hAB : A ≠ B) (hOD : O ≠ D) :
    ∃! X, X ∈ plane κ ∧ OnRay O D X ∧ apart κ A B = apart κ O X := by
  rcases hκ.lt_or_eq with h | rfl
  · obtain ⟨X, ⟨hX, hray, hd⟩, huniq⟩ := segment_construction h hA hB hO hAB hOD
    exact ⟨X, ⟨hX, hray, (apart_eq_iff_kleinDist_eq h hA hB hO hX).mpr hd⟩,
      fun Y ⟨hY, hrY, haY⟩ => huniq Y ⟨hY, hrY, (apart_eq_iff_kleinDist_eq h hA hB hO hY).mp haY⟩⟩
  · exact euclid_segment_construction hAB hOD

/-- C3 with `apart`, under a bound that is not positive. -/
theorem segment_addition_apart {κ : ℝ} (hκ : κ ≤ 0) {A B C D E F : ℝ × ℝ} (hA : A ∈ plane κ)
    (hC : C ∈ plane κ) (hD : D ∈ plane κ) (hF : F ∈ plane κ) (hABC : Between A B C)
    (hDEF : Between D E F) (h1 : apart κ A B = apart κ D E) (h2 : apart κ B C = apart κ E F) :
    apart κ A C = apart κ D F := by
  rcases hκ.lt_or_eq with h | rfl
  · have hB := (kleinDist_add_of_between h hA hC hABC).1
    have hE := (kleinDist_add_of_between h hD hF hDEF).1
    rw [apart_eq_iff_kleinDist_eq h hA hC hD hF]
    exact segment_addition h hA hC hD hF hABC hDEF
      ((apart_eq_iff_kleinDist_eq h hA hB hD hE).mp h1)
      ((apart_eq_iff_kleinDist_eq h hB hC hE hF).mp h2)
  · exact euclid_segment_addition hABC hDEF h1 h2

/-- C6 with `apart`, under a bound that is not positive. -/
theorem sas_apart {κ : ℝ} (hκ : κ ≤ 0) {A B C D E F : ℝ × ℝ} (hA : A ∈ plane κ)
    (hB : B ∈ plane κ) (hC : C ∈ plane κ) (hD : D ∈ plane κ) (hE : E ∈ plane κ)
    (hF : F ∈ plane κ) (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C) (hDE : D ≠ E) (hDF : D ≠ F)
    (hEF : E ≠ F) (h1 : apart κ A B = apart κ D E) (h2 : apart κ A C = apart κ D F)
    (h3 : kleinAngle κ A B C = kleinAngle κ D E F) :
    apart κ B C = apart κ E F ∧ kleinAngle κ B A C = kleinAngle κ E D F ∧
      kleinAngle κ C A B = kleinAngle κ F D E := by
  rcases hκ.lt_or_eq with h | rfl
  · obtain ⟨e1, e2, e3⟩ := side_angle_side h hA hB hC hD hE hF hAB hAC hBC hDE hDF hEF
      ((apart_eq_iff_kleinDist_eq h hA hB hD hE).mp h1)
      ((apart_eq_iff_kleinDist_eq h hA hC hD hF).mp h2) h3
    exact ⟨(apart_eq_iff_kleinDist_eq h hB hC hE hF).mpr e1, e2, e3⟩
  · exact euclid_sas hAB hAC hBC hDE hDF hEF h1 h2 h3

end Apart

end HyperbolicPlane

end ParallelPostulate

/-!
# The figure of the three-dimensions section under the bound `-1`

Example H10 lays the figure of the three-dimensions section in the plane of the bound `-1`, with
fractions for numbers: it meets the hypotheses of the postulate there, and its lines `b` and `c`
meet only outside the plane. Theorem H14 lays the same figure among the pairs of real numbers,
measures its two interior angles with `kleinAngle`, a right angle and the angle whose cosine is
`3 / √409`, and so shows that Euclid's fifth postulate, as he states it, fails under the bound
`-1`.

## Contents

* Example H10, the figure of the three-dimensions section under the bound `-1`: `leaningFigure`,
  `leaningFigure_within`, `leaningFigure_values`, `leaningFigure_hypotheses`,
  `leaningFigure_numbers`, `leaningFigure_meets_beyond`, `leaningFigure_never_meets`,
  `leaningFigure_angles`
* Theorem H14, Euclid's fifth postulate fails under the bound `-1`: `EuclidFifth`,
  `realLeaningFigure`, `realLeaningFigure_within`, `realLeaningFigure_sides`,
  `realLeaningFigure_angle_a0`, `realLeaningFigure_angle_a1`, `realLeaningFigure_angle_a1_lt`,
  `realLeaningFigure_angles`, `realLeaningFigure_never_meets`, `not_euclidFifth`
-/

namespace ParallelPostulate

namespace HyperbolicPlane

open Pairs

/-! ## The figure of the three-dimensions section under the bound -/

/-- A figure within the bound `-1`. `a` runs from `(0, 0)` to `(3/5, 0)`, `b` leaves `a0`
straight up, and `c` leaves `a1` leaning toward `b`. -/
@[expose] def leaningFigure : Figure ℚ where
  a := ⟨(0, 0), (3 / 5, 0)⟩
  b := ⟨(0, 0), (0, 1 / 2)⟩
  c := ⟨(3 / 5, 0), (27 / 50, 1 / 2)⟩
  a0_eq_b0 := rfl
  a1_eq_c0 := rfl

/-- Its zeros and its 1s are points of the plane of the bound `-1`. -/
theorem leaningFigure_within :
    leaningFigure.a.zero ∈ plane (-1 : ℚ) ∧ leaningFigure.a.one ∈ plane (-1 : ℚ) ∧
      leaningFigure.b.one ∈ plane (-1 : ℚ) ∧ leaningFigure.c.one ∈ plane (-1 : ℚ) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num [leaningFigure, plane]

/-- The sides of `b1` and of `c1`, and the cross product of the directions of `b` and `c`. -/
theorem leaningFigure_values :
    leaningFigure.a.side leaningFigure.b.one = 3 / 10 ∧
      leaningFigure.a.side leaningFigure.c.one = 3 / 10 ∧
      cross leaningFigure.b.dir leaningFigure.c.dir = 3 / 100 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [leaningFigure, Dim.side, Dim.dir, cross]

/-- It meets the three hypotheses of Theorem E4 (the three-dimensions section). -/
theorem leaningFigure_hypotheses :
    0 < leaningFigure.a.side leaningFigure.b.one ∧
      0 < leaningFigure.a.side leaningFigure.c.one ∧
      0 < cross leaningFigure.b.dir leaningFigure.c.dir := by
  obtain ⟨h1, h2, h3⟩ := leaningFigure_values
  rw [h1, h2, h3]
  norm_num

/-- The two numbers at which Theorem E4 (the three-dimensions section) has `b` and `c` meet are both
10. -/
theorem leaningFigure_numbers :
    cross leaningFigure.a.dir leaningFigure.c.dir / cross leaningFigure.b.dir leaningFigure.c.dir
        = 10 ∧
      cross leaningFigure.a.dir leaningFigure.b.dir
          / cross leaningFigure.b.dir leaningFigure.c.dir = 10 := by
  refine ⟨?_, ?_⟩ <;> norm_num [leaningFigure, Dim.dir, cross]

/-- As dimensions, `b` and `c` meet at the number 10 of each, at the pair `(0, 5)`, which is
not a point of the plane. -/
theorem leaningFigure_meets_beyond :
    leaningFigure.b.pt 10 = (0, 5) ∧ leaningFigure.c.pt 10 = (0, 5) ∧
      ((0 : ℚ), (5 : ℚ)) ∉ plane (-1 : ℚ) := by
  refine ⟨?_, ?_, ?_⟩
  · apply Prod.ext <;> norm_num [leaningFigure, Dim.pt]
  · apply Prod.ext <;> norm_num [leaningFigure, Dim.pt]
  · norm_num [plane]

/-- **In the plane of the bound `-1` the lines of `b` and `c` do not meet.** -/
theorem leaningFigure_never_meets :
    (leaningFigure.b.points ∩ plane (-1 : ℚ)) ∩ (leaningFigure.c.points ∩ plane (-1 : ℚ))
      = ∅ := by
  apply Set.eq_empty_of_forall_notMem
  rintro X ⟨⟨⟨t, rfl⟩, hX⟩, ⟨⟨u, hu⟩, -⟩⟩
  have e1 := congrArg Prod.fst hu
  have e2 := congrArg Prod.snd hu
  simp only [leaningFigure, Dim.pt] at e1 e2
  have hu10 : u = 10 := by linarith
  have ht10 : t = 10 := by linarith
  rw [ht10] at hX
  rw [leaningFigure_meets_beyond.1] at hX
  exact leaningFigure_meets_beyond.2.2 hX

/-- **The two interior angles of the figure, as far as numbers can show them.** At `a0`, which
is `(0, 0)`, the directions of `a` and `b` have the inner product 0. The motion along the first
axis with `a = -3/5` and `w = 4/5` takes `a1` to `(0, 0)`, `a0` to `(-3/5, 0)`, and `c1` to
`(-15/169, 100/169)`. So after the motion `c` leaves `(0, 0)`, and the inner product of its
direction with the direction of `a` run backwards is positive. -/
theorem leaningFigure_angles :
    leaningFigure.a.dir.1 * leaningFigure.b.dir.1
        + leaningFigure.a.dir.2 * leaningFigure.b.dir.2 = 0 ∧
      ((4 / 5 : ℚ)) ^ 2 = 1 + (-1) * (-3 / 5) ^ 2 ∧
      shift (-1 : ℚ) (-3 / 5) (4 / 5) leaningFigure.a.one = (0, 0) ∧
      shift (-1 : ℚ) (-3 / 5) (4 / 5) leaningFigure.a.zero = (-3 / 5, 0) ∧
      shift (-1 : ℚ) (-3 / 5) (4 / 5) leaningFigure.c.one = (-15 / 169, 100 / 169) ∧
      (0 : ℚ) < (-15 / 169) * (-3 / 5) + (100 / 169) * 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num [leaningFigure, Dim.dir]
  · norm_num
  · apply Prod.ext <;> norm_num [leaningFigure, shift]
  · apply Prod.ext <;> norm_num [leaningFigure, shift]
  · apply Prod.ext <;> norm_num [leaningFigure, shift]
  · norm_num

/-! ## Euclid's fifth postulate under the bound `-1`

The figure of Example H10, with real numbers, and its two interior angles measured with
`kleinAngle`. -/

section KleinFifth

open Real

/-- **Euclid's fifth postulate in the plane of the bound `κ`**, with the angles of
`kleinAngle`. Let `a` fall on `b` and `c`, with its zero, its 1, and `b1` and `c1` points of the
plane. Let `b1` and `c1` lie on the left of `a`, and let the two interior angles on that side be
together less than two right angles. Then `b` and `c`, produced on that side, meet at a point of
the plane, on that side. -/
@[expose] def EuclidFifth (κ : ℝ) : Prop :=
  ∀ F : Figure ℝ, F.a.zero ∈ plane κ → F.a.one ∈ plane κ → F.b.one ∈ plane κ →
    F.c.one ∈ plane κ → 0 < F.a.side F.b.one → 0 < F.a.side F.c.one →
    kleinAngle κ F.a.zero F.a.one F.b.one + kleinAngle κ F.a.one F.a.zero F.c.one < π →
    ∃ t u : ℝ, 0 < t ∧ 0 < u ∧ F.b.pt t = F.c.pt u ∧ F.b.pt t ∈ plane κ ∧
      0 < F.a.side (F.b.pt t)

/-- The figure of Example H10, with real numbers. -/
@[expose] noncomputable def realLeaningFigure : Figure ℝ where
  a := ⟨(0, 0), (3 / 5, 0)⟩
  b := ⟨(0, 0), (0, 1 / 2)⟩
  c := ⟨(3 / 5, 0), (27 / 50, 1 / 2)⟩
  a0_eq_b0 := rfl
  a1_eq_c0 := rfl

/-- Its zeros and its 1s are points of the plane of the bound `-1`. -/
theorem realLeaningFigure_within :
    realLeaningFigure.a.zero ∈ plane (-1 : ℝ) ∧ realLeaningFigure.a.one ∈ plane (-1 : ℝ) ∧
      realLeaningFigure.b.one ∈ plane (-1 : ℝ) ∧ realLeaningFigure.c.one ∈ plane (-1 : ℝ) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num [realLeaningFigure, plane]

/-- `b1` and `c1` lie on the left of `a`. -/
theorem realLeaningFigure_sides :
    0 < realLeaningFigure.a.side realLeaningFigure.b.one ∧
      0 < realLeaningFigure.a.side realLeaningFigure.c.one := by
  refine ⟨?_, ?_⟩ <;> norm_num [realLeaningFigure, Dim.side, Dim.dir, cross]

/-- **The interior angle at `a0` is a right angle.** -/
theorem realLeaningFigure_angle_a0 :
    kleinAngle (-1) realLeaningFigure.a.zero realLeaningFigure.a.one realLeaningFigure.b.one
      = π / 2 := by
  have h : kleinInner (-1) realLeaningFigure.a.zero realLeaningFigure.a.one
      realLeaningFigure.b.one = 0 := by
    norm_num [realLeaningFigure, kleinInner, cross]
  rw [kleinAngle, h, zero_div, arccos_zero]

/-- **The interior angle at `a1`** is the angle whose cosine is `3 / √409`, about 81.5 degrees.
With the angles of Euclid it would be the angle whose cosine is `3 / √634`. -/
theorem realLeaningFigure_angle_a1 :
    kleinAngle (-1) realLeaningFigure.a.one realLeaningFigure.a.zero realLeaningFigure.c.one
      = arccos (3 / √409) := by
  have h : kleinInner (-1) realLeaningFigure.a.one realLeaningFigure.a.zero
      realLeaningFigure.c.one = 9 / 250 := by
    norm_num [realLeaningFigure, kleinInner, cross]
  have h1 : kleinInner (-1) realLeaningFigure.a.one realLeaningFigure.a.zero
      realLeaningFigure.a.zero = (3 / 5) ^ 2 := by
    norm_num [realLeaningFigure, kleinInner, cross]
  have h2 : kleinInner (-1) realLeaningFigure.a.one realLeaningFigure.c.one
      realLeaningFigure.c.one = 409 / 50 ^ 2 := by
    norm_num [realLeaningFigure, kleinInner, cross]
  have hs : 0 < √409 := by positivity
  rw [kleinAngle, h, h1, h2, sqrt_sq (by norm_num), sqrt_div' _ (by norm_num),
    sqrt_sq (by norm_num)]
  congr 1
  field_simp
  norm_num

/-- The interior angle at `a1` is less than a right angle. -/
theorem realLeaningFigure_angle_a1_lt :
    kleinAngle (-1) realLeaningFigure.a.one realLeaningFigure.a.zero realLeaningFigure.c.one
      < π / 2 := by
  rw [realLeaningFigure_angle_a1, arccos_lt_pi_div_two]
  positivity

/-- **The two interior angles are together less than two right angles.** -/
theorem realLeaningFigure_angles :
    kleinAngle (-1) realLeaningFigure.a.zero realLeaningFigure.a.one realLeaningFigure.b.one
      + kleinAngle (-1) realLeaningFigure.a.one realLeaningFigure.a.zero realLeaningFigure.c.one
      < π := by
  rw [realLeaningFigure_angle_a0]
  linarith [realLeaningFigure_angle_a1_lt]

/-- **In the plane of the bound `-1` the lines of `b` and `c` do not meet**, on either side
of `a`. As dimensions they meet at the pair `(0, 5)`, which is not a point of the plane. -/
theorem realLeaningFigure_never_meets :
    (realLeaningFigure.b.points ∩ plane (-1 : ℝ)) ∩ (realLeaningFigure.c.points ∩ plane (-1 : ℝ))
      = ∅ := by
  apply Set.eq_empty_of_forall_notMem
  rintro X ⟨⟨⟨t, rfl⟩, hX⟩, ⟨⟨u, hu⟩, -⟩⟩
  have e1 := congrArg Prod.fst hu
  have e2 := congrArg Prod.snd hu
  simp only [realLeaningFigure, Dim.pt] at e1 e2
  have hu10 : u = 10 := by linarith
  have ht10 : t = 10 := by linarith
  rw [ht10] at hX
  norm_num [realLeaningFigure, Dim.pt, plane] at hX

/-- **Theorem H14. Euclid's fifth postulate fails in the plane of the bound `-1`.** The figure
of Example H10 meets every hypothesis: its points are points of the plane, `b1` and `c1` lie on
the left of `a`, and the two interior angles on that side, a right angle and the angle whose
cosine is `3 / √409`, are together less than two right angles. But `b` and `c` have no point of
the plane in common. -/
theorem not_euclidFifth : ¬ EuclidFifth (-1) := by
  intro h
  obtain ⟨h0, h1, hb, hc⟩ := realLeaningFigure_within
  obtain ⟨sb, sc⟩ := realLeaningFigure_sides
  obtain ⟨t, u, -, -, htu, ht, -⟩ :=
    h realLeaningFigure h0 h1 hb hc sb sc realLeaningFigure_angles
  have hmem : realLeaningFigure.b.pt t ∈ (realLeaningFigure.b.points ∩ plane (-1 : ℝ))
      ∩ (realLeaningFigure.c.points ∩ plane (-1 : ℝ)) :=
    ⟨⟨⟨t, rfl⟩, ht⟩, ⟨⟨u, htu.symm⟩, ht⟩⟩
  rw [realLeaningFigure_never_meets] at hmem
  exact hmem

end KleinFifth

end HyperbolicPlane

end ParallelPostulate
