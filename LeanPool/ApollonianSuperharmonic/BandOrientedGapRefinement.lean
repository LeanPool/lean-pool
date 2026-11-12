/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BandPackingExterior
public import LeanPool.ApollonianSuperharmonic.ProperBandQuadruple

-- [TABLET NODE: BandOrientedGapRefinement]

/-!
# BandOrientedGapRefinement

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
An oriented band-gap refinement certificate consists of closed sets
$G(a,\sigma,w)$ indexed by a Gaussian integer $a$, a side
$\sigma\in\{-,+\}$, and a finite word $w\in\{0,1,2\}^*$, together with a
positive band circle $K(a,\sigma,w)$ and a proper ordered Descartes
presentation $q(a,\sigma,w)$, satisfying the following conditions.

For $a=x+iy$, the two root sets are the closures
$$
\begin{split}
G(a,-,\varnothing)=\{(X,Y):&,2x\le X\le2x+1, 2y\le Y\le2y+2,\\
 &(X-1-2x)^2+(Y-2y)^2\ge1,\\
 &(X-1-2x)^2+(Y-2y-2)^2\ge1\},
\end{split}
$$
and the analogous set $G(a,+,\varnothing)$ with
$2x+1\le X\le2x+2$.  These root gaps cover the exterior of all open band
disks.  Their ordered boundary lists contain, respectively, the oriented
line $(0,-1)$ or $(0,1)$ and the two unit coordinates
$(1,1+2a)$ and $(1,1+2a+2i)$ in the displayed cyclic order.

For every index $\iota$, $q(\iota)$ is proper, its child is $K(\iota)$,
and the presentations at $\iota0,\iota1,\iota2$ are exactly the successor
presentations obtained after zero, one, or two cyclic parent rotations.
Moreover
$$
G(\iota)=\overline{B(K(\iota))}\cup
G(\iota0)\cup G(\iota1)\cup G(\iota2),
$$
each residual gap is contained in $G(\iota)$, and the interiors of the
three residual gaps are pairwise disjoint.  The whole boundary of the
inserted disk is covered by the three residual closures.  Quantitatively,
$$
 \operatorname{diam}G(\iota)\le6\sqrt{R_{K(\iota)}}.
$$

Along every infinite branch both the Euclidean diameter of the closed gaps
and the radius of their inserted circles tend to zero.

The remaining data are local incidence data.  For each positive band
circle $C$, there is a finite set $S_C$ of gap indices such that the sets
$$
                 A_\iota=G(\iota)\cap\partial C
                 \qquad(\iota\in S_C)
$$
are nonempty closed connected arcs, every $q(\iota)$ retains $C$ in one
of its three parent slots, and $\partial C=\bigcup_{\iota\in S_C}A_\iota$.
If $q(\iota)$ retains $C$ and $p\in A_\iota$, let $K(\iota)$ be the
circle inserted in $G(\iota)$.  Exactly two of the three child
presentations retain $C$; call their digit set $E\subset\{0,1,2\}$.  Thus
$|E|=2$, and the retained parent criterion is exact:
$$
 b\in E\quad\Longleftrightarrow\quad
 C\text{ occurs in a parent slot of }q(\iota b).
$$
Their closed connected boundary arcs split the old arc exactly,
$$
 G(\iota)\cap\partial C
   =\bigcup_{b\in E}\bigl(G(\iota b)\cap\partial C\bigr).
$$
Both child arcs contain the contact point $t$ of $C$ with $K(\iota)$,
and at least one contains $p$.  The data record
$K(\iota)\ne C$, $R_{K(\iota)}<R_C$, and the exact contact equations
$$
 |t-z_C|=R_C,\qquad |t-z_{K(\iota)}|=R_{K(\iota)},\qquad
 |z_C-z_{K(\iota)}|=R_C+R_{K(\iota)}.
$$
No infinite incident sequence or density conclusion is part of the
certificate.
-/
structure BandOrientedGapRefinement where
-- BODY
  /-- The closed residual gap at a root, side and finite refinement word. -/
  gap : GaussianInt × Bool × List (Fin 3) → Set Complex
  gap_closed : ∀ ι, IsClosed (gap ι)
  /-- The positive circle inserted at each refinement index. -/
  circle : GaussianInt × Bool × List (Fin 3) → BandCircle
  /-- The ordered proper presentation of the circle inserted at each index. -/
  presentation : GaussianInt × Bool × List (Fin 3) → Fin 4 → CircleCoordinates
  root_cover : ∀ z : Complex, BandPackingExterior z →
    ∃ a : GaussianInt, ∃ side : Bool, z ∈ gap (a, side, [])
  root_left : ∀ a : GaussianInt,
    gap (a, false, []) = {z : Complex |
      2 * (a.re : Real) ≤ z.re ∧ z.re ≤ 2 * (a.re : Real) + 1 ∧
      2 * (a.im : Real) ≤ z.im ∧ z.im ≤ 2 * (a.im : Real) + 2 ∧
      1 ≤ dist z ((1 + 2 * a : GaussianInt) : Complex) ∧
      1 ≤ dist z ((1 + 2 * a + 2 * ⟨0, 1⟩ : GaussianInt) : Complex)}
  root_right : ∀ a : GaussianInt,
    gap (a, true, []) = {z : Complex |
      2 * (a.re : Real) + 1 ≤ z.re ∧ z.re ≤ 2 * (a.re : Real) + 2 ∧
      2 * (a.im : Real) ≤ z.im ∧ z.im ≤ 2 * (a.im : Real) + 2 ∧
      1 ≤ dist z ((1 + 2 * a : GaussianInt) : Complex) ∧
      1 ≤ dist z ((1 + 2 * a + 2 * ⟨0, 1⟩ : GaussianInt) : Complex)}
  proper : ∀ ι, ProperBandQuadruple (presentation ι)
  presented_circle : ∀ ι, (circle ι).1.1 = presentation ι 0
  root_oriented_lines : ∀ a side,
    let q := presentation (a, side, [])
    ((side = false ∧ q 0 = (4, 1 + 8 * a + 4 * ⟨0, 1⟩) ∧
        q 1 = (1, 1 + 2 * a) ∧ q 2 = (0, -1) ∧
        q 3 = (1, 1 + 2 * a + 2 * ⟨0, 1⟩)) ∨
      (side = true ∧ q 0 = (4, 7 + 8 * a + 4 * ⟨0, 1⟩) ∧
        q 1 = (1, 1 + 2 * a) ∧
        q 2 = (1, 1 + 2 * a + 2 * ⟨0, 1⟩) ∧ q 3 = (0, 1)))
  successor_slots : ∀ ι b,
    ∃ r : Fin 4 → CircleCoordinates,
      ((b = 0 ∧ r = presentation ι) ∨
       (b = 1 ∧ r = ![presentation ι 0, presentation ι 2,
              presentation ι 3, presentation ι 1]) ∨
       (b = 2 ∧ r = ![presentation ι 0, presentation ι 3,
              presentation ι 1, presentation ι 2])) ∧
      presentation (ι.1, ι.2.1, ι.2.2 ++ [b]) =
        ![(2 * (r 0).1 + 2 * (r 2).1 + 2 * (r 3).1 - (r 1).1,
            2 * (r 0).2 + 2 * (r 2).2 + 2 * (r 3).2 - (r 1).2),
          r 0, r 2, r 3]
  child_contained : ∀ ι b,
    gap (ι.1, ι.2.1, ι.2.2 ++ [b]) ⊆ gap ι
  exact_three_residual : ∀ ι,
    gap ι = Metric.closedBall (BandCircleEuclideanData (circle ι)).center
        (BandCircleEuclideanData (circle ι)).radius ∪
      ⋃ b : Fin 3, gap (ι.1, ι.2.1, ι.2.2 ++ [b])
  inserted_boundary_covered : ∀ ι,
    Metric.sphere (BandCircleEuclideanData (circle ι)).center
        (BandCircleEuclideanData (circle ι)).radius ⊆
      ⋃ b : Fin 3, gap (ι.1, ι.2.1, ι.2.2 ++ [b])
  residual_interiors_disjoint : ∀
      (ι : GaussianInt × Bool × List (Fin 3)) (b c : Fin 3), b ≠ c →
    interior (gap (ι.1, ι.2.1, ι.2.2 ++ [b])) ∩
      interior (gap (ι.1, ι.2.1, ι.2.2 ++ [c])) = ∅
  diameter_bound : ∀ ι,
    Metric.diam (gap ι) ≤
      6 * Real.sqrt (BandCircleEuclideanData (circle ι)).radius
  branch_shrinks : ∀ a side (branch : Nat → Fin 3),
    Filter.Tendsto
      (fun n ↦ Metric.diam (gap (a, side, (List.range n).map branch)))
      Filter.atTop (nhds 0) ∧
    Filter.Tendsto
      (fun n ↦ (BandCircleEuclideanData
        (circle (a, side, (List.range n).map branch))).radius)
      Filter.atTop (nhds 0)
  initial_incident_arcs : ∀ C : BandCircle,
    ∃ seeds : Finset (GaussianInt × Bool × List (Fin 3)),
      Metric.sphere (BandCircleEuclideanData C).center
          (BandCircleEuclideanData C).radius =
        ⋃ ι ∈ seeds, gap ι ∩
          Metric.sphere (BandCircleEuclideanData C).center
            (BandCircleEuclideanData C).radius ∧
      ∀ ι ∈ seeds,
        IsClosed (gap ι ∩ Metric.sphere (BandCircleEuclideanData C).center
          (BandCircleEuclideanData C).radius) ∧
        IsPreconnected (gap ι ∩
          Metric.sphere (BandCircleEuclideanData C).center
            (BandCircleEuclideanData C).radius) ∧
        (gap ι ∩ Metric.sphere (BandCircleEuclideanData C).center
          (BandCircleEuclideanData C).radius).Nonempty ∧
        ∃ j : Fin 3, presentation ι j.succ = C.1.1
  incident_arc_step : ∀ (C : BandCircle)
      (ι : GaussianInt × Bool × List (Fin 3)) (p : Complex),
    (∃ j : Fin 3, presentation ι j.succ = C.1.1) →
    p ∈ gap ι ∩ Metric.sphere (BandCircleEuclideanData C).center
      (BandCircleEuclideanData C).radius →
    ∃ (t : Complex) (keep : Finset (Fin 3)) (b : Fin 3),
      keep.card = 2 ∧ b ∈ keep ∧
      (∀ c : Fin 3, c ∈ keep ↔
        ∃ j : Fin 3,
          presentation (ι.1, ι.2.1, ι.2.2 ++ [c]) j.succ = C.1.1) ∧
      gap ι ∩ Metric.sphere (BandCircleEuclideanData C).center
          (BandCircleEuclideanData C).radius =
        ⋃ c ∈ keep,
          gap (ι.1, ι.2.1, ι.2.2 ++ [c]) ∩
            Metric.sphere (BandCircleEuclideanData C).center
              (BandCircleEuclideanData C).radius ∧
      (∀ c ∈ keep,
        IsClosed (gap (ι.1, ι.2.1, ι.2.2 ++ [c]) ∩
          Metric.sphere (BandCircleEuclideanData C).center
            (BandCircleEuclideanData C).radius) ∧
        IsPreconnected (gap (ι.1, ι.2.1, ι.2.2 ++ [c]) ∩
          Metric.sphere (BandCircleEuclideanData C).center
            (BandCircleEuclideanData C).radius) ∧
        t ∈ gap (ι.1, ι.2.1, ι.2.2 ++ [c]) ∩
          Metric.sphere (BandCircleEuclideanData C).center
            (BandCircleEuclideanData C).radius) ∧
      p ∈ gap (ι.1, ι.2.1, ι.2.2 ++ [b]) ∩
        Metric.sphere (BandCircleEuclideanData C).center
          (BandCircleEuclideanData C).radius ∧
      circle ι ≠ C ∧
      (BandCircleEuclideanData (circle ι)).radius <
        (BandCircleEuclideanData C).radius ∧
      dist t (BandCircleEuclideanData C).center =
        (BandCircleEuclideanData C).radius ∧
      dist t (BandCircleEuclideanData (circle ι)).center =
        (BandCircleEuclideanData (circle ι)).radius ∧
      dist (BandCircleEuclideanData C).center
          (BandCircleEuclideanData (circle ι)).center =
        (BandCircleEuclideanData C).radius +
          (BandCircleEuclideanData (circle ι)).radius

end ApollonianSuperharmonic

end
