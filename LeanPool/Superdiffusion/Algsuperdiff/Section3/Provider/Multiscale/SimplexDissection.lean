/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Whitney.KuhnCells
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.SimplexDomains
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.MultiscaleEllipticity
public import LeanPool.HighContrastHomogenization.Support.Geometry.CubeMeasure

/-!
# SimplexDissection

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# A triadic Whitney dissection of the open Kuhn simplex

The identified route needs, as its first ingredient,

> a triadic Whitney decomposition of the open simplex into countably many
> pairwise disjoint triadic cubes filling it up to a Lebesgue-null set.

That decomposition is what this file provides.  Nothing about the response
functional appears here; the analytic half (the boundary-count summability and
the subadditivity assembly) is `SimplexResponseBound.lean`.

## Contents

* the open Kuhn simplex as a Chapter 2 domain (`simplexDomain`), through its
  openness, convexity, boundedness and an explicit interior ball
  (`ball_simplexIncenter_subset_openCarrier`) around the equally spaced
  incenter of the ordered simplex;
* the Whitney selection `whitneyInnerCubes U Q` of an arbitrary set `U` inside a
  triadic cube `Q`: the triadic descendants of `Q` whose half-open realization
  lies in `U` while their triadic parent's does not — i.e. the *maximal* inner
  triadic cubes;
* its three defining properties: the selected cubes lie in `U`
  (`cubeSet_subset_of_mem_whitneyInnerCubes`), they are pairwise disjoint
  (`pairwiseDisjoint_whitneyInnerCubes`), and for `U` open they cover `U`
  (`subset_iUnion_whitneyInnerCubes`);
* the specialization to the open Kuhn simplex
  (`simplexDissection`), including the covering up to a null set in the *open*
  cube realizations that the Chapter 2 domain interface needs
  (`volume_openCarrier_diff_iUnion_eq_zero`).

## Reading notes

* The selection is by triadic *maximality*, not by the usual comparison of
  side length with the distance to the boundary; the two agree up to a bounded
  number of generations, and maximality is what the disjointness proof and the
  boundary bound of `SimplexResponseBound.lean` actually use.  The maximality
  clause is stated through `parentCube`, which is the triadic parent by
  `Homogenization.childCube_parent`.
* No Mathlib covering theorem (`MeasureTheory.Covering.*`, `Vitali`) is used:
  those produce almost-covering subfamilies of a *given* fine family with
  Besicovitch/Vitali structure, whereas what is needed here is the exact
  maximal-triadic-cube selection, whose disjointness and covering come from the
  triadic hierarchy of `Homogenization.Geometry.TriadicPartition` directly.

## References

* ABK26, `e.simplex.def`, `p.bfA.multiscalebound`, Step 1.
-/

namespace Algsuperdiff.Section3.Provider.Multiscale

open HCPolySupport HCPolySupport.Book
open Algsuperdiff.Section3.Provider.Whitney
open MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## The open Kuhn simplex is open, convex and bounded -/


-- `isOpen_openCarrier`, `convex_openCarrier`, `isBoundedDomain_openCarrier`
-- resolve to `SimplexDomains.lean`'s identically-typed versions through the
-- import-order-silent and latent-hazardous).

/-! ## The incenter and the interior ball -/

/-- An inner radius of a Kuhn cell in the `sup` metric: `3^{scale} / (2 (d+1))`. -/
def simplexInradius (T : KuhnCell d) : ℝ :=
  cubeScaleFactor T.supportCube / (2 * ((d : ℝ) + 1))

theorem simplexInradius_pos (T : KuhnCell d) : 0 < simplexInradius T := by
  have hs : (0 : ℝ) < cubeScaleFactor T.supportCube := zpow_pos (by norm_num) _
  have hd : (0 : ℝ) < 2 * ((d : ℝ) + 1) := by positivity
  exact div_pos hs hd

/-- The incenter of a Kuhn cell: the point of the ordered simplex whose local
coordinates are equally spaced, `3^{scale} (k+1)/(d+1) - 3^{scale}/2` at the
coordinate of rank `k` in the cell's order. -/
def simplexIncenter (T : KuhnCell d) : Vec d := fun i =>
  (T.supportCube.index i : ℝ) * cubeScaleFactor T.supportCube +
    simplexInradius T * (2 * ((T.order.symm i).val : ℝ) + 2 - ((d : ℝ) + 1))


private theorem half_cubeScaleFactor_eq (T : KuhnCell d) :
    cubeScaleFactor T.supportCube / 2 = simplexInradius T * ((d : ℝ) + 1) := by
  have hd : (2 : ℝ) * ((d : ℝ) + 1) ≠ 0 := by positivity
  rw [simplexInradius, div_mul_eq_mul_div, eq_div_iff hd]
  ring

/-- **The interior ball of a Kuhn cell.**  The open `sup`-ball of radius
`3^{scale}/(2(d+1))` around the equally spaced incenter is contained in the open
simplex.  Both the radius and the center are explicit; only positivity of the
radius and this inclusion are used downstream. -/
theorem ball_simplexIncenter_subset_openCarrier (T : KuhnCell d) :
    Metric.ball (simplexIncenter T) (simplexInradius T) ⊆ T.openCarrier := by
  intro x hx
  have hrho : 0 < simplexInradius T := simplexInradius_pos T
  have hcoord : ∀ i : Fin d, |x i - simplexIncenter T i| < simplexInradius T := by
    intro i
    have h := (dist_pi_lt_iff hrho).1 (Metric.mem_ball.1 hx) i
    rwa [Real.dist_eq] at h
  have hlocal : ∀ i : Fin d,
      |triadicLocalCoordinate T.supportCube x i -
        simplexInradius T * (2 * ((T.order.symm i).val : ℝ) + 2 - ((d : ℝ) + 1))| <
        simplexInradius T := by
    intro i
    have h := hcoord i
    have heq : triadicLocalCoordinate T.supportCube x i -
        simplexInradius T * (2 * ((T.order.symm i).val : ℝ) + 2 - ((d : ℝ) + 1)) =
        x i - simplexIncenter T i := by
      simp only [triadicLocalCoordinate, simplexIncenter]
      ring
    rwa [heq]
  have hrank : ∀ i : Fin d, ((T.order.symm i).val : ℝ) + 1 ≤ (d : ℝ) := by
    intro i
    have h : (T.order.symm i).val + 1 ≤ d := (T.order.symm i).isLt
    exact_mod_cast h
  have hrank0 : ∀ i : Fin d, (0 : ℝ) ≤ ((T.order.symm i).val : ℝ) := fun i =>
    Nat.cast_nonneg _
  rw [KuhnCell.mem_openCarrier_iff]
  constructor
  · intro i
    have hb := abs_lt.1 (hlocal i)
    have hlo := hb.1
    have hhi := hb.2
    have hr1 := hrank i
    have hr0 := hrank0 i
    have hhalf := half_cubeScaleFactor_eq T
    constructor
    · have hkey : ((T.supportCube.index i : ℝ) - 1 / 2) * cubeScaleFactor T.supportCube <
          x i ↔ -(cubeScaleFactor T.supportCube / 2) <
            triadicLocalCoordinate T.supportCube x i := by
        simp only [triadicLocalCoordinate, sub_mul]
        constructor <;> intro h <;> linarith
      rw [hkey, hhalf]
      nlinarith
    · have hkey : x i < ((T.supportCube.index i : ℝ) + 1 / 2) * cubeScaleFactor T.supportCube ↔
          triadicLocalCoordinate T.supportCube x i < cubeScaleFactor T.supportCube / 2 := by
        simp only [triadicLocalCoordinate, add_mul]
        constructor <;> intro h <;> linarith
      rw [hkey, hhalf]
      nlinarith
  · intro i j hij
    have hbi := abs_lt.1 (hlocal (T.order i))
    have hbj := abs_lt.1 (hlocal (T.order j))
    have hsi : (T.order.symm (T.order i)).val = i.val := by simp
    have hsj : (T.order.symm (T.order j)).val = j.val := by simp
    rw [hsi] at hbi
    rw [hsj] at hbj
    have hijr : ((i.val : ℝ) + 1) ≤ (j.val : ℝ) := by
      have : i.val + 1 ≤ j.val := hij
      exact_mod_cast this
    nlinarith [hbi.1, hbi.2, hbj.1, hbj.2, hrho]

theorem simplexIncenter_mem_openCarrier (T : KuhnCell d) :
    simplexIncenter T ∈ T.openCarrier :=
  ball_simplexIncenter_subset_openCarrier T
    (Metric.mem_ball_self (simplexInradius_pos T))

-- `openCarrier_nonempty` likewise resolves to `SimplexDomains.lean`'s copy.

/-- **The open Kuhn simplex as a Chapter 2 domain.**  This is the carrier at which
ABK26 applies the crude response bounds/6348. -/
def simplexDomain (T : KuhnCell d) : Ch02.Domain d where
  carrier := T.openCarrier
  isDomain := ⟨isOpen_openCarrier T, isBoundedDomain_openCarrier T, convex_openCarrier T⟩
  nonempty := openCarrier_nonempty T

@[simp] theorem simplexDomain_coe (T : KuhnCell d) :
    ((simplexDomain T : Ch02.Domain d) : Set (Vec d)) = T.openCarrier :=
  rfl

/-! ## The maximal inner triadic cubes of a set -/

/-- **The triadic Whitney selection.**  The triadic descendants `R` of `Q` whose
half-open realization is contained in `U` but whose triadic parent's is not:
the *maximal* inner triadic cubes of `U` below `Q`. -/
def whitneyInnerCubes (U : Set (Vec d)) (Q : TriadicCube d) : Set (TriadicCube d) :=
  {R | (∃ t : ℕ, R ∈ descendantsAtDepth Q t) ∧ cubeSet R ⊆ U ∧ ¬ cubeSet (parentCube R) ⊆ U}

theorem cubeSet_subset_of_mem_whitneyInnerCubes {U : Set (Vec d)} {Q R : TriadicCube d}
    (hR : R ∈ whitneyInnerCubes U Q) : cubeSet R ⊆ U := hR.2.1

theorem exists_depth_of_mem_whitneyInnerCubes {U : Set (Vec d)} {Q R : TriadicCube d}
    (hR : R ∈ whitneyInnerCubes U Q) : ∃ t : ℕ, R ∈ descendantsAtDepth Q t := hR.1

/-- A selected cube is a strict descendant: its own realization is inside `U`
while `Q`'s is not, so the selection depth is at least one. -/
theorem one_le_depth_of_mem_whitneyInnerCubes {U : Set (Vec d)} {Q R : TriadicCube d}
    (hQ : ¬ cubeSet Q ⊆ U) (hR : R ∈ whitneyInnerCubes U Q) {t : ℕ}
    (ht : R ∈ descendantsAtDepth Q t) : 1 ≤ t := by
  rcases Nat.eq_zero_or_pos t with rfl | hpos
  · rw [descendantsAtDepth_zero, Finset.mem_singleton] at ht
    exact absurd (ht ▸ hR.2.1) hQ
  · exact hpos

/-- Cross-scale nesting: a descendant of `Q` whose realization meets that of a
shallower descendant is a descendant of the latter. -/
private theorem mem_descendantsAtDepth_of_not_disjoint {Q A B : TriadicCube d} {t u : ℕ}
    (hA : A ∈ descendantsAtDepth Q t) (hB : B ∈ descendantsAtDepth Q (t + u))
    (hmeet : ¬ Disjoint (cubeSet A) (cubeSet B)) : B ∈ descendantsAtDepth A u := by
  obtain ⟨C, hC, hBC⟩ := exists_descendant_ancestor_at_depth t u hB
  have hCA : C = A := by
    by_contra hne
    refine hmeet ?_
    exact ((pairwiseDisjoint_descendantsAtDepth Q t hC hA hne).mono
      Set.Subset.rfl Set.Subset.rfl).symm.mono
      Set.Subset.rfl (cubeSet_subset_of_mem_descendantsAtDepth hBC)
  exact hCA ▸ hBC

/-- **The selected cubes are pairwise disjoint.**  Two distinct maximal inner
cubes cannot be nested: the deeper one's parent would then already be an inner
cube. -/
theorem pairwiseDisjoint_whitneyInnerCubes (U : Set (Vec d)) (Q : TriadicCube d) :
    (whitneyInnerCubes U Q).PairwiseDisjoint cubeSet := by
  have key : ∀ {A B : TriadicCube d}, A ∈ whitneyInnerCubes U Q →
      B ∈ whitneyInnerCubes U Q → ∀ {t u : ℕ}, A ∈ descendantsAtDepth Q t →
        B ∈ descendantsAtDepth Q (t + u) → ¬ Disjoint (cubeSet A) (cubeSet B) → A = B := by
    intro A B hA hB t u htA huB hmeet
    have hBA : B ∈ descendantsAtDepth A u := mem_descendantsAtDepth_of_not_disjoint htA huB hmeet
    rcases Nat.eq_zero_or_pos u with rfl | hpos
    · rw [descendantsAtDepth_zero, Finset.mem_singleton] at hBA
      exact hBA.symm
    · obtain ⟨u', rfl⟩ : ∃ u', u = u' + 1 := ⟨u - 1, by omega⟩
      obtain ⟨C, hC, hBC⟩ := mem_descendantsAtDepth_succ_iff.mp hBA
      obtain ⟨digits, hdig⟩ := mem_childCubes_iff.mp hBC
      have hparent : parentCube B = C := by
        rw [hdig]
        exact childCube_parent C digits
      exact absurd (hparent ▸ (cubeSet_subset_of_mem_descendantsAtDepth hC).trans hA.2.1) hB.2.2
  intro A hA B hB hAB
  obtain ⟨t, htA⟩ := hA.1
  obtain ⟨u, huB⟩ := hB.1
  by_contra hnd
  rcases le_total t u with hle | hle
  · obtain ⟨u', rfl⟩ : ∃ u', u = t + u' := ⟨u - t, by omega⟩
    exact hAB (key hA hB htA huB (by simpa [Function.onFun] using hnd))
  · obtain ⟨t', rfl⟩ : ∃ t', t = u + t' := ⟨t - u, by omega⟩
    refine hAB (key hB hA huB htA ?_).symm
    intro hd
    exact hnd (by simpa [Function.onFun] using hd.symm)

/-- **The selected cubes cover an open set.**  For `U` open with
`U ⊆ cubeSet Q` and `cubeSet Q ⊄ U`, every point of `U` lies in a maximal inner
cube: take the shallowest triadic cube of the point whose realization already
lies in `U`. -/
theorem subset_iUnion_whitneyInnerCubes {U : Set (Vec d)} {Q : TriadicCube d}
    (hopen : IsOpen U) (hUQ : U ⊆ cubeSet Q) (hQU : ¬ cubeSet Q ⊆ U) :
    U ⊆ ⋃ R ∈ whitneyInnerCubes U Q, cubeSet R := by
  classical
  intro x hx
  set P : ℕ → Prop := fun t => ∃ R ∈ descendantsAtDepth Q t, x ∈ cubeSet R ∧ cubeSet R ⊆ U
    with hP
  have hxQ : x ∈ cubeSet Q := hUQ hx
  -- deep enough cubes of `x` are inside `U`
  have hexists : ∃ t : ℕ, P t := by
    obtain ⟨eps, heps, hball⟩ := Metric.isOpen_iff.1 hopen x hx
    obtain ⟨t, ht⟩ : ∃ t : ℕ, cubeScaleFactor Q / (3 : ℝ) ^ t < eps := by
      have hbase : (0 : ℝ) < cubeScaleFactor Q := zpow_pos (by norm_num) _
      obtain ⟨t, ht⟩ := pow_unbounded_of_one_lt (cubeScaleFactor Q / eps) (by norm_num : (1:ℝ) < 3)
      refine ⟨t, ?_⟩
      have hpow : (0 : ℝ) < (3 : ℝ) ^ t := by positivity
      rw [div_lt_iff₀ hpow]
      rw [div_lt_iff₀ heps] at ht
      linarith
    obtain ⟨R, hR, hxR⟩ := exists_mem_descendantsAtDepth_of_mem_cubeSet t hxQ
    refine ⟨t, R, hR, hxR, ?_⟩
    intro y hy
    refine hball ?_
    have hxc := cubeSet_subset_closedBall R hxR
    have hyc := cubeSet_subset_closedBall R hy
    have hdist : dist y x ≤ 2 * cubeRadius R :=
      (dist_triangle y (cubeCenter R) x).trans
        (by
          have h1 : dist y (cubeCenter R) ≤ cubeRadius R := Metric.mem_closedBall.1 hyc
          have h2 : dist (cubeCenter R) x ≤ cubeRadius R := by
            rw [dist_comm]
            exact Metric.mem_closedBall.1 hxc
          linarith)
    have hfac : 2 * cubeRadius R = cubeScaleFactor R :=
      (cubeScaleFactor_eq_two_mul_cubeRadius R).symm
    have hRfac : cubeScaleFactor R = cubeScaleFactor Q / (3 : ℝ) ^ t :=
      cubeScaleFactor_descendant_eq_div_pow hR
    rw [Metric.mem_ball]
    calc dist y x ≤ 2 * cubeRadius R := hdist
      _ = cubeScaleFactor Q / (3 : ℝ) ^ t := by rw [hfac, hRfac]
      _ < eps := ht
  have hnot0 : ¬ P 0 := by
    rintro ⟨R, hR, -, hRU⟩
    rw [descendantsAtDepth_zero, Finset.mem_singleton] at hR
    exact hQU (hR ▸ hRU)
  obtain ⟨t, htP, hmin⟩ : ∃ t, P t ∧ ∀ t' < t, ¬ P t' :=
    ⟨Nat.find hexists, Nat.find_spec hexists, fun _ h => Nat.find_min hexists h⟩
  obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := by
    rcases Nat.eq_zero_or_pos t with rfl | hpos
    · exact absurd htP hnot0
    · exact ⟨t - 1, by omega⟩
  obtain ⟨R, hR, hxR, hRU⟩ := htP
  obtain ⟨C, hC, hRC⟩ := mem_descendantsAtDepth_succ_iff.mp hR
  obtain ⟨digits, hdig⟩ := mem_childCubes_iff.mp hRC
  have hparent : parentCube R = C := by
    rw [hdig]; exact childCube_parent C digits
  have hCU : ¬ cubeSet C ⊆ U := fun hCU =>
    hmin t' (by omega) ⟨C, hC, cubeSet_subset_of_mem_childCubes hRC hxR, hCU⟩
  refine Set.mem_iUnion.mpr ⟨R, Set.mem_iUnion.mpr ⟨⟨⟨t' + 1, hR⟩, hRU, ?_⟩, hxR⟩⟩
  rwa [hparent]


/-! ## The dissection of an open Kuhn simplex -/

/-- The realization of a Kuhn cell is not all of its support cube: the lower
corner of the half-open cube is not even in the open cube. -/
theorem not_cubeSet_supportCube_subset_openCarrier [NeZero d] (T : KuhnCell d) :
    ¬ cubeSet T.supportCube ⊆ T.openCarrier := by
  have hs : (0 : ℝ) < cubeScaleFactor T.supportCube := zpow_pos (by norm_num) _
  set y : Vec d := fun i =>
    ((T.supportCube.index i : ℝ) - 1 / 2) * cubeScaleFactor T.supportCube with hy
  have hyQ : y ∈ cubeSet T.supportCube := by
    intro i
    refine ⟨le_rfl, ?_⟩
    simp only [hy]
    nlinarith
  intro hsub
  have hyopen := T.openCarrier_subset_openCubeSet (hsub hyQ)
  have := (hyopen (0 : Fin d)).1
  simp only [hy] at this
  exact absurd this (lt_irrefl _)

/-- **The triadic Whitney dissection of an open Kuhn simplex** (the geometric
ingredient of the identified route): the maximal inner triadic cubes of the open simplex
below its support cube. -/
def simplexDissection (T : KuhnCell d) : Set (TriadicCube d) :=
  whitneyInnerCubes T.openCarrier T.supportCube

theorem cubeSet_subset_openCarrier_of_mem_simplexDissection {T : KuhnCell d}
    {R : TriadicCube d} (hR : R ∈ simplexDissection T) : cubeSet R ⊆ T.openCarrier :=
  cubeSet_subset_of_mem_whitneyInnerCubes hR

theorem openCubeSet_subset_openCarrier_of_mem_simplexDissection {T : KuhnCell d}
    {R : TriadicCube d} (hR : R ∈ simplexDissection T) : openCubeSet R ⊆ T.openCarrier :=
  (openCubeSet_subset_cubeSet R).trans (cubeSet_subset_openCarrier_of_mem_simplexDissection hR)

theorem pairwiseDisjoint_simplexDissection (T : KuhnCell d) :
    (simplexDissection T).PairwiseDisjoint cubeSet :=
  pairwiseDisjoint_whitneyInnerCubes _ _

theorem pairwiseDisjoint_openCubeSet_simplexDissection (T : KuhnCell d) :
    (simplexDissection T).PairwiseDisjoint openCubeSet :=
  (pairwiseDisjoint_simplexDissection T).mono fun R => openCubeSet_subset_cubeSet R


/-- **The dissection fills the simplex** (half-open realizations). -/
theorem openCarrier_subset_iUnion_simplexDissection [NeZero d] (T : KuhnCell d) :
    T.openCarrier ⊆ ⋃ R ∈ simplexDissection T, cubeSet R :=
  subset_iUnion_whitneyInnerCubes (isOpen_openCarrier T)
    (T.openCarrier_subset_openCubeSet.trans (openCubeSet_subset_cubeSet _))
    (not_cubeSet_supportCube_subset_openCarrier T)

/-- **The dissection fills the simplex up to a null set** in the *open* cube
realizations, which are the Chapter 2 domains of the subadditivity interface. -/
theorem volume_openCarrier_diff_iUnion_eq_zero [NeZero d] (T : KuhnCell d) :
    volume (T.openCarrier \ ⋃ R : ↥(simplexDissection T), openCubeSet (R : TriadicCube d))
      = 0 := by
  have hcover := openCarrier_subset_iUnion_simplexDissection T
  have hsub : (T.openCarrier \ ⋃ R : ↥(simplexDissection T), openCubeSet (R : TriadicCube d)) ⊆
      ⋃ R : ↥(simplexDissection T), (cubeSet (R : TriadicCube d) \ openCubeSet R) := by
    rintro x ⟨hxU, hxnot⟩
    obtain ⟨R, hR, hxR⟩ := by
      simpa only [Set.mem_iUnion, exists_prop] using hcover hxU
    refine Set.mem_iUnion.mpr ⟨⟨R, hR⟩, hxR, ?_⟩
    intro hxopen
    exact hxnot (Set.mem_iUnion.mpr ⟨⟨R, hR⟩, hxopen⟩)
  refine measure_mono_null hsub ?_
  exact measure_iUnion_null fun R =>
    (MeasureTheory.ae_eq_set.mp (cubeSet_ae_eq_openCubeSet (R : TriadicCube d))).1

end

end Algsuperdiff.Section3.Provider.Multiscale
