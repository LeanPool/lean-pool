/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Whitney.SimplexPartition
public import Mathlib.Analysis.Convex.Measure

/-!
# SimplexDomains

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The cells of `SW(□_m)` as Chapter 2 domains

This module is the measure-theoretic layer that the proved simplex partition
`d.simplex.partition` (`Provider/Whitney/SimplexPartition.lean`) explicitly
leaves open, and that the subadditive decomposition of `p.bfA.multiscalebound`
(`e.sum-of-a-decomp`) needs in order to feed `SW(□_m)` to `l.subadd.betterer`
(`Provider/Whitney/SubadditivityCountable.lean`):

* the manuscript's **open** simplex `△_n^π(z)` (`KuhnCell.openCarrier`) is a
  nonempty bounded open convex set, hence a `Homogenization.Book.Ch02.Domain`
  (`KuhnCell.domain`);
* `KuhnCell d` is countable, so `SW(□_m)` is a countable family
  (`instCountableKuhnCell`);
* the canonical half-open realization differs from the open one by a Lebesgue
  null set (`volume_carrier_diff_openCarrier`), because the half-open cell is
  contained in the closure of the open one and an open convex set has null
  frontier;
* consequently the open cells of `SW(□_m)` cover the open root cube up to a
  null set (`volume_openCubeSet_diff_iUnion_openCarrier`), which is exactly the
  `hcover` hypothesis of
  `Whitney.ofReal_bfA_quadratic_le_simplex_weighted_tsum`.

## Why the open realization

`l.subadd.betterer` is stated for a family of `Ch02.Domain`s — open bounded
convex nonempty sets — because the variational class `L²_pot,0(U) ×
L²_sol,0(U)` of `e.variational.mu.U.P` is only defined there.  The manuscript's
simplices are open, and the exact half-open partition of
`SimplexPartition.lean` is the bookkeeping device that makes the covering
statement exact; the passage between them is the null-boundary fact proved
here.  No face-to-face or simplicial-complex property is used or asserted.

## References

* ABK26, (`e.simplex.def`), (`e.SW.def`).
-/

namespace Algsuperdiff.Section3.Provider.Multiscale

open HCPolySupport MeasureTheory
open Algsuperdiff.Section3.Provider.Whitney

noncomputable section

variable {d : ℕ}

/-! ## Countability -/

/-- `KuhnCell d` is countable: a cell is a triadic cube together with a
permutation of `Fin d`. -/
instance instCountableKuhnCell (d : ℕ) : Countable (KuhnCell d) := by
  classical
  have hinj : Function.Injective
      (fun T : KuhnCell d => (T.supportCube, T.order)) := by
    intro T U hTU
    cases T
    cases U
    simp only [Prod.mk.injEq] at hTU
    simp [hTU.1, hTU.2]
  exact hinj.countable

/-! ## The open cell is a Chapter 2 domain -/

private theorem isLinearMap_coord_sub (a b : Fin d) :
    IsLinearMap ℝ (fun x : Vec d => x a - x b) where
  map_add x y := by simp only [Pi.add_apply]; ring
  map_smul c x := by simp only [Pi.smul_apply, smul_eq_mul]; ring

private theorem continuous_triadicLocalCoordinate (Q : TriadicCube d) (k : Fin d) :
    Continuous fun x : Vec d => triadicLocalCoordinate Q x k :=
  (continuous_apply k).sub continuous_const

/-- The open simplex is the open cube cut by the finitely many strict
order conditions of `e.simplex.def`. -/
private theorem openCarrier_eq_inter (T : KuhnCell d) :
    T.openCarrier =
      openCubeSet T.supportCube ∩
        ⋂ i : Fin d, ⋂ j : Fin d,
          {x : Vec d | i.val < j.val →
            triadicLocalCoordinate T.supportCube x (T.order i) <
              triadicLocalCoordinate T.supportCube x (T.order j)} := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq,
    KuhnCell.mem_openCarrier_iff]

theorem isOpen_openCarrier (T : KuhnCell d) : IsOpen T.openCarrier := by
  rw [openCarrier_eq_inter]
  refine (isOpen_openCubeSet T.supportCube).inter ?_
  refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
  by_cases h : i.val < j.val
  · have hset :
        {x : Vec d | i.val < j.val →
            triadicLocalCoordinate T.supportCube x (T.order i) <
              triadicLocalCoordinate T.supportCube x (T.order j)} =
          {x : Vec d |
            triadicLocalCoordinate T.supportCube x (T.order i) <
              triadicLocalCoordinate T.supportCube x (T.order j)} := by
      ext x
      simp [h]
    rw [hset]
    exact isOpen_lt (continuous_triadicLocalCoordinate T.supportCube (T.order i))
      (continuous_triadicLocalCoordinate T.supportCube (T.order j))
  · have hset :
        {x : Vec d | i.val < j.val →
            triadicLocalCoordinate T.supportCube x (T.order i) <
              triadicLocalCoordinate T.supportCube x (T.order j)} = Set.univ := by
      ext x
      simp [h]
    rw [hset]
    exact isOpen_univ

theorem convex_openCarrier (T : KuhnCell d) : Convex ℝ T.openCarrier := by
  rw [openCarrier_eq_inter]
  refine (convex_openCubeSet T.supportCube).inter ?_
  refine convex_iInter fun i => convex_iInter fun j => ?_
  by_cases h : i.val < j.val
  · have hset :
        {x : Vec d | i.val < j.val →
            triadicLocalCoordinate T.supportCube x (T.order i) <
              triadicLocalCoordinate T.supportCube x (T.order j)} =
          {x : Vec d | (fun y : Vec d => y (T.order i) - y (T.order j)) x <
            (T.supportCube.index (T.order i) : ℝ) * cubeScaleFactor T.supportCube -
              (T.supportCube.index (T.order j) : ℝ) * cubeScaleFactor T.supportCube} := by
      ext x
      simp only [Set.mem_ofPred_eq, triadicLocalCoordinate, h, forall_const]
      constructor <;> intro hx <;> linarith
    rw [hset]
    exact convex_halfSpace_lt (isLinearMap_coord_sub (T.order i) (T.order j)) _
  · have hset :
        {x : Vec d | i.val < j.val →
            triadicLocalCoordinate T.supportCube x (T.order i) <
              triadicLocalCoordinate T.supportCube x (T.order j)} = Set.univ := by
      ext x
      simp [h]
    rw [hset]
    exact convex_univ

/-- The barycentric-type interior point of a Kuhn cell: the `k`-th coordinate is
placed at height `(rank(k) + 1)/(d + 1)` of the support cube, where `rank` is the
position of `k` in the cell's order. -/
def kuhnCellInteriorPoint (T : KuhnCell d) : Vec d := fun k =>
  ((T.supportCube.index k : ℝ) +
      (((T.order.symm k).val + 1 : ℝ) / (d + 1) - 1 / 2)) *
    cubeScaleFactor T.supportCube

theorem kuhnCellInteriorPoint_mem_openCarrier (T : KuhnCell d) :
    kuhnCellInteriorPoint T ∈ T.openCarrier := by
  have hs : (0 : ℝ) < cubeScaleFactor T.supportCube := zpow_pos (by norm_num) _
  have hd1 : (0 : ℝ) < (d : ℝ) + 1 := by positivity
  have hfrac : ∀ k : Fin d,
      (0 : ℝ) < (((T.order.symm k).val + 1 : ℝ) / (d + 1)) ∧
        (((T.order.symm k).val + 1 : ℝ) / (d + 1)) < 1 := by
    intro k
    have hlt : ((T.order.symm k).val : ℝ) + 1 < (d : ℝ) + 1 := by
      have := (T.order.symm k).isLt
      have : ((T.order.symm k).val : ℝ) < (d : ℝ) := by exact_mod_cast this
      linarith
    constructor
    · positivity
    · rw [div_lt_one hd1]
      exact hlt
  have hlocal : ∀ k : Fin d,
      triadicLocalCoordinate T.supportCube (kuhnCellInteriorPoint T) k =
        ((((T.order.symm k).val + 1 : ℝ) / (d + 1)) - 1 / 2) *
          cubeScaleFactor T.supportCube := by
    intro k
    simp only [triadicLocalCoordinate, kuhnCellInteriorPoint]
    ring
  rw [KuhnCell.mem_openCarrier_iff]
  refine ⟨?_, ?_⟩
  · simp only [openCubeSet, Set.mem_ofPred_eq, kuhnCellInteriorPoint]
    intro k
    have hk := hfrac k
    constructor <;> nlinarith [hk.1, hk.2]
  · intro i j hij
    rw [hlocal, hlocal]
    simp only [Equiv.symm_apply_apply]
    have hlt : ((i.val : ℝ) + 1) < ((j.val : ℝ) + 1) := by
      have hij' : (i.val : ℝ) < (j.val : ℝ) := by exact_mod_cast hij
      linarith
    have hdiv : ((i.val : ℝ) + 1) / ((d : ℝ) + 1) < ((j.val : ℝ) + 1) / ((d : ℝ) + 1) := by
      gcongr
    nlinarith

theorem openCarrier_nonempty (T : KuhnCell d) : T.openCarrier.Nonempty :=
  ⟨kuhnCellInteriorPoint T, kuhnCellInteriorPoint_mem_openCarrier T⟩

theorem isBoundedDomain_openCarrier (T : KuhnCell d) :
    IsBoundedDomain T.openCarrier :=
  Bornology.IsBounded.isBoundedDomain
    ((isBounded_cubeSet T.supportCube).subset
      (T.openCarrier_subset_carrier.trans T.carrier_subset_cubeSet))

/-- **The open simplex `△` as a Chapter 2 domain.**  This is the carrier at
which `l.subadd.betterer` reads the cells of `SW(□_m)`. -/
def kuhnCellDomain (T : KuhnCell d) : Book.Ch02.Domain d where
  carrier := T.openCarrier
  isDomain := ⟨isOpen_openCarrier T, isBoundedDomain_openCarrier T, convex_openCarrier T⟩
  nonempty := openCarrier_nonempty T


/-! ## The half-open cell exceeds the open one by a null set -/

/-- The half-open cell is contained in the closure of the open one: sliding a
point of the half-open cell towards the interior point makes every weak
inequality strict. -/
theorem carrier_subset_closure_openCarrier (T : KuhnCell d) :
    T.carrier ⊆ closure T.openCarrier := by
  intro x hx
  have hs : (0 : ℝ) < cubeScaleFactor T.supportCube := zpow_pos (by norm_num) _
  set y : Vec d := kuhnCellInteriorPoint T with hy
  have hymem := kuhnCellInteriorPoint_mem_openCarrier T
  rw [KuhnCell.mem_openCarrier_iff] at hymem
  -- the weak inequalities satisfied by `x`
  have hxcube : x ∈ cubeSet T.supportCube := hx.1
  have hxord : ∀ i j : Fin d, i.val ≤ j.val →
      triadicLocalCoordinate T.supportCube x (T.order i) ≤
        triadicLocalCoordinate T.supportCube x (T.order j) := by
    intro i j hij
    rw [hx.2]
    exact Tuple.monotone_sort (triadicLocalCoordinate T.supportCube x) hij
  -- the segment point
  have hseg : ∀ t : ℝ, 0 < t → t ≤ 1 →
      (fun k => (1 - t) * x k + t * y k) ∈ T.openCarrier := by
    intro t ht0 ht1
    rw [KuhnCell.mem_openCarrier_iff]
    refine ⟨?_, ?_⟩
    · simp only [openCubeSet, Set.mem_ofPred_eq]
      intro k
      have hxk := hxcube k
      have hyk := hymem.1 k
      constructor <;> nlinarith [hxk.1, hxk.2, hyk.1, hyk.2]
    · intro i j hij
      have hxij := hxord i j hij.le
      have hyij := hymem.2 i j hij
      simp only [triadicLocalCoordinate] at hxij hyij ⊢
      nlinarith
  -- the segment point converges to `x`
  rw [Metric.mem_closure_iff]
  intro eps heps
  set R : ℝ := dist x y + 1 with hR
  have hR0 : (0 : ℝ) < R := by
    have := dist_nonneg (x := x) (y := y)
    simp only [hR]
    linarith
  set t : ℝ := min 1 (eps / (2 * R)) with ht
  have ht0 : 0 < t := lt_min zero_lt_one (by positivity)
  have ht1 : t ≤ 1 := min_le_left _ _
  refine ⟨fun k => (1 - t) * x k + t * y k, hseg t ht0 ht1, ?_⟩
  have hdist : dist x (fun k => (1 - t) * x k + t * y k) = t * dist x y := by
    rw [dist_eq_norm, dist_eq_norm]
    have hfun : (x - fun k => (1 - t) * x k + t * y k) = t • (x - y) := by
      funext k
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [hfun, norm_smul, Real.norm_eq_abs, abs_of_pos ht0]
  rw [hdist]
  have htle : t ≤ eps / (2 * R) := min_le_right _ _
  have hxy : dist x y < R := by
    simp only [hR]
    linarith
  have hstep : t * dist x y ≤ (eps / (2 * R)) * R :=
    mul_le_mul htle hxy.le dist_nonneg (by positivity)
  have hhalf : (eps / (2 * R)) * R = eps / 2 := by
    field_simp
  rw [hhalf] at hstep
  linarith

theorem volume_carrier_diff_openCarrier (T : KuhnCell d) :
    volume (T.carrier \ T.openCarrier) = 0 := by
  refine measure_mono_null ?_ ((convex_openCarrier T).addHaar_frontier volume)
  intro x hx
  simp only [frontier, Set.mem_sdiff, (isOpen_openCarrier T).interior_eq]
  exact ⟨carrier_subset_closure_openCarrier T hx.1, hx.2⟩

/-! ## The open cells cover the root cube up to a null set -/

/-- **The `hcover` input of `l.subadd.betterer` at `SW(□_m)`.**  The open cells
of the simplex partition exhaust the open root cube up to a Lebesgue null set:
the half-open cells exhaust it exactly
(`iUnion_carrier_simplexPartition_eq_openCubeSet`) and each half-open cell
exceeds its open cell by a null set. -/
theorem volume_openCubeSet_diff_iUnion_openCarrier [NeZero d] {m : ℤ} {hn : ℕ → ℕ}
    (hstep : ∀ n : ℕ, hn n ≤ hn (n + 1) + 1) :
    volume (openCubeSet (originCube d m) \
        ⋃ T ∈ simplexPartition (d := d) m hn, T.openCarrier) = 0 := by
  have hsub :
      openCubeSet (originCube d m) \
          (⋃ T ∈ simplexPartition (d := d) m hn, T.openCarrier) ⊆
        ⋃ T ∈ simplexPartition (d := d) m hn, (T.carrier \ T.openCarrier) := by
    intro x hx
    have hxU : x ∈ ⋃ T ∈ simplexPartition (d := d) m hn, T.carrier := by
      rw [iUnion_carrier_simplexPartition_eq_openCubeSet hstep]
      exact hx.1
    obtain ⟨T, hT, hxT⟩ := by simpa only [Set.mem_iUnion] using hxU
    refine Set.mem_iUnion.mpr ⟨T, Set.mem_iUnion.mpr ⟨hT, hxT, ?_⟩⟩
    intro hxo
    exact hx.2 (Set.mem_iUnion.mpr ⟨T, Set.mem_iUnion.mpr ⟨hT, hxo⟩⟩)
  refine measure_mono_null hsub ?_
  refine measure_biUnion_null_iff (Set.to_countable _) |>.mpr ?_
  intro T _
  exact volume_carrier_diff_openCarrier T

end

end Algsuperdiff.Section3.Provider.Multiscale
