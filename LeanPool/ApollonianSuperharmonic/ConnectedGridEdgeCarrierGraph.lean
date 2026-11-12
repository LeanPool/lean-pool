/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Tactic.ByContra
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.Order.Compact

public import LeanPool.ApollonianSuperharmonic.FourNeighborAdjacent
public import LeanPool.ApollonianSuperharmonic.GridEdgeCarrier
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

-- [TABLET NODE: ConnectedGridEdgeCarrierGraph]

/-!
# ConnectedGridEdgeCarrierGraph

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace ConnectedEdgeGraph

private noncomputable def X (E : Set (Finset GaussianInt)) : Set GaussianInt := {x | ∃ e ∈ E, x ∈ e}

private noncomputable def G (E : Set (Finset GaussianInt)) : SimpleGraph (X E) :=
    SimpleGraph.fromRel fun a b =>
    ({a.1, b.1} : Finset GaussianInt) ∈ E

private noncomputable def J : GaussianInt := ⟨0, 1⟩

private theorem carrier_pair (a b : GaussianInt) :
      GridEdgeCarrier ({a, b} : Finset GaussianInt) =
        Set.uIcc (GaussianRealPoint a) (GaussianRealPoint b) := by
  classical
  unfold GridEdgeCarrier
  simp [Set.uIcc_comm]

private theorem canonical (E : Set (Finset GaussianInt)) (hgrid : ∀ e ∈ E, ∃ a b : GaussianInt, e
    = {a, b} ∧ FourNeighborAdjacent a b) (e : Finset GaussianInt) (he : e ∈ E) :
      ∃ a : GaussianInt, e = {a, a + 1} ∨ e = {a, a + J} := by
  classical
  let J : GaussianInt := ⟨0, 1⟩
  change (∃ a : GaussianInt, e = {a, a + 1} ∨ e = {a, a + J})
  rcases hgrid e he with ⟨a, b, rfl, hab⟩
  rcases hab with rfl | rfl | rfl | rfl
  · exact ⟨a, Or.inl rfl⟩
  · refine ⟨a - 1, Or.inl ?_⟩
    have h : a - 1 + 1 = a := by ring
    rw [h, Finset.pair_comm]
  · exact ⟨a, Or.inr rfl⟩
  · refine ⟨a - J, Or.inr ?_⟩
    have h : a - J + J = a := by ring
    rw [h, Finset.pair_comm]

private theorem point_of_common {e f : Finset GaussianInt} {z : GaussianInt}
      (hze : z ∈ e) (hzf : z ∈ f) :
      (GridEdgeCarrier e ∩ GridEdgeCarrier f).Nonempty := by
  classical
  refine ⟨GaussianRealPoint z, ?_, ?_⟩
  · unfold GridEdgeCarrier
    exact Set.mem_iUnion.2 ⟨z, Set.mem_iUnion.2 ⟨hze,
      Set.mem_iUnion.2 ⟨z, Set.mem_iUnion.2 ⟨hze, by simp⟩⟩⟩⟩
  · unfold GridEdgeCarrier
    exact Set.mem_iUnion.2 ⟨z, Set.mem_iUnion.2 ⟨hzf,
      Set.mem_iUnion.2 ⟨z, Set.mem_iUnion.2 ⟨hzf, by simp⟩⟩⟩⟩

private theorem horizontal_inter (a c : GaussianInt) :
      (GridEdgeCarrier ({a, a + 1} : Finset GaussianInt) ∩
        GridEdgeCarrier ({c, c + 1} : Finset GaussianInt)).Nonempty →
        ∃ z, z ∈ ({a, a + 1} : Finset GaussianInt) ∧
          z ∈ ({c, c + 1} : Finset GaussianInt) := by
  classical
  have carrier_pair (a b : GaussianInt) :
      GridEdgeCarrier ({a, b} : Finset GaussianInt) =
        Set.uIcc (GaussianRealPoint a) (GaussianRealPoint b) := carrier_pair a b
  rintro ⟨⟨x, y⟩, hx, hy⟩
  rw [carrier_pair] at hx hy
  simp only [Set.uIcc, GaussianRealPoint, Int.reduceNeg, GaussianInt.intCast_re,
      GaussianInt.intCast_im, Zsqrtd.re_add, Zsqrtd.re_one, Int.cast_add, Int.cast_one,
      Zsqrtd.im_add, Zsqrtd.im_one, add_zero, Prod.mk_le_mk, le_add_iff_nonneg_right,
      zero_le_one, Std.le_refl, and_self, inf_of_le_left, sup_of_le_right, Set.mem_Icc]
      at hx hy
  rw [← GaussianInt.intCast_re a, ← GaussianInt.intCast_im a] at hx
  rw [← GaussianInt.intCast_re c, ← GaussianInt.intCast_im c] at hy
  have him : a.im = c.im := by
    have himR : ((a.im : Int) : Real) = ((c.im : Int) : Real) := by
      linarith [hx.1.2, hx.2.2, hy.1.2, hy.2.2]
    exact_mod_cast himR
  have hac : a.re ≤ c.re + 1 := by
    have hacR : ((a.re : Int) : Real) ≤ ((c.re : Int) : Real) + 1 := by
      linarith [hx.1.1, hx.2.1, hy.1.1, hy.2.1]
    exact_mod_cast hacR
  have hca : c.re ≤ a.re + 1 := by
    have hcaR : ((c.re : Int) : Real) ≤ ((a.re : Int) : Real) + 1 := by
      linarith [hx.1.1, hx.2.1, hy.1.1, hy.2.1]
    exact_mod_cast hcaR
  have hre : a.re = c.re ∨ a.re = c.re + 1 ∨ c.re = a.re + 1 := by omega
  rcases hre with hre | hre | hre
  · have hacEq : a = c := by
      apply Zsqrtd.ext <;> simp [hre, him]
    exact ⟨a, by simp, by simp [hacEq]⟩
  · have hacEq : a = c + 1 := by
      apply Zsqrtd.ext <;> simp [hre, him]
    exact ⟨a, by simp, by simp [hacEq]⟩
  · have hcaEq : c = a + 1 := by
      apply Zsqrtd.ext <;> simp [hre, him]
    exact ⟨c, by simp [hcaEq], by simp⟩

private theorem vertical_inter (a c : GaussianInt) :
      (GridEdgeCarrier ({a, a + J} : Finset GaussianInt) ∩
        GridEdgeCarrier ({c, c + J} : Finset GaussianInt)).Nonempty →
        ∃ z, z ∈ ({a, a + J} : Finset GaussianInt) ∧
          z ∈ ({c, c + J} : Finset GaussianInt) := by
  classical
  let J : GaussianInt := ⟨0, 1⟩
  have carrier_pair (a b : GaussianInt) :
      GridEdgeCarrier ({a, b} : Finset GaussianInt) =
        Set.uIcc (GaussianRealPoint a) (GaussianRealPoint b) := carrier_pair a b
  change ((GridEdgeCarrier ({a, a + J} : Finset GaussianInt) ∩
        GridEdgeCarrier ({c, c + J} : Finset GaussianInt)).Nonempty →
        ∃ z, z ∈ ({a, a + J} : Finset GaussianInt) ∧
          z ∈ ({c, c + J} : Finset GaussianInt))
  rintro ⟨⟨x, y⟩, hx, hy⟩
  rw [carrier_pair] at hx hy
  simp only [Set.uIcc, GaussianRealPoint, Int.reduceNeg, GaussianInt.intCast_re,
      GaussianInt.intCast_im, Zsqrtd.re_add, add_zero, Zsqrtd.im_add, Int.cast_add,
      Int.cast_one, Prod.mk_le_mk, Std.le_refl, le_add_iff_nonneg_right, zero_le_one,
      and_self, inf_of_le_left, sup_of_le_right, Set.mem_Icc, J] at hx hy
  rw [← GaussianInt.intCast_re a, ← GaussianInt.intCast_im a] at hx
  rw [← GaussianInt.intCast_re c, ← GaussianInt.intCast_im c] at hy
  have hre : a.re = c.re := by
    have hreR : ((a.re : Int) : Real) = ((c.re : Int) : Real) := by
      linarith [hx.1.1, hx.2.1, hy.1.1, hy.2.1]
    exact_mod_cast hreR
  have hac : a.im ≤ c.im + 1 := by
    have hacR : ((a.im : Int) : Real) ≤ ((c.im : Int) : Real) + 1 := by
      linarith [hx.1.2, hx.2.2, hy.1.2, hy.2.2]
    exact_mod_cast hacR
  have hca : c.im ≤ a.im + 1 := by
    have hcaR : ((c.im : Int) : Real) ≤ ((a.im : Int) : Real) + 1 := by
      linarith [hx.1.2, hx.2.2, hy.1.2, hy.2.2]
    exact_mod_cast hcaR
  have him : a.im = c.im ∨ a.im = c.im + 1 ∨ c.im = a.im + 1 := by omega
  rcases him with him | him | him
  · have hacEq : a = c := by
      apply Zsqrtd.ext <;> simp [hre, him]
    exact ⟨a, by simp, by simp [hacEq]⟩
  · have hacEq : a = c + J := by
      apply Zsqrtd.ext <;> simp [hre, him, J]
    exact ⟨a, by simp, by simp [hacEq]⟩
  · have hcaEq : c = a + J := by
      apply Zsqrtd.ext <;> simp [hre, him, J]
    exact ⟨c, by simp [hcaEq], by simp⟩

private theorem cross_inter (a c : GaussianInt) :
      (GridEdgeCarrier ({a, a + 1} : Finset GaussianInt) ∩
        GridEdgeCarrier ({c, c + J} : Finset GaussianInt)).Nonempty →
        ∃ z, z ∈ ({a, a + 1} : Finset GaussianInt) ∧
          z ∈ ({c, c + J} : Finset GaussianInt) := by
  classical
  let J : GaussianInt := ⟨0, 1⟩
  have carrier_pair (a b : GaussianInt) :
      GridEdgeCarrier ({a, b} : Finset GaussianInt) =
        Set.uIcc (GaussianRealPoint a) (GaussianRealPoint b) := carrier_pair a b
  change ((GridEdgeCarrier ({a, a + 1} : Finset GaussianInt) ∩
        GridEdgeCarrier ({c, c + J} : Finset GaussianInt)).Nonempty →
        ∃ z, z ∈ ({a, a + 1} : Finset GaussianInt) ∧
          z ∈ ({c, c + J} : Finset GaussianInt))
  rintro ⟨⟨x, y⟩, hx, hy⟩
  rw [carrier_pair] at hx hy
  simp only [Set.uIcc, GaussianRealPoint, Int.reduceNeg, GaussianInt.intCast_re,
      GaussianInt.intCast_im, Zsqrtd.re_add, Zsqrtd.re_one, Int.cast_add, Int.cast_one,
      Zsqrtd.im_add, Zsqrtd.im_one, add_zero, Prod.mk_le_mk, le_add_iff_nonneg_right,
      zero_le_one, Std.le_refl, and_self, inf_of_le_left, sup_of_le_right, Set.mem_Icc, J]
      at hx hy
  rw [← GaussianInt.intCast_re a, ← GaussianInt.intCast_im a] at hx
  rw [← GaussianInt.intCast_re c, ← GaussianInt.intCast_im c] at hy
  have hca : c.re = a.re ∨ c.re = a.re + 1 := by
    have hlo : a.re ≤ c.re := by
      have hr : ((a.re : Int) : Real) ≤ ((c.re : Int) : Real) := by
        linarith [hx.1.1, hy.2.1]
      exact_mod_cast hr
    have hhi : c.re ≤ a.re + 1 := by
      have hr : ((c.re : Int) : Real) ≤ ((a.re : Int) : Real) + 1 := by
        linarith [hy.1.1, hx.2.1]
      exact_mod_cast hr
    omega
  have hac : a.im = c.im ∨ a.im = c.im + 1 := by
    have hlo : c.im ≤ a.im := by
      have hr : ((c.im : Int) : Real) ≤ ((a.im : Int) : Real) := by
        linarith [hy.1.2, hx.2.2]
      exact_mod_cast hr
    have hhi : a.im ≤ c.im + 1 := by
      have hr : ((a.im : Int) : Real) ≤ ((c.im : Int) : Real) + 1 := by
        linarith [hx.1.2, hy.2.2]
      exact_mod_cast hr
    omega
  rcases hca with hca | hca <;> rcases hac with hac | hac
  · have h : a = c := by apply Zsqrtd.ext <;> simp [hca, hac]
    exact ⟨a, by simp, by simp [h]⟩
  · have h : a = c + J := by apply Zsqrtd.ext <;> simp [hca, hac, J]
    exact ⟨a, by simp, by simp [h]⟩
  · have h : a + 1 = c := by apply Zsqrtd.ext <;> simp [hca, hac]
    exact ⟨a + 1, by simp, by simp [h]⟩
  · have h : a + 1 = c + J := by apply Zsqrtd.ext <;> simp [hca, hac, J]
    exact ⟨a + 1, by simp, by simp [h]⟩

private theorem carrier_intersection (E : Set (Finset GaussianInt)) (hgrid : ∀ e ∈ E, ∃ a b :
    GaussianInt, e = {a, b} ∧ FourNeighborAdjacent a b) {e f : Finset GaussianInt} (he : e ∈ E)
    (hf : f ∈ E) :
      (GridEdgeCarrier e ∩ GridEdgeCarrier f).Nonempty ↔
        ∃ z, z ∈ e ∧ z ∈ f := by
  classical
  let J : GaussianInt := ⟨0, 1⟩
  have canonical (e : Finset GaussianInt) (he : e ∈ E) :
      ∃ a : GaussianInt, e = {a, a + 1} ∨ e = {a, a + J} := canonical E hgrid e he
  have point_of_common {e f : Finset GaussianInt} {z : GaussianInt}
      (hze : z ∈ e) (hzf : z ∈ f) :
      (GridEdgeCarrier e ∩ GridEdgeCarrier f).Nonempty := point_of_common (e := e) (f := f) (z :=
          z) hze hzf
  have horizontal_inter (a c : GaussianInt) :
      (GridEdgeCarrier ({a, a + 1} : Finset GaussianInt) ∩
        GridEdgeCarrier ({c, c + 1} : Finset GaussianInt)).Nonempty →
        ∃ z, z ∈ ({a, a + 1} : Finset GaussianInt) ∧
          z ∈ ({c, c + 1} : Finset GaussianInt) := horizontal_inter a c
  have vertical_inter (a c : GaussianInt) :
      (GridEdgeCarrier ({a, a + J} : Finset GaussianInt) ∩
        GridEdgeCarrier ({c, c + J} : Finset GaussianInt)).Nonempty →
        ∃ z, z ∈ ({a, a + J} : Finset GaussianInt) ∧
          z ∈ ({c, c + J} : Finset GaussianInt) := vertical_inter a c
  have cross_inter (a c : GaussianInt) :
      (GridEdgeCarrier ({a, a + 1} : Finset GaussianInt) ∩
        GridEdgeCarrier ({c, c + J} : Finset GaussianInt)).Nonempty →
        ∃ z, z ∈ ({a, a + 1} : Finset GaussianInt) ∧
          z ∈ ({c, c + J} : Finset GaussianInt) := cross_inter a c
  constructor
  · rcases canonical e he with ⟨a, rfl | rfl⟩ <;>
      rcases canonical f hf with ⟨c, rfl | rfl⟩
    · exact horizontal_inter a c
    · exact cross_inter a c
    · intro h
      rcases cross_inter c a (by simpa [Set.inter_comm] using h) with ⟨z, hz1, hz2⟩
      exact ⟨z, hz2, hz1⟩
    · exact vertical_inter a c
  · rintro ⟨z, hze, hzf⟩
    exact point_of_common hze hzf

private noncomputable def step (E : Set (Finset GaussianInt)) : Finset GaussianInt → Finset
    GaussianInt → Prop := fun e f =>
    e ∈ E ∧ f ∈ E ∧ (GridEdgeCarrier e ∩ GridEdgeCarrier f).Nonempty

private noncomputable def reach (E : Set (Finset GaussianInt)) : Finset GaussianInt → Finset
    GaussianInt → Prop := Relation.ReflTransGen (step E)

private theorem step_symm (E : Set (Finset GaussianInt)) {e f : Finset GaussianInt} (hef : (step
    E) e f) : (step E) f e := by
  classical
  let step : Finset GaussianInt → Finset GaussianInt → Prop := fun e f =>
    e ∈ E ∧ f ∈ E ∧ (GridEdgeCarrier e ∩ GridEdgeCarrier f).Nonempty
  change (step f e)
  refine ⟨hef.2.1, hef.1, ?_⟩
  simpa only [Set.inter_comm] using hef.2.2

private theorem reach_symm (E : Set (Finset GaussianInt)) {e f : Finset GaussianInt} (hef :
    (reach E) e f) : (reach E) f e := by
  classical
  let step : Finset GaussianInt → Finset GaussianInt → Prop := fun e f =>
    e ∈ E ∧ f ∈ E ∧ (GridEdgeCarrier e ∩ GridEdgeCarrier f).Nonempty
  let reach : Finset GaussianInt → Finset GaussianInt → Prop :=
    Relation.ReflTransGen step
  have step_symm {e f : Finset GaussianInt} (hef : step e f) : step f e := step_symm E (e := e)
      (f := f) hef
  change (reach f e)
  induction hef using Relation.ReflTransGen.head_induction_on with
  | refl => exact Relation.ReflTransGen.refl
  | @head a b hab hrest ih =>
      exact Relation.ReflTransGen.trans ih
        (Relation.ReflTransGen.single (step_symm hab))

private theorem carrier_closed (E : Set (Finset GaussianInt)) (hgrid : ∀ e ∈ E, ∃ a b :
    GaussianInt, e = {a, b} ∧ FourNeighborAdjacent a b) {e : Finset GaussianInt} (he : e ∈ E) :
      IsClosed (GridEdgeCarrier e) := by
  classical
  let J : GaussianInt := ⟨0, 1⟩
  have carrier_pair (a b : GaussianInt) :
      GridEdgeCarrier ({a, b} : Finset GaussianInt) =
        Set.uIcc (GaussianRealPoint a) (GaussianRealPoint b) := carrier_pair a b
  have canonical (e : Finset GaussianInt) (he : e ∈ E) :
      ∃ a : GaussianInt, e = {a, a + 1} ∨ e = {a, a + J} := canonical E hgrid e he
  rcases canonical e he with ⟨a, rfl | rfl⟩ <;>
    rw [carrier_pair] <;> exact isClosed_Icc

private theorem carrier_nonempty (E : Set (Finset GaussianInt)) (hgrid : ∀ e ∈ E, ∃ a b :
    GaussianInt, e = {a, b} ∧ FourNeighborAdjacent a b) {e : Finset GaussianInt} (he : e ∈ E) :
      (GridEdgeCarrier e).Nonempty := by
  classical
  let J : GaussianInt := ⟨0, 1⟩
  have canonical (e : Finset GaussianInt) (he : e ∈ E) :
      ∃ a : GaussianInt, e = {a, a + 1} ∨ e = {a, a + J} := canonical E hgrid e he
  rcases canonical e he with ⟨a, rfl | rfl⟩
  · exact ⟨GaussianRealPoint a, by unfold GridEdgeCarrier; simp⟩
  · exact ⟨GaussianRealPoint a, by unfold GridEdgeCarrier; simp⟩

private theorem E_nonempty (E : Set (Finset GaussianInt)) (hconnected : IsConnected (⋃ e ∈ E,
    GridEdgeCarrier e)) : E.Nonempty := by
  classical
  rcases hconnected.nonempty with ⟨p, hp⟩
  simp only [Set.mem_iUnion] at hp
  rcases hp with ⟨e, he, hp⟩
  exact ⟨e, he⟩

private theorem reach_all (E : Set (Finset GaussianInt)) (hEfinite : E.Finite) (hgrid : ∀ e ∈ E,
    ∃ a b : GaussianInt, e = {a, b} ∧ FourNeighborAdjacent a b) (hconnected : IsConnected (⋃ e ∈
    E, GridEdgeCarrier e)) (e0 : Finset GaussianInt) (he0 : e0 ∈ E) : ∀ f ∈ E, (reach E) e0 f := by
  classical
  let step : Finset GaussianInt → Finset GaussianInt → Prop := fun e f =>
    e ∈ E ∧ f ∈ E ∧ (GridEdgeCarrier e ∩ GridEdgeCarrier f).Nonempty
  let reach : Finset GaussianInt → Finset GaussianInt → Prop :=
    Relation.ReflTransGen step
  have carrier_closed {e : Finset GaussianInt} (he : e ∈ E) :
      IsClosed (GridEdgeCarrier e) := carrier_closed E hgrid (e := e) he
  have carrier_nonempty {e : Finset GaussianInt} (he : e ∈ E) :
      (GridEdgeCarrier e).Nonempty := carrier_nonempty E hgrid (e := e) he
  change (∀ f ∈ E, reach e0 f)
  intro f hf
  by_contra hnot
  let edgeFinset : Finset (Finset GaussianInt) := hEfinite.toFinset
  let component : Finset (Finset GaussianInt) :=
    edgeFinset.filter (fun e => reach e0 e)
  let remainder : Finset (Finset GaussianInt) := edgeFinset \ component
  let A : Set (Real × Real) := ⋃ e ∈ component, GridEdgeCarrier e
  let B : Set (Real × Real) := ⋃ e ∈ remainder, GridEdgeCarrier e
  have he0C : e0 ∈ component := by
    apply Finset.mem_filter.2
    exact ⟨hEfinite.mem_toFinset.mpr he0, Relation.ReflTransGen.refl⟩
  have hfR : f ∈ remainder := by
    apply Finset.mem_sdiff.2
    refine ⟨hEfinite.mem_toFinset.mpr hf, ?_⟩
    intro hfC
    exact hnot (Finset.mem_filter.1 hfC).2
  have Aclosed : IsClosed A := by
    dsimp [A]
    apply isClosed_biUnion_finset
    intro e heC
    exact carrier_closed (hEfinite.mem_toFinset.mp (Finset.mem_filter.1 heC).1)
  have Bclosed : IsClosed B := by
    dsimp [B]
    apply isClosed_biUnion_finset
    intro e heR
    exact carrier_closed
      (hEfinite.mem_toFinset.mp (Finset.mem_sdiff.1 heR).1)
  have unionCovers : (⋃ e ∈ E, GridEdgeCarrier e) ⊆ A ∪ B := by
    intro p hp
    simp only [Set.mem_iUnion] at hp
    rcases hp with ⟨e, he, hp⟩
    by_cases heC : e ∈ component
    · left
      exact Set.mem_iUnion.2 ⟨e, Set.mem_iUnion.2 ⟨heC, hp⟩⟩
    · right
      have heR : e ∈ remainder := Finset.mem_sdiff.2
        ⟨hEfinite.mem_toFinset.mpr he, heC⟩
      exact Set.mem_iUnion.2 ⟨e, Set.mem_iUnion.2 ⟨heR, hp⟩⟩
  have separated : A ∩ B = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro p hp
    change p ∈ (⋃ e ∈ component, GridEdgeCarrier e) ∩
      (⋃ e ∈ remainder, GridEdgeCarrier e) at hp
    rcases Set.mem_iUnion.1 hp.1 with ⟨e, hpA⟩
    rcases Set.mem_iUnion.1 hpA with ⟨heC, hpe⟩
    rcases Set.mem_iUnion.1 hp.2 with ⟨g, hpB⟩
    rcases Set.mem_iUnion.1 hpB with ⟨hgR, hpg⟩
    have heE : e ∈ E :=
      hEfinite.mem_toFinset.mp (Finset.mem_filter.1 heC).1
    have heReach : reach e0 e := (Finset.mem_filter.1 heC).2
    have hgE : g ∈ E :=
      hEfinite.mem_toFinset.mp (Finset.mem_sdiff.1 hgR).1
    have hgNot : ¬ reach e0 g := by
      intro hgReach
      exact (Finset.mem_sdiff.1 hgR).2
        (Finset.mem_filter.2 ⟨hEfinite.mem_toFinset.mpr hgE, hgReach⟩)
    exact hgNot (Relation.ReflTransGen.trans heReach
      (Relation.ReflTransGen.single ⟨heE, hgE, ⟨p, hpe, hpg⟩⟩))
  have firstPoint : ∃ p, p ∈ (⋃ e ∈ E, GridEdgeCarrier e) ∧ p ∈ A := by
    rcases carrier_nonempty he0 with ⟨p, hp⟩
    exact ⟨p, Set.mem_iUnion.2 ⟨e0, Set.mem_iUnion.2 ⟨he0, hp⟩⟩,
      Set.mem_iUnion.2 ⟨e0, Set.mem_iUnion.2 ⟨he0C, hp⟩⟩⟩
  have secondPoint : ∃ p, p ∈ (⋃ e ∈ E, GridEdgeCarrier e) ∧ p ∈ B := by
    rcases carrier_nonempty hf with ⟨p, hp⟩
    exact ⟨p, Set.mem_iUnion.2 ⟨f, Set.mem_iUnion.2 ⟨hf, hp⟩⟩,
      Set.mem_iUnion.2 ⟨f, Set.mem_iUnion.2 ⟨hfR, hp⟩⟩⟩
  have separatedRelative :
      (⋃ e ∈ E, GridEdgeCarrier e) ∩ (A ∩ B) = ∅ := by
    rw [separated]
    simp
  rcases (isPreconnected_iff_subset_of_disjoint_closed.mp
    hconnected.isPreconnected A B Aclosed Bclosed unionCovers separatedRelative) with
    hsubA | hsubB
  · rcases secondPoint with ⟨p, hpK, hpB⟩
    have : p ∈ A ∩ B := ⟨hsubA hpK, hpB⟩
    rw [separated] at this
    exact this
  · rcases firstPoint with ⟨p, hpK, hpA⟩
    have : p ∈ A ∩ B := ⟨hpA, hsubB hpK⟩
    rw [separated] at this
    exact this

private theorem edge_reachable (E : Set (Finset GaussianInt)) (hgrid : ∀ e ∈ E, ∃ a b :
    GaussianInt, e = {a, b} ∧ FourNeighborAdjacent a b) {e : Finset GaussianInt} (he : e ∈ E)
      (u v : (X E)) (hu : u.1 ∈ e) (hv : v.1 ∈ e) : (G E).Reachable u v := by
  classical
  let X : Set GaussianInt := {x | ∃ e ∈ E, x ∈ e}
  let G : SimpleGraph X := SimpleGraph.fromRel fun a b =>
    ({a.1, b.1} : Finset GaussianInt) ∈ E
  let J : GaussianInt := ⟨0, 1⟩
  have canonical (e : Finset GaussianInt) (he : e ∈ E) :
      ∃ a : GaussianInt, e = {a, a + 1} ∨ e = {a, a + J} := canonical E hgrid e he
  change (G.Reachable u v)
  by_cases huv : u = v
  · subst v
    exact SimpleGraph.Reachable.rfl
  apply SimpleGraph.Adj.reachable
  simp only [G]
  refine ⟨huv, Or.inl ?_⟩
  have hval : u.1 ≠ v.1 := by
    intro h
    exact huv (Subtype.ext h)
  rcases canonical e he with ⟨a, rfl | rfl⟩
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
    rcases hu with hu | hu <;> rcases hv with hv | hv
    · exact (hval (hu.trans hv.symm)).elim
    · simpa [hu, hv]
    · simpa [hu, hv, Finset.pair_comm] using he
    · exact (hval (hu.trans hv.symm)).elim
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
    rcases hu with hu | hu <;> rcases hv with hv | hv
    · exact (hval (hu.trans hv.symm)).elim
    · simpa [hu, hv]
    · simpa [hu, hv, Finset.pair_comm] using he
    · exact (hval (hu.trans hv.symm)).elim

private theorem chain_graph (E : Set (Finset GaussianInt)) (hgrid : ∀ e ∈ E, ∃ a b : GaussianInt,
    e = {a, b} ∧ FourNeighborAdjacent a b) : ∀ {e f : Finset GaussianInt}, e ∈ E → f ∈ E → (reach
    E) e f →
      ∀ (u v : (X E)), u.1 ∈ e → v.1 ∈ f → (G E).Reachable u v := by
  classical
  let X : Set GaussianInt := {x | ∃ e ∈ E, x ∈ e}
  let G : SimpleGraph X := SimpleGraph.fromRel fun a b =>
    ({a.1, b.1} : Finset GaussianInt) ∈ E
  have carrier_intersection {e f : Finset GaussianInt} (he : e ∈ E) (hf : f ∈ E) :
      (GridEdgeCarrier e ∩ GridEdgeCarrier f).Nonempty ↔
        ∃ z, z ∈ e ∧ z ∈ f := carrier_intersection E hgrid (e := e) (f := f) he hf
  let step : Finset GaussianInt → Finset GaussianInt → Prop := fun e f =>
    e ∈ E ∧ f ∈ E ∧ (GridEdgeCarrier e ∩ GridEdgeCarrier f).Nonempty
  let reach : Finset GaussianInt → Finset GaussianInt → Prop :=
    Relation.ReflTransGen step
  have edge_reachable {e : Finset GaussianInt} (he : e ∈ E)
      (u v : X) (hu : u.1 ∈ e) (hv : v.1 ∈ e) : G.Reachable u v := edge_reachable E hgrid (e :=
          e) he u v hu hv
  change (∀ {e f : Finset GaussianInt}, e ∈ E → f ∈ E → reach e f →
      ∀ (u v : X), u.1 ∈ e → v.1 ∈ f → G.Reachable u v)
  intro e f he hf hef
  induction hef using Relation.ReflTransGen.head_induction_on with
  | refl =>
      intro u v hu hv
      exact edge_reachable he u v hu hv
  | @head a b hab hrest ih =>
      intro u v hu hv
      rcases (carrier_intersection hab.1 hab.2.1).mp hab.2.2 with
        ⟨z, hza, hzb⟩
      let w : X := ⟨z, ⟨a, hab.1, hza⟩⟩
      have huw : G.Reachable u w := edge_reachable hab.1 u w hu hza
      have hwv : G.Reachable w v := ih hab.2.1 w v hzb hv
      exact huw.trans hwv

private theorem X_nonempty (E : Set (Finset GaussianInt)) (hgrid : ∀ e ∈ E, ∃ a b : GaussianInt,
    e = {a, b} ∧ FourNeighborAdjacent a b) (e0 : Finset GaussianInt) (he0 : e0 ∈ E) : Nonempty (X
    E) := by
  classical
  let X : Set GaussianInt := {x | ∃ e ∈ E, x ∈ e}
  let J : GaussianInt := ⟨0, 1⟩
  have canonical (e : Finset GaussianInt) (he : e ∈ E) :
      ∃ a : GaussianInt, e = {a, a + 1} ∨ e = {a, a + J} := canonical E hgrid e he
  change (Nonempty X)
  rcases canonical e0 he0 with ⟨a, ha | ha⟩
  · refine ⟨⟨a, ?_⟩⟩
    exact ⟨e0, he0, ha.symm ▸ by simp⟩
  · refine ⟨⟨a, ?_⟩⟩
    exact ⟨e0, he0, ha.symm ▸ by simp⟩

end ConnectedEdgeGraph

theorem ConnectedGridEdgeCarrierGraph
    (E : Set (Finset GaussianInt))
    (hEfinite : E.Finite)
    (hgrid : ∀ e ∈ E, ∃ a b : GaussianInt,
      e = {a, b} ∧ FourNeighborAdjacent a b)
    (hconnected : IsConnected (⋃ e ∈ E, GridEdgeCarrier e)) :
    let X : Set GaussianInt := {x | ∃ e ∈ E, x ∈ e}
    let G : SimpleGraph X := SimpleGraph.fromRel fun a b =>
      ({a.1, b.1} : Finset GaussianInt) ∈ E
    G.Connected := by
-- BODY
  classical
  dsimp only
  let X : Set GaussianInt := {x | ∃ e ∈ E, x ∈ e}
  let G : SimpleGraph X := SimpleGraph.fromRel fun a b =>
    ({a.1, b.1} : Finset GaussianInt) ∈ E
  change G.Connected
  let J : GaussianInt := ⟨0, 1⟩
  have carrier_pair (a b : GaussianInt) :
      GridEdgeCarrier ({a, b} : Finset GaussianInt) =
        Set.uIcc (GaussianRealPoint a) (GaussianRealPoint b) := ConnectedEdgeGraph.carrier_pair a b
  have canonical (e : Finset GaussianInt) (he : e ∈ E) :
      ∃ a : GaussianInt, e = {a, a + 1} ∨ e = {a, a + J} := ConnectedEdgeGraph.canonical E hgrid
          e he
  have point_of_common {e f : Finset GaussianInt} {z : GaussianInt}
      (hze : z ∈ e) (hzf : z ∈ f) :
      (GridEdgeCarrier e ∩ GridEdgeCarrier f).Nonempty := ConnectedEdgeGraph.point_of_common (e
          := e) (f := f) (z := z) hze hzf
  have horizontal_inter (a c : GaussianInt) :
      (GridEdgeCarrier ({a, a + 1} : Finset GaussianInt) ∩
        GridEdgeCarrier ({c, c + 1} : Finset GaussianInt)).Nonempty →
        ∃ z, z ∈ ({a, a + 1} : Finset GaussianInt) ∧
          z ∈ ({c, c + 1} : Finset GaussianInt) := ConnectedEdgeGraph.horizontal_inter a c
  have vertical_inter (a c : GaussianInt) :
      (GridEdgeCarrier ({a, a + J} : Finset GaussianInt) ∩
        GridEdgeCarrier ({c, c + J} : Finset GaussianInt)).Nonempty →
        ∃ z, z ∈ ({a, a + J} : Finset GaussianInt) ∧
          z ∈ ({c, c + J} : Finset GaussianInt) := ConnectedEdgeGraph.vertical_inter a c
  have cross_inter (a c : GaussianInt) :
      (GridEdgeCarrier ({a, a + 1} : Finset GaussianInt) ∩
        GridEdgeCarrier ({c, c + J} : Finset GaussianInt)).Nonempty →
        ∃ z, z ∈ ({a, a + 1} : Finset GaussianInt) ∧
          z ∈ ({c, c + J} : Finset GaussianInt) := ConnectedEdgeGraph.cross_inter a c
  have carrier_intersection {e f : Finset GaussianInt} (he : e ∈ E) (hf : f ∈ E) :
      (GridEdgeCarrier e ∩ GridEdgeCarrier f).Nonempty ↔
        ∃ z, z ∈ e ∧ z ∈ f := ConnectedEdgeGraph.carrier_intersection E hgrid (e := e) (f := f)
            he hf
  let step : Finset GaussianInt → Finset GaussianInt → Prop := fun e f =>
    e ∈ E ∧ f ∈ E ∧ (GridEdgeCarrier e ∩ GridEdgeCarrier f).Nonempty
  let reach : Finset GaussianInt → Finset GaussianInt → Prop :=
    Relation.ReflTransGen step
  have step_symm {e f : Finset GaussianInt} (hef : step e f) : step f e :=
      ConnectedEdgeGraph.step_symm E (e := e) (f := f) hef
  have reach_symm {e f : Finset GaussianInt} (hef : reach e f) : reach f e :=
      ConnectedEdgeGraph.reach_symm E (e := e) (f := f) hef
  have carrier_closed {e : Finset GaussianInt} (he : e ∈ E) :
      IsClosed (GridEdgeCarrier e) := ConnectedEdgeGraph.carrier_closed E hgrid (e := e) he
  have carrier_nonempty {e : Finset GaussianInt} (he : e ∈ E) :
      (GridEdgeCarrier e).Nonempty := ConnectedEdgeGraph.carrier_nonempty E hgrid (e := e) he
  have E_nonempty : E.Nonempty := ConnectedEdgeGraph.E_nonempty E hconnected
  rcases E_nonempty with ⟨e0, he0⟩
  have reach_all : ∀ f ∈ E, reach e0 f := ConnectedEdgeGraph.reach_all E hEfinite hgrid
      hconnected e0 he0
  have edge_reachable {e : Finset GaussianInt} (he : e ∈ E)
      (u v : X) (hu : u.1 ∈ e) (hv : v.1 ∈ e) : G.Reachable u v :=
          ConnectedEdgeGraph.edge_reachable E hgrid (e := e) he u v hu hv
  have chain_graph : ∀ {e f : Finset GaussianInt}, e ∈ E → f ∈ E → reach e f →
      ∀ (u v : X), u.1 ∈ e → v.1 ∈ f → G.Reachable u v := ConnectedEdgeGraph.chain_graph E hgrid
  have X_nonempty : Nonempty X := ConnectedEdgeGraph.X_nonempty E hgrid e0 he0
  let _ : Nonempty X := X_nonempty
  apply SimpleGraph.Connected.mk
  intro u v
  rcases u.2 with ⟨e, he, hue⟩
  rcases v.2 with ⟨f, hf, hvf⟩
  have hef : reach e f := Relation.ReflTransGen.trans
    (reach_symm (reach_all e he)) (reach_all f hf)
  exact chain_graph he hf hef u v hue hvf

end ApollonianSuperharmonic

end
