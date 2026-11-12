/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BoundaryFootprintEdges
public import LeanPool.ApollonianSuperharmonic.BoundaryFootprintVertices
public import LeanPool.ApollonianSuperharmonic.CommonFootprintEdgeVertices
public import LeanPool.ApollonianSuperharmonic.FootprintEdges
public import LeanPool.ApollonianSuperharmonic.FootprintVertices
public import LeanPool.ApollonianSuperharmonic.ProtoTile
public import LeanPool.ApollonianSuperharmonic.TileRealization

-- [TABLET NODE: CellDisjointCommonFootprintIncidence]

/-!
# CellDisjointCommonFootprintIncidence

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace CommonFootprintIncidence

private noncomputable def I : GaussianInt := ⟨0, 1⟩

private theorem horiz_unique (x y : GaussianInt)
      (h : ({x, x + 1} : Finset GaussianInt) = {y, y + 1}) : x = y := by
  classical
  have hx : x = y ∨ x = y + 1 := by
    have : x ∈ ({y, y + 1} : Finset GaussianInt) := by rw [← h]; simp
    simpa using this
  have hy : y = x ∨ y = x + 1 := by
    have : y ∈ ({x, x + 1} : Finset GaussianInt) := by rw [h]; simp
    simpa using this
  rcases hx with hxy | hxy
  · exact hxy
  rcases hy with hyx | hyx
  · exact hyx.symm
  · exfalso
    have hre := congrArg Zsqrtd.re hxy
    have hre' := congrArg Zsqrtd.re hyx
    norm_num at hre hre'
    omega

private theorem vert_unique (x y : GaussianInt)
      (h : ({x, x + I} : Finset GaussianInt) = {y, y + I}) : x = y := by
  classical
  let I : GaussianInt := ⟨0, 1⟩
  change ({x, x + I} : Finset GaussianInt) = {y, y + I} at h
  have hx : x = y ∨ x = y + I := by
    have : x ∈ ({y, y + I} : Finset GaussianInt) := by rw [← h]; simp
    simpa using this
  have hy : y = x ∨ y = x + I := by
    have : y ∈ ({x, x + I} : Finset GaussianInt) := by rw [h]; simp
    simpa using this
  rcases hx with hxy | hxy
  · exact hxy
  rcases hy with hyx | hyx
  · exact hyx.symm
  · exfalso
    have him := congrArg Zsqrtd.im hxy
    have him' := congrArg Zsqrtd.im hyx
    simp [I] at him him'
    omega

private theorem horiz_ne_vert (x y : GaussianInt) :
      ({x, x + 1} : Finset GaussianInt) ≠ {y, y + I} := by
  classical
  let I : GaussianInt := ⟨0, 1⟩
  change (({x, x + 1} : Finset GaussianInt) ≠ {y, y + I})
  intro h
  have hx : x = y ∨ x = y + I := by
    have : x ∈ ({y, y + I} : Finset GaussianInt) := by rw [← h]; simp
    simpa using this
  have hx1 : x + 1 = y ∨ x + 1 = y + I := by
    have : x + 1 ∈ ({y, y + I} : Finset GaussianInt) := by rw [← h]; simp
    simpa using this
  rcases hx with hx | hx <;> rcases hx1 with hx1 | hx1
  all_goals
    have hre := congrArg Zsqrtd.re hx
    have him := congrArg Zsqrtd.im hx
    have hre1 := congrArg Zsqrtd.re hx1
    have him1 := congrArg Zsqrtd.im hx1
    simp [I] at hre him hre1 him1
    omega

private theorem footprint_normalize (T : ProtoTile) (e : Finset GaussianInt)
      (he : e ∈ FootprintEdges T) :
      (∃ z, e = {z, z + 1} ∧ (z ∈ T.cells ∨ z - I ∈ T.cells)) ∨
      (∃ z, e = {z, z + I} ∧ (z ∈ T.cells ∨ z - 1 ∈ T.cells)) := by
  classical
  let I : GaussianInt := ⟨0, 1⟩
  change ((∃ z, e = {z, z + 1} ∧ (z ∈ T.cells ∨ z - I ∈ T.cells)) ∨
      (∃ z, e = {z, z + I} ∧ (z ∈ T.cells ∨ z - 1 ∈ T.cells)))
  rcases he with ⟨x, hx, h | h | h | h⟩
  · exact Or.inl ⟨x, h, Or.inl hx⟩
  · exact Or.inr ⟨x, h, Or.inl hx⟩
  · refine Or.inr ⟨x + 1, h, Or.inr ?_⟩
    simpa [add_sub_cancel_right] using hx
  · refine Or.inl ⟨x + I, ?_, Or.inr ?_⟩
    · simpa [I, Zsqrtd.ext_iff, add_comm, add_left_comm, add_assoc] using h
    simpa [I, Zsqrtd.ext_iff] using hx

private theorem boundary_footprint (T : ProtoTile) (e : Finset GaussianInt)
      (he : e ∈ BoundaryFootprintEdges T) : e ∈ FootprintEdges T := by
  classical
  let I : GaussianInt := ⟨0, 1⟩
  rcases he with ⟨z, ⟨rfl, h⟩ | ⟨rfl, h⟩⟩
  · rcases h with ⟨hz, -⟩ | ⟨-, hz⟩
    · exact ⟨z, hz, Or.inl rfl⟩
    · refine ⟨z - I, hz, Or.inr (Or.inr (Or.inr ?_))⟩
      congr 1 <;> simp [I, Zsqrtd.ext_iff]
  · rcases h with ⟨hz, -⟩ | ⟨-, hz⟩
    · exact ⟨z, hz, Or.inr (Or.inl rfl)⟩
    · refine ⟨z - 1, hz, Or.inr (Or.inr (Or.inl ?_))⟩
      congr 1 <;> simp []

private theorem hEdge (U : ProtoTile) (V : ProtoTile) (hdisjoint : Disjoint U.cells V.cells) :
    FootprintEdges U ∩ FootprintEdges V =
      BoundaryFootprintEdges U ∩ BoundaryFootprintEdges V := by
  classical
  let I : GaussianInt := ⟨0, 1⟩
  have horiz_unique (x y : GaussianInt)
      (h : ({x, x + 1} : Finset GaussianInt) = {y, y + 1}) : x = y := horiz_unique x y h
  have vert_unique (x y : GaussianInt)
      (h : ({x, x + I} : Finset GaussianInt) = {y, y + I}) : x = y := vert_unique x y h
  have horiz_ne_vert (x y : GaussianInt) :
      ({x, x + 1} : Finset GaussianInt) ≠ {y, y + I} := horiz_ne_vert x y
  have footprint_normalize (T : ProtoTile) (e : Finset GaussianInt)
      (he : e ∈ FootprintEdges T) :
      (∃ z, e = {z, z + 1} ∧ (z ∈ T.cells ∨ z - I ∈ T.cells)) ∨
      (∃ z, e = {z, z + I} ∧ (z ∈ T.cells ∨ z - 1 ∈ T.cells)) := footprint_normalize T e he
  have boundary_footprint (T : ProtoTile) (e : Finset GaussianInt)
      (he : e ∈ BoundaryFootprintEdges T) : e ∈ FootprintEdges T := boundary_footprint T e he
  as_aux_lemma =>
  ext e
  constructor
  · rintro ⟨heU, heV⟩
    have hd := Finset.disjoint_left.mp hdisjoint
    rcases footprint_normalize U e heU with ⟨z, hz, hzU⟩ | ⟨z, hz, hzU⟩ <;>
      rcases footprint_normalize V e heV with ⟨w, hw, hwV⟩ | ⟨w, hw, hwV⟩
    · have bzw : z = w := horiz_unique z w (hz.symm.trans hw)
      subst w
      constructor <;> refine ⟨z, Or.inl ⟨?_, ?_⟩⟩
      · exact hz
      · rcases hzU with hzU | hzU <;> rcases hwV with hzV | hzV
        · exact (hd hzU hzV).elim
        · exact Or.inl ⟨hzU, fun hbad => hd hbad hzV⟩
        · exact Or.inr ⟨fun hbad => hd hbad hzV, hzU⟩
        · exact (hd hzU hzV).elim
      · exact hz
      · rcases hzU with hzU | hzU <;> rcases hwV with hzV | hzV
        · exact (hd hzU hzV).elim
        · exact Or.inr ⟨fun hbad => hd hzU hbad, hzV⟩
        · exact Or.inl ⟨hzV, fun hbad => hd hzU hbad⟩
        · exact (hd hzU hzV).elim
    · exact (horiz_ne_vert z w (hz.symm.trans hw)).elim
    · exact (horiz_ne_vert w z (hw.symm.trans hz)).elim
    · have bzw : z = w := vert_unique z w (hz.symm.trans hw)
      subst w
      constructor <;> refine ⟨z, Or.inr ⟨?_, ?_⟩⟩
      · exact hz
      · rcases hzU with hzU | hzU <;> rcases hwV with hzV | hzV
        · exact (hd hzU hzV).elim
        · exact Or.inl ⟨hzU, fun hbad => hd hbad hzV⟩
        · exact Or.inr ⟨fun hbad => hd hbad hzV, hzU⟩
        · exact (hd hzU hzV).elim
      · exact hz
      · rcases hzU with hzU | hzU <;> rcases hwV with hzV | hzV
        · exact (hd hzU hzV).elim
        · exact Or.inr ⟨fun hbad => hd hzU hbad, hzV⟩
        · exact Or.inl ⟨hzV, fun hbad => hd hzU hbad⟩
        · exact (hd hzU hzV).elim
  · rintro ⟨heU, heV⟩
    exact ⟨boundary_footprint U e heU, boundary_footprint V e heV⟩

private noncomputable def toR : GaussianInt → Real × Real := fun z => ((z.re : Int), (z.im : Int))

private theorem vertex_realization (T : ProtoTile) (hne : T.cells.Nonempty)
      (z : GaussianInt) (hz : z ∈ FootprintVertices T) :
      toR z ∈ TileRealization T := by
  classical
  let toR : GaussianInt → Real × Real := fun z => ((z.re : Int), (z.im : Int))
  change (toR z ∈ TileRealization T)
  unfold FootprintVertices at hz
  rw [ite_eq_left hne] at hz
  rcases hz with ⟨c, hc, h | h | h | h⟩
  all_goals
    rw [TileRealization]
    refine Set.mem_iUnion.2 ⟨c, Set.mem_iUnion.2 ⟨hc, ?_⟩⟩
    subst z
    simp [ClosedSquareRealization, toR, Prod.le_def]

private theorem edge_vertex_footprint (T : ProtoTile) (e : Finset GaussianInt)
      (he : e ∈ FootprintEdges T) (z : GaussianInt) (hz : z ∈ e) :
      z ∈ FootprintVertices T := by
  classical
  rcases he with ⟨c, hc, he⟩
  unfold FootprintVertices
  rw [ite_eq_left ⟨c, hc⟩]
  rcases he with h | h | h | h <;> subst e
  all_goals simp only [Finset.mem_insert, Finset.mem_singleton] at hz
  · rcases hz with rfl | rfl
    · exact ⟨_, hc, Or.inl rfl⟩
    · exact ⟨_, hc, Or.inr (Or.inl rfl)⟩
  · rcases hz with rfl | rfl
    · exact ⟨_, hc, Or.inl rfl⟩
    · exact ⟨_, hc, Or.inr (Or.inr (Or.inl rfl))⟩
  · rcases hz with rfl | rfl
    · exact ⟨_, hc, Or.inr (Or.inl rfl)⟩
    · exact ⟨_, hc, Or.inr (Or.inr (Or.inr rfl))⟩
  · rcases hz with rfl | rfl
    · exact ⟨_, hc, Or.inr (Or.inr (Or.inl rfl))⟩
    · exact ⟨_, hc, Or.inr (Or.inr (Or.inr rfl))⟩

private theorem local_cell (z c : GaussianInt) (p : Real × Real)
      (hpnear : dist p (toR z) < (1 / 2 : Real))
      (hpsq : p ∈ ClosedSquareRealization c) :
      c = z ∨ c = z - 1 ∨ c = z - I ∨ c = z - 1 - I := by
  classical
  let I : GaussianInt := ⟨0, 1⟩
  let toR : GaussianInt → Real × Real := fun z => ((z.re : Int), (z.im : Int))
  change (c = z ∨ c = z - 1 ∨ c = z - I ∨ c = z - 1 - I)
  have hdist1 : |p.1 - (toR z).1| < (1 / 2 : Real) := by
    have := lt_of_le_of_lt (le_max_left (dist p.1 (toR z).1)
      (dist p.2 (toR z).2)) hpnear
    simpa [Prod.dist_eq, Real.dist_eq] using this
  have hdist2 : |p.2 - (toR z).2| < (1 / 2 : Real) := by
    have := lt_of_le_of_lt (le_max_right (dist p.1 (toR z).1)
      (dist p.2 (toR z).2)) hpnear
    simpa [Prod.dist_eq, Real.dist_eq] using this
  change (((c.re : Int) : Real), ((c.im : Int) : Real)) ≤ p ∧
    p ≤ ((((c.re : Int) : Real) + 1), (((c.im : Int) : Real) + 1)) at hpsq
  have hrele : c.re ≤ z.re := by
    by_contra hn
    have hstep : ((z.re : Int) : Real) + 1 ≤ ((c.re : Int) : Real) := by
      exact_mod_cast (show z.re + 1 ≤ c.re by omega)
    have habs := (abs_lt.mp hdist1).2
    dsimp [toR] at habs
    linarith [hpsq.1.1]
  have hrige : z.re - 1 ≤ c.re := by
    by_contra hn
    have hstep : ((c.re : Int) : Real) + 1 ≤ ((z.re : Int) : Real) - 1 := by
      exact_mod_cast (show c.re + 1 ≤ z.re - 1 by omega)
    have habs := (abs_lt.mp hdist1).1
    dsimp [toR] at habs
    linarith [hpsq.2.1]
  have himle : c.im ≤ z.im := by
    by_contra hn
    have hstep : ((z.im : Int) : Real) + 1 ≤ ((c.im : Int) : Real) := by
      exact_mod_cast (show z.im + 1 ≤ c.im by omega)
    have habs := (abs_lt.mp hdist2).2
    dsimp [toR] at habs
    linarith [hpsq.1.2]
  have himge : z.im - 1 ≤ c.im := by
    by_contra hn
    have hstep : ((c.im : Int) : Real) + 1 ≤ ((z.im : Int) : Real) - 1 := by
      exact_mod_cast (show c.im + 1 ≤ z.im - 1 by omega)
    have habs := (abs_lt.mp hdist2).1
    dsimp [toR] at habs
    linarith [hpsq.2.2]
  have hre : c.re = z.re ∨ c.re = z.re - 1 := by omega
  have him : c.im = z.im ∨ c.im = z.im - 1 := by omega
  rcases hre with hre | hre <;> rcases him with him | him
  · left; apply Zsqrtd.ext <;> simp [hre, him]
  · right; right; left; apply Zsqrtd.ext <;> simp [I, hre, him]
  · right; left; apply Zsqrtd.ext <;> simp [hre, him]
  · right; right; right; apply Zsqrtd.ext <;> simp [I, hre, him]

private theorem hVertex (U : ProtoTile) (V : ProtoTile) (hUne : U.cells.Nonempty) (hVne :
    V.cells.Nonempty) (hdisjoint : Disjoint U.cells V.cells) (hconnected : IsConnected
    (TileRealization U ∩ TileRealization V)) (hcommon : (FootprintEdges U ∩ FootprintEdges
    V).Nonempty) : FootprintVertices U ∩ FootprintVertices V =
      CommonFootprintEdgeVertices U V := by
  classical
  let I : GaussianInt := ⟨0, 1⟩
  let toR : GaussianInt → Real × Real := fun z => ((z.re : Int), (z.im : Int))
  have vertex_realization (T : ProtoTile) (hne : T.cells.Nonempty)
      (z : GaussianInt) (hz : z ∈ FootprintVertices T) :
      toR z ∈ TileRealization T := vertex_realization T hne z hz
  have edge_vertex_footprint (T : ProtoTile) (e : Finset GaussianInt)
      (he : e ∈ FootprintEdges T) (z : GaussianInt) (hz : z ∈ e) :
      z ∈ FootprintVertices T := edge_vertex_footprint T e he z hz
  have local_cell (z c : GaussianInt) (p : Real × Real)
      (hpnear : dist p (toR z) < (1 / 2 : Real))
      (hpsq : p ∈ ClosedSquareRealization c) :
      c = z ∨ c = z - 1 ∨ c = z - I ∨ c = z - 1 - I := local_cell z c p hpnear hpsq
  as_aux_lemma =>
  apply Set.Subset.antisymm
  · rintro z ⟨hzU, hzV⟩
    by_contra hznot
    have hd := Finset.disjoint_left.mp hdisjoint
    have local_isolation : ∀ p ∈ TileRealization U ∩ TileRealization V,
        dist p (toR z) < (1 / 2 : Real) → p = toR z := by
      as_aux_lemma =>
      intro p hp hpnear
      simp only [Set.mem_inter_iff, TileRealization, Set.mem_iUnion] at hp
      rcases hp.1 with ⟨c, hcU, hpc⟩
      rcases hp.2 with ⟨d, hdV, hpd⟩
      have hcd : c ≠ d := fun h => hd hcU (h ▸ hdV)
      rcases local_cell z c p hpnear hpc with hc | hc | hc | hc <;>
        rcases local_cell z d p hpnear hpd with hd' | hd' | hd' | hd'
      · exact (hcd (hc.trans hd'.symm)).elim
      · subst c; subst d
        exfalso; apply hznot
        refine ⟨{z, z + I}, ⟨⟨z, hcU, Or.inr (Or.inl rfl)⟩,
          ⟨z - 1, hdV, Or.inr (Or.inr (Or.inl ?_))⟩⟩, by simp⟩
        simp [I, add_comm]
      · subst c; subst d
        exfalso; apply hznot
        refine ⟨{z, z + 1}, ⟨⟨z, hcU, Or.inl rfl⟩,
          ⟨z - I, hdV, Or.inr (Or.inr (Or.inr ?_))⟩⟩, by simp⟩
        simp [I, add_comm, add_left_comm]
      · subst c; subst d
        simp only [ClosedSquareRealization, Set.mem_Icc, Prod.le_def] at hpc hpd
        apply Prod.ext <;> dsimp [toR]
        · norm_num [I, Zsqrtd.re_sub, Zsqrtd.im_sub] at hpc hpd ⊢; linarith
        · norm_num [I, Zsqrtd.re_sub, Zsqrtd.im_sub] at hpc hpd ⊢; linarith
      · subst c; subst d
        exfalso; apply hznot
        refine ⟨{z, z + I}, ⟨⟨z - 1, hcU, Or.inr (Or.inr (Or.inl ?_))⟩,
          ⟨z, hdV, Or.inr (Or.inl rfl)⟩⟩, by simp⟩
        simp [I, add_comm]
      · exact (hcd (hc.trans hd'.symm)).elim
      · subst c; subst d
        simp only [ClosedSquareRealization, Set.mem_Icc, Prod.le_def] at hpc hpd
        apply Prod.ext <;> dsimp [toR]
        · norm_num [I, Zsqrtd.re_sub, Zsqrtd.im_sub] at hpc hpd ⊢; linarith
        · norm_num [I, Zsqrtd.re_sub, Zsqrtd.im_sub] at hpc hpd ⊢; linarith
      · subst c; subst d
        exfalso; apply hznot
        refine ⟨{z - 1, z}, ⟨⟨z - 1, hcU, Or.inl ?_⟩,
          ⟨z - 1 - I, hdV, Or.inr (Or.inr (Or.inr ?_))⟩⟩, by simp⟩
        all_goals simp [I, add_comm, add_left_comm]
      · subst c; subst d
        exfalso; apply hznot
        refine ⟨{z, z + 1}, ⟨⟨z - I, hcU, Or.inr (Or.inr (Or.inr ?_))⟩,
          ⟨z, hdV, Or.inl rfl⟩⟩, by simp⟩
        simp [I, add_comm, add_left_comm]
      · subst c; subst d
        simp only [ClosedSquareRealization, Set.mem_Icc, Prod.le_def] at hpc hpd
        apply Prod.ext <;> dsimp [toR]
        · norm_num [I, Zsqrtd.re_sub, Zsqrtd.im_sub] at hpc hpd ⊢; linarith
        · norm_num [I, Zsqrtd.re_sub, Zsqrtd.im_sub] at hpc hpd ⊢; linarith
      · exact (hcd (hc.trans hd'.symm)).elim
      · subst c; subst d
        exfalso; apply hznot
        refine ⟨{z - I, z}, ⟨⟨z - I, hcU, Or.inr (Or.inl ?_)⟩,
          ⟨z - 1 - I, hdV, Or.inr (Or.inr (Or.inl ?_))⟩⟩, by simp⟩
        all_goals congr 1
        all_goals try simp only [Finset.singleton_inj]
        all_goals apply Zsqrtd.ext <;> simp [I]
      · subst c; subst d
        simp only [ClosedSquareRealization, Set.mem_Icc, Prod.le_def] at hpc hpd
        apply Prod.ext <;> dsimp [toR]
        · norm_num [I, Zsqrtd.re_sub, Zsqrtd.im_sub] at hpc hpd ⊢; linarith
        · norm_num [I, Zsqrtd.re_sub, Zsqrtd.im_sub] at hpc hpd ⊢; linarith
      · subst c; subst d
        exfalso; apply hznot
        refine ⟨{z - 1, z}, ⟨⟨z - 1 - I, hcU, Or.inr (Or.inr (Or.inr ?_))⟩,
          ⟨z - 1, hdV, Or.inl ?_⟩⟩, by simp⟩
        all_goals congr 1
        all_goals try simp only [Finset.singleton_inj]
        all_goals apply Zsqrtd.ext <;> simp [I]
      · subst c; subst d
        exfalso; apply hznot
        refine ⟨{z - I, z}, ⟨⟨z - 1 - I, hcU, Or.inr (Or.inr (Or.inl ?_))⟩,
          ⟨z - I, hdV, Or.inr (Or.inl ?_)⟩⟩, by simp⟩
        all_goals congr 1
        all_goals try simp only [Finset.singleton_inj]
        all_goals apply Zsqrtd.ext <;> simp [I]
      · exact (hcd (hc.trans hd'.symm)).elim
    let K := TileRealization U ∩ TileRealization V
    let A : Set (Real × Real) := {toR z}
    let B : Set (Real × Real) := {p | (1 / 2 : Real) ≤ dist p (toR z)}
    have hAclosed : IsClosed A := isClosed_singleton
    have hBclosed : IsClosed B := by
      change IsClosed ((fun p : Real × Real => dist p (toR z)) ⁻¹' Set.Ici (1 / 2 : Real))
      exact isClosed_Ici.preimage (continuous_id.dist continuous_const)
    have hcover : K ⊆ A ∪ B := by
      intro p hp
      by_cases hnear : dist p (toR z) < (1 / 2 : Real)
      · left; simpa [A] using local_isolation p hp hnear
      · right; exact le_of_not_gt hnear
    have hsep : K ∩ (A ∩ B) = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro p hp
      have hpz : p = toR z := by simpa [A] using hp.2.1
      subst p
      have hbad : (1 / 2 : Real) ≤ dist (toR z) (toR z) := hp.2.2
      rw [dist_self] at hbad
      norm_num at hbad
    have hzK : toR z ∈ K := ⟨vertex_realization U hUne z hzU,
      vertex_realization V hVne z hzV⟩
    rcases hcommon with ⟨e, heU, heV⟩
    have htwo : ∃ y ∈ e, y ≠ z := by
      rcases heU with ⟨c, hc, rfl | rfl | rfl | rfl⟩
      · by_cases h : c = z
        · refine ⟨c + 1, by simp, ?_⟩
          intro hh; have := congrArg Zsqrtd.re hh; simp [h] at this
        · exact ⟨c, by simp, h⟩
      · by_cases h : c = z
        · refine ⟨c + I, by simp [I], ?_⟩
          intro hh; have := congrArg Zsqrtd.im hh; simp [h, I] at this
        · exact ⟨c, by simp, h⟩
      · by_cases h : c + 1 = z
        · refine ⟨c + 1 + I, by simp [I], ?_⟩
          intro hh; have := congrArg Zsqrtd.im hh; simp [h, I] at this
        · exact ⟨c + 1, by simp, h⟩
      · by_cases h : c + I = z
        · refine ⟨c + 1 + I, by simp [I], ?_⟩
          intro hh
          have h1 := congrArg Zsqrtd.re h
          have h2 := congrArg Zsqrtd.re hh
          simp [I] at h1 h2
          omega
        · exact ⟨c + I, by simp [I], h⟩
    rcases htwo with ⟨y, hye, hyz⟩
    have hyUfp := edge_vertex_footprint U e heU y hye
    have hyVfp := edge_vertex_footprint V e heV y hye
    have hyK : toR y ∈ K := ⟨vertex_realization U hUne y hyUfp,
      vertex_realization V hVne y hyVfp⟩
    have hyRne : toR y ≠ toR z := by
      intro h
      apply hyz
      apply Zsqrtd.ext
      · have h' := congrArg Prod.fst h
        dsimp [toR] at h'
        exact_mod_cast h'
      · have h' := congrArg Prod.snd h
        dsimp [toR] at h'
        exact_mod_cast h'
    rcases (isPreconnected_iff_subset_of_disjoint_closed.mp hconnected.isPreconnected
      A B hAclosed hBclosed hcover hsep) with hKA | hKB
    · exact hyRne (by simpa [A] using hKA hyK)
    · have : (1 / 2 : Real) ≤ 0 := by simpa [B] using hKB hzK
      norm_num at this
  · rintro z ⟨e, ⟨heU, heV⟩, hze⟩
    exact ⟨edge_vertex_footprint U e heU z hze,
      edge_vertex_footprint V e heV z hze⟩

end CommonFootprintIncidence

theorem CellDisjointCommonFootprintIncidence (U V : ProtoTile)
    (hUne : U.cells.Nonempty) (hVne : V.cells.Nonempty)
    (hdisjoint : Disjoint U.cells V.cells)
    (hconnected : IsConnected
      (TileRealization U ∩ TileRealization V))
    (hcommon :
      (FootprintEdges U ∩ FootprintEdges V).Nonempty) :
    FootprintEdges U ∩ FootprintEdges V =
        BoundaryFootprintEdges U ∩ BoundaryFootprintEdges V ∧
      FootprintVertices U ∩ FootprintVertices V =
        CommonFootprintEdgeVertices U V ∧
      BoundaryFootprintVertices U ∩ BoundaryFootprintVertices V =
        CommonFootprintEdgeVertices U V := by
-- BODY
  classical
  have boundary_footprint (T : ProtoTile) (e : Finset GaussianInt)
      (he : e ∈ BoundaryFootprintEdges T) : e ∈ FootprintEdges T :=
          CommonFootprintIncidence.boundary_footprint T e he
  have hEdge : FootprintEdges U ∩ FootprintEdges V =
      BoundaryFootprintEdges U ∩ BoundaryFootprintEdges V := CommonFootprintIncidence.hEdge U V
          hdisjoint
  have edge_vertex_footprint (T : ProtoTile) (e : Finset GaussianInt)
      (he : e ∈ FootprintEdges T) (z : GaussianInt) (hz : z ∈ e) :
      z ∈ FootprintVertices T := CommonFootprintIncidence.edge_vertex_footprint T e he z hz
  have hVertex : FootprintVertices U ∩ FootprintVertices V =
      CommonFootprintEdgeVertices U V := CommonFootprintIncidence.hVertex U V hUne hVne hdisjoint
          hconnected hcommon
  refine ⟨hEdge, hVertex, ?_⟩
  apply Set.Subset.antisymm
  · rintro z ⟨hzU, hzV⟩
    have boundary_vertex_footprint (T : ProtoTile) (hne : T.cells.Nonempty)
        (hz : z ∈ BoundaryFootprintVertices T) : z ∈ FootprintVertices T := by
      unfold BoundaryFootprintVertices at hz
      rw [ite_eq_left hne] at hz
      rcases hz with ⟨e, he, hze⟩
      exact edge_vertex_footprint T e (boundary_footprint T e he) z hze
    rw [← hVertex]
    exact ⟨boundary_vertex_footprint U hUne hzU,
      boundary_vertex_footprint V hVne hzV⟩
  · rintro z ⟨e, he, hze⟩
    have heBoundary : e ∈ BoundaryFootprintEdges U ∩
        BoundaryFootprintEdges V := hEdge ▸ he
    constructor
    · unfold BoundaryFootprintVertices
      rw [ite_eq_left hUne]
      exact ⟨e, heBoundary.1, hze⟩
    · unfold BoundaryFootprintVertices
      rw [ite_eq_left hVne]
      exact ⟨e, heBoundary.2, hze⟩

end ApollonianSuperharmonic

end
