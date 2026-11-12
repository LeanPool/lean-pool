/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.PeriodicTileAdjacentContactRegularity
public import LeanPool.ApollonianSuperharmonic.PeriodicTileIntersectionClassification
public import LeanPool.ApollonianSuperharmonic.SimpleGridPathBetween
public import LeanPool.ApollonianSuperharmonic.LocalLatticeInterfaceSectors
public import LeanPool.ApollonianSuperharmonic.P3192T1SimplePathOrientation
public import LeanPool.ApollonianSuperharmonic.P3192T1FourOwnerTriangleExclusion
public import LeanPool.ApollonianSuperharmonic.P3192T1PeriodicIndicesInfinite

-- [TABLET NODE: PeriodicTileIntersectionPaths]

/-!
# PeriodicTileIntersectionPaths

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace IntersectionPathGeometry

private theorem hdisjoint :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (u : ι), ∀ (v : ι), (u ≠ v) → (Disjoint
            (P.tile u).cells (P.tile v).cells) ) := by
  classical
  intro ι P u v huv
  apply Finset.disjoint_left.mpr
  intro x hxu hxv
  obtain ⟨w, hw, hunique⟩ := PeriodicTileIndexedMultiplicityOne P x
  exact huv ((hunique u hxu).trans (hunique v hxv).symm)

private theorem face_adjacent :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (f : P.plane.Face), ∀ (u : ι), ∀ (v : ι),
            (u ≠ v) → ((∃ i, P.plane.faceVertex f i = u) → ((∃ i, P.plane.faceVertex f i = v) →
            (P.plane.adjacent u v))) ) := by
  classical
  intro ι P f u v huv hu hv
  obtain ⟨i, hi⟩ := hu
  obtain ⟨j, hj⟩ := hv
  have hij : i ≠ j := by
    intro h
    exact huv (hi.symm.trans (h ▸ hj))
  simpa [hi, hj] using P.plane.face_edges f i j hij

private theorem face_point :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (f : P.plane.Face), ∀ (u : ι), (∃ i,
            P.plane.faceVertex f i = u) → (P.rho f ∈ FootprintVertices (P.tile u)) ) := by
  classical
  intro ι P f u hu
  obtain ⟨i, hi⟩ := hu
  simpa [hi] using P.rho_common f i

private theorem third_vertex :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (a : ι), ∀ (b : ι), ∀ (f : P.plane.Face),
            (∃ i, P.plane.faceVertex f i = a) → ((∃ i, P.plane.faceVertex f i = b) → (∃ c : ι, c
            ≠ a ∧ c ≠ b ∧ ∃ i, P.plane.faceVertex f i = c)) ) := by
  classical
  intro ι P a b f hfa hfb
  obtain ⟨i, hi⟩ := hfa
  obtain ⟨j, hj⟩ := hfb
  have hindex : ∀ i j : Fin 3, ∃ k : Fin 3, k ≠ i ∧ k ≠ j := by decide
  obtain ⟨k, hki, hkj⟩ := hindex i j
  refine ⟨P.plane.faceVertex f k, ?_, ?_, k, rfl⟩
  · intro h
    exact hki (P.plane.face_vertices_distinct f (h.trans hi.symm))
  · intro h
    exact hkj (P.plane.face_vertices_distinct f (h.trans hj.symm))

private theorem hgc :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (g : P.plane.Face), ∀ (c : ι), ∀ (d : ι),
            (∃ (i : Fin (3 : ℕ)), P.plane.faceVertex g i = d) → ((c = d) → (∃ i,
            P.plane.faceVertex g i = c)) ) := by
  classical
  intro ι P g c d hgd hcd
  obtain ⟨i, hi⟩ := hgd
  exact ⟨i, hi.trans hcd.symm⟩

private theorem triangle_boundary :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (a : ι), ∀ (b : ι), (a ≠ b) → (∀ (c : ι),
            (c ≠ a) → ((c ≠ b) → (
        let J := P.plane.edgeArc a b ∪ P.plane.edgeArc b c ∪ P.plane.edgeArc c a
        ∀ (h : P.plane.Face), (∃ i, P.plane.faceVertex h i = a) → ((∃ i, P.plane.faceVertex h i =
            b) → ((∃ i, P.plane.faceVertex h i = c) → (frontier (P.plane.faceRegion h) = J))))))
            ) := by
  classical
  intro ι P a b hab c hca hcb J h hha hhb hhc
  obtain ⟨i, hi⟩ := hha
  obtain ⟨j, hj⟩ := hhb
  obtain ⟨k, hk⟩ := hhc
  have hij : i ≠ j := by
    intro heq
    exact hab (hi.symm.trans (heq ▸ hj))
  have hik : i ≠ k := by
    intro heq
    exact hca (hk.symm.trans (heq.symm ▸ hi))
  have hjk : j ≠ k := by
    intro heq
    exact hcb (hk.symm.trans (heq.symm ▸ hj))
  have hfin0 : (⟨0, by decide⟩ : Fin 3) = 0 := rfl
  have hfin1 : (⟨1, by decide⟩ : Fin 3) = 1 := rfl
  have hfin2 : (⟨2, by decide⟩ : Fin 3) = 2 := rfl
  rw [P.plane.face_boundary h]
  fin_cases i <;> fin_cases j <;> fin_cases k
  all_goals try exact (hij rfl).elim
  all_goals try exact (hik rfl).elim
  all_goals try exact (hjk rfl).elim
  all_goals dsimp only at hi hj hk
  all_goals simp only [hfin0, hfin1, hfin2] at hi hj hk
  all_goals rw [hi, hj, hk]
  all_goals try simp only [P.plane.arc_symmetric b a, P.plane.arc_symmetric a c,
    P.plane.arc_symmetric c b]
  all_goals dsimp only [J]
  all_goals ac_rfl

private theorem hJtrace :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (a : ι), ∀ (b : ι), ∀ (f : P.plane.Face),
            ∀ (c : ι),
        let J := P.plane.edgeArc a b ∪ P.plane.edgeArc b c ∪ P.plane.edgeArc c a
        (frontier (P.plane.faceRegion f) = J) → ((∀ (f : P.plane.Face), Disjoint
            (P3767T1FixedTrace P.plane) (P.plane.faceRegion f) ∧ frontier (P.plane.faceRegion
            f) ⊆ P3767T1FixedTrace P.plane) → (J ⊆ P3767T1FixedTrace P.plane)) ) := by
  classical
  intro ι P a b f c J hfrontf htrace
  rw [← hfrontf]
  exact (htrace f).2

private theorem hseparation :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (a : ι), ∀ (b : ι), (a ≠ b) → ((∀ (f :
            P.plane.Face), ∀ (u : ι), ∀ (v : ι), (u ≠ v) → ((∃ i, P.plane.faceVertex f i = u) →
            ((∃ i, P.plane.faceVertex f i = v) → (P.plane.adjacent u v)))) → ((P.plane.adjacent a
            b) → (∀ (f : P.plane.Face), ∀ (g : P.plane.Face), (f ≠ g) → (((∃ (i : Fin (3 : ℕ)),
            P.plane.faceVertex f i = a) ∧ ∃ (i : Fin (3 : ℕ)), P.plane.faceVertex f i = b) → (∀
            (c : ι), (c ≠ a) → ((c ≠ b) → ((∃ (i : Fin (3 : ℕ)), P.plane.faceVertex f i = c) → (
        let J := P.plane.edgeArc a b ∪ P.plane.edgeArc b c ∪ P.plane.edgeArc c a
        (frontier (P.plane.faceRegion f) = J) → ((∀ (f : P.plane.Face), ∀ (V : Set (ℝ × ℝ)),
            IsPreconnected V → Disjoint V (frontier (P.plane.faceRegion f)) → (V ∩
            P.plane.faceRegion f).Nonempty → V ⊆ P.plane.faceRegion f) → ((∀ (h : P.plane.Face),
            Disjoint (P.plane.faceRegion h) J) → (∃ U V : Set (Real × Real), IsOpen U ∧ IsOpen V
            ∧ IsConnected U ∧ IsConnected V ∧ Disjoint U V ∧ U ∪ V = Jᶜ))))))))))) ) := by
  classical
  intro ι P a b hab face_adjacent hadj f g hfg hf c hca hcb hfc J hfrontf hmaximal hregion_avoids
  obtain ⟨e, he, heJ⟩ := P3821T1ThreeArcCircle P.plane a b c
    hab hcb.symm hca hadj
    (face_adjacent f b c hcb.symm hf.2 hfc)
    (face_adjacent f c a hca hfc hf.1)
  change Set.range e = J at heJ
  have hopen : IsOpen Jᶜ := by
    rw [← heJ]
    exact (isCompact_range e.continuous).isClosed.isOpen_compl
  obtain ⟨x, hxf⟩ := (P.plane.region_connected f).nonempty
  obtain ⟨y, hyg⟩ := (P.plane.region_connected g).nonempty
  have hx : x ∈ Jᶜ := fun hxJ =>
    Set.disjoint_left.mp (hregion_avoids f) hxf hxJ
  have hy : y ∈ Jᶜ := fun hyJ =>
    Set.disjoint_left.mp (hregion_avoids g) hyg hyJ
  have hcomponent_f : connectedComponentIn Jᶜ x ⊆ P.plane.faceRegion f := by
    apply hmaximal f _ isPreconnected_connectedComponentIn
    · rw [hfrontf]
      apply Set.disjoint_left.mpr
      intro w hw hwJ
      exact connectedComponentIn_subset Jᶜ x hw hwJ
    · exact ⟨x, mem_connectedComponentIn hx, hxf⟩
  have hne : connectedComponentIn Jᶜ x ≠ connectedComponentIn Jᶜ y := by
    intro h
    have hyx : y ∈ connectedComponentIn Jᶜ x := by
      rw [h]
      exact mem_connectedComponentIn hy
    exact Set.disjoint_left.mp (P.plane.region_disjoint hfg)
      (hcomponent_f hyx) hyg
  have hbound (w : Real × Real) (hw : w ∈ Jᶜ) :
      connectedComponentIn Jᶜ x = connectedComponentIn Jᶜ y ∨
      connectedComponentIn Jᶜ y = connectedComponentIn Jᶜ w ∨
      connectedComponentIn Jᶜ x = connectedComponentIn Jᶜ w := by
    have hxe : x ∈ (Set.range e)ᶜ := by simpa only [heJ] using hx
    have hye : y ∈ (Set.range e)ᶜ := by simpa only [heJ] using hy
    have hwe : w ∈ (Set.range e)ᶜ := by simpa only [heJ] using hw
    simpa only [heJ] using P3821T1CircleComponentBound e he x y w hxe hye hwe
  refine ⟨connectedComponentIn Jᶜ x, connectedComponentIn Jᶜ y,
    hopen.connectedComponentIn, hopen.connectedComponentIn,
    isConnected_connectedComponentIn_iff.mpr hx,
    isConnected_connectedComponentIn_iff.mpr hy, ?_, ?_⟩
  · apply Set.disjoint_left.mpr
    intro w hwx hwy
    exact hne ((connectedComponentIn_eq hwx).trans
      (connectedComponentIn_eq hwy).symm)
  · apply Set.Subset.antisymm
    · exact Set.union_subset (connectedComponentIn_subset Jᶜ x)
        (connectedComponentIn_subset Jᶜ y)
    · intro w hw
      rcases hbound w hw with hxy | hyw | hxw
      · exact (hne hxy).elim
      · exact Or.inr (hyw.symm ▸ mem_connectedComponentIn hw)
      · exact Or.inl (hxw.symm ▸ mem_connectedComponentIn hw)

private theorem hside_avoids :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (a : ι), ∀ (b : ι), ∀ (c : ι),
        let J := P.plane.edgeArc a b ∪ P.plane.edgeArc b c ∪ P.plane.edgeArc c a
        ∀ (U : Set (ℝ × ℝ)), ∀ (V : Set (ℝ × ℝ)), (U ∪ V = Jᶜ) → (Disjoint (U ∪ V) J) ) := by
  classical
  intro ι P a b c J U V hcover
  rw [hcover]
  exact disjoint_compl_left

private theorem region_is_side :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (a : ι), ∀ (b : ι), ∀ (c : ι),
        let J := P.plane.edgeArc a b ∪ P.plane.edgeArc b c ∪ P.plane.edgeArc c a
        (∀ (f : P.plane.Face), ∀ (V : Set (ℝ × ℝ)), IsPreconnected V → Disjoint V (frontier
            (P.plane.faceRegion f)) → (V ∩ P.plane.faceRegion f).Nonempty → V ⊆
            P.plane.faceRegion f) → ((∀ (h : P.plane.Face), Disjoint (P.plane.faceRegion h) J) →
            (∀ (U : Set (ℝ × ℝ)), ∀ (V : Set (ℝ × ℝ)), (IsOpen U) → ((IsOpen V) → ((IsConnected
            U) → ((IsConnected V) → ((Disjoint U V) → ((U ∪ V = Jᶜ) → ((Disjoint (U ∪ V) J) → (∀
            (h : P.plane.Face), (frontier (P.plane.faceRegion h) = J) → (P.plane.faceRegion h = U
            ∨ P.plane.faceRegion h = V)))))))))) ) := by
  classical
  intro ι P a b c J hmaximal hregion_avoids U V hU hV hUc hVc hUV hcover hside_avoids h hfront
  have hsubset : P.plane.faceRegion h ⊆ U ∪ V := by
    rw [hcover]
    intro x hx hxJ
    exact Set.disjoint_left.mp (hregion_avoids h) hx hxJ
  by_cases hmeet : (P.plane.faceRegion h ∩ U).Nonempty
  · left
    apply Set.Subset.antisymm
    · exact (P.plane.region_connected h).isPreconnected.subset_left_of_subset_union
        hU hV hUV hsubset hmeet
    · apply hmaximal h U hUc.isPreconnected
      · rw [hfront]
        exact hside_avoids.mono_left Set.subset_union_left
      · simpa only [Set.inter_comm] using hmeet
  · right
    have hmeetV : (P.plane.faceRegion h ∩ V).Nonempty := by
      obtain ⟨x, hx⟩ := (P.plane.region_connected h).nonempty
      rcases hsubset hx with hxU | hxV
      · exact (hmeet ⟨x, hx, hxU⟩).elim
      · exact ⟨x, hx, hxV⟩
    apply Set.Subset.antisymm
    · apply (P.plane.region_connected h).isPreconnected.subset_left_of_subset_union
        hV hU hUV.symm
      · simpa only [Set.union_comm] using hsubset
      · exact hmeetV
    · apply hmaximal h V hVc.isPreconnected
      · rw [hfront]
        exact hside_avoids.mono_left Set.subset_union_right
      · simpa only [Set.inter_comm] using hmeetV

private theorem hregions_ne :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (f : P.plane.Face), ∀ (g : P.plane.Face),
            (f ≠ g) → (P.plane.faceRegion f ≠ P.plane.faceRegion g) ) := by
  classical
  intro ι P f g hfg heq
  obtain ⟨x, hx⟩ := (P.plane.region_connected f).nonempty
  exact Set.disjoint_left.mp (P.plane.region_disjoint hfg) hx (heq ▸ hx)

private theorem hregions :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (a : ι), ∀ (b : ι), ∀ (f : P.plane.Face),
            ∀ (g : P.plane.Face), ∀ (c : ι),
        let J := P.plane.edgeArc a b ∪ P.plane.edgeArc b c ∪ P.plane.edgeArc c a
        (frontier (P.plane.faceRegion f) = J) → ((frontier (P.plane.faceRegion g) = J) → (∀ (U :
            Set (ℝ × ℝ)), ∀ (V : Set (ℝ × ℝ)), (U ∪ V = Jᶜ) → ((∀ (h : P.plane.Face), (frontier
            (P.plane.faceRegion h) = J) → (P.plane.faceRegion h = U ∨ P.plane.faceRegion h = V))
            → ((P.plane.faceRegion f ≠ P.plane.faceRegion g) → (P.plane.faceRegion f ∪
            P.plane.faceRegion g = Jᶜ))))) ) := by
  classical
  intro ι P a b f g c J hfrontf hfrontg U V hcover region_is_side hregions_ne
  rcases region_is_side f hfrontf with hfU | hfV <;>
    rcases region_is_side g hfrontg with hgU | hgV
  · exact (hregions_ne (hfU.trans hgU.symm)).elim
  · rw [hfU, hgV]
    exact hcover
  · rw [hfV, hgU, Set.union_comm]
    exact hcover
  · exact (hregions_ne (hfV.trans hgV.symm)).elim

private theorem htrace_eq :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (a : ι), ∀ (b : ι), ∀ (f : P.plane.Face),
            ∀ (g : P.plane.Face), ∀ (c : ι),
        let J := P.plane.edgeArc a b ∪ P.plane.edgeArc b c ∪ P.plane.edgeArc c a
        ((P3767T1FixedTrace P.plane)ᶜ = {x : ℝ × ℝ | ∃ (f : P.plane.Face), x ∈
            P.plane.faceRegion f}) → ((∀ (h : P.plane.Face), Disjoint (P.plane.faceRegion h) J) →
            ((P.plane.faceRegion f ∪ P.plane.faceRegion g = Jᶜ) → (P3767T1FixedTrace P.plane =
            J))) ) := by
  classical
  intro ι P a b f g c J hexhaust hregion_avoids hregions
  have hcompeq : (P3767T1FixedTrace P.plane)ᶜ = Jᶜ := by
    rw [hexhaust]
    apply Set.Subset.antisymm
    · rintro x ⟨h, hx⟩ hxJ
      exact Set.disjoint_left.mp (hregion_avoids h) hx hxJ
    · intro x hx
      rw [← hregions] at hx
      rcases hx with hxf | hxg
      · exact ⟨f, hxf⟩
      · exact ⟨g, hxg⟩
  simpa only [compl_compl] using
    congrArg (fun s : Set (Real × Real) => sᶜ) hcompeq

private theorem hw :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (a : ι), ∀ (b : ι), ∀ (c : ι),
        let J := P.plane.edgeArc a b ∪ P.plane.edgeArc b c ∪ P.plane.edgeArc c a
        (P3767T1FixedTrace P.plane = J) → (∀ (w : ι), P.plane.position w ∈ J) ) := by
  classical
  intro ι P a b c J htrace_eq w
  rw [← htrace_eq]
  exact Or.inl ⟨w, rfl⟩

private theorem hcd :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (a : ι), ∀ (b : ι), (a ≠ b) → ((∀ (f :
            P.plane.Face), (∃ i, P.plane.faceVertex f i = a) → ((∃ i, P.plane.faceVertex f i = b)
            → (∃ c : ι, c ≠ a ∧ c ≠ b ∧ ∃ i, P.plane.faceVertex f i = c))) → ((((FootprintEdges
            (P.tile a) ∩ FootprintEdges (P.tile b)).Nonempty ↔ P.plane.adjacent a b) ∧
            ((FootprintEdges (P.tile a) ∩ FootprintEdges (P.tile b)).Nonempty → SimpleGridPath
            (CommonFootprintEdgeVertices (P.tile a) (P.tile b)) (FootprintEdges (P.tile a) ∩
            FootprintEdges (P.tile b)) ∧ FootprintVertices (P.tile a) ∩ FootprintVertices (P.tile
            b) = CommonFootprintEdgeVertices (P.tile a) (P.tile b)) ∧ (¬(FootprintEdges (P.tile
            a) ∩ FootprintEdges (P.tile b)).Nonempty → FootprintVertices (P.tile a) ∩
            FootprintVertices (P.tile b) = ∅ ∨ (FootprintVertices (P.tile a) ∩ FootprintVertices
            (P.tile b)).Subsingleton)) → (((FootprintEdges (P.tile a) ∩ FootprintEdges (P.tile
            b)).Nonempty ↔ P.plane.adjacent a b) → ((P.plane.adjacent a b) → (∀ (f :
            P.plane.Face), ∀ (g : P.plane.Face), ((∃ (i : Fin (3 : ℕ)), P.plane.faceVertex f i =
            a) ∧ ∃ (i : Fin (3 : ℕ)), P.plane.faceVertex f i = b) → (((∃ (i : Fin (3 : ℕ)),
            P.plane.faceVertex g i = a) ∧ ∃ (i : Fin (3 : ℕ)), P.plane.faceVertex g i = b) → ((∀
            (h : P.plane.Face), ((∃ (i : Fin (3 : ℕ)), P.plane.faceVertex h i = a) ∧ ∃ (i : Fin
            (3 : ℕ)), P.plane.faceVertex h i = b) → h = f ∨ h = g) → (∀ (c : ι), (c ≠ a) → ((c ≠
            b) → ((∃ (i : Fin (3 : ℕ)), P.plane.faceVertex f i = c) → (∀ (d : ι), (d ≠ a) → ((d ≠
            b) → ((c = d → ∀ w : ι, w = a ∨ w = b ∨ w = c) → (c ≠ d)))))))))))))) ) := by
  classical
  intro ι P a b hab third_vertex hclassification hcriterion hadj f g hf hg hfaces c hca hcb hfc d
      hda hdb hcellular h
  let : Infinite ι := P3192T1PeriodicIndicesInfinite P
  obtain ⟨w, hw⟩ := ({a, b, c} : Finset ι).exists_notMem
  rcases hcellular h w with rfl | rfl | rfl <;> exact hw (by simp)

private theorem hxAt393 :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), (PeriodicTileAdjacentContactRegularity P) →
            (∀ (a : ι), ∀ (b : ι), (∀ (f : P.plane.Face), ∀ (u : ι), (∃ i, P.plane.faceVertex f i
            = u) → (P.rho f ∈ FootprintVertices (P.tile u))) → ((P.plane.adjacent a b) → (∀ (h :
            P.plane.Face), (∃ i, P.plane.faceVertex h i = a) → ((∃ i, P.plane.faceVertex h i = b)
            → (P.rho h ∈ CommonFootprintEdgeVertices (P.tile a) (P.tile b)))))) ) := by
  classical
  intro ι P contact_regular a b face_point hadj h hha hhb
  rw [← contact_regular.adjacent_raw_eq_edge_vertices a b hadj]
  exact ⟨face_point h a hha, face_point h b hhb⟩

private theorem hpoints :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), (PeriodicTileAdjacentContactRegularity P) →
            (∀ (a : ι), ∀ (b : ι), (a ≠ b) → ((∀ (u : ι), ∀ (v : ι), (u ≠ v) → (Disjoint (P.tile
            u).cells (P.tile v).cells)) → ((∀ (f : P.plane.Face), ∀ (u : ι), (∃ i,
            P.plane.faceVertex f i = u) → (P.rho f ∈ FootprintVertices (P.tile u))) → (∀ (f :
            P.plane.Face), ∀ (g : P.plane.Face), ((∃ (i : Fin (3 : ℕ)), P.plane.faceVertex f i =
            a) ∧ ∃ (i : Fin (3 : ℕ)), P.plane.faceVertex f i = b) → (∀ (c : ι), (c ≠ a) → ((c ≠
            b) → ((∃ (i : Fin (3 : ℕ)), P.plane.faceVertex f i = c) → (∀ (d : ι), (d ≠ a) → ((d ≠
            b) → ((∃ (i : Fin (3 : ℕ)), P.plane.faceVertex g i = d) → ((c ≠ d) →
            ((P.plane.adjacent a c) → ((P.plane.adjacent b c) → ((P.rho f ∈
            CommonFootprintEdgeVertices (P.tile a) (P.tile b)) → (P.rho f ≠ P.rho
            g))))))))))))))) ) := by
  classical
  intro ι P contact_regular a b hab hdisjoint face_point f g hf c hca hcb hfc d hda hdb hgd hcd
      hfac hfbc hrhof heq
  let idx : Fin 4 → ι := ![a, b, c, d]
  have hinj : Function.Injective idx := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [idx, ne_comm]
  have hnonempty (i : Fin 4) : (P.tile (idx i)).cells.Nonempty :=
    (LatticeTileGridStructure _ (P.tiles_are_disks (idx i))).1.1
  have hdis (i j : Fin 4) (hij : i ≠ j) :
      Disjoint (P.tile (idx i)).cells (P.tile (idx j)).cells :=
    hdisjoint _ _ (fun h => hij (hinj h))
  have hraw (i : Fin 4) : P.rho f ∈ FootprintVertices (P.tile (idx i)) := by
    fin_cases i
    · exact face_point f a hf.1
    · exact face_point f b hf.2
    · exact face_point f c hfc
    · change P.rho f ∈ FootprintVertices (P.tile d)
      rw [heq]
      exact face_point g d hgd
  apply P3192T1FourOwnerTriangleExclusion (fun i => P.tile (idx i))
    (P.rho f) hnonempty hdis hraw
  refine ⟨hrhof, ?_, ?_⟩
  · change P.rho f ∈ CommonFootprintEdgeVertices (P.tile b) (P.tile c)
    rw [← contact_regular.adjacent_raw_eq_edge_vertices b c hfbc]
    exact ⟨face_point f b hf.2, face_point f c hfc⟩
  · change P.rho f ∈ CommonFootprintEdgeVertices (P.tile c) (P.tile a)
    rw [← contact_regular.adjacent_raw_eq_edge_vertices c a
      ((P.plane.adjacent_symmetric a c).mp hfac)]
    exact ⟨face_point f c hfc, face_point f a hf.1⟩

private theorem third_owner_degree :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (a : ι), ∀ (b : ι), (a ≠ b) → ((∀ (u : ι),
            ∀ (v : ι), (u ≠ v) → (Disjoint (P.tile u).cells (P.tile v).cells)) → (∀ (z : ι), (z ≠
            a) → ((z ≠ b) → (∀ (x : GaussianInt), (x ∈ FootprintVertices (P.tile z)) → (∀ e f :
            Finset GaussianInt, x ∈ e → x ∈ f → e ∈ FootprintEdges (P.tile a) ∩ FootprintEdges
            (P.tile b) → f ∈ FootprintEdges (P.tile a) ∩ FootprintEdges (P.tile b) → e = f))))) )
            := by
  classical
  intro ι P a b hab hdisjoint z hza hzb x hx
  have hzne : (P.tile z).cells.Nonempty :=
    (LatticeTileGridStructure _ (P.tiles_are_disks z)).1.1
  have hincident :
      ∃ j : Fin 4, LatticeVertexIncidentCell x j ∈ (P.tile z).cells := by
    simp only [FootprintVertices, hzne, ite_true, Set.mem_ofPred_eq] at hx
    rcases hx with ⟨c, hc, h | h | h | h⟩
    · refine ⟨0, ?_⟩
      simpa [LatticeVertexIncidentCell] using h ▸ hc
    · refine ⟨1, ?_⟩
      subst x
      convert hc using 1; simp [LatticeVertexIncidentCell]
    · refine ⟨3, ?_⟩
      subst x
      convert hc using 1; simp [LatticeVertexIncidentCell]
    · refine ⟨2, ?_⟩
      change x - 1 - ⟨0, 1⟩ ∈ (P.tile z).cells
      rw [h]
      convert hc using 1
      ext <;> simp
  intro e f hxe hxf he hf
  by_contra hne
  have hcover := (LocalLatticeInterfaceSectors.2 (P.tile a) (P.tile b) x
    (P.tiles_are_disks a) (P.tiles_are_disks b) (hdisjoint a b hab)
    ⟨e, f, hne, hxe, hxf, he, hf⟩).1
  obtain ⟨j, hj⟩ := hincident
  rcases hcover j with h | h
  · exact Finset.disjoint_left.mp (hdisjoint a z hza.symm) h hj
  · exact Finset.disjoint_left.mp (hdisjoint b z hzb.symm) h hj

end IntersectionPathGeometry

theorem PeriodicTileIntersectionPaths {ι : Type} (P : PeriodicTileComplex ι)
    (contact_regular : PeriodicTileAdjacentContactRegularity P)
    (a b : ι) (hab : a ≠ b) :
    ((P.plane.adjacent a b ∧
        ∃ f g : P.plane.Face, f ≠ g ∧
          ((∃ i, P.plane.faceVertex f i = a) ∧
            (∃ i, P.plane.faceVertex f i = b)) ∧
          ((∃ i, P.plane.faceVertex g i = a) ∧
            (∃ i, P.plane.faceVertex g i = b)) ∧
          (∀ h : P.plane.Face,
            ((∃ i, P.plane.faceVertex h i = a) ∧
              (∃ i, P.plane.faceVertex h i = b)) → h = f ∨ h = g) ∧
          SimpleGridPathBetween
            (CommonFootprintEdgeVertices (P.tile a) (P.tile b))
            (FootprintEdges (P.tile a) ∩ FootprintEdges (P.tile b))
            (P.rho f) (P.rho g)) ↔
      (FootprintEdges (P.tile a) ∩ FootprintEdges (P.tile b)).Nonempty) ∧
    ((FootprintVertices (P.tile a) ∩
        FootprintVertices (P.tile b)).Nonempty →
      (P.plane.adjacent a b ∧
        ∃ f g : P.plane.Face, f ≠ g ∧
          ((∃ i, P.plane.faceVertex f i = a) ∧
            (∃ i, P.plane.faceVertex f i = b)) ∧
          ((∃ i, P.plane.faceVertex g i = a) ∧
            (∃ i, P.plane.faceVertex g i = b)) ∧
          (∀ h : P.plane.Face,
            ((∃ i, P.plane.faceVertex h i = a) ∧
              (∃ i, P.plane.faceVertex h i = b)) → h = f ∨ h = g) ∧
          SimpleGridPathBetween
            (CommonFootprintEdgeVertices (P.tile a) (P.tile b))
            (FootprintEdges (P.tile a) ∩ FootprintEdges (P.tile b))
            (P.rho f) (P.rho g)) ∨
      (¬ P.plane.adjacent a b ∧
        FootprintEdges (P.tile a) ∩ FootprintEdges (P.tile b) = ∅)) := by
-- BODY
  classical
  have hdisjoint (u v : ι) (huv : u ≠ v) := IntersectionPathGeometry.hdisjoint ι P u v huv
  have face_adjacent (f : P.plane.Face) (u v : ι) (huv : u ≠ v)
      (hu : ∃ i, P.plane.faceVertex f i = u)
      (hv : ∃ i, P.plane.faceVertex f i = v) := IntersectionPathGeometry.face_adjacent ι P f u v
          huv hu hv
  have face_point (f : P.plane.Face) (u : ι)
      (hu : ∃ i, P.plane.faceVertex f i = u) := IntersectionPathGeometry.face_point ι P f u hu
  have third_vertex (f : P.plane.Face)
      (hfa : ∃ i, P.plane.faceVertex f i = a)
      (hfb : ∃ i, P.plane.faceVertex f i = b) := IntersectionPathGeometry.third_vertex ι P a b f
          hfa hfb
  have hclassification := (PeriodicTileIntersectionClassification P).1 a b hab
  have hcriterion := hclassification.1
  have adjacent_package (hadj : P.plane.adjacent a b) :
      ∃ f g : P.plane.Face, f ≠ g ∧
        ((∃ i, P.plane.faceVertex f i = a) ∧
          (∃ i, P.plane.faceVertex f i = b)) ∧
        ((∃ i, P.plane.faceVertex g i = a) ∧
          (∃ i, P.plane.faceVertex g i = b)) ∧
        (∀ h : P.plane.Face,
          ((∃ i, P.plane.faceVertex h i = a) ∧
            (∃ i, P.plane.faceVertex h i = b)) → h = f ∨ h = g) ∧
        SimpleGridPathBetween
          (CommonFootprintEdgeVertices (P.tile a) (P.tile b))
          (FootprintEdges (P.tile a) ∩ FootprintEdges (P.tile b))
          (P.rho f) (P.rho g) := by
    obtain ⟨f, g, hfg, hf, hg, hfaces⟩ := P.plane.every_edge_two_faces a b hadj
    obtain ⟨c, hca, hcb, hfc⟩ := third_vertex f hf.1 hf.2
    obtain ⟨d, hda, hdb, hgd⟩ := third_vertex g hg.1 hg.2
    have hcellular : c = d → ∀ w : ι, w = a ∨ w = b ∨ w = c := by
      intro hcd
      let : Nontrivial ι := ⟨⟨a, b, hab⟩⟩
      have hgc := IntersectionPathGeometry.hgc ι P g c d hgd hcd
      let J := P.plane.edgeArc a b ∪ P.plane.edgeArc b c ∪ P.plane.edgeArc c a
      have triangle_boundary (h : P.plane.Face)
          (hha : ∃ i, P.plane.faceVertex h i = a)
          (hhb : ∃ i, P.plane.faceVertex h i = b)
          (hhc : ∃ i, P.plane.faceVertex h i = c) := IntersectionPathGeometry.triangle_boundary ι
              P a b hab c hca hcb h hha hhb hhc
      have hfrontf := triangle_boundary f hf.1 hf.2 hfc
      have hfrontg := triangle_boundary g hg.1 hg.2 hgc
      obtain ⟨htrace, hmaximal, hexhaust⟩ := P3767T1FixedFaceComponents P.plane
      have hJtrace := IntersectionPathGeometry.hJtrace ι P a b f c hfrontf htrace
      have hregion_avoids (h : P.plane.Face) :
          Disjoint (P.plane.faceRegion h) J :=
        (htrace h).1.symm.mono_right hJtrace
      have hseparation := IntersectionPathGeometry.hseparation ι P a b hab face_adjacent hadj f g
          hfg hf c hca hcb hfc hfrontf hmaximal hregion_avoids
      obtain ⟨U, V, hU, hV, hUc, hVc, hUV, hcover⟩ := hseparation
      have hside_avoids := IntersectionPathGeometry.hside_avoids ι P a b c U V hcover
      have region_is_side (h : P.plane.Face)
          (hfront : frontier (P.plane.faceRegion h) = J) :=
              IntersectionPathGeometry.region_is_side ι P a b c hmaximal hregion_avoids U V hU hV
              hUc hVc hUV hcover hside_avoids h hfront
      have hregions_ne := IntersectionPathGeometry.hregions_ne ι P f g hfg
      have hregions := IntersectionPathGeometry.hregions ι P a b f g c hfrontf hfrontg U V hcover
          region_is_side hregions_ne
      have htrace_eq := IntersectionPathGeometry.htrace_eq ι P a b f g c hexhaust hregion_avoids
          hregions
      intro w
      have hw := IntersectionPathGeometry.hw ι P a b c htrace_eq w
      rcases hw with (hw | hw) | hw
      · rcases (P3767T1VertexEdgeIncidence P.plane w).2 a b hadj hw with ha | hb
        · exact Or.inl ha
        · exact Or.inr (Or.inl hb)
      · rcases (P3767T1VertexEdgeIncidence P.plane w).2 b c
          (face_adjacent f b c hcb.symm hf.2 hfc) hw with hb | hc
        · exact Or.inr (Or.inl hb)
        · exact Or.inr (Or.inr hc)
      · rcases (P3767T1VertexEdgeIncidence P.plane w).2 c a
          (face_adjacent f c a hca hfc hf.1) hw with hc | ha
        · exact Or.inr (Or.inr hc)
        · exact Or.inl ha
    have hcd := IntersectionPathGeometry.hcd ι P a b hab third_vertex hclassification hcriterion
        hadj f g hf hg hfaces c hca hcb hfc d hda hdb hcellular
    have hfac := face_adjacent f a c hca.symm hf.1 hfc
    have hfbc := face_adjacent f b c hcb.symm hf.2 hfc
    have hx (h : P.plane.Face)
        (hha : ∃ i, P.plane.faceVertex h i = a)
        (hhb : ∃ i, P.plane.faceVertex h i = b) := IntersectionPathGeometry.hxAt393 ι P
            contact_regular a b face_point hadj h hha hhb
    have hrhof := hx f hf.1 hf.2
    have hrhog := hx g hg.1 hg.2
    have hpoints := IntersectionPathGeometry.hpoints ι P contact_regular a b hab hdisjoint
        face_point f g hf c hca hcb hfc d hda hdb hgd hcd hfac hfbc hrhof
    have third_owner_degree (z : ι) (hza : z ≠ a) (hzb : z ≠ b)
        (x : GaussianInt) (hx : x ∈ FootprintVertices (P.tile z)) :=
            IntersectionPathGeometry.third_owner_degree ι P a b hab hdisjoint z hza hzb x hx
    have hdegreef := third_owner_degree c hca hcb (P.rho f) (face_point f c hfc)
    have hdegreeg := third_owner_degree d hda hdb (P.rho g) (face_point g d hgd)
    refine ⟨f, g, hfg, hf, hg, hfaces, ?_⟩
    exact P3192T1SimplePathOrientation _ _ (P.rho f) (P.rho g)
      (hclassification.2.1 (hcriterion.mpr hadj)).1
      hrhof hrhog hpoints hdegreef hdegreeg
  constructor
  · constructor
    · intro hp
      exact hcriterion.mpr hp.1
    · intro he
      have hadj := hcriterion.mp he
      exact ⟨hadj, adjacent_package hadj⟩
  · intro _
    by_cases he : (FootprintEdges (P.tile a) ∩ FootprintEdges (P.tile b)).Nonempty
    · have hadj := hcriterion.mp he
      exact Or.inl ⟨hadj, adjacent_package hadj⟩
    · exact Or.inr ⟨fun hadj => he (hcriterion.mpr hadj),
        Set.not_nonempty_iff_eq_empty.mp he⟩

end ApollonianSuperharmonic

end
