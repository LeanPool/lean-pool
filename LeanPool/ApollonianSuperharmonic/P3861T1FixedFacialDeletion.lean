/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P3776T1FixedGeometry
public import LeanPool.ApollonianSuperharmonic.P3821T1ThreeArcCircle
public import LeanPool.ApollonianSuperharmonic.P3821T1CircleComponentBound

-- [TABLET NODE: P3861T1FixedFacialDeletion]

/-!
# P3861T1FixedFacialDeletion

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace FacialDeletionProof

private theorem hCcompact :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileCore ι),
        let U (f : P.plane.Face) := P.plane.faceRegion f
        let C (f : P.plane.Face) := frontier (U f)
        (∀ (f : P.plane.Face), C f = P.plane.edgeArc (P.plane.faceVertex f 0) (P.plane.faceVertex
            f 1) ∪ P.plane.edgeArc (P.plane.faceVertex f 1) (P.plane.faceVertex f 2) ∪
            P.plane.edgeArc (P.plane.faceVertex f 2) (P.plane.faceVertex f 0)) → (∀ (f :
            P.plane.Face), IsCompact (C f)) ) := by
  classical
  intro ι P U C hfront f
  rw [hfront f]
  have hacomp (a b : ι) (hab : P.plane.adjacent a b) :
      IsCompact (P.plane.edgeArc a b) := by
    obtain ⟨e, _, _⟩ := P.plane.arc_homeomorph a b hab
    have himage : Set.range (fun x : Set.Icc (0 : Real) 1 =>
        ((e x : P.plane.edgeArc a b) : Real × Real)) = P.plane.edgeArc a b := by
      ext x
      constructor
      · rintro ⟨t, rfl⟩
        exact (e t).property
      · intro hx
        exact ⟨e.symm ⟨x, hx⟩, by simp⟩
    rw [← himage]
    exact isCompact_range (continuous_subtype_val.comp e.continuous)
  exact ((hacomp _ _ (P.plane.face_edges f 0 1 (by decide))).union
    (hacomp _ _ (P.plane.face_edges f 1 2 (by decide)))).union
    (hacomp _ _ (P.plane.face_edges f 2 0 (by decide)))

private theorem hWnonempty :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileCore ι),
        let U (f : P.plane.Face) := P.plane.faceRegion f
        let W (f : P.plane.Face) := (closure (U f))ᶜ
        (Nontrivial ι ∧ (∀ (f : P.plane.Face), IsCompact (closure (P.plane.faceRegion f))) ∧ (∀
            (K : Set (ℝ × ℝ)), IsCompact K → {f : P.plane.Face | (K ∩ closure (P.plane.faceRegion
            f)).Nonempty}.Finite) ∧ (∀ (x : ℝ × ℝ), ∃ (f : P.plane.Face), x ∈ closure
            (P.plane.faceRegion f)) ∧ (∀ (a : ι), IsOpen (P3776T1OpenStar P a) ∧ IsCompact
            (closure (P3776T1OpenStar P a))) ∧ (∀ (x : ℝ × ℝ), ∃ (a : ι), x ∈ P3776T1OpenStar
            P a) ∧ (∀ (u : ↥P.lattice), ∀ (a : ι), P3776T1OpenStar P (P.shift u a) = (fun (x :
            ℝ × ℝ) => x + GaussianRealPoint (↑u : GaussianInt)) '' P3776T1OpenStar P a) ∧ ∀ (u
            : ↥P.lattice), ∀ (v : ↥P.lattice), ∀ (a : ι), P.shift u a = P.shift v a → u = v) → (∀
            (f : P.plane.Face), (W f).Nonempty) ) := by
  classical
  intro ι P U W hgeom f
  have hb := (hgeom.2.1 f).isBounded
  by_contra hn
  have hclosure : closure (U f) = Set.univ := by
    apply Set.eq_univ_iff_forall.mpr
    intro x
    by_contra hx
    apply hn
    exact ⟨x, by simpa [W] using hx⟩
  have hbound : Bornology.IsBounded (Set.univ : Set (Real × Real)) := by
    rw [← hclosure]
    exact hb
  exact (NormedSpace.unbounded_univ ℝ (Real × Real)) hbound

private theorem hWpartition :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileCore ι),
        let U (f : P.plane.Face) := P.plane.faceRegion f
        let C (f : P.plane.Face) := frontier (U f)
        let W (f : P.plane.Face) := (closure (U f))ᶜ
        ∀ (f : P.plane.Face), (C f)ᶜ = U f ∪ W f ) := by
  classical
  intro ι P U C W f
  ext x
  constructor
  · intro hx
    by_cases hu : x ∈ U f
    · exact Or.inl hu
    · right
      change x ∉ closure (U f)
      intro hcl
      have hfrontier : x ∈ frontier (U f) := by
        rw [frontier_eq_closure_inter_closure]
        refine ⟨hcl, ?_⟩
        exact subset_closure hu
      exact hx hfrontier
  · rintro (hu | hw)
    · apply Set.disjoint_left.mp ((disjoint_frontier_iff_isOpen.mpr
        (P.plane.region_open f)).symm) hu
    · intro hxC
      exact hw (frontier_subset_closure hxC)

private theorem hUsub :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileCore ι),
        let U (f : P.plane.Face) := P.plane.faceRegion f
        let C (f : P.plane.Face) := frontier (U f)
        ∀ (f : P.plane.Face), U f ⊆ (C f)ᶜ ) := by
  classical
  intro ι P U C f x hx
  exact Set.disjoint_left.mp ((disjoint_frontier_iff_isOpen.mpr
    (P.plane.region_open f)).symm) hx

private theorem hcomponentU :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileCore ι),
        let U (f : P.plane.Face) := P.plane.faceRegion f
        let C (f : P.plane.Face) := frontier (U f)
        (∀ (f : P.plane.Face), ∀ (V : Set (ℝ × ℝ)), IsPreconnected V → Disjoint V (frontier
            (P.plane.faceRegion f)) → (V ∩ P.plane.faceRegion f).Nonempty → V ⊆
            P.plane.faceRegion f) → ((∀ (f : P.plane.Face), U f ⊆ (C f)ᶜ) → (∀ (f :
            P.plane.Face), ∀ x ∈ U f, connectedComponentIn (C f)ᶜ x = U f)) ) := by
  classical
  intro ι P U C hbarrier hUsub f x hx
  have hcompSub : connectedComponentIn (C f)ᶜ x ⊆ U f := by
    apply hbarrier f _ isPreconnected_connectedComponentIn
    · apply Set.disjoint_left.mpr
      intro y hy hyC
      exact connectedComponentIn_subset (C f)ᶜ x hy hyC
    · exact ⟨x, mem_connectedComponentIn (hUsub f hx), hx⟩
  have hUcomp : U f ⊆ connectedComponentIn (C f)ᶜ x := by
    exact (P.plane.region_connected f).isPreconnected.subset_connectedComponentIn hx
      (hUsub f)
  exact Set.Subset.antisymm hcompSub hUcomp

private theorem hWconnected :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileCore ι),
        let U (f : P.plane.Face) := P.plane.faceRegion f
        let C (f : P.plane.Face) := frontier (U f)
        let W (f : P.plane.Face) := (closure (U f))ᶜ
        (∀ (f : P.plane.Face), C f = P.plane.edgeArc (P.plane.faceVertex f 0) (P.plane.faceVertex
            f 1) ∪ P.plane.edgeArc (P.plane.faceVertex f 1) (P.plane.faceVertex f 2) ∪
            P.plane.edgeArc (P.plane.faceVertex f 2) (P.plane.faceVertex f 0)) → ((∀ (f :
            P.plane.Face), (W f).Nonempty) → ((∀ (f : P.plane.Face), (C f)ᶜ = U f ∪ W f) → ((∀ (f
            : P.plane.Face), U f ⊆ (C f)ᶜ) → ((∀ (f : P.plane.Face), ∀ (x : Real × Real), (x ∈ U
            f) → (connectedComponentIn (C f)ᶜ x = U f)) → (∀ (f : P.plane.Face), IsConnected (W
            f)))))) ) := by
  classical
  intro ι P U C W hfront hWnonempty hWpartition hUsub hcomponentU f
  obtain ⟨e, he, hE⟩ := P3821T1ThreeArcCircle P.plane
    (P.plane.faceVertex f 0) (P.plane.faceVertex f 1) (P.plane.faceVertex f 2)
    (fun h => by have hh := P.plane.face_vertices_distinct f h; norm_num at hh)
    (fun h => by
      have hh := P.plane.face_vertices_distinct f h
      exact (by decide : (1 : Fin 3) ≠ 2) hh)
    (fun h => by
      have hh := P.plane.face_vertices_distinct f h
      exact (by decide : (2 : Fin 3) ≠ 0) hh)
    (P.plane.face_edges f 0 1 (by decide))
    (P.plane.face_edges f 1 2 (by decide))
    (P.plane.face_edges f 2 0 (by decide))
  have hErange : Set.range e = C f := by rw [hfront f]; exact hE
  obtain ⟨r, hr⟩ := (P.plane.region_connected f).nonempty
  obtain ⟨x, hx⟩ := hWnonempty f
  have hrC : r ∈ (C f)ᶜ := hUsub f hr
  have hxC : x ∈ (C f)ᶜ := by
    rw [hWpartition f]
    exact Or.inr hx
  have hcompR (y : Real × Real) (hy : y ∈ W f) :
      connectedComponentIn (C f)ᶜ r ≠ connectedComponentIn (C f)ᶜ y := by
    intro heq
    have hyR : y ∈ U f := by
      have hy' : y ∈ connectedComponentIn (C f)ᶜ r := by
        rw [heq]
        exact mem_connectedComponentIn (by
          rw [hWpartition f]
          exact Or.inr hy)
      rw [← hcomponentU f r hr]
      exact hy'
    exact hy (subset_closure hyR)
  have hsame (y z : Real × Real) (hy : y ∈ W f) (hz : z ∈ W f) :
      connectedComponentIn (C f)ᶜ y = connectedComponentIn (C f)ᶜ z := by
    have hyC : y ∈ (C f)ᶜ := by rw [hWpartition f]; exact Or.inr hy
    have hzC : z ∈ (C f)ᶜ := by rw [hWpartition f]; exact Or.inr hz
    have hyE : y ∈ (Set.range e)ᶜ := by rw [hErange]; exact hyC
    have hzE : z ∈ (Set.range e)ᶜ := by rw [hErange]; exact hzC
    have hrE : r ∈ (Set.range e)ᶜ := by rw [hErange]; exact hrC
    have hb₀ := P3821T1CircleComponentBound e he r y z hrE hyE hzE
    have hb : connectedComponentIn (C f)ᶜ r = connectedComponentIn (C f)ᶜ y ∨
        connectedComponentIn (C f)ᶜ y = connectedComponentIn (C f)ᶜ z ∨
        connectedComponentIn (C f)ᶜ r = connectedComponentIn (C f)ᶜ z := by
      simpa only [hErange] using hb₀
    rcases hb with h | h | h
    · exact (hcompR y hy h).elim
    · exact h
    · exact (hcompR z hz h).elim
  have hxComponent : connectedComponentIn (C f)ᶜ x = W f := by
    apply Set.Subset.antisymm
    · intro y hy
      have hyC : y ∈ (C f)ᶜ := connectedComponentIn_subset (C f)ᶜ x hy
      rw [hWpartition f] at hyC
      rcases hyC with hyU | hyW
      · have hxy : connectedComponentIn (C f)ᶜ x =
            connectedComponentIn (C f)ᶜ y := connectedComponentIn_eq hy
        have hxmem : x ∈ connectedComponentIn (C f)ᶜ x :=
          mem_connectedComponentIn hxC
        rw [hxy, hcomponentU f y hyU] at hxmem
        exact (hx (subset_closure hxmem)).elim
      · exact hyW
    · intro y hy
      have hxy := hsame x y hx hy
      rw [hxy]
      exact mem_connectedComponentIn (by
        rw [hWpartition f]
        exact Or.inr hy)
  rw [← hxComponent]
  exact isConnected_connectedComponentIn_iff.mpr hxC

private theorem hWunbounded :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileCore ι),
        let U (f : P.plane.Face) := P.plane.faceRegion f
        let W (f : P.plane.Face) := (closure (U f))ᶜ
        (Nontrivial ι ∧ (∀ (f : P.plane.Face), IsCompact (closure (P.plane.faceRegion f))) ∧ (∀
            (K : Set (ℝ × ℝ)), IsCompact K → {f : P.plane.Face | (K ∩ closure (P.plane.faceRegion
            f)).Nonempty}.Finite) ∧ (∀ (x : ℝ × ℝ), ∃ (f : P.plane.Face), x ∈ closure
            (P.plane.faceRegion f)) ∧ (∀ (a : ι), IsOpen (P3776T1OpenStar P a) ∧ IsCompact
            (closure (P3776T1OpenStar P a))) ∧ (∀ (x : ℝ × ℝ), ∃ (a : ι), x ∈ P3776T1OpenStar
            P a) ∧ (∀ (u : ↥P.lattice), ∀ (a : ι), P3776T1OpenStar P (P.shift u a) = (fun (x :
            ℝ × ℝ) => x + GaussianRealPoint (↑u : GaussianInt)) '' P3776T1OpenStar P a) ∧ ∀ (u
            : ↥P.lattice), ∀ (v : ↥P.lattice), ∀ (a : ι), P.shift u a = P.shift v a → u = v) → (∀
            (f : P.plane.Face), ¬Bornology.IsBounded (W f)) ) := by
  classical
  intro ι P U W hgeom f hWb
  have hUnion : Bornology.IsBounded (closure (U f) ∪ W f) :=
    (hgeom.2.1 f).isBounded.union hWb
  have heq : closure (U f) ∪ W f = Set.univ := by
    ext x
    simp [W]
  rw [heq] at hUnion
  exact (NormedSpace.unbounded_univ ℝ (Real × Real)) hUnion

private theorem hboundaryEq :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileCore ι),
        let U (f : P.plane.Face) := P.plane.faceRegion f
        let C (f : P.plane.Face) := frontier (U f)
        (∀ (f : P.plane.Face), C f = P.plane.edgeArc (P.plane.faceVertex f 0) (P.plane.faceVertex
            f 1) ∪ P.plane.edgeArc (P.plane.faceVertex f 1) (P.plane.faceVertex f 2) ∪
            P.plane.edgeArc (P.plane.faceVertex f 2) (P.plane.faceVertex f 0)) → (∀ (f :
            P.plane.Face), ∀ (g : P.plane.Face), Set.range (P.plane.faceVertex f) = Set.range
            (P.plane.faceVertex g) → C f = C g) ) := by
  classical
  intro ι P U C hfront f g hv
  have hidx : ∀ i : Fin 3, ∃ j : Fin 3,
      P.plane.faceVertex f j = P.plane.faceVertex g i := by
    intro i
    have hi : P.plane.faceVertex g i ∈ Set.range (P.plane.faceVertex f) := by
      rw [hv]
      exact ⟨i, rfl⟩
    exact Set.mem_range.mp hi
  choose k hk using hidx
  have hedgeSub (h : P.plane.Face) (i j : Fin 3) (hij : i ≠ j) :
      P.plane.edgeArc (P.plane.faceVertex h i) (P.plane.faceVertex h j) ⊆ C h := by
    intro x hx
    rw [hfront h]
    fin_cases i <;> fin_cases j <;> dsimp at *
    all_goals try exact (hij rfl).elim
    all_goals first
      | exact Or.inl (Or.inl hx)
      | exact Or.inl (Or.inr hx)
      | exact Or.inr hx
      | rw [P.plane.arc_symmetric] at hx
        first
          | exact Or.inl (Or.inl hx)
          | exact Or.inl (Or.inr hx)
          | exact Or.inr hx
  have hsub (hsrc hdst : P.plane.Face)
      (hK : Set.range (P.plane.faceVertex hsrc) =
        Set.range (P.plane.faceVertex hdst)) : C hsrc ⊆ C hdst := by
    intro x hx
    rw [hfront hsrc] at hx
    have hidx' : ∀ i : Fin 3, ∃ j : Fin 3,
        P.plane.faceVertex hdst j = P.plane.faceVertex hsrc i := by
      intro i
      have hi : P.plane.faceVertex hsrc i ∈ Set.range (P.plane.faceVertex hdst) := by
        rw [← hK]
        exact ⟨i, rfl⟩
      exact Set.mem_range.mp hi
    choose l hl using hidx'
    have hEdge (i j : Fin 3) (hij : i ≠ j)
        (hijx : x ∈ P.plane.edgeArc (P.plane.faceVertex hsrc i)
          (P.plane.faceVertex hsrc j)) : x ∈ C hdst := by
      have hne : l i ≠ l j := by
        intro heq
        have heqv : P.plane.faceVertex hsrc i = P.plane.faceVertex hsrc j := by
          calc
            P.plane.faceVertex hsrc i = P.plane.faceVertex hdst (l i) := (hl i).symm
            _ = P.plane.faceVertex hdst (l j) := congrArg _ heq
            _ = P.plane.faceVertex hsrc j := hl j
        exact hij (P.plane.face_vertices_distinct hsrc heqv)
      have hijx' : x ∈ P.plane.edgeArc (P.plane.faceVertex hdst (l i))
          (P.plane.faceVertex hdst (l j)) := by
        simpa only [hl i, hl j] using hijx
      exact hedgeSub hdst (l i) (l j) hne hijx'
    rcases hx with (hx | hx) | hx
    · exact hEdge 0 1 (by decide) hx
    · exact hEdge 1 2 (by decide) hx
    · exact hEdge 2 0 (by decide) hx
  apply Set.Subset.antisymm
  · exact hsub f g hv
  · exact hsub g f hv.symm

private theorem hinj :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileCore ι),
        let U (f : P.plane.Face) := P.plane.faceRegion f
        let C (f : P.plane.Face) := frontier (U f)
        let W (f : P.plane.Face) := (closure (U f))ᶜ
        (Nontrivial ι ∧ (∀ (f : P.plane.Face), IsCompact (closure (P.plane.faceRegion f))) ∧ (∀
            (K : Set (ℝ × ℝ)), IsCompact K → {f : P.plane.Face | (K ∩ closure (P.plane.faceRegion
            f)).Nonempty}.Finite) ∧ (∀ (x : ℝ × ℝ), ∃ (f : P.plane.Face), x ∈ closure
            (P.plane.faceRegion f)) ∧ (∀ (a : ι), IsOpen (P3776T1OpenStar P a) ∧ IsCompact
            (closure (P3776T1OpenStar P a))) ∧ (∀ (x : ℝ × ℝ), ∃ (a : ι), x ∈ P3776T1OpenStar
            P a) ∧ (∀ (u : ↥P.lattice), ∀ (a : ι), P3776T1OpenStar P (P.shift u a) = (fun (x :
            ℝ × ℝ) => x + GaussianRealPoint (↑u : GaussianInt)) '' P3776T1OpenStar P a) ∧ ∀ (u
            : ↥P.lattice), ∀ (v : ↥P.lattice), ∀ (a : ι), P.shift u a = P.shift v a → u = v) →
            ((∀ (f : P.plane.Face), ∀ (V : Set (ℝ × ℝ)), IsPreconnected V → Disjoint V (frontier
            (P.plane.faceRegion f)) → (V ∩ P.plane.faceRegion f).Nonempty → V ⊆
            P.plane.faceRegion f) → ((∀ (f : P.plane.Face), Disjoint (P3767T1FixedTrace
            P.plane) (U f)) → ((∀ (f : P.plane.Face), C f ⊆ P3767T1FixedTrace P.plane) → ((∀ (f
            : P.plane.Face), IsConnected (W f)) → ((∀ (f : P.plane.Face), ¬ Bornology.IsBounded
            (W f)) → ((∀ (f : P.plane.Face), ∀ (g : P.plane.Face), (Set.range (P.plane.faceVertex
            f) = Set.range (P.plane.faceVertex g)) → (C f = C g)) → (Function.Injective (fun f :
            P.plane.Face => Set.range (P.plane.faceVertex f))))))))) ) := by
  classical
  intro ι P U C W hgeom hbarrier havoid hCtrace hWconnected hWunbounded hboundaryEq f g hv
  by_contra hne
  have hCfCg : C f = C g := hboundaryEq f g hv
  have hRgW : U g ⊆ W f := by
    intro x hx
    have hnotRf : x ∉ U f := by
      intro hxf
      exact Set.disjoint_left.mp (P.plane.region_disjoint hne).symm hx hxf
    have hnotCf : x ∉ C f := by
      intro hxf
      exact Set.disjoint_left.mp (havoid g) (hCtrace f hxf) hx
    intro hxcl
    rw [closure_eq_self_union_frontier] at hxcl
    rcases hxcl with hxR | hxC
    · exact hnotRf hxR
    · exact hnotCf hxC
  have hWg : W f ⊆ U g := by
    apply hbarrier g (W f) (hWconnected f).isPreconnected
    · apply Set.disjoint_left.mpr
      intro x hxW hxC
      have hxCf : x ∈ C f := hCfCg.symm ▸ hxC
      exact hxW (frontier_subset_closure hxCf)
    · obtain ⟨x, hx⟩ := (P.plane.region_connected g).nonempty
      exact ⟨x, hRgW hx, hx⟩
  have heq : W f = U g := Set.Subset.antisymm hWg hRgW
  have hboundG : Bornology.IsBounded (U g) :=
    (hgeom.2.1 g).isBounded.subset subset_closure
  exact hWunbounded f (heq ▸ hboundG)

private theorem hendpoints :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileCore ι), ∀ (a : ι), ∀ (b : ι), P.plane.adjacent a b →
            P.plane.position a ∈ P.plane.edgeArc a b ∧ P.plane.position b ∈ P.plane.edgeArc a b )
            := by
  classical
  intro ι P a b hab
  obtain ⟨e, hzero, hone⟩ := P.plane.arc_homeomorph a b hab
  constructor
  · rw [← hzero]
    exact (e ⟨0, by norm_num⟩).property
  · rw [← hone]
    exact (e ⟨1, by norm_num⟩).property

private theorem hvertexC :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileCore ι),
        let U (f : P.plane.Face) := P.plane.faceRegion f
        let C (f : P.plane.Face) := frontier (U f)
        ∀ [ Nontrivial ι], (∀ (f : P.plane.Face), C f = P.plane.edgeArc (P.plane.faceVertex
            f 0) (P.plane.faceVertex f 1) ∪ P.plane.edgeArc (P.plane.faceVertex f 1)
            (P.plane.faceVertex f 2) ∪ P.plane.edgeArc (P.plane.faceVertex f 2)
            (P.plane.faceVertex f 0)) → (∀ (f : P.plane.Face), (∀ (a : ι), ∀ (b : ι),
            (P.plane.adjacent a b) → (P.plane.position a ∈ P.plane.edgeArc a b ∧ P.plane.position
            b ∈ P.plane.edgeArc a b)) → (
        let A : Set ι := Set.range (P.plane.faceVertex f)
        ∀ (w : ι), P.plane.position w ∈ C f ↔ w ∈ A)) ) := by
  classical
  intro ι P U C this hfront f hendpoints A w
  constructor
  · intro hw
    rw [hfront f] at hw
    rcases hw with (hw | hw) | hw
    · rcases (P3767T1VertexEdgeIncidence P.plane w).2 _ _
        (P.plane.face_edges f 0 1 (by decide)) hw with h | h
      · exact ⟨0, h.symm⟩
      · exact ⟨1, h.symm⟩
    · rcases (P3767T1VertexEdgeIncidence P.plane w).2 _ _
        (P.plane.face_edges f 1 2 (by decide)) hw with h | h
      · exact ⟨1, h.symm⟩
      · exact ⟨2, h.symm⟩
    · rcases (P3767T1VertexEdgeIncidence P.plane w).2 _ _
        (P.plane.face_edges f 2 0 (by decide)) hw with h | h
      · exact ⟨2, h.symm⟩
      · exact ⟨0, h.symm⟩
  · rintro ⟨i, rfl⟩
    fin_cases i
    · rw [hfront f]
      exact Or.inl (Or.inl
        ((hendpoints _ _ (P.plane.face_edges f 0 1 (by decide))).1))
    · rw [hfront f]
      exact Or.inl (Or.inr
        ((hendpoints _ _ (P.plane.face_edges f 1 2 (by decide))).1))
    · rw [hfront f]
      exact Or.inr
        ((hendpoints _ _ (P.plane.face_edges f 2 0 (by decide))).1)

private theorem hedgeTri :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileCore ι),
        let U (f : P.plane.Face) := P.plane.faceRegion f
        let C (f : P.plane.Face) := frontier (U f)
        (∀ (f : P.plane.Face), C f = P.plane.edgeArc (P.plane.faceVertex f 0) (P.plane.faceVertex
            f 1) ∪ P.plane.edgeArc (P.plane.faceVertex f 1) (P.plane.faceVertex f 2) ∪
            P.plane.edgeArc (P.plane.faceVertex f 2) (P.plane.faceVertex f 0)) → (∀ (f :
            P.plane.Face), ∀ (i : Fin (3 : ℕ)), ∀ (j : Fin (3 : ℕ)), i ≠ j → P.plane.edgeArc
            (P.plane.faceVertex f i) (P.plane.faceVertex f j) ⊆ C f) ) := by
  classical
  intro ι P U C hfront f i j hij x hx
  rw [hfront f]
  fin_cases i <;> fin_cases j <;> dsimp at *
  all_goals try exact (hij rfl).elim
  all_goals first
    | exact Or.inl (Or.inl hx)
    | exact Or.inl (Or.inr hx)
    | exact Or.inr hx
      | rw [P.plane.arc_symmetric] at hx
        first
          | exact Or.inl (Or.inl hx)
          | exact Or.inl (Or.inr hx)
          | exact Or.inr hx

private theorem hstarIntersect :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileCore ι),
        let U (f : P.plane.Face) := P.plane.faceRegion f
        ∀ [ Nontrivial ι], (∀ (f : P.plane.Face), Disjoint (P3767T1FixedTrace P.plane) (U
            f)) → (∀ (u : ι), ∀ (v : ι), u ≠ v → ∀ x ∈ P3776T1OpenStar P u, x ∈
            P3776T1OpenStar P v → P.plane.adjacent u v) ) := by
  classical
  intro ι P U this havoid u v huv x hu hv
  change x = P.plane.position u ∨
    (∃ c, P.plane.adjacent u c ∧ x ∈ P.plane.edgeArc u c ∧
      x ≠ P.plane.position u ∧ x ≠ P.plane.position c) ∨
    ∃ g, (∃ i, P.plane.faceVertex g i = u) ∧ x ∈ U g at hu
  change x = P.plane.position v ∨
    (∃ c, P.plane.adjacent v c ∧ x ∈ P.plane.edgeArc v c ∧
      x ≠ P.plane.position v ∧ x ≠ P.plane.position c) ∨
    ∃ g, (∃ i, P.plane.faceVertex g i = v) ∧ x ∈ U g at hv
  have hposTrace (w : ι) : P.plane.position w ∈ P3767T1FixedTrace P.plane :=
    Or.inl ⟨w, rfl⟩
  rcases hu with hxu | ⟨c, huc, hxuArc, hxun, hxc⟩ | ⟨g, hgu, hxg⟩
  · rcases hv with hxv | ⟨d, hvd, hxvArc, hxvn, hxd⟩ | ⟨g, hgv, hxg⟩
    · exact (huv (P.plane.position_injective (hxu.symm.trans hxv))).elim
    · have hvtx := (P3767T1VertexEdgeIncidence P.plane u).2 v d hvd
        (hxu ▸ hxvArc)
      rcases hvtx with h | h
      · exact (huv h).elim
      · exact (hxd (hxu.trans (congrArg P.plane.position h))).elim
    · exact (Set.disjoint_left.mp (havoid g) (hposTrace u) (hxu ▸ hxg)).elim
  · rcases hv with hxv | ⟨d, hvd, hxvArc, hxvn, hxd⟩ | ⟨g, hgv, hxg⟩
    · have hvtx := (P3767T1VertexEdgeIncidence P.plane v).2 u c huc
        (hxv.symm ▸ hxuArc)
      rcases hvtx with h | h
      · exact (huv h.symm).elim
      · exact (hxc (hxv.trans (congrArg P.plane.position h))).elim
    · by_cases hend : ({u, c} : Set ι) = {v, d}
      · have humem : u ∈ ({v, d} : Set ι) := by rw [← hend]; simp
        rcases Set.mem_insert_iff.mp humem with h | h
        · exact (huv h).elim
        · have hdu : d = u := (Set.mem_singleton_iff.mp h).symm
          have hvu : P.plane.adjacent v u := hdu ▸ hvd
          exact (P.plane.adjacent_symmetric u v).mpr hvu
      · have hboth := P.plane.arc_intersections u c v d huc hvd hend
        have hxin : x ∈ P.plane.position '' (({u, c} : Set ι) ∩ {v, d}) := by
          rw [← hboth]
          exact ⟨hxuArc, hxvArc⟩
        obtain ⟨w, hw, hxw⟩ := hxin
        rcases Set.mem_insert_iff.mp hw.1 with h | h
        · subst w
          exact (hxun (hxw.symm)).elim
        · subst w
          exact (hxc (hxw.symm)).elim
    · exact (Set.disjoint_left.mp (havoid g)
        (Or.inr ⟨u, c, huc, hxuArc⟩) hxg).elim
  · rcases hv with hxv | ⟨d, hvd, hxvArc, hxvn, hxd⟩ | ⟨h, hvh, hxh⟩
    · exact (Set.disjoint_left.mp (havoid g) (hposTrace v) (hxv ▸ hxg)).elim
    · exact (Set.disjoint_left.mp (havoid g)
        (Or.inr ⟨v, d, hvd, hxvArc⟩) hxg).elim
    · have hface : g = h := by
        by_contra hne
        exact Set.disjoint_left.mp (P.plane.region_disjoint hne) hxg hxh
      subst h
      obtain ⟨i, hi⟩ := hgu
      obtain ⟨j, hj⟩ := hvh
      have hij : i ≠ j := by
        intro hij
        exact huv (hi.symm.trans (hij ▸ hj))
      simpa only [hi, hj] using P.plane.face_edges g i j hij

private theorem hstarCoverW :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileCore ι),
        let U (f : P.plane.Face) := P.plane.faceRegion f
        let C (f : P.plane.Face) := frontier (U f)
        let W (f : P.plane.Face) := (closure (U f))ᶜ
        (Function.Injective (fun f : P.plane.Face => Set.range (P.plane.faceVertex f))) → (∀ (f :
            P.plane.Face),
        let A : Set ι := Set.range (P.plane.faceVertex f)
        (∀ (w : ι), P.plane.position w ∈ C f ↔ w ∈ A) → ((∀ (i : Fin 3), ∀ (j : Fin 3), (i ≠ j) →
            (P.plane.edgeArc (P.plane.faceVertex f i) (P.plane.faceVertex f j) ⊆ C f)) → (∀ x ∈ W
            f, ∃ v ∉ A, x ∈ P3776T1OpenStar P v))) ) := by
  classical
  intro ι P U C W hinj f A hvertexC hedgeTri x hxW
  have hcover : x ∈ Set.range P.plane.position ∪
      {p | ∃ u v, P.plane.adjacent u v ∧ p ∈ P.plane.edgeArc u v} ∪
      {p | ∃ g, p ∈ U g} := by
    rw [P.plane.plane_cover]
    exact Set.mem_univ x
  rcases hcover with (⟨u, rfl⟩ | ⟨u, v, huv, hxarc⟩) | ⟨g, hxg⟩
  · have huA : u ∉ A := by
      intro huA
      exact hxW (frontier_subset_closure (hvertexC u |>.2 huA))
    exact ⟨u, huA, Or.inl rfl⟩
  · by_cases hxu : x = P.plane.position u
    · have huA : u ∉ A := by
        intro huA
        exact hxW (frontier_subset_closure (hxu ▸ hvertexC u |>.2 huA))
      exact ⟨u, huA, Or.inl hxu⟩
    · by_cases hxv : x = P.plane.position v
      · have hvA : v ∉ A := by
          intro hvA
          exact hxW (frontier_subset_closure (hxv ▸ hvertexC v |>.2 hvA))
        exact ⟨v, hvA, Or.inl hxv⟩
      · by_cases huA : u ∈ A
        · by_cases hvA : v ∈ A
          · change u ∈ Set.range (P.plane.faceVertex f) at huA
            change v ∈ Set.range (P.plane.faceVertex f) at hvA
            obtain ⟨i, hi⟩ := huA
            obtain ⟨j, hj⟩ := hvA
            have hij : i ≠ j := by
              intro hij
              have huv' : u = v := by
                calc
                  u = P.plane.faceVertex f i := hi.symm
                  _ = P.plane.faceVertex f j := congrArg (P.plane.faceVertex f) hij
                  _ = v := hj
              exact P.plane.adjacent_irreflexive u (huv' ▸ huv)
            have hxarc' : x ∈ P.plane.edgeArc
                (P.plane.faceVertex f i) (P.plane.faceVertex f j) := by
              rw [hi, hj]
              exact hxarc
            exact (hxW (frontier_subset_closure (hedgeTri i j hij hxarc'))).elim
          · exact ⟨v, hvA, Or.inr (Or.inl ⟨u,
              (P.plane.adjacent_symmetric v u).2 huv, by
                rw [P.plane.arc_symmetric]
                exact hxarc, hxv, hxu⟩)⟩
        · exact ⟨u, huA, Or.inr (Or.inl ⟨v, huv, hxarc, hxu, hxv⟩)⟩
  · have hsome : ∃ i : Fin 3, P.plane.faceVertex g i ∉ A := by
      by_contra hnone
      have hall : ∀ i : Fin 3, P.plane.faceVertex g i ∈ A := by
        intro i
        by_contra hi
        exact hnone ⟨i, hi⟩
      have hidx : ∀ i : Fin 3, ∃ j : Fin 3,
          P.plane.faceVertex f j = P.plane.faceVertex g i := by
        intro i
        have hiA := hall i
        change P.plane.faceVertex g i ∈ Set.range (P.plane.faceVertex f) at hiA
        have hi : P.plane.faceVertex g i ∈ Set.range (P.plane.faceVertex f) := hiA
        exact Set.mem_range.mp hi
      choose k hk using hidx
      have hkinj : Function.Injective k := by
        intro i j hij
        apply P.plane.face_vertices_distinct g
        calc
          P.plane.faceVertex g i = P.plane.faceVertex f (k i) := (hk i).symm
          _ = P.plane.faceVertex f (k j) := congrArg (P.plane.faceVertex f) hij
          _ = P.plane.faceVertex g j := hk j
      have hksurj : Function.Surjective k := Finite.surjective_of_injective hkinj
      have hfg : Set.range (P.plane.faceVertex f) = Set.range (P.plane.faceVertex g) := by
        apply Set.Subset.antisymm
        · intro x hx
          obtain ⟨i, rfl⟩ := Set.mem_range.mp hx
          obtain ⟨j, hji⟩ := hksurj i
          refine ⟨j, ?_⟩
          calc
            P.plane.faceVertex g j = P.plane.faceVertex f (k j) := (hk j).symm
            _ = P.plane.faceVertex f i := congrArg (P.plane.faceVertex f) hji
        · intro x hx
          obtain ⟨i, rfl⟩ := Set.mem_range.mp hx
          exact ⟨k i, hk i⟩
      have hfg' := hinj hfg
      subst g
      exact hxW (subset_closure hxg)
    obtain ⟨i, hi⟩ := hsome
    exact ⟨P.plane.faceVertex g i, hi, Or.inr (Or.inr ⟨g, ⟨i, rfl⟩, hxg⟩)⟩

private theorem hSopen :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileCore ι), (Nontrivial ι ∧ (∀ (f : P.plane.Face),
            IsCompact (closure (P.plane.faceRegion f))) ∧ (∀ (K : Set (ℝ × ℝ)), IsCompact K → {f
            : P.plane.Face | (K ∩ closure (P.plane.faceRegion f)).Nonempty}.Finite) ∧ (∀ (x : ℝ ×
            ℝ), ∃ (f : P.plane.Face), x ∈ closure (P.plane.faceRegion f)) ∧ (∀ (a : ι), IsOpen
            (P3776T1OpenStar P a) ∧ IsCompact (closure (P3776T1OpenStar P a))) ∧ (∀ (x : ℝ ×
            ℝ), ∃ (a : ι), x ∈ P3776T1OpenStar P a) ∧ (∀ (u : ↥P.lattice), ∀ (a : ι),
            P3776T1OpenStar P (P.shift u a) = (fun (x : ℝ × ℝ) => x + GaussianRealPoint (↑u :
            GaussianInt)) '' P3776T1OpenStar P a) ∧ ∀ (u : ↥P.lattice), ∀ (v : ↥P.lattice), ∀
            (a : ι), P.shift u a = P.shift v a → u = v) → (∀ (f : P.plane.Face), ∀ (a : ι),
        let A : Set ι := Set.range (P.plane.faceVertex f)
        let AdjOut : ι → ι → Prop := fun x y => P.plane.adjacent x y ∧ y ∉ A
        let Reach (v : ι) : Prop := Relation.ReflTransGen AdjOut a v
        let B : Set ι := {v | Reach v}
        ∀ (S : Set (ℝ × ℝ)), S = ⋃ v ∈ B, P3776T1OpenStar P v → IsOpen S) ) := by
  classical
  intro ι P hgeom f a A AdjOut Reach B S hS
  rw [hS]
  apply isOpen_iUnion
  intro v
  apply isOpen_iUnion
  intro hv
  exact (hgeom.2.2.2.2.1 v).1

private theorem hTopen :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileCore ι), (Nontrivial ι ∧ (∀ (f : P.plane.Face),
            IsCompact (closure (P.plane.faceRegion f))) ∧ (∀ (K : Set (ℝ × ℝ)), IsCompact K → {f
            : P.plane.Face | (K ∩ closure (P.plane.faceRegion f)).Nonempty}.Finite) ∧ (∀ (x : ℝ ×
            ℝ), ∃ (f : P.plane.Face), x ∈ closure (P.plane.faceRegion f)) ∧ (∀ (a : ι), IsOpen
            (P3776T1OpenStar P a) ∧ IsCompact (closure (P3776T1OpenStar P a))) ∧ (∀ (x : ℝ ×
            ℝ), ∃ (a : ι), x ∈ P3776T1OpenStar P a) ∧ (∀ (u : ↥P.lattice), ∀ (a : ι),
            P3776T1OpenStar P (P.shift u a) = (fun (x : ℝ × ℝ) => x + GaussianRealPoint (↑u :
            GaussianInt)) '' P3776T1OpenStar P a) ∧ ∀ (u : ↥P.lattice), ∀ (v : ↥P.lattice), ∀
            (a : ι), P.shift u a = P.shift v a → u = v) → (∀ (f : P.plane.Face), ∀ (a : ι),
        let A : Set ι := Set.range (P.plane.faceVertex f)
        let AdjOut : ι → ι → Prop := fun x y => P.plane.adjacent x y ∧ y ∉ A
        let Reach (v : ι) : Prop := Relation.ReflTransGen AdjOut a v
        let B : Set ι := {v | Reach v}
        let T : Set (Real × Real) :=
          ⋃ v ∈ {v : ι | v ∉ A ∧ v ∉ B}, P3776T1OpenStar P v
        IsOpen T) ) := by
  classical
  intro ι P hgeom f a A AdjOut Reach B T
  apply isOpen_iUnion
  intro v
  apply isOpen_iUnion
  intro hv
  exact (hgeom.2.2.2.2.1 v).1

private theorem hST :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileCore ι), ∀ (f : P.plane.Face), ∀ (a : ι),
        let A : Set ι := Set.range (P.plane.faceVertex f)
        (∀ (u : ι), ∀ (v : ι), (u ≠ v) → (∀ (x : Real × Real), (x ∈ P3776T1OpenStar P u) → ((x
            ∈ P3776T1OpenStar P v) → (P.plane.adjacent u v)))) → (
        let AdjOut : ι → ι → Prop := fun x y => P.plane.adjacent x y ∧ y ∉ A
        let Reach (v : ι) : Prop := Relation.ReflTransGen AdjOut a v
        let B : Set ι := {v | Reach v}
        let S : Set (Real × Real) := ⋃ v ∈ B, P3776T1OpenStar P v
        let T : Set (Real × Real) :=
          ⋃ v ∈ {v : ι | v ∉ A ∧ v ∉ B}, P3776T1OpenStar P v
        Disjoint S T) ) := by
  classical
  intro ι P f a A hstarIntersect AdjOut Reach B S T
  apply Set.disjoint_left.mpr
  intro x hxS hxT
  obtain ⟨u, huB, hxu⟩ := Set.mem_iUnion₂.mp hxS
  obtain ⟨v, hvMem, hxv⟩ := Set.mem_iUnion₂.mp hxT
  rcases hvMem with ⟨hvA, hvB⟩
  by_cases huv : u = v
  · exact hvB (huv ▸ huB)
  · have hadj := hstarIntersect u v huv x hxu hxv
    have hvReach : v ∈ B := by
      change Reach v
      exact Relation.ReflTransGen.tail huB ⟨hadj, hvA⟩
    exact hvB hvReach

private theorem hWcover :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileCore ι),
        let U (f : P.plane.Face) := P.plane.faceRegion f
        let W (f : P.plane.Face) := (closure (U f))ᶜ
        ∀ (f : P.plane.Face), ∀ (a : ι),
        let A : Set ι := Set.range (P.plane.faceVertex f)
        (∀ (x : Real × Real), (x ∈ W f) → (∃ v ∉ A, x ∈ P3776T1OpenStar P v)) → (
        let AdjOut : ι → ι → Prop := fun x y => P.plane.adjacent x y ∧ y ∉ A
        let Reach (v : ι) : Prop := Relation.ReflTransGen AdjOut a v
        let B : Set ι := {v | Reach v}
        let S : Set (Real × Real) := ⋃ v ∈ B, P3776T1OpenStar P v
        let T : Set (Real × Real) :=
          ⋃ v ∈ {v : ι | v ∉ A ∧ v ∉ B}, P3776T1OpenStar P v
        W f ⊆ S ∪ T) ) := by
  classical
  intro ι P U W f a A hstarCoverW AdjOut Reach B S T x hx
  obtain ⟨v, hvA, hxv⟩ := hstarCoverW x hx
  by_cases hvB : v ∈ B
  · left
    change x ∈ ⋃ u : ι, ⋃ _ : u ∈ B, P3776T1OpenStar P u
    exact Set.mem_iUnion₂.mpr ⟨v, hvB, hxv⟩
  · right
    change x ∈ ⋃ u : ι, ⋃ _ : u ∈ {v : ι | v ∉ A ∧ v ∉ B},
      P3776T1OpenStar P u
    exact Set.mem_iUnion₂.mpr ⟨v, ⟨hvA, hvB⟩, hxv⟩

private theorem haW :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileCore ι),
        let U (f : P.plane.Face) := P.plane.faceRegion f
        let C (f : P.plane.Face) := frontier (U f)
        let W (f : P.plane.Face) := (closure (U f))ᶜ
        (∀ (f : P.plane.Face), Disjoint (P3767T1FixedTrace P.plane) (U f)) → (∀ (f :
            P.plane.Face), ∀ (a : ι), (a ∉ Set.range (P.plane.faceVertex f)) → (
        let A : Set ι := Set.range (P.plane.faceVertex f)
        (∀ (w : ι), P.plane.position w ∈ C f ↔ w ∈ A) → (P.plane.position a ∈ W f))) ) := by
  classical
  intro ι P U C W havoid f a ha A hvertexC
  have hnotU : P.plane.position a ∉ U f := by
    intro h
    exact Set.disjoint_left.mp (havoid f) (Or.inl ⟨a, rfl⟩) h
  have hnotC : P.plane.position a ∉ C f := by
    intro h
    exact ha (hvertexC a |>.1 h)
  intro hcl
  rw [closure_eq_self_union_frontier] at hcl
  rcases hcl with h | h
  · exact hnotU h
  · exact hnotC h

private theorem haS :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileCore ι), ∀ (f : P.plane.Face), ∀ (a : ι),
        let A : Set ι := Set.range (P.plane.faceVertex f)
        let AdjOut : ι → ι → Prop := fun x y => P.plane.adjacent x y ∧ y ∉ A
        let Reach (v : ι) : Prop := Relation.ReflTransGen AdjOut a v
        let B : Set ι := {v | Reach v}
        (a ∈ B) → (
        let S : Set (Real × Real) := ⋃ v ∈ B, P3776T1OpenStar P v
        P.plane.position a ∈ S) ) := by
  classical
  intro ι P f a A AdjOut Reach B haB S
  change P.plane.position a ∈ ⋃ u : ι, ⋃ _ : u ∈ B, P3776T1OpenStar P u
  exact Set.mem_iUnion₂.mpr ⟨a, haB, Or.inl rfl⟩

private theorem hWS :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileCore ι),
        let U (f : P.plane.Face) := P.plane.faceRegion f
        let W (f : P.plane.Face) := (closure (U f))ᶜ
        (∀ (f : P.plane.Face), IsConnected (W f)) → (∀ (f : P.plane.Face), ∀ (a : ι),
        let A : Set ι := Set.range (P.plane.faceVertex f)
        let AdjOut : ι → ι → Prop := fun x y => P.plane.adjacent x y ∧ y ∉ A
        let Reach (v : ι) : Prop := Relation.ReflTransGen AdjOut a v
        let B : Set ι := {v | Reach v}
        let S : Set (Real × Real) := ⋃ v ∈ B, P3776T1OpenStar P v
        let T : Set (Real × Real) :=
          ⋃ v ∈ {v : ι | v ∉ A ∧ v ∉ B}, P3776T1OpenStar P v
        (IsOpen S) → ((IsOpen T) → ((Disjoint S T) → ((W f ⊆ S ∪ T) → ((P.plane.position a ∈ W f)
            → ((P.plane.position a ∈ S) → (W f ⊆ S))))))) ) := by
  classical
  intro ι P U W hWconnected f a A AdjOut Reach B S T hSopen' hTopen hST hWcover haW haS
  have hsep := (isPreconnected_iff_subset_of_disjoint.mp
    (hWconnected f).isPreconnected) S T hSopen' hTopen hWcover
    (by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
      rintro ⟨_, ⟨hxS, hxT⟩⟩
      exact Set.disjoint_left.mp hST hxS hxT)
  rcases hsep with hS | hT
  · exact hS
  · have haT := hT haW
    exact (Set.disjoint_left.mp hST haS haT).elim

private theorem hpositionW :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileCore ι),
        let U (f : P.plane.Face) := P.plane.faceRegion f
        let C (f : P.plane.Face) := frontier (U f)
        let W (f : P.plane.Face) := (closure (U f))ᶜ
        (∀ (f : P.plane.Face), Disjoint (P3767T1FixedTrace P.plane) (U f)) → (∀ (f :
            P.plane.Face),
        let A : Set ι := Set.range (P.plane.faceVertex f)
        (∀ (w : ι), P.plane.position w ∈ C f ↔ w ∈ A) → (∀ v ∉ A, P.plane.position v ∈ W f)) ) := by
  classical
  intro ι P U C W havoid f A hvertexC v hvA
  have hnotU : P.plane.position v ∉ U f := by
    intro h
    exact Set.disjoint_left.mp (havoid f) (Or.inl ⟨v, rfl⟩) h
  have hnotC : P.plane.position v ∉ C f := by
    intro h
    exact hvA (hvertexC v |>.1 h)
  intro hcl
  rw [closure_eq_self_union_frontier] at hcl
  rcases hcl with h | h
  · exact hnotU h
  · exact hnotC h

private theorem hReachAll :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileCore ι),
        let U (f : P.plane.Face) := P.plane.faceRegion f
        let W (f : P.plane.Face) := (closure (U f))ᶜ
        ∀ (f : P.plane.Face), ∀ (a : ι),
        let A : Set ι := Set.range (P.plane.faceVertex f)
        (∀ (u : ι), ∀ (v : ι), (u ≠ v) → (∀ (x : Real × Real), (x ∈ P3776T1OpenStar P u) → ((x
            ∈ P3776T1OpenStar P v) → (P.plane.adjacent u v)))) → (
        let AdjOut : ι → ι → Prop := fun x y => P.plane.adjacent x y ∧ y ∉ A
        let Reach (v : ι) : Prop := Relation.ReflTransGen AdjOut a v
        let B : Set ι := {v | Reach v}
        let S : Set (Real × Real) := ⋃ v ∈ B, P3776T1OpenStar P v
        (W f ⊆ S) → ((∀ (v : ι), (v ∉ A) → (P.plane.position v ∈ W f)) → (∀ v ∉ A, v ∈ B))) ) := by
  classical
  intro ι P U W f a A hstarIntersect AdjOut Reach B S hWS hpositionW v hvA
  have hvW := hpositionW v hvA
  have hvS := hWS hvW
  obtain ⟨u, uB, hvStar⟩ := Set.mem_iUnion₂.mp hvS
  by_cases huv : u = v
  · exact huv ▸ uB
  · have hadj := hstarIntersect u v huv (P.plane.position v) hvStar (Or.inl rfl)
    change Reach v
    exact Relation.ReflTransGen.tail uB ⟨hadj, hvA⟩

private theorem hchain :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileCore ι), ∀ (f : P.plane.Face),
        let A : Set ι := Set.range (P.plane.faceVertex f)
        let AdjOut : ι → ι → Prop := fun x y => P.plane.adjacent x y ∧ y ∉ A
        ∀ (p : List ι), (List.IsChain AdjOut p) → (∀ (x : ι), ∀ (y : ι), ∀ (l₁ : List ι), ∀ (l₂ :
            List ι), (p = l₁ ++ x :: y :: l₂) → (List.IsChain AdjOut (l₁ ++ x :: y :: l₂))) ) := by
  classical
  intro ι P f A AdjOut p hpchain x y l₁ l₂ heq
  rw [← heq]
  exact hpchain

end FacialDeletionProof

theorem P3861T1FixedFacialDeletion {ι : Type} (P : PeriodicTileCore ι) :
    Function.Injective (fun f : P.plane.Face => Set.range (P.plane.faceVertex f)) ∧
    ∀ f : P.plane.Face, ∀ a b : ι,
      a ∉ Set.range (P.plane.faceVertex f) →
      b ∉ Set.range (P.plane.faceVertex f) →
      ∃ p : List ι,
        p.head? = some a ∧ p.getLast? = some b ∧
        (∀ x ∈ p, x ∉ Set.range (P.plane.faceVertex f)) ∧
        ∀ x y : ι, ∀ l₁ l₂ : List ι,
          p = l₁ ++ x :: y :: l₂ → P.plane.adjacent x y := by
-- BODY
  classical
  let U (f : P.plane.Face) := P.plane.faceRegion f
  let C (f : P.plane.Face) := frontier (U f)
  let W (f : P.plane.Face) := (closure (U f))ᶜ
  have hgeom := P3776T1FixedGeometry P
  let : Nontrivial ι := hgeom.1
  have htrace := P3767T1FixedFaceComponents P.plane
  have hbarrier := htrace.2.1
  have havoid (f : P.plane.Face) :
      Disjoint (P3767T1FixedTrace P.plane) (U f) := htrace.1 f |>.1
  have hfront (f : P.plane.Face) :
      C f = P.plane.edgeArc (P.plane.faceVertex f 0) (P.plane.faceVertex f 1) ∪
        P.plane.edgeArc (P.plane.faceVertex f 1) (P.plane.faceVertex f 2) ∪
        P.plane.edgeArc (P.plane.faceVertex f 2) (P.plane.faceVertex f 0) :=
    P.plane.face_boundary f
  have hCtrace (f : P.plane.Face) : C f ⊆ P3767T1FixedTrace P.plane :=
    htrace.1 f |>.2
  have hCcompact (f : P.plane.Face) := FacialDeletionProof.hCcompact ι P hfront f
  have hWopen (f : P.plane.Face) : IsOpen (W f) := isClosed_closure.isOpen_compl
  have hWnonempty (f : P.plane.Face) := FacialDeletionProof.hWnonempty ι P hgeom f
  have hWpartition (f : P.plane.Face) := FacialDeletionProof.hWpartition ι P f
  have hUsub (f : P.plane.Face) := FacialDeletionProof.hUsub ι P f
  have hcomponentU (f : P.plane.Face) (x : Real × Real)
      (hx : x ∈ U f) := FacialDeletionProof.hcomponentU ι P hbarrier hUsub f x hx
  have hWconnected (f : P.plane.Face) := FacialDeletionProof.hWconnected ι P hfront hWnonempty
      hWpartition hUsub hcomponentU f
  have hWunbounded (f : P.plane.Face) := FacialDeletionProof.hWunbounded ι P hgeom f
  have hboundaryEq (f g : P.plane.Face)
      (hv : Set.range (P.plane.faceVertex f) = Set.range (P.plane.faceVertex g)) :=
          FacialDeletionProof.hboundaryEq ι P hfront f g hv
  have hinj := FacialDeletionProof.hinj ι P hgeom hbarrier havoid hCtrace hWconnected hWunbounded
      hboundaryEq
  refine ⟨hinj, ?_⟩
  intro f a b ha hb
  have hendpoints (a b : ι) (hab : P.plane.adjacent a b) := FacialDeletionProof.hendpoints ι P a
      b hab
  let A : Set ι := Set.range (P.plane.faceVertex f)
  have hvertexC (w : ι) := FacialDeletionProof.hvertexC ι P  hfront f hendpoints w
  have hedgeTri (i j : Fin 3) (hij : i ≠ j) := FacialDeletionProof.hedgeTri ι P hfront f i j hij
  have hstarIntersect (u v : ι) (huv : u ≠ v) (x : Real × Real)
      (hu : x ∈ P3776T1OpenStar P u) (hv : x ∈ P3776T1OpenStar P v) :=
          FacialDeletionProof.hstarIntersect ι P  havoid u v huv x hu hv
  have hstarCoverW (x : Real × Real) (hxW : x ∈ W f) := FacialDeletionProof.hstarCoverW ι P hinj
      f hvertexC hedgeTri x hxW
  let AdjOut : ι → ι → Prop := fun x y => P.plane.adjacent x y ∧ y ∉ A
  let Reach (v : ι) : Prop := Relation.ReflTransGen AdjOut a v
  let B : Set ι := {v | Reach v}
  have haB : a ∈ B := Relation.ReflTransGen.refl
  have hSopen (S : Set (Real × Real))
      (hS : S = ⋃ v ∈ B, P3776T1OpenStar P v) := FacialDeletionProof.hSopen ι P hgeom f a S hS
  let S : Set (Real × Real) := ⋃ v ∈ B, P3776T1OpenStar P v
  let T : Set (Real × Real) :=
    ⋃ v ∈ {v : ι | v ∉ A ∧ v ∉ B}, P3776T1OpenStar P v
  have hSopen' : IsOpen S := hSopen S rfl
  have hTopen := FacialDeletionProof.hTopen ι P hgeom f a
  have hST := FacialDeletionProof.hST ι P f a hstarIntersect
  have hWcover := FacialDeletionProof.hWcover ι P f a hstarCoverW
  have haW := FacialDeletionProof.haW ι P havoid f a ha hvertexC
  have haS := FacialDeletionProof.haS ι P f a haB
  have hWS := FacialDeletionProof.hWS ι P hWconnected f a hSopen' hTopen hST hWcover haW haS
  have hpositionW (v : ι) (hvA : v ∉ A) := FacialDeletionProof.hpositionW ι P havoid f hvertexC v
      hvA
  have hReachAll (v : ι) (hvA : v ∉ A) := FacialDeletionProof.hReachAll ι P f a hstarIntersect
      hWS hpositionW v hvA
  have hpath : Relation.ReflTransGen AdjOut a b := by
    exact hReachAll b hb
  obtain ⟨p, hpne, hpchain, hphead, hplast⟩ :=
    List.exists_isChain_ne_nil_of_relationReflTransGen hpath
  refine ⟨p, ?_, ?_, ?_, ?_⟩
  · calc
      p.head? = some (p.head hpne) := List.head?_eq_some_head hpne
      _ = some a := congrArg some hphead
  · calc
      p.getLast? = some (p.getLast hpne) := List.getLast?_eq_getLast_of_ne_nil hpne
      _ = some b := congrArg some hplast
  · intro x hx
    have hall := hpchain.induction (fun z => z ∉ A) p
      (fun {u v} huv hu => huv.2)
      (by
        intro hne
        simpa [A, hphead] using ha) x hx
    exact hall
  · intro x y l₁ l₂ heq
    have hchain := FacialDeletionProof.hchain ι P f p hpchain x y l₁ l₂ heq
    exact (List.isChain_append_cons_cons.mp hchain).2.1.1

end ApollonianSuperharmonic

end
