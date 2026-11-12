/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P3861T1FacialDomains
public import LeanPool.ApollonianSuperharmonic.P3861T1FixedFacialDeletion
public import LeanPool.ApollonianSuperharmonic.PlaneFaceOrientation
public import LeanPool.ApollonianSuperharmonic.P3767T1BarrierRegionMaximal
public import LeanPool.ApollonianSuperharmonic.P3934T1PolygonalSidePropagation
public import LeanPool.ApollonianSuperharmonic.P3934T1ArcSideComparison

-- [TABLET NODE: P3861T1RoutedFaceOrientation]

/-!
# P3861T1RoutedFaceOrientation

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace RoutedOrientationProof

private theorem endpoints :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1AllContactRouting P), (∀ (a
            : ι), ∀ (b : ι), (P.plane.adjacent a b) → (P3723T1EdgeContact P a b)) → (∀ (a : ι),
            ∀ (b : ι), (P.plane.adjacent a b) → (D.position a ∈ D.edgeArc a b ∧ D.position b ∈
            D.edgeArc a b)) ) := by
  classical
  intro ι P D contact a b hab
  obtain ⟨g, _, _, hr, h0, h1, _⟩ := D.edgeArc_parameterization a b (contact a b hab)
  rw [← hr]
  exact ⟨⟨⟨0, by norm_num⟩, h0⟩, ⟨⟨1, by norm_num⟩, h1⟩⟩

private theorem position_on_arc :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1AllContactRouting P), ∀
            [Nontrivial ι], (∀ (a : ι), ∀ (b : ι), (P.plane.adjacent a b) →
            (P3723T1EdgeContact P a b)) → ((∀ (a : ι), ∀ (b : ι), (P.plane.adjacent a b) →
            (D.position a ∈ D.edgeArc a b ∧ D.position b ∈ D.edgeArc a b)) → (∀ (w : ι), ∀ (a :
            ι), ∀ (b : ι), (P.plane.adjacent a b) → ((D.position w ∈ D.edgeArc a b) → (w = a ∨ w
            = b)))) ) := by
  classical
  intro ι P D this contact endpoints w a b hab hw
  obtain ⟨z, hwz⟩ := (P3767T1VertexEdgeIncidence P.plane w).1
  by_cases heq : ({w, z} : Set ι) = {a, b}
  · have hm : w ∈ ({a, b} : Set ι) := heq ▸ (by simp)
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hm
  · have hm : D.position w ∈ D.position '' (({w, z} : Set ι) ∩ {a, b}) := by
      rw [← D.edgeArc_intersections w z a b (contact w z hwz) (contact a b hab) heq]
      exact ⟨(endpoints w z hwz).1, hw⟩
    obtain ⟨v, hv, hvw⟩ := hm
    have hvw' : v = w := D.position_injective hvw
    subst v
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hv.2

private theorem front_trace :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1AllContactRouting P), ∀ (F :
            P3861T1FacialDomains P D), ∀ (f : P.plane.Face), frontier (F.region f) ⊆ Set.range
            D.position ∪ {p | ∃ a b, P.plane.adjacent a b ∧ p ∈ D.edgeArc a b} ) := by
  classical
  intro ι P D F f x hx
  rw [F.region_frontier] at hx
  rcases hx with (hx | hx) | hx
  · exact Or.inr ⟨_, _, P.plane.face_edges f 0 1 (by decide), hx⟩
  · exact Or.inr ⟨_, _, P.plane.face_edges f 1 2 (by decide), hx⟩
  · exact Or.inr ⟨_, _, P.plane.face_edges f 2 0 (by decide), hx⟩

private theorem front_positions :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1AllContactRouting P), ∀ (F :
            P3861T1FacialDomains P D), (∀ (a : ι), ∀ (b : ι), (P.plane.adjacent a b) →
            (D.position a ∈ D.edgeArc a b ∧ D.position b ∈ D.edgeArc a b)) → ((∀ (w : ι), ∀ (a :
            ι), ∀ (b : ι), (P.plane.adjacent a b) → ((D.position w ∈ D.edgeArc a b) → (w = a ∨ w
            = b))) → (∀ (f : P.plane.Face), ∀ (w : ι), D.position w ∈ frontier (F.region f) ↔ w ∈
            Set.range (P.plane.faceVertex f))) ) := by
  classical
  intro ι P D F endpoints position_on_arc f w
  rw [F.region_frontier]
  constructor
  · rintro ((hw | hw) | hw)
    · rcases position_on_arc w _ _ (P.plane.face_edges f 0 1 (by decide)) hw with h | h
      · exact ⟨0, h.symm⟩
      · exact ⟨1, h.symm⟩
    · rcases position_on_arc w _ _ (P.plane.face_edges f 1 2 (by decide)) hw with h | h
      · exact ⟨1, h.symm⟩
      · exact ⟨2, h.symm⟩
    · rcases position_on_arc w _ _ (P.plane.face_edges f 2 0 (by decide)) hw with h | h
      · exact ⟨2, h.symm⟩
      · exact ⟨0, h.symm⟩
  · rintro ⟨i, rfl⟩
    fin_cases i
    · exact Or.inl (Or.inl (endpoints _ _ (P.plane.face_edges f 0 1 (by decide))).1)
    · exact Or.inl (Or.inr (endpoints _ _ (P.plane.face_edges f 1 2 (by decide))).1)
    · exact Or.inr (endpoints _ _ (P.plane.face_edges f 2 0 (by decide))).1

private theorem disjoint_from_labels :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1AllContactRouting P), ∀ (F :
            P3861T1FacialDomains P D), (∀ (f : P.plane.Face), frontier (F.region f) ⊆ Set.range
            D.position ∪ {p | ∃ a b, P.plane.adjacent a b ∧ p ∈ D.edgeArc a b}) → ((∀ (f :
            P.plane.Face), ∀ (w : ι), D.position w ∈ frontier (F.region f) ↔ w ∈ Set.range
            (P.plane.faceVertex f)) → (Function.Injective (fun f : P.plane.Face => Set.range
            (P.plane.faceVertex f)) → Pairwise (fun f g : P.plane.Face => Disjoint (F.region f)
            (F.region g)))) ) := by
  classical
  intro ι P D F front_trace front_positions hinj f g hne
  apply Set.disjoint_left.mpr
  intro x hxf hxg
  have sub (f g : P.plane.Face) (hx : (F.region g ∩ F.region f).Nonempty) :
      F.region g ⊆ F.region f :=
    P3767T1BarrierRegionMaximal _ _ _ (F.region_open f) (front_trace f)
      (F.region_connected g).isPreconnected (F.region_avoids_trace g) hx
  have heq : F.region f = F.region g :=
    Set.Subset.antisymm (sub g f ⟨x, hxf, hxg⟩) (sub f g ⟨x, hxg, hxf⟩)
  apply hne
  apply hinj
  ext w
  rw [← front_positions f w, ← front_positions g w, heq]

private theorem face_sides :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1AllContactRouting P), ∀ (F :
            P3861T1FacialDomains P D), (∀ (a : ι), ∀ (b : ι), (P.plane.adjacent a b) →
            (P3723T1EdgeContact P a b)) → (∀ (f : P.plane.Face), ∃ e : Bool, ∀ k : Fin 3,
            P3934T1ArcSide (F.region f) (D.edgeArc (P.plane.faceVertex f k) (P.plane.faceVertex
            f (k + 1))) (D.position (P.plane.faceVertex f k)) (D.position (P.plane.faceVertex f
            (k + 1))) e) ) := by
  classical
  intro ι P D F contact f
  have hp (k : Fin 3) := D.edgeArc_parameterization
    (P.plane.faceVertex f k) (P.plane.faceVertex f (k + 1))
    (contact _ _ (P.plane.face_edges f k (k + 1) (by omega)))
  choose g hc hi hr h0 h1 hs using hp
  let s (k : Fin 3) := Classical.choice (hs k)
  have hjoin (k : Fin 3) : g k ⟨1, by norm_num⟩ = g (k + 1) ⟨0, by norm_num⟩ := by
    rw [h1, h0]
  have hv : Function.Injective (fun k => g k ⟨0, by norm_num⟩) := by
    intro k l h
    dsimp only at h
    rw [h0, h0] at h
    exact P.plane.face_vertices_distinct f (D.position_injective h)
  have pair_ne (k l : Fin 3) (hkl : k ≠ l) :
      ({P.plane.faceVertex f k, P.plane.faceVertex f (k + 1)} : Set ι) ≠
        {P.plane.faceVertex f l, P.plane.faceVertex f (l + 1)} := by
    intro heq
    have hk : P.plane.faceVertex f k ∈
        ({P.plane.faceVertex f l, P.plane.faceVertex f (l + 1)} : Set ι) :=
      heq ▸ (by simp)
    have hk' : P.plane.faceVertex f (k + 1) ∈
        ({P.plane.faceVertex f l, P.plane.faceVertex f (l + 1)} : Set ι) :=
      heq ▸ (by simp)
    have hidx : k = l ∨ k = l + 1 := by
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff,
        (P.plane.face_vertices_distinct f).eq_iff] using hk
    have hidx' : k + 1 = l ∨ k + 1 = l + 1 := by
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff,
        (P.plane.face_vertices_distinct f).eq_iff] using hk'
    fin_cases k <;> fin_cases l <;> simp_all
  have hinter (k l : Fin 3) (hkl : k ≠ l) :
      Set.range (g k) ∩ Set.range (g l) ⊆
        {q | (q = g k ⟨0, by norm_num⟩ ∨ q = g k ⟨1, by norm_num⟩) ∧
          (q = g l ⟨0, by norm_num⟩ ∨ q = g l ⟨1, by norm_num⟩)} := by
    intro q hq
    rw [hr k, hr l, D.edgeArc_intersections _ _ _ _
      (contact _ _ (P.plane.face_edges f k (k + 1) (by omega)))
      (contact _ _ (P.plane.face_edges f l (l + 1) (by omega))) (pair_ne k l hkl)] at hq
    obtain ⟨w, hw, rfl⟩ := hq
    simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    simpa only [Set.mem_ofPred_eq, h0, h1, D.position_injective.eq_iff] using hw
  have hf : frontier (F.region f) = ⋃ k, Set.range (g k) := by
    rw [F.region_frontier]
    ext q
    simp only [Set.mem_union, Set.mem_iUnion, hr]
    constructor
    · rintro ((h | h) | h)
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩
      · exact ⟨2, h⟩
    · rintro ⟨k, h⟩
      fin_cases k
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
  obtain ⟨e, he⟩ := P3934T1PolygonalSidePropagation g s hc hi hjoin hv hinter
    (F.region f) (F.region_open f) hf (F.exterior_frontier f)
  refine ⟨e, fun k => ?_⟩
  exact ⟨g k, hc k, hi k, hr k, h0 k, h1 k, s k, (he k).1⟩

private theorem reverse :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1AllContactRouting P), ∀
            {U : Set (Real × Real)}, ∀ {a : ι}, ∀ {b : ι}, ∀ {e : Bool}, (P3934T1ArcSide U
            (D.edgeArc a b) (D.position a) (D.position b) e) → (P3934T1ArcSide U (D.edgeArc b
            a) (D.position b) (D.position a) (!e)) ) := by
  classical
  intro ι P D U a b e h
  rw [← D.edgeArc_symmetric a b]
  exact (P3934T1ArcSideComparison U U _ _ _ e e).1 h

private theorem any_side :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1AllContactRouting P), ∀ (F :
            P3861T1FacialDomains P D), ∀ (c : P.plane.Face → Bool), (∀ (f : P.plane.Face), ∀ (k
            : Fin (3 : ℕ)), P3934T1ArcSide (F.region f) (D.edgeArc (P.plane.faceVertex f k)
            (P.plane.faceVertex f (k + (1 : Fin (3 : ℕ))))) (D.position (P.plane.faceVertex f k))
            (D.position (P.plane.faceVertex f (k + (1 : Fin (3 : ℕ))))) (c f)) → ((∀
            {U : Set (Real × Real)}, ∀ {a : ι}, ∀ {b : ι}, ∀ {e : Bool}, (P3934T1ArcSide U
            (D.edgeArc a b) (D.position a) (D.position b) e) → (P3934T1ArcSide U (D.edgeArc b
            a) (D.position b) (D.position a) (!e))) → (∀ (f : P.plane.Face), ∀ (a : ι), ∀ (b :
            ι), (P.plane.adjacent a b) → (((∃ i, P.plane.faceVertex f i = a) ∧ (∃ i,
            P.plane.faceVertex f i = b)) → (∃ e : Bool, P3934T1ArcSide (F.region f) (D.edgeArc
            a b) (D.position a) (D.position b) e)))) ) := by
  classical
  intro ι P D F c hc reverse f a b hab hf
  obtain ⟨⟨i, rfl⟩, ⟨j, rfl⟩⟩ := hf
  have hij : i ≠ j := by
    intro h
    subst j
    exact P.plane.adjacent_irreflexive _ hab
  fin_cases i <;> fin_cases j
  all_goals first
    | exact (hij rfl).elim
    | exact ⟨c f, by simpa using hc f 0⟩
    | exact ⟨c f, by simpa using hc f 1⟩
    | exact ⟨c f, by simpa using hc f 2⟩
    | exact ⟨!(c f), by simpa using reverse (hc f 0)⟩
    | exact ⟨!(c f), by simpa using reverse (hc f 1)⟩
    | exact ⟨!(c f), by simpa using reverse (hc f 2)⟩

private theorem left_exists :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1AllContactRouting P), ∀ (F :
            P3861T1FacialDomains P D), (Pairwise fun (f g : P.plane.Face) => Disjoint (F.region
            f) (F.region g)) → ((∀ (f : P.plane.Face), ∀ (a : ι), ∀ (b : ι), (P.plane.adjacent a
            b) → (((∃ i, P.plane.faceVertex f i = a) ∧ (∃ i, P.plane.faceVertex f i = b)) → (∃ e
            : Bool, P3934T1ArcSide (F.region f) (D.edgeArc a b) (D.position a) (D.position b)
            e))) → (∀ (a : ι), ∀ (b : ι), (P.plane.adjacent a b) → (∃ f : P.plane.Face, ((∃ i,
            P.plane.faceVertex f i = a) ∧ (∃ i, P.plane.faceVertex f i = b)) ∧ P3934T1ArcSide
            (F.region f) (D.edgeArc a b) (D.position a) (D.position b) true))) ) := by
  classical
  intro ι P D F hdis any_side a b hab
  obtain ⟨f, g, hfg, hf, hg, _⟩ := P.plane.every_edge_two_faces a b hab
  obtain ⟨e, he⟩ := any_side f a b hab hf
  obtain ⟨d, hd⟩ := any_side g a b hab hg
  have hed := (P3934T1ArcSideComparison (F.region f) (F.region g) _ _ _ e d).2.2
    (hdis hfg) he hd
  cases e <;> cases d
  · exact (hed rfl).elim
  · exact ⟨g, hg, hd⟩
  · exact ⟨f, hf, he⟩
  · exact (hed rfl).elim

private theorem left_spec :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1AllContactRouting P), ∀ (F :
            P3861T1FacialDomains P D), ∀ (left_exists : ∀ (a : ι), ∀ (b : ι), (P.plane.adjacent
            a b) → (∃ f : P.plane.Face, ((∃ i, P.plane.faceVertex f i = a) ∧ (∃ i,
            P.plane.faceVertex f i = b)) ∧ P3934T1ArcSide (F.region f) (D.edgeArc a b)
            (D.position a) (D.position b) true)), ∀ (f₀ : P.plane.Face),
        let L (a b : ι) : P.plane.Face := if h : P.plane.adjacent a b then
          Classical.choose (left_exists a b h) else f₀
        ∀ (a : ι), ∀ (b : ι), (P.plane.adjacent a b) → (((∃ i, P.plane.faceVertex (L a b) i = a)
            ∧ (∃ i, P.plane.faceVertex (L a b) i = b)) ∧ P3934T1ArcSide (F.region (L a b))
            (D.edgeArc a b) (D.position a) (D.position b) true) ) := by
  classical
  intro ι P D F left_exists f₀ L a b h
  dsimp only [L]
  rw [dite_eq_left h]
  exact Classical.choose_spec (left_exists a b h)

private theorem identify :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (D : P3723T1AllContactRouting P), ∀ (F :
            P3861T1FacialDomains P D), (Pairwise fun (f g : P.plane.Face) => Disjoint (F.region
            f) (F.region g)) → (∀ (left_exists : ∀ (a : ι), ∀ (b : ι), (P.plane.adjacent a b) →
            (∃ f : P.plane.Face, ((∃ i, P.plane.faceVertex f i = a) ∧ (∃ i, P.plane.faceVertex f
            i = b)) ∧ P3934T1ArcSide (F.region f) (D.edgeArc a b) (D.position a) (D.position b)
            true)), ∀ (f₀ : P.plane.Face),
        let L (a b : ι) : P.plane.Face := if h : P.plane.adjacent a b then
          Classical.choose (left_exists a b h) else f₀
        (∀ (a : ι), ∀ (b : ι), (P.plane.adjacent a b) → (((∃ i, P.plane.faceVertex (L a b) i = a)
            ∧ (∃ i, P.plane.faceVertex (L a b) i = b)) ∧ P3934T1ArcSide (F.region (L a b))
            (D.edgeArc a b) (D.position a) (D.position b) true)) → (∀ (f : P.plane.Face), ∀ (a :
            ι), ∀ (b : ι), (P.plane.adjacent a b) → ((P3934T1ArcSide (F.region f) (D.edgeArc a b)
            (D.position a) (D.position b) true) → (L a b = f)))) ) := by
  classical
  intro ι P D F hdis left_exists f₀ L left_spec f a b hab h
  by_contra hne
  exact ((P3934T1ArcSideComparison (F.region (L a b)) (F.region f) _ _ _
    true true).2.2 (hdis hne) (left_spec a b hab).2 h) rfl

end RoutedOrientationProof

theorem P3861T1RoutedFaceOrientation {ι : Type} (P : PeriodicTileComplex ι)
    (D : P3723T1AllContactRouting P) (F : P3861T1FacialDomains P D) :
    Pairwise (fun f g : P.plane.Face => Disjoint (F.region f) (F.region g)) ∧
      Nonempty (PlaneFaceOrientation P.plane) := by
-- BODY
  classical
  let : Nontrivial ι := (P3776T1FixedGeometry P.toPeriodicTileCore).1
  have contact (a b : ι) (hab : P.plane.adjacent a b) :
      P3723T1EdgeContact P a b :=
    ⟨fun h => P.plane.adjacent_irreflexive a (h ▸ hab),
      P.adjacent_has_common_edge a b hab⟩
  have endpoints (a b : ι) (hab : P.plane.adjacent a b) := RoutedOrientationProof.endpoints ι P D
      contact a b hab
  have position_on_arc (w a b : ι) (hab : P.plane.adjacent a b)
      (hw : D.position w ∈ D.edgeArc a b) := RoutedOrientationProof.position_on_arc ι P D
          contact endpoints w a b hab hw
  have front_trace (f : P.plane.Face) := RoutedOrientationProof.front_trace ι P D F f
  have front_positions (f : P.plane.Face) (w : ι) := RoutedOrientationProof.front_positions ι P D
      F endpoints position_on_arc f w
  have disjoint_from_labels := RoutedOrientationProof.disjoint_from_labels ι P D F front_trace
      front_positions
  have hdis := disjoint_from_labels (P3861T1FixedFacialDeletion P.toPeriodicTileCore).1
  refine ⟨hdis, ?_⟩
  have face_sides (f : P.plane.Face) := RoutedOrientationProof.face_sides ι P D F contact f
  choose c hc using face_sides
  have reverse {U : Set (Real × Real)} {a b : ι} {e : Bool}
      (h : P3934T1ArcSide U (D.edgeArc a b) (D.position a) (D.position b) e) :
      P3934T1ArcSide U (D.edgeArc b a) (D.position b) (D.position a) (!e) :=
          RoutedOrientationProof.reverse ι P D (U := U) (a := a) (b := b) (e := e) h
  have any_side (f : P.plane.Face) (a b : ι) (hab : P.plane.adjacent a b)
      (hf : (∃ i, P.plane.faceVertex f i = a) ∧ (∃ i, P.plane.faceVertex f i = b)) :=
          RoutedOrientationProof.any_side ι P D F c hc reverse f a b hab hf
  have left_exists (a b : ι) (hab : P.plane.adjacent a b) := RoutedOrientationProof.left_exists ι
      P D F hdis any_side a b hab
  obtain ⟨a⟩ := (inferInstance : Nonempty ι)
  obtain ⟨b, hab⟩ := (P3767T1VertexEdgeIncidence P.plane a).1
  obtain ⟨f₀, _⟩ := left_exists a b hab
  let L (a b : ι) : P.plane.Face := if h : P.plane.adjacent a b then
    Classical.choose (left_exists a b h) else f₀
  have left_spec (a b : ι) (h : P.plane.adjacent a b) :
      ((∃ i, P.plane.faceVertex (L a b) i = a) ∧
        (∃ i, P.plane.faceVertex (L a b) i = b)) ∧
      P3934T1ArcSide (F.region (L a b)) (D.edgeArc a b)
        (D.position a) (D.position b) true  := RoutedOrientationProof.left_spec ι P D F
      left_exists f₀ a b h
  have identify (f : P.plane.Face) (a b : ι) (hab : P.plane.adjacent a b)
      (h : P3934T1ArcSide (F.region f) (D.edgeArc a b)
        (D.position a) (D.position b) true) : L a b = f := RoutedOrientationProof.identify ι P D
            F hdis left_exists f₀ left_spec f a b hab h
  refine ⟨{ leftFace := L
            left_incident := fun a b h => (left_spec a b h).1
            opposite_sides := ?_
            sides_exhaust_faces := ?_
            coherently_oriented := ?_ }⟩
  · intro a b hab heq
    have hba := (P.plane.adjacent_symmetric a b).mp hab
    have hr := reverse (left_spec b a hba).2
    rw [← heq] at hr
    have hfalse := (P3934T1ArcSideComparison (F.region (L a b))
      (F.region (L a b)) _ _ _ true false).2.1 (left_spec a b hab).2 hr
    exact Bool.noConfusion hfalse
  · intro a b hab f hf
    obtain ⟨e, he⟩ := any_side f a b hab hf
    cases e
    · right
      exact (identify f b a ((P.plane.adjacent_symmetric a b).mp hab)
        (reverse he)).symm
    · exact Or.inl (identify f a b hab he).symm
  · intro f
    have adj (i j : Fin 3) (h : i ≠ j) := P.plane.face_edges f i j h
    cases he : c f
    · refine ⟨Equiv.swap (1 : Fin 3) 2, ?_, ?_, ?_⟩
      · simpa [Equiv.swap_apply_def] using identify f _ _ (adj 0 2 (by decide)) (by
          simpa [he] using reverse (hc f 2))
      · simpa using identify f _ _ (adj 2 1 (by decide)) (by
          simpa [he] using reverse (hc f 1))
      · simpa [Equiv.swap_apply_def] using identify f _ _ (adj 1 0 (by decide)) (by
          simpa [he] using reverse (hc f 0))
    · refine ⟨Equiv.refl _, ?_, ?_, ?_⟩
      · exact identify f _ _ (adj 0 1 (by decide)) (by simpa [he] using hc f 0)
      · exact identify f _ _ (adj 1 2 (by decide)) (by simpa [he] using hc f 1)
      · exact identify f _ _ (adj 2 0 (by decide)) (by simpa [he] using hc f 2)

end ApollonianSuperharmonic

end
