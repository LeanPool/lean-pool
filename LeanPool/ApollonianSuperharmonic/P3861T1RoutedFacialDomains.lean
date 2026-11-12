/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P3861T1FacialDomains
public import LeanPool.ApollonianSuperharmonic.P3861T1FixedFacialDeletion
public import LeanPool.ApollonianSuperharmonic.P3861T1RealPolygonDomains
public import LeanPool.ApollonianSuperharmonic.P3913T1RoutedFaceSubdivision
public import LeanPool.ApollonianSuperharmonic.P3913T1OffFaceExterior
public import LeanPool.ApollonianSuperharmonic.P3913T1RoutedArcExterior
public import LeanPool.ApollonianSuperharmonic.P3913T1RoutedTraceClosed

-- [TABLET NODE: P3861T1RoutedFacialDomains]

/-!
# P3861T1RoutedFacialDomains

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P3861T1RoutedFacialDomains {ι : Type} (P : PeriodicTileComplex ι)
    (D : P3723T1AllContactRouting P) :
    Nonempty (P3861T1FacialDomains P D) := by
-- BODY
  classical
  let J (f : P.plane.Face) : Set (Real × Real) :=
    D.edgeArc (P.plane.faceVertex f 0) (P.plane.faceVertex f 1) ∪
      D.edgeArc (P.plane.faceVertex f 1) (P.plane.faceVertex f 2) ∪
      D.edgeArc (P.plane.faceVertex f 2) (P.plane.faceVertex f 0)
  have polygons (f : P.plane.Face) :
      ∃ (n : Nat) (p : Fin (n + 3) → Real × Real),
        Function.Injective p ∧
        (∀ i j : Fin (n + 3), i ≠ j →
          segment Real (p i) (p (i + 1)) ∩ segment Real (p j) (p (j + 1)) =
            {x | (x = p i ∨ x = p (i + 1)) ∧
              (x = p j ∨ x = p (j + 1))}) ∧
        (⋃ i, segment Real (p i) (p (i + 1))) = J f := by
    have contact (a b : ι) (hab : P.plane.adjacent a b) :
        P3723T1EdgeContact P a b :=
      ⟨(fun e => P.plane.adjacent_irreflexive a (e.symm ▸ hab)),
        P.adjacent_has_common_edge a b hab⟩
    have params (k : Fin 3) := D.edgeArc_parameterization
      (P.plane.faceVertex f k) (P.plane.faceVertex f (k + 1))
      (contact _ _ (P.plane.face_edges f k (k + 1) (by fin_cases k <;> decide)))
    choose g hc hi hr h0 h1 hs using params
    let s (k : Fin 3) := Classical.choice (hs k)
    obtain ⟨n, p, _, hinj, hedge, hcarrier, _⟩ :=
      P3913T1RoutedFaceSubdivision P D f g hc hi hr h0 h1 s
    exact ⟨n, p, hinj, hedge, hcarrier⟩
  have separated (f : P.plane.Face) :
      ∃ U V : Set (Real × Real),
        IsOpen U ∧ IsConnected U ∧ Bornology.IsBounded U ∧
        IsOpen V ∧ IsConnected V ∧ ¬ Bornology.IsBounded V ∧
        Disjoint U V ∧ U ∪ V = (J f)ᶜ ∧
        frontier U = J f ∧ frontier V = J f := by
    obtain ⟨n, p, hi, he, hJ⟩ := polygons f
    have hs := P3861T1RealPolygonDomains p hi he
    dsimp only at hs
    rw [hJ] at hs
    exact hs
  choose U V hUo hUc hUb hVo hVc hVb hd hp hUf hVf using separated
  have avoidance_from_deletion :
      (∀ f : P.plane.Face, ∀ a b : ι,
        a ∉ Set.range (P.plane.faceVertex f) →
        b ∉ Set.range (P.plane.faceVertex f) →
        ∃ p : List ι,
          p.head? = some a ∧ p.getLast? = some b ∧
          (∀ x ∈ p, x ∉ Set.range (P.plane.faceVertex f)) ∧
          ∀ x y : ι, ∀ l₁ l₂ : List ι,
            p = l₁ ++ x :: y :: l₂ → P.plane.adjacent x y) →
      ∀ f, Disjoint (U f) (Set.range D.position ∪
        {p | ∃ a b, P.plane.adjacent a b ∧ p ∈ D.edgeArc a b}) := by
    intro hdelete f
    have hout := (P3913T1OffFaceExterior P D f (U f) (V f)
      (hUo f) (hVo f) (hUb f) (hd f) (hp f) (hdelete f)).2
    obtain ⟨hpos, _, harc⟩ := P3913T1RoutedArcExterior P D f (U f) (V f)
      (hUo f) (hVo f) (hd f) (hp f) hout
    have hmissJ : Disjoint (U f) (J f) := by
      apply Set.disjoint_left.mpr
      intro x hx hxJ
      have hcomp : x ∈ (J f)ᶜ := by
        rw [← hp f]
        exact Or.inl hx
      exact hcomp hxJ
    have hmiss : Disjoint (U f) (J f ∪ V f) := hmissJ.union_right (hd f)
    apply Set.disjoint_left.mpr
    intro x hx htrace
    apply Set.disjoint_left.mp hmiss hx
    rcases htrace with h | ⟨a, b, hab, hx⟩
    · exact hpos h
    · exact harc a b hab hx
  have havoid := avoidance_from_deletion
    (P3861T1FixedFacialDeletion P.toPeriodicTileCore).2
  have exterior (f : P.plane.Face) : (closure (U f))ᶜ = V f := by
    rw [closure_eq_self_union_frontier, hUf f]
    apply Set.Subset.antisymm
    · intro x hx
      have hnot : x ∉ U f ∧ x ∉ J f := by
        simpa only [Set.mem_compl_iff, Set.mem_union, not_or] using hx
      have hUV : x ∈ U f ∪ V f := by
        rw [hp f]
        exact hnot.2
      exact hUV.resolve_left hnot.1
    · intro x hx
      have hnotU : x ∉ U f := fun hu => Set.disjoint_left.mp (hd f) hu hx
      have hnotJ : x ∉ J f := by
        have hUV : x ∈ U f ∪ V f := Or.inr hx
        rw [hp f] at hUV
        exact hUV
      exact fun h => h.elim hnotU hnotJ
  refine ⟨{
    region := U
    trace_closed := ?_
    region_open := hUo
    region_connected := hUc
    region_bounded := hUb
    region_avoids_trace := havoid
    region_frontier := hUf
    exterior_connected := ?_
    exterior_frontier := ?_
  }⟩
  · exact P3913T1RoutedTraceClosed P D
  · intro f
    rw [exterior]
    exact hVc f
  · intro f
    rw [exterior, hVf, hUf]

end ApollonianSuperharmonic

end
