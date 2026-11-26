/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Statement

/-!
# Isomorphisms specified by one pair of ends per edge

Bijections on vertices and edges form a graph isomorphism when
one pair of ends for each edge is preserved. Any other pair is
that pair or its reverse. This supplies the isomorphism check
when paths are matched by their ordered vertex and edge lists.
-/

public section
namespace GraphMinor.GM16
open Set Graph
universe u v u' v'

/-- Preserving one pair of ends per edge under bijections preserves
all links in both directions. -/
theorem isLink_iff_of_edge_ends {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}
    {P : Graph α β} {Q : Graph α' β'} (fv : V(P) ≃ V(Q)) (fe : E(P) ≃ E(Q))
    (hEnds : ∀ e : E(P), ∃ x y : V(P), P.IsLink e.val x.val y.val ∧
      Q.IsLink (fe e).val (fv x).val (fv y).val)
    (e : E(P)) (x y : V(P)) :
    P.IsLink e.val x.val y.val ↔ Q.IsLink (fe e).val (fv x).val (fv y).val := by
  obtain ⟨a,b,hP,hQ⟩ := hEnds e
  constructor
  · intro h
    rcases h.eq_and_eq_or_eq_and_eq hP with ⟨hx,hy⟩ | ⟨hx,hy⟩
    · have hx' : x=a := Subtype.ext hx
      have hy' : y=b := Subtype.ext hy
      subst x y
      exact hQ
    · have hx' : x=b := Subtype.ext hx
      have hy' : y=a := Subtype.ext hy
      subst x y
      exact hQ.symm
  · intro h
    rcases h.eq_and_eq_or_eq_and_eq hQ with ⟨hx,hy⟩ | ⟨hx,hy⟩
    · have hx' : x=a := fv.injective (Subtype.ext hx)
      have hy' : y=b := fv.injective (Subtype.ext hy)
      subst x y
      exact hP
    · have hx' : x=b := fv.injective (Subtype.ext hx)
      have hy' : y=a := fv.injective (Subtype.ext hy)
      subst x y
      exact hP.symm

/-- A graph isomorphism preserves incidence on its actual edges and vertices. -/
theorem graphIso_inc_iff {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}
    {P : Graph α β} {Q : Graph α' β'} (φ : Iso P Q) (e : E(P)) (x : V(P)) :
    P.Inc e.val x.val ↔ Q.Inc (φ.edgeEquiv e).val (φ.vertexEquiv x).val := by
  constructor
  · rintro ⟨y,hLink⟩
    exact ⟨(φ.vertexEquiv ⟨y,hLink.right_mem⟩).val,
      (φ.isLink_iff e x ⟨y,hLink.right_mem⟩).mp hLink⟩
  · rintro ⟨y,hLink⟩
    let y₀ := φ.vertexEquiv.symm ⟨y,hLink.right_mem⟩
    refine ⟨y₀.val,(φ.isLink_iff e x y₀).mpr ?_⟩
    simpa only [y₀,Equiv.apply_symm_apply] using hLink

end GraphMinor.GM16
