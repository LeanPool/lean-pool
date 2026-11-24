/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM09.Defs
public import LeanPool.GraphMinor.Statement
import LeanPool.GraphMinor.GM16.PathIsoWalks
import LeanPool.GraphMinor.GM16.PathWalkEquivalences
import Mathlib.Data.Set.Card

/-!
# Isomorphic paths with the same number of vertices

A spanning simple walk enumerates the vertices of a path by a
finite interval with one more position than its length. Equal
vertex counts therefore give equal walk lengths. Matching these
positions gives an isomorphism preserving the stated ends. This
is used for the subdivision drawing in XVI (4.2).
-/

public section
namespace GraphMinor.GM16
open Set Graph Surface GM09
universe u v u' v'

/-- Paths with equal vertex cardinalities have an isomorphism that
matches their stated ends. -/
theorem exists_iso_of_paths_of_ncard_eq
    {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}
    {G P : Graph α β} {G' Q : Graph α' β'} {a b : α} {a' b' : α'}
    (hP : IsGraphPathWithEnds G P a b) (hQ : IsGraphPathWithEnds G' Q a' b')
    (hCard : V(P).ncard = V(Q).ncard) :
    ∃ φ : Iso P Q, (∀ x : V(P), x.val=a → (φ.vertexEquiv x).val=a') ∧
      (∀ x : V(P), x.val=b → (φ.vertexEquiv x).val=b') := by
  obtain ⟨W,hW,hV,hE⟩ := hP.2
  obtain ⟨W',hW',hV',hE'⟩ := hQ.2
  obtain ⟨φ,hφ⟩ := exists_pathWalk_vertexEquiv W hW hV
  obtain ⟨φ',hφ'⟩ := exists_pathWalk_vertexEquiv W' hW' hV'
  have hPCard : V(P).ncard=W.length+1 := by
    simpa only [Nat.card_fin,Nat.card_coe_set_eq] using (Nat.card_congr φ).symm
  have hQCard : V(Q).ncard=W'.length+1 := by
    simpa only [Nat.card_fin,Nat.card_coe_set_eq] using (Nat.card_congr φ').symm
  exact exists_iso_of_spanning_path_walks W W' hW hW' hV hE hV' hE' (by omega)

end GraphMinor.GM16
