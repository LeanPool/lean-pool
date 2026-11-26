/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
/- Modified by Lean Pool contributors for the current Lean and Mathlib toolchain. -/
module

public import LeanPool.SplitCliqueGap.R434.CoreDirections
public import LeanPool.SplitCliqueGap.R434.TightTriangles
import Mathlib.Tactic.FinCases

/-! Lifting the H54 triangle incidence table to the affine core. -/

@[expose] public section

open Finset

namespace GapExtremal.R434.H54

variable {R : Type} [Fintype R] [DecidableEq R] [CommRing R]

/-- The ordered vertices of a template triangle lifted into an affine block. -/
def blockTriangle (a x : R) (t : Triangle) : OrderedTriangle (Role × R) :=
  (affineVertex a x (0,t.1), affineVertex a x (1,t.2.1), affineVertex a x (2,t.2.2))

/-- The template edge of the specified kind in a triangle. -/
def onTriangleIndex (t : Triangle) (k : Fin 3) : Edge :=
  if k = 0 then (0,t.1,t.2.1) else if k = 1 then (1,t.2.1,t.2.2) else (2,t.1,t.2.2)

theorem onTriangleIndex_kind (t : Triangle) (k : Fin 3) : (onTriangleIndex t k).1 = k := by
  fin_cases k <;> rfl

theorem onEdge_iff_index (t : Triangle) (e : Edge) :
    onEdge t e ↔ e = onTriangleIndex t e.1 := by
  obtain ⟨k, i, j⟩ := e
  fin_cases k <;> simp [onEdge, onTriangleIndex]

omit [Fintype R] in
theorem triangleEdges_block (a x : R) (t : Triangle) :
    triangleEdges (blockTriangle a x t) =
      univ.image (fun k => blockEdge a x (onTriangleIndex t k)) := by
  ext y
  simp only [triangleEdges, mem_insert, mem_singleton, mem_image, mem_univ, true_and]
  constructor
  · rintro (hy | hy | hy)
    · exact ⟨0, hy.symm⟩
    · exact ⟨1, hy.symm⟩
    · exact ⟨2, hy.symm⟩
  · rintro ⟨k,hk⟩
    fin_cases k
    · exact Or.inl hk.symm
    · exact Or.inr (Or.inl hk.symm)
    · exact Or.inr (Or.inr hk.symm)

omit [Fintype R] in
theorem blockEdge_mem_blockTriangle (h : R) (hh : 2 * h = 1)
    {a x b y : R} {t : Triangle} {e : Edge} :
    blockEdge b y e ∈ triangleEdges (blockTriangle a x t) ↔
      b = a ∧ y = x ∧ onEdge t e := by
  rw [triangleEdges_block]
  constructor
  · intro hmem
    obtain ⟨k, _, hk⟩ := mem_image.mp hmem
    have hei : (a,x,onTriangleIndex t k) = (b,y,e) := blockEdge_injective h hh hk
    have hdir : a = b := congrArg Prod.fst hei
    have hx : x = y := congrArg (fun z : R × R × Edge => z.2.1) hei
    have he : onTriangleIndex t k = e := congrArg (fun z : R × R × Edge => z.2.2) hei
    have hkind : k = e.1 := (onTriangleIndex_kind t k).symm.trans (congrArg Prod.fst he)
    exact ⟨hdir.symm, hx.symm, (onEdge_iff_index t e).mpr (hkind ▸ he.symm)⟩
  · rintro ⟨rfl,rfl,he⟩
    exact mem_image.mpr ⟨e.1, mem_univ _, congrArg (blockEdge b y) ((onEdge_iff_index t e).mp
      he).symm⟩

omit [DecidableEq R] [Fintype R] in
theorem blockTriangle_injective (h : R) (hh : 2 * h = 1) :
    Function.Injective (fun z : R × R × Triangle => blockTriangle z.1 z.2.1 z.2.2) := by
  intro ⟨a,x,t⟩ ⟨b,y,s⟩ he
  have h₂ : blockEdge a x (0,t.1,t.2.1) = blockEdge b y (0,s.1,s.2.1) :=
    congrArg (fun z : OrderedTriangle (Role × R) => s(z.1,z.2.1)) he
  have ei : ((a,x,(0,t.1,t.2.1)) : R × R × Edge) = (b,y,(0,s.1,s.2.1)) :=
    blockEdge_injective h hh h₂
  have ha : a = b := congrArg Prod.fst ei
  have hx : x = y := congrArg (fun z : R × R × Edge => z.2.1) ei
  have hfst : t.1 = s.1 := congrArg (fun z : R × R × Edge => z.2.2.2.1) ei
  have hmid : t.2.1 = s.2.1 := congrArg (fun z : R × R × Edge => z.2.2.2.2) ei
  have hlast : t.2.2 = s.2.2 := congrArg (fun z : OrderedTriangle (Role × R) => z.2.2.1.2) he
  exact Prod.ext ha (Prod.ext hx (Prod.ext hfst (Prod.ext hmid hlast)))

omit [DecidableEq R] [Fintype R] in
theorem short_directions_eq_of_blockTriangle (h : R) (hh : 2 * h = 1)
    (a x : R) (t : Triangle) :
    let u := blockTriangle a x t
    pairDirection (roleStep h) u.1 u.2.1 = pairDirection (roleStep h) u.2.1 u.2.2 := by
  dsimp only [blockTriangle]
  rw [edge_direction h hh (show (0 : Fin 3) < 1 by decide),
    edge_direction h hh (show (1 : Fin 3) < 2 by decide)]

omit [DecidableEq R] [Fintype R] in
theorem is_blockTriangle_of_local (h : R) {T : OrderedTriangle (Role × R)}
    (hc : T.1.1.1 = 0 ∧ T.2.1.1.1 = 1 ∧ T.2.2.1.1 = 2)
    (hloc : pairDirection (roleStep h) T.1 T.2.1 = pairDirection (roleStep h) T.2.1 T.2.2) :
    ∃ a x, ∃ t : Triangle, blockTriangle a x t = T := by
  obtain ⟨a,x,_,hu,hv,hw⟩ := local_vertices_of_short_directions h hc.1 hc.2.1 hc.2.2 hloc
  let t : Triangle := (T.1.1.2,T.2.1.1.2,T.2.2.1.2)
  have h₁ : ((0,t.1) : Role) = T.1.1 := Prod.ext hc.1.symm rfl
  have h₂ : ((1,t.2.1) : Role) = T.2.1.1 := Prod.ext hc.2.1.symm rfl
  have h₃ : ((2,t.2.2) : Role) = T.2.2.1 := Prod.ext hc.2.2.symm rfl
  refine ⟨a,x,t,?_⟩
  unfold blockTriangle
  rw [h₁,h₂,h₃,hu,hv,hw]

end GapExtremal.R434.H54
