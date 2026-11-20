/-
Copyright (c) 2026 Tom Murphy VII, Jason Reed, David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Murphy VII, Jason Reed, David Renshaw
-/

module

public import LeanPool.RupertMinimality.Minimality.Oct9Axis

/-! # Oct9 Data -/

@[expose] public section

namespace RupertMinimality

/-!
# Facet functions of an octahedron, bundled

`OctFacets a a' b b' c c'` fixes, once and for all, an affine function for each
of the eight facets (with its linear part).  Conditions such as "the edge
`x → y` is a quad edge" are stated with these functions; the symmetries of the
octahedron act on the bundle.
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

/-- An affine function of a facet `PQR` of `conv V`, with its linear part. -/
structure FacetFn (V : Finset ℝ³) (P Q R : ℝ³) where
  /-- The affine height function supporting the facet. -/
  f : ℝ³ → ℝ
  /-- The normal vector of the affine height function. -/
  N : ℝ³
  hN : ∀ y z, f y - f z = ⟪N, y - z⟫
  hP : f P = 0
  hQ : f Q = 0
  hR : f R = 0
  neg : ∀ w ∈ V, w ≠ P → w ≠ Q → w ≠ R → f w < 0

theorem IsFacetTriangle.nonempty_facetFn {V : Finset ℝ³} {P Q R : ℝ³}
    (h : IsFacetTriangle V P Q R) : Nonempty (FacetFn V P Q R) := by
  obtain ⟨f, fP, fQ, fR, hf⟩ := h
  obtain ⟨N, hN⟩ := exists_normal_of_affine f
  exact ⟨⟨f, N, hN, fP, fQ, fR, hf⟩⟩

/-- Reorder the vertices. -/
noncomputable def FacetFn.p12 {V : Finset ℝ³} {P Q R : ℝ³} (F : FacetFn V P Q R) : FacetFn V Q P
  R :=
  ⟨F.f, F.N, F.hN, F.hQ, F.hP, F.hR, fun w hw h1 h2 h3 => F.neg w hw h2 h1 h3⟩

/-- Exchange the final two vertices of a supporting triangle. -/
noncomputable def FacetFn.p23 {V : Finset ℝ³} {P Q R : ℝ³} (F : FacetFn V P Q R) : FacetFn V P R
  Q :=
  ⟨F.f, F.N, F.hN, F.hP, F.hR, F.hQ, fun w hw h1 h2 h3 => F.neg w hw h1 h3 h2⟩

/-- Transport a supporting triangle along equality of its ambient vertex set. -/
noncomputable def FacetFn.congr {V W : Finset ℝ³} {P Q R : ℝ³} (F : FacetFn V P Q R) (h : V = W) :
    FacetFn W P Q R :=
  ⟨F.f, F.N, F.hN, F.hP, F.hQ, F.hR, fun w hw => F.neg w (h ▸ hw)⟩

/-- The eight facet functions of an octahedron with opposite pairs `(a, a')`,
`(b, b')`, `(c, c')`. -/
structure OctFacets (a a' b b' c c' : ℝ³) where
  nodup : [a, a', b, b', c, c'].Nodup
  /-- Supporting affine function for the face through `a`, `b` and `c`. -/
  abc : FacetFn {a, a', b, b', c, c'} a b c
  /-- Supporting affine function for the face through `a`, `b` and `c'`. -/
  abc' : FacetFn {a, a', b, b', c, c'} a b c'
  /-- Supporting affine function for the face through `a`, `b'` and `c`. -/
  ab'c : FacetFn {a, a', b, b', c, c'} a b' c
  /-- Supporting affine function for the face through `a`, `b'` and `c'`. -/
  ab'c' : FacetFn {a, a', b, b', c, c'} a b' c'
  /-- Supporting affine function for the face through `a'`, `b` and `c`. -/
  a'bc : FacetFn {a, a', b, b', c, c'} a' b c
  /-- Supporting affine function for the face through `a'`, `b` and `c'`. -/
  a'bc' : FacetFn {a, a', b, b', c, c'} a' b c'
  /-- Supporting affine function for the face through `a'`, `b'` and `c`. -/
  a'b'c : FacetFn {a, a', b, b', c, c'} a' b' c
  /-- Supporting affine function for the face through `a'`, `b'` and `c'`. -/
  a'b'c' : FacetFn {a, a', b, b', c, c'} a' b' c'

theorem IsOctahedron.nonempty_octFacets {a a' b b' c c' : ℝ³} (h : IsOctahedron a a' b b' c c') :
    Nonempty (OctFacets a a' b b' c c') := by
  obtain ⟨F1⟩ := h.facet_abc.nonempty_facetFn
  obtain ⟨F2⟩ := h.facet_abc'.nonempty_facetFn
  obtain ⟨F3⟩ := h.facet_ab'c.nonempty_facetFn
  obtain ⟨F4⟩ := h.facet_ab'c'.nonempty_facetFn
  obtain ⟨F5⟩ := h.facet_a'bc.nonempty_facetFn
  obtain ⟨F6⟩ := h.facet_a'bc'.nonempty_facetFn
  obtain ⟨F7⟩ := h.facet_a'b'c.nonempty_facetFn
  obtain ⟨F8⟩ := h.facet_a'b'c'.nonempty_facetFn
  exact ⟨⟨h.nodup, F1, F2, F3, F4, F5, F6, F7, F8⟩⟩

theorem nodup_perm_aux {l l' : List ℝ³} (hp : l.Perm l') (h : l.Nodup) : l'.Nodup :=
  hp.nodup_iff.mp h

/-! Symmetries (the facet functions are the same functions). -/

/-- Exchange the first pair of opposite vertices. -/
noncomputable def OctFacets.swap₁ {a a' b b' c c' : ℝ³} (F : OctFacets a a' b b' c c') :
    OctFacets a' a b b' c c' :=
  have e : ({a, a', b, b', c, c'} : Finset ℝ³) = {a', a, b, b', c, c'} := by
    ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  ⟨nodup_perm_aux (by
    simp only [List.perm_iff_count, List.count_cons]
    intro z
    omega) F.nodup, F.a'bc.congr e, F.a'bc'.congr e, F.a'b'c.congr e,
    F.a'b'c'.congr e, F.abc.congr e, F.abc'.congr e, F.ab'c.congr e, F.ab'c'.congr e⟩

/-- Exchange the second pair of opposite vertices. -/
noncomputable def OctFacets.swap₂ {a a' b b' c c' : ℝ³} (F : OctFacets a a' b b' c c') :
    OctFacets a a' b' b c c' :=
  have e : ({a, a', b, b', c, c'} : Finset ℝ³) = {a, a', b', b, c, c'} := by
    ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  ⟨nodup_perm_aux (by
    simp only [List.perm_iff_count, List.count_cons]
    intro z
    omega) F.nodup, F.ab'c.congr e, F.ab'c'.congr e, F.abc.congr e,
    F.abc'.congr e, F.a'b'c.congr e, F.a'b'c'.congr e, F.a'bc.congr e, F.a'bc'.congr e⟩

/-- Exchange the third pair of opposite vertices. -/
noncomputable def OctFacets.swap₃ {a a' b b' c c' : ℝ³} (F : OctFacets a a' b b' c c') :
    OctFacets a a' b b' c' c :=
  have e : ({a, a', b, b', c, c'} : Finset ℝ³) = {a, a', b, b', c', c} := by
    ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  ⟨nodup_perm_aux (by
    simp only [List.perm_iff_count, List.count_cons]
    intro z
    omega) F.nodup, F.abc'.congr e, F.abc.congr e, F.ab'c'.congr e,
    F.ab'c.congr e, F.a'bc'.congr e, F.a'bc.congr e, F.a'b'c'.congr e, F.a'b'c.congr e⟩

/-- Exchange the first and second pairs of opposite vertices. -/
noncomputable def OctFacets.perm₁₂ {a a' b b' c c' : ℝ³} (F : OctFacets a a' b b' c c') :
    OctFacets b b' a a' c c' :=
  have e : ({a, a', b, b', c, c'} : Finset ℝ³) = {b, b', a, a', c, c'} := by
    ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  ⟨nodup_perm_aux (by
    simp only [List.perm_iff_count, List.count_cons]
    intro z
    omega) F.nodup, F.abc.p12.congr e, F.abc'.p12.congr e, F.a'bc.p12.congr e,
    F.a'bc'.p12.congr e, F.ab'c.p12.congr e, F.ab'c'.p12.congr e, F.a'b'c.p12.congr e,
    F.a'b'c'.p12.congr e⟩

/-- Exchange the second and third pairs of opposite vertices. -/
noncomputable def OctFacets.perm₂₃ {a a' b b' c c' : ℝ³} (F : OctFacets a a' b b' c c') :
    OctFacets a a' c c' b b' :=
  have e : ({a, a', b, b', c, c'} : Finset ℝ³) = {a, a', c, c', b, b'} := by
    ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  ⟨nodup_perm_aux (by
    simp only [List.perm_iff_count, List.count_cons]
    intro z
    omega) F.nodup, F.abc.p23.congr e, F.ab'c.p23.congr e, F.abc'.p23.congr e,
    F.ab'c'.p23.congr e, F.a'bc.p23.congr e, F.a'b'c.p23.congr e, F.a'bc'.p23.congr e,
    F.a'b'c'.p23.congr e⟩

end Minimality

end RupertMinimality
