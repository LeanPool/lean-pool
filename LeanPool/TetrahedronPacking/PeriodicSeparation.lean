/-
Copyright (c) 2026 Mike Lady. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mike Lady
-/

-- Modified for Lean Pool.

module

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
import Mathlib.Tactic.Linarith

/-!
# Certifying all translates of a finite motif

Linear inequalities that hold on the vertices hold throughout their convex
hull. A nonzero separating functional sends interior points to strict
inequalities, so equality at a shared boundary is allowed. In lattice
coordinates, a point common to two translated hulls forces the shift to lie
between differences of vertex-coordinate bounds. This reduces interior
disjointness for the infinite orbit to separation checks in finite boxes.
-/

@[expose] public section

namespace TetrahedronPacking

open Set

private theorem hull_le {E : Type*} [AddCommGroup E] [Module ℝ E]
    {ι : Type*} {v : ι → E} {f : E →ₗ[ℝ] ℝ} {a : ℝ}
    (h : ∀ i, f (v i) ≤ a) {x : E} (hx : x ∈ convexHull ℝ (range v)) :
    f x ≤ a := by
  refine convexHull_min ?_ (convex_halfSpace_le f.isLinear a) hx
  rintro _ ⟨i, rfl⟩
  exact h i

private theorem hull_ge {E : Type*} [AddCommGroup E] [Module ℝ E]
    {ι : Type*} {v : ι → E} {f : E →ₗ[ℝ] ℝ} {a : ℝ}
    (h : ∀ i, a ≤ f (v i)) {x : E} (hx : x ∈ convexHull ℝ (range v)) :
    a ≤ f x := by
  refine convexHull_min ?_ (convex_halfSpace_ge f.isLinear a) hx
  rintro _ ⟨i, rfl⟩
  exact h i

theorem disjoint_interiors_of_separating_plane
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι κ : Type*} {v : ι → E} {w : κ → E}
    (f : E →L[ℝ] ℝ) (hf : f ≠ 0) (a : ℝ)
    (hv : ∀ i, f (v i) ≤ a) (hw : ∀ j, a ≤ f (w j)) :
    Disjoint (interior (convexHull ℝ (range v))) (interior (convexHull ℝ (range w))) := by
  apply disjoint_left.2
  intro x hx hx'
  have hsubset : convexHull ℝ (range v) ⊆ f ⁻¹' Iic a :=
    fun _ hy => hull_le (f := f.toLinearMap) hv hy
  have hlt := (f.isOpenMap_of_ne_zero hf).interior_preimage_subset_preimage_interior
    (interior_mono hsubset hx)
  rw [interior_Iic] at hlt
  exact (not_lt_of_ge (hull_ge (f := f.toLinearMap) hw (interior_subset hx'))) hlt

theorem separator_of_vertex_comparisons {E : Type*}
    [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    {ι κ : Type*} [Finite ι] [Nonempty ι]
    {v : ι → E} {w : κ → E} (f : E →L[ℝ] ℝ) (hf : f ≠ 0)
    (h : (∀ i j, f (v i) ≤ f (w j)) ∨ (∀ i j, f (w j) ≤ f (v i))) :
    ∃ (g : E →L[ℝ] ℝ) (a : ℝ), g ≠ 0 ∧
      (∀ i, g (v i) ≤ a) ∧ ∀ j, a ≤ g (w j) := by
  have forward (g : E →L[ℝ] ℝ) (hg : g ≠ 0) (hvw : ∀ i j, g (v i) ≤ g (w j)) :
      ∃ (g : E →L[ℝ] ℝ) (a : ℝ), g ≠ 0 ∧
        (∀ i, g (v i) ≤ a) ∧ ∀ j, a ≤ g (w j) := by
    let s := range fun i => g (v i)
    refine ⟨g, sSup s, hg, fun i => le_csSup ?_ ⟨i, rfl⟩, fun j => csSup_le ?_ ?_⟩
    · exact (finite_range _).bddAbove
    · exact range_nonempty _
    · rintro _ ⟨i, rfl⟩
      exact hvw i j
  obtain h | h := h
  · exact forward f hf h
  · exact forward (-f) (neg_ne_zero.mpr hf) (fun i j => by simpa using neg_le_neg (h i j))

/-- The lattice-coordinate shift of any intersection lies between differences
of vertex bounds. The endpoints may include shifts at boundary contact. -/
theorem shift_bounds_of_hulls_intersect
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    {ι κ α : Type*} (C : E ≃ₗ[ℝ] (α → ℝ))
    (v : ι → E) (w : κ → E) (k : α → ℤ)
    (loV hiV loW hiW : α → ℝ)
    (hv : ∀ i j, loV j ≤ C (v i) j ∧ C (v i) j ≤ hiV j)
    (hw : ∀ i j, loW j ≤ C (w i) j ∧ C (w i) j ≤ hiW j)
    {x : E} (hx : x ∈ convexHull ℝ (range v))
    (hx' : x ∈ convexHull ℝ (range (fun i => w i + C.symm (fun j => (k j : ℝ))))) :
    ∀ j, loV j - hiW j ≤ (k j : ℝ) ∧ (k j : ℝ) ≤ hiV j - loW j := by
  intro j
  let f := (LinearMap.proj j).comp C.toLinearMap
  have hV₁ := hull_ge (f := f) (fun i => (hv i j).1) hx
  have hV₂ := hull_le (f := f) (fun i => (hv i j).2) hx
  have hshift (i : κ) : f (w i + C.symm (fun j => (k j : ℝ))) = C (w i) j + k j := by
    simp [f]
  have hW₁ := hull_ge (f := f) (a := loW j + k j) (fun i => by
    rw [hshift]
    exact add_le_add_left (hw i j).1 _) hx'
  have hW₂ := hull_le (f := f) (a := hiW j + k j) (fun i => by
    rw [hshift]
    exact add_le_add_left (hw i j).2 _) hx'
  constructor <;> linarith

/-- A certificate of interior disjointness for every integer shift. For a
motif, apply this to each ordered pair and omit the zero shift for self-pairs.
For finite coordinate index types the integer bounds give finite test sets. -/
theorem disjoint_interiors_of_bounded_shift_certificates
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι κ α : Type*} (C : E ≃ₗ[ℝ] (α → ℝ))
    (v : ι → E) (w : κ → E) (required : (α → ℤ) → Prop)
    (loV hiV loW hiW : α → ℝ)
    (hv : ∀ i j, loV j ≤ C (v i) j ∧ C (v i) j ≤ hiV j)
    (hw : ∀ i j, loW j ≤ C (w i) j ∧ C (w i) j ≤ hiW j)
    (certificate : ∀ k : α → ℤ, required k →
      (∀ j, loV j - hiW j ≤ (k j : ℝ) ∧ (k j : ℝ) ≤ hiV j - loW j) →
      ∃ (f : E →L[ℝ] ℝ) (a : ℝ), f ≠ 0 ∧ (∀ i, f (v i) ≤ a) ∧
        ∀ i, a ≤ f (w i + C.symm (fun j => (k j : ℝ)))) :
    ∀ k : α → ℤ, required k →
      Disjoint (interior (convexHull ℝ (range v)))
        (interior (convexHull ℝ (range (fun i => w i + C.symm (fun j => (k j : ℝ)))))) := by
  intro k hk
  by_contra hoverlap
  obtain ⟨x, hx, hx'⟩ := Set.not_disjoint_iff.mp hoverlap
  have h := shift_bounds_of_hulls_intersect C v w k loV hiV loW hiW hv hw
    (interior_subset hx) (interior_subset hx')
  obtain ⟨f, a, hf, hfv, hfw⟩ := certificate k hk h
  exact Set.disjoint_left.mp (disjoint_interiors_of_separating_plane f hf a hfv hfw) hx hx'

end TetrahedronPacking
