/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Metric
import LeanPool.GraphMinor.GM11.Regions
import LeanPool.GraphMinor.GM11.NiceStatements
import LeanPool.GraphMinor.GM12.Section4WalkMetric

/-!
# Distances at vertices

A vertex belongs to just its singleton atom. Thus the point distances used for
compressions agree with the singleton distances used for horns and hairs.
-/

public section
namespace GraphMinor.GM16
open Set GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM14 GraphMinor.GM15
universe w
variable {S : Type w} [TopologicalSpace S]

/-- The only atom containing a drawing vertex is its singleton. -/
theorem atom_eq_singleton_of_mem_vertex {H : Drawing S} {a : Set S} {x : S}
    (ha : a ∈ H.A) (hx : x ∈ H.V) (hxa : x ∈ a) : a = {x} := by
  rcases ha with (⟨v, hv, rfl⟩ | ha) | ha
  · rw [mem_singleton_iff] at hxa
    exact congrArg singleton hxa.symm
  · exact ((ha.2.1 hxa).2 hx).elim
  · exact (region_subset ha hxa (H.V_subset_U hx)).elim

/-- At a vertex, point-to-atom distance is singleton-to-atom distance. -/
theorem pointAtomDist_of_mem_vertex {H : Drawing S} (d : Set S → Set S → ℕ)
    {x : S} (hx : x ∈ H.V) (b : Set S) : pointAtomDist H d x b = d {x} b := by
  have hset : {k : ℕ | ∃ a ∈ H.A, x ∈ a ∧ d a b = k} = {d {x} b} := by
    ext k
    constructor
    · rintro ⟨a, ha, hxa, rfl⟩
      rw [atom_eq_singleton_of_mem_vertex ha hx hxa]
      exact mem_singleton _
    · rintro rfl
      exact ⟨{x}, Or.inl (Or.inl ⟨x, hx, rfl⟩), mem_singleton x, rfl⟩
  unfold pointAtomDist
  rw [hset, csInf_singleton]

/-- At two vertices, point distance is the distance of their singleton atoms. -/
theorem pointDist_of_mem_vertices {H : Drawing S} (d : Set S → Set S → ℕ)
    {x y : S} (hx : x ∈ H.V) (hy : y ∈ H.V) : pointDist H d x y = d {x} {y} := by
  have hset : {k : ℕ | ∃ a ∈ H.A, ∃ b ∈ H.A, x ∈ a ∧ y ∈ b ∧ d a b = k} =
      {d {x} {y}} := by
    ext k
    constructor
    · rintro ⟨a, ha, b, hb, hxa, hyb, rfl⟩
      rw [atom_eq_singleton_of_mem_vertex ha hx hxa,
        atom_eq_singleton_of_mem_vertex hb hy hyb]
      exact mem_singleton _
    · rintro rfl
      exact ⟨{x}, Or.inl (Or.inl ⟨x, hx, rfl⟩),
        {y}, Or.inl (Or.inl ⟨y, hy, rfl⟩), mem_singleton x, mem_singleton y, rfl⟩
  unfold pointDist
  rw [hset, csInf_singleton]

/-- Two atoms containing the same point are equal. -/
theorem atom_eq_of_mem {H : Drawing S} {a b : Set S} {x : S}
    (ha : a ∈ H.A) (hb : b ∈ H.A) (hxa : x ∈ a) (hxb : x ∈ b) : a = b := by
  by_cases hx : x ∈ H.V
  · exact (atom_eq_singleton_of_mem_vertex ha hx hxa).trans
      (atom_eq_singleton_of_mem_vertex hb hx hxb).symm
  rcases ha with (⟨v, hv, rfl⟩ | ha) | ha
  · exact (hx (mem_singleton_iff.mp hxa ▸ hv)).elim
  · rcases hb with (⟨v, hv, rfl⟩ | hb) | hb
    · exact (hx (mem_singleton_iff.mp hxb ▸ hv)).elim
    · exact H.edge_eq_of_mem ha hb hxa hxb
    · exact (region_subset hb hxb (ha.2.1 hxa).1).elim
  · rcases hb with (⟨v, hv, rfl⟩ | hb) | hb
    · exact (hx (mem_singleton_iff.mp hxb ▸ hv)).elim
    · exact (region_subset ha hxa (hb.2.1 hxb).1).elim
    · exact region_eq_of_mem ha hb hxa hxb

/-- Point-to-atom distance can be evaluated at the atom containing the point. -/
theorem pointAtomDist_of_mem_atom {H : Drawing S} (d : Set S → Set S → ℕ)
    {x : S} {a : Set S} (ha : a ∈ H.A) (hx : x ∈ a) (b : Set S) :
    pointAtomDist H d x b = d a b := by
  have hset : {k : ℕ | ∃ c ∈ H.A, x ∈ c ∧ d c b = k} = {d a b} := by
    ext k
    constructor
    · rintro ⟨c, hc, hxc, rfl⟩
      rw [atom_eq_of_mem hc ha hxc hx]
      exact mem_singleton _
    · rintro rfl
      exact ⟨a, ha, hx, rfl⟩
  unfold pointAtomDist
  rw [hset, csInf_singleton]

/-- Point distance can be evaluated at the atoms containing the two points. -/
theorem pointDist_of_mem_atoms {H : Drawing S} (d : Set S → Set S → ℕ)
    {x y : S} {a b : Set S} (ha : a ∈ H.A) (hb : b ∈ H.A)
    (hx : x ∈ a) (hy : y ∈ b) : pointDist H d x y = d a b := by
  have hset : {k : ℕ | ∃ c ∈ H.A, ∃ e ∈ H.A, x ∈ c ∧ y ∈ e ∧ d c e = k} =
      {d a b} := by
    ext k
    constructor
    · rintro ⟨c, hc, e, he, hxc, hye, rfl⟩
      rw [atom_eq_of_mem hc ha hxc hx, atom_eq_of_mem he hb hye hy]
      exact mem_singleton _
    · rintro rfl
      exact ⟨a, ha, b, hb, hx, hy, rfl⟩
  unfold pointDist
  rw [hset, csInf_singleton]

variable [T2Space S]

omit [T2Space S] in
/-- The atom triangle inequality also holds for point-to-atom distances. -/
theorem pointAtomDist_triangle {H : Drawing S} {d : Set S → Set S → ℕ}
    (htri : ∀ a ∈ H.A, ∀ b ∈ H.A, ∀ c ∈ H.A, d a c ≤ d a b + d b c)
    (x y : S) {z : Set S} (hz : z ∈ H.A) :
    pointAtomDist H d x z ≤ pointDist H d x y + pointAtomDist H d y z := by
  obtain ⟨a, ha, hxa⟩ := exists_atom H x
  obtain ⟨b, hb, hyb⟩ := exists_atom H y
  rw [pointAtomDist_of_mem_atom d ha hxa z, pointDist_of_mem_atoms d ha hb hxa hyb,
    pointAtomDist_of_mem_atom d hb hyb z]
  exact htri a ha b hb z hz

omit [T2Space S] in
/-- Cutting off atom distances also cuts off point-to-atom distances. -/
theorem pointAtomDist_min (H : Drawing S) (d : Set S → Set S → ℕ) (k : ℕ)
    (x : S) (z : Set S) :
    pointAtomDist H (fun a b => min (d a b) k) x z = min (pointAtomDist H d x z) k := by
  obtain ⟨a, ha, hxa⟩ := exists_atom H x
  rw [pointAtomDist_of_mem_atom _ ha hxa z, pointAtomDist_of_mem_atom d ha hxa z]

omit [T2Space S] in
/-- Cutting off all atom distances cuts off all point distances at the same value. -/
theorem pointDist_min (H : Drawing S) (d : Set S → Set S → ℕ) (k : ℕ) (x y : S) :
    pointDist H (fun a b => min (d a b) k) x y = min (pointDist H d x y) k := by
  obtain ⟨a, ha, hxa⟩ := exists_atom H x
  obtain ⟨b, hb, hyb⟩ := exists_atom H y
  rw [pointDist_of_mem_atoms _ ha hb hxa hyb, pointDist_of_mem_atoms d ha hb hxa hyb]

/-- Point distances of a tangle are at most its order. -/
theorem pointDist_le_order {H : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} (h : HasTangleMetric H θ T d) (x y : S) :
    pointDist H d x y ≤ θ := by
  obtain ⟨a, ha, hxa⟩ := exists_atom H x
  obtain ⟨b, hb, hyb⟩ := exists_atom H y
  obtain ⟨_, K, ins, hK, _, hd⟩ := h
  rw [pointDist_of_mem_atoms d ha hb hxa hyb, hd a ha b hb]
  exact GM12.tangleMetric_le_order hK ins θ a b

/-- Compression loses at most its parameter in the distance between vertices
that remain vertices of the new drawing. -/
theorem compression_vertex_dist_le {H H' : Drawing S} {θ lam : ℕ}
    {T T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d d' : Set S → Set S → ℕ}
    (h : IsLambdaCompression H H' θ lam T T' d d')
    {x y : S} (hx : x ∈ H.V) (hy : y ∈ H.V)
    (hx' : x ∈ H'.V) (hy' : y ∈ H'.V) : d {x} {y} ≤ d' {x} {y} + lam := by
  have hb := h.dist_le x y
  rwa [pointDist_of_mem_vertices d hx hy, pointDist_of_mem_vertices d' hx' hy'] at hb

end GraphMinor.GM16
