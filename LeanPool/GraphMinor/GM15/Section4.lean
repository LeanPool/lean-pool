/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

import LeanPool.GraphMinor.GM12.Section79

public import LeanPool.GraphMinor.GM15.Defs
public import LeanPool.GraphMinor.GM15.Cited
import LeanPool.GraphMinor.GM10.Section6
import LeanPool.GraphMinor.GM10.Section12
import LeanPool.GraphMinor.GM11.CitedResults
import LeanPool.GraphMinor.GM11.RadialExists
import LeanPool.GraphMinor.GM11.RadialFacts
import LeanPool.GraphMinor.GM11.Section6
import LeanPool.GraphMinor.GM12.Section1b
import LeanPool.GraphMinor.GM12.Section4
import LeanPool.GraphMinor.GM12.Section711Cited
import LeanPool.GraphMinor.GM14.DiscSlope
import LeanPool.GraphMinor.GM14.Section3
import LeanPool.GraphMinor.Surface.Epstein

import LeanPool.GraphMinor.GM12.Section710

import LeanPool.GraphMinor.GM12.Section77
import LeanPool.GraphMinor.GM12.Section4SpanSeparation

/-!
# Graph Minors XV, Section 4: Rearrangement

This file formalizes Section 4 ("Rearrangement", pages 124–128) of N. Robertson and P. D. Seymour,
*Graph Minors. XV. Giant steps*, J. Combin. Theory Ser. B 68 (1996) 112–148:
- **Graph Minors XV, (4.1)** (`GM15Theorem41Statement`, page 124): slope agreement for compressions
  `T₁, T₂` of `T`, and `T₁ ⊆ T₂` when `H₁ = H₂` and `λ₁ ≥ λ₂`.
- **Graph Minors XV, (4.2)** (`GM15Theorem42Statement`, page 125): distance bound `d'(x, y) ≤ d(x,
  y)`
  away from `Z`.
- **Graph Minors XV, (4.3)** (`GM15Theorem43Statement`, `theorem_4_3`, page 125): `H - z^λ` is
  2-cell,
  proved from Graph Minors XII, (7.11) (`GM12Theorem711Statement`).
- **Graph Minors XV, (4.4)** (`GM15Theorem44Statement`, page 126): unique `(4λ + 2)`-compression in
  a
  2-cell subdrawing `H' ⊆ H` containing all atoms at distance `> λ` from `z`.
- **Graph Minors XV, (4.5)** (`GM15Theorem45Statement`, page 126): unique `(4λ + 2)`-compression in
  a
  2-cell drawing `H'` containing all atoms of `H` at distance `> λ` from `z`.
- **Graph Minors XV, (4.6)** (`GM15Theorem46Statement`, page 126): rearranging a `Σ`-span within `λ`
  of `z`.
- **Graph Minors XV, (4.7)** (`GM15Theorem47Statement`, page 127): preservation of free sets at
  distance `> 2|X| + 5λ + 2` from `z` under `(4λ + 2)`-compression.
-/

@[expose] public section

namespace GraphMinor.GM15

open Set Function Topology
open Graph SimpleGraph Hypergraph Surface GM06 GM09 GM10 GM11 GM14

universe u v w

/-! ## Helper Lemmas on Atoms, Radial Drawings, and Tangle Metrics -/

/-- Every atom `a ∈ Γ.A` of a drawing `Γ` is nonempty. -/
theorem atom_nonempty {S : Type w} [TopologicalSpace S] {Γ : Drawing S} {a : Set S}
    (ha : a ∈ Γ.A) : a.Nonempty := by
  rcases ha with (⟨v, _, rfl⟩ | he) | hr
  · exact singleton_nonempty v
  · exact he.1
  · exact region_nonempty hr

/-- Distinct atoms of a drawing `Γ` are disjoint: if `σ ∈ a₁` and `σ ∈ a₂` for `a₁, a₂ ∈ Γ.A`,
then `a₁ = a₂`. -/
theorem atom_eq_of_mem {S : Type w} [TopologicalSpace S] {Γ : Drawing S} {a₁ a₂ : Set S}
    (ha₁ : a₁ ∈ Γ.A) (ha₂ : a₂ ∈ Γ.A) {σ : S} (h₁ : σ ∈ a₁) (h₂ : σ ∈ a₂) :
    a₁ = a₂ := by
  rcases ha₁ with (⟨v₁, hv₁, hEq₁⟩ | he₁) | hr₁ <;>
    rcases ha₂ with (⟨v₂, hv₂, hEq₂⟩ | he₂) | hr₂
  · subst hEq₁; subst hEq₂
    rw [← mem_singleton_iff.mp h₁, ← mem_singleton_iff.mp h₂]
  · subst hEq₁
    rw [mem_singleton_iff.mp h₁] at h₂
    exact ((he₂.2.1 h₂).2 hv₁).elim
  · subst hEq₁
    rw [mem_singleton_iff.mp h₁] at h₂
    exact (region_subset hr₂ h₂ (Γ.V_subset_U hv₁)).elim
  · subst hEq₂
    rw [mem_singleton_iff.mp h₂] at h₁
    exact ((he₁.2.1 h₁).2 hv₂).elim
  · exact Γ.edge_eq_of_mem he₁ he₂ h₁ h₂
  · exact (region_subset hr₂ h₂ (he₁.2.1 h₁).1).elim
  · subst hEq₂
    rw [mem_singleton_iff.mp h₂] at h₁
    exact (region_subset hr₁ h₁ (Γ.V_subset_U hv₂)).elim
  · exact (region_subset hr₁ h₁ (he₂.2.1 h₂).1).elim
  · exact region_eq_of_mem hr₁ hr₂ h₁ h₂

/-- Every point `σ : S` lies in some atom `a ∈ Γ.A`. -/
theorem exists_atom_of_point {S : Type w} [TopologicalSpace S] (Γ : Drawing S) (σ : S) :
    ∃ a ∈ Γ.A, σ ∈ a := by
  by_cases hV : σ ∈ Γ.V
  · exact ⟨{σ}, Or.inl (Or.inl ⟨σ, hV, rfl⟩), mem_singleton σ⟩
  · by_cases hU : σ ∈ Γ.U
    · obtain ⟨e, he, hσe⟩ := Γ.exists_edge_of_mem hU hV
      exact ⟨e, Or.inl (Or.inr he), hσe⟩
    · obtain ⟨r, hr, hσr⟩ := exists_region_of_notMem hU
      exact ⟨r, Or.inr hr, hσr⟩

/-- If `σ₁ ∈ a₁ ∈ Γ.A` and `σ₂ ∈ a₂ ∈ Γ.A`, then `pointDist Γ d σ₁ σ₂ = d a₁ a₂`. -/
theorem pointDist_eq_of_mem_atom {S : Type w} [TopologicalSpace S]
    {Γ : Drawing S} {d : Set S → Set S → ℕ} {σ₁ σ₂ : S} {a₁ a₂ : Set S}
    (ha₁ : a₁ ∈ Γ.A) (ha₂ : a₂ ∈ Γ.A) (h₁ : σ₁ ∈ a₁) (h₂ : σ₂ ∈ a₂) :
    pointDist Γ d σ₁ σ₂ = d a₁ a₂ := by
  have hEq : {k : ℕ | ∃ b₁ ∈ Γ.A, ∃ b₂ ∈ Γ.A, σ₁ ∈ b₁ ∧ σ₂ ∈ b₂ ∧ d b₁ b₂ = k} = {d a₁ a₂} := by
    ext k
    simp only [mem_ofPred_eq, mem_singleton_iff]
    refine ⟨?_, fun hk => ⟨a₁, ha₁, a₂, ha₂, h₁, h₂, hk.symm⟩⟩
    rintro ⟨b₁, hb₁, b₂, hb₂, hσ₁, hσ₂, rfl⟩
    rw [atom_eq_of_mem hb₁ ha₁ hσ₁ h₁, atom_eq_of_mem hb₂ ha₂ hσ₂ h₂]
  rw [pointDist, hEq, csInf_singleton]

/-- If `σ ∈ a ∈ Γ.A`, then `pointAtomDist Γ d σ b = d a b`. -/
theorem pointAtomDist_eq_of_mem_atom {S : Type w} [TopologicalSpace S]
    {Γ : Drawing S} {d : Set S → Set S → ℕ} {σ : S} {a b : Set S}
    (ha : a ∈ Γ.A) (hσ : σ ∈ a) :
    pointAtomDist Γ d σ b = d a b := by
  have hEq : {k : ℕ | ∃ a' ∈ Γ.A, σ ∈ a' ∧ d a' b = k} = {d a b} := by
    ext k
    simp only [mem_ofPred_eq, mem_singleton_iff]
    refine ⟨?_, fun hk => ⟨a, ha, hσ, hk.symm⟩⟩
    rintro ⟨a', ha', hσ', rfl⟩
    rw [atom_eq_of_mem ha' ha hσ' hσ]
  rw [pointAtomDist, hEq, csInf_singleton]

/-- If `H'` is a subdrawing of `H` and an atom `a ∈ H.A` meets an atom `a' ∈ H'.A`, then `a ⊆ a'`.
-/
theorem atom_subset_of_isSubdrawing {S : Type w} [TopologicalSpace S]
    {H H' : Drawing S} (hSub : H'.IsSubdrawing H) {a a' : Set S}
    (ha : a ∈ H.A) (ha' : a' ∈ H'.A) {σ : S} (hσ : σ ∈ a) (hσ' : σ ∈ a') :
    a ⊆ a' := by
  rcases ha with (⟨v, hv, hEq⟩ | he) | hr
  · subst hEq
    rw [← mem_singleton_iff.mp hσ]
    exact singleton_subset_iff.mpr hσ'
  · rcases ha' with (⟨v', hv', hEq'⟩ | he') | hr'
    · subst hEq'
      rw [mem_singleton_iff.mp hσ'] at hσ
      exact ((he.2.1 hσ).2 (hSub.1 hv')).elim
    · rw [H.edge_eq_of_mem he (hSub.2 he') hσ hσ']
    · have hdisj : Disjoint a H'.U := by
        rw [Set.disjoint_left]
        intro x hxe hxU'
        by_cases hxV' : x ∈ H'.V
        · exact (he.2.1 hxe).2 (hSub.1 hxV')
        · obtain ⟨f, hf, hxf⟩ := H'.exists_edge_of_mem hxU' hxV'
          have hef : a = f := H.edge_eq_of_mem he (hSub.2 hf) hxe hxf
          exact region_subset hr' hσ' (hf.2.1 (hef ▸ hσ)).1
      exact subset_region hr' he.2.2.1.isConnected.isPreconnected hdisj hσ hσ'
  · rcases ha' with (⟨v', hv', hEq'⟩ | he') | hr'
    · subst hEq'
      rw [mem_singleton_iff.mp hσ'] at hσ
      exact (region_subset hr hσ (H.V_subset_U (hSub.1 hv'))).elim
    · exact (region_subset hr hσ (hSub.U_subset (he'.2.1 hσ').1)).elim
    · have hdisj : Disjoint a H'.U := by
        rw [Set.disjoint_left]
        intro x hxr hxU'
        exact region_subset hr hxr (hSub.U_subset hxU')
      exact subset_region hr' (region_isPreconnected hr) hdisj hσ hσ'

/-- In a closed surface `S`, if an edge `e ∈ H.E` is also an atom of another drawing `H'`, then
`e ∈ H'.E`. -/
theorem edge_mem_E_of_mem_A {S : Type w} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) {H H' : Drawing S} {e : Set S}
    (he : e ∈ H.E) (he' : e ∈ H'.A) : e ∈ H'.E := by
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  rcases he' with (⟨w, _, rfl⟩ | he'E) | hr'
  · exfalso
    obtain ⟨u, v, hlink⟩ := (H.toGraph.edge_mem_iff_exists_isLink {w}).mp he
    have hu : u ∈ closure ({w} : Set S) ∩ H.V := by
      rw [hlink.2.2.2]
      exact mem_insert u {v}
    rw [isClosed_singleton.closure_eq] at hu
    exact (he.2.1 hu.1).2 hu.2
  · exact he'E
  · exfalso
    obtain ⟨y, hye, hyU⟩ :=
      exists_notMem_U (Γ := H) hS (region_isOpen hr') (region_nonempty hr')
    exact hyU (he.2.1 hye).1

/-- In a closed surface `S`, if a vertex singleton `{v}` (`v ∈ H.V`) is an atom of another drawing
`H'`, then `v ∈ H'.V`. -/
theorem vertex_mem_V_of_mem_A {S : Type w} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) {H H' : Drawing S} {v : S}
    (hv : v ∈ H.V) (hv' : ({v} : Set S) ∈ H'.A) : v ∈ H'.V := by
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  rcases hv' with (⟨w, hw, hwv⟩ | he') | hr'
  · rwa [singleton_eq_singleton_iff.mp hwv] at hw
  · exfalso
    obtain ⟨u, w, hlink⟩ := (H'.toGraph.edge_mem_iff_exists_isLink {v}).mp he'
    have hu : u ∈ closure ({v} : Set S) ∩ H'.V := by
      rw [hlink.2.2.2]
      exact mem_insert u {w}
    rw [isClosed_singleton.closure_eq] at hu
    exact (he'.2.1 hu.1).2 hu.2
  · exfalso
    obtain ⟨y, hyv, hyU⟩ :=
      exists_notMem_U (Γ := H) hS (region_isOpen hr') (region_nonempty hr')
    rw [mem_singleton_iff.mp hyv] at hyU
    exact hyU (H.V_subset_U hv)

/-- In a closed surface `S`, if a region `r ∈ H.R` is also an atom of another drawing `H'`, then
`r ∈ H'.R`. -/
theorem region_mem_R_of_mem_A {S : Type w} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) {H H' : Drawing S} {r : Set S}
    (hr : r ∈ H.R) (hr' : r ∈ H'.A) : r ∈ H'.R := by
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  rcases hr' with (⟨w, hw', rfl⟩ | he') | hr'R
  · exfalso
    obtain ⟨y, hyr, hyU⟩ :=
      exists_notMem_U (Γ := H') hS (region_isOpen hr) (region_nonempty hr)
    rw [mem_singleton_iff.mp hyr] at hyU
    exact hyU (H'.V_subset_U hw')
  · exfalso
    obtain ⟨y, hyr, hyU⟩ :=
      exists_notMem_U (Γ := H') hS (region_isOpen hr) (region_nonempty hr)
    exact hyU (he'.2.1 hyr).1
  · exact hr'R

/-- In a bipartite graph with bipartition `(X, Xᶜ)`, a walk from `u` to `v` has even length if and
only if `u` and `v` lie on the same side of the bipartition. -/
theorem even_length_of_bipartite {α' β' : Type*} {G : Graph α' β'} {X : Set α'}
    (hbip : ∀ e x y, G.IsLink e x y → (x ∈ X ↔ y ∉ X)) {u v : α'}
    (W : GraphWalk G u v) :
    (u ∈ X ↔ v ∈ X) ↔ Even W.length := by
  induction W with
  | nil _ => simp
  | @cons a y b e hl r ih =>
    have h₁ := hbip e a y hl
    rw [GraphWalk.length_cons, Nat.even_add_one, ← ih]
    tauto

/-- Every closed walk `W` of a radial drawing `K` of `H` has even length. -/
theorem even_length_of_preRadial {S : Type w} [TopologicalSpace S] {H K : Drawing S}
    (hrad : (PaintingOrDrawing.drawing H).IsPreRadialDrawing K) {u : S}
    (W : GraphWalk K.toGraph u u) :
    Even W.length :=
  (even_length_of_bipartite (GM11.bipartite_of_preRadial hrad) W).mp Iff.rfl

/-- Every atom `x ∈ H.A` has a corresponding atom `x' ∈ K.A` in a radial drawing `K` of `H`. -/
theorem exists_correspondingAtom {S : Type w} [TopologicalSpace S] {H K : Drawing S}
    (hrad : (PaintingOrDrawing.drawing H).IsPreRadialDrawing K) {x : Set S} (hx : x ∈ H.A) :
    ∃ x' : Set S, IsCorrespondingAtom H K x x' := by
  have hUU : H.U ∩ K.U = H.V := hrad.1
  rcases hx with (⟨v, hv, rfl⟩ | he) | hr
  · exact ⟨{v}, Or.inl (Or.inl ⟨v, hv, rfl⟩), Or.inl (Or.inl ⟨v, hrad.2.1 hv, rfl⟩),
      Or.inl ⟨v, hv, rfl, rfl⟩⟩
  · obtain ⟨y, hy⟩ := he.1
    have hyK : y ∉ K.U := fun h => by
      have : y ∈ H.U ∩ K.U := ⟨(he.2.1 hy).1, h⟩
      rw [hUU] at this
      exact (he.2.1 hy).2 this
    obtain ⟨r', hr', hyr'⟩ := exists_region_of_notMem hyK
    have hdisj : Disjoint x K.U := by
      rw [Set.disjoint_left]
      intro z hz hzK
      have : z ∈ H.U ∩ K.U := ⟨(he.2.1 hz).1, hzK⟩
      rw [hUU] at this
      exact (he.2.1 hz).2 this
    have hsub : x ⊆ r' := subset_region hr' he.2.2.1.isConnected.isPreconnected hdisj hy hyr'
    exact ⟨r', Or.inl (Or.inr he), Or.inr hr', Or.inr (Or.inl ⟨he, hr', hsub⟩)⟩
  · obtain ⟨w, ⟨hwr, hwK⟩, _⟩ := hrad.2.2.1 x hr
    exact ⟨{w}, Or.inr hr, Or.inl (Or.inl ⟨w, hwK, rfl⟩), Or.inr (Or.inr ⟨hr, w, ⟨hwK, hwr⟩, rfl⟩)⟩

/-- The atom `x' ∈ K.A` corresponding to `x ∈ H.A` is unique. -/
theorem correspondingAtom_unique {S : Type w} [TopologicalSpace S] {H K : Drawing S}
    (hrad : (PaintingOrDrawing.drawing H).IsPreRadialDrawing K) {x x₁' x₂' : Set S}
    (h₁ : IsCorrespondingAtom H K x x₁') (h₂ : IsCorrespondingAtom H K x x₂') :
    x₁' = x₂' := by
  rcases h₁.2.2 with ⟨v₁, hv₁, hEq₁, hEq₁'⟩ | ⟨he₁, hr₁', hsub₁⟩ | ⟨hr₁, w₁, hw₁, hEq₁'⟩ <;>
    rcases h₂.2.2 with ⟨v₂, hv₂, hEq₂, hEq₂'⟩ | ⟨he₂, hr₂', hsub₂⟩ | ⟨hr₂, w₂, hw₂, hEq₂'⟩
  · rw [hEq₁', hEq₂', ← singleton_eq_singleton_iff, ← hEq₁, ← hEq₂]
  · subst hEq₁
    exact ((he₂.2.1 (mem_singleton v₁)).2 hv₁).elim
  · subst hEq₁
    exact (region_subset hr₂ (mem_singleton v₁) (H.V_subset_U hv₁)).elim
  · subst hEq₂
    exact ((he₁.2.1 (mem_singleton v₂)).2 hv₂).elim
  · obtain ⟨y, hy⟩ := he₁.1
    exact region_eq_of_mem hr₁' hr₂' (hsub₁ hy) (hsub₂ hy)
  · obtain ⟨y, hy⟩ := he₁.1
    exact (region_subset hr₂ hy (he₁.2.1 hy).1).elim
  · subst hEq₂
    exact (region_subset hr₁ (mem_singleton v₂) (H.V_subset_U hv₂)).elim
  · obtain ⟨y, hy⟩ := he₂.1
    exact (region_subset hr₁ hy (he₂.2.1 hy).1).elim
  · have hw_eq : w₁ = w₂ := (hrad.2.2.1 x hr₁).unique ⟨hw₁.2, hw₁.1⟩ ⟨hw₂.2, hw₂.1⟩
    rw [hEq₁', hEq₂', hw_eq]

/-- For any `x, y : Set S`, `tangleMetric H K ins θ x y ≤ θ`. -/
theorem tangleMetric_le_ord {S : Type w} [TopologicalSpace S] [T1Space S]
    (H K : Drawing S) (ins : Drawing S → Set S) (θ : ℕ) (x y : Set S) :
    tangleMetric H K ins θ x y ≤ θ := by
  classical
  unfold tangleMetric
  split_ifs with hxy hex
  · exact Nat.zero_le θ
  · by_cases hne : {k : ℕ | ∃ (u : S) (W : GraphWalk K.toGraph u u) (x' y' : Set S),
        IsCorrespondingAtom H K x x' ∧ IsCorrespondingAtom H K y y' ∧
        W.length < 2 * θ ∧ W.length = 2 * k ∧ x' ⊆ insWalk ins K W ∧ y' ⊆ insWalk ins K W}.Nonempty
    · obtain ⟨k, hk⟩ := hne
      obtain ⟨_, W', _, _, _, _, hlen', hk', _, _⟩ := id hk
      exact (Nat.sInf_le hk).trans (by omega)
    · rw [Set.not_nonempty_iff_eq_empty.mp hne, Nat.sInf_empty]
      exact Nat.zero_le θ
  · exact le_rfl

/-- If `W` is a closed walk of `K` with `W.length < 2 * θ` such that the corresponding atoms
`x', y'` of `x, y ∈ H.A` satisfy `x' ⊆ insWalk ins K W` and `y' ⊆ insWalk ins K W`, then
`2 * tangleMetric H K ins θ x y ≤ W.length`. -/
theorem two_mul_tangleMetric_le_of_walk {S : Type w} [TopologicalSpace S] [T1Space S]
    {H K : Drawing S} (hrad : (PaintingOrDrawing.drawing H).IsPreRadialDrawing K)
    (ins : Drawing S → Set S) (θ : ℕ) {x y x' y' : Set S}
    (hx' : IsCorrespondingAtom H K x x') (hy' : IsCorrespondingAtom H K y y')
    {u : S} (W : GraphWalk K.toGraph u u) (hlen : W.length < 2 * θ)
    (hxW : x' ⊆ insWalk ins K W) (hyW : y' ⊆ insWalk ins K W) :
    2 * tangleMetric H K ins θ x y ≤ W.length := by
  classical
  unfold tangleMetric
  split_ifs with hxy hex
  · exact Nat.zero_le _
  · obtain ⟨k, hk⟩ := even_length_of_preRadial hrad W
    have hmem : k ∈ {k : ℕ | ∃ (u : S) (W : GraphWalk K.toGraph u u) (x' y' : Set S),
        IsCorrespondingAtom H K x x' ∧ IsCorrespondingAtom H K y y' ∧
        W.length < 2 * θ ∧ W.length = 2 * k ∧ x' ⊆ insWalk ins K W ∧ y' ⊆ insWalk ins K W} :=
      ⟨u, W, x', y', hx', hy', hlen, by omega, hxW, hyW⟩
    have hle := Nat.sInf_le hmem
    omega
  · exact (hex ⟨u, W, x', y', hx', hy', hlen, hxW, hyW⟩).elim

/-- If `x ≠ y` and `tangleMetric H K ins θ x y < θ`, then there is a closed walk `W` of `K` of
length `2 * tangleMetric H K ins θ x y` whose `insWalk` contains the corresponding atoms of `x` and
`y`. -/
theorem exists_walk_of_tangleMetric_lt {S : Type w} [TopologicalSpace S] [T1Space S]
    {H K : Drawing S} (hrad : (PaintingOrDrawing.drawing H).IsPreRadialDrawing K)
    (ins : Drawing S → Set S) {θ : ℕ} {x y : Set S} (hne : x ≠ y)
    (hlt : tangleMetric H K ins θ x y < θ) :
    ∃ (u : S) (W : GraphWalk K.toGraph u u) (x' y' : Set S),
      IsCorrespondingAtom H K x x' ∧ IsCorrespondingAtom H K y y' ∧
      W.length < 2 * θ ∧ W.length = 2 * tangleMetric H K ins θ x y ∧
      x' ⊆ insWalk ins K W ∧ y' ⊆ insWalk ins K W := by
  classical
  have hlt' := hlt
  unfold tangleMetric at hlt'
  split_ifs at hlt' with hxy hex
  · exact (hne hxy).elim
  · rcases hex with ⟨u₀, W₀, x₀', y₀', hx₀', hy₀', hlen₀, hxW₀, hyW₀⟩
    obtain ⟨k₀, hk₀⟩ := even_length_of_preRadial hrad W₀
    have hSne : {k : ℕ | ∃ (u : S) (W : GraphWalk K.toGraph u u) (x' y' : Set S),
        IsCorrespondingAtom H K x x' ∧ IsCorrespondingAtom H K y y' ∧
        W.length < 2 * θ ∧ W.length = 2 * k ∧ x' ⊆ insWalk ins K W ∧ y' ⊆ insWalk ins K W}.Nonempty
          :=
      ⟨k₀, u₀, W₀, x₀', y₀', hx₀', hy₀', hlen₀, by omega, hxW₀, hyW₀⟩
    obtain ⟨u, W, x', y', hx', hy', hlen, hk, hxW, hyW⟩ := Nat.sInf_mem hSne
    have heq : tangleMetric H K ins θ x y = sInf {k : ℕ | ∃ (u : S) (W : GraphWalk K.toGraph u u)
        (x' y' : Set S), IsCorrespondingAtom H K x x' ∧ IsCorrespondingAtom H K y y' ∧
        W.length < 2 * θ ∧ W.length = 2 * k ∧ x' ⊆ insWalk ins K W ∧ y' ⊆ insWalk ins K W} := by
      unfold tangleMetric
      split_ifs with hex'
      · rfl
      · exact (hex' ⟨u₀, W₀, x₀', y₀', hx₀', hy₀', hlen₀, hxW₀, hyW₀⟩).elim
    exact ⟨u, W, x', y', hx', hy', hlen, heq ▸ hk, hxW, hyW⟩
  · exact (lt_irrefl θ hlt').elim

/-- Dual of `GM11.two_mul_count_le`: in a bipartite walk, at most half the steps visit `X`. -/
theorem two_mul_countP_le_of_bipartite {S : Type w} [TopologicalSpace S]
    {G : Drawing S} (X : Set S) [DecidablePred (· ∈ X)]
    (hb : ∀ e x y, G.toGraph.IsLink e x y → (x ∈ X ↔ y ∉ X)) {u v : S}
    (W : GraphWalk G.toGraph u v) :
    2 * (W.support.tail.countP (· ∈ X)) + (if u ∈ X then 1 else 0) ≤
      W.length + (if v ∈ X then 1 else 0) := by
  induction W with
  | nil _ => simp [GraphWalk.length, GraphWalk.support]
  | @cons a y b e hl r ih =>
    have h₁ := hb e a y hl
    have hsup : (GraphWalk.cons hl r).support.tail = r.support := rfl
    have hsup₂ : r.support = y :: r.support.tail := r.support_eq_cons
    have hlen : (GraphWalk.cons hl r).length = r.length + 1 := rfl
    rw [hsup, hlen, hsup₂, List.countP_cons]
    by_cases hy : y ∈ X
    · have ha : a ∉ X := fun h => (h₁.mp h) hy
      simp only [hy, ha, ite_true, ite_false, decide_true] at ih ⊢
      omega
    · have ha : a ∈ X := h₁.mpr hy
      simp only [hy, ha, ite_true, ite_false, decide_false, Bool.false_eq_true] at ih ⊢
      omega

/-- Every circuit `C` of a radial drawing `K` of `H` has `IsOArc C.U`, `2 ≤ C.length`, and
`2 * (C.U ∩ H.V).ncard ≤ C.length`. -/
theorem circuit_props_of_preRadial {S : Type w} [TopologicalSpace S] [T2Space S]
    {H K C : Drawing S} (hrad : (PaintingOrDrawing.drawing H).IsPreRadialDrawing K)
    (hC : C.IsCircuit) (hCs : C.IsSubdrawing K) :
    IsOArc C.U ∧ 2 ≤ C.length ∧ 2 * (C.U ∩ H.V).ncard ≤ C.length := by
  classical
  have hbip := GM11.bipartite_of_preRadial hrad
  have hbC : ∀ e x y, C.toGraph.IsLink e x y → (x ∈ H.V ↔ y ∉ H.V) := by
    intro e x y hl
    refine hbip e x y ⟨hCs.2 hl.1, hCs.1 hl.2.1, hCs.1 hl.2.2.1, ?_⟩
    rw [← hCs.closure_inter_V hl.1]
    exact hl.2.2.2
  obtain ⟨u, W, ⟨hnd, hed⟩, hpos, hCV, hCE⟩ := id hC
  have hlen : C.length = W.length := by
    rw [Drawing.length, hCE]
    have h : {e | e ∈ W.edges} = (W.edges.toFinset : Set (Set S)) := by ext; simp
    rw [h, ncard_coe_finset, List.toFinset_card_of_nodup hed]
    rfl
  have heven : Even W.length := (even_length_of_bipartite hbC W).mp Iff.rfl
  have h2le : 2 ≤ C.length := by
    rcases heven with ⟨k, hk⟩
    omega
  have hc := two_mul_countP_le_of_bipartite H.V hbC W
  have hU_sub : C.U ∩ H.V ⊆ ((W.support.tail.filter (· ∈ H.V)).toFinset : Set S) := by
    rintro x ⟨hxU, hxV⟩
    have hxCV : x ∈ C.V := by
      by_contra hxCV
      obtain ⟨e, he, hxe⟩ := C.exists_edge_of_mem hxU hxCV
      exact ((hCs.2 he).2.1 hxe).2 (hrad.2.1 hxV)
    rw [hCV] at hxCV
    have hxtail : x ∈ W.support.tail := by
      cases W with
      | nil _ => simp at hpos
      | cons hl r =>
        rcases List.mem_cons.mp hxCV with rfl | hx'
        · exact r.end_mem_support
        · exact hx'
    simpa using ⟨hxtail, hxV⟩
  have hcard : (C.U ∩ H.V).ncard ≤ W.support.tail.countP (· ∈ H.V) := by
    have hf : (W.support.tail.filter (· ∈ H.V)).Nodup := hnd.filter _
    have hle := ncard_le_ncard hU_sub (Finset.finite_toSet _)
    rw [ncard_coe_finset, List.toFinset_card_of_nodup hf, ← List.countP_eq_length_filter] at hle
    exact hle
  have hcard2 : 2 * (C.U ∩ H.V).ncard ≤ C.length := by omega
  have hoarc : IsOArc C.U := by
    cases W with
    | nil _ => simp at hpos
    | @cons u v _ e hl r =>
      have huv : u ≠ v := by
        intro hEq
        subst hEq
        by_cases hu : u ∈ H.V
        · exact (hbC e u u hl).mp hu hu
        · exact hu ((hbC e u u hl).mpr hu)
      obtain ⟨P, Q, hP, hQ, hPs, hQs, _, _, hPQV, hdisjE, hsup⟩ :=
        Drawing.IsCircuit.exists_two_paths hC hl.2.1 hl.2.2.1 huv
      have hsupU : (C.sup P Q).U = P.U ∪ Q.U := by
        rw [Drawing.U_eq, Drawing.sup_V hPs hQs, Drawing.sup_E hPs hQs, P.U_eq, Q.U_eq,
          biUnion_union]
        ext x; simp only [mem_union]; tauto
      rw [← hsup, hsupU]
      refine GM11.isOArc_union (GM11.isLine_of_isPathBetween hP huv)
        (GM11.isLine_of_isPathBetween hQ huv) ?_
      rw [GM11.U_inter_of_disjoint hPs hQs hdisjE, hPQV]
  exact ⟨hoarc, h2le, hcard2⟩

/-- Every respectful tangle `T` of order `θ` in a 2-cell drawing `H` has a derived slope `ins` in
any radial drawing `K` of `H`. -/
theorem exists_derivedSlope {S : Type w} [TopologicalSpace S] [T2Space S]
    {H K : Drawing S} {θ : ℕ} {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hResp : IsRespectfulDrawingTangle H θ T)
    (hrad : (PaintingOrDrawing.drawing H).IsPreRadialDrawing K) :
    ∃ ins : Drawing S → Set S, IsDerivedSlope (PaintingOrDrawing.drawing H) K θ T ins := by
  classical
  have hUU : H.U ∩ K.U = H.V := hrad.1
  have hex : ∀ C : Drawing S, C.IsCircuit → C.IsSubdrawing K → C.length < 2 * θ →
      ∃ Δ : Set S, IsClosedDisc Δ ∧ subBd Δ = C.U ∧
        ((PaintingOrDrawing.drawing H).inter Δ, (PaintingOrDrawing.drawing H).interOutside Δ) ∈ T
          := by
    intro C hC hCs hlen
    obtain ⟨hoarc, _, hcard2⟩ := circuit_props_of_preRadial hrad hC hCs
    have hnorm : (PaintingOrDrawing.drawing H).IsNormal C.U := by
      rintro x ⟨hxC, hxH⟩
      have : x ∈ H.U ∩ K.U := ⟨hxH, hCs.U_subset hxC⟩
      rwa [hUU] at this
    refine hResp.2.2.2 C.U hoarc hnorm ?_
    change (C.U ∩ H.V).ncard < θ
    omega
  refine ⟨fun C => if h : C.IsCircuit ∧ C.IsSubdrawing K ∧ C.length < 2 * θ then
    (hex C h.1 h.2.1 h.2.2).choose else ∅, fun C hC hCs hlen => ?_⟩
  have h : C.IsCircuit ∧ C.IsSubdrawing K ∧ C.length < 2 * θ := ⟨hC, hCs, hlen⟩
  simp only [h]
  exact (hex C hC hCs hlen).choose_spec

/-- Every respectful tangle `T` of order `θ` in a 2-cell drawing `H` in a closed surface `S` has a
tangle metric `d` (`HasTangleMetric H θ T d`). -/
theorem exists_hasTangleMetric {S : Type w} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) {H : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hResp : IsRespectfulDrawingTangle H θ T) :
    ∃ d : Set S → Set S → ℕ, HasTangleMetric H θ T d := by
  obtain ⟨K, hK⟩ := GM11.exists_radialDrawing hS hResp.1
  obtain ⟨ins, hins⟩ := exists_derivedSlope hResp hK.2.1
  exact ⟨tangleMetric H K ins θ, hResp, K, ins, hK, hins, fun _ _ _ _ => rfl⟩

/-- If `H₁` is a 2-cell drawing in a closed surface `S` with `H₁.E = ∅`, then `H₁.V.ncard ≤ 1`. -/
theorem ncard_V_le_one_of_E_empty {S : Type w} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {H₁ : Drawing S} (h2cell : (PaintingOrDrawing.drawing H₁).IsTwoCell)
    (hE : H₁.E = ∅) : H₁.V.ncard ≤ 1 :=
  GM12.ncard_V_le_one_of_E_empty hS h2cell hE

/-- Every edge of a drawing has at least one endpoint in `V`. -/
theorem edge_closure_inter_V_nonempty {S : Type w} [TopologicalSpace S]
    {H : Drawing S} {e : Set S} (he : e ∈ H.E) : (closure e ∩ H.V).Nonempty := by
  rcases H.edge_cond e he with ⟨u, v, _, hcl, _⟩ | ⟨u, hcl, _⟩
  · exact ⟨u, by rw [hcl]; simp⟩
  · exact ⟨u, by rw [hcl]; simp⟩

/-- Graph Minors XI, (9.1), proved from `GM11.gm15_theorem_9_1` and `Surface.epstein`. -/
theorem gm11_theorem_9_1 : GM11Theorem91Statement.{w} :=
  GM11.gm15_theorem_9_1

/-- Graph Minors XIV, (7.3), proved from `GM14.theorem_7_3_proof`, `GM11.gm14_theorem_8_12`,
`GM11.gm19_theorem_8_5`, `gm11_theorem_9_1`, and `Surface.epstein`. -/
theorem gm14_theorem_7_3 : GM14Theorem73Statement.{w} :=
  GM14.theorem_7_3_proof

/-- Graph Minors XII, (1.2), from the established `GM12.theorem_1_2_proof`. -/
theorem gm12_theorem_1_2 : GM12Theorem12Statement.{w} :=
  fun _ _ _ _ _ hS _ _ hMetric hE hc =>
    GM12.theorem_1_2_proof hS hMetric hE hc

/-- A 2-cell drawing in a closed surface with a respectful tangle of order `θ ≥ 2` has at least one
edge. -/
theorem edges_nonempty_of_tangle {S : Type w} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) {H : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hT : IsRespectfulDrawingTangle H θ T) (hθ : 2 ≤ θ) : H.E.Nonempty := by
  have : ConnectedSpace S := hT.1.1
  by_contra hE
  have hV := ncard_V_le_one_of_E_empty hS hT.1 (Set.not_nonempty_iff_eq_empty.mp hE)
  have hord : θ ≤ H.V.ncard := hT.2.1.order_le_ncard_vertexSet
  omega

/-- A 2-cell drawing in a closed surface with a respectful tangle of order `θ ≥ 3` has at least two
edges. -/
theorem two_le_ncard_edges_of_tangle {S : Type w} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) {H : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hT : IsRespectfulDrawingTangle H θ T) (hθ : 3 ≤ θ) : 2 ≤ H.E.ncard := by
  have : ConnectedSpace S := hT.1.1
  have hE : H.E.Nonempty := edges_nonempty_of_tangle hS hT (by omega)
  obtain ⟨e₀, he₀⟩ := id hE
  by_contra hlt
  have heq : ∀ e ∈ H.E, e = e₀ := fun e he => by
    by_contra hne
    exact hlt ((Set.one_lt_ncard_iff H.finite_edges).mpr ⟨e, e₀, he, he₀, hne⟩)
  obtain ⟨K, hK⟩ := GM11.exists_radialDrawing hS hT.1
  have hrf : GM11.RegionFacts (PaintingOrDrawing.drawing H) K :=
    GM11.regionFacts_of_radial ⟨hK.1, hK.2.1⟩ hS hK.2.2 hE
  have hV_sub : H.V ⊆ closure e₀ ∩ H.V := fun v hv => by
    obtain ⟨e, he, hve⟩ := GM11.exists_edge_of_regionFacts hS hrf hv
    exact ⟨heq e he ▸ hve, hv⟩
  have hcl_le : (closure e₀ ∩ H.V).ncard ≤ 2 := by
    rcases H.edge_cond e₀ he₀ with ⟨u, v, _, hcl, _⟩ | ⟨u, hcl, _⟩
    · rw [hcl]
      exact (Set.ncard_insert_le u {v}).trans (by simp)
    · rw [hcl]
      simp
  have hV_le : H.V.ncard ≤ 2 :=
    (Set.ncard_le_ncard hV_sub (H.finite_V.subset inter_subset_right)).trans hcl_le
  have hord : θ ≤ H.V.ncard := hT.2.1.order_le_ncard_vertexSet
  omega

/-- For any 2-cell drawing `H` in a closed surface `S` with a respectful tangle `T` of order `θ ≥ 2`
with metric `d`, and any atom `z ∈ H.A`, there exists an atom `b ∈ H.A` with `d z b = θ`
(Graph Minors XV, proof of (4.1), page 125, applying Graph Minors XI, (8.12)). -/
theorem exists_atom_dist_eq_theta {S : Type w} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) {H : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} (hMetric : HasTangleMetric H θ T d) (hθ : 2 ≤ θ)
    {z : Set S} (hz : z ∈ H.A) :
    ∃ b ∈ H.A, d z b = θ := by
  have hConn : ConnectedSpace S := hMetric.1.1.1
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have hE : H.E.Nonempty := edges_nonempty_of_tangle hS hMetric.1 hθ
  obtain ⟨hResp, K, ins, hK, hd, hd_eq⟩ := hMetric
  have hsl : IsSlope K (2 * θ) ins :=
    GM11.isSlope_of_derived (Γ := PaintingOrDrawing.drawing H) hS
      ⟨hResp.2.1.one_le, hResp.2.1.isSeparation, hResp.2.1.order_lt,
        hResp.2.1.axiom1, hResp.2.1.axiom2⟩ hK.2.1.1 hd
  have hrf := GM11.regionFacts_of_radial ⟨hK.1, hK.2.1⟩ hS hK.2.2 hE
  obtain ⟨z', hz'⟩ := exists_correspondingAtom hK.2.1 hz
  obtain ⟨c, hc⟩ := atom_nonempty hz'.2.1
  obtain ⟨r₁, hr₁, hno₁⟩ := GM11.gm14_theorem_8_12 S hS hConn K (2 * θ) ins hsl c
  obtain ⟨e₁, he₁, he₁r₁⟩ := hrf.1 r₁ hr₁
  have he₁A : e₁ ∈ H.A := Or.inl (Or.inr he₁)
  have he₁_corr : IsCorrespondingAtom H K e₁ r₁ :=
    ⟨he₁A, Or.inr hr₁, Or.inr (Or.inl ⟨he₁, hr₁, he₁r₁⟩)⟩
  by_cases he₁z : e₁ = z
  · subst he₁z
    obtain ⟨u₀, hu₀⟩ := edge_closure_inter_V_nonempty he₁
    have hu₀A : ({u₀} : Set S) ∈ H.A := Or.inl (Or.inl ⟨u₀, hu₀.2, rfl⟩)
    have hu₀_ne : ({u₀} : Set S) ≠ e₁ := fun h =>
      (he₁.2.1 (h ▸ mem_singleton u₀)).2 hu₀.2
    have hz'_eq_r₁ : z' = r₁ := correspondingAtom_unique hK.2.1 hz' he₁_corr
    refine ⟨{u₀}, hu₀A, ?_⟩
    rw [hd_eq e₁ hz {u₀} hu₀A]
    unfold tangleMetric
    split_ifs with h1 h2
    · exact (hu₀_ne h1.symm).elim
    · exfalso
      obtain ⟨u, W, z₁', _, hz₁', _, hW, hzW, _⟩ := h2
      have hz₁_eq : z₁' = r₁ := (correspondingAtom_unique hK.2.1 hz₁' hz').trans hz'_eq_r₁
      subst hz₁_eq
      have hrest := (GM11.gm19_theorem_8_5 S hS hConn K (2 * θ) ins hsl u W hW).1
      exact hno₁ (insWalk ins K W) hrest ⟨hzW (hz'_eq_r₁ ▸ hc), hzW⟩
    · rfl
  · refine ⟨e₁, he₁A, ?_⟩
    rw [hd_eq z hz e₁ he₁A]
    unfold tangleMetric
    split_ifs with h1 h2
    · exact (he₁z h1.symm).elim
    · exfalso
      obtain ⟨u, W, z₁', r₁', hz₁', hr₁', hW, hzW, hrW⟩ := h2
      have hz₁_eq : z₁' = z' := correspondingAtom_unique hK.2.1 hz₁' hz'
      have hr₁_eq : r₁' = r₁ := correspondingAtom_unique hK.2.1 hr₁' he₁_corr
      subst hz₁_eq hr₁_eq
      have hrest := (GM11.gm19_theorem_8_5 S hS hConn K (2 * θ) ins hsl u W hW).1
      exact hno₁ (insWalk ins K W) hrest ⟨hzW hc, hrW⟩
    · rfl

/-- Every vertex `x ∈ H.V` in the closure of an atom `a ∈ H.A` has `d {x} a ≤ 2`. -/
theorem vertex_atom_dist_le_two
    {S : Type w} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) {H : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} (hm : HasTangleMetric H θ T d) :
    ∀ x ∈ H.V, ∀ a ∈ H.A, x ∈ closure a → d {x} a ≤ 2 := by
  obtain ⟨_, hs, hb, _, _, hr, he⟩ := gm11_theorem_9_1 H θ T d hS hm.1.1.1 hm
  intro x hx a ha hxa
  have hxA : ({x} : Set S) ∈ H.A := Or.inl (Or.inl ⟨x, hx, rfl⟩)
  by_cases hθ : θ ≤ 2
  · exact (hb _ hxA _ ha).trans hθ
  rcases ha with (⟨y, hy, rfl⟩ | ha) | ha
  · have hxy : x = y := by simpa only [closure_singleton, mem_singleton_iff] using hxa
    subst y
    exact (hs _ hxA).le.trans (Nat.zero_le _)
  · exact he x hx a ha hxa
  · exact (hr (edges_nonempty_of_tangle hS hm.1 (by omega)) x hx a ha hxa).trans (by omega)

/-- Any two atoms `a, b ∈ H.A` with `(a ∩ closure b).Nonempty` have `d a b ≤ 3`. -/
theorem atom_closure_dist_le_three
    {S : Type w} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) {H : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} (hm : HasTangleMetric H θ T d) :
    ∀ a ∈ H.A, ∀ b ∈ H.A, (a ∩ closure b).Nonempty → d a b ≤ 3 := by
  have : ConnectedSpace S := hm.1.1.1
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  obtain ⟨_, hs, _, hsym, htri, hr, he⟩ := gm11_theorem_9_1 H θ T d hS hm.1.1.1 hm
  have hv2 := vertex_atom_dist_le_two hS hm
  intro a ha b hb ⟨y, hya, hyb⟩
  by_cases hab : a = b
  · subst hab
    exact (hs a ha).le.trans (Nat.zero_le _)
  rcases ha with (⟨v, hv, rfl⟩ | haE) | haR
  · rw [mem_singleton_iff] at hya
    subst hya
    exact (hv2 y hv b hb hyb).trans (by omega)
  · rcases hb with (⟨w, hw, rfl⟩ | hbE) | hbR
    · rw [closure_singleton, mem_singleton_iff] at hyb
      subst hyb
      exact ((haE.2.1 hya).2 hw).elim
    · have hyb' : y ∈ b := H.closure_diff_V hbE ▸ ⟨hyb, (haE.2.1 hya).2⟩
      exact (hab (H.edge_eq_of_mem haE hbE hya hyb')).elim
    · have he_sub : a ⊆ closure b :=
        GM11.edge_subset_closure_of_incident hS haE hbR ⟨y, hya, hyb⟩
      obtain ⟨v, hve, hvV⟩ := edge_closure_inter_V_nonempty haE
      have hvb : v ∈ closure b := closure_minimal he_sub isClosed_closure hve
      have hvA : ({v} : Set S) ∈ H.A := Or.inl (Or.inl ⟨v, hvV, rfl⟩)
      have h1 : d {v} a ≤ 2 := he v hvV a haE hve
      have h2 : d {v} b ≤ 1 := hr ⟨a, haE⟩ v hvV b hbR hvb
      have h3 := htri a (Or.inl (Or.inr haE)) {v} hvA b (Or.inr hbR)
      have h4 := hsym {v} hvA a (Or.inl (Or.inr haE))
      omega
  · obtain ⟨z, hzr, hzb⟩ := mem_closure_iff.mp hyb a (region_isOpen haR) hya
    exact (hab (atom_eq_of_mem (Or.inr haR) hb hzr hzb)).elim

/-! ## Section 4 Statements and Proofs -/

/-- Statement of Graph Minors XV, (4.1) (pages 124–125):
"Let $\mathcal{T}$ be a respectful tangle of order $\theta$ in a 2-cell drawing $H$ in a surface
$\Sigma$. Let $H_1, H_2$ be 2-cell drawings in $\Sigma$, and for $i = 1, 2$ let $\mathcal{T}_i$ be a
$\lambda_i$-compression of $\mathcal{T}$ in $H_i$. Let $H_1, H_2$ have radial drawings $K_1, K_2$.
Then ... for every $W$ which is a closed walk of a common subdrawing of $K_1$ and $K_2$, if
$ins_1(W)$,
$ins_2(W)$ are both defined then they are equal. In particular, if $H_1 = H_2$ and
$\lambda_1 \ge \lambda_2$, then $\mathcal{T}_1 \subseteq \mathcal{T}_2$." -/
def GM15Theorem41Statement : Prop :=
  ∀ {S : Type w} [TopologicalSpace S] [T2Space S]
    (H H₁ H₂ K₁ K₂ : Drawing S) (θ lam₁ lam₂ : ℕ)
    (T T₁ T₂ : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (d d₁ d₂ : Set S → Set S → ℕ) (ins₁ ins₂ : Drawing S → Set S),
    IsClosedSurface S →
    IsLambdaCompression H H₁ θ lam₁ T T₁ d d₁ →
    IsLambdaCompression H H₂ θ lam₂ T T₂ d d₂ →
    (PaintingOrDrawing.drawing H₁).IsRadialDrawing K₁ →
    IsDerivedSlope (PaintingOrDrawing.drawing H₁) K₁ (θ - lam₁) T₁ ins₁ →
    (∀ x ∈ H₁.A, ∀ y ∈ H₁.A, d₁ x y = tangleMetric H₁ K₁ ins₁ (θ - lam₁) x y) →
    (PaintingOrDrawing.drawing H₂).IsRadialDrawing K₂ →
    IsDerivedSlope (PaintingOrDrawing.drawing H₂) K₂ (θ - lam₂) T₂ ins₂ →
    (∀ x ∈ H₂.A, ∀ y ∈ H₂.A, d₂ x y = tangleMetric H₂ K₂ ins₂ (θ - lam₂) x y) →
    (∀ (u₁ u₂ : S) (W₁ : GraphWalk K₁.toGraph u₁ u₁) (W₂ : GraphWalk K₂.toGraph u₂ u₂),
      walkDrawing K₁ W₁ = walkDrawing K₂ W₂ →
      W₁.length < 2 * (θ - lam₁) → W₂.length < 2 * (θ - lam₂) →
      insWalk ins₁ K₁ W₁ = insWalk ins₂ K₂ W₂) ∧
    (H₁ = H₂ → K₁ = K₂ → lam₂ ≤ lam₁ → T₁ ⊆ T₂)

/-- **Graph Minors XV, (4.1)** (pages 124–125):
Slope agreement for compressions `T₁, T₂` of `T`, and `T₁ ⊆ T₂` when `H₁ = H₂` and `λ₁ ≥ λ₂`.
Proved from Graph Minors XI, (8.12) (`exists_atom_dist_eq_theta`). -/
theorem theorem_4_1_proof :
    GM15Theorem41Statement.{w} := by
  intro S _ _ H H₁ H₂ K₁ K₂ θ lam₁ lam₂ T T₁ T₂ d d₁ d₂ ins₁ ins₂
    hS hComp₁ hComp₂ hK₁ hins₁ hd₁ hK₂ hins₂ hd₂
  have hConn : ConnectedSpace S := hComp₁.hasMetric.1.1.1
  have hCircEq : ∀ C : Drawing S, C.IsCircuit → C.IsSubdrawing K₁ → C.IsSubdrawing K₂ →
      C.length < 2 * (θ - lam₁) → C.length < 2 * (θ - lam₂) → ins₁ C = ins₂ C := by
    intro C hC hCs₁ hCs₂ hlen₁ hlen₂
    obtain ⟨_, h2le, _⟩ := circuit_props_of_preRadial hK₁.2.1 hC hCs₁
    have hθ2 : 2 ≤ θ := by omega
    obtain ⟨v, W_C, ⟨hnd, hed⟩, hpos, hCV, hCE⟩ := id hC
    have hvC : v ∈ C.V := by rw [hCV]; exact W_C.start_mem_support
    have hvU : v ∈ C.U := C.V_subset_U hvC
    obtain ⟨a_v, ha_v, hv_av⟩ := exists_atom_of_point H v
    obtain ⟨b_v, hb_v, hd_eq⟩ := exists_atom_dist_eq_theta hS hComp₁.hasMetric hθ2 ha_v
    obtain ⟨σ, hσb⟩ := atom_nonempty hb_v
    have hpt : pointDist H d v σ = θ := by
      rw [pointDist_eq_of_mem_atom ha_v hb_v hv_av hσb, hd_eq]
    have hlen_WC : W_C.length = C.length := by
      rw [Drawing.length, hCE]
      have h : {f | f ∈ W_C.edges} = (W_C.edges.toFinset : Set (Set S)) := by ext; simp
      rw [h, ncard_coe_finset, List.toFinset_card_of_nodup hed]
      rfl
    have hnot_mem : ∀ (Hᵢ Kᵢ : Drawing S) (lamᵢ : ℕ)
        (Tᵢ : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
        (dᵢ : Set S → Set S → ℕ) (insᵢ : Drawing S → Set S),
        IsLambdaCompression H Hᵢ θ lamᵢ T Tᵢ d dᵢ →
        (PaintingOrDrawing.drawing Hᵢ).IsRadialDrawing Kᵢ →
        IsDerivedSlope (PaintingOrDrawing.drawing Hᵢ) Kᵢ (θ - lamᵢ) Tᵢ insᵢ →
        (∀ x ∈ Hᵢ.A, ∀ y ∈ Hᵢ.A, dᵢ x y = tangleMetric Hᵢ Kᵢ insᵢ (θ - lamᵢ) x y) →
        C.IsSubdrawing Kᵢ → C.length < 2 * (θ - lamᵢ) → σ ∉ insᵢ C := by
      intro Hᵢ Kᵢ lamᵢ Tᵢ dᵢ insᵢ hCompᵢ hKᵢ hinsᵢ hdᵢ hCsᵢ hlenᵢ hσ_in
      obtain ⟨Wᵢ, hsupᵢ, hedᵢ⟩ := hCsᵢ.exists_walk_up W_C
      have hlenᵢ' : Wᵢ.length < 2 * (θ - lamᵢ) := by
        have : Wᵢ.length = W_C.length := by simp [GraphWalk.length, hedᵢ]
        omega
      have hWD : walkDrawing Kᵢ Wᵢ = C := by
        apply Drawing.ext_of_V_E
        · rw [GM11.walkDrawing_V, hsupᵢ, hCV]
        · rw [GM11.walkDrawing_E, hedᵢ, hCE]
      have hv_insW : v ∈ insWalk insᵢ Kᵢ Wᵢ := by
        change v ∈ insOf insᵢ (walkDrawing Kᵢ Wᵢ)
        rw [hWD]
        exact Or.inl hvU
      have hσ_insW : σ ∈ insWalk insᵢ Kᵢ Wᵢ := by
        change σ ∈ insOf insᵢ (walkDrawing Kᵢ Wᵢ)
        rw [hWD]
        exact Or.inr (mem_iUnion₂.mpr ⟨C, ⟨hC, Drawing.IsSubdrawing.refl C⟩, hσ_in⟩)
      obtain ⟨aᵢ, haᵢ, hv_aᵢ⟩ := exists_atom_of_point Hᵢ v
      obtain ⟨bᵢ, hbᵢ, hσ_bᵢ⟩ := exists_atom_of_point Hᵢ σ
      obtain ⟨aᵢ', haᵢ'⟩ := exists_correspondingAtom hKᵢ.2.1 haᵢ
      obtain ⟨bᵢ', hbᵢ'⟩ := exists_correspondingAtom hKᵢ.2.1 hbᵢ
      have haᵢ_sub : aᵢ' ⊆ insWalk insᵢ Kᵢ Wᵢ :=
        (GM14.theorem_3_1_proof hS hKᵢ hinsᵢ haᵢ' Wᵢ hlenᵢ').mpr ⟨v, hv_aᵢ, hv_insW⟩
      have hbᵢ_sub : bᵢ' ⊆ insWalk insᵢ Kᵢ Wᵢ :=
        (GM14.theorem_3_1_proof hS hKᵢ hinsᵢ hbᵢ' Wᵢ hlenᵢ').mpr ⟨σ, hσ_bᵢ, hσ_insW⟩
      have hle2 := two_mul_tangleMetric_le_of_walk hKᵢ.2.1 insᵢ (θ - lamᵢ) haᵢ' hbᵢ' Wᵢ hlenᵢ'
        haᵢ_sub hbᵢ_sub
      rw [← hdᵢ aᵢ haᵢ bᵢ hbᵢ, ← pointDist_eq_of_mem_atom (d := dᵢ) haᵢ hbᵢ hv_aᵢ hσ_bᵢ] at hle2
      have hge := hCompᵢ.dist_le v σ
      rw [hpt] at hge
      omega
    have hσ₁ := hnot_mem H₁ K₁ lam₁ T₁ d₁ ins₁ hComp₁ hK₁ hins₁ hd₁ hCs₁ hlen₁
    have hσ₂ := hnot_mem H₂ K₂ lam₂ T₂ d₂ ins₂ hComp₂ hK₂ hins₂ hd₂ hCs₂ hlen₂
    obtain ⟨hD₁, hbd₁, _⟩ := hins₁ C hC hCs₁ hlen₁
    obtain ⟨hD₂, hbd₂, _⟩ := hins₂ C hC hCs₂ hlen₂
    by_contra hne
    have hdb : discBd (ins₁ C) = discBd (ins₂ C) := by
      rw [← GM11.IsClosedDisc.frontier_eq_discBd hS hD₁,
        ← GM11.IsClosedDisc.frontier_eq_discBd hS hD₂,
        GM11.subBd_eq_frontier', GM11.subBd_eq_frontier', hbd₁, hbd₂]
    have hcov := GM11.cover_of_discBd_eq hS hD₁ hD₂ hdb hne
    rcases (hcov ▸ mem_univ σ : σ ∈ ins₁ C ∪ ins₂ C) with h | h
    · exact hσ₁ h
    · exact hσ₂ h
  refine ⟨fun u₁ u₂ W₁ W₂ hWD hlen₁ hlen₂ => ?_, fun hH hK hlam => ?_⟩
  · unfold insWalk
    rw [hWD]
    ext x
    simp only [insOf, mem_union, mem_iUnion, exists_prop]
    refine or_congr Iff.rfl (exists_congr fun C => and_congr_right fun ⟨hC, hCs₂⟩ => ?_)
    have hCs₁ : C.IsSubdrawing (walkDrawing K₁ W₁) := hWD.symm ▸ hCs₂
    have hSub₁ : C.IsSubdrawing K₁ := hCs₁.trans (GM11.walkDrawing_isSubdrawing K₁ W₁)
    have hSub₂ : C.IsSubdrawing K₂ := hCs₂.trans (GM11.walkDrawing_isSubdrawing K₂ W₂)
    have hClen : ∀ {K : Drawing S} {u : S} (W : GraphWalk K.toGraph u u),
        C.IsSubdrawing (walkDrawing K W) → C.length ≤ W.length := by
      intro K u W hCs
      have hsub : C.E ⊆ {e | e ∈ W.edges} := by
        have := hCs.2
        rwa [GM11.walkDrawing_E] at this
      calc C.E.ncard ≤ ({e | e ∈ W.edges} : Set (Set S)).ncard :=
            Set.ncard_le_ncard hsub (List.finite_toSet _)
        _ ≤ W.edges.length := by
            rw [show ({e | e ∈ W.edges} : Set (Set S)) = ↑W.edges.toFinset by ext; simp,
              Set.ncard_coe_finset]
            exact List.toFinset_card_le _
        _ = W.length := rfl
    have hC₁ : C.length < 2 * (θ - lam₁) := lt_of_le_of_lt (hClen W₁ hCs₁) hlen₁
    have hC₂ : C.length < 2 * (θ - lam₂) := lt_of_le_of_lt (hClen W₂ hCs₂) hlen₂
    rw [hCircEq C hC hSub₁ hSub₂ hC₁ hC₂]
  · subst hH; subst hK
    have hT₁ : IsTangle H₁.toHypergraph (θ - lam₁) T₁ := hComp₁.hasMetric'.1.2.1
    have hT₂ : IsTangle H₁.toHypergraph (θ - lam₂) T₂ := hComp₂.hasMetric'.1.2.1
    have hPre₁ : IsPretangle (PaintingOrDrawing.drawing H₁).toHypergraph (θ - lam₁) T₁ :=
      ⟨hT₁.one_le, hT₁.isSeparation, hT₁.order_lt, hT₁.axiom1, hT₁.axiom2⟩
    have hPre₂ : IsPretangle (PaintingOrDrawing.drawing H₁).toHypergraph (θ - lam₂) T₂ :=
      ⟨hT₂.one_le, hT₂.isSeparation, hT₂.order_lt, hT₂.axiom1, hT₂.axiom2⟩
    by_cases hE : H₁.E.Nonempty
    · have hf : GM11.RegionFacts (PaintingOrDrawing.drawing H₁) K₁ :=
        GM11.regionFacts_of_radial ⟨hK₁.1, hK₁.2.1⟩ hS hK₁.2.2 hE
      have h63_1 := (GM11.theorem_6_3_of_regionFacts hS hPre₁ hK₁.2.1 hins₁ hf).1
      have h63_2 := (GM11.theorem_6_3_of_regionFacts hS hPre₂ hK₁.2.1 hins₂ hf).1
      rintro ⟨A, B⟩ hAB
      have hsep := hT₁.isSeparation hAB
      have hord₁ := hT₁.order_lt hAB
      have hord₂ : separationOrder A B < θ - lam₂ := by omega
      obtain ⟨k, C, hC, hin⟩ := (h63_1 A B hsep hord₁).mp hAB
      refine (h63_2 A B hsep hord₂).mpr ⟨k, C, fun i => ?_, fun e he => ?_⟩
      · obtain ⟨hc, hs, hl, hv⟩ := hC i
        exact ⟨hc, hs, by omega, hv⟩
      · obtain ⟨i, hi⟩ := hin e he
        obtain ⟨hc, hs, hl, _⟩ := hC i
        rw [hCircEq (C i) hc hs hs hl (by omega)] at hi
        exact ⟨i, hi⟩
    · have hE_empty : H₁.E = ∅ := Set.not_nonempty_iff_eq_empty.mp hE
      have hV_le : H₁.V.ncard ≤ 1 := ncard_V_le_one_of_E_empty hS hK₁.1 hE_empty
      have hord_le : θ - lam₁ ≤ 1 := hT₁.order_le_ncard_vertexSet.trans hV_le
      rintro ⟨A, B⟩ hAB
      have hsep := hT₁.isSeparation hAB
      have hord0 : separationOrder A B = 0 := by
        have := hT₁.order_lt hAB
        omega
      have hVA_empty : A.vertexSet = ∅ := by
        by_contra hne
        obtain ⟨x, hxA⟩ := Set.nonempty_iff_ne_empty.mpr hne
        have hxV : x ∈ H₁.V := hsep.left_le.vertexSet_subset hxA
        have hV_eq : H₁.V = {x} := by
          apply Set.Subset.antisymm _ (Set.singleton_subset_iff.mpr hxV)
          intro y hy
          by_contra hyx
          have hxy_ne : x ≠ y := fun h => hyx (h.symm ▸ Set.mem_singleton x)
          have h2 : ({x, y} : Set S).ncard = 2 := Set.ncard_pair hxy_ne
          have hsub : ({x, y} : Set S) ⊆ H₁.V := by
            rintro w (rfl | rfl)
            · exact hxV
            · exact hy
          have := Set.ncard_le_ncard hsub H₁.finite_V
          omega
        have hVA : A.vertexSet = H₁.V :=
          Set.Subset.antisymm hsep.left_le.vertexSet_subset (hV_eq ▸ Set.singleton_subset_iff.mpr
            hxA)
        exact hT₁.axiom3 hAB hVA
      have hEA_empty : A.edgeSet = ∅ :=
        Set.subset_empty_iff.mp (hE_empty ▸ hsep.left_le.edgeSet_subset)
      have hVB_eq : B.vertexSet = H₁.V := by
        have := hsep.vertexSet_union
        rwa [hVA_empty, Set.empty_union] at this
      have hord₂ : separationOrder A B < θ - lam₂ := by
        have := hT₂.one_le
        omega
      exact (hT₂.axiom1 hsep hord₂).resolve_right fun hBA => hT₂.axiom3 hBA hVB_eq

/-- For any tangle `T` of order `θ` in `G`, `GM12.inducedBySubgraph G G θ T = T`. -/
private theorem inducedBySubgraph_self {α β : Type*} {G : Hypergraph α β} {θ : ℕ}
    {T : Set (Hypergraph α β × Hypergraph α β)} (hT : IsTangle G θ T) :
    GM12.inducedBySubgraph G G θ T = T := by
  ext ⟨A, B⟩
  have h_inter_eq : ∀ {C : Hypergraph α β}, C ≤ G → C ∩ G = C := fun hC =>
    GM10.eq_of_le_of_vertexSet_eq_of_edgeSet_eq (inter_le_left hC le_rfl) le_rfl
      (Set.inter_eq_left.mpr hC.vertexSet_subset) (Set.inter_eq_left.mpr hC.edgeSet_subset)
  constructor
  · rintro ⟨hsep, _, hAB⟩
    rwa [h_inter_eq hsep.left_le, h_inter_eq hsep.right_le] at hAB
  · intro hAB
    have hsep := hT.isSeparation hAB
    refine ⟨hsep, hT.order_lt hAB, ?_⟩
    rwa [h_inter_eq hsep.left_le, h_inter_eq hsep.right_le]

/-- Any two tangle metrics `d₁, d₂` of the same respectful tangle `(H, θ, T)` coincide on `H.A`,
`pointDist`, and `pointAtomDist`. -/
theorem tangleMetric_eq_of_hasTangleMetric
    {S : Type w} [TopologicalSpace S] [T2Space S]
    {H : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d₁ d₂ : Set S → Set S → ℕ}
    (hS : IsClosedSurface S) (hConn : ConnectedSpace S)
    (hM₁ : HasTangleMetric H θ T d₁) (hM₂ : HasTangleMetric H θ T d₂) :
    (∀ a ∈ H.A, ∀ b ∈ H.A, d₁ a b = d₂ a b) ∧
    (∀ σ₁ σ₂ : S, pointDist H d₁ σ₁ σ₂ = pointDist H d₂ σ₁ σ₂) ∧
    (∀ σ : S, ∀ b ∈ H.A, pointAtomDist H d₁ σ b = pointAtomDist H d₂ σ b) := by
  have hInd : T = GM12.inducedBySubgraph H.toHypergraph H.toHypergraph θ T :=
    (inducedBySubgraph_self hM₁.1.2.1).symm
  have hle₁₂ := (GraphMinor.GM12.gm15_theorem_7_7.{w} H H θ θ T T d₂ d₁ hS hConn hM₂
    (Drawing.IsSubdrawing.refl H)
    hM₁.1.1 le_rfl hM₁).2 rfl hInd
  have hle₂₁ := (GraphMinor.GM12.gm15_theorem_7_7.{w} H H θ θ T T d₁ d₂ hS hConn hM₁
    (Drawing.IsSubdrawing.refl H)
    hM₂.1.1 le_rfl hM₂).2 rfl hInd
  have hA : ∀ a ∈ H.A, ∀ b ∈ H.A, d₁ a b = d₂ a b := fun a ha b hb =>
    le_antisymm (hle₁₂ a ha b hb a ha b hb Subset.rfl Subset.rfl)
      (hle₂₁ a ha b hb a ha b hb Subset.rfl Subset.rfl)
  refine ⟨hA, fun σ₁ σ₂ => ?_, fun σ b hb => ?_⟩
  · obtain ⟨a₁, ha₁, hσ₁⟩ := exists_atom_of_point H σ₁
    obtain ⟨a₂, ha₂, hσ₂⟩ := exists_atom_of_point H σ₂
    rw [pointDist_eq_of_mem_atom ha₁ ha₂ hσ₁ hσ₂,
      pointDist_eq_of_mem_atom ha₁ ha₂ hσ₁ hσ₂, hA a₁ ha₁ a₂ ha₂]
  · obtain ⟨a, ha, hσ⟩ := exists_atom_of_point H σ
    rw [pointAtomDist_eq_of_mem_atom ha hσ, pointAtomDist_eq_of_mem_atom ha hσ, hA a ha b hb]

/-- Given a radial drawing `K` of `H`, a closed walk `W` of `K`, and a 2-cell drawing `H'` such
that every atom of `H` intersecting `U(walkDrawing K W)` is an atom of `H'`, there is a radial
drawing `K'` of `H'` in which `W` is a closed walk (Graph Minors XV, proof of (4.2), page 125:
"Consequently every atom of $H$ which intersects $ins(W)$ is an atom of $H'$, and we may
therefore choose a radial drawing $K'$ of $H'$ such that $W$ is a walk of $K'$"). -/
theorem exists_radialDrawing_with_walk {S : Type w} [TopologicalSpace S] [T2Space S]
    {H H' K : Drawing S} {u : S} (hS : IsClosedSurface S)
    (h2cell' : (PaintingOrDrawing.drawing H').IsTwoCell)
    (hK : (PaintingOrDrawing.drawing H).IsRadialDrawing K)
    (W : GraphWalk K.toGraph u u)
    (hAtomsW : ∀ a ∈ H.A, (a ∩ (walkDrawing K W).U).Nonempty → a ∈ H'.A) :
    ∃ (K' : Drawing S) (W' : GraphWalk K'.toGraph u u),
      (PaintingOrDrawing.drawing H').IsRadialDrawing K' ∧
      walkDrawing K W = walkDrawing K' W' ∧ W'.length = W.length := by
  classical
  have : ConnectedSpace S := h2cell'.1
  have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  let L := walkDrawing K W
  have hLK : L.IsSubdrawing K := GM11.walkDrawing_isSubdrawing K W
  have hrad : GM11.PreRad (PaintingOrDrawing.drawing H) K := ⟨hK.1, hK.2.1⟩
  have hLV_V : ∀ v ∈ L.V, v ∈ H.V → v ∈ H'.V := by
    intro v hvL hvH
    exact vertex_mem_V_of_mem_A hS hvH
      (hAtomsW {v} (Or.inl (Or.inl ⟨v, hvH, rfl⟩)) ⟨v, rfl, L.V_subset_U hvL⟩)
  have hLV_R : ∀ w ∈ L.V, w ∉ H.V → ∃ r ∈ H.R, r ∈ H'.R ∧ w ∈ r := by
    intro w hwL hwnH
    obtain ⟨r, hr, hwr⟩ := hK.2.1.2.2.2.1 w ⟨hLK.1 hwL, hwnH⟩
    have hr' : r ∈ H'.R :=
      region_mem_R_of_mem_A hS hr (hAtomsW r (Or.inr hr) ⟨w, hwr, L.V_subset_U hwL⟩)
    exact ⟨r, hr, hr', hwr⟩
  have hLV_iff : ∀ x ∈ L.V, x ∈ H.V ↔ x ∈ H'.V := by
    intro x hxL
    refine ⟨hLV_V x hxL, fun hxH' => ?_⟩
    by_contra hxnH
    obtain ⟨r, _, hr', hxr⟩ := hLV_R x hxL hxnH
    exact region_subset hr' hxr (H'.V_subset_U hxH')
  have hLE_props : ∀ e ∈ L.E,
      ∃ v ∈ H.V ∩ L.V, ∃ r ∈ H.R ∩ H'.R, ∃ w ∈ r ∩ L.V,
        closure e ∩ L.V = {v, w} ∧ closure e ∩ K.V = {v, w} ∧ e ⊆ r := by
    intro e heL
    obtain ⟨v, hvH, r, hrH, w, hwr, hwK, hcapK, he_sub⟩ :=
      GM11.spoke_ends hrad hS (hLK.2 heL)
    have hcapL : closure e ∩ L.V = {v, w} := by
      rw [hLK.closure_inter_V heL, hcapK]
    have hvL : v ∈ L.V := by
      have : v ∈ closure e ∩ L.V := by rw [hcapL]; simp
      exact this.2
    have hwL : w ∈ L.V := by
      have : w ∈ closure e ∩ L.V := by rw [hcapL]; simp
      exact this.2
    have hrH' : r ∈ H'.R :=
      region_mem_R_of_mem_A hS hrH (hAtomsW r (Or.inr hrH) ⟨w, hwr, L.V_subset_U hwL⟩)
    exact ⟨v, ⟨hvH, hvL⟩, r, ⟨hrH, hrH'⟩, w, ⟨hwr, hwL⟩, hcapL, hcapK, he_sub⟩
  have hRf' : H'.R.Finite := finite_R hS H'
  have hne' : ∀ r ∈ H'.R, r.Nonempty := fun _ hr => region_nonempty hr
  choose! hub hhub using hne'
  let R_rem := {r ∈ H'.R | Disjoint r L.V}
  have hR_rem_fin : R_rem.Finite := hRf'.subset fun _ hr => hr.1
  let A : Set S := H'.V ∪ hub '' R_rem
  have hA_fin : A.Finite := H'.finite_V.union (hR_rem_fin.image hub)
  let P_pts := GM11.pointsDrawing hA_fin
  have hP_V : P_pts.V = A := rfl
  have hP_U : P_pts.U = A := rfl
  have hP_E : P_pts.E = ∅ := GM11.pointsDrawing_E hA_fin
  have h_glue : L.U ∩ P_pts.U ⊆ L.V ∩ P_pts.V := by
    rintro x ⟨hxLU, hxA⟩
    refine ⟨?_, hxA⟩
    by_contra hxLV
    obtain ⟨e, heL, hxe⟩ := L.exists_edge_of_mem hxLU hxLV
    obtain ⟨v, _, r₀, ⟨_, hr₀'⟩, w₀, ⟨hw₀r, hw₀L⟩, _, _, he_sub⟩ := hLE_props e heL
    have hxr₀ : x ∈ r₀ := he_sub hxe
    rcases hxA with hxH' | ⟨r, ⟨hr', hdisj⟩, rfl⟩
    · exact region_subset hr₀' hxr₀ (H'.V_subset_U hxH')
    · have hreq : r = r₀ := region_eq_of_mem hr' hr₀' (hhub r hr') hxr₀
      exact disjoint_left.mp (hreq ▸ hdisj) hw₀r hw₀L
  let K₀' := L.glue P_pts h_glue
  have hK₀'_U : K₀'.U = L.U ∪ A := rfl
  have hK₀'_V : K₀'.V = L.V ∪ A := rfl
  have hK₀'_E : K₀'.E = L.E := by rw [Drawing.glue_E h_glue, hP_E, union_empty]
  have hLK₀' : L.IsSubdrawing K₀' := ⟨subset_union_left, by rw [hK₀'_E]⟩
  have hpre₀ : (PaintingOrDrawing.drawing H').IsPreRadialDrawing K₀' := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · apply Subset.antisymm
      · rintro x ⟨hxH'U, hxLU | hxA⟩
        · by_cases hxLV : x ∈ L.V
          · by_contra hxnH'
            have hxnH : x ∉ H.V := fun h => hxnH' ((hLV_iff x hxLV).mp h)
            obtain ⟨r, _, hr', hxr⟩ := hLV_R x hxLV hxnH
            exact region_subset hr' hxr hxH'U
          · obtain ⟨e, heL, hxe⟩ := L.exists_edge_of_mem hxLU hxLV
            obtain ⟨_, _, r₀, ⟨_, hr₀'⟩, _, _, _, _, he_sub⟩ := hLE_props e heL
            exact (region_subset hr₀' (he_sub hxe) hxH'U).elim
        · rcases hxA with hxH'V | ⟨r, ⟨hr', _⟩, rfl⟩
          · exact hxH'V
          · exact (region_subset hr' (hhub r hr') hxH'U).elim
      · intro x hxH'V
        exact ⟨H'.V_subset_U hxH'V, Or.inr (Or.inl hxH'V)⟩
    · intro x hxH'V
      exact Or.inr (Or.inl hxH'V)
    · intro r hr'
      by_cases hdisj : Disjoint r L.V
      · refine ⟨hub r, ⟨hhub r hr', Or.inr (Or.inr ⟨r, ⟨hr', hdisj⟩, rfl⟩)⟩, ?_⟩
        rintro w ⟨hwr, hwL | hwH' | ⟨r₁, ⟨hr₁', _⟩, rfl⟩⟩
        · exact (disjoint_left.mp hdisj hwr hwL).elim
        · exact (region_subset hr' hwr (H'.V_subset_U hwH')).elim
        · rw [region_eq_of_mem hr₁' hr' (hhub r₁ hr₁') hwr]
      · obtain ⟨w₀, hw₀r, hw₀L⟩ := not_disjoint_iff.mp hdisj
        refine ⟨w₀, ⟨hw₀r, Or.inl hw₀L⟩, ?_⟩
        have hw₀nH' : w₀ ∉ H'.V := fun h => region_subset hr' hw₀r (H'.V_subset_U h)
        have hw₀nH : w₀ ∉ H.V := fun h => hw₀nH' ((hLV_iff w₀ hw₀L).mp h)
        obtain ⟨r₀, hr₀H, hr₀H', hw₀r₀⟩ := hLV_R w₀ hw₀L hw₀nH
        have hr_eq : r = r₀ := region_eq_of_mem hr' hr₀H' hw₀r hw₀r₀
        rintro w ⟨hwr, hwL | hwH' | ⟨r₁, ⟨hr₁', hdisj₁⟩, rfl⟩⟩
        · exact GM11.hub_unique hrad (hr_eq ▸ hr₀H) hw₀r (hLK.1 hw₀L) hwr (hLK.1 hwL)
        · exact (region_subset hr' hwr (H'.V_subset_U hwH')).elim
        · have hr₁_eq : r₁ = r := region_eq_of_mem hr₁' hr' (hhub r₁ hr₁') hwr
          exact (disjoint_left.mp (hr₁_eq ▸ hdisj₁) hw₀r hw₀L).elim
    · rintro w ⟨hwL | hwH' | ⟨r, ⟨hr', _⟩, rfl⟩, hwnH'⟩
      · have hwnH : w ∉ H.V := fun h => hwnH' ((hLV_iff w hwL).mp h)
        obtain ⟨r, _, hr', hwr⟩ := hLV_R w hwL hwnH
        exact ⟨r, hr', hwr⟩
      · exact (hwnH' hwH').elim
      · exact ⟨r, hr', hhub r hr'⟩
    · intro e heK₀'
      rw [hK₀'_E] at heK₀'
      obtain ⟨v, ⟨hvH, hvL⟩, r, ⟨_, hrH'⟩, w, ⟨hwr, hwL⟩, hcapL, _, he_sub⟩ := hLE_props e heK₀'
      have hvH' : v ∈ H'.V := hLV_V v hvL hvH
      have hwnH' : w ∉ H'.V := fun h => region_subset hrH' hwr (H'.V_subset_U h)
      refine ⟨v, hvH', w, ⟨Or.inl hwL, hwnH'⟩, ?_⟩
      rw [← hLK₀'.closure_inter_V heK₀', hcapL]
    · intro e heK₀' f hfK₀' hef v hvH' r hrH' w ⟨hwr, hwK₀'⟩ hcape hcapf
      rw [hK₀'_E] at heK₀' hfK₀'
      rw [← hLK₀'.closure_inter_V heK₀'] at hcape
      rw [← hLK₀'.closure_inter_V hfK₀'] at hcapf
      have hvL : v ∈ L.V := by
        have : v ∈ closure e ∩ L.V := by rw [hcape]; simp
        exact this.2
      have hwL : w ∈ L.V := by
        have : w ∈ closure e ∩ L.V := by rw [hcape]; simp
        exact this.2
      have hvH : v ∈ H.V := (hLV_iff v hvL).mpr hvH'
      have hwnH' : w ∉ H'.V := fun h => region_subset hrH' hwr (H'.V_subset_U h)
      have hwnH : w ∉ H.V := fun h => hwnH' ((hLV_iff w hwL).mp h)
      obtain ⟨r₀, hr₀H, hr₀H', hw_r₀⟩ := hLV_R w hwL hwnH
      have hr_eq : r = r₀ := region_eq_of_mem hrH' hr₀H' hwr hw_r₀
      have hcapeK : closure e ∩ K.V = {v, w} := by
        rw [← hLK.closure_inter_V heK₀', hcape]
      have hcapfK : closure f ∩ K.V = {v, w} := by
        rw [← hLK.closure_inter_V hfK₀', hcapf]
      exact hK.2.1.2.2.2.2.2 e (hLK.2 heK₀') f (hLK.2 hfK₀') hef v hvH r (hr_eq ▸ hr₀H)
        w ⟨hwr, hLK.1 hwL⟩ hcapeK hcapfK
  obtain ⟨N, hN⟩ := GM11.exists_spoke_bound_drawing h2cell' hS
  let S_nat : Set ℕ :=
    {n | ∃ K' : Drawing S, (PaintingOrDrawing.drawing H').IsPreRadialDrawing K' ∧
      K₀'.IsSubdrawing K' ∧ K'.E.ncard = n}
  have hS_ne : S_nat.Nonempty := ⟨K₀'.E.ncard, K₀', hpre₀, Drawing.IsSubdrawing.refl K₀', rfl⟩
  have hS_bdd : BddAbove S_nat := ⟨N, by rintro _ ⟨K', hpre, _, rfl⟩; exact hN K' hpre⟩
  obtain ⟨K', hpre', hsub₀, hcard⟩ := Nat.sSup_mem hS_ne hS_bdd
  have hRad' : (PaintingOrDrawing.drawing H').IsRadialDrawing K' := by
    refine ⟨h2cell', hpre', ?_⟩
    rintro K'' hpre'' ⟨hV, hE⟩
    refine ⟨?_, ?_⟩
    · intro w hw
      by_cases hwV : w ∈ H'.V
      · exact hpre'.2.1 hwV
      obtain ⟨r, hr, hwr⟩ := hpre''.2.2.2.1 w ⟨hw, hwV⟩
      obtain ⟨w', ⟨hw'r, hw'⟩, -⟩ := hpre'.2.2.1 r hr
      rw [(hpre''.2.2.1 r hr).unique ⟨hwr, hw⟩ ⟨hw'r, hV hw'⟩]
      exact hw'
    · have hsub₀'' : K₀'.IsSubdrawing K'' := hsub₀.trans ⟨hV, hE⟩
      have hle : K''.E.ncard ≤ K'.E.ncard := by
        rw [hcard]
        exact le_csSup hS_bdd ⟨K'', hpre'', hsub₀'', rfl⟩
      exact (eq_of_subset_of_ncard_le hE hle K''.finite_edges).ge
  have hLK' : L.IsSubdrawing K' := hLK₀'.trans hsub₀
  have hWL_V : ∀ x ∈ W.support, x ∈ L.V := fun x hx => by
    rw [GM11.walkDrawing_V]; exact hx
  have hWL_E : ∀ e ∈ W.edges, e ∈ L.E := fun e he => by
    rw [GM11.walkDrawing_E]; exact he
  obtain ⟨W_L, hWL_sup, hWL_ed⟩ := hLK.exists_walk_down W hWL_V hWL_E
  obtain ⟨W', hW'_sup, hW'_ed⟩ := hLK'.exists_walk_up W_L
  have hWD : walkDrawing K W = walkDrawing K' W' := by
    apply Drawing.ext_of_V_E
    · rw [GM11.walkDrawing_V, GM11.walkDrawing_V, hW'_sup, hWL_sup]
    · rw [GM11.walkDrawing_E, GM11.walkDrawing_E, hW'_ed, hWL_ed]
  have hW'_len : W'.length = W.length := by
    change W'.edges.length = W.edges.length
    rw [hW'_ed, hWL_ed]
  exact ⟨K', W', hRad', hWD, hW'_len⟩

/-- Statement of Graph Minors XV, (4.2) (page 125):
"Let $H, H'$ be 2-cell drawings in a surface $\Sigma$, and let $Z \subseteq \Sigma$ include every
atom of $H$ which is not in $A(H')$. (Hence $Z$ includes every atom of $H'$ not in $A(H)$.) Let
$\mathcal{T}, \mathcal{T}'$ be respectful tangles in $H, H'$ respectively, such that, for some
$\lambda \ge 0$, one of $\mathcal{T}, \mathcal{T}'$ is a $\lambda$-compression of the other. Then
for
all $x, y \in \Sigma$, if $d(x, y) < d(x, \sigma)$ for all $\sigma \in Z$, and
$d(x, y) < ord(\mathcal{T})$, then $d'(x, y) \le d(x, y)$." -/
def GM15Theorem42Statement : Prop :=
  ∀ {S : Type w} [TopologicalSpace S] [T2Space S]
    (H H' : Drawing S) (Z : Set S) (θ θ' lam : ℕ)
    (T T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (d d' : Set S → Set S → ℕ) (x y : S),
    IsClosedSurface S → ConnectedSpace S →
    HasTangleMetric H θ T d → HasTangleMetric H' θ' T' d' →
    (∀ a ∈ H.A, a ∉ H'.A → a ⊆ Z) →
    (IsLambdaCompression H H' θ lam T T' d d' ∨ IsLambdaCompression H' H θ' lam T' T d' d) →
    (∀ σ ∈ Z, pointDist H d x y < pointDist H d x σ) →
    pointDist H d x y < θ →
    pointDist H' d' x y ≤ pointDist H d x y

/-- **Graph Minors XV, (4.2)** (page 125):
Distance bound `d'(x, y) ≤ d(x, y)` away from `Z`.
Proved from `(4.1)` (`theorem_4_1_proof`), Graph Minors XII, `(7.7)` (`GM12Theorem77Statement`), and
Graph Minors XIV, `(3.1)` (`GM14.theorem_3_1_proof`). -/
theorem theorem_4_2_proof
     :
    GM15Theorem42Statement.{w} := by
  intro S _ _ H H' Z θ θ' lam T T' d d' x y
    hS hConn hMetric hMetric' hZ hComp hltZ hltθ
  obtain ⟨_, K, ins, hK, hins, hd⟩ := id hMetric
  obtain ⟨ax, hax, hx_ax⟩ := exists_atom_of_point H x
  obtain ⟨ay, hay, hy_ay⟩ := exists_atom_of_point H y
  obtain ⟨ax', hax', hx_ax'⟩ := exists_atom_of_point H' x
  obtain ⟨ay', hay', hy_ay'⟩ := exists_atom_of_point H' y
  have hpt : pointDist H d x y = d ax ay := pointDist_eq_of_mem_atom hax hay hx_ax hy_ay
  have hpt' : pointDist H' d' x y = d' ax' ay' := pointDist_eq_of_mem_atom hax' hay' hx_ax' hy_ay'
  by_cases hxy : ax = ay
  · subst hxy
    have h0 : d ax ax = 0 := by rw [hd ax hax ax hax]; simp [tangleMetric]
    have hax_mem' : ax ∈ H'.A := by
      by_contra hnot
      have hsubZ : ax ⊆ Z := hZ ax hax hnot
      have hlt_xx := hltZ x (hsubZ hx_ax)
      rw [pointDist_eq_of_mem_atom hax hax hx_ax hx_ax] at hlt_xx
      omega
    have hax_eq : ax' = ax := atom_eq_of_mem hax' hax_mem' hx_ax' hx_ax
    have hay_eq : ay' = ax := atom_eq_of_mem hay' hax_mem' hy_ay' hy_ay
    obtain ⟨_, K₀', ins₀', _, _, hd₀'⟩ := hMetric'
    rw [hpt', hax_eq, hay_eq, hd₀' ax hax_mem' ax hax_mem']
    simp [tangleMetric]
  · by_cases hltθ' : pointDist H d x y < θ'
    · have htm_lt : tangleMetric H K ins θ ax ay < θ := by
        rwa [← hd ax hax ay hay, ← hpt]
      obtain ⟨u, W, ax_K, ay_K, hax_K, hay_K, hW_lt, hW_len, hax_sub, hay_sub⟩ :=
        exists_walk_of_tangleMetric_lt hK.2.1 ins hxy htm_lt
      rw [← hd ax hax ay hay, ← hpt] at hW_len
      have hAtomsInW : ∀ a ∈ H.A, (a ∩ insWalk ins K W).Nonempty → a ∈ H'.A := by
        intro a ha ⟨σ, hσa, hσW⟩
        by_contra hnot
        have hσZ : σ ∈ Z := hZ a ha hnot hσa
        obtain ⟨a_K, ha_K⟩ := exists_correspondingAtom hK.2.1 ha
        have ha_sub : a_K ⊆ insWalk ins K W :=
          (GM14.theorem_3_1_proof hS hK hins ha_K W hW_lt).mpr ⟨σ, hσa, hσW⟩
        have hle2 := two_mul_tangleMetric_le_of_walk hK.2.1 ins θ hax_K ha_K W hW_lt hax_sub ha_sub
        rw [← hd ax hax a ha, ← pointDist_eq_of_mem_atom (d := d) hax ha hx_ax hσa] at hle2
        have hlt_σ := hltZ σ hσZ
        omega
      have hAtomsW : ∀ a ∈ H.A, (a ∩ (walkDrawing K W).U).Nonempty → a ∈ H'.A := by
        intro a ha ⟨σ, hσa, hσU⟩
        exact hAtomsInW a ha ⟨σ, hσa, Or.inl hσU⟩
      obtain ⟨K', W', hK', hWD, hW'_len⟩ :=
        exists_radialDrawing_with_walk hS hMetric'.1.1 hK W hAtomsW
      obtain ⟨ins', hins'⟩ := exists_derivedSlope hMetric'.1 hK'.2.1
      let d'_K' := tangleMetric H' K' ins' θ'
      have hM'_K' : HasTangleMetric H' θ' T' d'_K' :=
        ⟨hMetric'.1, K', ins', hK', hins', fun _ _ _ _ => rfl⟩
      obtain ⟨hd'_eq_A, hd'_eq_pt, _⟩ :=
        tangleMetric_eq_of_hasTangleMetric hS hConn hMetric' hM'_K'
      have hd' : ∀ a ∈ H'.A, ∀ b ∈ H'.A, d' a b = tangleMetric H' K' ins' θ' a b := hd'_eq_A
      have hins_eq : insWalk ins K W = insWalk ins' K' W' := by
        have hComp0 : IsLambdaCompression H H θ 0 T T d d :=
          ⟨hMetric.1.2.1.one_le, hMetric, by simpa using hMetric, fun _ _ => by simp⟩
        have hComp0' : IsLambdaCompression H' H' θ' 0 T' T' d' d' :=
          ⟨hMetric'.1.2.1.one_le, hMetric', by simpa using hMetric', fun _ _ => by simp⟩
        rcases hComp with hC | hC
        · have hθ'_eq : θ - lam = θ' :=
            le_antisymm
              ((GM10.subset_iff_truncation hMetric'.1.2.1 hC.hasMetric'.1.2.1).mp subset_rfl).1
              ((GM10.subset_iff_truncation hC.hasMetric'.1.2.1 hMetric'.1.2.1).mp subset_rfl).1
          subst hθ'_eq
          exact (theorem_4_1_proof H H H' K K' θ 0 lam T T T' d d d' ins ins'
            hS hComp0 hC hK (by simpa using hins) (by simpa using hd)
            hK' hins' hd').1 u u W W' hWD (by omega) (by omega)
        · have hθ_eq : θ' - lam = θ :=
            le_antisymm
              ((GM10.subset_iff_truncation hMetric.1.2.1 hC.hasMetric'.1.2.1).mp subset_rfl).1
              ((GM10.subset_iff_truncation hC.hasMetric'.1.2.1 hMetric.1.2.1).mp subset_rfl).1
          subst hθ_eq
          exact (theorem_4_1_proof H' H H' K K' θ' lam 0 T' T T' d' d d' ins ins'
            hS hC hComp0' hK hins hd
            hK' (by simpa using hins') (by simpa using hd')).1 u u W W' hWD (by omega) (by omega)
      have hx_inW : (ax ∩ insWalk ins K W).Nonempty :=
        (GM14.theorem_3_1_proof hS hK hins hax_K W hW_lt).mp hax_sub
      have hy_inW : (ay ∩ insWalk ins K W).Nonempty :=
        (GM14.theorem_3_1_proof hS hK hins hay_K W hW_lt).mp hay_sub
      have hax_eq : ax' = ax :=
        atom_eq_of_mem hax' (hAtomsInW ax hax hx_inW) hx_ax' hx_ax
      have hay_eq : ay' = ay :=
        atom_eq_of_mem hay' (hAtomsInW ay hay hy_inW) hy_ay' hy_ay
      obtain ⟨ax'_K', hax'_K'⟩ := exists_correspondingAtom hK'.2.1 hax'
      obtain ⟨ay'_K', hay'_K'⟩ := exists_correspondingAtom hK'.2.1 hay'
      have hW'_lt : W'.length < 2 * θ' := by omega
      have hax'_sub : ax'_K' ⊆ insWalk ins' K' W' :=
        (GM14.theorem_3_1_proof hS hK' hins' hax'_K' W' hW'_lt).mpr (by rwa [hax_eq, ← hins_eq])
      have hay'_sub : ay'_K' ⊆ insWalk ins' K' W' :=
        (GM14.theorem_3_1_proof hS hK' hins' hay'_K' W' hW'_lt).mpr (by rwa [hay_eq, ← hins_eq])
      have hle2' := two_mul_tangleMetric_le_of_walk hK'.2.1 ins' θ' hax'_K' hay'_K' W' hW'_lt
        hax'_sub hay'_sub
      rw [← hd' ax' hax' ay' hay', ← hpt'] at hle2'
      omega
    · obtain ⟨_, K₀', ins₀', _, _, hd₀'⟩ := hMetric'
      have hle_θ' : pointDist H' d' x y ≤ θ' := by
        rw [hpt', hd₀' ax' hax' ay' hay']
        exact tangleMetric_le_ord H' K₀' ins₀' θ' ax' ay'
      omega

/-- Statement of Graph Minors XV, (4.3) (page 125), with the hypotheses `E(H) ≠ ∅` and "if `z ∈
E(H)`
then `λ ≥ 2`" that XII (7.11) needs (`GM12Theorem711Statement`). The printed form of XII (7.11) is
false: see the correction to (7.11) in `corrections/GM12.md`. (4.3) is only used in (4.5), (4.6),
(4.7) of XV, where `λ ≥ 2`: "If $H, \Sigma, \mathcal{T}, \theta, d, \lambda, z$ are as above then
$H - z^\lambda$ is 2-cell." -/
def GM15Theorem43Statement : Prop :=
  ∀ {S : Type w} [TopologicalSpace S] [T2Space S]
    (H : Drawing S) (θ lam : ℕ)
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (d : Set S → Set S → ℕ) (z : Set S),
    IsClosedSurface S → ConnectedSpace S →
    HasTangleMetric H θ T d → H.E.Nonempty → z ∈ H.A → lam < θ → (z ∈ H.E → 2 ≤ lam) →
    (PaintingOrDrawing.drawing (deleteAtomNeighborhood H d z lam)).IsTwoCell

/-- **Graph Minors XII, (4.1)** (`GM12Theorem41Statement`, page 248):
Proved from `GM12.theorem_4_1_proof`. -/
theorem gm12_theorem_4_1 : GM12Theorem41Statement.{w} :=
  GM12.theorem_4_1_proof

/-- **Graph Minors XV, (4.3)** (page 125):
For a 2-cell drawing `H` with `E(H) ≠ ∅` in a connected surface `Σ` with a respectful tangle `T`
of order `θ` with metric `d`, `z ∈ A(H)`, `λ < θ`, and `λ ≥ 2` if `z ∈ E(H)`, the subdrawing
`H - z^λ` is 2-cell.
Proved from Graph Minors XII, (7.11) (`GM12.gm12_theorem_7_11`). -/
theorem theorem_4_3_proof : GM15Theorem43Statement.{w} :=
  GM12.gm12_theorem_7_11

/-- Statement of Graph Minors XV, (4.4) (page 126):
"Let $\mathcal{T}$ be a respectful tangle of order $\theta$ in a 2-cell drawing $H$ in a surface
$\Sigma$. Let $z \in A(H)$, let $\lambda \ge 2$ be an integer with $\theta > 4\lambda + 2$, and let
$H' \subseteq H$ be a 2-cell subdrawing such that $a \in A(H')$ for every $a \in A(H)$ with
$d(z, a) > \lambda$. Then there is a unique respectful tangle $\mathcal{T}'$ in $H'$ which is a
$(4\lambda + 2)$-compression of $\mathcal{T}$, and it includes $(A \cap H', B \cap H')$ for every
$(A, B) \in \mathcal{T}$ of order $< \theta - 4\lambda - 2$." -/
def GM15Theorem44Statement : Prop :=
  ∀ {S : Type w} [TopologicalSpace S] [T2Space S]
    (H H' : Drawing S) (θ lam : ℕ)
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (d : Set S → Set S → ℕ) (z : Set S),
    IsClosedSurface S → ConnectedSpace S →
    HasTangleMetric H θ T d → z ∈ H.A →
    2 ≤ lam → 4 * lam + 2 < θ →
    H'.IsSubdrawing H → (PaintingOrDrawing.drawing H').IsTwoCell →
    (∀ a ∈ H.A, lam < d z a → a ∈ H'.A) →
    ∃ (T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
      (d' : Set S → Set S → ℕ),
      IsLambdaCompression H H' θ (4 * lam + 2) T T' d d' ∧
      (∀ A B : Hypergraph S (Set S),
        (A, B) ∈ T → separationOrder A B < θ - (4 * lam + 2) →
          (A ∩ H'.toHypergraph, B ∩ H'.toHypergraph) ∈ T') ∧
      (∀ (T'' : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
          (d'' : Set S → Set S → ℕ),
        IsLambdaCompression H H' θ (4 * lam + 2) T T'' d d'' → T'' = T')

/-- **Graph Minors XV, (4.4)** (page 126):
Unique `(4λ + 2)`-compression of `T` in a 2-cell subdrawing `H' ⊆ H` containing all atoms `a ∈ A(H)`
with `d(z, a) > λ`.
Proved from Graph Minors XII, (7.10) (`GM12Theorem710Statement`). -/
theorem theorem_4_4_proof :
    GM15Theorem44Statement.{w} := by
  intro S _ _ H H' θ lam T d z hS hConn hMetric hz hlam hθ hSub h2cell hAtoms
  have hθ' : 4 * lam + 3 ≤ θ := by omega
  have hEdist : ∀ e ∈ H.E \ H'.E, d z e ≤ lam := by
    rintro e ⟨heH, henot⟩
    by_contra hnot
    have hlt : lam < d z e := Nat.lt_of_not_le hnot
    have heA' : e ∈ H'.A := hAtoms e (Or.inl (Or.inr heH)) hlt
    exact henot (edge_mem_E_of_mem_A hS heH heA')
  obtain ⟨T', d', ⟨hM', hMem', hDist'⟩, hUniq⟩ :=
    GraphMinor.GM12.gm14_theorem_7_10.{w} S hS hConn H H' θ lam T d z hθ' hMetric hz hSub h2cell
      hEdist (fun _ => hlam)
  have hSubEq : θ - 4 * lam - 2 = θ - (4 * lam + 2) := by omega
  rw [hSubEq] at hM' hMem' hUniq
  refine ⟨T', d', ⟨hθ, hMetric, hM', fun σ₁ σ₂ => ?_⟩, hMem', fun T'' d'' hComp'' => ?_⟩
  · obtain ⟨a₁, ha₁, hσ₁⟩ := exists_atom_of_point H σ₁
    obtain ⟨a₂, ha₂, hσ₂⟩ := exists_atom_of_point H σ₂
    obtain ⟨a₁', ha₁', hσ₁'⟩ := exists_atom_of_point H' σ₁
    obtain ⟨a₂', ha₂', hσ₂'⟩ := exists_atom_of_point H' σ₂
    rw [pointDist_eq_of_mem_atom ha₁ ha₂ hσ₁ hσ₂, pointDist_eq_of_mem_atom ha₁' ha₂' hσ₁' hσ₂']
    have hsub₁ := atom_subset_of_isSubdrawing hSub ha₁ ha₁' hσ₁ hσ₁'
    have hsub₂ := atom_subset_of_isSubdrawing hSub ha₂ ha₂' hσ₂ hσ₂'
    have hle := (hDist' a₁ ha₁ a₂ ha₂ a₁' ha₁' a₂' ha₂' hsub₁ hsub₂).1
    omega
  · refine hUniq T'' d'' hComp''.hasMetric' (fun a ha b hb a' ha' b' hb' hsub₁ hsub₂ => ?_)
    obtain ⟨σ₁, hσ₁⟩ := atom_nonempty ha
    obtain ⟨σ₂, hσ₂⟩ := atom_nonempty hb
    have hσ₁' : σ₁ ∈ a' := hsub₁ hσ₁
    have hσ₂' : σ₂ ∈ b' := hsub₂ hσ₂
    have hle := hComp''.dist_le σ₁ σ₂
    rw [pointDist_eq_of_mem_atom ha hb hσ₁ hσ₂, pointDist_eq_of_mem_atom ha' hb' hσ₁' hσ₂'] at hle
    omega

/-- If `G' ≤ G` and `(A, B)` is a separation of `G`, then `(A ∩ G', B ∩ G')` is a separation of `G'`
of order at most `separationOrder A B`. -/
theorem isSeparation_inter_subhypergraph {α β : Type*} {G G' A B : Hypergraph α β}
    (hSub : G' ≤ G) (hsep : G.IsSeparation A B) :
    G'.IsSeparation (A ∩ G') (B ∩ G') ∧
      separationOrder (A ∩ G') (B ∩ G') ≤ separationOrder A B := by
  have hAl : A ∩ G' ≤ G' := inter_le_right hsep.left_le hSub
  have hBl : B ∩ G' ≤ G' := inter_le_right hsep.right_le hSub
  refine ⟨(isSeparation_iff_of_le hAl hBl).mpr ⟨?_, ?_, ?_⟩, ?_⟩
  · change (A.vertexSet ∩ G'.vertexSet) ∪ (B.vertexSet ∩ G'.vertexSet) = G'.vertexSet
    rw [← Set.union_inter_distrib_right, hsep.vertexSet_union,
      Set.inter_eq_right.mpr hSub.vertexSet_subset]
  · change (A.edgeSet ∩ G'.edgeSet) ∪ (B.edgeSet ∩ G'.edgeSet) = G'.edgeSet
    rw [← Set.union_inter_distrib_right, hsep.edgeSet_union,
      Set.inter_eq_right.mpr hSub.edgeSet_subset]
  · ext e
    change e ∈ (A.edgeSet ∩ G'.edgeSet) ∩ (B.edgeSet ∩ G'.edgeSet) ↔ e ∈ (∅ : Set β)
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
    rintro ⟨⟨heA, _⟩, ⟨heB, _⟩⟩
    exact hsep.notMem_edgeSet_right heA heB
  · refine Set.ncard_le_ncard (fun x hx => ⟨hx.1.1, hx.2.1⟩) ?_
    exact (G.vertexSet_finite.subset hsep.left_le.vertexSet_subset).subset Set.inter_subset_left

/-- If `G' ≤ G` and `T'` is a tangle of order `θ` in `G'`, then `inducedBySubgraph G G' θ T'` is a
tangle of order `θ` in `G` (Graph Minors XII, Section 4, page 248). -/
theorem isTangle_inducedBySubgraph {α β : Type*} {G G' : Hypergraph α β} {θ : ℕ}
    {T' : Set (Hypergraph α β × Hypergraph α β)}
    (hSub : G' ≤ G) (hT' : IsTangle G' θ T') :
    IsTangle G θ (GM12.inducedBySubgraph G G' θ T') where
  one_le := hT'.one_le
  isSeparation _ _ h := h.1
  order_lt _ _ h := h.2.1
  axiom1 {A B} hsep hord := by
    obtain ⟨hsep', hle⟩ := isSeparation_inter_subhypergraph hSub hsep
    have hord' : separationOrder (A ∩ G') (B ∩ G') < θ := lt_of_le_of_lt hle hord
    rcases hT'.axiom1 hsep' hord' with h1 | h2
    · exact Or.inl ⟨hsep, hord, h1⟩
    · exact Or.inr ⟨hsep.symm, by rwa [separationOrder_comm], h2⟩
  axiom2 {A₁ B₁ A₂ B₂ A₃ B₃} h1 h2 h3 hcov := by
    apply hT'.axiom2 h1.2.2 h2.2.2 h3.2.2
    have hle1 : A₁ ∩ G' ≤ G' := inter_le_right h1.1.left_le hSub
    have hle2 : A₂ ∩ G' ≤ G' := inter_le_right h2.1.left_le hSub
    have hle3 : A₃ ∩ G' ≤ G' := inter_le_right h3.1.left_le hSub
    have hleU : (A₁ ∩ G') ∪ (A₂ ∩ G') ∪ (A₃ ∩ G') ≤ G' :=
      union_le (union_le hle1 hle2) hle3
    refine GM10.eq_of_le_of_vertexSet_eq_of_edgeSet_eq hleU le_rfl ?_ ?_
    · ext x
      change (x ∈ (A₁.vertexSet ∩ G'.vertexSet) ∪ (A₂.vertexSet ∩ G'.vertexSet) ∪
        (A₃.vertexSet ∩ G'.vertexSet)) ↔ x ∈ G'.vertexSet
      have hV : A₁.vertexSet ∪ A₂.vertexSet ∪ A₃.vertexSet = G.vertexSet :=
        congrArg Hypergraph.vertexSet hcov
      constructor
      · rintro ((⟨_, hx⟩ | ⟨_, hx⟩) | ⟨_, hx⟩) <;> exact hx
      · intro hx
        have hxG : x ∈ A₁.vertexSet ∪ A₂.vertexSet ∪ A₃.vertexSet :=
          hV.symm ▸ hSub.vertexSet_subset hx
        rcases hxG with (hx1 | hx2) | hx3
        · exact Or.inl (Or.inl ⟨hx1, hx⟩)
        · exact Or.inl (Or.inr ⟨hx2, hx⟩)
        · exact Or.inr ⟨hx3, hx⟩
    · ext e
      change (e ∈ (A₁.edgeSet ∩ G'.edgeSet) ∪ (A₂.edgeSet ∩ G'.edgeSet) ∪
        (A₃.edgeSet ∩ G'.edgeSet)) ↔ e ∈ G'.edgeSet
      have hE : A₁.edgeSet ∪ A₂.edgeSet ∪ A₃.edgeSet = G.edgeSet :=
        congrArg Hypergraph.edgeSet hcov
      constructor
      · rintro ((⟨_, he⟩ | ⟨_, he⟩) | ⟨_, he⟩) <;> exact he
      · intro he
        have heG : e ∈ A₁.edgeSet ∪ A₂.edgeSet ∪ A₃.edgeSet :=
          hE.symm ▸ hSub.edgeSet_subset he
        rcases heG with (he1 | he2) | he3
        · exact Or.inl (Or.inl ⟨he1, he⟩)
        · exact Or.inl (Or.inr ⟨he2, he⟩)
        · exact Or.inr ⟨he3, he⟩
  axiom3 {A B} hAB hV := by
    apply hT'.axiom3 hAB.2.2
    change A.vertexSet ∩ G'.vertexSet = G'.vertexSet
    rw [hV, Set.inter_eq_right.mpr hSub.vertexSet_subset]

/-- If `H₀` is a subdrawing of `H'` and `T₀` is a respectful tangle of order `θ'` in `H₀`, then
`inducedBySubgraph H'.toHypergraph H₀.toHypergraph θ' T₀` is respectful in `H'`. -/
private theorem isRespectful_inducedBySubgraph {S : Type w} [TopologicalSpace S] [T2Space S]
    {H₀ H' : Drawing S} {θ' : ℕ}
    {T₀ : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hSub : H₀.IsSubdrawing H')
    (hResp₀ : (PaintingOrDrawing.drawing H₀).IsRespectful θ' T₀) :
    (PaintingOrDrawing.drawing H').IsRespectful θ'
      (GM12.inducedBySubgraph H'.toHypergraph H₀.toHypergraph θ' T₀) := by
  exact GM12.isRespectful_inducedBySubgraph hSub hResp₀

/-- For `H₀ = H.span ∅ E'` with `H₀.IsSubdrawing H'` and `IsTangle H₀.toHypergraph θ' T₀`, the
edge-based `GM10.inducedTangle` coincides with `GM12.inducedBySubgraph`. -/
theorem inducedTangle_eq_inducedBySubgraph_of_span_empty
    {S : Type w} [TopologicalSpace S] [T2Space S]
    {H H₀ H' : Drawing S} {E' : Set (Set S)} {θ' : ℕ}
    {T₀ : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hH₀ : H₀ = H.span ∅ E') (hSub : H₀.IsSubdrawing H')
    (hT₀ : IsTangle H₀.toHypergraph θ' T₀) :
    GM10.inducedTangle H'.toHypergraph H₀.toHypergraph T₀ θ' =
      GM12.inducedBySubgraph H'.toHypergraph H₀.toHypergraph θ' T₀ := by
  have hSubHyp : H₀.toHypergraph ≤ H'.toHypergraph := by
    refine ⟨hSub.1, hSub.2, fun e he₀ => ?_⟩
    ext v
    change (e ∈ H'.E ∧ v ∈ H'.V ∧ v ∈ closure e) ↔ (e ∈ H₀.E ∧ v ∈ H₀.V ∧ v ∈ closure e)
    constructor
    · rintro ⟨_, hv', hve⟩
      refine ⟨he₀, ?_, hve⟩
      have hv_in : v ∈ closure e ∩ H'.V := ⟨hve, hv'⟩
      rw [← hSub.closure_inter_V he₀] at hv_in
      exact hv_in.2
    · rintro ⟨_, hv₀, hve⟩
      exact ⟨hSub.2 he₀, hSub.1 hv₀, hve⟩
  ext ⟨A, B⟩
  constructor
  · rintro ⟨hsep, hord, ⟨C, D⟩, hCD, hCE⟩
    change H'.toHypergraph.IsSeparation A B at hsep
    change separationOrder A B < θ' at hord
    change C.edgeSet = A.edgeSet ∩ H₀.E at hCE
    refine ⟨hsep, hord, ?_⟩
    obtain ⟨hsep₀, hle₀⟩ := isSeparation_inter_subhypergraph hSubHyp hsep
    have hord₀ : separationOrder (A ∩ H₀.toHypergraph) (B ∩ H₀.toHypergraph) < θ' :=
      lt_of_le_of_lt hle₀ hord
    by_cases hθ2 : 2 ≤ θ'
    · exact GM10.theorem_2_9_proof hT₀ hCD hsep₀ hord₀
        (Or.inr (Or.inr ⟨hθ2, subset_of_eq hCE.symm⟩))
    · refine GM10.theorem_2_9_proof hT₀ hCD hsep₀ hord₀ (Or.inr (Or.inl ?_))
      rintro v ⟨hvA, hv₀⟩
      have hv_span : v ∈ (H.span ∅ E').V := hH₀ ▸ hv₀
      rcases hv_span with ⟨h, _⟩ | hv_edges
      · exact False.elim h
      · obtain ⟨e, he_mem, hve_cl, hvH⟩ := mem_iUnion₂.mp hv_edges
        have he₀ : e ∈ H₀.E := by rw [hH₀, H.span_E]; exact he_mem
        have he' : e ∈ H'.E := hSub.2 he₀
        have hinc' : H'.toHypergraph.Inc e v := ⟨he', hSub.1 hv₀, hve_cl⟩
        have he_not_B : e ∉ B.edgeSet := by
          intro heB
          have hvB_ends : v ∈ B.ends e := by
            rw [← hsep.right_le.ends_eq e heB]
            exact hinc'
          have hvB : v ∈ B.vertexSet := B.vertex_mem_of_inc hvB_ends
          have hmem_inter : v ∈ (A ∩ B).vertexSet := ⟨hvA, hvB⟩
          have hpos : 0 < separationOrder A B :=
            (Set.ncard_pos ((H'.finite_V.subset hsep.left_le.vertexSet_subset).subset
              Set.inter_subset_left)).mpr ⟨v, hmem_inter⟩
          have := hT₀.one_le
          omega
        have heA : e ∈ A.edgeSet := by
          have he_union : e ∈ A.edgeSet ∪ B.edgeSet := hsep.edgeSet_union.symm ▸ he'
          exact he_union.resolve_right he_not_B
        have heC : e ∈ C.edgeSet := by
          rw [hCE]
          exact ⟨heA, he₀⟩
        have hinc₀ : H₀.toHypergraph.Inc e v := ⟨he₀, hv₀, hve_cl⟩
        have hvC_ends : v ∈ C.ends e := by
          rw [← (hT₀.isSeparation hCD).left_le.ends_eq e heC]
          exact hinc₀
        exact C.vertex_mem_of_inc hvC_ends
  · rintro ⟨hsep, hord, hmem₀⟩
    exact ⟨hsep, hord, (A ∩ H₀.toHypergraph, B ∩ H₀.toHypergraph), hmem₀, rfl⟩

/-- Statement of Graph Minors XV, (4.5) (page 126):
"Let $\mathcal{T}$ be a respectful tangle of order $\theta$ in a 2-cell drawing $H$ in a surface
$\Sigma$. Let $z \in A(H)$, let $\lambda \ge 2$ be an integer with $\theta > 4\lambda + 2$, and let
$H'$ be a 2-cell drawing in $\Sigma$ such that $a \in A(H')$ for every $a \in A(H)$ with
$d(z, a) > \lambda$. Then
(i) there is a unique $(4\lambda + 2)$-compression $\mathcal{T}'$ of $\mathcal{T}$ in $H'$
(ii) $H - z^\lambda \subseteq H'$, and $\mathcal{T}'$ is the tangle induced in $H'$ from the unique
$(4\lambda + 2)$-compression of $\mathcal{T}$ in $H - z^\lambda$
(iii) if $H' \subseteq H$ then $(A \cap H', B \cap H') \in \mathcal{T}'$ for every
$(A, B) \in \mathcal{T}$ of order $< \theta - 4\lambda - 2$." -/
def GM15Theorem45Statement : Prop :=
  ∀ {S : Type w} [TopologicalSpace S] [T2Space S]
    (H H' : Drawing S) (θ lam : ℕ)
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (d : Set S → Set S → ℕ) (z : Set S),
    IsClosedSurface S → ConnectedSpace S →
    HasTangleMetric H θ T d → z ∈ H.A →
    2 ≤ lam → 4 * lam + 2 < θ →
    (PaintingOrDrawing.drawing H').IsTwoCell →
    (∀ a ∈ H.A, lam < d z a → a ∈ H'.A) →
    (deleteAtomNeighborhood H d z lam).IsSubdrawing H' ∧
    ∃ (T₀ T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
      (d₀ d' : Set S → Set S → ℕ),
      IsLambdaCompression H (deleteAtomNeighborhood H d z lam) θ (4 * lam + 2) T T₀ d d₀ ∧
      IsLambdaCompression H H' θ (4 * lam + 2) T T' d d' ∧
      T' = GM10.inducedTangle H'.toHypergraph (deleteAtomNeighborhood H d z lam).toHypergraph
        T₀ (θ - (4 * lam + 2)) ∧
      (∀ (T'' : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
          (d'' : Set S → Set S → ℕ),
        IsLambdaCompression H H' θ (4 * lam + 2) T T'' d d'' → T'' = T')

/-- **Graph Minors XV, (4.5)** (page 126):
Existence and uniqueness of the `(4λ + 2)`-compression `T'` of `T` in `H'`, with `H - z^λ ⊆ H'` and
`T'` induced in `H'` from the `(4λ + 2)`-compression `T₀` of `T` in `H - z^λ`.
Proved from `(4.1)`, `(4.3)`, Graph Minors XII, `(7.7)`, `(7.10)`, and `(7.11)`. -/
theorem theorem_4_5_proof
     :
    GM15Theorem45Statement.{w} := by
  intro S _ _ H H' θ lam T d z hS hConn hMetric hz hlam hθ h2cell' hAtoms
  let H₀ := deleteAtomNeighborhood H d z lam
  have hE_ne : H.E.Nonempty := by
    by_contra hE
    have hV_le := ncard_V_le_one_of_E_empty hS hMetric.1.1 (Set.not_nonempty_iff_eq_empty.mp hE)
    have hord_le : θ ≤ H.V.ncard := hMetric.1.2.1.order_le_ncard_vertexSet
    omega
  have hH₀_eq : H₀ = H.span ∅ {e ∈ H.E | lam < d z e} := by
    change deleteAtomNeighborhood H d z lam = _
    rw [deleteAtomNeighborhood, ite_eq_right_iff.mpr fun h => False.elim (hE_ne.ne_empty h)]
  have hSubH₀H : H₀.IsSubdrawing H := by
    rw [hH₀_eq]
    exact H.span_isSubdrawing _ _
  have h2cell₀ : (PaintingOrDrawing.drawing H₀).IsTwoCell :=
    theorem_4_3_proof H θ lam T d z hS hConn hMetric
      hE_ne hz (by omega) (fun _ => hlam)
  have hSubH₀H' : H₀.IsSubdrawing H' := by
    refine ⟨?_, ?_⟩
    · intro v hv₀
      rw [hH₀_eq] at hv₀
      rcases hv₀ with ⟨h, _⟩ | hv_edges
      · exact False.elim h
      · obtain ⟨e, ⟨⟨heH, hlt⟩, _⟩, hve_cl, hvH⟩ := mem_iUnion₂.mp hv_edges
        have he' : e ∈ H'.E :=
          edge_mem_E_of_mem_A hS heH (hAtoms e (Or.inl (Or.inr heH)) hlt)
        have hv_not_e : v ∉ e := fun hve => (heH.2.1 hve).2 hvH
        have hcl' : closure e \ H'.V = e := H'.closure_diff_V he'
        by_contra hv'
        exact hv_not_e (hcl' ▸ ⟨hve_cl, hv'⟩)
    · intro e he₀
      rw [hH₀_eq, H.span_E] at he₀
      exact edge_mem_E_of_mem_A hS he₀.1.1 (hAtoms e (Or.inl (Or.inr he₀.1.1)) he₀.1.2)
  have hEdist₀ : ∀ e ∈ H.E \ H₀.E, d z e ≤ lam := by
    rintro e ⟨heH, henot⟩
    rw [hH₀_eq, H.span_E] at henot
    have : ¬ lam < d z e := fun hlt => henot ⟨⟨heH, hlt⟩, heH⟩
    omega
  obtain ⟨T₀, d₀, ⟨hM₀, hMem₀, hDist₀⟩, _⟩ :=
    GraphMinor.GM12.gm14_theorem_7_10.{w} S hS hConn H H₀ θ lam T d z
      (by omega) hMetric hz hSubH₀H h2cell₀ hEdist₀ (fun _ => hlam)
  have hSubEq : θ - 4 * lam - 2 = θ - (4 * lam + 2) := by omega
  rw [hSubEq] at hM₀ hMem₀
  have hComp₀ : IsLambdaCompression H H₀ θ (4 * lam + 2) T T₀ d d₀ := by
    refine ⟨hθ, hMetric, hM₀, fun σ₁ σ₂ => ?_⟩
    obtain ⟨a₁, ha₁, hσ₁⟩ := exists_atom_of_point H σ₁
    obtain ⟨a₂, ha₂, hσ₂⟩ := exists_atom_of_point H σ₂
    obtain ⟨a₁', ha₁', hσ₁'⟩ := exists_atom_of_point H₀ σ₁
    obtain ⟨a₂', ha₂', hσ₂'⟩ := exists_atom_of_point H₀ σ₂
    rw [pointDist_eq_of_mem_atom ha₁ ha₂ hσ₁ hσ₂, pointDist_eq_of_mem_atom ha₁' ha₂' hσ₁' hσ₂']
    have hsub₁ := atom_subset_of_isSubdrawing hSubH₀H ha₁ ha₁' hσ₁ hσ₁'
    have hsub₂ := atom_subset_of_isSubdrawing hSubH₀H ha₂ ha₂' hσ₂ hσ₂'
    have hle := (hDist₀ a₁ ha₁ a₂ ha₂ a₁' ha₁' a₂' ha₂' hsub₁ hsub₂).1
    omega
  let θ' := θ - (4 * lam + 2)
  let T' := GM12.inducedBySubgraph H'.toHypergraph H₀.toHypergraph θ' T₀
  have hSubHyp : H₀.toHypergraph ≤ H'.toHypergraph := by
    refine ⟨hSubH₀H'.1, hSubH₀H'.2, fun e he₀ => ?_⟩
    ext v
    change (e ∈ H'.E ∧ v ∈ H'.V ∧ v ∈ closure e) ↔ (e ∈ H₀.E ∧ v ∈ H₀.V ∧ v ∈ closure e)
    constructor
    · rintro ⟨_, hv', hve⟩
      refine ⟨he₀, ?_, hve⟩
      have hv_in : v ∈ closure e ∩ H'.V := ⟨hve, hv'⟩
      rw [← hSubH₀H'.closure_inter_V he₀] at hv_in
      exact hv_in.2
    · rintro ⟨_, hv₀, hve⟩
      exact ⟨hSubH₀H'.2 he₀, hSubH₀H'.1 hv₀, hve⟩
  have hT' : IsTangle H'.toHypergraph θ' T' :=
    isTangle_inducedBySubgraph hSubHyp hM₀.1.2.1
  have hResp' : (PaintingOrDrawing.drawing H').IsRespectful θ' T' :=
    isRespectful_inducedBySubgraph hSubH₀H' hM₀.1.2.2
  have hRDT' : IsRespectfulDrawingTangle H' θ' T' :=
    ⟨h2cell', hT', hResp'⟩
  obtain ⟨d', hM'⟩ := exists_hasTangleMetric hS hRDT'
  have hComp_of_metric : ∀ d'_any : Set S → Set S → ℕ,
      HasTangleMetric H' θ' T' d'_any →
      IsLambdaCompression H H' θ (4 * lam + 2) T T' d d'_any := by
    intro d'_any hM'_any
    have h77_ii := (GraphMinor.GM12.gm15_theorem_7_7.{w} H' H₀ θ' θ' T' T₀ d'_any d₀ hS hConn
      hM'_any hSubH₀H' h2cell₀ le_rfl hM₀).2
      rfl rfl
    refine ⟨hθ, hMetric, hM'_any, fun σ₁ σ₂ => ?_⟩
    obtain ⟨a₁', ha₁', hσ₁'⟩ := exists_atom_of_point H' σ₁
    obtain ⟨a₂', ha₂', hσ₂'⟩ := exists_atom_of_point H' σ₂
    obtain ⟨a₁₀, ha₁₀, hσ₁₀⟩ := exists_atom_of_point H₀ σ₁
    obtain ⟨a₂₀, ha₂₀, hσ₂₀⟩ := exists_atom_of_point H₀ σ₂
    have hsub₁ := atom_subset_of_isSubdrawing hSubH₀H' ha₁' ha₁₀ hσ₁' hσ₁₀
    have hsub₂ := atom_subset_of_isSubdrawing hSubH₀H' ha₂' ha₂₀ hσ₂' hσ₂₀
    have hle_0_any := h77_ii a₁' ha₁' a₂' ha₂' a₁₀ ha₁₀ a₂₀ ha₂₀ hsub₁ hsub₂
    have hle_H_0 := hComp₀.dist_le σ₁ σ₂
    rw [pointDist_eq_of_mem_atom (d := d₀) ha₁₀ ha₂₀ hσ₁₀ hσ₂₀] at hle_H_0
    rw [pointDist_eq_of_mem_atom (d := d'_any) ha₁' ha₂' hσ₁' hσ₂']
    omega
  have hComp' : IsLambdaCompression H H' θ (4 * lam + 2) T T' d d' := hComp_of_metric d' hM'
  have hIndEq : T' = GM10.inducedTangle H'.toHypergraph H₀.toHypergraph T₀ θ' :=
    (inducedTangle_eq_inducedBySubgraph_of_span_empty hH₀_eq hSubH₀H' hM₀.1.2.1).symm
  refine ⟨hSubH₀H', T₀, T', d₀, d', hComp₀, hComp', hIndEq, fun T'' d'' hComp'' => ?_⟩
  obtain ⟨K'', ins'', hK'', hins'', hd''⟩ := hComp''.hasMetric'.2
  obtain ⟨ins'_K'', hins'_K''⟩ := exists_derivedSlope hRDT' hK''.2.1
  let d'_K'' := tangleMetric H' K'' ins'_K'' θ'
  have hM'_K'' : HasTangleMetric H' θ' T' d'_K'' :=
    ⟨hRDT', K'', ins'_K'', hK'', hins'_K'', fun _ _ _ _ => rfl⟩
  have hComp'_K'' := hComp_of_metric d'_K'' hM'_K''
  have hsub1 : T'' ⊆ T' :=
    (theorem_4_1_proof H H' H' K'' K'' θ (4 * lam + 2) (4 * lam + 2) T T'' T' d d'' d'_K''
      ins'' ins'_K'' hS hComp'' hComp'_K'' hK'' hins'' hd'' hK'' hins'_K'' (fun _ _ _ _ => rfl)).2
      rfl rfl le_rfl
  have hsub2 : T' ⊆ T'' :=
    (theorem_4_1_proof H H' H' K'' K'' θ (4 * lam + 2) (4 * lam + 2) T T' T'' d d'_K'' d''
      ins'_K'' ins'' hS hComp'_K'' hComp'' hK'' hins'_K'' (fun _ _ _ _ => rfl) hK'' hins'' hd'').2
      rfl rfl le_rfl
  exact Set.Subset.antisymm hsub1 hsub2

private theorem restrictedSeparation_props {S : Type w} [TopologicalSpace S] {α : Type u} {β : Type
  v}
    {G : Graph α β}
    {H : Drawing S} {η : SpanEmbedding H G}
    {A B : Hypergraph α β} {A_H B_H : Hypergraph S (Set S)}
    (hRestr : IsRestrictedSeparation H G η A B A_H B_H) :
    (∀ e ∈ H.E, e ∈ A_H.edgeSet ↔ η.eMap e ∈ A.edgeSet) ∧
    separationOrder A_H B_H ≤ separationOrder A B ∧
    IsRestrictedSeparation H G η B A B_H A_H := by
  refine ⟨fun e heH => ⟨fun heA => ?_, fun heA => ?_⟩, ?_,
    ⟨hRestr.1.symm, hRestr.2.2.2.1, hRestr.2.2.2.2, hRestr.2.1, hRestr.2.2.1⟩⟩
  · have hmem : η.eMap e ∈ η.eMap '' A_H.edgeSet := ⟨e, heA, rfl⟩
    rw [hRestr.2.2.1] at hmem
    exact hmem.1
  · have hmem : η.eMap e ∈ A.edgeSet ∩ E(η.imageGraph) := ⟨heA, η.bijOn_e.mapsTo heH⟩
    rw [← hRestr.2.2.1] at hmem
    obtain ⟨e', he'A, heq⟩ := hmem
    have he'H : e' ∈ H.E := hRestr.1.left_le.edgeSet_subset he'A
    have : e' = e := η.bijOn_e.injOn he'H heH heq
    exact this ▸ he'A
  · have hsub_img : η.vMap '' (A_H ∩ B_H).vertexSet ⊆ (A ∩ B).vertexSet := by
      rintro x ⟨v, ⟨hvA, hvB⟩, rfl⟩
      have h1 : η.vMap v ∈ η.vMap '' A_H.vertexSet := ⟨v, hvA, rfl⟩
      have h2 : η.vMap v ∈ η.vMap '' B_H.vertexSet := ⟨v, hvB, rfl⟩
      rw [hRestr.2.1] at h1
      rw [hRestr.2.2.2.1] at h2
      exact ⟨h1.1, h2.1⟩
    have hinj : InjOn η.vMap (A_H ∩ B_H).vertexSet :=
      η.bijOn_v.injOn.mono fun v ⟨hvA, _⟩ => hRestr.1.left_le.vertexSet_subset hvA
    calc separationOrder A_H B_H
      _ = (η.vMap '' (A_H ∩ B_H).vertexSet).ncard := (hinj.ncard_image).symm
      _ ≤ separationOrder A B := Set.ncard_le_ncard hsub_img (A ∩ B).vertexSet_finite

/-- Statement of Graph Minors XV, (4.6) (page 126):
"Let $\mathcal{T}, \theta, H, \Sigma, z, \lambda, H', \mathcal{T}'$ be as in (4.5). Let
$\mathcal{T}^*$ be a tangle in a graph $G$, and let $H, \eta, \mathcal{T}$ be a $\Sigma$-span in $G$
with respect to $\mathcal{T}^*$. Let $H'$ be rigid, and let $\eta'$ be an isomorphism from $H'$ to a
subgraph of $G$, such that $\eta'(x) = \eta(x)$ for every vertex or edge $x$ of $H$ with
$d(z, x) > \lambda$. Then $H', \eta', \mathcal{T}'$ is a $\Sigma$-span of order
$\theta - 4\lambda - 2$, obtained from $H, \eta, \mathcal{T}$ by rearranging within $\lambda$ of
$z$." -/
def GM15Theorem46Statement : Prop :=
  ∀ {S : Type w} [TopologicalSpace S] [T2Space S] {α : Type u} {β : Type v}
    (G : Graph α β) (H H' : Drawing S) (η : SpanEmbedding H G) (η' : SpanEmbedding H' G)
    (θ_star θ lam : ℕ) (T_star : Set (Hypergraph α β × Hypergraph α β))
    (T T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (d d' : Set S → Set S → ℕ) (z : Set S),
    IsSigmaSpan G H η θ_star θ T_star T →
    HasTangleMetric H θ T d →
    z ∈ H.A → 2 ≤ lam → 4 * lam + 2 < θ →
    IsRigid H' → (PaintingOrDrawing.drawing H').IsTwoCell →
    (∀ a ∈ H.A, lam < d z a → a ∈ H'.A) →
    (∀ v ∈ H.V, lam < d z {v} → v ∈ H'.V ∧ η'.vMap v = η.vMap v) →
    (∀ e ∈ H.E, lam < d z e → e ∈ H'.E ∧ η'.eMap e = η.eMap e) →
    IsLambdaCompression H H' θ (4 * lam + 2) T T' d d' →
    IsRearrangedWithin G H H' η η' θ_star θ lam T_star T T' d d' z

/-- **Graph Minors XV, (4.6)** (page 126):
If `H, η, T` is a `Σ`-span in `G` with respect to `T*`, `H'` is a rigid 2-cell drawing containing
all atoms `a ∈ A(H)` with `d(z, a) > λ`, `η'` agrees with `η` on vertices and edges with distance
`> λ` from `z`, and `T'` is a `(4λ + 2)`-compression of `T` in `H'`, then `H', η', T'` is a `Σ`-span
obtained from `H, η, T` by rearranging within `λ` of `z`.
Proved from `(4.5)` and Graph Minors XII, `(7.7)`, `(7.10)`, and `(7.11)`. -/
theorem theorem_4_6_proof
     :
    GM15Theorem46Statement.{u, v, w} := by
  intro S _ _ α β G H H' η η' θ_star θ lam T_star T T' d d' z
    hSpan hMetric hz hlam hθ hRigid' h2cell' hAtoms hV hE hComp
  have hS : IsClosedSurface S :=
    ⟨hSpan.isSurface.1, hSpan.isSurface.2.1, fun x =>
      by_contra fun hx => Set.eq_empty_iff_forall_notMem.mp hSpan.bd_empty x hx⟩
  have hConn : ConnectedSpace S := hSpan.isConnected
  let H₀ := deleteAtomNeighborhood H d z lam
  have hE_ne : H.E.Nonempty := by
    by_contra hE_emp
    have hV_le := ncard_V_le_one_of_E_empty hS hMetric.1.1 (Set.not_nonempty_iff_eq_empty.mp hE_emp)
    have hord_le : θ ≤ H.V.ncard := hMetric.1.2.1.order_le_ncard_vertexSet
    omega
  have hH₀_eq : H₀ = H.span ∅ {e ∈ H.E | lam < d z e} := by
    change deleteAtomNeighborhood H d z lam = _
    rw [deleteAtomNeighborhood, ite_eq_right_iff.mpr fun h => False.elim (hE_ne.ne_empty h)]
  have hSubH₀H : H₀.IsSubdrawing H := hH₀_eq ▸ H.span_isSubdrawing _ _
  have h2cell₀ : (PaintingOrDrawing.drawing H₀).IsTwoCell :=
    theorem_4_3_proof H θ lam T d z hS hConn hMetric
      hE_ne hz (by omega) (fun _ => hlam)
  have hEdist₀ : ∀ e ∈ H.E \ H₀.E, d z e ≤ lam := by
    rintro e ⟨heH, henot⟩
    rw [hH₀_eq, H.span_E] at henot
    have : ¬ lam < d z e := fun hlt => henot ⟨⟨heH, hlt⟩, heH⟩
    omega
  obtain ⟨T₀_710, d₀_710, ⟨hM₀_710, hMem₀_710, hDist₀_710⟩, hUniq₀_710⟩ :=
    GraphMinor.GM12.gm14_theorem_7_10.{w} S hS hConn H H₀ θ lam T d z
      (by omega) hMetric hz hSubH₀H h2cell₀ hEdist₀ (fun _ => hlam)
  have hSubEq : θ - 4 * lam - 2 = θ - (4 * lam + 2) := by omega
  rw [hSubEq] at hM₀_710 hMem₀_710 hUniq₀_710
  obtain ⟨hSubH₀H', T₀, T'_45, d₀, d'_45, hComp₀, hComp'_45, hIndEq, hUniq'⟩ :=
    theorem_4_5_proof H H' θ lam T d z hS hConn hMetric hz hlam hθ h2cell' hAtoms
  have hT₀_eq : T₀ = T₀_710 := by
    refine hUniq₀_710 T₀ d₀ hComp₀.hasMetric' (fun a ha b hb a' ha' b' hb' hsub₁ hsub₂ => ?_)
    obtain ⟨σ₁, hσ₁⟩ := atom_nonempty ha
    obtain ⟨σ₂, hσ₂⟩ := atom_nonempty hb
    have hle := hComp₀.dist_le σ₁ σ₂
    rw [pointDist_eq_of_mem_atom ha hb hσ₁ hσ₂,
      pointDist_eq_of_mem_atom ha' hb' (hsub₁ hσ₁) (hsub₂ hσ₂)] at hle
    omega
  subst hT₀_eq
  have hT'_eq : T' = T'_45 := hUniq' T' d' hComp
  subst hT'_eq
  let θ' := θ - (4 * lam + 2)
  have hV_star := hSpan.isControlling.isTangle_star.finite_V
  have hE_star := hSpan.isControlling.isTangle_star.finite_E
  have hForward : ∀ ⦃A B : Hypergraph α β⦄,
      (Hypergraph.ofGraph G hV_star hE_star).IsSeparation A B →
      separationOrder A B < θ' →
      ∀ ⦃A_H' B_H' : Hypergraph S (Set S)⦄,
        IsRestrictedSeparation H' G η' A B A_H' B_H' →
        (A, B) ∈ T_star → (A_H', B_H') ∈ T' := by
    intro A B hsepAB hordAB A_H' B_H' hRestr' hAB_star
    obtain ⟨A_H, B_H, hRestrH, _, _, _, _, hord_H⟩ :=
      GM12.exists_span_restricted_separation hV_star hE_star H η hsepAB
    have he_iff_H := (restrictedSeparation_props hRestrH).1
    obtain ⟨he_iff_H', hord_H', _⟩ := restrictedSeparation_props hRestr'
    have hAH_in_T : (A_H, B_H) ∈ T :=
      (hSpan.isControlling.controls hsepAB (by omega) hRestrH).mp hAB_star
    have hAH₀_in_T₀ : (A_H ∩ H₀.toHypergraph, B_H ∩ H₀.toHypergraph) ∈ T₀ :=
      hMem₀_710 A_H B_H hAH_in_T (lt_of_le_of_lt hord_H hordAB)
    rw [hIndEq]
    refine ⟨hRestr'.1, lt_of_le_of_lt hord_H' hordAB,
      (A_H ∩ H₀.toHypergraph, B_H ∩ H₀.toHypergraph), hAH₀_in_T₀, ?_⟩
    ext e
    change e ∈ A_H.edgeSet ∩ H₀.E ↔ e ∈ A_H'.edgeSet ∩ H₀.E
    refine and_congr_left fun he₀ => ?_
    have he₀' : e ∈ (H.span ∅ {e ∈ H.E | lam < d z e}).E := hH₀_eq ▸ he₀
    rw [H.span_E] at he₀'
    have heH : e ∈ H.E := he₀'.1.1
    have hlt : lam < d z e := he₀'.1.2
    obtain ⟨heH', heMap_eq⟩ := hE e heH hlt
    rw [he_iff_H e heH, he_iff_H' e heH', heMap_eq]
  refine ⟨hz, hSpan, ⟨hSpan.isSurface, hSpan.isConnected, hSpan.bd_empty, hRigid',
    hComp.hasMetric'.1, ⟨by have := hSpan.isControlling.theta_le; omega,
      hSpan.isControlling.isTangle_star, hComp.hasMetric'.1.2.1, ?_⟩⟩,
    hAtoms, hV, hE, hComp⟩
  intro A B hsepAB hordAB A_H' B_H' hRestr'
  refine ⟨hForward hsepAB hordAB hRestr', fun hAB' => ?_⟩
  by_contra hnot
  have hord_star : separationOrder A B < θ_star := by
    have := hSpan.isControlling.theta_le
    omega
  have hBA_star : (B, A) ∈ T_star :=
    (hSpan.isControlling.isTangle_star.isTangle.axiom1 hsepAB hord_star).resolve_left hnot
  have hRestr'_symm := (restrictedSeparation_props hRestr').2.2
  have hBA' : (B_H', A_H') ∈ T' :=
    hForward hsepAB.symm (by rwa [separationOrder_comm]) hRestr'_symm hBA_star
  exact GM10.theorem_2_1_proof hComp.hasMetric'.1.2.1 hAB' hBA'

/-- Every walk in a graph contains a simple walk with the same ends and a subset of vertices. -/
private theorem exists_simple_subwalk {α β : Type*} {G : Graph α β} {u v : α}
    (W : GraphWalk G u v) :
    ∃ W' : GraphWalk G u v, W'.IsSimple ∧ ∀ w ∈ W'.support, w ∈ W.support := by
  induction W with
  | nil h =>
    exact ⟨.nil h, List.nodup_singleton _, fun _ hw => hw⟩
  | @cons u' w' v' e' h r ih =>
    obtain ⟨r', hr'_sim, hr'_sub⟩ := ih
    by_cases hu : u' ∈ r'.support
    · obtain ⟨W₁, W₂, h_eq⟩ := r'.exists_append_of_mem hu
      have hnodup : (W₁.support ++ W₂.support.tail).Nodup := by
        rw [← W₁.support_append W₂, ← h_eq]
        exact hr'_sim
      obtain ⟨_, htail, hdisj⟩ := List.nodup_append.mp hnodup
      have hu_not_tail : u' ∉ W₂.support.tail :=
        fun hmem => hdisj u' W₁.end_mem_support u' hmem rfl
      have hW₂_sim : W₂.IsSimple := by
        unfold GraphWalk.IsSimple
        rw [W₂.support_eq_cons]
        exact List.nodup_cons.mpr ⟨hu_not_tail, htail⟩
      refine ⟨W₂, hW₂_sim, fun w hw => List.mem_cons_of_mem _ (hr'_sub w ?_)⟩
      rw [h_eq, W₁.mem_support_append W₂]
      exact Or.inr hw
    · refine ⟨.cons h r', List.nodup_cons.mpr ⟨hu, hr'_sim⟩, fun w hw => ?_⟩
      rcases List.mem_cons.mp hw with rfl | hw
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (hr'_sub w hw)

private theorem split_separation_left {S : Type w} {J A B A₁ A₂ : Hypergraph S (Set S)}
    (hsep : J.IsSeparation A B) (h₁ : A₁ ≤ J) (h₂ : A₂ ≤ J)
    (hV : A₁.vertexSet ∪ A₂.vertexSet = A.vertexSet)
    (hE : A₁.edgeSet ∪ A₂.edgeSet = A.edgeSet)
    (hDisj : Disjoint A₁.edgeSet A₂.edgeSet) :
    J.IsSeparation A₁ (A₂ ∪ B) := by
  apply (isSeparation_iff_of_le h₁ (union_le h₂ hsep.right_le)).mpr
  refine ⟨?_, ?_, ?_⟩
  · change A₁.vertexSet ∪ (A₂.vertexSet ∪ B.vertexSet) = J.vertexSet
    rw [← Set.union_assoc, hV, hsep.vertexSet_union]
  · change A₁.edgeSet ∪ (A₂.edgeSet ∪ B.edgeSet) = J.edgeSet
    rw [← Set.union_assoc, hE, hsep.edgeSet_union]
  · change A₁.edgeSet ∩ (A₂.edgeSet ∪ B.edgeSet) = ∅
    refine (disjoint_union_right.mpr ⟨hDisj, ?_⟩).inter_eq
    exact (disjoint_iff_inter_eq_empty.mpr hsep.edgeSet_inter_eq).mono_left (hE ▸ subset_union_left)

/-- Statement of Graph Minors XV, (4.7) (page 127):
"Let $\mathcal{T}$ be a respectful tangle of order $\theta$ in a 2-cell drawing $H$ in a surface
$\Sigma$. Let $z \in A(H)$, let $\lambda \ge 2$ be an integer, and let $X \subseteq V(H)$ be free
with respect to $\mathcal{T}$. Suppose that $d(z, v) > 2|X| + 5\lambda + 2$ for all $v \in X$. Now
let $H'$ be a 2-cell drawing in $\Sigma$ such that $a \in A(H')$ for every $a \in A(H)$ with
$d(z, a) > \lambda$; and let $\mathcal{T}'$ be a $(4\lambda + 2)$-compression of $\mathcal{T}$ in
$H'$. Then $X$ is free with respect to $\mathcal{T}'$." -/
def GM15Theorem47Statement : Prop :=
  ∀ {S : Type w} [TopologicalSpace S] [T2Space S]
    (H H' : Drawing S) (θ lam : ℕ)
    (T T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (d d' : Set S → Set S → ℕ) (z : Set S) (X : Set S),
    IsClosedSurface S → ConnectedSpace S →
    HasTangleMetric H θ T d → z ∈ H.A → 2 ≤ lam →
    IsFreeSet H.toHypergraph T θ X →
    (∀ v ∈ X, 2 * X.ncard + 5 * lam + 2 < d z {v}) →
    (PaintingOrDrawing.drawing H').IsTwoCell →
    (∀ a ∈ H.A, lam < d z a → a ∈ H'.A) →
    IsLambdaCompression H H' θ (4 * lam + 2) T T' d d' →
    IsFreeSet H'.toHypergraph T' (θ - (4 * lam + 2)) X

private theorem small_separation_side_is_walk_connected
    {S : Type w}
    [TopologicalSpace S]
    (H' : Drawing S)
    (T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (X : Set S)
    (θ' : ℕ)
    (hT' : IsTangle H'.toHypergraph θ' T')
    (n : ℕ)
    (ih : ∀ m < n, ∀ (A B : Hypergraph S (Set S)), A.vertexSet.ncard = m → (A, B) ∈ T' → (X ∩
      A.vertexSet).ncard ≤ A.separationOrder B)
    (A : Hypergraph S (Set S))
    (B : Hypergraph S (Set S))
    (hn : A.vertexSet.ncard = n)
    (hAB : (A, B) ∈ T')
    (hsepAB : H'.toHypergraph.IsSeparation A B)
    (hordAB : A.separationOrder B < θ')
    (hfinA_V : A.vertexSet.Finite)
    (hgt : ¬(X ∩ A.vertexSet).ncard ≤ A.separationOrder B)
    (v : S)
    (V₁ : Set S)
    (hV₁_sub : V₁ ⊆ A.vertexSet)
    (hvV₁ : v ∈ V₁)
    (hEndsE₁ : ∀ e ∈ ({e | e ∈ A.edgeSet ∧ ∃ w ∈ V₁, H'.toHypergraph.Inc e w}), ∀ (u : S),
      H'.toHypergraph.Inc e u → u ∈ V₁) :
    A.vertexSet = V₁ := by
  let E₁ := {e | e ∈ A.edgeSet ∧ ∃ w ∈ V₁, H'.toHypergraph.Inc e w}
  let V₂ := A.vertexSet \ V₁
  let E₂ := A.edgeSet \ E₁
  apply Set.Subset.antisymm _ hV₁_sub
  intro u₀ hu₀A
  by_contra hu₀_not
  have hu₀V₂ : u₀ ∈ V₂ := ⟨hu₀A, hu₀_not⟩
  let A₁ : Hypergraph S (Set S) :=
    { vertexSet := V₁
      edgeSet := E₁
      Inc e u := H'.toHypergraph.Inc e u ∧ e ∈ E₁
      vertex_mem_of_inc e u h := hEndsE₁ e h.2 u h.1
      edge_mem_of_inc _ _ h := h.2
      vertexSet_finite := hfinA_V.subset hV₁_sub
      edgeSet_finite := (H'.finite_edges.subset hsepAB.left_le.edgeSet_subset).subset
        fun _ h => h.1 }
  let A₂ : Hypergraph S (Set S) :=
    { vertexSet := V₂
      edgeSet := E₂
      Inc e u := H'.toHypergraph.Inc e u ∧ e ∈ E₂
      vertex_mem_of_inc e u h := by
        have huA : u ∈ A.vertexSet := by
          have : u ∈ A.ends e := by rw [← hsepAB.left_le.ends_eq e h.2.1]; exact h.1
          exact A.vertex_mem_of_inc this
        exact ⟨huA, fun huV₁ => h.2.2 ⟨h.2.1, u, huV₁, h.1⟩⟩
      edge_mem_of_inc _ _ h := h.2
      vertexSet_finite := hfinA_V.subset sdiff_subset
      edgeSet_finite := (H'.finite_edges.subset hsepAB.left_le.edgeSet_subset).subset
        sdiff_subset }
  have hA₁_le : A₁ ≤ H'.toHypergraph := by
    refine ⟨fun u h => hsepAB.left_le.vertexSet_subset (hV₁_sub h),
      fun e h => hsepAB.left_le.edgeSet_subset h.1, fun e he => ?_⟩
    ext u
    exact ⟨fun h => ⟨h, he⟩, fun h => h.1⟩
  have hA₂_le : A₂ ≤ H'.toHypergraph := by
    refine ⟨fun u h => hsepAB.left_le.vertexSet_subset h.1,
      fun e h => hsepAB.left_le.edgeSet_subset h.1, fun e he => ?_⟩
    ext u
    exact ⟨fun h => ⟨h, he⟩, fun h => h.1⟩
  have hVpartition : A₁.vertexSet ∪ A₂.vertexSet = A.vertexSet := by
    change V₁ ∪ (A.vertexSet \ V₁) = A.vertexSet
    ext x
    constructor
    · exact fun h => h.elim (fun hx => hV₁_sub hx) And.left
    · exact fun hx => (em (x ∈ V₁)).imp_right fun hn => ⟨hx, hn⟩
  have hEpartition : A₁.edgeSet ∪ A₂.edgeSet = A.edgeSet := by
    change E₁ ∪ (A.edgeSet \ E₁) = A.edgeSet
    ext e
    constructor
    · exact fun h => h.elim And.left And.left
    · exact fun he => (em (e ∈ E₁)).imp_right fun hn => ⟨he, hn⟩
  have hDisj : Disjoint A₁.edgeSet A₂.edgeSet :=
    disjoint_left.mpr fun e he₁ he₂ => he₂.2 he₁
  have hsep₁ : H'.toHypergraph.IsSeparation A₁ (A₂ ∪ B) :=
    split_separation_left hsepAB hA₁_le hA₂_le hVpartition hEpartition hDisj
  have hsep₂ : H'.toHypergraph.IsSeparation A₂ (A₁ ∪ B) :=
    split_separation_left hsepAB hA₂_le hA₁_le ((Set.union_comm _ _).trans hVpartition)
      ((Set.union_comm _ _).trans hEpartition) hDisj.symm
  have hinter₁ : (A₁ ∩ (A₂ ∪ B)).vertexSet = V₁ ∩ B.vertexSet := by
    ext x
    change (x ∈ V₁ ∧ (x ∈ V₂ ∨ x ∈ B.vertexSet)) ↔ x ∈ V₁ ∩ B.vertexSet
    exact ⟨fun ⟨hx₁, hx₂⟩ => ⟨hx₁, hx₂.resolve_left fun h => h.2 hx₁⟩,
      fun ⟨hx₁, hxB⟩ => ⟨hx₁, Or.inr hxB⟩⟩
  have hinter₂ : (A₂ ∩ (A₁ ∪ B)).vertexSet = V₂ ∩ B.vertexSet := by
    ext x
    change (x ∈ V₂ ∧ (x ∈ V₁ ∨ x ∈ B.vertexSet)) ↔ x ∈ V₂ ∩ B.vertexSet
    exact ⟨fun ⟨hx₂, hx₁⟩ => ⟨hx₂, hx₁.resolve_left fun h => hx₂.2 h⟩,
      fun ⟨hx₂, hxB⟩ => ⟨hx₂, Or.inr hxB⟩⟩
  have hord_sum : separationOrder A₁ (A₂ ∪ B) + separationOrder A₂ (A₁ ∪ B) =
      separationOrder A B := by
    change (A₁ ∩ (A₂ ∪ B)).vertexSet.ncard + (A₂ ∩ (A₁ ∪ B)).vertexSet.ncard =
      (A ∩ B).vertexSet.ncard
    have hdisj : Disjoint (V₁ ∩ B.vertexSet) (V₂ ∩ B.vertexSet) :=
      Set.disjoint_left.mpr fun x ⟨hx₁, _⟩ ⟨hx₂, _⟩ => hx₂.2 hx₁
    have hfin₁ : (V₁ ∩ B.vertexSet).Finite :=
      (hfinA_V.subset hV₁_sub).subset inter_subset_left
    have hfin₂ : (V₂ ∩ B.vertexSet).Finite :=
      (hfinA_V.subset sdiff_subset).subset inter_subset_left
    rw [hinter₁, hinter₂, ← Set.ncard_union_eq hdisj hfin₁ hfin₂]
    congr 1
    ext x
    exact ⟨by
      rintro (⟨hx, hxB⟩ | ⟨hx, hxB⟩)
      · exact ⟨hV₁_sub hx, hxB⟩
      · exact ⟨hx.1, hxB⟩,
      fun ⟨hxA, hxB⟩ => by
        by_cases hx₁ : x ∈ V₁
        · exact Or.inl ⟨hx₁, hxB⟩
        · exact Or.inr ⟨⟨hxA, hx₁⟩, hxB⟩⟩
  have hmem₁ : (A₁, A₂ ∪ B) ∈ T' :=
    GM10.theorem_2_9_proof hT' hAB hsep₁ (by omega) (Or.inr (Or.inl hV₁_sub))
  have hmem₂ : (A₂, A₁ ∪ B) ∈ T' :=
    GM10.theorem_2_9_proof hT' hAB hsep₂ (by omega) (Or.inr (Or.inl sdiff_subset))
  have hV_sum : V₁.ncard + V₂.ncard = n := by
    have hdisj : Disjoint V₁ V₂ :=
      Set.disjoint_left.mpr fun x hx₁ hx₂ => hx₂.2 hx₁
    rw [← hn, ← Set.ncard_union_eq hdisj
      (hfinA_V.subset hV₁_sub) (hfinA_V.subset sdiff_subset)]
    exact congrArg Set.ncard hVpartition
  have hV₁_pos : 0 < V₁.ncard :=
    (Set.ncard_pos (hfinA_V.subset hV₁_sub)).mpr ⟨v, hvV₁⟩
  have hV₂_pos : 0 < V₂.ncard :=
    (Set.ncard_pos (hfinA_V.subset sdiff_subset)).mpr ⟨u₀, hu₀V₂⟩
  have hle₁ := ih V₁.ncard (by omega) A₁ (A₂ ∪ B) rfl hmem₁
  have hle₂ := ih V₂.ncard (by omega) A₂ (A₁ ∪ B) rfl hmem₂
  have hX_sum : (X ∩ A₁.vertexSet).ncard + (X ∩ A₂.vertexSet).ncard =
      (X ∩ A.vertexSet).ncard := by
    change (X ∩ V₁).ncard + (X ∩ V₂).ncard = (X ∩ A.vertexSet).ncard
    have hdisj : Disjoint (X ∩ V₁) (X ∩ V₂) :=
      Set.disjoint_left.mpr fun x ⟨_, hx₁⟩ ⟨_, hx₂⟩ => hx₂.2 hx₁
    have hfin₁ : (X ∩ V₁).Finite :=
      (hfinA_V.subset hV₁_sub).subset inter_subset_right
    have hfin₂ : (X ∩ V₂).Finite :=
      (hfinA_V.subset sdiff_subset).subset inter_subset_right
    rw [← Set.ncard_union_eq hdisj hfin₁ hfin₂]
    congr 1
    ext x
    exact ⟨by
      rintro (⟨hxX, hx⟩ | ⟨hxX, hx⟩)
      · exact ⟨hxX, hV₁_sub hx⟩
      · exact ⟨hxX, hx.1⟩,
      fun ⟨hxX, hxA⟩ => by
        by_cases hx₁ : x ∈ V₁
        · exact Or.inl ⟨hxX, hx₁⟩
        · exact Or.inr ⟨hxX, ⟨hxA, hx₁⟩⟩⟩
  omega

private theorem walk_component_contains_both_edge_ends
    {S : Type w}
    [TopologicalSpace S]
    (H' : Drawing S)
    (A : Hypergraph S (Set S))
    (B : Hypergraph S (Set S))
    (hsepAB : H'.toHypergraph.IsSeparation A B)
    (v : S)
    (V₁ : Set S)
    (hV₁ : V₁ = {u ∈ A.vertexSet | ∃ W : GraphWalk H'.toGraph u v,
      (∀ w ∈ W.support, w ∈ A.vertexSet) ∧ (∀ e ∈ W.edges, e ∈ A.edgeSet)}) :
    ∀ e ∈ {e | e ∈ A.edgeSet ∧ ∃ w ∈ V₁, H'.toHypergraph.Inc e w}, ∀ u : S,
      H'.toHypergraph.Inc e u → u ∈ V₁ := by
  subst V₁
  rintro e ⟨heA, w, ⟨hwA, Ww, hWw_V, hWw_E⟩, he_w⟩ u he_u
  have huA : u ∈ A.vertexSet := by
    have : u ∈ A.ends e := by rw [← hsepAB.left_le.ends_eq e heA]; exact he_u
    exact A.vertex_mem_of_inc this
  by_cases huw : u = w
  · exact huw ▸ ⟨hwA, Ww, hWw_V, hWw_E⟩
  · have he' : e ∈ H'.E := he_u.1
    have hpair_eq : closure e ∩ H'.V = {u, w} := by
      rcases H'.edge_cond e he' with ⟨a, b, _, hcl, _⟩ | ⟨a, hcl, _⟩
      · have hu_ab : u = a ∨ u = b := by
          have : u ∈ ({a, b} : Set S) := hcl ▸ ⟨he_u.2.2, he_u.2.1⟩
          simpa using this
        have hw_ab : w = a ∨ w = b := by
          have : w ∈ ({a, b} : Set S) := hcl ▸ ⟨he_w.2.2, he_w.2.1⟩
          simpa using this
        rw [hcl]
        rcases hu_ab with rfl | rfl <;> rcases hw_ab with rfl | rfl
        · exact False.elim (huw rfl)
        · rfl
        · exact Set.pair_comm _ _
        · exact False.elim (huw rfl)
      · have hu_a : u = a := by
          have : u ∈ ({a} : Set S) := hcl ▸ ⟨he_u.2.2, he_u.2.1⟩
          simpa using this
        have hw_a : w = a := by
          have : w ∈ ({a} : Set S) := hcl ▸ ⟨he_w.2.2, he_w.2.1⟩
          simpa using this
        exact False.elim (huw (hu_a.trans hw_a.symm))
    have hlink : H'.toGraph.IsLink e u w := ⟨he', he_u.2.1, he_w.2.1, hpair_eq⟩
    refine ⟨huA, .cons hlink Ww, fun x hx => ?_, fun f hf => ?_⟩
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact huA
      · exact hWw_V x hx
    · rcases List.mem_cons.mp hf with rfl | hf
      · exact heA
      · exact hWw_E f hf

private theorem small_side_vertices_are_far_from_deleted_atom
    {S : Type w}
    [TopologicalSpace S]
    [T2Space S]
    (H : Drawing S)
    (H' : Drawing S)
    (θ : ℕ)
    (lam : ℕ)
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (d : Set S → Set S → ℕ)
    (d' : Set S → Set S → ℕ)
    (z : Set S)
    (X : Set S)
    (hS : IsClosedSurface S)
    (hz : z ∈ H.A)
    (hFree : IsFreeSet H.toHypergraph T θ X)
    (hDistX : ∀ v ∈ X, 2 * X.ncard + 5 * lam + 2 < d z {v})
    (hAtoms : ∀ a ∈ H.A, lam < d z a → a ∈ H'.A)
    (hComp : IsLambdaCompression H H' θ (4 * lam + 2) T T' d d')
    (hd_tri : ∀ a ∈ H.A, ∀ b ∈ H.A, ∀ c ∈ H.A, d a c ≤ d a b + d b c)
    (A : Hypergraph S (Set S))
    (B : Hypergraph S (Set S))
    (hsepAB : H'.toHypergraph.IsSeparation A B)
    (v : S)
    (hvX : v ∈ X)
    (hvH' : v ∈ H'.V)
    (hClaim2 : ∀ u ∈ A.vertexSet, d' {u} {v} ≤ 2 * A.separationOrder B)
    (hord_lt_X : A.separationOrder B < X.ncard) :
    ∀ u ∈ A.vertexSet, u ∈ H.V ∧ lam + 2 < d z {u} := by
  intro u huA
  have huH' : u ∈ H'.V := hsepAB.left_le.vertexSet_subset huA
  have hvH : v ∈ H.V := hFree.1 hvX
  have hd'_uv := hClaim2 u huA
  obtain ⟨au, hau, hu_au⟩ := exists_atom_of_point H u
  have hcomp_uv := hComp.dist_le u v
  rw [pointDist_eq_of_mem_atom (d := d) hau (Or.inl (Or.inl ⟨v, hvH, rfl⟩)) hu_au
      (Set.mem_singleton v),
    pointDist_eq_of_mem_atom (d := d') (Or.inl (Or.inl ⟨u, huH', rfl⟩))
      (Or.inl (Or.inl ⟨v, hvH', rfl⟩))
      (Set.mem_singleton u) (Set.mem_singleton v)] at hcomp_uv
  dsimp at hcomp_uv
  have htri_z := hd_tri z hz au hau {v} (Or.inl (Or.inl ⟨v, hvH, rfl⟩))
  have hzv := hDistX v hvX
  have hlt_au : lam + 2 < d z au := by omega
  have hau_H' : au ∈ H'.A := hAtoms au hau (by omega)
  have hau_eq : au = {u} :=
    atom_eq_of_mem hau_H' (Or.inl (Or.inl ⟨u, huH', rfl⟩)) hu_au (Set.mem_singleton u)
  rw [hau_eq] at hau hlt_au
  exact ⟨vertex_mem_V_of_mem_A hS huH' hau, hlt_au⟩

private theorem small_side_edges_survive_deletion
    {S : Type w}
    [TopologicalSpace S]
    [T2Space S]
    (H : Drawing S)
    (H' : Drawing S)
    (θ : ℕ)
    (lam : ℕ)
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (d : Set S → Set S → ℕ)
    (d' : Set S → Set S → ℕ)
    (z : Set S)
    (X : Set S)
    (hS : IsClosedSurface S)
    (hz : z ∈ H.A)
    (hFree : IsFreeSet H.toHypergraph T θ X)
    (hDistX : ∀ v ∈ X, 2 * X.ncard + 5 * lam + 2 < d z {v})
    (hAtoms : ∀ a ∈ H.A, lam < d z a → a ∈ H'.A)
    (hComp : IsLambdaCompression H H' θ (4 * lam + 2) T T' d d')
    (hd_tri : ∀ a ∈ H.A, ∀ b ∈ H.A, ∀ c ∈ H.A, d a c ≤ d a b + d b c)
    (hd'_symm : ∀ a ∈ H'.A, ∀ b ∈ H'.A, d' a b = d' b a)
    (hd'_tri : ∀ a ∈ H'.A, ∀ b ∈ H'.A, ∀ c ∈ H'.A, d' a c ≤ d' a b + d' b c)
    (hd'_inc : (H'.E.Nonempty → ∀ v ∈ H'.V, ∀ r ∈ H'.R, v ∈ closure r → d' {v} r ≤ 1) ∧ ∀ v ∈
      H'.V, ∀ e ∈ H'.E, v ∈ closure e → d' {v} e ≤ 2)
    (hH₀_eq : (deleteAtomNeighborhood H d z lam) = H.span ∅ {e | e ∈ H.E ∧ lam < d z e})
    (A : Hypergraph S (Set S))
    (B : Hypergraph S (Set S))
    (hsepAB : H'.toHypergraph.IsSeparation A B)
    (v : S)
    (hvX : v ∈ X)
    (hvH' : v ∈ H'.V)
    (hClaim2 : ∀ u ∈ A.vertexSet, d' {u} {v} ≤ 2 * A.separationOrder B)
    (hord_lt_X : A.separationOrder B < X.ncard) :
    ∀ u ∈ A.vertexSet, ∀ e ∈ H'.E, u ∈ closure e → e ∈ (deleteAtomNeighborhood H d z lam).E := by
  let H₀ := deleteAtomNeighborhood H d z lam
  intro u huA e he' hue
  have huH' : u ∈ H'.V := hsepAB.left_le.vertexSet_subset huA
  have hvH : v ∈ H.V := hFree.1 hvX
  have hd'_uv := hClaim2 u huA
  have hd'_ue : d' {u} e ≤ 2 := hd'_inc.2 u huH' e he' hue
  have hd'_ev : d' e {v} ≤ 2 * X.ncard := by
    have h1 := hd'_tri e (Or.inl (Or.inr he')) {u} (Or.inl (Or.inl ⟨u, huH', rfl⟩))
      {v} (Or.inl (Or.inl ⟨v, hvH', rfl⟩))
    have h2 := hd'_symm {u} (Or.inl (Or.inl ⟨u, huH', rfl⟩)) e (Or.inl (Or.inr he'))
    omega
  obtain ⟨σ, hσe⟩ := atom_nonempty (Or.inl (Or.inr he') : e ∈ H'.A)
  obtain ⟨aσ, haσ, hσ_aσ⟩ := exists_atom_of_point H σ
  have hcomp_σv := hComp.dist_le σ v
  rw [pointDist_eq_of_mem_atom (d := d) haσ (Or.inl (Or.inl ⟨v, hvH, rfl⟩)) hσ_aσ
      (Set.mem_singleton v),
    pointDist_eq_of_mem_atom (d := d') (Or.inl (Or.inr he'))
      (Or.inl (Or.inl ⟨v, hvH', rfl⟩))
      hσe (Set.mem_singleton v)] at hcomp_σv
  dsimp at hcomp_σv
  have htri_z := hd_tri z hz aσ haσ {v} (Or.inl (Or.inl ⟨v, hvH, rfl⟩))
  have hzv := hDistX v hvX
  have hlt_aσ : lam < d z aσ := by omega
  have haσ_H' : aσ ∈ H'.A := hAtoms aσ haσ hlt_aσ
  have haσ_eq : aσ = e :=
    atom_eq_of_mem haσ_H' (Or.inl (Or.inr he')) hσ_aσ hσe
  rw [haσ_eq] at haσ hlt_aσ
  have heH : e ∈ H.E := edge_mem_E_of_mem_A hS he' haσ
  rw [hH₀_eq, H.span_E]
  exact ⟨⟨heH, hlt_aσ⟩, heH⟩

private theorem lifted_small_side_belongs_to_original_tangle
    {S : Type w}
    [TopologicalSpace S]
    [T2Space S]
    (H : Drawing S)
    (H' : Drawing S)
    (θ : ℕ)
    (lam : ℕ)
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (d : Set S → Set S → ℕ)
    (z : Set S)
    (X : Set S)
    (hMetric : HasTangleMetric H θ T d)
    (hlam : 2 ≤ lam)
    (hθ : 4 * lam + 2 < θ)
    (v₀ : S)
    (hv₀_le_θ : d z {v₀} ≤ θ)
    (hv₀_gt : 2 * X.ncard + 5 * lam + 2 < d z {v₀})
    (hSubH₀H : (deleteAtomNeighborhood H d z lam).IsSubdrawing H)
    (hSubH₀H' : (deleteAtomNeighborhood H d z lam).IsSubdrawing H')
    (T₀ : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (hMem₀_710 : ∀ (A B : Hypergraph S (Set S)), (A, B) ∈ T → A.separationOrder B < θ - (4 * lam +
      2) → (A ∩ (deleteAtomNeighborhood H d z lam).toHypergraph, B ∩ (deleteAtomNeighborhood H d z
      lam).toHypergraph) ∈ T₀)
    (hIndEq : T' = inducedTangle H'.toHypergraph (deleteAtomNeighborhood H d z lam).toHypergraph
      T₀ (θ - (4 * lam + 2)))
    (hT' : IsTangle H'.toHypergraph (θ - (4 * lam + 2)) T')
    (A : Hypergraph S (Set S))
    (B : Hypergraph S (Set S))
    (hAB : (A, B) ∈ T')
    (hsepAB : H'.toHypergraph.IsSeparation A B)
    (hordAB : A.separationOrder B < (θ - (4 * lam + 2)))
    (hord_lt_X : A.separationOrder B < X.ncard)
    (C : Hypergraph S (Set S))
    (hCE : C.edgeSet = H.E \ A.edgeSet)
    (hsepAC : H.toHypergraph.IsSeparation A C)
    (hordAC_eq : A.separationOrder C = A.separationOrder B)
    (hordAC_lt : A.separationOrder C < (θ - (4 * lam + 2))) :
    (A, C) ∈ T := by
  let θ' := θ - (4 * lam + 2)
  let H₀ := deleteAtomNeighborhood H d z lam
  rcases hMetric.1.2.1.axiom1 hsepAC (by omega) with hAC | hCA
  · exact hAC
  · have hCA₀ : (C ∩ H₀.toHypergraph, A ∩ H₀.toHypergraph) ∈ T₀ :=
      hMem₀_710 C A hCA (by rwa [separationOrder_comm])
    have hBA_in_T' : (B, A) ∈ T' := by
      rw [hIndEq]
      refine ⟨hsepAB.symm, by rwa [separationOrder_comm],
        (C ∩ H₀.toHypergraph, A ∩ H₀.toHypergraph), hCA₀, ?_⟩
      ext e
      change e ∈ C.edgeSet ∩ H₀.E ↔ e ∈ B.edgeSet ∩ H₀.E
      rw [hCE]
      refine and_congr_left fun he₀ => ?_
      have heH : e ∈ H.E := hSubH₀H.2 he₀
      have he' : e ∈ H'.E := hSubH₀H'.2 he₀
      have he_u : e ∈ A.edgeSet ∪ B.edgeSet := hsepAB.edgeSet_union.symm ▸ he'
      constructor
      · rintro ⟨_, henotA⟩
        exact he_u.resolve_left henotA
      · intro heB
        exact ⟨heH, fun heA => hsepAB.notMem_edgeSet_right heA heB⟩
    exact False.elim (GM10.theorem_2_1_proof hT' hAB hBA_in_T')

private theorem compressed_tangle_small_sides_respect_free_set
    {S : Type w}
    [TopologicalSpace S]
    [T2Space S]
    (H : Drawing S)
    (H' : Drawing S)
    (θ : ℕ)
    (lam : ℕ)
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (d : Set S → Set S → ℕ)
    (d' : Set S → Set S → ℕ)
    (z : Set S)
    (X : Set S)
    (hS : IsClosedSurface S)
    [hConn : ConnectedSpace S]
    (hMetric : HasTangleMetric H θ T d)
    (hz : z ∈ H.A)
    (hlam : 2 ≤ lam)
    (hFree : IsFreeSet H.toHypergraph T θ X)
    (hDistX : ∀ v ∈ X, 2 * X.ncard + 5 * lam + 2 < d z {v})
    (hAtoms : ∀ a ∈ H.A, lam < d z a → a ∈ H'.A)
    (hComp : IsLambdaCompression H H' θ (4 * lam + 2) T T' d d')
    (hθ : 4 * lam + 2 < θ)
    (hd_symm : ∀ a ∈ H.A, ∀ b ∈ H.A, d a b = d b a)
    (hd_tri : ∀ a ∈ H.A, ∀ b ∈ H.A, ∀ c ∈ H.A, d a c ≤ d a b + d b c)
    (hd_inc : (H.E.Nonempty → ∀ v ∈ H.V, ∀ r ∈ H.R, v ∈ closure r → d {v} r ≤ 1) ∧ ∀ v ∈ H.V, ∀ e
      ∈ H.E, v ∈ closure e → d {v} e ≤ 2)
    (hd'_refl : ∀ a ∈ H'.A, d' a a = 0)
    (hd'_symm : ∀ a ∈ H'.A, ∀ b ∈ H'.A, d' a b = d' b a)
    (hd'_tri : ∀ a ∈ H'.A, ∀ b ∈ H'.A, ∀ c ∈ H'.A, d' a c ≤ d' a b + d' b c)
    (hd'_inc : (H'.E.Nonempty → ∀ v ∈ H'.V, ∀ r ∈ H'.R, v ∈ closure r → d' {v} r ≤ 1) ∧ ∀ v ∈
      H'.V, ∀ e ∈ H'.E, v ∈ closure e → d' {v} e ≤ 2)
    (v₀ : S)
    (hv₀_le_θ : d z {v₀} ≤ θ)
    (hv₀_gt : 2 * X.ncard + 5 * lam + 2 < d z {v₀})
    (hH₀_eq : (deleteAtomNeighborhood H d z lam) = H.span ∅ {e | e ∈ H.E ∧ lam < d z e})
    (hSubH₀H : (deleteAtomNeighborhood H d z lam).IsSubdrawing H)
    (hSubH₀H' : (deleteAtomNeighborhood H d z lam).IsSubdrawing H')
    (T₀ : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (hMem₀_710 : ∀ (A B : Hypergraph S (Set S)), (A, B) ∈ T → A.separationOrder B < θ - (4 * lam +
      2) → (A ∩ (deleteAtomNeighborhood H d z lam).toHypergraph, B ∩ (deleteAtomNeighborhood H d z
      lam).toHypergraph) ∈ T₀)
    (hIndEq : T' = inducedTangle H'.toHypergraph (deleteAtomNeighborhood H d z lam).toHypergraph
      T₀ (θ - (4 * lam + 2)))
    (hT' : IsTangle H'.toHypergraph (θ - (4 * lam + 2)) T') :
    ∀ (n : ℕ) (A B : Hypergraph S (Set S)), A.vertexSet.ncard = n → (A, B) ∈ T' → (X ∩
      A.vertexSet).ncard ≤ A.separationOrder B := by
  let θ' := θ - (4 * lam + 2)
  let H₀ := deleteAtomNeighborhood H d z lam
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro A B hn hAB
    have hsepAB : H'.toHypergraph.IsSeparation A B := hT'.isSeparation hAB
    have hordAB : separationOrder A B < θ' := hT'.order_lt hAB
    have hfinA_V : A.vertexSet.Finite := H'.finite_V.subset hsepAB.left_le.vertexSet_subset
    by_contra hgt
    have hlt_ord : separationOrder A B < (X ∩ A.vertexSet).ncard := Nat.lt_of_not_le hgt
    have hXA_ne : (X ∩ A.vertexSet).Nonempty :=
      (Set.ncard_pos (hfinA_V.subset inter_subset_right)).mp (by omega)
    obtain ⟨v, hvX, hvA⟩ := hXA_ne
    have hvH' : v ∈ H'.V := hsepAB.left_le.vertexSet_subset hvA
    let V₁ : Set S :=
      {u ∈ A.vertexSet | ∃ W : GraphWalk H'.toGraph u v,
        (∀ w ∈ W.support, w ∈ A.vertexSet) ∧ (∀ e ∈ W.edges, e ∈ A.edgeSet)}
    have hV₁_sub : V₁ ⊆ A.vertexSet := fun _ h => h.1
    let E₁ : Set (Set S) := {e ∈ A.edgeSet | ∃ w ∈ V₁, H'.toHypergraph.Inc e w}
    let V₂ : Set S := A.vertexSet \ V₁
    let E₂ : Set (Set S) := A.edgeSet \ E₁
    have hvV₁ : v ∈ V₁ :=
      ⟨hvA, .nil hvH',
        fun w hw => (List.mem_singleton.mp hw) ▸ hvA,
        fun _ he => False.elim (List.not_mem_nil he)⟩
    have hEndsE₁ : ∀ e ∈ E₁, ∀ u, H'.toHypergraph.Inc e u → u ∈ V₁ := by
      exact walk_component_contains_both_edge_ends (S := S) H' A B hsepAB v V₁ rfl
    -- Claim (1): every vertex of `A` belongs to `V₁` (`A` is connected).
    have hV₁_eq : A.vertexSet = V₁ := by
      exact small_separation_side_is_walk_connected (S := S) H' T' X θ' hT' n ih
        A B hn hAB hsepAB hordAB hfinA_V hgt v V₁ hV₁_sub hvV₁ hEndsE₁
    -- Claim (2): for every `u ∈ V(A)`, `d' {u} {v} ≤ 2 * separationOrder A B`.
    have hClaim2 : ∀ u ∈ A.vertexSet, d' {u} {v} ≤ 2 * separationOrder A B := by
      intro u huA
      have huH' : u ∈ H'.V := hsepAB.left_le.vertexSet_subset huA
      by_cases huv : u = v
      · subst huv
        rw [hd'_refl {u} (Or.inl (Or.inl ⟨u, huH', rfl⟩))]
        omega
      · obtain ⟨_, ⟨W, hW_V, _⟩⟩ : u ∈ V₁ := hV₁_eq ▸ huA
        obtain ⟨W', hW'_sim, hW'_sub⟩ := exists_simple_subwalk W
        let P := walkDrawing H' W'
        have hP_path : P.IsPathBetween u v := GM11.walkDrawing_isPathBetween H' hW'_sim
        have hP_sub : P.IsSubdrawing H' := GM11.walkDrawing_isSubdrawing H' W'
        have hP_V : P.V ⊆ A.vertexSet := by
          rw [GM11.walkDrawing_V]
          exact fun x hx => hW_V x (hW'_sub x hx)
        exact GM12.theorem_4_1_proof H' P θ' T' d' A B u v hS hConn hComp.hasMetric' huH' hvH'
          hP_path hP_sub hAB hP_V
    have hord_lt_X : separationOrder A B < X.ncard :=
      lt_of_lt_of_le hlt_ord
        (Set.ncard_le_ncard inter_subset_left (H.finite_V.subset hFree.1))
    -- Claim (3): every `u ∈ V(A)` is in `V(H)` with `d z {u} > lam + 2`, and every edge of `H'`
    -- incident with `u` is in `H₀.E`.
    have hClaim3_V : ∀ u ∈ A.vertexSet, u ∈ H.V ∧ lam + 2 < d z {u} := by
      exact small_side_vertices_are_far_from_deleted_atom (S := S) H H' θ lam T T' d d' z X hS
        hz hFree hDistX hAtoms hComp hd_tri A B hsepAB v hvX hvH' hClaim2 hord_lt_X
    have hClaim3_E : ∀ u ∈ A.vertexSet, ∀ e ∈ H'.E, u ∈ closure e → e ∈ H₀.E := by
      exact small_side_edges_survive_deletion (S := S) H H' θ lam T T' d d' z X hS hz hFree
        hDistX hAtoms hComp hd_tri hd'_symm hd'_tri hd'_inc hH₀_eq A B hsepAB v hvX hvH'
        hClaim2 hord_lt_X
    -- Claim (4): for all `u ∈ V(A)`, every edge of `H` incident with `u` is in `H₀.E`.
    have hClaim4 : ∀ u ∈ A.vertexSet, ∀ e ∈ H.E, u ∈ closure e → e ∈ H₀.E := by
      intro u huA e heH hue
      obtain ⟨huH, hlt_u⟩ := hClaim3_V u huA
      have hd_ue : d {u} e ≤ 2 := hd_inc.2 u huH e heH hue
      have htri := hd_tri z hz e (Or.inl (Or.inr heH)) {u} (Or.inl (Or.inl ⟨u, huH, rfl⟩))
      have hsym := hd_symm {u} (Or.inl (Or.inl ⟨u, huH, rfl⟩)) e (Or.inl (Or.inr heH))
      change e ∈ (deleteAtomNeighborhood H d z lam).E
      rw [hH₀_eq, H.span_E]
      exact ⟨⟨heH, by omega⟩, heH⟩
    -- Construct `(A, C)` in `H` such that `A ∩ C = A ∩ B` and `C ∩ H₀ = B ∩ H₀`.
    have hA_le_H : A ≤ H.toHypergraph := by
      refine ⟨fun u huA => (hClaim3_V u huA).1,
        fun e heA => ?_, fun e heA => ?_⟩
      · obtain ⟨u, hu_inc⟩ : (A.ends e).Nonempty := by
          have he' : e ∈ H'.E := hsepAB.left_le.edgeSet_subset heA
          obtain ⟨u, hue, huV'⟩ := edge_closure_inter_V_nonempty he'
          refine ⟨u, ?_⟩
          rw [← hsepAB.left_le.ends_eq e heA]
          exact ⟨he', huV', hue⟩
        have huA : u ∈ A.vertexSet := A.vertex_mem_of_inc hu_inc
        have hinc' : H'.toHypergraph.Inc e u := by
          change u ∈ H'.toHypergraph.ends e
          rw [hsepAB.left_le.ends_eq e heA]
          exact hu_inc
        exact hSubH₀H.2 (hClaim3_E u huA e hinc'.1 hinc'.2.2)
      · ext u
        change (e ∈ H.E ∧ u ∈ H.V ∧ u ∈ closure e) ↔ u ∈ A.ends e
        rw [← hsepAB.left_le.ends_eq e heA]
        change (e ∈ H.E ∧ u ∈ H.V ∧ u ∈ closure e) ↔ (e ∈ H'.E ∧ u ∈ H'.V ∧ u ∈ closure e)
        constructor
        · rintro ⟨heH, huH, hue⟩
          have he' : e ∈ H'.E := hsepAB.left_le.edgeSet_subset heA
          have hu_in : u ∈ closure e ∩ H.V := ⟨hue, huH⟩
          obtain ⟨w, hw_inc⟩ : (A.ends e).Nonempty := by
            obtain ⟨w, hwe, hwV'⟩ := edge_closure_inter_V_nonempty he'
            refine ⟨w, ?_⟩
            rw [← hsepAB.left_le.ends_eq e heA]
            exact ⟨he', hwV', hwe⟩
          have hwA : w ∈ A.vertexSet := A.vertex_mem_of_inc hw_inc
          have hinc' : H'.toHypergraph.Inc e w := by
            change w ∈ H'.toHypergraph.ends e
            rw [hsepAB.left_le.ends_eq e heA]
            exact hw_inc
          have he₀ : e ∈ H₀.E := hClaim3_E w hwA e hinc'.1 hinc'.2.2
          rw [← hSubH₀H.closure_inter_V he₀, hSubH₀H'.closure_inter_V he₀] at hu_in
          exact ⟨he', hu_in.2, hue⟩
        · rintro ⟨he', hu', hue⟩
          have huA : u ∈ A.vertexSet := by
            have : u ∈ A.ends e := by
              rw [← hsepAB.left_le.ends_eq e heA]
              exact ⟨he', hu', hue⟩
            exact A.vertex_mem_of_inc this
          exact ⟨hSubH₀H.2 (hClaim3_E u huA e he' hue), (hClaim3_V u huA).1, hue⟩
    let C : Hypergraph S (Set S) :=
      { vertexSet := (H.V \ A.vertexSet) ∪ (A.vertexSet ∩ B.vertexSet)
        edgeSet := H.E \ A.edgeSet
        Inc e u := H.toHypergraph.Inc e u ∧ e ∈ H.E \ A.edgeSet
        vertex_mem_of_inc e u h := by
          by_cases huA : u ∈ A.vertexSet
          · refine Or.inr ⟨huA, ?_⟩
            have he₀ : e ∈ H₀.E := hClaim4 u huA e h.1.1 h.1.2.2
            have he' : e ∈ H'.E := hSubH₀H'.2 he₀
            have he_u : e ∈ A.edgeSet ∪ B.edgeSet := hsepAB.edgeSet_union.symm ▸ he'
            have heB : e ∈ B.edgeSet := he_u.resolve_left h.2.2
            have hinc' : H'.toHypergraph.Inc e u :=
              ⟨he', hsepAB.left_le.vertexSet_subset huA, h.1.2.2⟩
            have huB_ends : u ∈ B.ends e := by
              rw [← hsepAB.right_le.ends_eq e heB]
              exact hinc'
            exact B.vertex_mem_of_inc huB_ends
          · exact Or.inl ⟨h.1.2.1, huA⟩
        edge_mem_of_inc _ _ h := h.2
        vertexSet_finite := H.finite_V.subset
          (union_subset sdiff_subset (inter_subset_left.trans hA_le_H.vertexSet_subset))
        edgeSet_finite := H.finite_edges.subset sdiff_subset }
    have hC_le_H : C ≤ H.toHypergraph := by
      refine ⟨union_subset sdiff_subset (inter_subset_left.trans hA_le_H.vertexSet_subset),
        sdiff_subset, fun e heC => ?_⟩
      ext u
      exact ⟨fun h => ⟨h, heC⟩, fun h => h.1⟩
    have hsepAC : H.toHypergraph.IsSeparation A C := by
      refine (isSeparation_iff_of_le hA_le_H hC_le_H).mpr ⟨?_, ?_, ?_⟩
      · ext x
        change (x ∈ A.vertexSet ∨ x ∈ (H.V \ A.vertexSet) ∪ (A.vertexSet ∩ B.vertexSet)) ↔
          x ∈ H.V
        constructor
        · rintro (hxA | ⟨hxH, _⟩ | ⟨hxA, _⟩)
          · exact hA_le_H.vertexSet_subset hxA
          · exact hxH
          · exact hA_le_H.vertexSet_subset hxA
        · intro hxH
          by_cases hxA : x ∈ A.vertexSet
          · exact Or.inl hxA
          · exact Or.inr (Or.inl ⟨hxH, hxA⟩)
      · ext e
        change (e ∈ A.edgeSet ∨ e ∈ H.E \ A.edgeSet) ↔ e ∈ H.E
        constructor
        · rintro (heA | ⟨heH, _⟩)
          · exact hA_le_H.edgeSet_subset heA
          · exact heH
        · intro heH
          by_cases heA : e ∈ A.edgeSet
          · exact Or.inl heA
          · exact Or.inr ⟨heH, heA⟩
      · ext e
        change (e ∈ A.edgeSet ∧ e ∈ H.E \ A.edgeSet) ↔ e ∈ (∅ : Set (Set S))
        simp only [mem_sdiff, mem_empty_iff_false, iff_false]
        exact fun ⟨heA, _, henot⟩ => henot heA
    have hinterAC : (A ∩ C).vertexSet = (A ∩ B).vertexSet := by
      ext x
      change (x ∈ A.vertexSet ∧ (x ∈ H.V \ A.vertexSet ∨ x ∈ A.vertexSet ∧ x ∈ B.vertexSet)) ↔
        x ∈ A.vertexSet ∧ x ∈ B.vertexSet
      exact ⟨fun ⟨hxA, h⟩ => ⟨hxA, (h.resolve_left fun h' => h'.2 hxA).2⟩,
        fun ⟨hxA, hxB⟩ => ⟨hxA, Or.inr ⟨hxA, hxB⟩⟩⟩
    have hordAC_eq : separationOrder A C = separationOrder A B :=
      congrArg Set.ncard hinterAC
    have hordAC_lt : separationOrder A C < θ' := hordAC_eq.symm ▸ hordAB
    have hAC_in_T : (A, C) ∈ T := by
      exact lifted_small_side_belongs_to_original_tangle (S := S) H H' θ lam T T' d z X
        hMetric hlam hθ v₀ hv₀_le_θ hv₀_gt hSubH₀H hSubH₀H' T₀ hMem₀_710 hIndEq hT' A B hAB
        hsepAB hordAB hord_lt_X C rfl hsepAC hordAC_eq hordAC_lt
    have hFreeXA : IsFreeSet H.toHypergraph T θ (X ∩ A.vertexSet) :=
      GM14.freeSet_subset hMetric.1.2.1 hFree inter_subset_left
    have hle_ord := hFreeXA.2.2 hAC_in_T inter_subset_right
    omega

/-- **Graph Minors XV, (4.7)** (pages 127–128):
Preservation of a free set `X ⊆ V(H)` with `d(z, v) > 2|X| + 5λ + 2` for all `v ∈ X` under a
`(4λ + 2)`-compression `T'` of `T` in `H'`.
Proved from `(4.4)`, `(4.5)`, Graph Minors XI, `(9.1)`, and Graph Minors XII, `(4.1)`,
`(7.7)`, `(7.10)`, and `(7.11)`. -/
theorem theorem_4_7_proof
     :
    GM15Theorem47Statement.{w} := by
  intro S _ _ H H' θ lam T T' d d' z X
    hS hConn hMetric hz hlam hFree hDistX h2cell' hAtoms hComp
  let θ' := θ - (4 * lam + 2)
  have hθ : 4 * lam + 2 < θ := hComp.lam_lt
  obtain ⟨_, hd_refl, hd_le_θ, hd_symm, hd_tri, hd_inc⟩ := gm11_theorem_9_1 H θ T d hS hConn hMetric
  obtain ⟨_, hd'_refl, hd'_le_θ', hd'_symm, hd'_tri, hd'_inc⟩ :=
    gm11_theorem_9_1 H' θ' T' d' hS hConn hComp.hasMetric'
  by_cases hXne : X.Nonempty
  · obtain ⟨v₀, hv₀X⟩ := hXne
    have hv₀H : v₀ ∈ H.V := hFree.1 hv₀X
    have hv₀_le_θ : d z {v₀} ≤ θ := hd_le_θ z hz {v₀} (Or.inl (Or.inl ⟨v₀, hv₀H, rfl⟩))
    have hv₀_gt := hDistX v₀ hv₀X
    have hX_pos : 0 < X.ncard := (Set.ncard_pos (H.finite_V.subset hFree.1)).mpr ⟨v₀, hv₀X⟩
    have hX_le_θ' : X.ncard ≤ θ' := by omega
    have hX_sub_H' : X ⊆ H'.V := by
      intro v hvX
      have hvH : v ∈ H.V := hFree.1 hvX
      have hlt : lam < d z {v} := by have := hDistX v hvX; omega
      exact vertex_mem_V_of_mem_A hS hvH (hAtoms {v} (Or.inl (Or.inl ⟨v, hvH, rfl⟩)) hlt)
    let H₀ := deleteAtomNeighborhood H d z lam
    have hE_ne : H.E.Nonempty := by
      by_contra hE_emp
      have hV_le := ncard_V_le_one_of_E_empty hS hMetric.1.1 (Set.not_nonempty_iff_eq_empty.mp
        hE_emp)
      have hord_le : θ ≤ H.V.ncard := hMetric.1.2.1.order_le_ncard_vertexSet
      omega
    have hH₀_eq : H₀ = H.span ∅ {e ∈ H.E | lam < d z e} := by
      change deleteAtomNeighborhood H d z lam = _
      rw [deleteAtomNeighborhood, ite_eq_right_iff.mpr fun h => False.elim (hE_ne.ne_empty h)]
    have hSubH₀H : H₀.IsSubdrawing H := hH₀_eq ▸ H.span_isSubdrawing _ _
    have h2cell₀ : (PaintingOrDrawing.drawing H₀).IsTwoCell :=
      theorem_4_3_proof H θ lam T d z hS hConn hMetric
        hE_ne hz (by omega) (fun _ => hlam)
    have hEdist₀ : ∀ e ∈ H.E \ H₀.E, d z e ≤ lam := by
      rintro e ⟨heH, henot⟩
      rw [hH₀_eq, H.span_E] at henot
      have : ¬ lam < d z e := fun hlt => henot ⟨⟨heH, hlt⟩, heH⟩
      omega
    obtain ⟨T₀_710, d₀_710, ⟨hM₀_710, hMem₀_710, _⟩, hUniq₀_710⟩ :=
      GraphMinor.GM12.gm14_theorem_7_10.{w} S hS hConn H H₀ θ lam T d z
        (by omega) hMetric hz hSubH₀H h2cell₀ hEdist₀ (fun _ => hlam)
    have hSubEq : θ - 4 * lam - 2 = θ - (4 * lam + 2) := by omega
    rw [hSubEq] at hM₀_710 hMem₀_710 hUniq₀_710
    obtain ⟨hSubH₀H', T₀, T'_45, d₀, d'_45, hComp₀, _, hIndEq, hUniq'⟩ :=
      theorem_4_5_proof H H' θ lam T d z hS hConn hMetric hz hlam hθ h2cell' hAtoms
    have hT₀_eq : T₀ = T₀_710 := by
      refine hUniq₀_710 T₀ d₀ hComp₀.hasMetric' (fun a ha b hb a' ha' b' hb' hsub₁ hsub₂ => ?_)
      obtain ⟨σ₁, hσ₁⟩ := atom_nonempty ha
      obtain ⟨σ₂, hσ₂⟩ := atom_nonempty hb
      have hle := hComp₀.dist_le σ₁ σ₂
      rw [pointDist_eq_of_mem_atom ha hb hσ₁ hσ₂,
        pointDist_eq_of_mem_atom ha' hb' (hsub₁ hσ₁) (hsub₂ hσ₂)] at hle
      omega
    subst hT₀_eq
    have hT'_eq : T' = T'_45 := hUniq' T' d' hComp
    subst hT'_eq
    have hT' : IsTangle H'.toHypergraph θ' T' := hComp.hasMetric'.1.2.1
    have hMain : ∀ n : ℕ, ∀ A B : Hypergraph S (Set S),
        A.vertexSet.ncard = n → (A, B) ∈ T' →
        (X ∩ A.vertexSet).ncard ≤ separationOrder A B := by
      exact compressed_tangle_small_sides_respect_free_set (S := S) H H' θ lam T T' d d' z X hS
        hMetric hz hlam hFree hDistX hAtoms hComp hθ hd_symm hd_tri hd_inc hd'_refl hd'_symm
        hd'_tri hd'_inc v₀ hv₀_le_θ hv₀_gt hH₀_eq hSubH₀H hSubH₀H' T₀ hMem₀_710 hIndEq hT'
    refine ⟨hX_sub_H', hX_le_θ', fun A B hAB hXsub => ?_⟩
    have hXA : X ∩ A.vertexSet = X := Set.inter_eq_left.mpr hXsub
    have hle := hMain A.vertexSet.ncard A B rfl hAB
    rwa [hXA] at hle
  · have hX_emp : X = ∅ := Set.not_nonempty_iff_eq_empty.mp hXne
    subst hX_emp
    exact ⟨empty_subset _, by simp, fun _ _ _ _ => by simp⟩

end GraphMinor.GM15
