/-
Copyright (c) 2026 Jacob Parish. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jacob Parish
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.SetTheory.Cardinal.Arithmetic

/-!
# Closure over a set: replication of finite extensions

The proof uses elementary submodels only through replication: a finite configuration
whose new vertices lie outside the previous model has a copy, with the same diagram over
its roots, inside the next model. `ClosedOver G M N` states exactly this property of the
next model `N` over the previous model `M`, with an additional finite set `D ⊆ N` to
avoid, so that copies can be chosen pairwise disjoint.

A closure of `M ∪ X` over `M` is built in `ω` rounds, adding one witness for each finite
diagram over finite sets of roots and avoided vertices, so its size is at most
`max (#M + #X) ℵ₀`.
-/

@[expose] public section

open Cardinal

namespace Erdos111

variable {V : Type*}

/-- `g` realizes over `R` the same finite diagram as `f`: the same adjacencies among the
new vertices and between the new vertices and the roots. -/
def SameDiagram (G : SimpleGraph V) (R : Finset V) {m : ℕ} (f g : Fin m → V) : Prop :=
  (∀ i j, G.Adj (f i) (f j) ↔ G.Adj (g i) (g j)) ∧
    ∀ i, ∀ r ∈ R, (G.Adj (f i) r ↔ G.Adj (g i) r)

/-- `N` is closed over `M`: it contains `M`, and every finite configuration with roots
`R ⊆ N` whose new vertices avoid `M`, a finite `D ⊆ N` and `R` has a copy with the same
diagram over `R` inside `N`, still avoiding `M`, `D` and `R`. -/
def ClosedOver (G : SimpleGraph V) (M N : Set V) : Prop :=
  M ⊆ N ∧ ∀ (R D : Finset V) (m : ℕ) (f : Fin m → V), ↑R ⊆ N → ↑D ⊆ N →
    Function.Injective f → (∀ i, f i ∉ M ∧ f i ∉ D ∧ f i ∉ R) →
    ∃ g : Fin m → V, Function.Injective g ∧ (∀ i, g i ∈ N ∧ g i ∉ M ∧ g i ∉ D ∧ g i ∉ R) ∧
      SameDiagram G R f g

namespace Closure

/-- A request over `S`: finite sets of roots and of avoided vertices in `S`, and the number
of new vertices. -/
abbrev Request (S : Set V) : Type _ :=
  Finset S × Finset S × ℕ

/-- A finite diagram for a request: the adjacencies among the new vertices and between the
new vertices and the roots. -/
abbrev Diagram {S : Set V} (p : Request S) : Type _ :=
  (Fin p.2.2 → Fin p.2.2 → Bool) × (Fin p.2.2 → p.1 → Bool)

/-- `g` realizes the diagram `d` of the request `p`, with new vertices avoiding `M`, the
avoided vertices and the roots. -/
def Realizes (G : SimpleGraph V) (M : Set V) {S : Set V} (p : Request S) (d : Diagram p)
    (g : Fin p.2.2 → V) : Prop :=
  Function.Injective g ∧
    (∀ i, g i ∉ M ∧ (∀ r ∈ p.2.1, g i ≠ r) ∧ ∀ r ∈ p.1, g i ≠ r) ∧
    (∀ i j, G.Adj (g i) (g j) ↔ d.1 i j = true) ∧
    ∀ i (r : p.1), G.Adj (g i) r.1 ↔ d.2 i r = true

open scoped Classical in
/-- The new vertices of one realization of the diagram `d`, when there is one. -/
noncomputable def witness (G : SimpleGraph V) (M : Set V) {S : Set V} (p : Request S)
    (d : Diagram p) : Set V :=
  if h : ∃ g, Realizes G M p d g then Set.range h.choose else ∅

/-- A witness is finite. -/
theorem witness_finite (G : SimpleGraph V) (M : Set V) {S : Set V} (p : Request S)
    (d : Diagram p) : (witness G M p d).Finite := by
  unfold witness
  split
  · exact Set.finite_range _
  · exact Set.finite_empty

/-- A realizable diagram has a realization inside its witness. -/
theorem exists_realizes_subset_witness {G : SimpleGraph V} {M S : Set V} {p : Request S}
    {d : Diagram p} (h : ∃ g, Realizes G M p d g) :
    ∃ g, Realizes G M p d g ∧ Set.range g ⊆ witness G M p d := by
  refine ⟨h.choose, h.choose_spec, ?_⟩
  simp [witness, h]

/-- One round over `S`: add a realization of every realizable diagram over `S`. -/
noncomputable def step (G : SimpleGraph V) (M S : Set V) : Set V :=
  S ∪ ⋃ (p : Request S) (d : Diagram p), witness G M p d

/-- The rounds of the closure of `M ∪ X` over `M`. -/
noncomputable def rounds (G : SimpleGraph V) (M X : Set V) : ℕ → Set V
  | 0 => M ∪ X
  | n + 1 => step G M (rounds G M X n)

/-- A round keeps a set of size at most an infinite `κ` of size at most `κ`. -/
theorem mk_step_le (G : SimpleGraph V) (M : Set V) {S : Set V} {κ : Cardinal} (hκ : ℵ₀ ≤ κ)
    (hS : #S ≤ κ) : #(step G M S) ≤ κ := by
  classical
  have hmul : ∀ {a b : Cardinal}, a ≤ κ → b ≤ κ → a * b ≤ κ := fun ha hb =>
    (mul_le_mul' ha hb).trans (mul_eq_self hκ).le
  have hfin : #(Finset S) ≤ κ := by
    refine (mk_le_of_surjective (f := fun l : List S => l.toFinset)
      fun s => ⟨s.toList, s.toList_toFinset⟩).trans ((mk_list_le_max S).trans (max_le hκ hS))
  have hreq : #(Request S) ≤ κ := by
    simp only [Request, mk_prod, lift_id, lift_uzero, mk_nat, lift_aleph0]
    exact hmul hfin (hmul hfin hκ)
  have hU : #(⋃ (p : Request S) (d : Diagram p), witness G M p d) ≤ κ := by
    refine (mk_iUnion_le _).trans (hmul hreq (ciSup_le' fun p => ?_))
    exact (Set.finite_iUnion fun d => witness_finite G M p d).lt_aleph0.le.trans hκ
  exact (mk_union_le _ _).trans ((add_le_add hS hU).trans (add_eq_self hκ).le)

end Closure

open Closure in
/-- Every `M ∪ X` lies in a set closed over `M` of size at most `max (#M + #X) ℵ₀`. -/
theorem exists_closedOver (G : SimpleGraph V) (M X : Set V) :
    ∃ N : Set V, M ∪ X ⊆ N ∧ ClosedOver G M N ∧ #N ≤ max (#M + #X) ℵ₀ := by
  classical
  have hκ : ℵ₀ ≤ max (#M + #X) ℵ₀ := le_max_right _ _
  set N := rounds G M X
  have hmono : Monotone N := monotone_nat_of_le_succ fun n => Set.subset_union_left
  have hcard : ∀ n, #(N n) ≤ max (#M + #X) ℵ₀ := by
    intro n
    induction n with
    | zero => exact (mk_union_le M X).trans (le_max_left _ _)
    | succ n ih => exact mk_step_le G M hκ ih
  refine ⟨⋃ n, N n, Set.subset_iUnion N 0,
    ⟨Set.subset_union_left.trans (Set.subset_iUnion N 0), ?_⟩, ?_⟩
  · intro R D m f hR hD hf hfa
    obtain ⟨n, hn⟩ := Directed.exists_mem_subset_of_finset_subset_biUnion hmono.directed_le
      (s := R ∪ D) (by simpa [Set.union_subset_iff] using And.intro hR hD)
    rw [Finset.coe_union, Set.union_subset_iff] at hn
    let R' : Finset (N n) := R.subtype (· ∈ N n)
    let D' : Finset (N n) := D.subtype (· ∈ N n)
    let p : Request (N n) := (R', D', m)
    let d : Diagram p := (fun i j => decide (G.Adj (f i) (f j)),
      fun i r => decide (G.Adj (f i) r.1.1))
    have hfr : Realizes G M p d f := by
      refine ⟨hf, fun i => ⟨(hfa i).1, ?_, ?_⟩, fun i j => by simp [d],
        fun i r => by simp [d]⟩
      · intro r hr h
        exact (hfa i).2.1 (h ▸ Finset.mem_subtype.1 hr)
      · intro r hr h
        exact (hfa i).2.2 (h ▸ Finset.mem_subtype.1 hr)
    obtain ⟨g, ⟨hg, hga, hgA, hgB⟩, hgW⟩ :=
      exists_realizes_subset_witness (G := G) (M := M) (p := p) (d := d) ⟨f, hfr⟩
    refine ⟨g, hg, fun i => ⟨?_, (hga i).1, ?_, ?_⟩, fun i j => ?_, fun i r hr => ?_⟩
    · refine Set.subset_iUnion N (n + 1) (Set.subset_union_right ?_)
      exact Set.mem_iUnion₂.2 ⟨p, d, hgW ⟨i, rfl⟩⟩
    · intro h
      exact (hga i).2.1 ⟨g i, hn.2 h⟩ (Finset.mem_subtype.2 h) rfl
    · intro h
      exact (hga i).2.2 ⟨g i, hn.1 h⟩ (Finset.mem_subtype.2 h) rfl
    · rw [hgA i j]
      simp [d]
    · have := hgB i ⟨⟨r, hn.1 hr⟩, Finset.mem_subtype.2 hr⟩
      rw [this]
      simp [d]
  · have h := mk_iUnion_le_lift N
    rw [lift_uzero, mk_nat, lift_aleph0] at h
    simp only [lift_uzero] at h
    exact h.trans ((mul_le_mul' hκ (ciSup_le' hcard)).trans (mul_eq_self hκ).le)

end Erdos111
