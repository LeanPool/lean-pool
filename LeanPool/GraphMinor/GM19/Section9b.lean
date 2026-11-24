/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.PaintingPatchwork
public import LeanPool.GraphMinor.GM18.Section6Part2

/-!
# Rooted locations of paintings as rooted locations of patchworks

The arms of a rooted location of a painting are rooted hypergraphs, and the rooted location is one
in the sense of Graph Minors XVIII.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Function Topology GraphMinor.Surface
open GraphMinor.GM04 (Patchwork freePatch IsGrouping IsComponent)

universe u w

variable {S : Type u} [TopologicalSpace S] {α : Type w}

namespace Arm

variable {Γ : Painting S} (A : Arm Γ)

theorem mem_π {v : S} : v ∈ A.π ↔ v ∈ A.minus.vertexSet ∧ v ∈ A.compl.vertexSet := by
  have h : v ∈ {v | v ∈ A.π} ↔ v ∈ (A.minus ∩ A.compl).vertexSet := by rw [A.π_set]
  exact h

theorem mem_or {v : S} (hv : v ∈ Γ.V) : v ∈ A.minus.vertexSet ∨ v ∈ A.compl.vertexSet := by
  have h : v ∈ (A.minus ∪ A.compl).vertexSet := by
    rw [A.isSeparation.union_eq]
    exact hv
  exact h

theorem edge_or {e : Set S} (he : e ∈ Γ.E) : e ∈ A.minus.edgeSet ∨ e ∈ A.compl.edgeSet := by
  have h : e ∈ (A.minus ∪ A.compl).edgeSet := by
    rw [A.isSeparation.union_eq]
    exact he
  exact h

theorem edge_not {e : Set S} (h₁ : e ∈ A.minus.edgeSet) (h₂ : e ∈ A.compl.edgeSet) : False := by
  have h : e ∈ (A.minus ∩ A.compl).edgeSet := ⟨h₁, h₂⟩
  rw [A.isSeparation.edgeSet_inter_eq] at h
  exact h

theorem edge_mem {e : Set S} (h : e ∈ A.minus.edgeSet) : e ∈ Γ.E :=
  A.isSeparation.left_le.edgeSet_subset h

theorem compl_edge_mem {e : Set S} (h : e ∈ A.compl.edgeSet) : e ∈ Γ.E :=
  A.isSeparation.right_le.edgeSet_subset h

theorem minus_ends {e : Set S} (h : e ∈ A.minus.edgeSet) : A.minus.ends e = tilde e :=
  (A.isSeparation.left_le.ends_eq e h).symm.trans (Γ.ends_eq (A.edge_mem h))

theorem compl_ends {e : Set S} (h : e ∈ A.compl.edgeSet) : A.compl.ends e = tilde e :=
  (A.isSeparation.right_le.ends_eq e h).symm.trans (Γ.ends_eq (A.compl_edge_mem h))

theorem minus_end {e : Set S} (h : e ∈ A.minus.edgeSet) {v : S} (hv : v ∈ tilde e) :
    v ∈ A.minus.vertexSet :=
  A.minus.vertex_mem_of_inc (e := e) (by
    have : v ∈ A.minus.ends e := by rw [A.minus_ends h]; exact hv
    exact this)

theorem compl_end {e : Set S} (h : e ∈ A.compl.edgeSet) {v : S} (hv : v ∈ tilde e) :
    v ∈ A.compl.vertexSet :=
  A.compl.vertex_mem_of_inc (e := e) (by
    have : v ∈ A.compl.ends e := by rw [A.compl_ends h]; exact hv
    exact this)

theorem compl_eq : A.compl =
    GM18.complementHypergraph Γ.toHypergraph.toRooted A.toRootedHypergraph := by
  apply Hypergraph.ext
  · ext v
    constructor
    · intro hv
      have hvG : v ∈ Γ.V := A.isSeparation.right_le.vertexSet_subset hv
      by_cases hm : v ∈ A.minus.vertexSet
      · exact Or.inr ⟨hvG, A.mem_π.2 ⟨hm, hv⟩⟩
      · exact Or.inl ⟨hvG, hm⟩
    · rintro (⟨hv, hn⟩ | ⟨-, hr⟩)
      · exact (A.mem_or hv).resolve_left hn
      · exact (A.mem_π.1 hr).2
  · ext e
    constructor
    · exact fun he ↦ ⟨A.compl_edge_mem he, fun h ↦ A.edge_not h he⟩
    · exact fun he ↦ (A.edge_or he.1).resolve_left he.2
  · funext e v
    apply propext
    constructor
    · intro h
      have he : e ∈ A.compl.edgeSet := A.compl.edge_mem_of_inc h
      have hv : v ∈ A.compl.ends e := h
      rw [A.compl_ends he] at hv
      have heG := A.compl_edge_mem he
      have hvG := Γ.tilde_subset_V heG hv
      have hvc := A.compl_end he hv
      refine ⟨⟨heG, fun h' ↦ A.edge_not h' he⟩, ⟨heG, hvG, hv⟩, ?_⟩
      by_cases hm : v ∈ A.minus.vertexSet
      · exact Or.inr ⟨hvG, A.mem_π.2 ⟨hm, hvc⟩⟩
      · exact Or.inl ⟨hvG, hm⟩
    · rintro ⟨⟨heG, heA⟩, ⟨-, -, hv⟩, -⟩
      have he : e ∈ A.compl.edgeSet := (A.edge_or heG).resolve_left heA
      have : v ∈ A.compl.ends e := by rw [A.compl_ends he]; exact hv
      exact this

theorem isComplemented :
    GM18.IsComplemented Γ.toHypergraph.toRooted A.toRootedHypergraph where
  le := A.isSeparation.left_le
  roots_mem _ _ h := absurd h List.not_mem_nil
  inc_diff_mem v e hv he hinc := by
    have hc : e ∈ A.compl.edgeSet := (A.edge_or he.1).resolve_left he.2
    exact A.mem_π.2 ⟨hv, A.compl_end hc hinc.2.2⟩

theorem toRooted_injective {A B : Arm Γ}
    (h : A.toRootedHypergraph = B.toRootedHypergraph) : A = B := by
  have hm : A.minus = B.minus := congrArg RootedHypergraph.toHypergraph h
  have hπ : A.π = B.π := congrArg RootedHypergraph.roots h
  have hc : A.compl = B.compl := by rw [A.compl_eq, B.compl_eq, h]
  obtain ⟨m, c, s, p, n, ps⟩ := A
  obtain ⟨m', c', s', p', n', ps'⟩ := B
  simp only at hm hπ hc
  subst hm hπ hc
  rfl

end Arm

namespace RootedLocation

variable {Γ : Painting S} (L : RootedLocation Γ)

/-- The rooted hypergraphs of a rooted location. -/
def rooted : Set (RootedHypergraph S (Set S)) := Arm.toRootedHypergraph '' L.arms

theorem location_eq :
    GM18.rootedLocationToLocation Γ.toHypergraph.toRooted L.rooted = L.seps := by
  ext p
  constructor
  · rintro ⟨_, ⟨A, hA, rfl⟩, rfl⟩
    refine ⟨A, hA, ?_⟩
    simp only [Arm.sep, A.compl_eq]
    rfl
  · rintro ⟨A, hA, rfl⟩
    refine ⟨_, ⟨A, hA, rfl⟩, ?_⟩
    simp only [Arm.sep, A.compl_eq]
    rfl

theorem isRootedLocation : GM18.IsRootedLocation Γ.toHypergraph.toRooted L.rooted where
  isComplemented := by
    rintro _ ⟨A, -, rfl⟩
    exact A.isComplemented
  le_complement := by
    rintro _ ⟨A₁, hA₁, rfl⟩ _ ⟨A₂, hA₂, rfl⟩ hne
    rw [← GM18.complementHypergraph_eq_of_isComplemented, ← A₂.compl_eq]
    exact L.disjoint_arms A₁ hA₁ A₂ hA₂ fun h ↦ hne (h ▸ rfl)

theorem isLocation : GM10.IsLocation Γ.toHypergraph L.seps where
  isSeparation := by
    rintro _ ⟨A, -, rfl⟩
    exact A.isSeparation
  left_le_right := by
    rintro _ ⟨A₁, hA₁, rfl⟩ _ ⟨A₂, hA₂, rfl⟩ hne
    exact L.disjoint_arms A₁ hA₁ A₂ hA₂ fun h ↦ hne (h ▸ rfl)

theorem core_eq : GM18.rootedLocationCore Γ.toHypergraph.toRooted L.rooted = L.M := by
  unfold GM18.rootedLocationCore
  rw [L.location_eq]
  have hall : ∀ {x : Hypergraph S (Set S) × Hypergraph S (Set S) → Prop},
      (∀ p ∈ L.seps, x p) ↔ ∀ A ∈ L.arms, x A.sep := by
    intro x
    exact ⟨fun h A hA ↦ h _ ⟨A, hA, rfl⟩, fun h _ ⟨A, hA, e⟩ ↦ e ▸ h A hA⟩
  apply Hypergraph.ext
  · ext v
    exact and_congr_right fun _ ↦ hall
  · ext e
    exact and_congr_right fun _ ↦ hall
  · funext e v
    apply propext
    constructor
    · rintro ⟨h₁, -, h₃⟩
      exact ⟨⟨h₁.1, hall.1 h₃⟩, h₁.2⟩
    · rintro ⟨⟨h₁, h₂⟩, h₃, h₄⟩
      exact ⟨⟨h₁, h₃, h₄⟩, hall.2 fun A hA ↦ A.compl_end (h₂ A hA) h₄, hall.2 h₂⟩

variable {L}

theorem mem_M_V {v : S} : v ∈ L.M.vertexSet ↔ v ∈ Γ.V ∧ ∀ A ∈ L.arms, v ∈ A.compl.vertexSet :=
  Iff.rfl

theorem mem_M_E {e : Set S} : e ∈ L.M.edgeSet ↔ e ∈ Γ.E ∧ ∀ A ∈ L.arms, e ∈ A.compl.edgeSet :=
  Iff.rfl

theorem π_mem_M {A : Arm Γ} (hA : A ∈ L.arms) {v : S} (hv : v ∈ A.π) : v ∈ L.M.vertexSet := by
  have h := A.mem_π.1 hv
  refine ⟨A.isSeparation.left_le.vertexSet_subset h.1, fun B hB ↦ ?_⟩
  by_cases hAB : A = B
  · exact hAB ▸ h.2
  · exact (L.disjoint_arms A hA B hB hAB).vertexSet_subset h.1

theorem tilde_mem_M {e : Set S} (he : e ∈ L.M.edgeSet) {v : S} (hv : v ∈ tilde e) :
    v ∈ L.M.vertexSet :=
  ⟨Γ.tilde_subset_V he.1 hv, fun A hA ↦ A.compl_end (he.2 A hA) hv⟩

theorem exists_arm_of_notMem {e : Set S} (he : e ∈ Γ.E) (hn : e ∉ L.M.edgeSet) :
    ∃ A ∈ L.arms, e ∈ A.minus.edgeSet := by
  by_contra hno
  refine hn ⟨he, fun A hA ↦ (A.edge_or he).resolve_left fun h ↦ hno ⟨A, hA, h⟩⟩

theorem mem_π_of_M {A : Arm Γ} (hA : A ∈ L.arms) {v : S} (hM : v ∈ L.M.vertexSet)
    (hv : v ∈ A.minus.vertexSet) : v ∈ A.π :=
  A.mem_π.2 ⟨hv, hM.2 A hA⟩

/-- An edge of `A⁻` at a vertex of `A` outside `πBar(A)` lies only in `A⁻`. -/
theorem eq_of_edge {A B : Arm Γ} (hA : A ∈ L.arms) (hB : B ∈ L.arms) {e : Set S}
    (heA : e ∈ A.minus.edgeSet) (heB : e ∈ B.minus.edgeSet) : A = B := by
  by_contra hne
  exact B.edge_not heB ((L.disjoint_arms A hA B hB hne).edgeSet_subset heA)

end RootedLocation

end GraphMinor.GM19
