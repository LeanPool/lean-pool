/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.Section5

/-!
# Graph Minors XI, (5.5) from (5.4)

This file proves that a drawing in a connected closed surface has only finitely many regions
(`finite_R`), and deduces (5.5) from (5.4) by the paper's argument (`theorem_5_5_of_partition`).
Statement (5.4) itself is `PartitionNotSmall`, and it is a hypothesis of the deduction only. It is
proved in `Section5c.lean`, where (5.5) is stated without this hypothesis.
-/

public section

namespace GraphMinor.GM11

open Set Topology GraphMinor.Surface

universe u

variable {S : Type u} [TopologicalSpace S] [T2Space S] {Γ : Drawing S}

/-- A drawing in a connected closed surface has finitely many regions. Deleting an edge merges only
regions incident with that edge, and these are at most two. A drawing without edges has one
region. -/
theorem finite_R (hS : IsClosedSurface S) [PreconnectedSpace S]
    (Γ : Drawing S) : Γ.R.Finite := by
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  induction hn : Γ.E.ncard using Nat.strong_induction_on generalizing Γ with
  | _ n ih =>
    by_cases hE : Γ.E.Nonempty
    · obtain ⟨e, he⟩ := hE
      have hlt : (Γ.deleteEdge e).E.ncard < n := by
        rw [deleteEdge_E, ← hn]
        exact Set.ncard_sdiff_singleton_lt_of_mem he Γ.finite_edges
      have h₁ := ih _ hlt (Γ.deleteEdge e) rfl
      have h₂ : {r ∈ Γ.R | e ⊆ closure r}.Finite := by
        by_contra hinf
        obtain ⟨T, hT, hcard⟩ := (Set.not_finite.mp hinf |> Set.Infinite.exists_subset_ncard_eq) 3
        obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Set.ncard_eq_three.mp hcard.2
        have ha := hT (show a ∈ _ by simp)
        have hb := hT (show b ∈ _ by simp)
        have hc := hT (show c ∈ _ by simp)
        rcases region_incident_two hS he ha.1 hb.1 hc.1 ha.2 hb.2 hc.2 with h | h | h
        · exact hab h
        · exact hac h
        · exact hbc h
      refine (h₁.union h₂).subset fun r hr => ?_
      rcases edge_incident_or_disjoint hS he hr with h | h
      · exact Or.inr ⟨hr, h⟩
      · exact Or.inl (region_deleteEdge_of_not_incident he hr h)
    · have hU : Γ.U = Γ.V := by
        rw [Γ.U_eq, not_nonempty_iff_eq_empty.mp hE]
        simp
      have hc : IsPreconnected (univ \ Γ.U) := by
        rw [hU, ← compl_eq_univ_sdiff]
        exact isPreconnected_compl_finite hS Γ.finite_V
      refine Set.Subsingleton.finite fun r₁ h₁ r₂ h₂ => ?_
      obtain ⟨x, hx⟩ := region_nonempty h₁
      obtain ⟨y, hy⟩ := region_nonempty h₂
      refine region_eq_of_mem h₁ h₂ (subset_region h₁ hc ?_ ⟨mem_univ _, region_subset h₁ hx⟩ hx
        ⟨mem_univ _, region_subset h₂ hy⟩) hy
      exact disjoint_left.mpr fun q hq => hq.2

/-- The vertices of `N(Z)` are those incident with a member of `Z` and a region outside `Z`. The
ends of an edge of `N(Z)` are of this kind, since an edge lies in the closure of its regions. -/
theorem mem_boundaryDrawing_V (hS : IsClosedSurface S)
    {Z : Set (Set S)} {v : S} :
    v ∈ (boundaryDrawing Γ Z).V ↔ (∃ r ∈ Z, Γ.VertexIncident v r) ∧
      ∃ r ∈ Γ.R \ Z, Γ.VertexIncident v r := by
  constructor
  · intro hv
    rcases hv with ⟨hv, -⟩ | hv
    · exact hv
    · obtain ⟨e, ⟨he, heΓ⟩, hve, hvV⟩ := mem_iUnion₂.mp hv
      obtain ⟨⟨r₁, hr₁, hi₁⟩, r₂, hr₂, hi₂⟩ := he
      have hclosure : ∀ r ∈ Γ.R, Γ.EdgeRegionIncident e r → Γ.VertexIncident v r := by
        intro r hr hi
        have hsub := edge_subset_closure_of_incident hS heΓ hr hi.2.2
        exact ⟨hvV, Or.inr hr, closure_minimal hsub isClosed_closure hve⟩
      exact ⟨⟨r₁, hr₁, hclosure r₁ hi₁.2.1 hi₁⟩, r₂, hr₂, hclosure r₂ hr₂.1 hi₂⟩
  · intro hv
    exact Or.inl ⟨hv, hv.1.choose_spec.2.1⟩

/-- Graph Minors XI, (5.4) (page 82): "If $(Z_1, Z_2, Z_3)$ is a partition of $R(\Gamma)$, then one
of $Z_1, Z_2, Z_3$ is not
small." -/
@[expose] def PartitionNotSmall (Γ : Drawing S) (ins : Drawing S → Set S) (k : ℕ) (Ω : Set S)
  (ω : ℕ) : Prop :=
  ∀ Z₁ Z₂ Z₃ : Set (Set S), Z₁ ∪ Z₂ ∪ Z₃ = Γ.R → Disjoint Z₁ Z₂ → Disjoint Z₁ Z₃ →
    Disjoint Z₂ Z₃ → ¬ (IsSmall Γ ins k Ω ω Z₁ ∧ IsSmall Γ ins k Ω ω Z₂ ∧ IsSmall Γ ins k Ω ω Z₃)

/-- The counting step of (5.5): the sets of `Ω`-vertices of `N(Z₁ - Z₂)` and `N(Z₂ - Z₁)` have total
size at most that of `N(Z₁)` and `N(Z₂)`. -/
private theorem count_step (hS : IsClosedSurface S)
    {Ω : Set S} (hΩ : Ω ⊆ Γ.V) {Z₁ Z₂ : Set (Set S)}
    (hZ₁ : Z₁ ⊆ Γ.R) (hZ₂ : Z₂ ⊆ Γ.R) :
    (Ω ∩ (boundaryDrawing Γ (Z₁ \ Z₂)).V).ncard + (Ω ∩ (boundaryDrawing Γ (Z₂ \ Z₁)).V).ncard ≤
      (Ω ∩ (boundaryDrawing Γ Z₁).V).ncard + (Ω ∩ (boundaryDrawing Γ Z₂).V).ncard := by
  have hmem := fun Z v => mem_boundaryDrawing_V (Γ := Γ) (Z := Z) (v := v) hS
  set A := (boundaryDrawing Γ (Z₁ \ Z₂)).V with hA
  set B := (boundaryDrawing Γ (Z₂ \ Z₁)).V with hB'
  set X := (boundaryDrawing Γ Z₁).V with hX
  set Y := (boundaryDrawing Γ Z₂).V with hY
  have hΩf : Ω.Finite := Γ.finite_V.subset hΩ
  -- The first claim of the paper, for either order of `Z₁` and `Z₂`.
  have hclaim : ∀ P Q : Set (Set S), P ⊆ Γ.R → ∀ v, v ∈ (boundaryDrawing Γ (P \ Q)).V →
      v ∈ (boundaryDrawing Γ P).V ∨ v ∈ (boundaryDrawing Γ Q).V := by
    intro P Q hP v hv
    obtain ⟨⟨r₁, ⟨hr₁P, hr₁Q⟩, hi₁⟩, r₂, ⟨hr₂R, hr₂⟩, hi₂⟩ := (hmem _ v).mp hv
    by_cases hr₂P : r₂ ∈ P
    · have hr₂Q : r₂ ∈ Q := by
        by_contra h
        exact hr₂ ⟨hr₂P, h⟩
      exact Or.inr ((hmem _ v).mpr ⟨⟨r₂, hr₂Q, hi₂⟩, r₁, ⟨hP hr₁P, hr₁Q⟩, hi₁⟩)
    · exact Or.inl ((hmem _ v).mpr ⟨⟨r₁, hr₁P, hi₁⟩, r₂, ⟨hr₂R, hr₂P⟩, hi₂⟩)
  have hun : Ω ∩ (A ∪ B) ⊆ Ω ∩ (X ∪ Y) := by
    rintro v ⟨hvΩ, hv | hv⟩
    · exact ⟨hvΩ, hclaim Z₁ Z₂ hZ₁ v hv⟩
    · refine ⟨hvΩ, ?_⟩
      rcases hclaim Z₂ Z₁ hZ₂ v hv with h | h
      · exact Or.inr h
      · exact Or.inl h
  have hin : Ω ∩ (A ∩ B) ⊆ Ω ∩ (X ∩ Y) := by
    rintro v ⟨hvΩ, hvA, hvB⟩
    obtain ⟨⟨r₁, ⟨hr₁, hr₁n⟩, hi₁⟩, -⟩ := (hmem _ v).mp hvA
    obtain ⟨⟨r₂, ⟨hr₂, hr₂n⟩, hi₂⟩, -⟩ := (hmem _ v).mp hvB
    exact ⟨hvΩ, (hmem _ v).mpr ⟨⟨r₁, hr₁, hi₁⟩, r₂, ⟨hZ₂ hr₂, hr₂n⟩, hi₂⟩,
      (hmem _ v).mpr ⟨⟨r₂, hr₂, hi₂⟩, r₁, ⟨hZ₁ hr₁, hr₁n⟩, hi₁⟩⟩
  have hf : ∀ T : Set S, (Ω ∩ T).Finite := fun T => hΩf.subset inter_subset_left
  have e₁ := Set.ncard_union_add_ncard_inter (Ω ∩ A) (Ω ∩ B) (hf A) (hf B)
  have e₂ := Set.ncard_union_add_ncard_inter (Ω ∩ X) (Ω ∩ Y) (hf X) (hf Y)
  rw [← inter_union_distrib_left, ← inter_inter_distrib_left] at e₁ e₂
  have l₁ := Set.ncard_le_ncard hun (hf _)
  have l₂ := Set.ncard_le_ncard hin (hf _)
  omega

/-- One step of the proof of (5.5): if `Z₁` and `Z₂` meet, the triple can be made smaller. -/
private theorem step_5_5 (hS : IsClosedSurface S) [ConnectedSpace S]
    {k ω : ℕ} {ins : Drawing S → Set S} {Ω : Set S}
    (hs : IsSlope Γ k ins) (hw : IsWeighting Γ k Ω ω) {Z₁ Z₂ Z₃ : Set (Set S)}
    (hU : Z₁ ∪ Z₂ ∪ Z₃ = Γ.R) (h₁ : IsSmall Γ ins k Ω ω Z₁) (h₂ : IsSmall Γ ins k Ω ω Z₂)
    (hne : (Z₁ ∩ Z₂).Nonempty) :
    (IsSmall Γ ins k Ω ω (Z₁ \ Z₂) ∧ (Z₁ \ Z₂) ∪ Z₂ ∪ Z₃ = Γ.R ∧ (Z₁ \ Z₂).ncard < Z₁.ncard) ∨
    (IsSmall Γ ins k Ω ω (Z₂ \ Z₁) ∧ Z₁ ∪ (Z₂ \ Z₁) ∪ Z₃ = Γ.R ∧ (Z₂ \ Z₁).ncard < Z₂.ncard) := by
  have hZ₁ : Z₁ ⊆ Γ.R := fun r hr => hU ▸ Or.inl (Or.inl hr)
  have hZ₂ : Z₂ ⊆ Γ.R := fun r hr => hU ▸ Or.inl (Or.inr hr)
  have hfin := finite_R hS Γ
  have hcount := count_step hS hw.subset hZ₁ hZ₂
  have ha := h₁.1
  have hb := h₂.1
  have hlt : (Ω ∩ (boundaryDrawing Γ (Z₁ \ Z₂)).V).ncard < ω ∨
      (Ω ∩ (boundaryDrawing Γ (Z₂ \ Z₁)).V).ncard < ω := by omega
  obtain ⟨x, hx₁, hx₂⟩ := hne
  rcases hlt with h | h
  · refine Or.inl ⟨theorem_5_3_proof hS hs hw hZ₁ h₁ sdiff_subset h, ?_, ?_⟩
    · rw [← hU]
      ext r
      simp only [mem_union, mem_sdiff]
      tauto
    · exact Set.ncard_lt_ncard ⟨sdiff_subset, fun hsub => (hsub hx₁).2 hx₂⟩ (hfin.subset hZ₁)
  · refine Or.inr ⟨theorem_5_3_proof hS hs hw hZ₂ h₂ sdiff_subset h, ?_, ?_⟩
    · rw [← hU]
      ext r
      simp only [mem_union, mem_sdiff]
      tauto
    · exact Set.ncard_lt_ncard ⟨sdiff_subset, fun hsub => (hsub hx₂).2 hx₁⟩ (hfin.subset hZ₂)

/-- Graph Minors XI, (5.5) (page 86), deduced from (5.4) as in the paper: "If $Z_1, Z_2, Z_3
\subseteq R(\Gamma)$ are small, then $Z_1 \cup Z_2 \cup Z_3 \ne
R(\Gamma)$." -/
theorem theorem_5_5_of_partition (hS : IsClosedSurface S) [ConnectedSpace S]
    {k ω : ℕ} {ins : Drawing S → Set S} {Ω : Set S}
    (hs : IsSlope Γ k ins) (hw : IsWeighting Γ k Ω ω) (h54 : PartitionNotSmall Γ ins k Ω ω)
    {Z₁ Z₂ Z₃ : Set (Set S)} (h₁ : IsSmall Γ ins k Ω ω Z₁) (h₂ : IsSmall Γ ins k Ω ω Z₂)
    (h₃ : IsSmall Γ ins k Ω ω Z₃) : Z₁ ∪ Z₂ ∪ Z₃ ≠ Γ.R := by
  intro hU
  induction hn : Z₁.ncard + Z₂.ncard + Z₃.ncard using Nat.strong_induction_on
    generalizing Z₁ Z₂ Z₃ with
  | _ n ih =>
    by_cases h₁₂ : (Z₁ ∩ Z₂).Nonempty
    · rcases step_5_5 hS hs hw hU h₁ h₂ h₁₂ with ⟨a, b, c⟩ | ⟨a, b, c⟩
      · exact ih _ (by omega) a h₂ h₃ b rfl
      · exact ih _ (by omega) h₁ a h₃ b rfl
    by_cases h₁₃ : (Z₁ ∩ Z₃).Nonempty
    · have hU' : Z₁ ∪ Z₃ ∪ Z₂ = Γ.R := by rw [← hU, union_right_comm]
      rcases step_5_5 hS hs hw hU' h₁ h₃ h₁₃ with ⟨a, b, c⟩ | ⟨a, b, c⟩
      · exact ih _ (by omega) a h₃ h₂ b rfl
      · exact ih _ (by omega) h₁ a h₂ b rfl
    by_cases h₂₃ : (Z₂ ∩ Z₃).Nonempty
    · have hU' : Z₂ ∪ Z₃ ∪ Z₁ = Γ.R := by
        rw [← hU]
        ext r
        simp only [mem_union]
        tauto
      rcases step_5_5 hS hs hw hU' h₂ h₃ h₂₃ with ⟨a, b, c⟩ | ⟨a, b, c⟩
      · exact ih _ (by omega) a h₃ h₁ b rfl
      · exact ih _ (by omega) h₂ a h₁ b rfl
    exact h54 Z₁ Z₂ Z₃ hU (disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp h₁₂))
      (disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp h₁₃))
      (disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp h₂₃)) ⟨h₁, h₂, h₃⟩

end GraphMinor.GM11
