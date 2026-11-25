/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Epstein
public import LeanPool.GraphMinor.GM11.Section7
public import LeanPool.GraphMinor.GM11.Section6
public import LeanPool.GraphMinor.GM11.Section3
public import LeanPool.GraphMinor.Surface.Disc

/-!
# Graph Minors XI, Section 7: lemmas on simply-connected sets

`theorem_7_2`, `theorem_7_8` and `theorem_7_11` are (7.2), (7.8) and (7.11) of the paper. The last
two
rest on (3.1), so they carry its local hypothesis `IsLocalDeformationRetract`: see `theorem_3_1` and
the correction to (3.1) in `corrections/GM11.md`.
-/

@[expose] public section

namespace GraphMinor.GM11

open Set Topology GraphMinor.Surface

universe u

variable {S : Type u} [TopologicalSpace S]

/-- The compact-surface case of Graph Minors XI, (7.1), page 93. A null-homotopic `O`-arc
disjoint from the boundary of a connected compact surface bounds a disc in that surface.
The paper cites D. B. A. Epstein, *Curves on 2-manifolds and isotopies*, Acta Math. 115 (1966)
83–107, Theorem 1.7, which applies to connected triangulable 2-manifolds. -/
theorem theorem_7_1_proof [ConnectedSpace S] (hS : IsSurface S)
    {F : Set S} (hF : IsOArc F) (hbd : Disjoint F (bd S)) (hn : IsNullHomotopicOArcIn univ F) :
    ∃ Δ : Set S, IsClosedDisc Δ ∧ discBd Δ = F := by
  obtain ⟨Δ, -, hd, hb⟩ := (epstein S univ F hS inferInstance hF (subset_univ F) hbd).1 hn
  exact ⟨Δ, hd, hb⟩

/-- Robertson and Seymour, Graph Minors XI, (7.2), page 93. An `O`-arc null-homotopic in `Z`
bounds a disc in `Z`. This is the closed-surface form of the first clause of
`GraphMinor.Surface.EpsteinStatement`. -/
theorem theorem_7_2_proof [ConnectedSpace S] (hS : IsClosedSurface S)
    {Z F : Set S} (hF : IsOArc F) (hFZ : F ⊆ Z) (hn : IsNullHomotopicOArcIn Z F) :
    ∃ Δ : Set S, Δ ⊆ Z ∧ IsClosedDisc Δ ∧ subBd Δ = F := by
  have : T2Space S := hS.2.1
  have hbd : Disjoint F (bd S) := disjoint_left.mpr fun x _ hx => hx (hS.2.2 x)
  obtain ⟨Δ, hΔ, hd, hb⟩ := (epstein S Z F (IsClosedSurface.isSurface hS) inferInstance hF hFZ
    hbd).1 hn
  refine ⟨Δ, hΔ, hd, ?_⟩
  rw [subBd_eq_frontier, IsClosedDisc.frontier_eq_discBd hS hd, hb]

/-- A curve null-homotopic in `Y ⊆ Z`, homotopic in `Z` to a given curve. -/
theorem null_of_homotopic {Y Z : Set S} (hYZ : Y ⊆ Z) {φ φ' : C(Circle, S)}
    (hh : ClosedCurvesHomotopicIn Z φ φ') (hn : ClosedCurveIsNullHomotopicIn Y φ') :
    ClosedCurveIsNullHomotopicIn Z φ := by
  obtain ⟨c, hc, hh'⟩ := hn
  exact ⟨c, hYZ hc, hh.trans (hh'.mono hYZ)⟩

/-- The conclusion of (3.1): each curve in `X ∪ Y` is homotopic in `X ∪ Y` to a curve in `Y`. -/
def CanPush (X Y : Set S) : Prop :=
  ∀ φ : C(Circle, S), range φ ⊆ X ∪ Y →
    ∃ φ' : C(Circle, S), range φ' ⊆ Y ∧ ClosedCurvesHomotopicIn (X ∪ Y) φ φ'

/-- **(7.8)** of Graph Minors XI (page 94): "If $X, Y \subseteq \Sigma$ are closed and
simply-connected and $X \cap Y \ne \emptyset$ is
arc-wise connected, then $X \cup Y$ is simply-connected." The hypothesis `hpush` is the
conclusion of (3.1). `theorem_3_1_proof` gives it for a tame intersection, and `nice_31` for nice
sets. -/
theorem theorem_7_8_proof {X Y : Set S} (hsX : IsSimplyConnectedSet X)
    (hsY : IsSimplyConnectedSet Y) (hL : IsPathConnected (X ∩ Y))
    (hpush : CanPush X Y) : IsSimplyConnectedSet (X ∪ Y) := by
  obtain ⟨z, hz⟩ := hL.nonempty
  refine ⟨hsX.1.union hsY.1 ⟨z, hz⟩, fun φ hφ => ?_⟩
  obtain ⟨φ', hr, hh⟩ := hpush φ hφ
  exact null_of_homotopic subset_union_right hh (hsY.2 φ' hr)

/-- `X` with the discs of the list `L` added. -/
def withDiscs (X : Set S) (L : List (Set S)) : Set S := X ∪ ⋃ Y ∈ L, Y

/-- **(7.11)** of Graph Minors XI (page 95): "If $X \subseteq \Sigma$ is closed and arc-wise
connected and $Y_1, \dots, Y_r \subseteq
\Sigma$ are closed discs with boundary in $X$, and $Z = X \cup Y_1 \cup \dots \cup Y_r$, and
every continuous $\phi \colon S^1 \to X$ is null-homotopic in $Z$, then every continuous
$\phi \colon S^1 \to Z$ is null-homotopic in $Z$."
We also record that `Z` is arc-wise connected, as the induction shows. The hypothesis `hpush` is the
conclusion of (3.1), for the steps of the paper's induction. -/
theorem theorem_7_11_proof (hS : IsClosedSurface S) {X : Set S} (hX : IsClosed X)
    (hp : IsPathConnected X) {L : List (Set S)} (hL : ∀ Y ∈ L, IsClosedDisc Y ∧ frontier Y ⊆ X)
    (hpush : ∀ Y L', (Y :: L') <:+ L → IsPathConnected (Y ∩ withDiscs X L') →
      CanPush Y (withDiscs X L'))
    (hnull : ∀ φ : C(Circle, S), range φ ⊆ X →
      ClosedCurveIsNullHomotopicIn (withDiscs X L) φ) :
    IsSimplyConnectedSet (withDiscs X L) := by
  have : T2Space S := hS.2.1
  have key : ∀ L', L' <:+ L → IsClosed (withDiscs X L') ∧ IsPathConnected (withDiscs X L') ∧
      ∀ φ : C(Circle, S), range φ ⊆ withDiscs X L' →
        ClosedCurveIsNullHomotopicIn (withDiscs X L) φ := by
    intro L'
    induction L' with
    | nil =>
      intro _
      have heq : withDiscs X [] = X := by simp [withDiscs]
      rw [heq]
      exact ⟨hX, hp, hnull⟩
    | cons Y L' ih =>
      intro hs
      obtain ⟨hc, hpc, hn⟩ := ih ((List.suffix_cons Y L').trans hs)
      obtain ⟨hd, hf⟩ := hL Y (hs.subset List.mem_cons_self)
      have heq : withDiscs X (Y :: L') = Y ∪ withDiscs X L' := by
        ext x
        simp only [withDiscs, List.mem_cons, iUnion_iUnion_eq_or_left, mem_union]
        tauto
      have hYc : IsClosed Y := hd.isCompact.isClosed
      have hfs : frontier Y ⊆ withDiscs X L' := hf.trans subset_union_left
      have hfp : IsPathConnected (frontier Y) := by
        rw [IsClosedDisc.frontier_eq_discBd hS hd]
        obtain ⟨f⟩ := IsClosedDisc.isOArc_discBd hd
        have : discBd Y = range fun x : Circle => (f x).1 := by
          ext y
          constructor
          · intro hy
            obtain ⟨x, hx⟩ := f.surjective ⟨y, hy⟩
            exact ⟨x, by simp [hx]⟩
          · rintro ⟨x, rfl⟩
            exact (f x).2
        rw [this]
        exact isPathConnected_range (by fun_prop)
      have hcap : IsPathConnected (withDiscs X L' ∩ Y) :=
        theorem_7_10_proof hpc hYc (subBd_eq_frontier Y ▸ hfp) (subBd_eq_frontier Y ▸ hfs)
      rw [inter_comm] at hcap
      rw [heq]
      refine ⟨hYc.union hc, ?_, fun φ hφ => ?_⟩
      · obtain ⟨z, hz⟩ := hcap.nonempty
        exact (IsClosedDisc.isSimplyConnectedSet hd).1.union hpc ⟨z, hz⟩
      · obtain ⟨φ', hr, hh⟩ := hpush Y L' hs hcap φ hφ
        have hsub : Y ∪ withDiscs X L' ⊆ withDiscs X L := by
          rw [← heq]
          intro x hx
          rcases hx with hx | hx
          · exact Or.inl hx
          · obtain ⟨W, hW, hxW⟩ := mem_iUnion₂.mp hx
            exact Or.inr (mem_iUnion₂.mpr ⟨W, hs.subset hW, hxW⟩)
        obtain ⟨c, hc', hh'⟩ := hn φ' hr
        exact ⟨c, hc', (hh.mono hsub).trans hh'⟩
  exact ⟨(key L List.suffix_rfl).2.1, (key L List.suffix_rfl).2.2⟩

end GraphMinor.GM11
