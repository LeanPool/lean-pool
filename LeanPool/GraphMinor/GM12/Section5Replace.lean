/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section5Piece
import LeanPool.GraphMinor.GM07.Section11
import LeanPool.GraphMinor.Surface.DiscGrow

/-!
# Replacing finitely many pieces of an `O`-arc

The proof of Graph Minors XII, (5.3) (page 256), replaces each piece of `F` outside `Σ₂` by the line
that (5.4) gives on the common boundary. We do this for a finite set `J` of pieces, one at a time
(`exists_curve`). Each step does not add to the number of vertices on the curve, by the bound in
(5.4).
-/

public section

namespace GraphMinor.GM12

open Set Topology Metric GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM10 Hypergraph

local notation "𝕀" => unitInterval

universe u

variable {S T : Type u} [TopologicalSpace S] [T2Space S] [TopologicalSpace T] [T2Space T]
  {n : ℕ} {C : Fin n → Set S} {P₁ P₂ : Set S} {ι : P₁ → T}
  {Γ : Drawing S} {Γ₁ : Drawing T}
  {𝒯 : Set (Hypergraph T (Set T) × Hypergraph T (Set T))}

/-- The arcs of the pieces in a finite set `J` of gaps of `φ ⁻¹' P₂`, with the output of (5.4) for
each. -/
structure Pieces (C : Fin n → Set S) (P₂ : Set S) (ι : P₁ → T) (Γ : Drawing S) (Γ₁ : Drawing T)
    (𝒯 : Set (Hypergraph T (Set T) × Hypergraph T (Set T))) (φ : C(Circle, S)) (J : Finset
      (Set Circle))
    (a b : Set Circle → 𝕀 → Circle) (R : Set Circle → Set S) (Δ₁ : Set Circle → Set T)
    (Δ : Set Circle → Set S) : Prop where
  /-- Each member of `J` is a gap. -/
  gap : ∀ G ∈ J, IsGap (φ ⁻¹' P₂) G (a G) (b G)
  /-- Each gap has the data of (5.4). -/
  piece : ∀ G ∈ J, PieceData C ι Γ Γ₁ 𝒯 (φ '' range (a G)) (φ (a G 0)) (φ (a G 1)) (R G) (Δ₁ G)
    (Δ G)

variable {φ : C(Circle, S)} {J : Finset (Set Circle)} {a b : Set Circle → 𝕀 → Circle}
  {R : Set Circle → Set S} {Δ₁ : Set Circle → Set T} {Δ : Set Circle → Set S}

omit [T2Space S] in
theorem closedCurvesHomotopicIn_mono {Z Z' : Set S} {c c' : C(Circle, S)}
    (h : ClosedCurvesHomotopicIn Z c c') (hZ : Z ⊆ Z') : ClosedCurvesHomotopicIn Z' c c' := by
  obtain ⟨ψ, h1, h2, h3⟩ := h
  exact ⟨ψ, fun p => hZ (h1 p), h2, h3⟩

omit [T2Space S] in
theorem closedCurvesHomotopicIn_refl {Z : Set S} {c : C(Circle, S)} (hZ : ∀ x, c x ∈ Z) :
    ClosedCurvesHomotopicIn Z c c :=
  ⟨⟨fun p => c p.1, by fun_prop⟩, fun p => hZ p.1, fun _ => rfl, fun _ => rfl⟩

omit [T2Space S] in
/-- The count in one replacement. -/
theorem count_step {X R' L c' : Set S} {Y : Set S} {s t : S} (hV : Γ.V.Finite)
    (hXc : X ∩ Γ.V ⊆ Y ∩ Γ.V) (hc' : c' ∩ Γ.V ⊆ ((Y ∩ Γ.V) \ (X ∩ Γ.V)) ∪ ((R' \ {s, t}) ∩ Γ.V))
    (hL : L = X ∪ {s, t}) (hXs : Disjoint X {s, t}) (hR : ({s, t} : Set S) ⊆ R')
    (hcount : (R' ∩ Γ.V).ncard ≤ (L ∩ Γ.V).ncard) :
    (c' ∩ Γ.V).ncard ≤ (Y ∩ Γ.V).ncard := by
  classical
  have hf : ∀ Z : Set S, (Z ∩ Γ.V).Finite := fun Z => hV.subset inter_subset_right
  have hE : (({s, t} : Set S) ∩ Γ.V).Finite := hf _
  have h1 : (L ∩ Γ.V).ncard = (X ∩ Γ.V).ncard + (({s, t} : Set S) ∩ Γ.V).ncard := by
    rw [hL, union_inter_distrib_right]
    exact ncard_union_eq (hXs.mono inter_subset_left inter_subset_left) (hf _) hE
  have h2 : (R' ∩ Γ.V).ncard = ((R' \ {s, t}) ∩ Γ.V).ncard + (({s, t} : Set S) ∩ Γ.V).ncard := by
    have : R' ∩ Γ.V = ((R' \ {s, t}) ∩ Γ.V) ∪ (({s, t} : Set S) ∩ Γ.V) := by
      rw [← union_inter_distrib_right, sdiff_union_of_subset hR]
    rw [this]
    refine ncard_union_eq ?_ (hf _) hE
    exact (disjoint_sdiff_left.mono inter_subset_left inter_subset_left)
  have h3 : (X ∩ Γ.V).ncard + ((Y ∩ Γ.V) \ (X ∩ Γ.V)).ncard = (Y ∩ Γ.V).ncard := by
    have := ncard_sdiff_add_ncard_of_subset hXc (hf Y)
    omega
  have h4 := ncard_le_ncard hc' (((hf Y).subset sdiff_subset).union (hf _))
  have h5 := ncard_union_le ((Y ∩ Γ.V) \ (X ∩ Γ.V)) ((R' \ {s, t}) ∩ Γ.V)
  omega

omit [T2Space T] in
omit [T2Space S] in
/-- Replace the pieces in `J`, one at a time. -/
theorem exists_curve (hφ : Function.Injective φ) (hA : IsClosed (φ ⁻¹' P₂))
    (hC : ∀ k, C k ⊆ P₂) (hP : Pieces C P₂ ι Γ Γ₁ 𝒯 φ J a b R Δ₁ Δ) {Z : Set S}
    (hφZ : ∀ x, φ x ∈ Z) (hZ : ∀ G ∈ J, Δ G ⊆ Z) :
    ∃ c : C(Circle, S), (∀ x, (∀ G ∈ J, x ∉ G) → c x = φ x) ∧
      (∀ G ∈ J, ∀ x ∈ G, ∃ k, c x ∈ C k) ∧
      (range c ∩ Γ.V).ncard ≤ (range φ ∩ Γ.V).ncard ∧ ClosedCurvesHomotopicIn Z φ c := by
  classical
  induction J using Finset.induction_on with
  | empty => exact ⟨φ, fun _ _ => rfl, by simp, le_rfl, closedCurvesHomotopicIn_refl hφZ⟩
  | insert G J' hG ih =>
    have hP' : Pieces C P₂ ι Γ Γ₁ 𝒯 φ J' a b R Δ₁ Δ :=
      ⟨fun G' hG' => hP.gap G' (Finset.mem_insert_of_mem hG'),
        fun G' hG' => hP.piece G' (Finset.mem_insert_of_mem hG')⟩
    obtain ⟨c, hc1, hc2, hc3, hc4⟩ := ih hP' fun G' hG' => hZ G' (Finset.mem_insert_of_mem hG')
    have hgap := hP.gap G (Finset.mem_insert_self _ _)
    have hpc := hP.piece G (Finset.mem_insert_self _ _)
    have hcφ : ∀ t, c (a G t) = φ (a G t) := by
      intro t
      apply hc1
      intro G' hG' hmem
      by_cases ht : t = 0 ∨ t = 1
      · rcases ht with rfl | rfl
        · exact Set.disjoint_left.mp (hP.gap G' (Finset.mem_insert_of_mem hG')).disjoint hmem
            hgap.zero
        · exact Set.disjoint_left.mp (hP.gap G' (Finset.mem_insert_of_mem hG')).disjoint hmem
            hgap.one
      · push Not at ht
        have hmem' : a G t ∈ G := hgap.mem_iff.mpr ht
        rcases hgap.eq_or_disjoint hA (hP.gap G' (Finset.mem_insert_of_mem hG')) with he | hd
        · exact hG (he ▸ hG')
        · exact Set.disjoint_left.mp hd hmem' hmem
    obtain ⟨γ, hγ, hγr, hγ0, hγ1⟩ := hpc.line.exists_arc
    have hrc : ∀ x, c x ∈ Z := by
      obtain ⟨ψ, h1, -, h3⟩ := hc4
      exact fun x => h3 x ▸ h1 (x, 1)
    obtain ⟨c', hb', ha', hh⟩ := exists_replace hgap.two hgap.cover hγ.1
      (by rw [hγ0, hcφ]) (by rw [hγ1, hcφ]) hpc.disc
      (fun t => by rw [hcφ]; exact hpc.sub_L ⟨_, ⟨t, rfl⟩, rfl⟩)
      (fun t => hpc.sub_R (hγr ▸ ⟨t, rfl⟩))
    have hrb : ∀ x, x ∉ G → x ∈ range (b G) := by
      intro x hx
      by_contra hn
      exact hx (hgap.eq.symm.subset hn)
    refine ⟨c', ?_, ?_, ?_, ?_⟩
    · intro x hx
      have hxG : x ∉ G := hx G (Finset.mem_insert_self _ _)
      rw [hb' x (hrb x hxG)]
      exact hc1 x fun G' hG' => hx G' (Finset.mem_insert_of_mem hG')
    · intro G' hG' x hx
      rcases Finset.mem_insert.mp hG' with rfl | hG''
      · obtain ⟨t, rfl⟩ := hgap.subset_range hx
        obtain ⟨k, hk⟩ := hpc.on
        exact ⟨k, by rw [ha']; exact hk (hγr ▸ ⟨t, rfl⟩)⟩
      · have hxG : x ∉ G := fun hxG => by
          rcases hgap.eq_or_disjoint hA (hP.gap G' hG') with he | hd
          · exact hG (he ▸ hG'')
          · exact Set.disjoint_left.mp hd hxG hx
        rw [hb' x (hrb x hxG)]
        exact hc2 G' hG'' x hx
    · refine le_trans ?_ hc3
      have hL : φ '' range (a G) = (φ '' G) ∪ {φ (a G 0), φ (a G 1)} := by
        ext y
        constructor
        · rintro ⟨_, ⟨t, rfl⟩, rfl⟩
          by_cases h0 : t = 0
          · subst h0
            exact .inr (.inl rfl)
          by_cases h1 : t = 1
          · subst h1
            exact .inr (.inr rfl)
          exact .inl ⟨_, hgap.mem_iff.mpr ⟨h0, h1⟩, rfl⟩
        · rintro (⟨x, hx, rfl⟩ | rfl | rfl)
          · exact ⟨x, hgap.subset_range hx, rfl⟩
          · exact ⟨_, ⟨0, rfl⟩, rfl⟩
          · exact ⟨_, ⟨1, rfl⟩, rfl⟩
      have hXs : Disjoint (φ '' G) {φ (a G 0), φ (a G 1)} := by
        refine Set.disjoint_left.mpr ?_
        rintro _ ⟨x, hx, rfl⟩ (he | he)
        · rw [hφ he] at hx
          exact Set.disjoint_left.mp hgap.disjoint hx hgap.zero
        · rw [hφ he] at hx
          exact Set.disjoint_left.mp hgap.disjoint hx hgap.one
      have hends : ({φ (a G 0), φ (a G 1)} : Set S) ⊆ R G := by
        rintro _ (rfl | rfl)
        · exact hpc.line.left_mem
        · exact hpc.line.right_mem
      have hoffP : ∀ y ∈ φ '' G, y ∉ P₂ := by
        rintro _ ⟨x, hx, rfl⟩ hmem
        exact Set.disjoint_left.mp hgap.disjoint hx hmem
      refine count_step Γ.finite_V ?_ ?_ hL hXs hends hpc.count
      · rintro _ ⟨⟨x, hx, rfl⟩, hV⟩
        have hxr : x ∈ range (a G) := hgap.subset_range hx
        obtain ⟨t, rfl⟩ := hxr
        exact ⟨⟨_, hcφ t⟩, hV⟩
      · rintro _ ⟨⟨x, rfl⟩, hV⟩
        by_cases hxG : x ∈ G
        · obtain ⟨t, rfl⟩ := hgap.subset_range hxG
          rw [ha'] at hV ⊢
          by_cases hend : γ t ∈ ({φ (a G 0), φ (a G 1)} : Set S)
          · refine .inl ⟨⟨?_, hV⟩, fun hn => hoffP _ hn.1 ?_⟩
            · rcases hend with he | he
              · exact ⟨a G 0, by rw [hcφ, he]⟩
              · exact ⟨a G 1, by rw [hcφ, he]⟩
            · rcases hend with he | he
              · rw [he]
                exact hgap.zero
              · rw [he]
                exact hgap.one
          · exact .inr ⟨⟨hγr ▸ ⟨t, rfl⟩, hend⟩, hV⟩
        · rw [hb' x (hrb x hxG)] at hV ⊢
          refine .inl ⟨⟨⟨x, rfl⟩, hV⟩, fun hn => hoffP _ hn.1 ?_⟩
          by_cases hgaps : ∀ G' ∈ J', x ∉ G'
          · have he := hc1 x hgaps
            obtain ⟨x', hx', hxe⟩ := hn.1
            rw [he] at hxe
            rw [hφ hxe] at hx'
            exact absurd hx' hxG
          · push Not at hgaps
            obtain ⟨G', hG', hx'⟩ := hgaps
            obtain ⟨k, hk⟩ := hc2 G' hG' x hx'
            exact hC k hk
    · apply hc4.trans (closedCurvesHomotopicIn_mono hh (union_subset ?_ ?_))
      · rintro _ ⟨x, rfl⟩
        exact hrc x
      · exact hZ G (Finset.mem_insert_self _ _)

end GraphMinor.GM12
