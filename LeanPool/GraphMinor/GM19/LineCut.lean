/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.FragmentShape
import LeanPool.GraphMinor.GM19.Section6Cuff

/-!
# Lines and `O`-arcs cut at a finite set

A line with `m` marked points, its two ends among them, falls into `m - 1` open arcs, each with two
of the marked points as ends. An
`O`-arc with `m ≥ 2` marked points falls into `m` open arcs. The proof of (10.5) uses this twice. It
tells how many edges a circuit
has once we forget its vertices that are off `Γ`, and how many sides of the frame lie in an arc of a
cuff.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface

variable {T : Type} [TopologicalSpace T] [T2Space T]

omit [T2Space T] in
/-- A path-connected set off `N` lies in one of two closed sets that cover it and meet only in `N`.
-/
theorem subset_or_of_closed {X Y N C : Set T} (hX : IsClosed X) (hY : IsClosed Y) (hXY : X ∩ Y ⊆ N)
    (hC : IsPathConnected C) (hsub : C ⊆ (X ∪ Y) \ N) : C ⊆ X ∨ C ⊆ Y := by
  have hp := hC.isConnected.isPreconnected
  by_contra hno
  push Not at hno
  obtain ⟨hnX, hnY⟩ := hno
  obtain ⟨a, ha, haX⟩ := not_subset.1 hnX
  obtain ⟨b, hb, hbY⟩ := not_subset.1 hnY
  have haY : a ∈ Y := ((hsub ha).1).resolve_left haX
  have hbX : b ∈ X := ((hsub hb).1).resolve_right hbY
  obtain ⟨z, hz, hz₁, hz₂⟩ := isPreconnected_closed_iff.mp hp X Y hX hY (fun z hz ↦
    (hsub hz).1) ⟨b, hb, hbX⟩ ⟨a, ha, haY⟩
  exact (hsub hz).2 (hXY ⟨hz₁, hz₂⟩)

omit [T2Space T] in
/-- The arcs of a union of two closed sets that meet only in `N` are the arcs of the two sets. -/
theorem arcComponentsIn_union_sdiff {X Y N : Set T} (hX : IsClosed X) (hY : IsClosed Y)
  (hXY : X ∩ Y ⊆ N) :
    arcComponentsIn ((X ∪ Y) \ N) = arcComponentsIn (X \ N) ∪ arcComponentsIn (Y \ N) := by
  have hsX : X \ N ⊆ (X ∪ Y) \ N := sdiff_subset_sdiff_left subset_union_left
  have hsY : Y \ N ⊆ (X ∪ Y) \ N := sdiff_subset_sdiff_left subset_union_right
  ext C
  constructor
  · rintro ⟨hne, hsub, hC, hmax⟩
    have key : ∀ {W : Set T}, W \ N ⊆ (X ∪ Y) \ N → C ⊆ W → C ∈ arcComponentsIn (W \ N)
      := fun {W} hW hCW ↦
      ⟨hne, fun x hx ↦ ⟨hCW hx, (hsub hx).2⟩, hC, fun D hD hDc hCD ↦ hmax D (hD.trans hW) hDc hCD⟩
    rcases subset_or_of_closed hX hY hXY hC hsub with h | h
    · exact Or.inl (key hsX h)
    · exact Or.inr (key hsY h)
  · have key : ∀ {W W' : Set T}, IsClosed W → IsClosed W' → W ∩ W' ⊆ N → W \ N ⊆ (X ∪ Y) \ N →
    (X ∪ Y) = W ∪ W' →
        C ∈ arcComponentsIn (W \ N) → C ∈ arcComponentsIn ((X ∪ Y) \ N) := by
      rintro W W' h₁ h₂ h₃ hW hun ⟨hne, hsub, hC, hmax⟩
      refine ⟨hne, hsub.trans hW, hC, fun D hD hDc hCD ↦ hmax D ?_ hDc hCD⟩
      rw [hun] at hD
      rcases subset_or_of_closed h₁ h₂ h₃ hDc hD with h | h
      · exact fun x hx ↦ ⟨h hx, (hD hx).2⟩
      · obtain ⟨x, hx⟩ := hne
        exact absurd h₃ fun hc ↦ (hD (hCD hx)).2 (hc ⟨(hsub hx).1, h (hCD hx)⟩)
    rintro (h | h)
    · exact key hX hY hXY hsX rfl h
    · exact key hY hX (by rwa [inter_comm]) hsY (union_comm _ _) h

/-- The shape of an open arc cut from a line or an `O`-arc. -/
def IsMarkedArc (N e : Set T) : Prop :=
  ∃ u v, u ≠ v ∧ closure e ∩ N = {u, v} ∧ IsLineWithEnds (closure e) u v

omit [T2Space T] in
theorem line_isPathConnected_sdiff {L : Set T} {a b : T} (h : IsLineWithEnds L a b) :
  IsPathConnected (L \ {a, b}) := by
  obtain ⟨c, hc, hr, h0, h1⟩ := h.exists_arc
  rw [IsLineWithEnds.diff_eq hc hr h0 h1]
  exact ((convex_Ioo (0 : ℝ) 1).isPathConnected (nonempty_Ioo.2 zero_lt_one)).image'
    (continuous_extI hc.1).continuousOn

/-- **A line cut at a finite set.** -/
theorem arcs_of_line : ∀ (m : ℕ) {N L : Set T} {a b : T}, N.Finite → N.ncard = m
  → IsLineWithEnds L a b → a ∈ N → b ∈ N → N ⊆ L →
    (arcComponentsIn (L \ N)).Finite ∧ (arcComponentsIn (L \ N)).ncard + 1 = N.ncard ∧
      ∀ e ∈ arcComponentsIn (L \ N), IsMarkedArc N e ∧ e ⊆ L := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro N L a b hN hm hL ha hb hNL
    have hab : a ≠ b := (ends_of_line hL).2.2
    by_cases hx : ∃ x ∈ N, x ≠ a ∧ x ≠ b
    · obtain ⟨x, hxN, hxa, hxb⟩ := hx
      obtain ⟨L₁, L₂, h₁, h₂, hun, hint⟩ := hL.split (hNL hxN) hxa hxb
      have hc₁ := isClosed_of_cuffLine h₁
      have hc₂ := isClosed_of_cuffLine h₂
      have hxL₁ := (ends_of_line h₁).2.1
      have hxL₂ := (ends_of_line h₂).1
      have haL := (ends_of_line h₁).1
      have hbL := (ends_of_line h₂).2.1
      have hbn₁ : b ∉ L₁ := fun h ↦ hxb (by
        have : b ∈ L₁ ∩ L₂ := ⟨h, hbL⟩
        rw [hint] at this
        exact this.symm)
      have han₂ : a ∉ L₂ := fun h ↦ hxa (by
        have : a ∈ L₁ ∩ L₂ := ⟨haL, h⟩
        rw [hint] at this
        exact this.symm)
      have hsub₁ : N ∩ L₁ ⊂ N := ⟨inter_subset_left, fun h ↦ hbn₁ (h hb).2⟩
      have hsub₂ : N ∩ L₂ ⊂ N := ⟨inter_subset_left, fun h ↦ han₂ (h ha).2⟩
      have hl₁ : (N ∩ L₁).ncard < m := hm ▸ ncard_lt_ncard hsub₁ hN
      have hl₂ : (N ∩ L₂).ncard < m := hm ▸ ncard_lt_ncard hsub₂ hN
      obtain ⟨f₁, n₁, s₁⟩ := ih _ hl₁ (hN.subset inter_subset_left) rfl h₁ ⟨ha, haL⟩ ⟨hxN, hxL₁⟩
        inter_subset_right
      obtain ⟨f₂, n₂, s₂⟩ := ih _ hl₂ (hN.subset inter_subset_left) rfl h₂ ⟨hxN, hxL₂⟩ ⟨hb, hbL⟩
        inter_subset_right
      have hXN : L₁ ∩ L₂ ⊆ N := by
        rw [hint]
        rintro _ rfl
        exact hxN
      have hs₁ : L₁ \ (N ∩ L₁) = L₁ \ N := by
        ext z
        simp only [mem_sdiff, mem_inter_iff, not_and]
        exact ⟨fun h ↦ ⟨h.1, fun hz ↦ h.2 hz h.1⟩, fun h ↦ ⟨h.1, fun hz ↦ absurd hz h.2⟩⟩
      have hs₂ : L₂ \ (N ∩ L₂) = L₂ \ N := by
        ext z
        simp only [mem_sdiff, mem_inter_iff, not_and]
        exact ⟨fun h ↦ ⟨h.1, fun hz ↦ h.2 hz h.1⟩, fun h ↦ ⟨h.1, fun hz ↦ absurd hz h.2⟩⟩
      rw [hs₁] at f₁ n₁ s₁
      rw [hs₂] at f₂ n₂ s₂
      have hA : arcComponentsIn (L \ N) = arcComponentsIn (L₁ \ N) ∪ arcComponentsIn (L₂ \ N) := by
        rw [← hun]
        exact arcComponentsIn_union_sdiff hc₁ hc₂ hXN
      have hdisj : Disjoint (arcComponentsIn (L₁ \ N)) (arcComponentsIn (L₂ \ N))
        := disjoint_left.2 fun e he₁ he₂ ↦ by
        obtain ⟨z, hz⟩ := he₁.1
        exact (he₁.2.1 hz).2 (hXN ⟨(he₁.2.1 hz).1, (he₂.2.1 hz).1⟩)
      have hcard : (N ∩ L₁).ncard + (N ∩ L₂).ncard = N.ncard + 1 := by
        have hu : (N ∩ L₁) ∪ (N ∩ L₂) = N := by
          rw [← inter_union_distrib_left, hun]
          exact inter_eq_left.2 hNL
        have hi : (N ∩ L₁) ∩ (N ∩ L₂) = {x} := by
          ext z
          constructor
          · rintro ⟨⟨-, h₁'⟩, -, h₂'⟩
            have : z ∈ L₁ ∩ L₂ := ⟨h₁', h₂'⟩
            rwa [hint] at this
          · rintro rfl
            exact ⟨⟨hxN, hxL₁⟩, hxN, hxL₂⟩
        have := ncard_union_add_ncard_inter (N ∩ L₁) (N ∩ L₂) (hN.subset inter_subset_left)
          (hN.subset inter_subset_left)
        rw [hu, hi, ncard_singleton] at this
        omega
      rw [hA]
      refine ⟨f₁.union f₂, ?_, ?_⟩
      · rw [ncard_union_eq hdisj f₁ f₂]
        omega
      · have conv : ∀ {W e : Set T}, IsMarkedArc (N ∩ W) e → e ∈ arcComponentsIn (W \ N)
        → IsClosed W → W ⊆ L → IsMarkedArc N e ∧ e ⊆ L := by
          rintro W e ⟨u, v, huv, hs, hl⟩ he hW hWL
          have hclo : closure e ⊆ W := closure_minimal (fun z hz ↦ (he.2.1 hz).1) hW
          refine ⟨⟨u, v, huv, ?_, hl⟩, (subset_closure.trans hclo).trans hWL⟩
          rw [← hs]
          ext z
          exact ⟨fun h ↦ ⟨h.1, h.2, hclo h.1⟩, fun h ↦ ⟨h.1, h.2.1⟩⟩
        rintro e (he | he)
        · exact conv (s₁ e he).1 he hc₁ (hun ▸ subset_union_left)
        · exact conv (s₂ e he).1 he hc₂ (hun ▸ subset_union_right)
    · push Not at hx
      have hNe : N = {a, b} := by
        apply Subset.antisymm
        · intro z hz
          by_cases hza : z = a
          · exact Or.inl hza
          · exact Or.inr (hx z hz hza)
        · rintro _ (rfl | h)
          · exact ha
          · exact (mem_singleton_iff.1 h) ▸ hb
      subst hNe
      have hpc := line_isPathConnected_sdiff hL
      have hne := hpc.nonempty
      have hA : arcComponentsIn (L \ {a, b}) = {L \ {a, b}} := by
        ext e
        constructor
        · intro he
          exact (he.2.2.2 _ Subset.rfl hpc he.2.1).symm
        · rintro rfl
          exact ⟨hne, Subset.rfl, hpc, fun D hD _ hsub ↦ Subset.antisymm hD hsub⟩
      have hcl : closure (L \ {a, b}) = L :=
        Subset.antisymm (closure_minimal sdiff_subset (isClosed_of_cuffLine hL))
          hL.subset_closure_diff
      rw [hA, ncard_singleton, ncard_pair hab]
      refine ⟨finite_singleton _, rfl, ?_⟩
      rintro _ rfl
      refine ⟨⟨a, b, hab, ?_, ?_⟩, sdiff_subset⟩
      · rw [hcl]
        exact inter_eq_right.2 hNL
      · rw [hcl]
        exact hL

/-- **An `O`-arc cut at a finite set.** -/
theorem arcs_of_oArc {N F : Set T} (hN : N.Finite) (hF : IsOArc F) (hNF : N ⊆ F) (h2 : 2
  ≤ N.ncard) :
    (arcComponentsIn (F \ N)).Finite ∧ (arcComponentsIn (F \ N)).ncard = N.ncard ∧
      ∀ e ∈ arcComponentsIn (F \ N), IsMarkedArc N e ∧ e ⊆ F := by
  obtain ⟨x, hx, y, hy, hxy⟩ := (one_lt_ncard hN).1 h2
  obtain ⟨A, B, hA, hB, hun, hint⟩ := hF.lines (hNF hx) (hNF hy) hxy
  have hcA := isClosed_of_cuffLine hA
  have hcB := isClosed_of_cuffLine hB
  have hxA := (ends_of_line hA).1
  have hyA := (ends_of_line hA).2.1
  have hxB := (ends_of_line hB).1
  have hyB := (ends_of_line hB).2.1
  obtain ⟨f₁, n₁, s₁⟩ := arcs_of_line _ (hN.subset inter_subset_left) rfl hA ⟨hx, hxA⟩ ⟨hy, hyA⟩
    inter_subset_right
  obtain ⟨f₂, n₂, s₂⟩ := arcs_of_line _ (hN.subset inter_subset_left) rfl hB ⟨hx, hxB⟩ ⟨hy, hyB⟩
    inter_subset_right
  have hXN : A ∩ B ⊆ N := by
    rw [hint]
    rintro _ (rfl | h)
    · exact hx
    · exact (mem_singleton_iff.1 h) ▸ hy
  have hs : ∀ W : Set T, W \ (N ∩ W) = W \ N := fun W ↦ by
    ext z
    simp only [mem_sdiff, mem_inter_iff, not_and]
    exact ⟨fun h ↦ ⟨h.1, fun hz ↦ h.2 hz h.1⟩, fun h ↦ ⟨h.1, fun hz ↦ absurd hz h.2⟩⟩
  rw [hs] at f₁ n₁ s₁ f₂ n₂ s₂
  have hA' : arcComponentsIn (F \ N) = arcComponentsIn (A \ N) ∪ arcComponentsIn (B \ N) := by
    rw [← hun]
    exact arcComponentsIn_union_sdiff hcA hcB hXN
  have hdisj : Disjoint (arcComponentsIn (A \ N)) (arcComponentsIn (B \ N))
    := disjoint_left.2 fun e he₁ he₂ ↦ by
    obtain ⟨z, hz⟩ := he₁.1
    exact (he₁.2.1 hz).2 (hXN ⟨(he₁.2.1 hz).1, (he₂.2.1 hz).1⟩)
  have hcard : (N ∩ A).ncard + (N ∩ B).ncard = N.ncard + 2 := by
    have hu : (N ∩ A) ∪ (N ∩ B) = N := by
      rw [← inter_union_distrib_left, hun]
      exact inter_eq_left.2 hNF
    have hi : (N ∩ A) ∩ (N ∩ B) = {x, y} := by
      ext z
      constructor
      · rintro ⟨⟨-, h₁'⟩, -, h₂'⟩
        have : z ∈ A ∩ B := ⟨h₁', h₂'⟩
        rwa [hint] at this
      · rintro (rfl | h)
        · exact ⟨⟨hx, hxA⟩, hx, hxB⟩
        · rw [mem_singleton_iff.1 h]
          exact ⟨⟨hy, hyA⟩, hy, hyB⟩
    have := ncard_union_add_ncard_inter (N ∩ A) (N ∩ B) (hN.subset inter_subset_left)
      (hN.subset inter_subset_left)
    rw [hu, hi, ncard_pair hxy] at this
    omega
  rw [hA']
  refine ⟨f₁.union f₂, ?_, ?_⟩
  · rw [ncard_union_eq hdisj f₁ f₂]
    omega
  · have conv : ∀ {W e : Set T}, IsMarkedArc (N ∩ W) e → e ∈ arcComponentsIn (W \ N) → IsClosed W
    → W ⊆ F → IsMarkedArc N e ∧ e ⊆ F := by
      rintro W e ⟨u, v, huv, hs, hl⟩ he hW hWL
      have hclo : closure e ⊆ W := closure_minimal (fun z hz ↦ (he.2.1 hz).1) hW
      refine ⟨⟨u, v, huv, ?_, hl⟩, (subset_closure.trans hclo).trans hWL⟩
      rw [← hs]
      ext z
      exact ⟨fun h ↦ ⟨h.1, h.2, hclo h.1⟩, fun h ↦ ⟨h.1, h.2.1⟩⟩
    rintro e (he | he)
    · exact conv (s₁ e he).1 he hcA (hun ▸ subset_union_left)
    · exact conv (s₂ e he).1 he hcB (hun ▸ subset_union_right)

omit [T2Space T] in
/-- A finite set does not cut points off a line. -/
theorem line_subset_closure_sdiff {L N : Set T} {a b : T} (hl : IsLineWithEnds L a b)
  (hN : N.Finite) : L ⊆ closure (L \ N) := by
  obtain ⟨f, -, -⟩ := hl
  let g : unitInterval → T := fun t ↦ (f t).1
  have hg : Continuous g := continuous_subtype_val.comp f.continuous
  have hginj : Function.Injective g := fun u v h ↦ f.injective (Subtype.ext h)
  have hd : Dense (g ⁻¹' N)ᶜ := by
    have := (dense_univ (X := unitInterval)).sdiff_finite (hN.preimage hginj.injOn)
    rwa [compl_eq_univ_sdiff]
  intro x hx
  have hmem : (f.symm ⟨x, hx⟩) ∈ closure (g ⁻¹' N)ᶜ := hd _
  have := image_closure_subset_closure_image hg (mem_image_of_mem g hmem)
  have hgx : g (f.symm ⟨x, hx⟩) = x := by simp [g]
  rw [hgx] at this
  refine closure_mono ?_ this
  rintro _ ⟨t, ht, rfl⟩
  exact ⟨(f t).2, ht⟩

/-- A finite set does not cut points off an `O`-arc with two points. -/
theorem oArc_subset_closure_sdiff {F N : Set T} (hF : IsOArc F) {x y : T} (hx : x ∈ F) (hy : y ∈ F)
  (hxy : x ≠ y) (hN : N.Finite) :
    F ⊆ closure (F \ N) := by
  obtain ⟨A, B, hA, hB, hun, -⟩ := hF.lines hx hy hxy
  rw [← hun]
  refine union_subset ((line_subset_closure_sdiff hA hN).trans (closure_mono ?_))
    ((line_subset_closure_sdiff hB hN).trans (closure_mono ?_))
  · exact sdiff_subset_sdiff_left subset_union_left
  · exact sdiff_subset_sdiff_left subset_union_right

end GraphMinor.GM19
