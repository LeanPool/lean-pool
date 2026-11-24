/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section12a
public import LeanPool.GraphMinor.GM19.Section10l

/-!
# Graph Minors XIX, Section 12: growing a disc along a chord

A disc whose boundary is a circuit of `Γ*` grows along a chord outside it. This is the step "and
subject to that with
`D(F)` maximal" of the proof of (12.1). The main result is `exists_larger_circuit`.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11

section Chord

variable {T : Type} [TopologicalSpace T] [T2Space T]

omit [T2Space T] in
theorem _root_.GraphMinor.Surface.IsLineWithEnds.exists_arcMap {L : Set T} {s t : T}
  (h : IsLineWithEnds L s t) :
    ∃ a : unitInterval → T, IsArcMap a ∧ range a = L ∧ a 0 = s ∧ a 1 = t := by
  obtain ⟨f, h0, h1⟩ := h
  refine ⟨fun x ↦ (f x).1, ⟨continuous_subtype_val.comp f.continuous,
    fun x y hxy ↦ f.injective (Subtype.ext hxy)⟩, ?_, h0, h1⟩
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact (f x).2
  · intro hy
    exact ⟨f.symm ⟨y, hy⟩, by simp⟩

omit [T2Space T] in
/-- A line has a point besides its two ends. -/
theorem _root_.GraphMinor.Surface.IsLineWithEnds.exists_ne_ends {L : Set T} {s t : T}
  (h : IsLineWithEnds L s t) : ∃ x ∈ L, x ≠ s ∧ x ≠ t := by
  obtain ⟨a, ha, rfl, rfl, rfl⟩ := h.exists_arcMap
  let m : unitInterval := ⟨1 / 2, by norm_num, by norm_num⟩
  refine ⟨a m, ⟨m, rfl⟩, fun h ↦ ?_, fun h ↦ ?_⟩
  · have := congrArg Subtype.val (ha.2 h)
    norm_num [m] at this
  · have := congrArg Subtype.val (ha.2 h)
    norm_num [m] at this

/-- **A chord of a disc inside a bigger disc.** The boundary of `W` is the union of two lines `A`,
`B` with the same ends
`s`, `t`, and the line `L` with these ends misses `W` otherwise. Then a bigger disc in `Δ` has
boundary `L ∪ A` or `L ∪ B`. -/
theorem exists_larger_disc (hT : IsClosedSurface T) {Δ W A B L : Set T} {s t : T}
  (hΔ : IsClosedDisc Δ)
    (hW : IsClosedDisc W) (hWΔ : W ⊆ Δ) (hLΔ : L ⊆ Δ) (hA : IsLineWithEnds A s t)
      (hB : IsLineWithEnds B s t)
    (hL : IsLineWithEnds L s t) (hAB : A ∪ B = discBd W) (hAB' : A ∩ B = {s, t}) (hLW : L ∩ W
      = {s, t}) :
    ∃ W', W' ⊆ Δ ∧ IsClosedDisc W' ∧ W ⊂ W' ∧ (discBd W' = L ∪ A ∨ discBd W' = L ∪ B) := by
  have hman : ∀ x : T, IsManifoldPoint x := (Surface.IsClosedSurface.isSurface hT).2.2
  obtain ⟨a, ha, hra, ha0, ha1⟩ := hA.exists_arcMap
  obtain ⟨l, hl, hrl, hl0, hl1⟩ := hL.exists_arcMap
  have hAW : A ⊆ W := (subset_union_left.trans hAB.le).trans (Surface.discBd_subset W)
  have hBW : B ⊆ W := (subset_union_right.trans hAB.le).trans (Surface.discBd_subset W)
  have hmeet : ∀ x y, a x = l y → (x = 0 ∧ y = 0) ∨ (x = 1 ∧ y = 1) := by
    intro x y he
    have hm : a x ∈ L ∩ W := ⟨hrl ▸ ⟨y, he.symm⟩, hAW (hra ▸ ⟨x, rfl⟩)⟩
    rw [hLW] at hm
    rcases hm with hm | hm
    · have hx : x = 0 := ha.2 (hm.trans ha0.symm)
      have hy : y = 0 := hl.2 (by rw [← he, hx, ha0, hl0])
      exact .inl ⟨hx, hy⟩
    · have hx : x = 1 := ha.2 (hm.trans ha1.symm)
      have hy : y = 1 := hl.2 (by rw [← he, hx, ha1, hl1])
      exact .inr ⟨hx, hy⟩
  have hO : IsOArc (A ∪ L) := by
    rw [← hra, ← hrl]
    exact oArc_of_two_arcs ha hl (ha0.trans hl0.symm) (ha1.trans hl1.symm) hmeet
  have hsub : A ∪ L ⊆ Δ := union_subset (hAW.trans hWΔ) hLΔ
  obtain ⟨Δ₁, ⟨hΔ₁Δ, hΔ₁, hb₁, -⟩, -⟩ := disc_oArc Δ (A ∪ L) hΔ hsub hO
  have hsub₁ : A ∪ L ⊆ Δ₁ := hb₁ ▸ Surface.discBd_subset Δ₁
  have hsL : s ∈ L ∧ t ∈ L := by
    rw [← hl0, ← hl1, ← hrl]
    exact ⟨⟨0, rfl⟩, ⟨1, rfl⟩⟩
  have hsA : s ∈ A ∧ t ∈ A := by
    rw [← ha0, ← ha1, ← hra]
    exact ⟨⟨0, rfl⟩, ⟨1, rfl⟩⟩
  have hdisj : Disjoint (discInt W) (discBd Δ₁) := by
    rw [hb₁, disjoint_left]
    rintro x ⟨hx, hx'⟩ (h | h)
    · exact hx' (hAB ▸ Or.inl h)
    · have : x ∈ L ∩ W := ⟨h, hx⟩
      rw [hLW] at this
      apply hx'
      rw [← hAB]
      exact Or.inl (by rcases this with rfl | rfl; exacts [hsA.1, hsA.2])
  obtain ⟨y, hyL, hys, hyt⟩ := hL.exists_ne_ends
  have hyW : y ∉ W := fun h ↦ by
    have : y ∈ L ∩ W := ⟨hyL, h⟩
    rw [hLW] at this
    rcases this with h | h
    exacts [hys h, hyt h]
  rcases hΔ₁.side hman hW.isPreconnected_discInt hdisj with hin | hout
  · refine ⟨Δ₁, hΔ₁Δ, hΔ₁, ⟨?_, fun h ↦ hyW (h (hsub₁ (Or.inr hyL)))⟩, .inl (by rw [hb₁,
      Set.union_comm])⟩
    exact hW.subset_closure_discInt.trans (closure_minimal (hin.trans sdiff_subset) hΔ₁.isClosed)
  have hbout : ∀ x ∈ B, x ≠ s → x ≠ t → x ∉ Δ₁ := by
    intro x hxB hxs hxt hmem
    have hxb : x ∉ discBd Δ₁ := by
      rw [hb₁]
      rintro (h | h)
      · have : x ∈ A ∩ B := ⟨h, hxB⟩
        rw [hAB'] at this
        rcases this with h | h
        exacts [hxs h, hxt h]
      · have : x ∈ L ∩ W := ⟨h, hBW hxB⟩
        rw [hLW] at this
        rcases this with h | h
        exacts [hxs h, hxt h]
    have hcl : x ∈ closure (discInt W) := hW.subset_closure_discInt (hBW hxB)
    obtain ⟨w, hw1, hw2⟩ := mem_closure_iff.mp hcl _ (hΔ₁.isOpen_discInt hman) ⟨hmem, hxb⟩
    exact disjoint_left.mp hout hw2 hw1.1
  have hinter : Δ₁ ∩ W = A := by
    ext x
    constructor
    · rintro ⟨hx, hx'⟩
      by_cases hb : x ∈ discBd W
      · rw [← hAB] at hb
        rcases hb with hb | hb
        · exact hb
        · by_cases hxs : x = s
          · exact hxs ▸ hsA.1
          by_cases hxt : x = t
          · exact hxt ▸ hsA.2
          exact absurd hx (hbout x hb hxs hxt)
      · exact absurd hx (disjoint_left.mp hout ⟨hx', hb⟩)
    · intro hx
      exact ⟨hsub₁ (Or.inl hx), hAW hx⟩
  have hu := disc_union.{0} Δ₁ W A s t hΔ₁ hW hA hinter (hb₁ ▸ subset_union_left)
    (hAB ▸ subset_union_left)
  refine ⟨Δ₁ ∪ W, union_subset hΔ₁Δ hWΔ, hu.1, ⟨subset_union_right, fun h ↦ ?_⟩, .inr ?_⟩
  · exact hyW (h (Or.inl (hsub₁ (Or.inr hyL))))
  · rw [hu.2, hb₁, ← hAB]
    ext x
    have hends : ∀ {x}, x = s ∨ x = t → x ∈ L := fun h ↦ by
      rcases h with rfl | rfl
      exacts [hsL.1, hsL.2]
    have hLA : x ∈ L → x ∈ A → x = s ∨ x = t := fun h h' ↦ by
      have : x ∈ L ∩ W := ⟨h, hAW h'⟩
      rwa [hLW] at this
    have hBA : x ∈ A → x ∈ B → x = s ∨ x = t := fun h h' ↦ by
      have : x ∈ A ∩ B := ⟨h, h'⟩
      rwa [hAB'] at this
    simp only [mem_sdiff, mem_union, mem_insert_iff, mem_singleton_iff]
    constructor
    · rintro ⟨h, hn⟩
      by_cases hst : x = s ∨ x = t
      · exact .inl (hends hst)
      · rcases h with (h | h) | (h | h)
        · exact absurd ⟨h, hst⟩ hn
        · exact .inl h
        · exact absurd ⟨h, hst⟩ hn
        · exact .inr h
    · rintro (h | h)
      · exact ⟨.inl (.inr h), fun ⟨h', hn⟩ ↦ hn (hLA h h')⟩
      · exact ⟨.inr (.inr h), fun ⟨h', hn⟩ ↦ hn (hBA h' h)⟩

end Chord

end GraphMinor.GM19
