/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.FreeTopology
public import LeanPool.GraphMinor.GM19.LineCut
import LeanPool.GraphMinor.GM19.Section6Cuff

/-!
# A disc around a cuff disc and finitely many bites

Let `E` be a closed disc, and let `Δ i` be closed discs, each with a chord `β i` of `E` on its
boundary. If two of the `Δ i` meet only inside `E`, then `E` and all the `Δ i` make one closed
disc `Z`. This is `exists_outer_half` used once for each `i`, and the result is `exists_disc_union`.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface

variable {T : Type} [TopologicalSpace T] [T2Space T] {ι : Type}

/-- A closed disc with a chord of `E` on its boundary, as in `exists_outer_half`. -/
structure IsChordDisc (E Δ β : Set T) (s t : T) : Prop where
  disc : IsClosedDisc Δ
  ne : s ≠ t
  line : IsLineWithEnds β s t
  on_bd : β ⊆ discBd Δ
  in_E : β ⊆ E
  meet : β ∩ discBd E = {s, t}
  off : discInt E ∩ discBd Δ ⊆ β
  touch : ∀ x ∈ discBd E ∩ discBd Δ, x ∉ β → ∃ C, C ⊆ discInt E \ β ∧ C ⊆ Δ ∧ C.Nonempty
    ∧ IsPreconnected C ∧ x ∈ closure C

/-- **The disc around `E` and the `Δ i`.** -/
theorem exists_disc_union (hT : IsClosedSurface T) {E : Set T}
  (hE : IsClosedDisc E) (ℐ : Finset ι) (Δ β : ι → Set T) (s t : ι → T)
    (h : ∀ i ∈ ℐ, IsChordDisc E (Δ i) (β i) (s i) (t i)) (hsep : ∀ i ∈ ℐ, ∀ j ∈ ℐ, i ≠ j
      → Δ i ∩ Δ j ⊆ discInt E) :
    ∃ Z, IsClosedDisc Z ∧ E ⊆ Z ∧ (∀ i ∈ ℐ, Δ i ⊆ Z) ∧ Z ⊆ E ∪ ⋃ i ∈ ℐ, Δ i ∧ discInt E ⊆ discInt Z
      ∧ (∀ x, x ∉ discInt E → (x ∈ discInt Z ↔ ∃ i ∈ ℐ, x ∈ discInt (Δ i))) ∧
      discBd Z ⊆ discBd E ∪ ⋃ i ∈ ℐ, discBd (Δ i) \ discInt E ∧ discBd E \
        (⋃ i ∈ ℐ, Δ i) ⊆ discBd Z ∧ ∀ i ∈ ℐ, discBd (Δ i) \ (β i \ {s i, t i}) ⊆ discBd Z := by
  classical
  induction ℐ using Finset.induction_on with
  | empty =>
    refine ⟨E, hE, Subset.rfl, by simp, by simp, Subset.rfl, fun x hx ↦ ?_, by simp, by simp,
      by simp⟩
    simpa using hx
  | insert a ℐ ha ih =>
    obtain ⟨Y, hY, hEY, hΔY, hYc, hintY, hJ3, hJ1, hJ2, hJ4⟩ := ih (fun i hi ↦ h i
      (Finset.mem_insert_of_mem hi))
      (fun i hi j hj hne ↦ hsep i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hne)
    have hA := h a (Finset.mem_insert_self _ _)
    have hbdsub : ∀ {D : Set T}, discBd D ⊆ D := fun {D} ↦ Surface.discBd_subset D
    have hne : ∀ j ∈ ℐ, a ≠ j := fun j hj he ↦ ha (he ▸ hj)
    have hsepa : ∀ j ∈ ℐ, Δ a ∩ Δ j ⊆ discInt E := fun j hj ↦ hsep a (Finset.mem_insert_self _ _) j
      (Finset.mem_insert_of_mem hj) (hne j hj)
    have hoffE : ∀ {x}, x ∈ β a → x ∈ discBd Y → x ∈ ({s a, t a} : Set T) := by
      intro x hxβ hxY
      rcases hJ1 hxY with h' | h'
      · exact hA.meet ▸ ⟨hxβ, h'⟩
      · obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.1 h'
        exact absurd (hsepa j hj ⟨hbdsub (hA.on_bd hxβ), hbdsub hxj.1⟩) hxj.2
    have hendβ : ∀ {x}, x ∈ ({s a, t a} : Set T) → x ∈ β a ∩ discBd E := fun hx ↦ hA.meet ▸ hx
    have hend : ∀ {x}, x ∈ ({s a, t a} : Set T) → x ∈ discBd Y := by
      intro x hx
      obtain ⟨h₁, h₂⟩ := hendβ hx
      refine hJ2 ⟨h₂, fun hu ↦ ?_⟩
      obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.1 hu
      exact (hsepa j hj ⟨hbdsub (hA.on_bd h₁), hxj⟩).2 h₂
    have hmeet : β a ∩ discBd Y = {s a, t a} :=
      Subset.antisymm (fun x hx ↦ hoffE hx.1 hx.2) fun x hx ↦ ⟨(hendβ hx).1, hend hx⟩
    have hoff : discInt Y ∩ discBd (Δ a) ⊆ β a := by
      rintro x ⟨hxY, hxb⟩
      by_cases hxE : x ∈ discInt E
      · exact hA.off ⟨hxE, hxb⟩
      · obtain ⟨j, hj, hxj⟩ := (hJ3 x hxE).1 hxY
        exact absurd (hsepa j hj ⟨hbdsub hxb, discInt_subset _ hxj⟩) hxE
    have htouch : ∀ x ∈ discBd Y ∩ discBd (Δ a), x ∉ β a → ∃ C, C ⊆ discInt Y \ β a ∧ C ⊆ Δ a
      ∧ C.Nonempty ∧ IsPreconnected C ∧ x ∈ closure C := by
      rintro x ⟨hxY, hxb⟩ hxβ
      rcases hJ1 hxY with h' | h'
      · obtain ⟨C, h₁, h₂, h₃⟩ := hA.touch x ⟨h', hxb⟩ hxβ
        exact ⟨C, fun y hy ↦ ⟨hintY (h₁ hy).1, (h₁ hy).2⟩, h₂, h₃⟩
      · obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.1 h'
        exact absurd (hsepa j hj ⟨hbdsub hxb, hbdsub hxj.1⟩) hxj.2
    obtain ⟨Z, A', hZ, hA'b, -, hbZ, hA'd, hAc, hYZ, hΔZ, hZΔ, hiff⟩ := exists_outer_half hT
      hA.disc hY hA.ne hA.line hA.on_bd (hA.in_E.trans hEY) hmeet hoff htouch
    have hIY : discInt Y ⊆ discInt Z := by
      intro x hx
      refine ⟨hYZ (discInt_subset _ hx), fun hb ↦ ?_⟩
      rw [hbZ] at hb
      rcases hb with ⟨hb, hn⟩ | hb
      · have hxβ := hoff ⟨hx, hb⟩
        have hm : x ∈ ({s a, t a} : Set T) := by
          by_contra hn'
          exact hn ⟨hxβ, hn'⟩
        exact hx.2 (hend hm)
      · exact hx.2 (hA'b hb)
    have hnotE : ∀ {i}, i ∈ insert a ℐ → ∀ {x}, x ∈ discBd (Δ i) \ (β i \ {s i, t i})
      → x ∉ discInt E := by
      intro i hi x hx hxE
      have hi' := h i hi
      have hxβ := hi'.off ⟨hxE, hx.1⟩
      have hend' : x ∈ ({s i, t i} : Set T) := by
        by_contra hn
        exact hx.2 ⟨hxβ, hn⟩
      exact hxE.2 (hi'.meet ▸ hend' : x ∈ β i ∩ discBd E).2
    refine ⟨Z, hZ, hEY.trans hYZ, fun i hi ↦ ?_, fun x hx ↦ ?_, hintY.trans hIY,
      fun x hxE ↦ ⟨fun hx ↦ ?_, ?_⟩, fun x hx ↦ ?_, ?_, fun i hi ↦ ?_⟩
    · rcases Finset.mem_insert.1 hi with rfl | hi'
      · exact hΔZ
      · exact (hΔY i hi').trans hYZ
    · by_cases hxa : x ∈ Δ a
      · exact Or.inr (mem_biUnion (Finset.mem_coe.2 (Finset.mem_insert_self _ _)) hxa)
      · rcases hYc (hZΔ ⟨hx, hxa⟩) with h' | h'
        · exact Or.inl h'
        · obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.1 h'
          exact Or.inr (mem_biUnion (Finset.mem_coe.2 (Finset.mem_insert_of_mem hj)) hxj)
    · by_cases hxY : x ∈ discInt Y
      · obtain ⟨j, hj, hxj⟩ := (hJ3 x hxE).1 hxY
        exact ⟨j, Finset.mem_insert_of_mem hj, hxj⟩
      · exact ⟨a, Finset.mem_insert_self _ _, (hiff x hxY).1 hx⟩
    · rintro ⟨i, hi, hxi⟩
      rcases Finset.mem_insert.1 hi with rfl | hi'
      · by_cases hxY : x ∈ discInt Y
        · exact hIY hxY
        · exact (hiff x hxY).2 hxi
      · exact hIY ((hJ3 x hxE).2 ⟨i, hi', hxi⟩)
    · rw [hbZ] at hx
      rcases hx with hx | hx
      · exact Or.inr (mem_biUnion (Finset.mem_coe.2 (Finset.mem_insert_self _ _)) ⟨hx.1,
          hnotE (Finset.mem_insert_self _ _) hx⟩)
      · rcases hJ1 (hA'b hx) with h' | h'
        · exact Or.inl h'
        · obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.1 h'
          exact Or.inr (mem_biUnion (Finset.mem_coe.2 (Finset.mem_insert_of_mem hj)) hxj)
    · rintro x ⟨hxb, hxn⟩
      have hxY : x ∈ discBd Y := hJ2 ⟨hxb, fun hu ↦ hxn (by
        obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.1 hu
        exact mem_biUnion (Finset.mem_coe.2 (Finset.mem_insert_of_mem hj)) hxj)⟩
      rw [hbZ]
      refine Or.inr (by_contra fun hn ↦ hxn (mem_biUnion (Finset.mem_coe.2
        (Finset.mem_insert_self _ _)) (hAc ⟨hxY, hn⟩)))
    · rcases Finset.mem_insert.1 hi with rfl | hi'
      · rw [hbZ]
        exact subset_union_left
      · rw [hbZ]
        intro x hx
        refine Or.inr (by_contra fun hn ↦ ?_)
        have hxa := hAc ⟨hJ4 i hi' hx, hn⟩
        exact hnotE hi hx (hsep a (Finset.mem_insert_self _ _) i hi (hne i hi') ⟨hxa, hbdsub hx.1⟩)

omit [T2Space T] in
/-- **Finitely many disjoint lines, cut at a finite set holding their ends.** -/
theorem finite_lines_union [T2Space T] {𝓛 : Set (Set T)} (h𝓛 : 𝓛.Finite) {N : Set T}
  (hN : N.Finite) (hl : ∀ L ∈ 𝓛, ∃ a b, IsLineWithEnds L a b ∧ a ∈ N ∧ b ∈ N)
    (hd : ∀ L ∈ 𝓛, ∀ L' ∈ 𝓛, L ≠ L' → Disjoint L L') :
    IsClosed (⋃₀ 𝓛) ∧ (arcComponentsIn (⋃₀ 𝓛 \ (⋃₀ 𝓛 ∩ N))).Finite ∧ (arcComponentsIn (⋃₀ 𝓛 \
      (⋃₀ 𝓛 ∩ N))).ncard + 𝓛.ncard = (⋃₀ 𝓛 ∩ N).ncard ∧
      ∀ e ∈ arcComponentsIn (⋃₀ 𝓛 \ (⋃₀ 𝓛 ∩ N)), IsMarkedArc (⋃₀ 𝓛 ∩ N) e := by
  classical
  induction 𝓛, h𝓛 using Set.Finite.induction_on with
  | empty =>
    have : arcComponentsIn (∅ : Set T) = ∅ := by
      ext C
      simp only [mem_empty_iff_false, iff_false]
      rintro ⟨hne, hs, -⟩
      obtain ⟨x, hx⟩ := hne
      exact hs hx
    simp [this]
  | @insert L₀ 𝓛 hL₀ h𝓛 ih =>
    obtain ⟨hc, hfe, hcard, hm⟩ := ih (fun L hL ↦ hl L (mem_insert_of_mem _ hL)) fun L hL L' hL' ↦
      hd L (mem_insert_of_mem _ hL) L' (mem_insert_of_mem _ hL')
    obtain ⟨a, b, hL, ha, hb⟩ := hl L₀ (mem_insert _ _)
    set W := ⋃₀ 𝓛 with hW
    have hdis : Disjoint L₀ W := by
      refine disjoint_sUnion_right.2 fun L hL' ↦ hd L₀ (mem_insert _ _) L
        (mem_insert_of_mem _ hL') ?_
      rintro rfl
      exact hL₀ hL'
    have hun : ⋃₀ insert L₀ 𝓛 = L₀ ∪ W := sUnion_insert _ _
    rw [hun]
    have hcL : IsClosed L₀ := isClosed_of_cuffLine hL
    set M := (L₀ ∪ W) ∩ N with hM
    have hM₁ : L₀ \ M = L₀ \ (L₀ ∩ N) := by
      ext x
      simp only [mem_sdiff, hM, mem_inter_iff, mem_union, not_and]
      tauto
    have hM₂ : W \ M = W \ (W ∩ N) := by
      ext x
      simp only [mem_sdiff, hM, mem_inter_iff, mem_union, not_and]
      tauto
    have hsplit : arcComponentsIn ((L₀ ∪ W) \ M) = arcComponentsIn (L₀ \
      (L₀ ∩ N)) ∪ arcComponentsIn (W \ (W ∩ N)) := by
      have hLW : L₀ ∩ W ⊆ M := by
        rw [disjoint_iff_inter_eq_empty.1 hdis]
        exact empty_subset _
      rw [arcComponentsIn_union_sdiff hcL hc hLW, hM₁, hM₂]
    have hNL : (L₀ ∩ N).Finite := hN.subset inter_subset_right
    obtain ⟨f₁, c₁, m₁⟩ := arcs_of_line _ hNL rfl hL ⟨(ends_of_line hL).1, ha⟩ ⟨(ends_of_line
      hL).2.1, hb⟩ inter_subset_left
    have hdarc : Disjoint (arcComponentsIn (L₀ \ (L₀ ∩ N))) (arcComponentsIn (W \ (W ∩ N))) := by
      refine disjoint_left.2 fun C h₁ h₂ ↦ ?_
      obtain ⟨x, hx⟩ := h₁.1
      exact disjoint_left.1 hdis (h₁.2.1 hx).1 (h₂.2.1 hx).1
    have hMs : M = (L₀ ∩ N) ∪ (W ∩ N) := by rw [hM, union_inter_distrib_right]
    have hdN : Disjoint (L₀ ∩ N) (W ∩ N) := hdis.mono inter_subset_left inter_subset_left
    refine ⟨hcL.union hc, by rw [hsplit]; exact f₁.union hfe, ?_, ?_⟩
    · rw [hsplit, ncard_union_eq hdarc f₁ hfe, ncard_insert_of_notMem hL₀ h𝓛, hMs,
        ncard_union_eq hdN hNL (hN.subset inter_subset_right)]
      omega
    · have conv : ∀ {P e : Set T}, IsClosed P → IsMarkedArc (P ∩ N) e → e ∈ arcComponentsIn (P \
        (P ∩ N)) → P ⊆ L₀ ∪ W → IsMarkedArc M e := by
        rintro P e hP ⟨u, v, huv, hs, hl'⟩ he hsub
        have hclo : closure e ⊆ P := closure_minimal (fun z hz ↦ (he.2.1 hz).1) hP
        refine ⟨u, v, huv, ?_, hl'⟩
        rw [← hs]
        ext z
        exact ⟨fun h ↦ ⟨h.1, hclo h.1, h.2.2⟩, fun h ↦ ⟨h.1, hsub h.2.1, h.2.2⟩⟩
      rw [hsplit]
      rintro e (he | he)
      · exact conv hcL (m₁ e he).1 he subset_union_left
      · exact conv hc (hm e he) he subset_union_right

end GraphMinor.GM19
