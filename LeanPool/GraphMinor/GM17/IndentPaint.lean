/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM17.Section9b
public import LeanPool.GraphMinor.Surface.SurfacePull
public import LeanPool.GraphMinor.GM17.ThreeNodeReplace
import LeanPool.GraphMinor.GM17.CellNodes

/-!
# A painting from a push of a node

This is the bookkeeping for the step "Then `Γ'` is a painting in `Σ'`" of the proof of (9.3) of
Graph Minors XVII, page 184. Let `φ` be
an injection on a closed set `W` that holds everything outside a set `D`. Keep the cells of a
painting `Γ` that miss `D`, move them by `φ`,
and add two closed discs `T₁`, `T₂` along the boundary of the surface. If `φ` moves only one node
`n` and moves it to `n'`, this gives
a painting, and the new cells match the old ones outside the set `R` of cells in `D`
(`indented_of_push`).
-/

@[expose] public section

namespace GraphMinor.GM17

open Set Topology Metric GraphMinor.Surface

variable {S : Type} [TopologicalSpace S]

/-- An injection continuous on a compact set maps closed discs to closed discs. -/
theorem disc_of_injOn [T2Space S] {Δ : Set S} {φ : S → S} (hΔ : IsClosedDisc Δ)
  (hc : ContinuousOn φ Δ)
    (hi : InjOn φ Δ) : IsClosedDisc (φ '' Δ) ∧ discBd (φ '' Δ) = φ '' discBd Δ := by
  obtain ⟨e⟩ := hΔ.isOArc_discBd
  have : Nonempty S := ⟨(e 1).1⟩
  obtain ⟨ρ, hρ, hl⟩ := exists_inv_of_compactOn hΔ.isCompact hc hi
  exact hΔ.image hc hρ hl

/-- A closed injection keeps closures. -/
theorem closure_image_of_injOn [T2Space S] [CompactSpace S] {W d : Set S} {φ : S → S}
  (hW : IsClosed W) (hc : ContinuousOn φ W)
    (hd : d ⊆ W) : closure (φ '' d) = φ '' closure d := by
  have hcl : closure d ⊆ W := closure_minimal hd hW
  refine Subset.antisymm (closure_minimal (image_mono subset_closure) ?_) ?_
  · exact (isClosed_closure.isCompact.image_of_continuousOn (hc.mono hcl)).isClosed
  · exact (hc.mono hcl).image_closure

variable [T2Space S] [CompactSpace S]

private theorem indented_surface_cell_partition
    {S : Type}
    [TopologicalSpace S]
    (Γ : Painting S)
    {W : Set S}
    {T₁ : Set S}
    {T₂ : Set S}
    {φ : S → S}
    {n : S}
    {n₁ : S}
    {n₂ : S}
    {n' : S}
    (hφc : ContinuousOn φ W)
    (hφi : InjOn φ W)
    (hn₁N : n₁ ∈ Γ.N)
    (hn₂N : n₂ ∈ Γ.N)
    (hn₁ : n₁ ≠ n)
    (hn₂ : n₂ ≠ n)
    (hT₁ : IsClosedDisc T₁)
    (hT₂ : IsClosedDisc T₂)
    (hnode₁ : T₁ ∩ (Γ.N \ {n}) ⊆ {n₁})
    (hnode₂ : T₂ ∩ (Γ.N \ {n}) ⊆ {n₂})
    (K : Set (Set S)) (hK : K ⊆ Γ.C)
    (hclN : ∀ d ∈ K, ∀ x ∈ closure d, x ∉ d → x ∈ Γ.N)
    (hdW' : ∀ d ∈ K, d ⊆ W)
    (hcl : ∀ d ∈ K, closure (φ '' d) = φ '' closure d)
    (hφN : ∀ x ∈ Γ.N, φ x ∈ (Γ.N \ {n} ∪ {n'}))
    (hcl₁ : closure (T₁ \ {n₁, n'}) = T₁)
    (hcl₂ : closure (T₂ \ {n₂, n'}) = T₂)
    (hne₁c : (T₁ \ {n₁, n'}).Nonempty)
    (hne₂c : (T₂ \ {n₂, n'}).Nonempty)
    (hdisj12 : Disjoint (T₁ \ {n₁, n'}) (T₂ \ {n₂, n'}))
    (hnotN : ∀ d ∈ K, Disjoint (φ '' d) (Γ.N \ {n} ∪ {n'}))
    (hJfin : (insert (T₁ \ {n₁, n'}) (insert (T₂ \ {n₂, n'}) ((fun d => φ '' d) '' K))).Finite)
    (hsidefree : ∀ d ∈ K, Disjoint (φ '' d) (T₁ ∪ T₂)) :
    arcComponentsIn ((((Γ.N \ {n} ∪ {n'}) ∪ ⋃ d ∈ K, closure (φ '' d)) ∪ T₁ ∪ T₂) \ (Γ.N \ {n} ∪
      {n'})) = (insert (T₁ \ {n₁, n'}) (insert (T₂ \ {n₂, n'}) ((fun d => φ '' d) '' K))) := by
  let N' := Γ.N \ {n} ∪ {n'}
  let U' := (N' ∪ ⋃ d ∈ K, closure (φ '' d)) ∪ T₁ ∪ T₂
  let c₁ := T₁ \ {n₁, n'}
  let c₂ := T₂ \ {n₂, n'}
  let J := insert c₁ (insert c₂ ((fun d => φ '' d) '' K))
  refine arcComponentsIn_eq_of_finite_cover hJfin ?_ ?_ ?_ ?_ ?_
  · ext x
    constructor
    · rintro ⟨e, (rfl | rfl | ⟨d, hd, rfl⟩), hx⟩
      · refine ⟨.inl (.inr hx.1), ?_⟩
        rintro (h1 | h1)
        · exact hx.2 (.inl (hnode₁ ⟨hx.1, h1⟩))
        · exact hx.2 (.inr h1)
      · refine ⟨.inr hx.1, ?_⟩
        rintro (h1 | h1)
        · exact hx.2 (.inl (hnode₂ ⟨hx.1, h1⟩))
        · exact hx.2 (.inr h1)
      · refine ⟨.inl (.inl (.inr (mem_biUnion hd (subset_closure hx)))), fun h => ?_⟩
        exact disjoint_left.mp (hnotN d hd) hx h
    · rintro ⟨((hx | hx) | hx) | hx, hxN⟩
      · exact absurd hx hxN
      · obtain ⟨d, hd, hx⟩ := mem_iUnion₂.mp hx
        rw [hcl d hd] at hx
        obtain ⟨y, hy, rfl⟩ := hx
        by_cases hyd : y ∈ d
        · exact ⟨_, .inr (.inr ⟨d, hd, rfl⟩), mem_image_of_mem _ hyd⟩
        · exact absurd (hφN y (hclN d hd y hy hyd)) hxN
      · refine ⟨c₁, .inl rfl, hx, ?_⟩
        rintro (rfl | rfl)
        · exact hxN (.inl ⟨hn₁N, hn₁⟩)
        · exact hxN (.inr rfl)
      · refine ⟨c₂, .inr (.inl rfl), hx, ?_⟩
        rintro (rfl | rfl)
        · exact hxN (.inl ⟨hn₂N, hn₂⟩)
        · exact hxN (.inr rfl)
  · rintro e (rfl | rfl | ⟨d, hd, rfl⟩)
    · exact hne₁c
    · exact hne₂c
    · exact (arcComponentsIn_nonempty (hK hd)).image _
  · rintro e (rfl | rfl | ⟨d, hd, rfl⟩)
    · exact isPathConnected_of_isClosedDisc_finite_diff hT₁ sdiff_subset
        (((finite_singleton _).insert _).subset fun x hx => by
          by_contra h
          exact hx.2 ⟨hx.1, h⟩)
    · exact isPathConnected_of_isClosedDisc_finite_diff hT₂ sdiff_subset
        (((finite_singleton _).insert _).subset fun x hx => by
          by_contra h
          exact hx.2 ⟨hx.1, h⟩)
    · exact (arcComponentsIn_isPathConnected (hK hd)).image' (hφc.mono (hdW' d hd))
  · rintro e (rfl | rfl | ⟨d, hd, rfl⟩) e' (rfl | rfl | ⟨d', hd', rfl⟩) hne
    · exact absurd rfl hne
    · exact hdisj12
    · exact (hsidefree d' hd').symm.mono_left (sdiff_subset.trans subset_union_left : c₁ ⊆ T₁ ∪
      T₂)
    · exact hdisj12.symm
    · exact absurd rfl hne
    · exact (hsidefree d' hd').symm.mono_left (sdiff_subset.trans subset_union_right : c₂ ⊆ T₁ ∪
      T₂)
    · exact (hsidefree d hd).mono_right (sdiff_subset.trans subset_union_left : c₁ ⊆ T₁ ∪ T₂)
    · exact (hsidefree d hd).mono_right (sdiff_subset.trans subset_union_right : c₂ ⊆ T₁ ∪ T₂)
    · have hdd : d ≠ d' := fun h => hne (by rw [h])
      refine disjoint_left.mpr ?_
      rintro _ ⟨y, hy, rfl⟩ ⟨y', hy', he⟩
      have hyy : y' = y := hφi (hdW' d' hd' hy') (hdW' d hd hy) he
      exact disjoint_left.mp (arcComponentsIn_disjoint (hK hd) (hK hd') hdd) hy (hyy ▸ hy')
  · rintro e (rfl | rfl | ⟨d, hd, rfl⟩)
    · rw [hcl₁]
      ext x
      constructor
      · rintro ⟨hx, -, hxN⟩
        refine ⟨hx, ?_⟩
        rintro (rfl | rfl)
        · exact hxN (.inl ⟨hn₁N, hn₁⟩)
        · exact hxN (.inr rfl)
      · intro hx
        refine ⟨hx.1, .inl (.inr hx.1), ?_⟩
        rintro (h1 | h1)
        · exact hx.2 (.inl (hnode₁ ⟨hx.1, h1⟩))
        · exact hx.2 (.inr h1)
    · rw [hcl₂]
      ext x
      constructor
      · rintro ⟨hx, -, hxN⟩
        refine ⟨hx, ?_⟩
        rintro (rfl | rfl)
        · exact hxN (.inl ⟨hn₂N, hn₂⟩)
        · exact hxN (.inr rfl)
      · intro hx
        refine ⟨hx.1, .inr hx.1, ?_⟩
        rintro (h1 | h1)
        · exact hx.2 (.inl (hnode₂ ⟨hx.1, h1⟩))
        · exact hx.2 (.inr h1)
    · ext x
      constructor
      · rintro ⟨hx, -, hxN⟩
        rw [hcl d hd] at hx
        obtain ⟨y, hy, rfl⟩ := hx
        by_cases hyd : y ∈ d
        · exact mem_image_of_mem _ hyd
        · exact absurd (hφN y (hclN d hd y hy hyd)) hxN
      · intro hx
        exact ⟨subset_closure hx, .inl (.inl (.inr (mem_biUnion hd (subset_closure hx)))),
          fun h => disjoint_left.mp (hnotN d hd) hx h⟩

private theorem indented_painting_other_cells
    {S : Type}
    [TopologicalSpace S]
    {T₁ : Set S}
    {T₂ : Set S}
    {φ : S → S}
    {n₁ : S}
    {n₂ : S}
    {n' : S}
    {Γ : Painting S}
    (K : Set (Set S)) (hK : K ⊆ Γ.C)
    (hsidefree : ∀ d ∈ K, Disjoint (φ '' d) (T₁ ∪ T₂))
    (Γ' : Painting S)
    (hΓC : Γ'.C = (insert (T₁ \ {n₁, n'}) (insert (T₂ \ {n₂, n'}) ((fun d => φ '' d) '' K)))) :
    Γ'.C \ {(T₁ \ {n₁, n'}), (T₂ \ {n₂, n'})} = (fun d => φ '' d) '' K := by
  let c₁ := T₁ \ {n₁, n'}
  let c₂ := T₂ \ {n₂, n'}
  let J := insert c₁ (insert c₂ ((fun d => φ '' d) '' K))
  rw [hΓC]
  ext e
  constructor
  · rintro ⟨(rfl | rfl | he), hne⟩
    · exact absurd (.inl rfl) hne
    · exact absurd (.inr rfl) hne
    · exact he
  · rintro he
    refine ⟨.inr (.inr he), ?_⟩
    obtain ⟨d, hd, rfl⟩ := he
    obtain ⟨z, hz⟩ := (arcComponentsIn_nonempty (hK hd)).image φ
    rintro (h | h)
    · exact disjoint_left.mp (hsidefree d hd) hz (.inl ((show φ '' d = c₁ from h) ▸ hz).1)
    · exact disjoint_left.mp (hsidefree d hd) hz (.inr ((show φ '' d = c₂ from h) ▸ hz).1)

private noncomputable abbrev build_indented_border_painting
    {S : Type}
    [TopologicalSpace S]
    [T2Space S]
    (Γ : Painting S)
    {W : Set S}
    {D : Set S}
    {T₁ : Set S}
    {T₂ : Set S}
    {A₁ : Set S}
    {A₂ : Set S}
    {φ : S → S}
    {n : S}
    {n₁ : S}
    {n₂ : S}
    {n' : S}
    {R : Set (Set S)}
    (hDc : IsClosed D)
    (hφc : ContinuousOn φ W)
    (hφi : InjOn φ W)
    (hnb : n ∉ bd S)
    (hRsub : ∀ c ∈ Γ.C, c ∈ R → c ⊆ D)
    (hT₁ : IsClosedDisc T₁)
    (hT₂ : IsClosedDisc T₂)
    (hA₁ : IsLineWithEnds A₁ n₁ n')
    (hA₂ : IsLineWithEnds A₂ n₂ n')
    (hb₁ : T₁ ∩ bd S = A₁)
    (hb₂ : T₂ ∩ bd S = A₂)
    (hcov : ∀ x ∈ bd S, x ∈ T₁ ∨ x ∈ T₂ ∨ x ∉ D ∧ φ x = x)
    (hne₁ : n₁ ≠ n')
    (hne₂ : n₂ ≠ n')
    (hKfin : (Γ.C \ R).Finite)
    (hdW : ∀ d ∈ (Γ.C \ R), closure d ⊆ W)
    (hcl : ∀ d ∈ (Γ.C \ R), closure (φ '' d) = φ '' closure d)
    (hn₁T : n₁ ∈ discBd T₁)
    (hn'T₁ : n' ∈ discBd T₁)
    (hn₂T : n₂ ∈ discBd T₂)
    (hn'T₂ : n' ∈ discBd T₂)
    (hcl₁ : closure (T₁ \ {n₁, n'}) = T₁)
    (hcl₂ : closure (T₂ \ {n₂, n'}) = T₂)
    (ht₁ : tilde (T₁ \ {n₁, n'}) = {n₁, n'})
    (ht₂ : tilde (T₂ \ {n₂, n'}) = {n₂, n'})
    (hJfin : (insert (T₁ \ {n₁, n'}) (insert (T₂ \ {n₂, n'}) ((fun d => φ '' d) '' (Γ.C \
      R)))).Finite)
    (hJ : arcComponentsIn ((((Γ.N \ {n} ∪ {n'}) ∪ ⋃ d ∈ (Γ.C \ R), closure (φ '' d)) ∪ T₁ ∪ T₂) \
      (Γ.N \ {n} ∪ {n'})) = (insert (T₁ \ {n₁, n'}) (insert (T₂ \ {n₂, n'}) ((fun d => φ '' d) ''
      (Γ.C \ R)))))
    (htilde : ∀ d ∈ (Γ.C \ R), tilde (φ '' d) = φ '' tilde d)
    (hbdset : ∀ d ∈ (Γ.C \ R), ∀ y ∈ d, y ∈ bd S ∨ φ y ∈ bd S → φ y = y)
    (hfixN : ∀ d ∈ (Γ.C \ R), (d ∩ bd S).Nonempty → ∀ x ∈ tilde d, φ x = x) :
    Painting S := by
  let K := Γ.C \ R
  let N' := Γ.N \ {n} ∪ {n'}
  let U' := (N' ∪ ⋃ d ∈ K, closure (φ '' d)) ∪ T₁ ∪ T₂
  let c₁ := T₁ \ {n₁, n'}
  let c₂ := T₂ \ {n₂, n'}
  let J := insert c₁ (insert c₂ ((fun d => φ '' d) '' K))
  exact {
    U := U'
    N := N'
    isClosed_U := by
      refine (((Γ.finite_N.subset sdiff_subset).union (finite_singleton _)).isClosed.union ?_
        |>.union hT₁.isClosed).union hT₂.isClosed
      exact hKfin.isClosed_biUnion fun _ _ => isClosed_closure
    N_subset := fun x hx => .inl (.inl (.inl hx))
    finite_N := (Γ.finite_N.subset sdiff_subset).union (finite_singleton _)
    finite_cells := by
      rw [hJ]
      exact hJfin
    cell_disc := by
      rw [hJ]
      rintro e (rfl | rfl | ⟨d, hd, rfl⟩)
      · rw [hcl₁, ht₁]
        refine ⟨hT₁, ?_, by simp, by rw [ncard_pair hne₁]; omega⟩
        rintro x (rfl | rfl)
        · exact hn₁T
        · exact hn'T₁
      · rw [hcl₂, ht₂]
        refine ⟨hT₂, ?_, by simp, by rw [ncard_pair hne₂]; omega⟩
        rintro x (rfl | rfl)
        · exact hn₂T
        · exact hn'T₂
      · obtain ⟨h1, h2, h3, h4⟩ := Γ.cell_disc d hd.1
        have hD := disc_of_injOn h1 (hφc.mono (hdW d hd)) (hφi.mono (hdW d hd))
        change IsClosedDisc (closure (φ '' d)) ∧ tilde (φ '' d) ⊆ discBd (closure (φ '' d)) ∧
          (tilde (φ '' d)).Finite ∧ (tilde (φ '' d)).ncard ≤ 3
        rw [htilde d hd, hcl d hd]
        exact ⟨hD.1, hD.2 ▸ image_mono h2, h3.image _, (ncard_image_le h3).trans h4⟩
    bd_subset := fun x hx => by
      rcases hcov x hx with h | h | ⟨h1, h2⟩
      · exact .inl (.inr h)
      · exact .inr h
      · rcases Painting.mem_U_iff.mp (Γ.bd_subset hx) with h | ⟨d, hd, hxd⟩
        · refine .inl (.inl (.inl (.inl ⟨h, ?_⟩)))
          rintro rfl
          exact hnb hx
        · by_cases hdR : d ∈ R
          · exact absurd (closure_minimal (hRsub d hd hdR) hDc hxd) h1
          · have hdK : d ∈ K := ⟨hd, hdR⟩
            refine .inl (.inl (.inr (mem_biUnion hdK ?_)))
            rw [hcl d hdK]
            exact ⟨x, hxd, h2⟩
    border_cell := by
      rw [hJ]
      rintro e (rfl | rfl | ⟨d, hd, rfl⟩) hb
      · rw [hcl₁, ht₁, hb₁, ncard_pair hne₁, lineEnds_eq hA₁]
        exact ⟨rfl, by simp, ⟨hA₁.choose⟩, rfl⟩
      · rw [hcl₂, ht₂, hb₂, ncard_pair hne₂, lineEnds_eq hA₂]
        exact ⟨rfl, by simp, ⟨hA₂.choose⟩, rfl⟩
      · have hbd' : (d ∩ bd S).Nonempty := by
          obtain ⟨_, ⟨y, hy, rfl⟩, hyb⟩ := hb
          exact ⟨y, hy, hbdset d hd y hy (.inr hyb) ▸ hyb⟩
        have h4 := Γ.border_cell d hd.1 hbd'
        have hfc : ∀ x ∈ closure d, (x ∈ bd S ∨ φ x ∈ bd S) → φ x = x := fun x hx hb => by
          by_cases hxd : x ∈ d
          · exact hbdset d hd x hxd hb
          · exact hfixN d hd hbd' x ⟨hx, hxd⟩
        have hY : closure (φ '' d) ∩ bd S = closure d ∩ bd S := by
          rw [hcl d hd]
          ext z
          constructor
          · rintro ⟨⟨y, hy, rfl⟩, hz⟩
            exact ⟨by rw [hfc y hy (.inr hz)]; exact hy, hz⟩
          · rintro ⟨hz, hzb⟩
            exact ⟨⟨z, hz, hfc z hz (.inl hzb)⟩, hzb⟩
        have ht : tilde (φ '' d) = tilde d := by
          rw [htilde d hd]
          exact (image_congr (hfixN d hd hbd')).trans (image_id' _)
        change (tilde (φ '' d)).ncard = 2 ∧ (tilde (φ '' d)).Finite ∧ IsLine (closure
          (φ '' d) ∩ bd S) ∧
          lineEnds (closure (φ '' d) ∩ bd S) = tilde (φ '' d)
        rw [ht, hY]
        exact h4 }

theorem indented_of_push (Γ : Painting S) {W D T₁ T₂ A₁ A₂ Θ c₀ : Set S} {φ : S
  → S} {n n₁ n₂ n' : S} {R : Set (Set S)}
    (hW : IsClosed W) (hDc : IsClosed D) (hDW : Dᶜ ⊆ W) (hφc : ContinuousOn φ W) (hφi : InjOn φ W)
    (hnN : n ∈ Γ.N) (hnW : n ∈ W) (hn₁N : n₁ ∈ Γ.N) (hn₂N : n₂ ∈ Γ.N) (hn₁ : n₁ ≠ n) (hn₂ : n₂ ≠ n)
    (hfix : ∀ x ∈ Γ.N, x ≠ n → x ∈ W ∧ φ x = x) (hφn : φ n = n') (hnb : n ∉ bd S) (hn'N : n' ∉ Γ.N)
    (hn'c : n' ∈ c₀ ∩ Θ)
    (hRsub : ∀ c ∈ Γ.C, c ∈ R → c ⊆ D) (hRd : ∀ c ∈ Γ.C, c ∉ R → Disjoint c D)
    (hT₁ : IsClosedDisc T₁) (hT₂ : IsClosedDisc T₂) (hA₁ : IsLineWithEnds A₁ n₁ n')
      (hA₂ : IsLineWithEnds A₂ n₂ n')
    (hA₁b : A₁ ⊆ discBd T₁) (hA₂b : A₂ ⊆ discBd T₂) (hb₁ : T₁ ∩ bd S = A₁) (hb₂ : T₂ ∩ bd S = A₂)
    (hA₁Θ : A₁ ⊆ Θ) (hA₂Θ : A₂ ⊆ Θ) (hT : T₁ ∩ T₂ = {n'})
    (hnode₁ : T₁ ∩ (Γ.N \ {n}) ⊆ {n₁}) (hnode₂ : T₂ ∩ (Γ.N \ {n}) ⊆ {n₂})
    (hoff : ∀ y, y ∉ D → φ y ∉ T₁ ∧ φ y ∉ T₂) (hbd : ∀ y, y ∉ D → (y ∈ bd S ∨ φ y ∈ bd S) → φ y = y)
    (hcov : ∀ x ∈ bd S, x ∈ T₁ ∨ x ∈ T₂ ∨ (x ∉ D ∧ φ x = x)) :
    ∃ Γ' : Painting S, IsIndentedBorderPainting Γ Θ c₀ n₁ n₂ n R Γ' := by
  classical
  have hne₁ : n₁ ≠ n' := hA₁.ne'
  have hne₂ : n₂ ≠ n' := hA₂.ne'
  let K : Set (Set S) := Γ.C \ R
  have hKfin : K.Finite := Γ.finite_cells.subset sdiff_subset
  have hdc : ∀ d ∈ K, d ⊆ Dᶜ := fun d hd x hx hxD => disjoint_left.mp (hRd d hd.1 hd.2) hx hxD
  have hclN : ∀ d ∈ K, ∀ x ∈ closure d, x ∉ d → x ∈ Γ.N := fun d hd x hx hxd
    => Γ.tilde_subset_N hd.1 ⟨hx, hxd⟩
  have hdW : ∀ d ∈ K, closure d ⊆ W := fun d hd x hx => by
    by_cases hxd : x ∈ d
    · exact hDW (hdc d hd hxd)
    · have hxN := hclN d hd x hx hxd
      by_cases h : x = n
      · exact h ▸ hnW
      · exact (hfix x hxN h).1
  have hdW' : ∀ d ∈ K, d ⊆ W := fun d hd => subset_closure.trans (hdW d hd)
  have hcl : ∀ d ∈ K, closure (φ '' d) = φ '' closure d := fun d hd => closure_image_of_injOn hW
    hφc (hdW' d hd)
  let N' : Set S := (Γ.N \ {n}) ∪ {n'}
  have hφN : ∀ x ∈ Γ.N, φ x ∈ N' := fun x hx => by
    by_cases h : x = n
    · subst h
      exact .inr hφn
    · rw [(hfix x hx h).2]
      exact .inl ⟨hx, h⟩
  let U' : Set S := N' ∪ (⋃ d ∈ K, closure (φ '' d)) ∪ T₁ ∪ T₂
  let c₁ : Set S := T₁ \ {n₁, n'}
  let c₂ : Set S := T₂ \ {n₂, n'}
  have hn₁T : n₁ ∈ discBd T₁ := hA₁b hA₁.left_mem
  have hn'T₁ : n' ∈ discBd T₁ := hA₁b hA₁.right_mem
  have hn₂T : n₂ ∈ discBd T₂ := hA₂b hA₂.left_mem
  have hn'T₂ : n' ∈ discBd T₂ := hA₂b hA₂.right_mem
  have hcl₁ : closure c₁ = T₁ := by
    refine (hT₁.sdiff_of_inter_subset_discBd ?_).2.2
    rintro x ⟨rfl | rfl, -⟩
    · exact hn₁T
    · exact hn'T₁
  have hcl₂ : closure c₂ = T₂ := by
    refine (hT₂.sdiff_of_inter_subset_discBd ?_).2.2
    rintro x ⟨rfl | rfl, -⟩
    · exact hn₂T
    · exact hn'T₂
  have ht₁ : tilde c₁ = {n₁, n'} := by
    rw [tilde, hcl₁]
    ext x
    constructor
    · rintro ⟨h3, h4⟩
      exact by_contra fun h => h4 ⟨h3, h⟩
    · intro h3
      refine ⟨?_, fun h => h.2 h3⟩
      rcases h3 with rfl | rfl
      · exact discBd_subset _ hn₁T
      · exact discBd_subset _ hn'T₁
  have ht₂ : tilde c₂ = {n₂, n'} := by
    rw [tilde, hcl₂]
    ext x
    constructor
    · rintro ⟨h3, h4⟩
      exact by_contra fun h => h4 ⟨h3, h⟩
    · intro h3
      refine ⟨?_, fun h => h.2 h3⟩
      rcases h3 with rfl | rfl
      · exact discBd_subset _ hn₂T
      · exact discBd_subset _ hn'T₂
  have hne₁c : c₁.Nonempty := by
    obtain ⟨x, hx⟩ : (closure c₁).Nonempty := by
      rw [hcl₁]
      exact ⟨_, discBd_subset _ hn₁T⟩
    exact closure_nonempty_iff.mp ⟨x, hx⟩
  have hne₂c : c₂.Nonempty := by
    obtain ⟨x, hx⟩ : (closure c₂).Nonempty := by
      rw [hcl₂]
      exact ⟨_, discBd_subset _ hn₂T⟩
    exact closure_nonempty_iff.mp ⟨x, hx⟩
  have hdisj12 : Disjoint c₁ c₂ := disjoint_left.mpr fun x hx hx' => by
    have h3 : x ∈ T₁ ∩ T₂ := ⟨hx.1, hx'.1⟩
    rw [hT] at h3
    exact hx.2 (.inr h3)
  have hne12 : c₁ ≠ c₂ := fun h => by
    obtain ⟨x, hx⟩ := hne₁c
    exact disjoint_left.mp hdisj12 hx (h ▸ hx)
  have hnotN : ∀ d ∈ K, Disjoint (φ '' d) N' := fun d hd => disjoint_left.mpr fun x hx hxN => by
    obtain ⟨y, hy, rfl⟩ := hx
    have hyN : y ∉ Γ.N := fun h => disjoint_left.mp (Γ.cell_disjoint_N hd.1) hy h
    rcases hxN with ⟨h1, h2⟩ | h1
    · have := hfix _ h1 h2
      exact hyN (hφi (hdW' d hd hy) this.1 this.2.symm ▸ h1)
    · rw [← hφn] at h1
      exact hyN (hφi (hdW' d hd hy) hnW h1 ▸ hnN)
  let J : Set (Set S) := insert c₁ (insert c₂ ((fun d => φ '' d) '' K))
  have hJfin : J.Finite := ((hKfin.image _).insert _).insert _
  have hsidefree : ∀ d ∈ K, Disjoint (φ '' d) (T₁ ∪ T₂) := fun d hd => disjoint_left.mpr fun x hx
    hx' => by
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨h1, h2⟩ := hoff y (hdc d hd hy)
    exact hx'.elim h1 h2
  have hJ : arcComponentsIn (U' \ N') = J := by
    exact indented_surface_cell_partition (S := S) Γ (W := W) (T₁ := T₁) (T₂ := T₂) (φ := φ)
      (n := n) (n₁ := n₁) (n₂ := n₂) (n' := n') hφc hφi hn₁N hn₂N hn₁ hn₂ hT₁ hT₂ hnode₁
      hnode₂ K sdiff_subset hclN hdW' hcl hφN hcl₁ hcl₂ hne₁c hne₂c hdisj12 hnotN hJfin hsidefree
  have htilde : ∀ d ∈ K, tilde (φ '' d) = φ '' tilde d := fun d hd => by
    rw [tilde, hcl d hd, tilde, image_sdiff_of_injOn (hφi.mono (hdW d hd)) subset_closure]
  have hbdset : ∀ d ∈ K, ∀ y ∈ d, (y ∈ bd S ∨ φ y ∈ bd S) → φ y = y := fun d hd y hy h => hbd y
    (hdc d hd hy) h
  have hnotn : ∀ d ∈ K, (d ∩ bd S).Nonempty → n ∉ tilde d := fun d hd hb hn => by
    have h4 := Γ.border_cell d hd.1 hb
    have hends : ∀ x ∈ tilde d, x ∈ bd S := fun x hx => by
      rw [← h4.2.2.2] at hx
      obtain ⟨v, hv⟩ := hx
      exact hv.left_mem.2
    exact hnb (hends n hn)
  have hfixN : ∀ d ∈ K, (d ∩ bd S).Nonempty → ∀ x ∈ tilde d, φ x = x := fun d hd hb x hx =>
    (hfix x (Γ.tilde_subset_N hd.1 hx) fun h => hnotn d hd hb (h ▸ hx)).2
  let Γ' : Painting S := by
    exact build_indented_border_painting (S := S) Γ (W := W) (D := D) (T₁ := T₁) (T₂ := T₂) (A₁ :=
      A₁) (A₂ := A₂) (φ := φ) (n := n) (n₁ := n₁) (n₂ := n₂) (n' := n') (R := R) hDc hφc hφi hnb
      hRsub hT₁ hT₂ hA₁ hA₂ hb₁ hb₂ hcov hne₁ hne₂ hKfin hdW hcl hn₁T hn'T₁ hn₂T hn'T₂ hcl₁ hcl₂
      ht₁ ht₂ hJfin hJ htilde hbdset hfixN
  have hΓC : Γ'.C = J := hJ
  let cellMap : Set S → Set S := fun e => W ∩ φ ⁻¹' e
  have hback : ∀ d ∈ K, cellMap (φ '' d) = d := fun d hd => by
    ext x
    constructor
    · rintro ⟨hx, y, hy, he⟩
      exact hφi (hdW' d hd hy) hx he ▸ hy
    · intro hx
      exact ⟨hdW' d hd hx, mem_image_of_mem _ hx⟩
  have hset : Γ'.C \ {c₁, c₂} = (fun d => φ '' d) '' K := by
    exact indented_painting_other_cells (S := S) (T₁ := T₁) (T₂ := T₂) (φ := φ) (n₁ := n₁) (n₂ :=
      n₂) (n' := n') (Γ := Γ) K sdiff_subset hsidefree Γ' hΓC
  refine ⟨Γ', n', c₁, c₂, cellMap, hn'c, rfl, ?_, ?_, hne12, ?_, ?_, ht₁, ht₂, ?_, ?_, ?_, ?_⟩
  · rw [hΓC]
    exact .inl rfl
  · rw [hΓC]
    exact .inr (.inl rfl)
  · obtain ⟨z, hz⟩ := line_inner_nonempty hA₁
    exact ⟨z, ⟨discBd_subset _ (hA₁b hz.1), hz.2⟩, hA₁Θ hz.1⟩
  · obtain ⟨z, hz⟩ := line_inner_nonempty hA₂
    exact ⟨z, ⟨discBd_subset _ (hA₂b hz.1), hz.2⟩, hA₂Θ hz.1⟩
  · rw [hset]
    refine ⟨?_, ?_, ?_⟩
    · rintro _ ⟨d, hd, rfl⟩
      change cellMap (φ '' d) ∈ _
      rw [hback d hd]
      exact hd
    · rintro _ ⟨d, hd, rfl⟩ _ ⟨d', hd', rfl⟩ h
      change φ '' d = φ '' d'
      have h3 : cellMap (φ '' d) = cellMap (φ '' d') := h
      rw [hback d hd, hback d' hd'] at h3
      rw [h3]
    · intro d hd
      exact ⟨φ '' d, ⟨d, hd, rfl⟩, hback d hd⟩
  · intro e he Θ' hΘ'
    rw [hset] at he
    obtain ⟨d, hd, rfl⟩ := he
    change ((φ '' d) ∩ Θ').Nonempty ↔ (cellMap (φ '' d) ∩ Θ').Nonempty
    rw [hback d hd]
    have hΘb : Θ' ⊆ bd S := by
      obtain ⟨x, -, rfl⟩ := hΘ'
      exact connectedComponentIn_subset _ _
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, hyb⟩
      exact ⟨y, hy, hbdset d hd y hy (.inr (hΘb hyb)) ▸ hyb⟩
    · rintro ⟨y, hy, hyb⟩
      exact ⟨φ y, mem_image_of_mem _ hy, (hbdset d hd y hy (.inl (hΘb hyb))).symm ▸ hyb⟩
  · intro e he
    rw [hset] at he
    obtain ⟨d, hd, rfl⟩ := he
    change ((φ '' d) ∩ bd S).Nonempty ↔ (cellMap (φ '' d) ∩ bd S).Nonempty
    rw [hback d hd]
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, hyb⟩
      exact ⟨y, hy, hbdset d hd y hy (.inr hyb) ▸ hyb⟩
    · rintro ⟨y, hy, hyb⟩
      exact ⟨φ y, mem_image_of_mem _ hy, (hbdset d hd y hy (.inl hyb)).symm ▸ hyb⟩
  · intro e he
    rw [hset] at he
    obtain ⟨d, hd, rfl⟩ := he
    change tilde (φ '' d) = _ '' tilde (cellMap (φ '' d))
    rw [hback d hd, htilde d hd]
    refine image_congr fun x hx => ?_
    by_cases h : x = n
    · simp [h, hφn]
    · simp [h, (hfix x (Γ.tilde_subset_N hd.1 hx) h).2]

end GraphMinor.GM17
