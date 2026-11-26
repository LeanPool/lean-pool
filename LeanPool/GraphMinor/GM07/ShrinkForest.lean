/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.MoveHomotopy
public import LeanPool.GraphMinor.GM07.ForestPeel

/-!
# Shrinking a forest to a finite set

This is the induction on `|E(L)|` that Graph Minors VII offers for (4.4) on page 223. A forest with
no `O`-arc and no `I`-arc grows from `bd(Σ)` one line at a time (`exists_growth`). The last line has
a free end, so it can be slid along itself into any open set around its other end. So a move carries
the whole forest into any open set around a finite set of roots (`exists_shrink`).
-/

@[expose] public section

namespace GraphMinor.GM07

open Set Topology GraphMinor.Surface GraphMinor.GM11

variable {S : Type} [TopologicalSpace S]

/-- A small initial piece of a path stays in an open set. -/
theorem exists_initial {f : unitInterval → S} (hf : Continuous f) {N : Set S} (hN : IsOpen N)
  (hf0 : f 0 ∈ N) : ∃ t : unitInterval, 0 < t.1 ∧ t.1 < 1 ∧ ∀ s, s ≤ t → f s ∈ N := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp (hN.preimage hf) 0 hf0
  have h2 : 0 < min (r / 2) (1 / 2 : ℝ) := lt_min (by positivity) (by norm_num)
  have h3 : min (r / 2) (1 / 2 : ℝ) ≤ 1 / 2 := min_le_right _ _
  refine ⟨⟨min (r / 2) (1 / 2), h2.le, by linarith⟩, h2, ?_, fun s hs => hball ?_⟩
  · change min (r / 2) (1 / 2 : ℝ) < 1
    linarith
  · rw [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq]
    have h1 : s.1 ≤ min (r / 2) (1 / 2) := hs
    have h4 : min (r / 2) (1 / 2 : ℝ) ≤ r / 2 := min_le_left _ _
    have h5 := s.2.1
    change |s.1 - 0| < r
    rw [sub_zero, abs_of_nonneg h5]
    linarith

/-- The arc `f` from `f t` on. -/
theorem exists_tail {f : unitInterval → S} (hf : IsArcMap f) {t : unitInterval} (ht0 : 0 < t.1)
  (ht1 : t.1 < 1) :
    ∃ A : unitInterval → S, IsArcMap A ∧ A 0 = f t ∧ (∀ s, s ≠ 0 → ∃ s', t < s' ∧ A s = f s') ∧
      (∀ s, t ≤ s → ∃ s', A s' = f s) ∧ A 1 = f 1 := by
  let par : unitInterval → unitInterval := fun s =>
    ⟨t.1 + s.1 * (1 - t.1), by nlinarith [s.2.1, t.2.2], by nlinarith [s.2.2, t.2.2]⟩
  have hparc : Continuous par := by
    refine Continuous.subtype_mk ?_ _
    fun_prop
  have hpar0 : par 0 = t := Subtype.ext (by simp [par])
  have hpari : Function.Injective par := fun s s' h => by
    have h1 : t.1 + s.1 * (1 - t.1) = t.1 + s'.1 * (1 - t.1) := congrArg Subtype.val h
    have h2 : s.1 * (1 - t.1) = s'.1 * (1 - t.1) := by linarith
    exact Subtype.ext (mul_right_cancel₀ (sub_ne_zero.mpr (ne_of_gt ht1)) h2)
  have hpar1 : par 1 = 1 := Subtype.ext (by simp [par])
  refine ⟨f ∘ par, ⟨hf.1.comp hparc, hf.2.comp hpari⟩, by simp [hpar0], fun s hs => ⟨par s, ?_,
    rfl⟩, fun s hs => ?_, by simp [hpar1]⟩
  · have h1 : 0 < s.1 := lt_of_le_of_ne s.2.1 fun h => hs (Subtype.ext h.symm)
    change t.1 < t.1 + s.1 * (1 - t.1)
    nlinarith
  · have hst : t.1 ≤ s.1 := hs
    have hd : 0 < 1 - t.1 := by linarith
    let s' : unitInterval := ⟨(s.1 - t.1) / (1 - t.1), div_nonneg (by linarith) hd.le,
      (div_le_one hd).mpr (by linarith [s.2.2])⟩
    refine ⟨s', congrArg f (Subtype.ext ?_)⟩
    change t.1 + (s.1 - t.1) / (1 - t.1) * (1 - t.1) = s.1
    field_simp
    ring

/-- One slide. The arc `f` may touch `bd(Σ)` and the closed set `Z` only at `f 0`. A move carries
`f` and `Z` into any open set around them that holds `f 0` and `Z`. -/
theorem exists_step (hS : IsSurface S) {f : unitInterval → S} (hf : IsArcMap f) {Z N W : Set S}
  (hZ : IsClosed Z) (hN : IsOpen N) (hW : IsClosed W) (hNW : Disjoint N W) (hfW : ∀ s, f s ∉ W)
    (hZN : Z ⊆ N) (hf0 : f 0 ∈ N) (hbd : ∀ s, s ≠ 0 → f s ∉ bd S) (hfZ : ∀ s, s ≠ 0 → f s ∉ Z) :
    ∃ α : S ≃ₜ S, IsMove α ∧ (∀ z ∈ Z, α z ∈ N) ∧ (∀ s, α (f s) ∈ N) ∧ ∀ z ∈ W, α z = z := by
  classical
  have ht2 : T2Space S := hS.2.1
  obtain ⟨t, ht0, ht1, htN⟩ := exists_initial hf.1 hN hf0
  obtain ⟨A, hA, hA0, hAf, hfA, -⟩ := exists_tail hf ht0 ht1
  have hne : ∀ s', t < s' → s' ≠ 0 := fun s' h h0 => by
    rw [h0] at h
    exact absurd (show t.1 < 0 from h) (not_lt.mpr t.2.1)
  let Y : Set S := f '' Iic t
  have hYc : IsClosed Y := (isClosed_Iic.isCompact.image hf.1).isClosed
  have hZY : IsClosed (Z ∪ Y ∪ W) := (hZ.union hYc).union hW
  have hoff : ∀ s, A s ∉ bd S := fun s h => by
    by_cases hs : s = 0
    · rw [hs, hA0] at h
      exact hbd t (fun h0 => by rw [h0] at ht0; simp at ht0) h
    · obtain ⟨s', hs', he⟩ := hAf s hs
      exact hbd s' (hne s' hs') (he ▸ h)
  obtain ⟨α, hm, hz, hA'⟩ := exists_line_slide hS hA hoff hZY (fun s hs h => by
      obtain ⟨s', hs', he⟩ := hAf s hs
      rw [he] at h
      rcases h with (h | ⟨s'', hs'', he'⟩) | h
      · exact hfZ _ (hne s' hs') h
      · have := hf.2 he'
        exact absurd (show s'' ≤ t from hs'') (not_le.mpr (this ▸ hs'))
      · exact hfW _ h) hN (by
      rw [hA0]
      exact htN t le_rfl)
  have hZN' : ∀ z ∈ Z ∪ Y, z ∈ N := by
    rintro z (h | ⟨s', hs', rfl⟩)
    · exact hZN h
    · exact htN s' hs'
  have hall : ∀ z ∈ Z ∪ Y, α z ∈ N := fun z hzz => by
    rcases hz z (.inl hzz) with h | h
    · rw [h]
      exact hZN' z hzz
    · exact h.2
  refine ⟨α, hm, fun z hzz => hall z (.inl hzz), fun s => ?_, fun z hzz => ?_⟩
  · by_cases hs : s ≤ t
    · exact hall _ (.inr ⟨s, hs, rfl⟩)
    · obtain ⟨s', hs'⟩ := hfA s (le_of_not_ge hs)
      rw [← hs']
      exact hA' s'
  · rcases hz z (.inr hzz) with h | h
    · exact h
    · exact (disjoint_left.mp hNW h.1 hzz).elim

/-- The step of `exists_shrink_part`: first slide the new line, then apply the moves for the lines
after it. -/
theorem shrink_step (hS : IsSurface S) {P A R' W Q : Set S} (hP : IsClosed P) (hRf : R'.Finite)
  (f : unitInterval ≃ₜ A) (hbd : ∀ s, s ≠ 0 → (f s).1 ∉ bd S) (hfP : ∀ s, s ≠ 0 → (f s).1 ∉ P)
    (hW : IsClosed W) (hfW : ∀ s, (f s).1 ∉ W) (hRoff : ∀ r ∈ R', r ∈ bd S ∨ r ∉ P ∪ A)
      (hR : ∀ N, IsOpen N → P ∪ A ⊆ N → R' ⊆ N → Disjoint N W → ∃ α : S ≃ₜ S, IsMove α ∧ (∀ z ∈
        (P ∪ A) ∪ Q, α z ∈ N) ∧ ∀ z ∈ W, α z = z)
    (N : Set S) (hN : IsOpen N) (hPN : P ⊆ N) (hRN : R' ⊆ N) (hNW : Disjoint N W) (hf0 :
      (f 0).1 ∈ N) : ∃ α : S ≃ₜ S, IsMove α ∧ (∀ z ∈ P ∪ A ∪ Q, α z ∈ N) ∧ ∀ z ∈ W, α z = z := by
  have ht2 : T2Space S := hS.2.1
  have hc : IsArcMap fun t => (f t).1 := ⟨by fun_prop, fun x y h => f.injective (Subtype.ext h)⟩
  have hR'c : IsClosed R' := hRf.isClosed
  obtain ⟨α₀, hm₀, hZ₀, hf₀, hW₀⟩ := exists_step hS hc (hP.union hR'c) hN hW hNW hfW
    (union_subset hPN hRN) hf0 hbd (fun s hs h => by
    rcases h with h | h
    · exact hfP s hs h
    · rcases hRoff _ h with h' | h'
      · exact hbd s hs h'
      · exact h' (.inr (f s).2))
  obtain ⟨α₁, hm₁, h₁, hw₁⟩ := hR (α₀ ⁻¹' N) (hN.preimage α₀.continuous) (union_subset (fun z hz
    => hZ₀ z (.inl hz)) fun z hz => by
      obtain ⟨t, rfl⟩ : ∃ t, (f t).1 = z := ⟨f.symm ⟨z, hz⟩, by simp⟩
      exact hf₀ t) (fun z hz => hZ₀ z (.inr hz)) (disjoint_left.mpr fun z hz hzW => by
      have h1 : α₀ z ∈ N := hz
      rw [hW₀ z hzW] at h1
      exact disjoint_left.mp hNW h1 hzW)
  refine ⟨α₁.trans α₀, hm₁.trans hm₀, fun z hz => h₁ z hz, fun z hz => ?_⟩
  rw [Homeomorph.trans_apply, hw₁ z hz, hW₀ z hz]

/-- **Shrinking one part of a forest.** Let `l` grow from `B`, and let `K` be a closed set such that
every line of `l` lies in `K` or misses it. Assume that `bd(Σ) ∪ P ⊆ B`, and that `K` meets `B` only
in `bd(Σ) ∪ P`. Then there is a finite subset `R` of `K`, each point on `bd(Σ)` or off `P`, such
that a move carries `P` and the part of `l` in `K` into any open set around `P ∪ R`. The move fixes
every point of a given closed set `W` off `K` and off this open set. -/
theorem exists_shrink_part (hS : IsSurface S) {B : Set S} {l : List (Set S)} {k : ℕ}
  (h : IsGrowth B l k) :
    ∀ P K : Set S, IsClosed P → bd S ∪ P ⊆ B → B ∩ K ⊆ bd S ∪ P → (∀ A ∈ l, A ⊆ K ∨ Disjoint A K)
      → ∃ R : Set S, R.Finite ∧ R ⊆ K ∧ (∀ r ∈ R, r ∈ bd S ∨ r ∉ P) ∧
      ∀ W : Set S, IsClosed W → Disjoint W K → ∀ N, IsOpen N → P ⊆ N → R ⊆ N → Disjoint N W
        → ∃ α : S ≃ₜ S, IsMove α ∧ (∀ z ∈ P ∪ (listUnion l ∩ K), α z ∈ N) ∧ ∀ z ∈ W, α z = z := by
  classical
  have ht2 : T2Space S := hS.2.1
  have hmem : ∀ {A K : Set S} {l : List (Set S)} {P : Set S} {z : S}, z ∈ P ∪ (listUnion
    (A :: l) ∩ K) → z ∈ P ∪ A ∪ (listUnion l ∩ K) := fun {A K l P z} hz => by
    rcases hz with hz | ⟨hz, hzK⟩
    · exact .inl (.inl hz)
    · rw [listUnion_cons] at hz
      rcases hz with hz | hz
      · exact .inl (.inr hz)
      · exact .inr ⟨hz, hzK⟩
  have hskip : ∀ {A K : Set S} {l : List (Set S)} {P : Set S} {z : S}, Disjoint A K → z ∈ P ∪
    (listUnion (A :: l) ∩ K) → z ∈ P ∪ (listUnion l ∩ K) := fun {A K l P z} hd hz => by
    rcases hz with hz | ⟨hz, hzK⟩
    · exact .inl hz
    · rw [listUnion_cons] at hz
      rcases hz with hz | hz
      · exact (disjoint_left.mp hd hz hzK).elim
      · exact .inr ⟨hz, hzK⟩
  have hgrow : ∀ {B K P A : Set S}, B ∩ K ⊆ bd S ∪ P → (B ∪ A) ∩ K ⊆ bd S ∪ (P ∪ A)
    := fun {B K P A} hK => by
    rintro z ⟨h1 | h1, h2⟩
    · rcases hK ⟨h1, h2⟩ with h3 | h3
      · exact .inl h3
      · exact .inr (.inl h3)
    · exact .inr (.inr h1)
  have hgrow' : ∀ {B K P A : Set S}, B ∩ K ⊆ bd S ∪ P → Disjoint A K → (B ∪ A) ∩ K ⊆ bd S ∪ P
    := fun {B K P A} hK hd => by
    rintro z ⟨h1 | h1, h2⟩
    · exact hK ⟨h1, h2⟩
    · exact (disjoint_left.mp hd h1 h2).elim
  have hup : ∀ {B P A : Set S}, bd S ∪ P ⊆ B → bd S ∪ (P ∪ A) ⊆ B ∪ A := fun {B P A} hB => by
    rw [← union_assoc]
    exact union_subset_union_left _ hB
  induction h with
  | nil B =>
    intro P K _ _ _ _
    refine ⟨∅, finite_empty, empty_subset _, by simp, fun W _ _ N _ hP _ _ => ⟨Homeomorph.refl S,
      IsMove.refl, fun z hz => ?_, fun _ _ => rfl⟩⟩
    simp only [listUnion_nil, empty_inter, union_empty] at hz
    exact hP hz
  | @free B A l k hA hd _ ih =>
    intro P K hP hB hK hl
    have hl' : ∀ A' ∈ l, A' ⊆ K ∨ Disjoint A' K := fun A' h => hl A' (List.mem_cons_of_mem _ h)
    rcases hl A List.mem_cons_self with hAK | hAK
    · obtain ⟨f⟩ := hA
      have hL : IsLineWithEnds A (f 0).1 (f 1).1 := ⟨f, rfl, rfl⟩
      have hoff : ∀ s, (f s).1 ∉ B := fun s h => by
        have : (f s).1 ∈ A ∩ B := ⟨(f s).2, h⟩
        rw [hd] at this
        exact this
      obtain ⟨R', hRf, hRK, hRoff, hR⟩ := ih (P ∪ A) K (hP.union hL.isCompact.isClosed) (hup hB)
        (hgrow hK) hl'
      refine ⟨insert (f 0).1 R', hRf.insert _, insert_subset (hAK (f 0).2) hRK, fun r hr => ?_,
        fun W hW hWK N hN hPN hRN hNW => ?_⟩
      · rcases hr with rfl | hr
        · exact .inr fun h => hoff 0 (hB (.inr h))
        · exact (hRoff r hr).imp id fun h h' => h (.inl h')
      · obtain ⟨α, hm, h1, h2⟩ := shrink_step hS hP hRf f (fun s _ h => hoff s (hB (.inl h)))
          (fun s _ h => hoff s (hB (.inr h))) hW (fun s h => disjoint_left.mp hWK h (hAK
            (f s).2)) hRoff (hR W hW hWK) N hN hPN (fun r hr => hRN (mem_insert_of_mem _ hr)) hNW
              (hRN (mem_insert _ _))
        exact ⟨α, hm, fun z hz => h1 z (hmem hz), h2⟩
    · obtain ⟨R', hRf, hRK, hRoff, hR⟩ := ih P K hP (hB.trans subset_union_left) (hgrow' hK hAK) hl'
      refine ⟨R', hRf, hRK, hRoff, fun W hW hWK N hN hPN hRN hNW => ?_⟩
      obtain ⟨α, hm, h1, h2⟩ := hR W hW hWK N hN hPN hRN hNW
      exact ⟨α, hm, fun z hz => h1 z (hskip hAK hz), h2⟩
  | @attached B A l k p q hA hd _ ih =>
    intro P K hP hB hK hl
    have hl' : ∀ A' ∈ l, A' ⊆ K ∨ Disjoint A' K := fun A' h => hl A' (List.mem_cons_of_mem _ h)
    rcases hl A List.mem_cons_self with hAK | hAK
    · obtain ⟨f, h0, h1⟩ := id hA
      have hoff : ∀ s, s ≠ 0 → (f s).1 ∉ B := fun s hs h => by
        have h2 : (f s).1 ∈ A ∩ B := ⟨(f s).2, h⟩
        rw [hd] at h2
        have h3 : (f s).1 = (f 0).1 := h2.trans h0.symm
        exact hs (f.injective (Subtype.ext h3))
      obtain ⟨R', hRf, hRK, hRoff, hR⟩ := ih (P ∪ A) K (hP.union hA.isCompact.isClosed) (hup hB)
        (hgrow hK) hl'
      have hpA : p ∈ A := h0 ▸ (f 0).2
      refine ⟨R' ∪ ({p} \ P), hRf.union ((finite_singleton p).subset sdiff_subset),
        union_subset hRK ?_, fun r hr => ?_, fun W hW hWK N hN hPN hRN hNW => ?_⟩
      · rintro _ ⟨rfl, -⟩
        exact hAK hpA
      · rcases hr with hr | hr
        · exact (hRoff r hr).imp id fun h h' => h (.inl h')
        · exact .inr hr.2
      · obtain ⟨α, hm, h1, h2⟩ := shrink_step hS hP hRf f (fun s hs h => hoff s hs (hB (.inl h)))
          (fun s hs h => hoff s hs (hB (.inr h))) hW (fun s h => disjoint_left.mp hWK h (hAK
            (f s).2)) hRoff (hR W hW hWK) N hN hPN (fun r hr => hRN (.inl hr)) hNW (by
          rw [h0]
          by_cases hpP : p ∈ P
          · exact hPN hpP
          · exact hRN (.inr ⟨rfl, hpP⟩))
        exact ⟨α, hm, fun z hz => h1 z (hmem hz), h2⟩
    · obtain ⟨R', hRf, hRK, hRoff, hR⟩ := ih P K hP (hB.trans subset_union_left) (hgrow' hK hAK) hl'
      refine ⟨R', hRf, hRK, hRoff, fun W hW hWK N hN hPN hRN hNW => ?_⟩
      obtain ⟨α, hm, h1, h2⟩ := hR W hW hWK N hN hPN hRN hNW
      exact ⟨α, hm, fun z hz => h1 z (hskip hAK hz), h2⟩

end GraphMinor.GM07
