/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM17.RegionDegree

/-!
# The frontier of a region is an `O`-arc

A connected union of finitely many lines, in which two lines meet only in marked points and each
marked point lies on exactly two lines, is an `O`-arc
(`isOArc_sUnion`). We follow a path of lines as far as it goes. Applied to the sides of a region
this gives (8.2) of Graph Minors XVII (page 181): the frontier of every
region of a tame painting is an `O`-arc (`frontier_isOArc`).
-/

@[expose] public section

namespace GraphMinor.GM17

open Set Topology GraphMinor.Surface

variable {X : Type} [TopologicalSpace X] [T2Space X]

/-- A path of lines inside a family: its inner marked points have all their lines in the path, and
each end lies on one line of the path. -/
structure IsPathOf (𝓛 : Set (Set X)) (V : Set X) (𝓐 : Set (Set X)) (a b : X) : Prop where
  sub : 𝓐 ⊆ 𝓛
  line : IsLineWithEnds (⋃₀ 𝓐) a b
  sat : ∀ x ∈ V, x ∈ ⋃₀ 𝓐 → x ≠ a → x ≠ b → ∀ L ∈ 𝓛, x ∈ L → L ∈ 𝓐
  left : ∃ L ∈ 𝓐, a ∈ L ∧ ∀ L' ∈ 𝓐, a ∈ L' → L' = L
  right : ∃ L ∈ 𝓐, b ∈ L ∧ ∀ L' ∈ 𝓐, b ∈ L' → L' = L

omit [T2Space X] in
theorem IsPathOf.symm {𝓛 : Set (Set X)} {V : Set X} {𝓐 : Set (Set X)} {a b : X}
  (h : IsPathOf 𝓛 V 𝓐 a b) : IsPathOf 𝓛 V 𝓐 b a :=
  ⟨h.sub, h.line.symm, fun x hx hm hb ha L hL hxL => h.sat x hx hm ha hb L hL hxL, h.right, h.left⟩

/-- A connected union of lines that meet two at a time in marked points, with exactly two lines at
each marked point, is an `O`-arc. -/
theorem isOArc_sUnion {𝓛 : Set (Set X)} {V : Set X} (hf : 𝓛.Finite) (hline : ∀ L ∈ 𝓛, ∃ u v,
  IsLineWithEnds L u v ∧ L ∩ V = {u, v}) (hin : ∀ L ∈ 𝓛, ∀ L' ∈ 𝓛, L ≠ L' → L ∩ L' ⊆ V)
    (hdeg : ∀ x ∈ V, ∀ L ∈ 𝓛, x ∈ L → ∃ L' ∈ 𝓛, L' ≠ L ∧ x ∈ L')
    (hdeg3 : ∀ x ∈ V, ∀ L₁ ∈ 𝓛, ∀ L₂ ∈ 𝓛, ∀ L₃ ∈ 𝓛, x ∈ L₁ → x ∈ L₂ → x ∈ L₃ → L₁ ≠ L₂ → L₁ ≠ L₃
      → L₂ ≠ L₃ → False) (hconn : IsPreconnected (⋃₀ 𝓛)) {L₀ : Set X} (hL₀ : L₀ ∈ 𝓛) :
    IsOArc (⋃₀ 𝓛) := by
  classical
  have hmain : ∀ n : ℕ, ∀ (𝓐 : Set (Set X)) (a b : X), IsPathOf 𝓛 V 𝓐 a b → (𝓛 \ 𝓐).ncard = n
    → a ∈ V → b ∈ V → IsOArc (⋃₀ 𝓛) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro 𝓐 a b hP hn haV hbV
      obtain ⟨L_b, hL_b, hbL, huniq⟩ := hP.right
      obtain ⟨L', hL', hne, hbL'⟩ := hdeg b hbV L_b (hP.sub hL_b) hbL
      have hL'𝓐 : L' ∉ 𝓐 := fun h => hne (huniq L' h hbL')
      obtain ⟨u, v, hl, hiV⟩ := hline L' hL'
      obtain ⟨w, hlw, hiw⟩ : ∃ w, IsLineWithEnds L' b w ∧ L' ∩ V = {b, w} := by
        rcases (hiV.le ⟨hbL', hbV⟩ : b ∈ ({u, v} : Set X)) with rfl | rfl
        · exact ⟨v, hl, hiV⟩
        · exact ⟨u, hl.symm, by rw [pair_comm]; exact hiV⟩
      have hmeet : ∀ {z}, z ∈ ⋃₀ 𝓐 → z ∈ L' → z = b ∨ z = w := fun {z} hz hz' => by
        obtain ⟨L, hL, hzL⟩ := hz
        exact hiw.le ⟨hz', hin L (hP.sub hL) L' hL' (fun e => hL'𝓐 (e ▸ hL)) ⟨hzL, hz'⟩⟩
      have hwV : w ∈ V := (hiw.ge (mem_insert_of_mem _ rfl) : w ∈ L' ∩ V).2
      have hbw := hlw.ne'
      by_cases hw : w ∈ ⋃₀ 𝓐
      · have hwa : w = a := by
          by_contra hwa
          exact hL'𝓐 (hP.sat w hwV hw hwa (Ne.symm hbw) L' hL' hlw.right_mem)
        subst hwa
        have hne' : w ≠ b := Ne.symm hbw
        have hi : (⋃₀ 𝓐) ∩ L' = {w, b} := by
          apply subset_antisymm
          · rintro z ⟨h1, h2⟩
            rcases hmeet h1 h2 with h | h
            · exact .inr h
            · exact .inl h
          · rintro z (rfl | rfl)
            · exact ⟨hw, hlw.right_mem⟩
            · exact ⟨hP.line.right_mem, hbL'⟩
        have hO : IsOArc (⋃₀ 𝓐 ∪ L') := oArc_of_lines hP.line hlw.symm hi
        obtain ⟨L_a, hL_a, haL, -⟩ := hP.left
        have hrest : ∀ L ∈ 𝓛, L ∉ 𝓐 → L ≠ L' → Disjoint L (⋃₀ 𝓐 ∪ L') := fun L hL h1 h2 => by
          refine disjoint_left.mpr fun z hz hz' => ?_
          have hzV : z ∈ V := by
            rcases hz' with ⟨L'', hL'', hz''⟩ | hz'
            · exact hin L hL L'' (hP.sub hL'') (fun e => h1 (e ▸ hL'')) ⟨hz, hz''⟩
            · exact hin L hL L' hL' h2 ⟨hz, hz'⟩
          by_cases hzw : z = w
          · subst hzw
            exact hdeg3 z hzV L_a (hP.sub hL_a) L' hL' L hL haL hlw.right_mem hz (fun e => hL'𝓐
              (e ▸ hL_a)) (fun e => h1 (e ▸ hL_a)) (Ne.symm h2)
          · by_cases hzb : z = b
            · subst hzb
              exact hdeg3 z hzV L_b (hP.sub hL_b) L' hL' L hL hbL hbL' hz (Ne.symm hne) (fun e
                => h1 (e ▸ hL_b)) (Ne.symm h2)
            · rcases hz' with hz' | hz'
              · exact h1 (hP.sat z hzV hz' hzw hzb L hL hz)
              · rcases hiw.le ⟨hz', hzV⟩ with h | h
                · exact hzb h
                · exact hzw h
        have hall : ⋃₀ 𝓛 = ⋃₀ 𝓐 ∪ L' := by
          apply subset_antisymm
          · rintro z ⟨L, hL, hz⟩
            by_cases h1 : L ∈ 𝓐
            · exact .inl ⟨L, h1, hz⟩
            · by_cases h2 : L = L'
              · exact .inr (h2 ▸ hz)
              · exfalso
                have hO1 : IsClosed (⋃₀ 𝓐 ∪ L') := hP.line.isCompact.isClosed.union
                  hlw.isCompact.isClosed
                have hR : IsClosed (⋃₀ (𝓛 \ insert L' 𝓐)) := (hf.subset
                  sdiff_subset).isClosed_sUnion fun L₁ hL₁ => by
                  obtain ⟨u₁, v₁, h3, -⟩ := hline L₁ hL₁.1
                  exact h3.isCompact.isClosed
                have hcov : ⋃₀ 𝓛 ⊆ (⋃₀ 𝓐 ∪ L') ∪ ⋃₀ (𝓛 \ insert L' 𝓐) := by
                  rintro y ⟨L₁, hL₁, hy⟩
                  by_cases h3 : L₁ ∈ 𝓐
                  · exact .inl (.inl ⟨L₁, h3, hy⟩)
                  · by_cases h4 : L₁ = L'
                    · exact .inl (.inr (h4 ▸ hy))
                    · exact .inr ⟨L₁, ⟨hL₁, by rintro (h5 | h5); exacts [h4 h5, h3 h5]⟩, hy⟩
                have hbU : b ∈ ⋃₀ 𝓛 := ⟨L', hL', hbL'⟩
                have hLout : L ∈ 𝓛 \ insert L' 𝓐 := by
                  refine ⟨hL, ?_⟩
                  rintro (h5 | h5)
                  · exact h2 h5
                  · exact h1 h5
                obtain ⟨y, -, hy, hy'⟩ := isPreconnected_closed_iff.mp hconn _ _ hO1 hR hcov
                  ⟨b, hbU, .inr hbL'⟩ ⟨z, ⟨L, hL, hz⟩, ⟨L, hLout, hz⟩⟩
                obtain ⟨L₁, hL₁, hyL₁⟩ := hy'
                refine disjoint_left.mp (hrest L₁ hL₁.1 (fun h5 => hL₁.2 (.inr h5)) (fun h5
                  => hL₁.2 (.inl h5))) hyL₁ hy
          · rintro z (⟨L, hL, hz⟩ | hz)
            · exact ⟨L, hP.sub hL, hz⟩
            · exact ⟨L', hL', hz⟩
        rw [hall]
        exact hO
      · have hi : (⋃₀ 𝓐) ∩ L' = {b} := by
          apply subset_antisymm
          · rintro z ⟨h1, h2⟩
            rcases hmeet h1 h2 with h | h
            · exact h
            · exact absurd (h ▸ h1) hw
          · rintro _ rfl
            exact ⟨hP.line.right_mem, hbL'⟩
        have hab := hP.line.ne'
        have haL' : a ∉ L' := fun h => hab (by
          have h1 : a ∈ (⋃₀ 𝓐) ∩ L' := ⟨hP.line.left_mem, h⟩
          rw [hi] at h1
          exact h1)
        have hP' : IsPathOf 𝓛 V (insert L' 𝓐) a w := by
          refine ⟨insert_subset hL' hP.sub, ?_, ?_, ?_, ?_⟩
          · rw [sUnion_insert, union_comm]
            exact hP.line.union hlw hi
          · rintro x hx hm hxa hxw L hL hxL
            by_cases hxb : x = b
            · subst hxb
              by_cases h1 : L = L'
              · exact .inl h1
              · by_cases h2 : L = L_b
                · exact .inr (h2 ▸ hL_b)
                · exact (hdeg3 x hx L_b (hP.sub hL_b) L' hL' L hL hbL hbL' hxL (Ne.symm hne)
                  (Ne.symm h2) (Ne.symm h1)).elim
            · rcases hm with ⟨L₁, rfl | h1, hx1⟩
              · rcases hiw.le ⟨hx1, hx⟩ with h | h
                · exact absurd h hxb
                · exact absurd h hxw
              · exact .inr (hP.sat x hx ⟨L₁, h1, hx1⟩ hxa hxb L hL hxL)
          · obtain ⟨L_a, h1, h2, h3⟩ := hP.left
            refine ⟨L_a, .inr h1, h2, ?_⟩
            rintro L₁ (rfl | h4) h5
            · exact absurd h5 haL'
            · exact h3 L₁ h4 h5
          · refine ⟨L', .inl rfl, hlw.right_mem, ?_⟩
            rintro L₁ (rfl | h4) h5
            · rfl
            · exact absurd ⟨L₁, h4, h5⟩ hw
        have hlt : (𝓛 \ insert L' 𝓐).ncard < n := by
          rw [← hn]
          refine Set.ncard_lt_ncard ?_ (hf.subset sdiff_subset)
          refine ⟨fun x hx => ⟨hx.1, fun h => hx.2 (.inr h)⟩, fun h => ?_⟩
          exact (h ⟨hL', hL'𝓐⟩).2 (.inl rfl)
        exact ih _ hlt _ a w hP' rfl haV hwV
  obtain ⟨u, v, hl, hiV⟩ := hline L₀ hL₀
  have hu : u ∈ V := (hiV.ge (mem_insert _ _) : u ∈ L₀ ∩ V).2
  have hv : v ∈ V := (hiV.ge (mem_insert_of_mem _ rfl) : v ∈ L₀ ∩ V).2
  refine hmain _ {L₀} u v ⟨singleton_subset_iff.mpr hL₀, by simpa using hl, ?_, ?_, ?_⟩ rfl hu hv
  · rintro x hx hm hxu hxv L hL hxL
    rw [sUnion_singleton] at hm
    rcases hiV.le ⟨hm, hx⟩ with h | h
    · exact absurd h hxu
    · exact absurd h hxv
  · exact ⟨L₀, rfl, hl.left_mem, fun L' h _ => h⟩
  · exact ⟨L₀, rfl, hl.right_mem, fun L' h _ => h⟩

namespace Painting

variable {S : Type} [TopologicalSpace S] {Γ : Painting S}

/-- The frontier of a region of a tame painting is the union of the sides of the region. -/
theorem frontier_eq_sides [T2Space S] [ConnectedSpace S] (hS : IsSurface S)
  (hΓ : Γ.Tame) {r : Set S} (hr : r ∈ Γ.regions) : closure r \ r = ⋃₀ {L | Γ.SideOf r L} := by
  have hcS : CompactSpace S := hS.1
  apply subset_antisymm
  · rintro y ⟨hy, hyr⟩
    by_cases hyN : y ∈ Γ.N
    · obtain ⟨L, hL, hyL⟩ := first_side hS hΓ hr hy hyN
      exact ⟨L, hL, hyL⟩
    · obtain ⟨L, hL, hyL⟩ :=
        frontier_region hS hΓ.isOpen (fun c hc => two_nodes hS hΓ hc) hr hy hyr hyN
      exact ⟨L, hL, hyL⟩
  · rintro y ⟨L, ⟨c, u, v, hs, hcl⟩, hy⟩
    exact ⟨hcl hy, fun h => region_subset hr h (hs.1.subset_U hy)⟩

/-- The frontier of a region of a tame painting is an `O`-arc. -/
theorem frontier_isOArc [T2Space S] [ConnectedSpace S] (hS : IsSurface S) (hΓ : Γ.Tame) {r : Set S}
  (hr : r ∈ Γ.regions) : IsOArc (closure r \ r) := by
  have hcS : CompactSpace S := hS.1
  have hne : (closure r \ r).Nonempty := by
    by_contra hem
    have h1 : closure r ⊆ r := fun x hx => by
      by_contra hn
      exact hem ⟨x, hx, hn⟩
    have hclop : IsClopen r := ⟨closure_subset_iff_isClosed.mp h1, hΓ.isOpen r hr⟩
    obtain ⟨x, hx⟩ := arcComponentsIn_nonempty hr
    have huniv := hclop.eq_univ ⟨x, hx⟩
    have hNe : Γ.N.Nonempty := by
      by_contra h
      have h0 : Γ.N = ∅ := not_nonempty_iff_eq_empty.mp h
      have := hΓ.six
      rw [h0] at this
      simp at this
    obtain ⟨n, hn⟩ := hNe
    exact region_subset hr (huniv ▸ mem_univ n) (Γ.N_subset hn)
  rw [frontier_eq_sides hS hΓ hr] at hne ⊢
  obtain ⟨y, L₀, hL₀, -⟩ := hne
  refine isOArc_sUnion (V := Γ.N) (finite_sideOf r) ?_ ?_ ?_ ?_ ?_ hL₀
  · rintro L ⟨c, u, v, hs, -⟩
    exact ⟨u, v, hs.1.2.1, hs.1.2.2.2⟩
  · exact fun L hL L' hL' hne z hz => sides_inter hL hL' hne hz.1 hz.2
  · rintro x hx L hL hxL
    obtain ⟨L', h1, h2, h3⟩ := other_side hS hΓ hr hL hxL hx
    exact ⟨L', h1, h3, h2⟩
  · intro x hx L₁ h₁ L₂ h₂ L₃ h₃ h1 h2 h3 h12 h13 h23
    exact three_sides hS hΓ hr h₁ h₂ h₃ h1 h2 h3 hx h12 h13 h23
  · rw [← frontier_eq_sides hS hΓ hr]
    exact isPreconnected_frontier (hΓ.open_disc r hr)

end Painting

end GraphMinor.GM17
