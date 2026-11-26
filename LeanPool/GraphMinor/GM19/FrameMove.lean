/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.FrameExists

/-!
# Moving a painting onto the frame

For each cuff, a painting has a border edge on it. An arc of the cuff moves onto the short side, by
a
homeomorphism of the circle that preserves orientation, and this extends to the surface by
`move_cuff`. The
composite homeomorphism has null signature. This is "a suitable homeomorphism of $\Sigma$ to itself"
in the proof of
Graph Minors XIX, (2.1).
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface

variable {S : Type} [TopologicalSpace S] [T2Space S]

/-! ### Edges on a cuff -/

omit [T2Space S] in
theorem exists_edge_on_cuff (Γ : Painting S) (C : cuffs S) (f : Circle ≃ₜ C.1) :
    ∃ e ∈ Γ.E, e ⊆ C.1 ∧ Painting.IsBorder e := by
  have hpi := Real.pi_pos
  have hinf : (arcOf f 0 1).Infinite := by
    refine (Ioo_infinite (zero_lt_one' ℝ)).image ?_
    refine (cuffPoint_injOn_Icc f (a := 0) (b := 1) (by linarith [Real.pi_gt_three])).mono ?_
    exact Ioo_subset_Icc_self
  obtain ⟨x, hx, hxV⟩ := (hinf.sdiff Γ.finite_V).nonempty
  have hxC : x ∈ C.1 := arcOf_subset f _ _ hx
  have hxb : x ∈ bd S := cuff_subset_bd C hxC
  have hm : x ∈ Γ.U \ Γ.V := ⟨Γ.bd_subset hxb, hxV⟩
  have hc : pathComponentIn (Γ.U \ Γ.V) x ∈ Γ.E := Surface.mem_arcComponentsIn_of_mem hm
  have hxc : x ∈ pathComponentIn (Γ.U \ Γ.V) x := mem_pathComponentIn_self hm
  have hbo : Painting.IsBorder (pathComponentIn (Γ.U \ Γ.V) x) := ⟨x, hxc, hxb⟩
  refine ⟨_, hc, ?_, hbo⟩
  have key : ∀ C' ∈ cuffs S, x ∈ C' → C' = connectedComponentIn (bd S) x := by
    rintro _ ⟨y, -, rfl⟩ hx'
    exact connectedComponentIn_eq hx'
  rw [key _ C.2 hxC]
  exact hc.2.2.1.isConnected.isPreconnected.subset_connectedComponentIn hxc
    (Γ.border_edge _ hc hbo).2

theorem arc_eq_of_mem {Θ e : Set S} (f : Circle ≃ₜ Θ) {a b : ℝ} (hab : a < b)
    (hb : b < a + 2 * Real.pi) (he : IsPathConnected e) (heΘ : e ⊆ Θ) (hcl : closure e ⊆ Θ)
    (hL : IsLineWithEnds (closure e) (cuffPoint f a) (cuffPoint f b))
    (ht : tilde e = {cuffPoint f a, cuffPoint f b}) {z : S} (hz : z ∈ e)
    (hza : z ∈ arcOf f a b) : e = arcOf f a b := by
  have hF : IsOArc Θ := ⟨f⟩
  have hLA := isLine_arcOf f hab hb
  have htA := tilde_arcOf f hab hb
  have hsubA : arcOf f a b ⊆ Θ \ {cuffPoint f a, cuffPoint f b} := fun x hx ↦
    ⟨arcOf_subset f _ _ hx, fun hm ↦ (htA ▸ hm : x ∈ tilde (arcOf f a b)).2 hx⟩
  have hsube : e ⊆ Θ \ {cuffPoint f a, cuffPoint f b} := fun x hx ↦
    ⟨heΘ hx, fun hm ↦ (ht ▸ hm : x ∈ tilde e).2 hx⟩
  have hc₁ : closure (arcOf f a b) ⊆ Θ :=
    closure_minimal (arcOf_subset f _ _) (IsOArc.isCompact hF).isClosed
  apply Subset.antisymm
  · intro x hx
    have := subset_line_of_preconnected hF hLA hc₁ he.isConnected.isPreconnected hsube hz
      (subset_closure hza) hx
    by_contra hn
    have hm : x ∈ tilde (arcOf f a b) := ⟨this, hn⟩
    rw [htA] at hm
    exact (hsube hx).2 hm
  · intro x hx
    have := subset_line_of_preconnected hF hL hcl
      (isPathConnected_arcOf f hab).isConnected.isPreconnected hsubA hza (subset_closure hz) hx
    by_contra hn
    have hm : x ∈ tilde e := ⟨this, hn⟩
    rw [ht] at hm
    exact (hsubA hx).2 hm

/-- A border edge on a cuff is an open arc of the cuff, as read through any parametrization. -/
theorem edge_arc (Γ : Painting S) {e Θ : Set S} (f : Circle ≃ₜ Θ) (he : e ∈ Γ.E)
    (h2 : (tilde e).ncard = 2) (heΘ : e ⊆ Θ) :
    ∃ α θ : ℝ, θ ∈ Ioo 0 (2 * Real.pi) ∧ e = arcOf f α (α + θ) := by
  have hpi := Real.pi_pos
  have hF : IsOArc Θ := ⟨f⟩
  have hcl : closure e ⊆ Θ := closure_minimal heΘ (IsOArc.isCompact hF).isClosed
  obtain ⟨g, hne, ht⟩ := Γ.exists_line he h2
  have hL : IsLineWithEnds (closure e) (g 0).1 (g 1).1 := ⟨g, rfl, rfl⟩
  obtain ⟨a, ha, hax⟩ := exists_angle_in f 0 ⟨(g 0).1, hcl (g 0).2⟩
  obtain ⟨b, hb, hby⟩ := exists_angle_in f a ⟨(g 1).1, hcl (g 1).2⟩
  change cuffPoint f a = _ at hax
  change cuffPoint f b = _ at hby
  rw [← hax, ← hby] at hL ht
  have hab : a < b := by
    rcases eq_or_lt_of_le hb.1 with h | h
    · exact absurd (by rw [← hax, ← hby, h]) hne
    · exact h
  have hb2 := hb.2
  obtain ⟨z, hz⟩ := he.1
  have hzΘ := heΘ hz
  obtain ⟨t, ht₁, htz⟩ := exists_angle_in f a ⟨z, hzΘ⟩
  change cuffPoint f t = z at htz
  have hza : t ≠ a := fun h ↦ by
    have : z ∈ tilde e := ht ▸ Or.inl (by rw [← htz, h])
    exact this.2 hz
  have hzb : t ≠ b := fun h ↦ by
    have : z ∈ tilde e := ht ▸ Or.inr (by rw [← htz, h]; rfl)
    exact this.2 hz
  have hta : a < t := lt_of_le_of_ne ht₁.1 (Ne.symm hza)
  rcases lt_or_gt_of_ne hzb with h | h
  · exact ⟨a, b - a, ⟨by linarith, by linarith⟩, by
      rw [add_sub_cancel]
      exact arc_eq_of_mem f hab hb2 he.2.2.1 heΘ hcl hL ht hz ⟨t, ⟨hta, h⟩, htz⟩⟩
  · have hend : cuffPoint f (a + 2 * Real.pi) = cuffPoint f a := cuffPoint_add_two_pi f a
    refine ⟨b, a + 2 * Real.pi - b, ⟨by linarith, by linarith⟩, ?_⟩
    rw [add_sub_cancel]
    refine arc_eq_of_mem f (a := b) (b := a + 2 * Real.pi) hb2 (by linarith) he.2.2.1 heΘ hcl
      ?_ ?_ hz ⟨t, ⟨h, ht₁.2⟩, htz⟩
    · rw [hend]
      exact GM11.IsLineWithEnds.symm hL
    · rw [hend, ht, pair_comm]

/-! ### One cuff at a time -/

/-- Each homeomorphism of a surface that moves `Θ` along an orientation preserving homeomorphism of
the
circle. -/
def MovesAlong (h : S ≃ₜ S) {Θ : Set S} (f : Circle ≃ₜ Θ) : Prop :=
  ∃ ψ : Circle ≃ₜ Circle, PreservesCircleOrientation ψ ∧ ∀ z, h (f z).1 = (f (ψ z)).1

omit [T2Space S] in
theorem MovesAlong.symm {h : S ≃ₜ S} {Θ : Set S} {f : Circle ≃ₜ Θ} (hm : MovesAlong h f) :
    MovesAlong h.symm f := by
  obtain ⟨ψ, hψ, he⟩ := hm
  refine ⟨ψ.symm, preserves_symm hψ, fun z ↦ ?_⟩
  rw [Homeomorph.symm_apply_eq, he]
  simp

omit [T2Space S] in
theorem MovesAlong.trans {h h' : S ≃ₜ S} {Θ : Set S} {f : Circle ≃ₜ Θ} (hm : MovesAlong h f)
    (hm' : MovesAlong h' f) : MovesAlong (h.trans h') f := by
  obtain ⟨ψ, ⟨l, lc, lm, hl⟩, he⟩ := hm
  obtain ⟨ψ', ⟨l', lc', lm', hl'⟩, he'⟩ := hm'
  refine ⟨ψ.trans ψ', ⟨l' ∘ l, lc'.comp lc, lm'.comp lm, fun t ↦ ?_⟩, fun z ↦ ?_⟩
  · simp only [Homeomorph.trans_apply, Function.comp]
    rw [hl, hl']
  · simp only [Homeomorph.trans_apply]
    rw [he, he']

omit [T2Space S] in
theorem movesAlong_refl {Θ : Set S} (f : Circle ≃ₜ Θ) : MovesAlong (Homeomorph.refl S) f :=
  ⟨Homeomorph.refl _, ⟨id, continuous_id, strictMono_id, fun _ ↦ rfl⟩, fun _ ↦ rfl⟩

omit [T2Space S] in
theorem movesAlong_of_fix {h : S ≃ₜ S} {Θ : Set S} (f : Circle ≃ₜ Θ) (hfix : ∀ x ∈ Θ, h x = x) :
    MovesAlong h f :=
  ⟨Homeomorph.refl _, ⟨id, continuous_id, strictMono_id, fun _ ↦ rfl⟩, fun z ↦ hfix _ (f z).2⟩

omit [T2Space S] in
/-- A homeomorphism that moves each cuff along one parametrization has null signature. -/
theorem hasNullSignature_of_moves {h : S ≃ₜ S} {par : ∀ C : cuffs S, Circle ≃ₜ C.1}
    (hm : ∀ C, MovesAlong h (par C)) : HasNullSignature h := by
  intro C φ hC
  obtain ⟨ψ, hψ, he⟩ := hm ⟨C, hC⟩
  let τ : Circle ≃ₜ Circle := φ.trans (par ⟨C, hC⟩).symm
  refine ⟨τ.trans (ψ.trans τ.symm), preserves_conj τ hψ, fun x ↦ ?_⟩
  have h1 : (φ x).1 = ((par ⟨C, hC⟩) (τ x)).1 := by simp [τ]
  rw [h1, he]
  simp [τ]

variable (par : ∀ C : cuffs S, Circle ≃ₜ C.1)

theorem isClosed_cuff (hS : IsSurface S) (C : cuffs S) : IsClosed C.1 :=
  (IsOArc.isCompact ((cuff_statement S hS).2.2 C.1 C.2)).isClosed

theorem exists_move_one (hS : IsSurface S) (C : cuffs S) {e : Set S} {α θ : ℝ}
    (hθ : θ ∈ Ioo 0 (2 * Real.pi)) (he : e = arcOf (par C) α (α + θ)) :
    ∃ h : S ≃ₜ S, MovesAlong h (par C) ∧ (∀ C', C' ≠ C → ∀ x ∈ C'.1, h x = x) ∧
      h '' e = upSide par C := by
  have hpi := Real.pi_pos
  obtain ⟨ψ, hψ, hs⟩ := exists_circle_move (Circle.exp α) hθ
  have hopen : IsOpen (bd S \ C.1)ᶜ := by
    refine (?_ : IsClosed (bd S \ C.1)).isOpen_compl
    have heq : bd S \ C.1 = ⋃ C' ∈ {C' : cuffs S | C' ≠ C}, C'.1 := by
      ext x
      constructor
      · rintro ⟨hx, hn⟩
        exact mem_iUnion₂.2 ⟨⟨_, x, hx, rfl⟩, fun h ↦ hn (by
          rw [← h]
          exact mem_connectedComponentIn hx), mem_connectedComponentIn hx⟩
      · intro hx
        obtain ⟨C', hC', hxC⟩ := mem_iUnion₂.mp hx
        exact ⟨cuff_subset_bd C' hxC, disjoint_left.mp (cuffs_disjoint' hC') hxC⟩
    rw [heq]
    have : Finite (cuffs S) := (cuff_statement S hS).2.1.to_subtype
    exact (Set.toFinite _).isClosed_biUnion fun C' _ ↦ isClosed_cuff hS C'
  obtain ⟨h, hh, hfix⟩ := move_cuff S C.1 (bd S \ C.1)ᶜ (par C) ψ hS C.2 hopen
    (fun x hx hn ↦ hn.2 hx) hψ
  have hstep : ∀ s ∈ Icc 0 θ, h (cuffPoint (par C) (α + s)) = cuffPoint (par C) (Real.pi * (s / θ))
    := by
    intro s hsm
    simp only [cuffPoint]
    rw [hh, Circle.exp_add, hs s hsm]
  refine ⟨h, ⟨ψ, hψ, hh⟩, fun C' hne x hx ↦ hfix x ?_, ?_⟩
  · intro hU
    exact hU ⟨cuff_subset_bd C' hx, disjoint_left.mp (cuffs_disjoint' hne) hx⟩
  · rw [he]
    ext y
    constructor
    · rintro ⟨_, ⟨t, ht, rfl⟩, rfl⟩
      have hs₀ : t - α ∈ Ioo 0 θ := ⟨by linarith [ht.1], by linarith [ht.2]⟩
      have hrw := hstep (t - α) ⟨hs₀.1.le, hs₀.2.le⟩
      rw [add_sub_cancel] at hrw
      rw [hrw]
      refine ⟨_, ⟨by
        have := div_pos hs₀.1 hθ.1
        positivity, ?_⟩, rfl⟩
      have : (t - α) / θ < 1 := (div_lt_one hθ.1).mpr hs₀.2
      nlinarith
    · rintro ⟨t, ht, rfl⟩
      have ht' : θ * (t / Real.pi) ∈ Ioo 0 θ := by
        have h1 : 0 < t / Real.pi := div_pos ht.1 hpi
        have h2 : t / Real.pi < 1 := (div_lt_one hpi).mpr ht.2
        exact ⟨mul_pos hθ.1 h1, by nlinarith [hθ.1]⟩
      refine ⟨cuffPoint (par C) (α + θ * (t / Real.pi)), ⟨_, ⟨by linarith [ht'.1],
        by linarith [ht'.2]⟩,
        rfl⟩, ?_⟩
      rw [hstep _ ⟨ht'.1.le, ht'.2.le⟩]
      have h3 : θ * (t / Real.pi) / θ = t / Real.pi := mul_div_cancel_left₀ _ hθ.1.ne'
      rw [h3, mul_div_cancel₀ _ hpi.ne']

/-- All the cuffs at once. -/
theorem exists_move (hS : IsSurface S) (Γ : Painting S) :
    ∃ h : S ≃ₜ S, (∀ C, MovesAlong h (par C)) ∧
      ∀ C, ∃ e ∈ Γ.E, e ⊆ C.1 ∧ (tilde e).ncard = 2 ∧ h '' e = upSide par C := by
  have : Finite (cuffs S) := (cuff_statement S hS).2.1.to_subtype
  have := Fintype.ofFinite (cuffs S)
  classical
  have main : ∀ s : Finset (cuffs S), ∃ h : S ≃ₜ S, (∀ C, MovesAlong h (par C)) ∧
      (∀ C, C ∉ s → ∀ x ∈ C.1, h x = x) ∧
      ∀ C ∈ s, ∃ e ∈ Γ.E, e ⊆ C.1 ∧ (tilde e).ncard = 2 ∧ h '' e = upSide par C := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      exact ⟨Homeomorph.refl S, fun C ↦ movesAlong_refl _, fun _ _ _ _ ↦ rfl, fun C hC ↦
        absurd hC (by simp)⟩
    | insert C s hCs ih =>
      obtain ⟨h, h₁, h₂, h₃⟩ := ih
      obtain ⟨e, he, heC, hbo⟩ := exists_edge_on_cuff Γ C (par C)
      have h2 := size_two_of_border Γ he hbo
      obtain ⟨α, θ, hθ, heq⟩ := edge_arc Γ (par C) he h2 heC
      obtain ⟨k, k₁, k₂, k₃⟩ := exists_move_one par hS C hθ heq
      refine ⟨h.trans k, fun C' ↦ ?_, fun C' hC' x hx ↦ ?_, fun C' hC' ↦ ?_⟩
      · refine (h₁ C').trans ?_
        by_cases hCC : C' = C
        · subst hCC
          exact k₁
        · exact movesAlong_of_fix _ (k₂ C' hCC)
      · have hne : C' ≠ C := fun he ↦ hC' (by simp [he])
        have hns : C' ∉ s := fun he ↦ hC' (by simp [he])
        change k (h x) = x
        rw [h₂ C' hns x hx, k₂ C' hne x hx]
      · by_cases hCC : C' = C
        · subst hCC
          refine ⟨e, he, heC, h2, ?_⟩
          have : (h.trans k) '' e = k '' (h '' e) := by
            rw [← image_comp]
            rfl
          rw [this, ← k₃]
          congr 1
          ext y
          constructor
          · rintro ⟨x, hx, rfl⟩
            rwa [h₂ C' hCs x (heC hx)]
          · intro hy
            exact ⟨y, hy, h₂ C' hCs y (heC hy)⟩
        · have hs : C' ∈ s := by simpa [hCC] using hC'
          obtain ⟨e', he', hsub, h2', himg⟩ := h₃ C' hs
          refine ⟨e', he', hsub, h2', ?_⟩
          have : (h.trans k) '' e' = k '' (h '' e') := by
            rw [← image_comp]
            rfl
          rw [this, himg]
          ext y
          constructor
          · rintro ⟨x, hx, rfl⟩
            rwa [k₂ C' hCC x (arcOf_subset _ _ _ hx)]
          · intro hy
            exact ⟨y, hy, k₂ C' hCC y (arcOf_subset _ _ _ hy)⟩
  obtain ⟨h, h₁, -, h₃⟩ := main Finset.univ
  exact ⟨h, h₁, fun C ↦ h₃ C (Finset.mem_univ C)⟩

end GraphMinor.GM19
