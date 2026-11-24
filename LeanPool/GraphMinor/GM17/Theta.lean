/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM17.CellNodes
public import LeanPool.GraphMinor.Surface.ArcInPath

/-!
# Three lines between two points

Assume three lines join two points and the union of any two of them bounds a disc that misses the
third line. Then the three discs cover the surface
(`theta_cover`). This is how we show that the frontier of a region passes through a node at most
once. We also collect small tools on lines used there.
-/

@[expose] public section

namespace GraphMinor.GM17

open Set Topology Metric GraphMinor.Surface

variable {S : Type} [TopologicalSpace S] [T2Space S]

omit [T2Space S] in
/-- Near a point of the boundary of a disc, the disc without that point is connected. -/
theorem disc_punct {D V : Set S} {x : S} (hD : IsClosedDisc D) (hx : x ∈ discBd D) (hV : V ∈ 𝓝 x) :
    ∃ C W, IsPreconnected C ∧ C ⊆ D ∧ C ⊆ V ∧ x ∉ C ∧ W ∈ 𝓝 x ∧ (D ∩ W) \ {x} ⊆ C := by
  obtain ⟨h, g, c⟩ := hD.exists_isChart
  have hxD := discBd_subset D hx
  have hw : ‖h x‖ = 1 := by
    have h1 : h x ∈ sphere (0 : ℂ) 1 := c.bd ▸ mem_image_of_mem _ hx
    simpa using h1
  have hwm : h x ∈ closedBall (0 : ℂ) 1 := c.hm hxD
  have hgw : g (h x) = x := c.gh hxD
  have h1 : g ⁻¹' V ∈ 𝓝[closedBall (0 : ℂ) 1] (h x) := (c.gc _ hwm) (by rw [hgw]; exact hV)
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhdsWithin_iff.mp h1
  obtain ⟨u, hu, he⟩ := (_root_.continuousOn_iff'.mp c.hc) (ball (h x) ε) isOpen_ball
  refine ⟨g '' ((closedBall 0 1 ∩ ball (h x) ε) \ {h x}), u, (isPreconnected_ball_diff hw ε).image
    _ (c.gc.mono fun z hz => hz.1.1), ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact c.gm hz.1.1
  · rintro _ ⟨z, hz, rfl⟩
    exact hsub ⟨hz.1.2, hz.1.1⟩
  · rintro ⟨z, hz, he'⟩
    apply hz.2
    rw [← c.hg hz.1.1, he']
    rfl
  · refine hu.mem_nhds ?_
    have h2 : x ∈ h ⁻¹' ball (h x) ε ∩ D := ⟨mem_ball_self hε, hxD⟩
    rw [he] at h2
    exact h2.1
  · rintro y ⟨⟨hyD, hyu⟩, hyx⟩
    have h2 : y ∈ h ⁻¹' ball (h x) ε ∩ D := by
      rw [he]
      exact ⟨hyu, hyD⟩
    refine ⟨h y, ⟨⟨c.hm hyD, h2.1⟩, fun he' => hyx ?_⟩, c.gh hyD⟩
    rw [← c.gh hyD, he', hgw]
    rfl

/-- A line in a path connected set that joins two closed sets and meets them only in its ends. -/
theorem exists_bridge {r X Y : Set S} {x₀ y₀ : S} (hr : IsPathConnected r) (hX : IsClosed X)
  (hY : IsClosed Y) (hx₀ : x₀ ∈ X) (hx₀r : x₀ ∈ r) (hy₀ : y₀ ∈ Y) (hy₀r : y₀ ∈ r)
    (hd : ∀ z ∈ r, z ∈ X → z ∉ Y) : ∃ β x y, IsLineWithEnds β x y ∧ β ⊆ r ∧ x ∈ X ∧ y ∈ Y ∧ β ∩ X
      = {x} ∧ β ∩ Y = {y} := by
  obtain ⟨γ, hγ⟩ := (hr.joinedIn x₀ hx₀r y₀ hy₀r)
  have hne : γ 0 ≠ γ 1 := by
    rw [γ.source, γ.target]
    rintro rfl
    exact hd _ hx₀r hx₀ hy₀
  obtain ⟨e, hec, hei, he0, he1, her⟩ := exists_arc_of_path γ.continuous hne
  have her' : ∀ t, e t ∈ r := fun t => by
    obtain ⟨s, hs⟩ := her (mem_range_self t)
    exact hs ▸ hγ s
  have hT₁ : IsCompact (e ⁻¹' X) := (hX.preimage hec).isCompact
  obtain ⟨t₁, ht₁, hmax⟩ :=
    hT₁.exists_isGreatest ⟨0, by rw [mem_preimage, he0, γ.source]; exact hx₀⟩
  have hT₂ : IsCompact (e ⁻¹' Y ∩ Ici t₁) := ((hY.preimage hec).inter isClosed_Ici).isCompact
  obtain ⟨t₂, ⟨ht₂, ht₁₂⟩, hmin⟩ :=
    hT₂.exists_isLeast ⟨1, by
      rw [mem_inter_iff, mem_preimage, he1, γ.target]
      exact ⟨hy₀, unitInterval.le_one _⟩⟩
  have hlt : t₁ < t₂ := lt_of_le_of_ne ht₁₂ fun h => hd _ (her' t₁) ht₁ (h ▸ ht₂)
  refine ⟨e '' Icc t₁ t₂, e t₁, e t₂, isLine_piece ⟨hec, hei⟩ hlt, ?_, ht₁, ht₂, ?_, ?_⟩
  · rintro _ ⟨t, -, rfl⟩
    exact her' t
  · apply subset_antisymm
    · rintro _ ⟨⟨t, ht, rfl⟩, hX'⟩
      rw [show t = t₁ from le_antisymm (hmax hX') ht.1]
      rfl
    · rintro _ rfl
      exact ⟨⟨t₁, ⟨le_rfl, ht₁₂⟩, rfl⟩, ht₁⟩
  · apply subset_antisymm
    · rintro _ ⟨⟨t, ht, rfl⟩, hY'⟩
      rw [show t = t₂ from le_antisymm ht.2 (hmin ⟨hY', ht.1⟩)]
      rfl
    · rintro _ rfl
      exact ⟨⟨t₂, ⟨ht₁₂, le_rfl⟩, rfl⟩, ht₂⟩

/-- The piece of a line from one end up to a point other than this end. -/
theorem sub_line {L : Set S} {u v x : S} (hL : IsLineWithEnds L u v) (hx : x ∈ L)
  (hxu : x ≠ u) : ∃ L₁, IsLineWithEnds L₁ u x ∧ L₁ ⊆ L ∧ (x ≠ v → v ∉ L₁) := by
  by_cases hxv : x = v
  · subst hxv
    exact ⟨L, hL, subset_rfl, fun h => absurd rfl h⟩
  · obtain ⟨L₁, L₂, h1, h2, hu, hi⟩ := hL.split hx hxu hxv
    refine ⟨L₁, h1, hu ▸ subset_union_left, fun _ hv => hxv ?_⟩
    have h3 : v ∈ L₁ ∩ L₂ := ⟨hv, h2.right_mem⟩
    rw [hi] at h3
    exact h3.symm

/-- Splitting an `O`-arc made of two lines at another point, keeping each line near the first end.
-/
theorem split_oarc {A₁ A₂ : Set S} {a x q : S} (h₁ : IsLineWithEnds A₁ a x)
  (h₂ : IsLineWithEnds A₂ a x) (hi : A₁ ∩ A₂ = {a, x}) (hq : q ∈ A₁ ∪ A₂) (hqa : q ≠ a) :
    ∃ P₁ P₂, IsLineWithEnds P₁ a q ∧ IsLineWithEnds P₂ a q ∧ P₁ ∪ P₂ = A₁ ∪ A₂ ∧ P₁ ∩ P₂ = {a, q}
      ∧ a ∉ closure (P₁ \ A₁) ∧ a ∉ closure (P₂ \ A₂) := by
  have hstep : ∀ {A B : Set S}, IsLineWithEnds A a x → IsLineWithEnds B a x → A ∩ B = {a, x}
    → q ∈ B → q ≠ x →
      ∃ P₁ P₂, IsLineWithEnds P₁ a q ∧ IsLineWithEnds P₂ a q ∧ P₁ ∪ P₂ = A ∪ B ∧ P₁ ∩ P₂ = {a, q}
        ∧ a ∉ closure (P₁ \ A) ∧ a ∉ closure (P₂ \ B) := fun {A B} hA hB hAB hqB hqx => by
    obtain ⟨B₁, B₂, h1, h2, hu, hi'⟩ := hB.split hqB hqa hqx
    have hB₁ : B₁ ⊆ B := hu ▸ subset_union_left
    have hB₂ : B₂ ⊆ B := hu ▸ subset_union_right
    have hsub : A ∩ B₂ = {x} := by
      apply subset_antisymm
      · rintro z ⟨hz, hz'⟩
        rcases (hAB ▸ ⟨hz, hB₂ hz'⟩ : z ∈ ({a, x} : Set S)) with rfl | rfl
        · exfalso
          have h3 : z ∈ B₁ ∩ B₂ := ⟨h1.left_mem, hz'⟩
          rw [hi'] at h3
          exact hqa h3.symm
        · rfl
      · rintro _ rfl
        exact ⟨hA.right_mem, h2.right_mem⟩
    have hl : IsLineWithEnds (A ∪ B₂) a q := hA.union h2.symm hsub
    have hC : a ∉ B₂ := fun h => by
      have h3 : a ∈ B₁ ∩ B₂ := ⟨h1.left_mem, h⟩
      rw [hi'] at h3
      exact hqa h3.symm
    refine ⟨A ∪ B₂, B₁, hl, h1, ?_, ?_, ?_, ?_⟩
    · rw [union_assoc, union_comm B₂, hu]
    · apply subset_antisymm
      · rintro z ⟨h3 | h3, hz⟩
        · rcases (hAB ▸ ⟨h3, hB₁ hz⟩ : z ∈ ({a, x} : Set S)) with rfl | rfl
          · exact .inl rfl
          · exfalso
            have h4 : z ∈ B₁ ∩ B₂ := ⟨hz, h2.right_mem⟩
            rw [hi'] at h4
            exact hqx h4.symm
        · exact .inr (hi' ▸ ⟨hz, h3⟩)
      · rintro z (rfl | rfl)
        · exact ⟨.inl hA.left_mem, h1.left_mem⟩
        · exact ⟨.inr h2.left_mem, h1.right_mem⟩
    · have h3 : (A ∪ B₂) \ A ⊆ B₂ := fun z hz => hz.1.resolve_left hz.2
      exact fun h => hC (h2.isCompact.isClosed.closure_subset_iff.mpr h3 h)
    · have h3 : B₁ \ B = ∅ := Set.sdiff_eq_empty.mpr hB₁
      rw [h3, closure_empty]
      exact notMem_empty _
  by_cases hqx : q = x
  · subst hqx
    exact ⟨A₁, A₂, h₁, h₂, rfl, hi, by simp, by simp⟩
  rcases hq with h | h
  · obtain ⟨P₁, P₂, h1, h2, h3, h4, h5, h6⟩ := hstep h₂ h₁ (by rw [inter_comm]; exact hi) h hqx
    exact ⟨P₂, P₁, h2, h1, by rw [union_comm, h3, union_comm], by rw [inter_comm, h4], h6, h5⟩
  · exact hstep h₁ h₂ hi h hqx

/-- If three lines join two points and the union of any two bounds a disc that misses the third
line, then the discs cover the surface. -/
theorem theta_cover [ConnectedSpace S] (hS : IsSurface S) {P₁ P₂ P₃ Δ₁ Δ₂ Δ₃ : Set S} {a q : S}
  (h₁ : IsLineWithEnds P₁ a q) (h₂ : IsLineWithEnds P₂ a q) (h₃ : IsLineWithEnds P₃ a q)
    (h₁₂ : P₁ ∩ P₂ = {a, q}) (h₂₃ : P₂ ∩ P₃ = {a, q}) (hd₃ : IsClosedDisc Δ₃)
      (hd₁ : IsClosedDisc Δ₁) (hd₂ : IsClosedDisc Δ₂) (hb₃ : discBd Δ₃ = P₁ ∪ P₂)
      (hb₁ : discBd Δ₁ = P₂ ∪ P₃) (hb₂ : discBd Δ₂ = P₁ ∪ P₃)
    (hn₃ : Disjoint (P₃ \ {a, q}) Δ₃) (hn₁ : Disjoint (P₁ \ {a, q}) Δ₁) (hn₂ : Disjoint
      (P₂ \ {a, q}) Δ₂) : Δ₃ ∪ Δ₁ ∪ Δ₂ = univ := by
  have hman := hS.2.2
  have hinner : ∀ {P : Set S} , IsLineWithEnds P a q → ∃ z ∈ P, z ≠ a ∧ z ≠ q := fun hP => by
    obtain ⟨z, hz, h1, h2, -⟩ := Painting.exists_inner hP (finite_empty (α := S))
    exact ⟨z, hz, h1, h2⟩
  have hint : Disjoint (discInt Δ₁) (P₁ ∪ P₂) := by
    refine disjoint_left.mpr fun x hx hm => ?_
    rcases hm with h | h
    · by_cases hx' : x ∈ ({a, q} : Set S)
      · apply hx.2
        rw [hb₁]
        rcases hx' with rfl | rfl
        · exact .inl h₂.left_mem
        · exact .inl h₂.right_mem
      · exact disjoint_left.mp hn₁ ⟨h, hx'⟩ hx.1
    · exact hx.2 (hb₁ ▸ .inl h)
  have hdj : Disjoint (discInt Δ₁) Δ₃ := by
    rcases hd₃.side hman hd₁.isPreconnected_discInt (by rw [hb₃]; exact hint) with h | h
    · exfalso
      obtain ⟨z, hz, h1, h2⟩ := hinner h₃
      have h4 : z ∈ Δ₃ := closure_minimal (h.trans (discInt_subset _)) hd₃.isClosed
        (hd₁.subset_closure_discInt (discBd_subset _ (hb₁ ▸ .inr hz)))
      exact disjoint_left.mp hn₃ ⟨hz, by rintro (e | e); exacts [h1 e, h2 e]⟩ h4
    · exact h
  have hin : Δ₃ ∩ Δ₁ = P₂ := by
    apply subset_antisymm
    · rintro x ⟨hx, hx'⟩
      have hb : x ∈ discBd Δ₁ := by
        by_contra hn
        exact disjoint_left.mp hdj ⟨hx', hn⟩ hx
      rw [hb₁] at hb
      rcases hb with h | h
      · exact h
      · by_contra hn
        have hne : x ∉ ({a, q} : Set S) := by
          rintro (rfl | rfl)
          · exact hn h₂.left_mem
          · exact hn h₂.right_mem
        exact disjoint_left.mp hn₃ ⟨h, hne⟩ hx
    · exact fun x hx => ⟨discBd_subset _ (hb₃ ▸ .inr hx), discBd_subset _ (hb₁ ▸ .inl hx)⟩
  obtain ⟨hE, hEb⟩ := disc_union _ _ _ _ _ hd₃ hd₁ h₂ hin (hb₃ ▸ subset_union_right)
    (hb₁ ▸ subset_union_left)
  have hEb' : discBd (Δ₃ ∪ Δ₁) = discBd Δ₂ := by
    rw [hEb, hb₃, hb₁, hb₂]
    ext x
    constructor
    · rintro ⟨(h | h) | (h | h), hn⟩
      · exact .inl h
      · have h7 : x ∈ ({a, q} : Set S) := by
          by_contra h7
          exact hn ⟨h, h7⟩
        rcases h7 with rfl | rfl
        · exact .inl h₁.left_mem
        · exact .inl h₁.right_mem
      · have h7 : x ∈ ({a, q} : Set S) := by
          by_contra h7
          exact hn ⟨h, h7⟩
        rcases h7 with rfl | rfl
        · exact .inl h₁.left_mem
        · exact .inl h₁.right_mem
      · exact .inr h
    · rintro (h | h)
      · refine ⟨.inl (.inl h), fun hm => hm.2 ?_⟩
        have h3 : x ∈ P₁ ∩ P₂ := ⟨h, hm.1⟩
        rwa [h₁₂] at h3
      · refine ⟨.inr (.inr h), fun hm => hm.2 ?_⟩
        have h3 : x ∈ P₂ ∩ P₃ := ⟨hm.1, h⟩
        rwa [h₂₃] at h3
  rcases two_discs hS hE hd₂ hEb' with he | ⟨hcov, -⟩
  · exfalso
    obtain ⟨z, hz, h1, h2⟩ := hinner h₂
    have h4 : z ∈ Δ₂ := he ▸ .inl (discBd_subset _ (hb₃ ▸ .inr hz))
    exact disjoint_left.mp hn₂ ⟨hz, by rintro (e | e); exacts [h1 e, h2 e]⟩ h4
  · exact hcov

/-- A line that starts inside a strip near its end is off a disc whose boundary stays off the strip
near this end, if the side of the strip is off the disc. -/
theorem third_off {St L P Δ F : Set S} {a b q : S} (hman : ∀ x : S, IsManifoldPoint x)
  (hSt : IsClosedDisc St) (hL : IsLineWithEnds L a b) (hLb : L ⊆ discBd St)
  (hΔ : IsClosedDisc Δ) (hb : discBd Δ = F)
    (hLΔ : ∀ x ∈ L, x ≠ a → x ∉ Δ) (hP : IsLineWithEnds P a q) (hPF : Disjoint (P \ {a, q}) F)
      (hgerm : a ∉ closure (P \ St)) (hFa : a ∉ closure ((F ∩ St) \ {a})) :
    Disjoint (P \ {a, q}) Δ := by
  have hV : (closure ((F ∩ St) \ {a}) ∪ closure (P \ St))ᶜ ∈ 𝓝 a :=
    (isClosed_closure.union isClosed_closure).isOpen_compl.mem_nhds (by
      rintro (h | h)
      · exact hFa h
      · exact hgerm h)
  obtain ⟨C, W, hC, hCD, hCV, haC, hW, hsub⟩ := disc_punct hSt (hLb hL.left_mem) hV
  have hCF : Disjoint C (discBd Δ) := by
    rw [hb]
    refine disjoint_left.mpr fun x hx hxF => ?_
    have hxa : x ≠ a := fun e => haC (e ▸ hx)
    exact hCV hx (.inl (subset_closure ⟨⟨hxF, hCD hx⟩, hxa⟩))
  have hCΔ : Disjoint C Δ := by
    rcases hΔ.side hman hC hCF with h | h
    · exfalso
      have hcl : a ∈ closure (L \ {a, b}) := hL.subset_closure_diff hL.left_mem
      obtain ⟨z, hzW, hz⟩ := mem_closure_iff_nhds.mp hcl _ hW
      have hza : z ≠ a := fun e => hz.2 (.inl e)
      have hzC := hsub ⟨⟨discBd_subset _ (hLb hz.1), hzW⟩, hza⟩
      exact hLΔ z hz.1 hza (h hzC).1
    · exact h
  have hcl : a ∈ closure (P \ {a, q}) := hP.subset_closure_diff hP.left_mem
  obtain ⟨z, hzW, hz⟩ := mem_closure_iff_nhds.mp hcl _ (Filter.inter_mem hW hV)
  have hzSt : z ∈ St := by
    by_contra hn
    exact hzW.2 (.inr (subset_closure ⟨hz.1, hn⟩))
  have hza : z ≠ a := fun e => hz.2 (.inl e)
  have hzC := hsub ⟨⟨hzSt, hzW.1⟩, hza⟩
  have hpart : IsPreconnected (P \ {a, q}) := hP.isPreconnected_diff
  rcases hΔ.side hman hpart (by rw [hb]; exact hPF) with h | h
  · exact absurd (h hz).1 (disjoint_left.mp hCΔ hzC)
  · exact h

end GraphMinor.GM17
