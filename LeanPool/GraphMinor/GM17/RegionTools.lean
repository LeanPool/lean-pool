/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM17.Strip
public import LeanPool.GraphMinor.GM17.ReplaceDisc
public import LeanPool.GraphMinor.Surface.VertexLink
public import LeanPool.GraphMinor.Surface.Dissection

/-!
# Tools for regions of a surface

Three facts about surfaces that the study of regions of a painting uses. An open set with finite
frontier in a connected surface is the whole surface without
that frontier (`eq_compl_of_frontier_finite`). Just outside a disc, near a point of its boundary, a
surface looks like a connected piece (`exists_outer`). Two closed
discs in a connected closed surface with the same boundary are equal or cover the surface
(`two_discs`).
-/

@[expose] public section

namespace GraphMinor.GM17

open Set Topology Metric Filter GraphMinor.Surface

/-- An open set of a connected surface whose frontier is finite is everything off its frontier. -/
theorem eq_compl_of_frontier_finite {S : Type} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
  (hman : ∀ x : S, IsManifoldPoint x) {W A : Set S} (hW : IsOpen W) (hne : W.Nonempty)
    (hA : A.Finite) (hcl : closure W ⊆ W ∪ A) : Aᶜ ⊆ W := by
  classical
  have hN : ∀ a : S, ∃ N, IsOpen N ∧ a ∈ N ∧ N ∩ A ⊆ {a} ∧ IsPreconnected (N \ {a}) := fun a => by
    have h1 : IsOpen (A \ {a})ᶜ := (hA.subset sdiff_subset).isClosed.isOpen_compl
    obtain ⟨N, hN, hmem, hs, hp⟩ := (hman a).exists_punctured h1 (fun h => h.2 rfl)
    refine ⟨N, hN, hmem, fun y hy => ?_, hp⟩
    by_contra hne'
    exact hs hy.1 ⟨hy.2, hne'⟩
  choose N hNo hNm hNA hNp using hN
  have hsub : ∀ a, (N a \ {a}).Nonempty → ((N a \ {a}) ∩ W).Nonempty → N a \ {a} ⊆ W := fun a _ hm
    => by
    have hcov : N a \ {a} ⊆ W ∪ (closure W)ᶜ := fun y hy => by
      by_cases hc : y ∈ closure W
      · rcases hcl hc with h | h
        · exact .inl h
        · exact absurd (hNA a ⟨hy.1, h⟩) hy.2
      · exact .inr hc
    have h1 := (hNp a).subset_left_of_subset_union hW isClosed_closure.isOpen_compl
      (disjoint_left.mpr fun x hx hx' => hx' (subset_closure hx)) hcov
    exact h1 hm
  let W' : Set S := W ∪ {a | a ∈ A ∧ ((N a \ {a}) ∩ W).Nonempty}
  have hop : IsOpen W' := by
    rw [isOpen_iff_mem_nhds]
    rintro x (h | ⟨hxA, hm⟩)
    · exact Filter.mem_of_superset (hW.mem_nhds h) subset_union_left
    · refine Filter.mem_of_superset ((hNo x).mem_nhds (hNm x)) fun y hy => ?_
      by_cases hyx : y = x
      · exact hyx ▸ .inr ⟨hxA, hm⟩
      · exact .inl (hsub x (hm.mono inter_subset_left) hm ⟨hy, hyx⟩)
  have hcl' : IsClosed W' := by
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro x hx
    have hxW : x ∉ W := fun h => hx (.inl h)
    by_cases hxA : x ∈ A
    · have hem : (N x \ {x}) ∩ W = ∅ := by
        by_contra hne'
        exact hx (.inr ⟨hxA, nonempty_iff_ne_empty.mpr hne'⟩)
      refine Filter.mem_of_superset ((hNo x).mem_nhds (hNm x)) fun y hy => ?_
      by_cases hyx : y = x
      · exact hyx ▸ hx
      · have hyA : y ∉ A := fun h => hyx (hNA x ⟨hy, h⟩)
        have hyW : y ∉ W := fun h => (eq_empty_iff_forall_notMem.mp hem y) ⟨⟨hy, hyx⟩, h⟩
        rintro (h | h)
        · exact hyW h
        · exact hyA h.1
    · have hxc : x ∉ closure W := fun h => (hcl h).elim hxW hxA
      have h1 : IsOpen ((closure W)ᶜ ∩ Aᶜ) := isClosed_closure.isOpen_compl.inter
        hA.isClosed.isOpen_compl
      refine Filter.mem_of_superset (h1.mem_nhds ⟨hxc, hxA⟩) fun y hy => ?_
      rintro (h | h)
      · exact hy.1 (subset_closure h)
      · exact hy.2 h.1
  have huniv : W' = univ := IsClopen.eq_univ ⟨hcl', hop⟩ (hne.mono subset_union_left)
  intro x hx
  rcases (huniv ▸ mem_univ x : x ∈ W') with h | h
  · exact h
  · exact absurd h.1 hx

/-- A connected piece just outside the unit disc, near a point of the unit circle. -/
theorem exists_sector {w : ℂ} (hw : ‖w‖ = 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ A : Set ℂ, IsPreconnected A ∧ A ⊆ ball w ε ∧ (∀ z ∈ A, 1 < ‖z‖) ∧ ∀ᶠ z in 𝓝 w, 1 < ‖z‖
      → z ∈ A := by
  have hw0 : w ≠ 0 := fun h => by simp [h] at hw
  have hc : Continuous fun ζ : ℂ => w * Complex.exp ζ := by fun_prop
  have h0 : (fun ζ : ℂ => w * Complex.exp ζ) 0 = w := by simp
  obtain ⟨δ, hδ, hball⟩ := Metric.continuous_iff.mp hc 0 ε hε
  let Q : Set ℂ := ball 0 δ ∩ {ζ | 0 < ζ.re}
  have hQ : Convex ℝ Q := (convex_ball _ _).inter (convex_halfSpace_gt Complex.reLm.isLinear 0)
  refine ⟨(fun ζ => w * Complex.exp ζ) '' Q, hQ.isPreconnected.image _ hc.continuousOn, ?_, ?_, ?_⟩
  · rintro _ ⟨ζ, hζ, rfl⟩
    have h1 := hball ζ hζ.1
    simp only [Complex.exp_zero, mul_one] at h1
    exact h1
  · rintro _ ⟨ζ, hζ, rfl⟩
    rw [norm_mul, hw, one_mul, Complex.norm_exp]
    exact Real.one_lt_exp_iff.mpr hζ.2
  · have hl : ContinuousAt (fun z : ℂ => Complex.log (z / w)) w := by
      refine ContinuousAt.clog (by fun_prop) ?_
      rw [div_self hw0]
      exact Complex.ofReal_mem_slitPlane.mpr one_pos
    have h1 : Complex.log (w / w) = 0 := by
      rw [div_self hw0, Complex.log_one]
    have h2 := hl.eventually (ball_mem_nhds (Complex.log (w / w)) hδ)
    filter_upwards [h2, isOpen_ne.mem_nhds (show w ≠ 0 from hw0)] with z hz hz0 hn
    rw [h1] at hz
    refine ⟨Complex.log (z / w), ⟨hz, ?_⟩, ?_⟩
    · change 0 < (Complex.log (z / w)).re
      rw [Complex.log_re, norm_div, hw, div_one]
      exact Real.log_pos hn
    · change w * Complex.exp (Complex.log (z / w)) = z
      rw [Complex.exp_log (div_ne_zero hz0 hw0)]
      field_simp

/-- Near a point of the boundary of a disc, the outside of the disc is a connected piece, as small
as we like. -/
theorem exists_outer {T : Type} [TopologicalSpace T] (hT : IsSurface T) {B V : Set T} {a : T}
    (hB : IsClosedDisc B) (hint : ∀ x ∈ discBd B, IsInteriorPoint x)
    (ha : a ∈ discBd B) (hV : V ∈ 𝓝 a) :
    ∃ P Q, IsPreconnected P ∧ P ⊆ V ∧ Disjoint P B ∧ IsOpen Q ∧ a ∈ Q ∧ Q ⊆ V ∧ Q \ B ⊆ P := by
  have ht2 : T2Space T := hT.2.1
  have hman := hT.2.2
  obtain ⟨Δ', hΔ', hin, -⟩ := exists_disc_around hman hB hint isOpen_univ (subset_univ _)
  obtain ⟨p⟩ := hB.isOArc_discBd
  obtain ⟨c, c', hcc, hc'c, hmc, hmc', hl, hr, hcB, hcb, hcp⟩ := exists_disc_collar hB hΔ' hin p
  obtain ⟨w₀, rfl⟩ : ∃ w₀ : Circle, (p w₀).1 = a := by
    obtain ⟨w, hw⟩ := p.surjective ⟨a, ha⟩
    exact ⟨w, congrArg Subtype.val hw⟩
  have hw₀ : ‖(w₀ : ℂ)‖ = 1 := Circle.norm_coe w₀
  have hcw : c w₀ = (p w₀).1 := hcp w₀
  have h2 : (w₀ : ℂ) ∈ ball (0 : ℂ) 2 := by simp [hw₀]
  have hcat : ContinuousAt c w₀ := hcc.continuousAt (closedBall_mem_nhds_of_mem h2)
  have hV' : c ⁻¹' V ∈ 𝓝 (w₀ : ℂ) := hcat (by rw [hcw]; exact hV)
  obtain ⟨ε, hε, hεV⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem hV' (isOpen_ball.mem_nhds h2))
  obtain ⟨A, hAp, hAb, hAn, hAe⟩ := exists_sector hw₀ hε
  obtain ⟨ε', hε', hA'⟩ := Metric.eventually_nhds_iff_ball.mp hAe
  have hAs : A ⊆ ball 0 2 := fun z hz => (hεV (hAb hz)).2
  have hclosed2 : ball (0 : ℂ) 2 ⊆ closedBall 0 2 := ball_subset_closedBall
  have hsph : c '' sphere 0 2 = discBd Δ' := hcb
  have hopen : IsOpen (discInt Δ') := hΔ'.isOpen_discInt hman
  have hintΔ : ∀ z ∈ ball (0 : ℂ) 2, c z ∈ discInt Δ' := fun z hz => by
    refine ⟨hmc (hclosed2 hz), fun hb => ?_⟩
    rw [← hsph] at hb
    obtain ⟨z', hz', he⟩ := hb
    have h3 : z' = z := by
      rw [← hl (sphere_subset_closedBall hz'), he, hl (hclosed2 hz)]
    rw [h3, mem_sphere_zero_iff_norm] at hz'
    rw [mem_ball_zero_iff] at hz
    linarith
  have hc'a : c' (c w₀) = w₀ := hl (hclosed2 h2)
  let Q : Set T := discInt Δ' ∩ c' ⁻¹' (ball w₀ (min ε ε'))
  have hmemΔ : ∀ {x}, x ∈ discInt Δ' → x ∈ Δ' := fun hx => hx.1
  have hQo : IsOpen Q := by
    have h3 : ContinuousOn c' (discInt Δ') := hc'c.mono fun x hx => hx.1
    exact h3.isOpen_inter_preimage hopen isOpen_ball
  have hcyQ : ∀ {y}, y ∈ Q → c (c' y) = y := fun {y} hy => hr hy.1.1
  have hQb : ∀ {y}, y ∈ Q → c' y ∈ ball (w₀ : ℂ) (min ε ε') := fun hy => hy.2
  refine ⟨c '' A, Q, hAp.image _ (hcc.mono (hAs.trans hclosed2)), ?_, ?_, hQo, ?_, ?_, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact (hεV (hAb hz)).1
  · refine disjoint_left.mpr ?_
    rintro _ ⟨z, hz, rfl⟩ hm
    rw [← hcB] at hm
    obtain ⟨z', hz', he⟩ := hm
    have h3 : z' = z := by
      rw [← hl (closedBall_subset_closedBall (by norm_num) hz'), he, hl (hclosed2 (hAs hz))]
    rw [h3, mem_closedBall_zero_iff] at hz'
    linarith [hAn z hz]
  · refine ⟨by rw [← hcw]; exact hintΔ _ h2, ?_⟩
    change c' (p w₀).1 ∈ ball (w₀ : ℂ) (min ε ε')
    rw [← hcw, hc'a]
    exact mem_ball_self (lt_min hε hε')
  · intro y hy
    have h3 := hcyQ hy
    have h4 := hQb hy
    rw [← h3]
    exact (hεV (ball_subset_ball (min_le_left _ _) h4)).1
  · rintro y ⟨hy, hyB⟩
    have h3 := hcyQ hy
    have h4 := hQb hy
    refine ⟨c' y, ?_, h3⟩
    refine hA' _ (ball_subset_ball (min_le_right _ _) h4) ?_
    by_contra hn
    exact hyB (h3 ▸ hcB ▸ mem_image_of_mem _ (mem_closedBall_zero_iff.mpr (not_lt.mp hn)))

/-- Near a point of the boundary of a disc in the closure of an open set off the disc, there are
frontier points of that set off any line of the boundary with that end. -/
theorem frontier_near {T : Type} [TopologicalSpace T] (hT : IsSurface T) {B W L : Set T} {a b : T}
    (hB : IsClosedDisc B) (hint : ∀ x ∈ discBd B, IsInteriorPoint x)
    (hW : IsOpen W) (hWB : Disjoint W B)
    (ha : a ∈ closure W) (hL : IsLineWithEnds L a b) (hLB : L ⊆ discBd B) : a ∈ closure
      (frontier W \ L) := by
  have ht2 : T2Space T := hT.2.1
  by_contra hn
  have hV : (closure (frontier W \ L))ᶜ ∈ 𝓝 a := isClosed_closure.isOpen_compl.mem_nhds hn
  have hab : a ∈ discBd B := hLB hL.left_mem
  obtain ⟨P, Q, hP, hPV, hPB, hQ, haQ, hQV, hQB⟩ := exists_outer hT hB hint hab hV
  have hmeet : (P ∩ W).Nonempty := by
    obtain ⟨z, hzQ, hzW⟩ := mem_closure_iff.mp ha Q hQ haQ
    exact ⟨z, hQB ⟨hzQ, disjoint_left.mp hWB hzW⟩, hzW⟩
  have hPW : P ⊆ W := by
    refine hP.subset_left_of_subset_union hW isClosed_closure.isOpen_compl
      (disjoint_left.mpr fun x hx hx' => hx' (subset_closure hx)) (fun y hy => ?_) hmeet
    by_contra hcon
    have h1 : y ∉ W := fun h => hcon (.inl h)
    have h2 : y ∈ closure W := by
      by_contra h
      exact hcon (.inr h)
    have hyf : y ∈ frontier W := by
      rw [hW.frontier_eq]
      exact ⟨h2, h1⟩
    exact hPV hy (subset_closure ⟨hyf, fun hyL => disjoint_left.mp hPB hy (discBd_subset B
      (hLB hyL))⟩)
  obtain ⟨L', hL', hun, hin⟩ := oarc_split hB.isOArc_discBd hL hLB
  have h3 : a ∈ closure (L' \ {a, b}) := hL'.subset_closure_diff hL'.left_mem
  obtain ⟨y, hyQ, hyL'⟩ := mem_closure_iff.mp h3 Q hQ haQ
  have hyb : y ∈ discBd B := hun ▸ Or.inr hyL'.1
  have hyL : y ∉ L := fun h => hyL'.2 (hin ▸ ⟨h, hyL'.1⟩)
  have hycl : y ∈ closure P := by
    have h4 : y ∈ closure Bᶜ := mem_closure_compl hyb (hint y hyb)
    refine closure_mono hQB ?_
    refine mem_closure_iff.mpr fun O hO hyO => ?_
    obtain ⟨z, hz, hzB⟩ := mem_closure_iff.mp h4 (O ∩ Q) (hO.inter hQ) ⟨hyO, hyQ⟩
    exact ⟨z, hz.1, hz.2, hzB⟩
  have hyW : y ∉ W := fun h => disjoint_left.mp hWB h (discBd_subset B hyb)
  have hyf : y ∈ frontier W := by
    rw [hW.frontier_eq]
    exact ⟨closure_mono hPW hycl, hyW⟩
  exact hQV hyQ (subset_closure ⟨hyf, hyL⟩)

/-- Two closed discs with the same boundary in a connected closed surface are equal, or else they
cover the surface and meet exactly in the boundary. -/
theorem two_discs_closed {T : Type} [TopologicalSpace T] [ConnectedSpace T]
    (hT : IsClosedSurface T) {Δ Δ' : Set T} (h : IsClosedDisc Δ) (h' : IsClosedDisc Δ')
    (hb : discBd Δ = discBd Δ') :
    Δ = Δ' ∨ (Δ ∪ Δ' = univ ∧ Δ ∩ Δ' = discBd Δ) := by
  have ht2 : T2Space T := hT.2.1
  have hTs : IsSurface T := ⟨hT.1, hT.2.1, fun x => (hT.2.2 x).isManifoldPoint⟩
  have hman := hTs.2.2
  by_cases hm : (discInt Δ ∩ Δ').Nonempty
  · obtain ⟨z, hz, hz'⟩ := hm
    exact .inl (eq_of_int_meet hman (G := discBd Δ) h h' subset_rfl hb.ge
      (disjoint_left.mpr fun x hx hx' => hx.2 hx')
      (disjoint_left.mpr fun x hx hx' => hx.2 (hb ▸ hx')) hz hz')
  right
  have hd : Disjoint (discInt Δ) Δ' := disjoint_left.mpr fun x hx hx' => hm ⟨x, hx, hx'⟩
  constructor
  · refine IsClopen.eq_univ ⟨h.isClosed.union h'.isClosed, ?_⟩ ?_
    · rw [isOpen_iff_mem_nhds]
      intro x hx
      by_cases hxb : x ∈ discBd Δ
      · obtain ⟨P, Q, hP, -, hPB, hQ, hxQ, -, hQB⟩ :=
          exists_outer hTs h' (fun y _ => hT.2.2 y) (hb ▸ hxb) Filter.univ_mem
        have h1 : (P ∩ discInt Δ).Nonempty := by
          obtain ⟨z, hzQ, hzi⟩ := mem_closure_iff.mp (h.subset_closure_discInt
            (discBd_subset Δ hxb)) Q hQ hxQ
          exact ⟨z, hQB ⟨hzQ, disjoint_left.mp hd hzi⟩, hzi⟩
        have h2 : Disjoint P (discBd Δ) := by
          rw [hb]
          exact hPB.mono_right (discBd_subset Δ')
        rcases h.side hman hP h2 with h3 | h3
        · refine Filter.mem_of_superset (hQ.mem_nhds hxQ) fun y hy => ?_
          by_cases hyB : y ∈ Δ'
          · exact .inr hyB
          · exact .inl (h3 (hQB ⟨hy, hyB⟩)).1
        · obtain ⟨z, hz, hzi⟩ := h1
          exact absurd hzi.1 (disjoint_left.mp h3 hz)
      · rcases hx with hx | hx
        · exact Filter.mem_of_superset ((h.isOpen_discInt hman).mem_nhds ⟨hx,
            hxb⟩) fun y hy => .inl hy.1
        · exact Filter.mem_of_superset ((h'.isOpen_discInt hman).mem_nhds ⟨hx,
            hb ▸ hxb⟩) fun y hy => .inr hy.1
    · obtain ⟨φ⟩ := h.isOArc_discBd
      exact ⟨_, .inl (discBd_subset Δ (φ 1).2)⟩
  · apply subset_antisymm
    · rintro x ⟨hx, hx'⟩
      by_contra hn
      exact disjoint_left.mp hd ⟨hx, hn⟩ hx'
    · exact fun x hx => ⟨discBd_subset Δ hx, discBd_subset Δ' (hb ▸ hx)⟩

/-- A line with two marked ends and finitely many more marked points is a finite union of lines
between consecutive marks. -/
theorem exists_gaps_line {X : Type} [TopologicalSpace X] [T2Space X] (n : ℕ) : ∀ {L : Set X} {u v :
  X} {A : Set X}, IsLineWithEnds L u v → A.Finite → A ⊆ L → u ∈ A → v ∈ A → A.ncard = n →
    ∃ 𝓕 : Set (Set X), 𝓕.Finite ∧ (∀ F ∈ 𝓕, ∃ a ∈ A, ∃ b ∈ A, IsLineWithEnds F a b ∧ F ⊆ L ∧ F ∩ A
      = {a, b}) ∧ ⋃₀ 𝓕 = L := by
  classical
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro L u v A hL hA hAL hu hv hn
    by_cases hmore : ∃ z ∈ A, z ≠ u ∧ z ≠ v
    · obtain ⟨z, hz, hzu, hzv⟩ := hmore
      obtain ⟨L₁, L₂, hL₁, hL₂, hun, hin⟩ := hL.split (hAL hz) hzu hzv
      have hsub : ∀ {Q : Set X} {x}, x ∈ Q → (∃ y ∈ A, y ∉ Q) → (A ∩ Q).ncard < n := fun {Q x} _ hy
        => by
        rw [← hn]
        obtain ⟨y, hy, hyQ⟩ := hy
        exact Set.ncard_lt_ncard ⟨inter_subset_left, fun h => hyQ (h hy).2⟩ hA
      have hvL₁ : v ∉ L₁ := fun h => by
        have h1 : v ∈ L₁ ∩ L₂ := ⟨h, hL₂.right_mem⟩
        rw [hin] at h1
        exact hzv h1.symm
      have huL₂ : u ∉ L₂ := fun h => by
        have h1 : u ∈ L₁ ∩ L₂ := ⟨hL₁.left_mem, h⟩
        rw [hin] at h1
        exact hzu h1.symm
      obtain ⟨𝓕₁, hf₁, h₁, hu₁⟩ := ih _ (hsub hL₁.left_mem ⟨v, hv, hvL₁⟩) hL₁
        (hA.subset inter_subset_left) inter_subset_right ⟨hu, hL₁.left_mem⟩ ⟨hz, hL₁.right_mem⟩ rfl
      obtain ⟨𝓕₂, hf₂, h₂, hu₂⟩ := ih _ (hsub hL₂.left_mem ⟨u, hu, huL₂⟩) hL₂
        (hA.subset inter_subset_left) inter_subset_right ⟨hz, hL₂.left_mem⟩ ⟨hv, hL₂.right_mem⟩ rfl
      refine ⟨𝓕₁ ∪ 𝓕₂, hf₁.union hf₂, ?_, by rw [sUnion_union, hu₁, hu₂, hun]⟩
      have hstep : ∀ {Q : Set X}, Q ⊆ L → ∀ {F a b}, (∃ a' ∈ A ∩ Q, ∃ b' ∈ A ∩ Q, a' = a ∧ b' = b
        ∧ IsLineWithEnds F a b ∧ F ⊆ Q ∧ F ∩ (A ∩ Q) = {a, b}) →
        a ∈ A ∧ b ∈ A ∧ IsLineWithEnds F a b ∧ F ⊆ L ∧ F ∩ A = {a, b} := by
        rintro Q hQ F a b ⟨a', ha', b', hb', rfl, rfl, hF, hFQ, hFi⟩
        refine ⟨ha'.1, hb'.1, hF, hFQ.trans hQ, ?_⟩
        rw [← hFi]
        ext y
        exact ⟨fun h => ⟨h.1, h.2, hFQ h.1⟩, fun h => ⟨h.1, h.2.1⟩⟩
      rintro F (hF | hF)
      · obtain ⟨a, ha, b, hb, h1, h2, h3⟩ := h₁ F hF
        obtain ⟨h4, h5, h6⟩ := hstep (hun ▸ subset_union_left) ⟨a, ha, b, hb, rfl, rfl, h1, h2, h3⟩
        exact ⟨a, h4, b, h5, h6⟩
      · obtain ⟨a, ha, b, hb, h1, h2, h3⟩ := h₂ F hF
        obtain ⟨h4, h5, h6⟩ := hstep (hun ▸ subset_union_right) ⟨a, ha, b, hb, rfl, rfl, h1, h2, h3⟩
        exact ⟨a, h4, b, h5, h6⟩
    · push Not at hmore
      refine ⟨{L}, finite_singleton _, ?_, sUnion_singleton _⟩
      rintro F rfl
      refine ⟨u, hu, v, hv, hL, subset_rfl, ?_⟩
      apply subset_antisymm
      · rintro x ⟨-, hx⟩
        by_cases hxu : x = u
        · exact .inl hxu
        · exact .inr (hmore x hx hxu)
      · rintro x (rfl | rfl)
        · exact ⟨hL.left_mem, hu⟩
        · exact ⟨hL.right_mem, hv⟩

/-- An `O`-arc with at least two marked points, finitely many, is a finite union of lines between
consecutive marks. -/
theorem exists_gaps_oarc {X : Type} [TopologicalSpace X] [T2Space X] {O A : Set X} {x y : X}
  (hO : IsOArc O) (hA : A.Finite) (hAO : A ⊆ O) (hx : x ∈ A) (hy : y ∈ A) (hxy : x ≠ y) :
    ∃ 𝓕 : Set (Set X), 𝓕.Finite ∧ (∀ F ∈ 𝓕, ∃ a ∈ A, ∃ b ∈ A, IsLineWithEnds F a b ∧ F ⊆ O ∧ F ∩ A
      = {a, b}) ∧ ⋃₀ 𝓕 = O := by
  obtain ⟨B₁, B₂, hB₁, hB₂, hun, hin⟩ := hO.lines (hAO hx) (hAO hy) hxy
  have hpart : ∀ {B : Set X}, IsLineWithEnds B x y → B ⊆ O → ∃ 𝓕 : Set (Set X), 𝓕.Finite ∧
    (∀ F ∈ 𝓕, ∃ a ∈ A, ∃ b ∈ A, IsLineWithEnds F a b ∧ F ⊆ O ∧ F ∩ A = {a, b} ∧ F ⊆ B) ∧
      ⋃₀ 𝓕 = B := by
    intro B hB hBO
    obtain ⟨𝓕, hf, h, hu⟩ := exists_gaps_line _ hB (hA.subset (inter_subset_left (t
      := B))) inter_subset_right ⟨hx, hB.left_mem⟩ ⟨hy, hB.right_mem⟩ rfl
    refine ⟨𝓕, hf, fun F hF => ?_, hu⟩
    obtain ⟨a, ha, b, hb, h1, h2, h3⟩ := h F hF
    refine ⟨a, ha.1, b, hb.1, h1, h2.trans hBO, ?_, h2⟩
    rw [← h3]
    ext z
    exact ⟨fun h => ⟨h.1, h.2, h2 h.1⟩, fun h => ⟨h.1, h.2.1⟩⟩
  obtain ⟨𝓕₁, hf₁, h₁, hu₁⟩ := hpart hB₁ (hun ▸ subset_union_left)
  obtain ⟨𝓕₂, hf₂, h₂, hu₂⟩ := hpart hB₂ (hun ▸ subset_union_right)
  refine ⟨𝓕₁ ∪ 𝓕₂, hf₁.union hf₂, ?_, by rw [sUnion_union, hu₁, hu₂, hun]⟩
  rintro F (hF | hF)
  · obtain ⟨a, ha, b, hb, h1, h2, h3, -⟩ := h₁ F hF
    exact ⟨a, ha, b, hb, h1, h2, h3⟩
  · obtain ⟨a, ha, b, hb, h1, h2, h3, -⟩ := h₂ F hF
    exact ⟨a, ha, b, hb, h1, h2, h3⟩

end GraphMinor.GM17
