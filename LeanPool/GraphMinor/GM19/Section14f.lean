/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section14e

/-!
# Graph Minors XIX, Section 14: a chord made of two spokes

Two spokes that meet cut `W` in two discs. The hub lies on one side, so each spoke from the other
side must cross the chord, and then
it runs along one of the two spokes up to the point where they meet (`chord_side`). This is why the
spokes with the same inner end
leave `bd(W)` along one arc.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology Metric GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11

universe w

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
  {α : Type w} {cap : IsCappedSurface S Shat} {χ : ColourScheme S α}

omit [T2Space Shat] in
theorem GraphWalk.simple_append_meet {G : Drawing Shat} {a x b : Shat} {P : GraphWalk G.toGraph a
  x} {Q : GraphWalk G.toGraph x b}
    (h : (P.append Q).IsSimple) {y : Shat} (h₁ : y ∈ P.support) (h₂ : y ∈ Q.support) : y = x := by
  have hn : (P.append Q).support.Nodup := h
  rw [GraphWalk.support_append] at hn
  cases Q with
  | nil _ =>
    simpa [GraphWalk.support] using h₂
  | cons hl t =>
    rw [GraphWalk.support_cons, List.mem_cons] at h₂
    rcases h₂ with h₂ | h₂
    · exact h₂
    · exact ((List.nodup_append.mp hn).2.2 _ h₁ _ (by simpa [GraphWalk.support_cons] using h₂)
        rfl).elim

omit [T2Space Shat] in
theorem GraphWalk.closed_vertexAt_inj {G : Drawing Shat} {u : Shat} (B : GraphWalk G.toGraph u u)
  (hs : B.IsSimpleClosed) {p q : ℕ} (hp : p ≤ B.length) (hq : q ≤ B.length)
    (h : GraphWalk.vertexAt B p = GraphWalk.vertexAt B q) : p = q ∨ (p = 0 ∧ q = B.length) ∨ (p
      = B.length ∧ q = 0) := by
  cases hB : B with
  | nil _ =>
    subst hB
    have hp0 : p = 0 := by simpa [GraphWalk.length] using hp
    have hq0 : q = 0 := by simpa [GraphWalk.length] using hq
    omega
  | cons hl t =>
    subst hB
    have ht : t.IsSimple := by
      have := hs.1
      rwa [GraphWalk.support_cons, List.tail_cons] at this
    have hlen := GraphWalk.length_cons' hl t
    have hu : u ∈ G.V := hl.2.1
    have hat := GraphWalk.vertexAt_length t hu
    rw [hlen] at hp hq ⊢
    cases p with
    | zero =>
      cases q with
      | zero => exact .inl rfl
      | succ q =>
        rw [GraphWalk.vertexAt_cons, GraphWalk.vertexAt_zero] at h
        have := GraphWalk.vertexAt_inj t ht (le_refl _) (Nat.le_of_succ_le_succ hq) (hat.trans h)
        omega
    | succ p =>
      cases q with
      | zero =>
        rw [GraphWalk.vertexAt_cons, GraphWalk.vertexAt_zero] at h
        have := GraphWalk.vertexAt_inj t ht (Nat.le_of_succ_le_succ hp) (le_refl _)
          (h.trans hat.symm)
        omega
      | succ q =>
        rw [GraphWalk.vertexAt_cons, GraphWalk.vertexAt_cons] at h
        have := GraphWalk.vertexAt_inj t ht (by omega) (by omega) h
        omega

omit [T2Space Shat] in
theorem GraphWalk.link_at {G : Drawing Shat} {a b : Shat} (K : GraphWalk G.toGraph a b) {p : ℕ}
  (hp : p < K.length) :
    ∃ e ∈ K.edges, G.toGraph.IsLink e (GraphWalk.vertexAt K p) (GraphWalk.vertexAt K (p + 1)) := by
  induction K generalizing p with
  | nil _ => simp [GraphWalk.length] at hp
  | cons hl t ih =>
    rw [GraphWalk.length_cons'] at hp
    cases p with
    | zero =>
      refine ⟨_, List.mem_cons_self .., ?_⟩
      rw [GraphWalk.vertexAt_cons, GraphWalk.vertexAt_zero, GraphWalk.vertexAt_zero]
      exact hl
    | succ p =>
      obtain ⟨e, he, hl'⟩ := ih (p := p) (by omega)
      refine ⟨e, by rw [GraphWalk.edges_cons]; exact List.mem_cons_of_mem _ he, ?_⟩
      rwa [GraphWalk.vertexAt_cons, GraphWalk.vertexAt_cons]

omit [T2Space Shat] in
theorem GraphWalk.isSimple_of_vertexAt_inj {G : Drawing Shat} {a b : Shat}
  (K : GraphWalk G.toGraph a b) (h : ∀ p q, p ≤ K.length → q ≤ K.length → GraphWalk.vertexAt K p
    = GraphWalk.vertexAt K q → p = q) :
    K.IsSimple := by
  have hl := GraphWalk.length_support' K
  unfold GraphWalk.IsSimple
  rw [List.nodup_iff_injective_get]
  rintro ⟨p, hp⟩ ⟨q, hq⟩ he
  have hp' : p ≤ K.length := by omega
  have hq' : q ≤ K.length := by omega
  have := h p q hp' hq' (by
    rwa [GraphWalk.vertexAt_eq K hp' hp, GraphWalk.vertexAt_eq K hq' hq])
  exact Fin.ext this

omit [T2Space Shat] in
theorem GraphWalk.exists_seg_at {G : Drawing Shat} {a b : Shat} (K : GraphWalk G.toGraph a b)
  (p s : ℕ) (h : p + s ≤ K.length) :
    ∃ Y : GraphWalk G.toGraph (GraphWalk.vertexAt K p) (GraphWalk.vertexAt K (p + s)), Y.length = s
      ∧ (∀ t ≤ s, GraphWalk.vertexAt Y t = GraphWalk.vertexAt K (p + t)) ∧
      ∀ e ∈ Y.edges, e ∈ K.edges := by
  obtain ⟨P, Q, hPQ, hl⟩ := GraphWalk.exists_split_at K (p := p) (by omega)
  generalize hz : GraphWalk.vertexAt K p = z at P Q hPQ ⊢
  subst hl
  subst hPQ
  have hs : s ≤ Q.length := by
    rw [GraphWalk.length_append] at h
    omega
  rw [GraphWalk.vertexAt_append_right P Q hs]
  obtain ⟨Y, Z, hYZ, hYl⟩ := GraphWalk.exists_split_at Q hs
  refine ⟨Y, hYl, fun t ht ↦ ?_, fun e he ↦ ?_⟩
  · rw [GraphWalk.vertexAt_append_right P Q (by omega)]
    have := GraphWalk.vertexAt_append_left Y Z (t := t) (by omega)
    rw [← hYZ] at this
    exact this.symm
  · rw [GraphWalk.edges_append]
    refine List.mem_append_right _ ?_
    have h' : e ∈ (Y.append Z).edges := by
      rw [GraphWalk.edges_append]
      exact List.mem_append_left _ he
    rwa [← hYZ] at h'

/-- A cyclic word in which equal letters have one arc of that letter between them changes at most
once for each letter. -/
theorem cyclic_changes_injOn {L : Type*} (k : ℕ) (f : ℕ → L) (hper : f k = f 0)
    (harc : ∀ i j, i < j → j < k → f i = f j → (∀ l, i ≤ l → l ≤ j → f l = f i) ∨ ∀ l < k, (l ≤ i
      ∨ j ≤ l) → f l = f i) :
    InjOn f {i | i < k ∧ f i ≠ f (i + 1)} := by
  have key : ∀ i j, i < j → j < k → f i ≠ f (i + 1) → f j ≠ f (j + 1) → f i ≠ f j := by
    intro i j hij hj h₁ h₂ he
    rcases harc i j hij hj he with h' | h'
    · exact h₁ (h' (i + 1) (by omega) (by omega)).symm
    · by_cases hl : j + 1 = k
      · apply h₂
        rw [hl, hper, h' 0 (by omega) (.inl (by omega)), he]
      · apply h₂
        rw [h' (j + 1) (by omega) (.inr (by omega)), he]
  rintro i ⟨hi, hi'⟩ j ⟨hj, hj'⟩ he
  rcases lt_trichotomy i j with h | h | h
  · exact absurd he (key i j h hj hi' hj')
  · exact h
  · exact absurd he.symm (key j i h hi hj' hi')

namespace TangleDatum

variable {D : TangleDatum cap χ} {W : Set Shat} {H : Drawing Shat} {ρ : ℕ}

omit [T2Space S] in
/-- A spoke that meets the first part of another spoke runs along it to its end. -/
theorem IsSpokeWalk.passes {v v' m h h' x : Shat} {A : GraphWalk D.rad.G.toGraph v m} {T :
  GraphWalk D.rad.G.toGraph m h} {K : GraphWalk D.rad.G.toGraph v' h'}
    (h1 : D.IsSpokeWalk W H (A.append T)) (h2 : D.IsSpokeWalk W H K) (hx : x ∈ A.support)
      (hxK : x ∈ K.support) : m ∈ K.support := by
  obtain rfl := IsSpokeWalk.same_end h1 h2 ((GraphWalk.mem_support_append A T).mpr (.inl hx)) hxK
  obtain ⟨L, R, rfl⟩ := A.exists_append_of_mem hx
  obtain ⟨L', R', rfl⟩ := K.exists_append_of_mem hxK
  rw [GraphWalk.append_assoc'] at h1
  have := IsSpokeWalk.tail_after h1 h2
  subst this
  exact (GraphWalk.mem_support_append L' _).mpr (.inr ((GraphWalk.mem_support_append R T).mpr
    (.inr T.start_mem_support)))

omit [T2Space S] in
/-- The hub without one point `m` is connected, when `m` is not inside it. -/
theorem IsWheelHubOfRadius.hub_diff_preconnected (hW : D.IsWheelHubOfRadius W H ρ) {m : Shat}
  (hm : m ∈ hubSet D H → m ∈ H.U) : IsPreconnected (hubSet D H \ {m}) := by
  have : ConnectedSpace Shat := cap.connected
  rcases hW.hub_cases with ⟨z, -, -, hh⟩ | ⟨hH, hle, -, hh⟩
  · rw [hh]
    by_cases hzm : z = m
    · subst hzm
      simp [isPreconnected_empty]
    · rw [sdiff_singleton_eq_self (by simpa [eq_comm] using hzm)]
      exact isPreconnected_singleton
  · obtain ⟨-, -, -, hc, -⟩ := id hH
    have hrep := hW.rep_ge
    have hi := D.ins_spec hc (by omega)
    rw [hh] at hm ⊢
    have hbd := hi.2.2.2.1
    refine hi.2.2.1.isPreconnected_discInt.subset_closure ?_ ?_
    · refine fun a ha ↦ ⟨ha.1, ?_⟩
      rintro rfl
      exact ha.2 (hbd ▸ hm ha.1)
    · rw [closure_discInt hi.2.2.1]
      exact sdiff_subset

/-- **A chord made of two spokes.** One of the two discs has no hub in it, so each spoke from it
passes through the point `m`
where the two spokes meet. -/
theorem chord_side (hW : D.IsWheelHubOfRadius W H ρ) (hbdS : discBd W ⊆ cap.emb '' (univ \ bd S))
  (hin : ((W \ discBd W) ∩ (cap.emb '' D.Γ.V)).Nonempty)
    {v₁ v₂ m h : Shat} {A₁ : GraphWalk D.rad.G.toGraph v₁ m} {A₂ : GraphWalk D.rad.G.toGraph v₂ m}
      {T : GraphWalk D.rad.G.toGraph m h}
    (h1 : D.IsSpokeWalk W H (A₁.append T)) (h2 : D.IsSpokeWalk W H (A₂.append T)) {Δ₁ Δ₂ : Set
      Shat} (c₁ : IsClosed Δ₁) (c₂ : IsClosed Δ₂)
    (hu : Δ₁ ∪ Δ₂ = W) (hi : Δ₁ ∩ Δ₂ = (walkDrawing D.rad.G A₁).U ∪ (walkDrawing D.rad.G A₂).U) :
    (∀ (v h' : Shat) (K : GraphWalk D.rad.G.toGraph v h'), D.IsSpokeWalk W H K → v ∈ Δ₁
      → m ∈ K.support) ∨
      ∀ (v h' : Shat) (K : GraphWalk D.rad.G.toGraph v h'), D.IsSpokeWalk W H K → v ∈ Δ₂
        → m ∈ K.support := by
  have hhub := hW.hubSet_facts
  have hoffA : ∀ {a : Shat} {A : GraphWalk D.rad.G.toGraph a m}, D.IsSpokeWalk W H (A.append T)
    → Disjoint (hubSet D H \ {m}) (walkDrawing D.rad.G A).U := by
    intro a A hs
    refine disjoint_left.mpr fun y hy hyA ↦ hy.2 ?_
    have hyK := walkU_left_subset A T hyA
    have hy' : y ∈ ({h} : Set Shat) := by
      rw [← hW.hubSet_inter_spoke hs]
      exact ⟨hy.1, hyK⟩
    obtain rfl := mem_singleton_iff.mp hy'
    have hyV : y ∈ D.rad.G.V := hW.H_sub.1 hs.2.h_mem
    exact GraphWalk.simple_append_meet hs.1 (support_of_mem_U A hyA hyV) T.end_mem_support
  have hmU : m ∈ hubSet D H → m ∈ H.U := fun hm ↦ by
    have hm' : m ∈ ({h} : Set Shat) := by
      rw [← hW.hubSet_inter_spoke h1]
      exact ⟨hm, (mem_walkDrawing_U _ _).mpr (.inl ((GraphWalk.mem_support_append A₁ T).mpr
        (.inr T.start_mem_support)))⟩
    rw [mem_singleton_iff.mp hm']
    exact H.V_subset_U h1.2.h_mem
  have hc := hW.hub_diff_preconnected hmU
  -- The hub, without `m`, is in one disc.
  have hside : hubSet D H \ {m} ⊆ Δ₁ ∨ hubSet D H \ {m} ⊆ Δ₂ := by
    have hsub : hubSet D H \ {m} ⊆ Δ₁ ∪ Δ₂ := by
      rw [hu]
      exact sdiff_subset.trans hhub.2.1
    have hoff : ∀ y, y ∈ hubSet D H \ {m} → y ∉ Δ₁ ∩ Δ₂ := fun y hy hy' ↦ by
      rw [hi] at hy'
      rcases hy' with h' | h'
      · exact disjoint_left.mp (hoffA h1) hy h'
      · exact disjoint_left.mp (hoffA h2) hy h'
    by_contra hn
    push Not at hn
    obtain ⟨hn₁, hn₂⟩ := hn
    obtain ⟨a, ha, ha₁⟩ := not_subset.mp hn₁
    obtain ⟨b, hb, hb₂⟩ := not_subset.mp hn₂
    obtain ⟨z, hz, hz₁, hz₂⟩ := (isPreconnected_closed_iff.mp hc) Δ₁ Δ₂ c₁ c₂ hsub ⟨b, hb,
      (hsub hb).resolve_right hb₂⟩ ⟨a, ha, (hsub ha).resolve_left ha₁⟩
    exact hoff z hz ⟨hz₁, hz₂⟩
  have key : ∀ {Δ Δ' : Set Shat}, IsClosed Δ → IsClosed Δ' → Δ ∪ Δ' = W → Δ ∩ Δ' =
    (walkDrawing D.rad.G A₁).U ∪ (walkDrawing D.rad.G A₂).U → hubSet D H \ {m} ⊆ Δ' →
      ∀ (v h' : Shat) (K : GraphWalk D.rad.G.toGraph v h'), D.IsSpokeWalk W H K → v ∈ Δ
        → m ∈ K.support := by
    intro Δ Δ' c c' hu' hi' hsub v h' K hK hv
    by_contra hmK
    have hh' : h' ∈ Δ' := by
      refine hsub ⟨hW.hubSet_facts.2.2.2 (H.V_subset_U hK.2.h_mem), ?_⟩
      rintro rfl
      exact hmK K.end_mem_support
    have hsubW : (walkDrawing D.rad.G K).U ⊆ Δ ∪ Δ' := by
      rw [hu']
      exact hK.subset_W hW hbdS hin
    have hp := walkU_isPreconnected K hK.1
    obtain ⟨y, hy, hyΔ, hyΔ'⟩ := (isPreconnected_closed_iff.mp hp) Δ Δ' c c' hsubW
      ⟨v, (mem_walkDrawing_U _ _).mpr (.inl K.start_mem_support), hv⟩ ⟨h',
        (mem_walkDrawing_U _ _).mpr (.inl K.end_mem_support), hh'⟩
    have hy' : y ∈ Δ ∩ Δ' := ⟨hyΔ, hyΔ'⟩
    rw [hi'] at hy'
    have hshare : ∀ {a : Shat} {A : GraphWalk D.rad.G.toGraph a m}, D.IsSpokeWalk W H (A.append T)
      → y ∈ (walkDrawing D.rad.G A).U → False := by
      intro a A hs hyA
      rcases walkU_inter A K hyA hy with ⟨h₃, h₄⟩ | ⟨e, he₁, he₂⟩
      · exact hmK (IsSpokeWalk.passes hs hK h₃ h₄)
      · obtain ⟨p, q, -, hp, -, hcap⟩ := D.exists_ends_of_mem_edges A he₁
        exact hmK (IsSpokeWalk.passes hs hK hp (D.ends_mem_support K he₂ hcap).1)
    rcases hy' with h' | h'
    · exact hshare h1 h'
    · exact hshare h2 h'
  rcases hside with h' | h'
  · exact .inr (key c₂ c₁ (by rwa [Set.union_comm]) (by rwa [Set.inter_comm]) h')
  · exact .inl (key c₁ c₂ hu hi h')

/-- Two spokes that share `x`, with an arc `Y` of `bd(W)` between their outer ends: each spoke from
`Y`, or each spoke from outside `Y`,
holds `x`. -/
theorem chord_arc (hW : D.IsWheelHubOfRadius W H ρ) (hbdS : discBd W ⊆ cap.emb '' (univ \ bd S))
  (hin : ((W \ discBd W) ∩ (cap.emb '' D.Γ.V)).Nonempty)
    {u u' h₁ h₂ x : Shat} (hne : u ≠ u') {K₁ : GraphWalk D.rad.G.toGraph u h₁} {K₂ : GraphWalk
      D.rad.G.toGraph u' h₂} (h1 : D.IsSpokeWalk W H K₁) (h2 : D.IsSpokeWalk W H K₂)
    (hx₁ : x ∈ K₁.support) (hx₂ : x ∈ K₂.support) {Y : GraphWalk D.rad.G.toGraph u u'}
      (hY : Y.IsSimple) (hYb : (walkDrawing D.rad.G Y).U ⊆ discBd W) (hG : discBd W ⊆ D.rad.G.U) :
    (∀ (v h' : Shat) (K : GraphWalk D.rad.G.toGraph v h'), D.IsSpokeWalk W H K → v ∈
      (walkDrawing D.rad.G Y).U → x ∈ K.support) ∨
      ∀ (v h' : Shat) (K : GraphWalk D.rad.G.toGraph v h'), D.IsSpokeWalk W H K → v ∈ discBd W \
        ((walkDrawing D.rad.G Y).U \ {u, u'}) → x ∈ K.support := by
  have hT := cap.isClosedSurface
  have : ConnectedSpace Shat := cap.connected
  have hdisc := hW.is_disc
  obtain rfl := IsSpokeWalk.same_end h1 h2 hx₁ hx₂
  obtain ⟨m, A₁, A₂, T, rfl, rfl, hxT, hmeet⟩ := IsSpokeWalk.merge h1 h2 hx₁ hx₂
  have hsA₁ := (GraphWalk.IsSimple.of_append h1.1).1
  have hsA₂ := (GraphWalk.IsSimple.of_append h2.1).1
  have hmeet' : ∀ y ∈ A₁.support, y ∈ A₂.reverse.support → y = m := fun y hy hy' ↦ by
    refine hmeet y hy ((GraphWalk.mem_support_append A₂ T).mpr (.inl ?_))
    simpa [GraphWalk.support_reverse] using hy'
  have hZs : (A₁.append A₂.reverse).IsSimple := isSimple_append' hsA₁ hsA₂.reverse hmeet'
  have hZU : (walkDrawing D.rad.G (A₁.append A₂.reverse)).U = (walkDrawing D.rad.G A₁).U ∪
    (walkDrawing D.rad.G A₂).U := by
    rw [walkU_append, walkU_reverse]
  have hA₁ := walkU_left_subset A₁ T
  have hA₂ := walkU_left_subset A₂ T
  have hZW : (walkDrawing D.rad.G (A₁.append A₂.reverse)).U ⊆ W := by
    rw [hZU]
    exact union_subset (hA₁.trans (h1.subset_W hW hbdS hin)) (hA₂.trans (h2.subset_W hW hbdS hin))
  have huY : u ∈ (walkDrawing D.rad.G Y).U := (mem_walkDrawing_U _ _).mpr (.inl Y.start_mem_support)
  have huY' : u' ∈ (walkDrawing D.rad.G Y).U := (mem_walkDrawing_U _ _).mpr (.inl Y.end_mem_support)
  have hZb : (walkDrawing D.rad.G (A₁.append A₂.reverse)).U ∩ discBd W = {u, u'} := by
    apply subset_antisymm
    · rintro y ⟨hy, hyb⟩
      rw [hZU] at hy
      rcases hy with hy | hy
      · exact .inl (h1.meet_bd hW hbdS hin (hA₁ hy) hyb)
      · exact .inr (h2.meet_bd hW hbdS hin (hA₂ hy) hyb)
    · rintro y (rfl | rfl)
      · exact ⟨(mem_walkDrawing_U _ _).mpr (.inl (A₁.append A₂.reverse).start_mem_support), hYb huY⟩
      · exact ⟨(mem_walkDrawing_U _ _).mpr (.inl (A₁.append A₂.reverse).end_mem_support), hYb huY'⟩
  obtain ⟨Δ₁, Δ₂, d₁, d₂, hu, hi, b₁, b₂⟩ := exists_chord_discs hdisc hG hne hY hZs hYb hZW hZb
  rw [hZU] at hi b₁ b₂
  have hthrough : ∀ {v h' : Shat} {K : GraphWalk D.rad.G.toGraph v h'}, D.IsSpokeWalk W H K
    → m ∈ K.support → x ∈ K.support := by
    intro v h' K hK hm
    have hm' : m ∈ (A₁.append T).support := (GraphWalk.mem_support_append A₁ T).mpr
      (.inl A₁.end_mem_support)
    obtain rfl := IsSpokeWalk.same_end h1 hK hm' hm
    obtain ⟨L, R, rfl⟩ := K.exists_append_of_mem hm
    have := IsSpokeWalk.tail_after h1 hK
    subst this
    exact (GraphWalk.mem_support_append L T).mpr (.inr hxT)
  rcases chord_side hW hbdS hin h1 h2 d₁.isClosed d₂.isClosed hu hi with hs | hs
  · exact .inl fun v h' K hK hv ↦ hthrough hK (hs v h' K hK (Surface.discBd_subset _
      (b₁ ▸ .inl hv)))
  · exact .inr fun v h' K hK hv ↦ hthrough hK (hs v h' K hK (Surface.discBd_subset _
      (b₂ ▸ .inl hv)))

/-- `bd(W)` read as a closed walk of `Γ*` from a vertex of `Γ`, of length `2k`. -/
structure Rim (D : TangleDatum cap χ) (W : Set Shat) where
  /-- The base vertex of the rim walk. -/
  b : Shat
  /-- The closed radial walk on the boundary of the wheel disc. -/
  B : GraphWalk D.rad.G.toGraph b b
  /-- Half the length of the closed radial walk. -/
  k : ℕ
  simple : B.IsSimpleClosed
  len : B.length = 2 * k
  two : 2 ≤ k
  base : b ∈ D.P.Γ.hatV cap
  U_eq : (walkDrawing D.rad.G B).U = discBd W

namespace Rim

variable (R : Rim D W)

/-- The `i`th vertex of `Γ` on the rim, with `i` read modulo `k`. -/
noncomputable def vert (i : ℕ) : Shat := GraphWalk.vertexAt R.B (2 * (i % R.k))

/-- The `i`th vertex of `R*` on the rim, between the vertices `i` and `i + 1`. -/
noncomputable def reg (i : ℕ) : Shat := GraphWalk.vertexAt R.B (2 * (i % R.k) + 1)

omit [T2Space S] in
theorem pos_mem_bd {p : ℕ} (hp : p ≤ R.B.length) : GraphWalk.vertexAt R.B p ∈ discBd W := by
  rw [← R.U_eq]
  exact (mem_walkDrawing_U _ _).mpr (.inl (GraphWalk.vertexAt_mem _ hp))

theorem pos_hatV {p : ℕ} (hp : p ≤ R.B.length) : Even p ↔ GraphWalk.vertexAt R.B p ∈ D.P.Γ.hatV cap
  := by
  obtain ⟨P, Q, -, hl⟩ := GraphWalk.exists_split_at R.B hp
  have h := D.even_length_walk P
  rw [hl] at h
  rw [h]
  exact ⟨fun h' ↦ h'.mp R.base, fun h' ↦ ⟨fun _ ↦ h', fun _ ↦ R.base⟩⟩

omit [T2Space S] in
theorem mod_lt (i : ℕ) : i % R.k < R.k := Nat.mod_lt _ (by have := R.two; omega)

theorem vert_mem (i : ℕ) : R.vert i ∈ bdVerts D W := by
  have hl := R.mod_lt i
  have hle : 2 * (i % R.k) ≤ R.B.length := by rw [R.len]; omega
  exact ⟨(R.pos_hatV hle).mp (even_two_mul _), R.pos_mem_bd hle⟩

theorem reg_mem (i : ℕ) : R.reg i ∈ D.rad.Rstar ∩ discBd W := by
  have hl := R.mod_lt i
  have hle : 2 * (i % R.k) + 1 ≤ R.B.length := by rw [R.len]; omega
  have hb := R.pos_mem_bd hle
  refine ⟨⟨?_, fun h ↦ ?_⟩, hb⟩
  · exact (walkDrawing_isSubdrawing D.rad.G R.B).1 (by
      rw [walkDrawing_V]
      exact GraphWalk.vertexAt_mem _ hle)
  · have := (R.pos_hatV hle).mpr h
    rw [Nat.even_add_one] at this
    exact this (even_two_mul _)

theorem exists_vert (x : Shat) (hx : x ∈ bdVerts D W) : ∃ i < R.k, x = R.vert i := by
  have hxU : x ∈ (walkDrawing D.rad.G R.B).U := R.U_eq ▸ hx.2
  have hsupp := support_of_mem_U R.B hxU (D.rad.isPreRadial.2.1 hx.1)
  obtain ⟨p, hp, rfl⟩ := GraphWalk.exists_vertexAt R.B hsupp
  have hev := (R.pos_hatV hp).mpr hx.1
  obtain ⟨i, rfl⟩ := hev
  rw [R.len] at hp
  by_cases hi : i = R.k
  · subst hi
    refine ⟨0, by have := R.two; omega, ?_⟩
    have h₁ : GraphWalk.vertexAt R.B (R.k + R.k) = R.b := by
      rw [← two_mul, ← R.len]
      exact GraphWalk.vertexAt_length _ (D.rad.isPreRadial.2.1 R.base)
    rw [h₁, vert, Nat.zero_mod, Nat.mul_zero, GraphWalk.vertexAt_zero]
  · refine ⟨i, by omega, ?_⟩
    rw [vert, Nat.mod_eq_of_lt (by omega), two_mul]

theorem exists_reg (x : Shat) (hx : x ∈ D.rad.Rstar ∩ discBd W) : ∃ i < R.k, x = R.reg i := by
  have hxU : x ∈ (walkDrawing D.rad.G R.B).U := R.U_eq ▸ hx.2
  have hsupp := support_of_mem_U R.B hxU hx.1.1
  obtain ⟨p, hp, rfl⟩ := GraphWalk.exists_vertexAt R.B hsupp
  have hev : ¬ Even p := fun h ↦ hx.1.2 ((R.pos_hatV hp).mp h)
  obtain ⟨i, rfl⟩ := Nat.not_even_iff_odd.mp hev
  rw [R.len] at hp
  refine ⟨i, by omega, ?_⟩
  rw [reg, Nat.mod_eq_of_lt (by omega)]

omit [T2Space S] in
theorem vert_inj {i j : ℕ} (hi : i < R.k) (hj : j < R.k) (h : R.vert i = R.vert j) : i = j := by
  rw [vert, vert, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at h
  have := GraphWalk.closed_vertexAt_inj R.B R.simple
      (by rw [R.len]; omega) (by rw [R.len]; omega) h
  rw [R.len] at this
  omega

omit [T2Space S] in
theorem reg_inj {i j : ℕ} (hi : i < R.k) (hj : j < R.k) (h : R.reg i = R.reg j) : i = j := by
  rw [reg, reg, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at h
  have := GraphWalk.closed_vertexAt_inj R.B R.simple
      (by rw [R.len]; omega) (by rw [R.len]; omega) h
  rw [R.len] at this
  omega

omit [T2Space S] in
theorem vert_add_k (i : ℕ) : R.vert (i + R.k) = R.vert i := by
  rw [vert, vert, Nat.add_mod_right]

omit [T2Space S] in
theorem vert_ne_succ {i : ℕ} (hi : i < R.k) : R.vert i ≠ R.vert (i + 1) := by
  have h2 := R.two
  by_cases hl : i + 1 = R.k
  · have h₀ : R.vert (i + 1) = R.vert 0 := by
      rw [hl]
      simpa using R.vert_add_k 0
    rw [h₀]
    intro e
    have := R.vert_inj hi (by omega) e
    omega
  · intro e
    have := R.vert_inj hi (by omega) e
    omega

omit [T2Space S] in
/-- The two edges of the rim at the `i`th vertex of `R*`. -/
theorem exists_links (i : ℕ) : ∃ f g, D.rad.G.toGraph.IsLink f (R.reg i) (R.vert i)
  ∧ D.rad.G.toGraph.IsLink g (R.reg i) (R.vert (i + 1)) ∧ f ⊆ discBd W ∧ g ⊆ discBd W := by
  have hl := R.mod_lt i
  have hedge : ∀ e ∈ R.B.edges, e ⊆ discBd W := fun e he z hz ↦ by
    rw [← R.U_eq]
    exact (mem_walkDrawing_U _ _).mpr (.inr ⟨e, he, subset_closure hz⟩)
  obtain ⟨f, hf, hlf⟩ := GraphWalk.link_at R.B (p := 2 * (i % R.k)) (by rw [R.len]; omega)
  obtain ⟨g, hg, hlg⟩ := GraphWalk.link_at R.B (p := 2 * (i % R.k) + 1) (by rw [R.len]; omega)
  refine ⟨f, g, hlf.symm, ?_, hedge f hf, hedge g hg⟩
  have hnext : GraphWalk.vertexAt R.B (2 * (i % R.k) + 1 + 1) = R.vert (i + 1) := by
    rw [vert, show (i + 1) % R.k = (i % R.k + 1) % R.k from (Nat.mod_add_mod i R.k 1).symm]
    by_cases hlast : i % R.k + 1 = R.k
    · rw [hlast, Nat.mod_self, Nat.mul_zero, GraphWalk.vertexAt_zero]
      have : 2 * (i % R.k) + 1 + 1 = R.B.length := by rw [R.len]; omega
      rw [this]
      exact GraphWalk.vertexAt_length _ (D.rad.isPreRadial.2.1 R.base)
    · rw [Nat.mod_eq_of_lt (a := i % R.k + 1) (b := R.k) (by omega)]
      congr 1
  rw [← hnext]
  exact hlg

omit [T2Space S] in
/-- The part of the rim from the vertex `i` to the vertex `j`. -/
theorem exists_seg {i j : ℕ} (hij : i < j) (hj : j < R.k) : ∃ Y : GraphWalk D.rad.G.toGraph
  (R.vert i) (R.vert j), Y.IsSimple ∧ (walkDrawing D.rad.G Y).U ⊆ discBd W ∧
    (∀ l, i ≤ l → l ≤ j → R.vert l ∈ (walkDrawing D.rad.G Y).U) ∧ ∀ l < R.k, R.vert l ∈
      (walkDrawing D.rad.G Y).U → i ≤ l ∧ l ≤ j := by
  have hmod : ∀ {l}, l < R.k → R.vert l = GraphWalk.vertexAt R.B (2 * l) :=
    fun {l} hl ↦ by rw [vert, Nat.mod_eq_of_lt hl]
  rw [hmod (hij.trans hj), hmod hj]
  have hpos : 2 * j = 2 * i + 2 * (j - i) := by omega
  have hlen : 2 * i + 2 * (j - i) ≤ R.B.length := by rw [R.len]; omega
  obtain ⟨Y, hYl, hYt, hYe⟩ := GraphWalk.exists_seg_at R.B (2 * i) (2 * (j - i)) hlen
  rw [hpos]
  have hinj : ∀ {p q}, p < 2 * R.k → q < 2 * R.k → GraphWalk.vertexAt R.B p
    = GraphWalk.vertexAt R.B q → p = q := by
    intro p q hp hq h
    have := GraphWalk.closed_vertexAt_inj R.B R.simple
      (by rw [R.len]; omega) (by rw [R.len]; omega) h
    rw [R.len] at this
    omega
  have hsimple : Y.IsSimple := by
    refine GraphWalk.isSimple_of_vertexAt_inj Y fun p q hp hq h ↦ ?_
    rw [hYl] at hp hq
    rw [hYt p hp, hYt q hq] at h
    have := hinj (by omega) (by omega) h
    omega
  have hYU : (walkDrawing D.rad.G Y).U ⊆ (walkDrawing D.rad.G R.B).U := by
    intro y hy
    rw [mem_walkDrawing_U] at hy ⊢
    rcases hy with h | ⟨e, he, hye⟩
    · obtain ⟨t, ht, rfl⟩ := GraphWalk.exists_vertexAt Y h
      rw [hYl] at ht
      exact .inl (by rw [hYt t ht]; exact GraphWalk.vertexAt_mem _ (by omega))
    · exact .inr ⟨e, hYe e he, hye⟩
  refine ⟨Y, hsimple, R.U_eq ▸ hYU, fun l h₁ h₂ ↦ ?_, fun l hl hm ↦ ?_⟩
  · rw [hmod (by omega)]
    have := hYt (2 * (l - i)) (by omega)
    rw [show 2 * i + 2 * (l - i) = 2 * l by omega] at this
    rw [← this]
    exact (mem_walkDrawing_U _ _).mpr (.inl (GraphWalk.vertexAt_mem _ (by omega)))
  · rw [hmod hl] at hm
    have hV : GraphWalk.vertexAt R.B (2 * l) ∈ D.rad.G.V :=
      (walkDrawing_isSubdrawing D.rad.G R.B).1 (by
      rw [walkDrawing_V]
      exact GraphWalk.vertexAt_mem _ (by rw [R.len]; omega))
    obtain ⟨t, ht, he⟩ := GraphWalk.exists_vertexAt Y (support_of_mem_U Y hm hV)
    rw [hYl] at ht
    rw [hYt t ht] at he
    have := hinj (by omega) (by omega) he
    omega


/-- The spoke at the `i`th vertex of the rim. -/
noncomputable def spoke (sp : SpokeSystem D W H) (i : ℕ) : GraphWalk D.rad.G.toGraph (R.vert i)
  (sp.hEnd ⟨R.vert i, R.vert_mem i⟩) := sp.K ⟨R.vert i, R.vert_mem i⟩

/-- The inner end of the spoke at the `i`th vertex of the rim. -/
noncomputable def inner (sp : SpokeSystem D W H) (i : ℕ) : Shat := sp.hEnd ⟨R.vert i, R.vert_mem i⟩

theorem spoke_spoke (sp : SpokeSystem D W H) (i : ℕ) : D.IsSpokeWalk W H (R.spoke sp i)
  := sp.spoke _

omit [T2Space S] in
theorem G_sub (R : Rim D W) : discBd W ⊆ D.rad.G.U := by
  rw [← R.U_eq]
  exact (walkDrawing_isSubdrawing D.rad.G R.B).U_subset

/-- **The spokes through a point leave `bd(W)` along one arc.** -/
theorem arc (hW : D.IsWheelHubOfRadius W H ρ) (hbdS : discBd W ⊆ cap.emb '' (univ \ bd S)) (hin :
  ((W \ discBd W) ∩ (cap.emb '' D.Γ.V)).Nonempty) (sp : SpokeSystem D W H)
    {i j : ℕ} {x : Shat} (hij : i < j) (hj : j < R.k) (hxi : x ∈ (R.spoke sp i).support) (hxj : x ∈
      (R.spoke sp j).support) :
    (∀ l, i ≤ l → l ≤ j → x ∈ (R.spoke sp l).support) ∨ ∀ l < R.k, (l ≤ i ∨ j ≤ l) → x ∈
      (R.spoke sp l).support := by
  have hne : R.vert i ≠ R.vert j := fun e ↦ by
    have := R.vert_inj (hij.trans hj) hj e
    omega
  obtain ⟨Y, hYs, hYb, hin₁, hin₂⟩ := R.exists_seg hij hj
  rcases chord_arc hW hbdS hin hne (R.spoke_spoke sp i) (R.spoke_spoke sp j) hxi hxj hYs hYb
    R.G_sub with h' | h'
  · exact .inl fun l h₁ h₂ ↦ h' _ _ _ (R.spoke_spoke sp l) (hin₁ l h₁ h₂)
  · refine .inr fun l hl hl' ↦ h' _ _ _ (R.spoke_spoke sp l) ⟨(R.vert_mem l).2, fun hm ↦ hm.2 ?_⟩
    obtain ⟨h₁, h₂⟩ := hin₂ l hl hm.1
    have : l = i ∨ l = j := by omega
    rcases this with rfl | rfl
    · exact .inl rfl
    · exact .inr rfl

/-- The indices where the inner end changes. -/
def changes (sp : SpokeSystem D W H) : Set ℕ := {i | i < R.k ∧ R.inner sp i ≠ R.inner sp (i + 1)}

theorem inner_eq_of_mem (sp : SpokeSystem D W H) {i j : ℕ} {x :
  Shat} (hi : x ∈ (R.spoke sp i).support) (hj : x ∈ (R.spoke sp j).support) :
    R.inner sp i = R.inner sp j := IsSpokeWalk.same_end (R.spoke_spoke sp i)
      (R.spoke_spoke sp j) hi hj

/-- **At most `|V(H)|` changes.** -/
theorem injOn_inner_changes (hW : D.IsWheelHubOfRadius W H ρ) (hbdS : discBd W ⊆ cap.emb ''
  (univ \ bd S)) (hin : ((W \ discBd W) ∩ (cap.emb '' D.Γ.V)).Nonempty)
    (sp : SpokeSystem D W H) : InjOn (R.inner sp) (R.changes sp) := by
  have hper : R.inner sp R.k = R.inner sp 0 := by
    have : R.vert R.k = R.vert 0 := by simpa using R.vert_add_k 0
    simp only [inner, this]
  refine cyclic_changes_injOn R.k _ hper fun i j hij hj he ↦ ?_
  have hxi : R.inner sp i ∈ (R.spoke sp i).support := GraphWalk.end_mem_support _
  have hxj : R.inner sp i ∈ (R.spoke sp j).support := by
    rw [he]
    exact GraphWalk.end_mem_support _
  rcases R.arc hW hbdS hin sp hij hj hxi hxj with h' | h'
  · exact .inl fun l h₁ h₂ ↦ (R.inner_eq_of_mem sp (GraphWalk.end_mem_support _)
      (h' l h₁ h₂)).symm ▸ rfl
  · exact .inr fun l h₁ h₂ ↦ (R.inner_eq_of_mem sp (GraphWalk.end_mem_support _)
      (h' l h₁ h₂)).symm ▸ rfl

theorem inner_mem (sp : SpokeSystem D W H) (i : ℕ) : R.inner sp i ∈ H.V :=
  (R.spoke_spoke sp i).2.h_mem

theorem ncard_changes_le (hW : D.IsWheelHubOfRadius W H ρ) (hbdS : discBd W ⊆ cap.emb ''
  (univ \ bd S)) (hin : ((W \ discBd W) ∩ (cap.emb '' D.Γ.V)).Nonempty)
    (sp : SpokeSystem D W H) : (R.changes sp).ncard ≤ H.V.ncard := by
  rw [← (R.injOn_inner_changes hW hbdS hin sp).ncard_image]
  refine ncard_le_ncard ?_ H.finite_V
  rintro _ ⟨i, -, rfl⟩
  exact R.inner_mem sp i

end Rim

/-- `bd(W)` can be read as a rim. -/
theorem exists_rim (hW : D.IsWheelHubOfRadius W H ρ) (hbdS : discBd W ⊆ cap.emb '' (univ \ bd S))
  (hin : ((W \ discBd W) ∩ (cap.emb '' D.Γ.V)).Nonempty) : Nonempty (Rim D W) := by
  classical
  have : ConnectedSpace Shat := cap.connected
  obtain ⟨F, hFc, hFs, hFU⟩ := exists_circuit_of_oArc hW.is_disc.isOArc_discBd hW.bd_sub
  have h3 := three_le_ncard_bd hW hbdS hin
  obtain ⟨x, y, hx, hy, hxy⟩ : ∃ x y, x ∈ discBd W ∩ D.P.Γ.hatV cap ∧ y ∈ discBd W ∩ D.P.Γ.hatV cap
    ∧ x ≠ y := by
    have : 1 < (discBd W ∩ D.P.Γ.hatV cap).ncard := by omega
    obtain ⟨x, hx, y, hy, hne⟩ := (one_lt_ncard (D.P.Γ.finite_V.image _ |>.subset
      inter_subset_right)).mp this
    exact ⟨x, y, hx, hy, hne⟩
  have hV : ∀ {z}, z ∈ discBd W ∩ D.P.Γ.hatV cap → z ∈ F.V := fun hz ↦ mem_V_of_mem_U hFs
    (hFU ▸ hz.1) (D.rad.isPreRadial.2.1 hz.2)
  obtain ⟨P, Q, hP, hQ, hPs, hQs, -, -, hPQ, hdis, hsup⟩ := Drawing.IsCircuit.exists_two_paths hFc
    (hV hx) (hV hy) hxy
  obtain ⟨KP, hKP, hPV, hPE⟩ := Drawing.IsPathOf.exists_simple_walk (G
    := D.rad.G) ⟨hPs.trans hFs, hP⟩
  obtain ⟨KQ, hKQ, hQV, hQE⟩ := Drawing.IsPathOf.exists_simple_walk (G
    := D.rad.G) ⟨hQs.trans hFs, hQ⟩
  have hsimple : (KP.append KQ.reverse).IsSimpleClosed := by
    refine GraphWalk.isSimpleClosed_append hKP hKQ.reverse (fun z h₁ h₂ ↦ ?_) fun e h₁ h₂ ↦ ?_
    · have hz₂ : z ∈ KQ.support := by simpa [GraphWalk.support_reverse] using h₂
      have : z ∈ P.V ∩ Q.V := ⟨(hPV z).mpr h₁, (hQV z).mpr hz₂⟩
      rw [hPQ] at this
      exact this
    · have he₂ : e ∈ KQ.edges := by simpa [GraphWalk.edges_reverse] using h₂
      exact disjoint_left.mp hdis ((hPE e).mpr h₁) ((hQE e).mpr he₂)
  have hUeq : ∀ {Y : Drawing Shat} {a b : Shat} {K : GraphWalk D.rad.G.toGraph a b},
    (∀ x, x ∈ Y.V ↔ x ∈ K.support) → (∀ e, e ∈ Y.E ↔ e ∈ K.edges) → (walkDrawing D.rad.G K).U = Y.U
      := by
    intro Y a b K h₁ h₂
    rw [Drawing.U_eq, Drawing.U_eq, walkDrawing_V, walkDrawing_E]
    congr 1
    · ext z
      exact (h₁ z).symm
    · ext z
      simp only [mem_iUnion, exists_prop]
      exact ⟨fun ⟨e, he, hz⟩ ↦ ⟨e, (h₂ e).mpr he, hz⟩, fun ⟨e, he, hz⟩ ↦ ⟨e, (h₂ e).mp he, hz⟩⟩
  have hU : (walkDrawing D.rad.G (KP.append KQ.reverse)).U = discBd W := by
    rw [walkU_append, walkU_reverse, hUeq hPV hPE, hUeq hQV hQE, ← hFU]
    exact (paths_U_union hPs hQs hsup).symm
  have hev : Even (KP.append KQ.reverse).length := (D.even_length_walk _).mpr (Iff.rfl)
  obtain ⟨k, hk⟩ := hev
  have hxV : x ∈ D.rad.G.V := D.rad.isPreRadial.2.1 hx.2
  have hsupp : y ∈ (KP.append KQ.reverse).support := by
    have : y ∈ KP.support := KP.end_mem_support
    exact (GraphWalk.mem_support_append _ _).mpr (.inl this)
  refine ⟨⟨x, KP.append KQ.reverse, k, hsimple, by omega, ?_, hx.2, hU⟩⟩
  obtain ⟨p, hp, hpe⟩ := GraphWalk.exists_vertexAt _ hsupp
  have hEv : Even p := by
    obtain ⟨A, -, -, hl⟩ := GraphWalk.exists_split_at (KP.append KQ.reverse) hp
    have h := D.even_length_walk A
    rw [hl] at h
    exact h.mpr ⟨fun _ ↦ hpe ▸ hy.2, fun _ ↦ hx.2⟩
  by_contra hlt
  have hle : p = 0 ∨ p = (KP.append KQ.reverse).length := by
    obtain ⟨q, rfl⟩ := hEv
    omega
  rcases hle with rfl | hp'
  · rw [GraphWalk.vertexAt_zero] at hpe
    exact hxy hpe.symm
  · rw [hp', GraphWalk.vertexAt_length _ hxV] at hpe
    exact hxy hpe.symm

/-- A vertex of a hub that is a circuit is not strictly inside a small enclave. -/
theorem IsWheelHubOfRadius.hub_vertex_off_enclave (hW : D.IsWheelHubOfRadius W H ρ)
  (hH : IsEnclave D.tb D.ord D.𝒯 H) (hHle : H.E.ncard ≤ 4 * ρ + 4)
    (hne : ∀ H' : Drawing Shat, IsEnclave D.tb D.ord D.𝒯 H' → H' ≠ H → H'.E.ncard ≤ 4 * ρ + 4 → ¬
      (H.U ⊆ D.ins H')) {h : Shat} (hh : h ∈ H.V)
    {F : Drawing Shat} (hFe : IsEnclave D.tb D.ord D.𝒯 F) (hFle : F.E.ncard
      ≤ 4 * ρ + 4) : h ∉ D.ins F \ F.U := by
  have : ConnectedSpace Shat := cap.connected
  intro h'
  have hrep := hW.rep_ge
  obtain ⟨ord', 𝒯', h𝒯', hc, hlt₀, Δ, hins, hd⟩ := id hFe
  have hlt' : F.E.ncard < 2 * D.rep := hlt₀
  have hsl := D.isSlope (by omega)
  have hHlt : H.E.ncard < 2 * D.rep := by omega
  obtain ⟨ord₂, 𝒯₂, h𝒯₂, hcH, hlt₂, Δ₂, hins₂, hd₂⟩ := id hH
  obtain ⟨hclH, hfrH, hUH⟩ := ins_facts_of_length hsl hcH.2 hcH.1 hHlt
  have hne' : F ≠ H := by
    intro e
    have : h ∈ F.U := e ▸ H.V_subset_U hh
    exact h'.2 this
  have hnotsub : ¬ H.U ⊆ D.ins F := hne F hFe hne' hFle
  obtain rfl := D.eq_ins_of_isInsOf hins
  obtain rfl := D.eq_ins_of_isInsOf hins₂
  rcases theorem_8_6_proof χ.isSurface D.P.fits.internally_three_connected D.tb D.isTangle h𝒯₂ h𝒯'
    hins₂ hins hd₂ hd with h₁ | h₁ | h₁
  · exact hnotsub (hUH.trans h₁)
  · have hi := interior_mono h₁ ((D.ins_diff_iff hc hlt').mp h')
    exact (D.ins_diff_iff hcH hHlt).mpr hi |>.2 (H.V_subset_U hh)
  · have : h ∈ D.ins H ∩ D.ins F := ⟨hUH (H.V_subset_U hh), h'.1⟩
    rw [h₁] at this
    exact h'.2 this.2

/-- If the hub is a circuit, then not all spokes have the same inner end, because `H` is optimal. -/
theorem Rim.exists_change (R : Rim D W) (hopt : D.IsOptimalWheelHub W H ρ) (sp : SpokeSystem D W H)
  (hc : H.V.ncard ≠ 1) : (R.changes sp).Nonempty := by
  have hW := hopt.toIsWheelHubOfRadius
  by_contra hno
  have hall : ∀ i, i < R.k → R.inner sp i = R.inner sp 0 := by
    intro i hi
    induction i with
    | zero => rfl
    | succ i ih =>
      rw [← ih (by omega)]
      by_contra hn
      exact hno ⟨i, by omega, fun e ↦ hn e.symm⟩
  set h := R.inner sp 0 with hh
  have hhV : h ∈ H.V := R.inner_mem sp 0
  have huG : h ∈ D.rad.G.V := hW.H_sub.1 hhV
  have hsp : ∀ v ∈ (cap.emb '' D.Γ.V) ∩ discBd W, ∃ A : GraphWalk D.rad.G.toGraph v h, A.length +
    (GraphWalk.nil huG : GraphWalk D.rad.G.toGraph h h).length ≤ ρ := by
    intro v hv
    obtain ⟨i, hi, rfl⟩ := R.exists_vert v hv
    have e : R.inner sp i = h := hall i hi
    have hK := R.spoke_spoke sp i
    have hl := (hW.spoke_length hK).1
    have hS : ∀ {a : Shat} (A : GraphWalk D.rad.G.toGraph (R.vert i) a), a = h → A.length ≤ ρ
      → ∃ A : GraphWalk D.rad.G.toGraph (R.vert i) h, A.length + (GraphWalk.nil huG : GraphWalk
        D.rad.G.toGraph h h).length ≤ ρ := by
      rintro a A rfl hle
      exact ⟨A, by change A.length + 0 ≤ ρ; exact hle⟩
    exact hS (R.spoke sp i) e hl
  have hen : ∀ F : Drawing Shat, IsEnclave D.tb D.ord D.𝒯 F → F.E.ncard ≤ 4 * ρ + 4
    → h ∉ D.ins F \ F.U := by
    intro F h₁ h₂
    rcases hW.hub_cond with ⟨hcard, -, -⟩ | ⟨hen, hle, hne⟩
    · exact absurd hcard hc
    · exact hW.hub_vertex_off_enclave hen hle hne hhV h₁ h₂
  have hub := hW.hub_at huG (GraphWalk.nil huG) hhV
    (by change 0 < ρ; exact hW.pos_ρ) (hW.H_in_int (H.V_subset_U hhV)) hsp hen
  have hρ : (GraphWalk.nil huG : GraphWalk D.rad.G.toGraph h h).length = 0 := rfl
  rw [hρ, Nat.sub_zero] at hub
  rcases hopt.one_vertex_priority with h' | h'
  · exact hc h'
  · exact h' ⟨_, hub, by rw [(point_drawing_facts D.rad.G huG).1, ncard_singleton]⟩

end TangleDatum

end GraphMinor.GM19
