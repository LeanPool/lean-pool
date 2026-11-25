/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.PadData
public import LeanPool.GraphMinor.GM19.Conditional3

/-!
# Graph Minors XIX, (15.2): the topological step

We prove `Theorem152FeasibilityStatement`, which is steps (2) and (3) of the proof of (15.2), pages
381 and 382. The model has a pad for each disc of the family: the disc pasted on a cuff, the closed
disc
of an edge of size 3, and a thin disc around an edge of size 2 (`exists_pads`). The pads meet only
in `V(Γ₀)`. The order data of the pads hold because of the order along the sides, and because of the
hypothesis
on orientations for edges of size 3. Then `exists_realizing_discs` gives the homeomorphism `α` of
step (2) and pulls back the discs of step (3).
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Metric Topology GraphMinor.Surface GraphMinor.GM11

universe w

local notation "𝕀" => unitInterval

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
  {cap : IsCappedSurface S Shat} {β : Type w} {χ : ColourScheme S β}

omit [T2Space S] in
/-- A line edge, with the two ends written as its march. -/
theorem Painting.exists_march (Γ : Painting S) {e : Set S} (he : e ∈ Γ.E) (h2 : (tilde e).ncard
  = 2) : ∃ u w, Γ.γ e = [u, w] ∧ IsLineWithEnds (closure e) u w := by
  obtain ⟨f, hne, hset⟩ := Γ.exists_line he h2
  rcases list_pair (Γ.γ_nodup e he) (by rw [Γ.γ_set e he, hset]) hne with h | h
  · exact ⟨_, _, h, f, rfl, rfl⟩
  · exact ⟨_, _, h, (Surface.IsLineWithEnds.symm (L := closure e) ⟨f, rfl, rfl⟩)⟩

omit [T2Space S] [T2Space Shat] in
theorem isLineWithEnds_emb (cap : IsCappedSurface S Shat) {L : Set S} {u w : S}
  (h : IsLineWithEnds L u w) : IsLineWithEnds (cap.emb '' L) (cap.emb u) (cap.emb w) := by
  obtain ⟨f, h0, h1⟩ := h
  refine ⟨f.trans (cap.isEmbedding.homeomorphImage L), ?_, ?_⟩
  · change cap.emb (f 0).1 = _
    rw [h0]
  · change cap.emb (f 1).1 = _
    rw [h1]

namespace TangleDatum

variable {D : TangleDatum cap χ} {P₀ : ColouredPainting χ} {n : ℕ} {b : Set S → Set S}

/-- The closed set of each disc of the family, in the model `Γ₀`. -/
def padBase (cap : IsCappedSurface S Shat) (P₀ : ColouredPainting χ) : DiscIndex S P₀ → Set Shat
  | .inl Θ => closure (cap.cuffDisc Θ.1)
  | .inr e => cap.emb '' closure e.1

omit [T2Space S] in
theorem closure_inter_closure (Γ : Painting S) {e e' : Set S} (he : e ∈ Γ.E) (he' : e' ∈ Γ.E)
  (hne : e ≠ e') : closure e ∩ closure e' ⊆ Γ.V := by
  rintro z ⟨hz, hz'⟩
  by_cases h₁ : z ∈ e
  · by_cases h₂ : z ∈ e'
    · exact absurd (arcComponent_eq he he' h₁ h₂) hne
    · exact Γ.tilde_subset_V he' ⟨hz', h₂⟩
  · exact Γ.tilde_subset_V he ⟨hz, h₁⟩

omit [T2Space Shat] in
omit [T2Space S] in
theorem padBase_inter {i j : DiscIndex S P₀} (hne : i ≠ j) : padBase cap P₀ i ∩
  padBase cap P₀ j ⊆ cap.emb '' P₀.Γ.V := by
  have key : ∀ (Θ : {Θ : Set S // Θ ∈ cuffs S}) (e : {e : Set S // e ∈ P₀.Γ.E
      ∧ Painting.IsInternal e}),
      closure (cap.cuffDisc Θ.1) ∩ cap.emb '' closure e.1 ⊆ cap.emb '' P₀.Γ.V := by
    rintro Θ e x ⟨hx, z, hz, rfl⟩
    rw [cap.closure_cuffDisc Θ.2] at hx
    rcases hx with h | ⟨y, hy, hyz⟩
    · exact absurd (mem_range_self z) (cap.notMem_range Θ.2 h)
    · obtain rfl := cap.isEmbedding.injective hyz
      have hnz : y ∉ e.1 := fun h' => Set.disjoint_left.mp e.2.2 h' (cuff_subset_bd ⟨Θ.1, Θ.2⟩ hy)
      exact mem_image_of_mem _ (P₀.Γ.tilde_subset_V e.2.1 ⟨hz, hnz⟩)
  rcases i with Θ | e <;> rcases j with Θ' | e'
  · intro x hx
    have hd := cap.cuffDisc_disjoint Θ.1 Θ.2 Θ'.1 Θ'.2 fun h => hne (congrArg Sum.inl
      (Subtype.ext h))
    exact absurd hx.2 (Set.disjoint_left.mp hd hx.1)
  · exact key Θ e'
  · intro x hx
    exact key Θ' e ⟨hx.2, hx.1⟩
  · rintro _ ⟨⟨z, hz, rfl⟩, z', hz', he⟩
    obtain rfl := cap.isEmbedding.injective he
    exact mem_image_of_mem _ (closure_inter_closure P₀.Γ e.2.1 e'.2.1 (fun h => hne
      (congrArg Sum.inr (Subtype.ext h))) ⟨hz, hz'⟩)

omit [T2Space S] in
theorem isClosed_padBase (hS : IsSurface S) (i : DiscIndex S P₀) : IsClosed (padBase cap P₀ i) := by
  rcases i with Θ | e
  · exact isClosed_closure
  · have := hS.1
    exact (isClosed_closure.isCompact.image cap.isEmbedding.continuous).isClosed

omit [T2Space S] [T2Space Shat] in
theorem discBd_emb (cap : IsCappedSurface S Shat) {X : Set S} (hX : IsClosedDisc X) : IsClosedDisc
  (cap.emb '' X) ∧ discBd (cap.emb '' X) = cap.emb '' discBd X :=
  isClosedDisc_image hX cap.isEmbedding

omit [T2Space S] in
/-- **The pads.** -/
theorem exists_pads (hS : IsSurface S) (P₀ : ColouredPainting χ) (cap : IsCappedSurface S Shat) :
    ∃ C : DiscIndex S P₀ → Set Shat, (∀ i, IsClosedDisc (C i)) ∧ (∀ i j, i ≠ j
      → C i ∩ C j ⊆ cap.emb '' P₀.Γ.V) ∧ (∀ i, cap.emb '' P₀.Γ.V ∩ C i ⊆ discBd (C i)) ∧
      (∀ Θ, C (.inl Θ) = closure (cap.cuffDisc Θ.1)) ∧ (∀ e, (tilde e.1).ncard = 3 → C (.inr e)
        = cap.emb '' closure e.1) ∧ ∀ e, cap.emb '' closure e.1 ⊆ C (.inr e) := by
  classical
  have hT := cap.isClosedSurface
  have := finite_discIndex hS P₀
  have hS₀ : Nonempty S := by
    have := χ.connected
    infer_instance
  let L : Set (DiscIndex S P₀) := {i | ∃ e, i = .inr e ∧ (tilde e.1).ncard = 2}
  have hVc : IsClosed (cap.emb '' P₀.Γ.V) := (P₀.Γ.finite_V.image _).isClosed
  have hline : ∀ i, ∃ u w : Shat, i ∈ L → IsLineWithEnds (padBase cap P₀ i) u w
    ∧ padBase cap P₀ i ∩ cap.emb '' P₀.Γ.V = {u, w} := by
    intro i
    by_cases hi : i ∈ L
    · obtain ⟨e, rfl, h2⟩ := hi
      obtain ⟨u, w, hγ, hl⟩ := Painting.exists_march P₀.Γ e.2.1 h2
      refine ⟨cap.emb u, cap.emb w, fun _ => ⟨isLineWithEnds_emb cap hl, ?_⟩⟩
      have hset : tilde e.1 = {u, w} := by
        rw [← P₀.Γ.γ_set e.1 e.2.1, hγ]
        ext x
        simp
      change cap.emb '' closure e.1 ∩ cap.emb '' P₀.Γ.V = _
      rw [← image_inter cap.isEmbedding.injective, ← image_pair, ← hset]
      congr 1
      apply Subset.antisymm
      · rintro x ⟨h1, h2⟩
        exact ⟨h1, fun h => P₀.Γ.disjoint_V e.2.1 h h2⟩
      · exact fun x hx => ⟨hx.1, P₀.Γ.tilde_subset_V e.2.1 hx⟩
    · exact ⟨cap.emb (Classical.arbitrary _), cap.emb (Classical.arbitrary _), fun h => absurd h hi⟩
  choose u w hl using hline
  obtain ⟨C, -, h2, h3, h4⟩ := exists_thin_family hT (isClosed_padBase hS) hVc (fun i j h
    => padBase_inter h) (L := L) (fun i hi => (hl i hi).1) fun i hi => (hl i hi).2
  have hinl : ∀ Θ, (Sum.inl Θ : DiscIndex S P₀) ∉ L := fun Θ ⟨e, he, _⟩ => by cases he
  have hthree : ∀ e : {e : Set S // e ∈ P₀.Γ.E ∧ Painting.IsInternal e}, (tilde e.1).ncard = 3 →
    (Sum.inr e : DiscIndex S P₀) ∉ L := fun e h3' ⟨e', he, h2'⟩ => by
    have : e = e' := Sum.inr.inj he
    rw [this] at h3'
    omega
  have hC₀ : ∀ Θ, C (.inl Θ) = closure (cap.cuffDisc Θ.1) := fun Θ => h3 _ (hinl Θ)
  have hC₃ : ∀ e, (tilde e.1).ncard = 3 → C (.inr e) = cap.emb '' closure e.1 := fun e h => h3 _
    (hthree e h)
  have hdisc₃ : ∀ e : {e : Set S // e ∈ P₀.Γ.E ∧ Painting.IsInternal e}, (tilde e.1).ncard = 3
    → IsClosedDisc (closure e.1) ∧ tilde e.1 ⊆ discBd (closure e.1) := fun e h => by
    rcases P₀.Γ.edge_shape e.1 e.2.1 with h' | h'
    · have := h'.1
      omega
    · exact ⟨h'.2.2.1, h'.2.2.2⟩
  refine ⟨C, ?_, h2, ?_, hC₀, hC₃, fun e => ?_⟩
  · rintro (Θ | e)
    · rw [hC₀]
      exact cap.cuffDisc_closedDisc Θ.1 Θ.2
    · rcases P₀.Γ.size_cases e.2.1 with h | h
      · exact (h4 _ ⟨e, rfl, h⟩).1
      · rw [hC₃ e h]
        exact (discBd_emb cap (hdisc₃ e h).1).1
  · rintro (Θ | e)
    · rw [hC₀]
      rintro x ⟨⟨v, hv, rfl⟩, hx⟩
      rw [cap.closure_cuffDisc Θ.2] at hx
      rcases hx with h | h
      · exact absurd (mem_range_self v) (cap.notMem_range Θ.2 h)
      · rw [cap.cuffDisc_bd Θ.1 Θ.2]
        exact h
    · rcases P₀.Γ.size_cases e.2.1 with h | h
      · obtain ⟨-, h5, h6, -⟩ := h4 _ ⟨e, rfl, h⟩
        intro x hx
        apply h6
        rw [← h5]
        exact ⟨hx.2, hx.1⟩
      · rw [hC₃ e h, (discBd_emb cap (hdisc₃ e h).1).2]
        rintro _ ⟨⟨v, hv, rfl⟩, ⟨z, hz, he⟩⟩
        obtain rfl := cap.isEmbedding.injective he
        exact mem_image_of_mem _ ((hdisc₃ e h).2 ⟨hz, fun h' => P₀.Γ.disjoint_V e.2.1 h' hv⟩)
  · rcases P₀.Γ.size_cases e.2.1 with h | h
    · exact (h4 _ ⟨e, rfl, h⟩).2.2.2
    · rw [hC₃ e h]

/-- The vertex of an end, in `Σ̂`. -/
noncomputable def endMap [Nonempty S] (cap : IsCappedSurface S Shat) (P₀ P : ColouredPainting χ)
  (b : Set S → Set S) (x : Shat) : Shat :=
  cap.emb (endVertex P₀ P b (capBack cap x))

omit [T2Space S] [T2Space Shat] in
theorem endMap_emb [Nonempty S] (P₀ P : ColouredPainting χ) (b : Set S → Set S)
  (x : S) : endMap cap P₀ P b (cap.emb x) = cap.emb (endVertex P₀ P b x) := by
  rw [endMap, capBack_emb]

/-- The ends of a border edge, or the vertices of its image, in terms of marches. -/
theorem IsMatchSetting.endVertex_getElem (hM : D.IsMatchSetting P₀ n b)
  (hS : IsSurface S) {e : Set S} (he : e ∈ P₀.Γ.E) {i : ℕ} (hi : i < (P₀.Γ.γ e).length) (hi' : i <
    (D.P.Γ.γ (b e)).length) :
    endVertex P₀ D.P b (D.P.Γ.γ (b e))[i] = (P₀.Γ.γ e)[i] :=
  hM.endVertex_eq hS ⟨e, he, i, hi, hi', rfl, rfl⟩

/-- **The data of a cuff.** -/
theorem IsMatchSetting.exists_cuff_data [Nonempty S] (hM : D.IsMatchSetting P₀ n b)
  (hS : IsSurface S) {Θ : Set S} (hΘ : Θ ∈ cuffs S) {Δ : Set Shat} (hΔ : IsClosedDisc Δ)
    (hsub : Δ ⊆ closure (cap.cuffDisc Θ))
    (hY : cap.emb '' cuffEnds P₀ b Θ ⊆ discBd Δ) {𝓖 : Set (Set Shat)} {ϖ₀ : Set Shat → Shat → Shat
      → Shat → Prop} (hpart : IsPartialOrientation 𝓖 ϖ₀) (hh : ∀ Δ ∈ 𝓖, ∀ Δ' ⊆ Δ, Δ' ∈ 𝓖)
    (hC : closure (cap.cuffDisc Θ) ∈ 𝓖) :
    ∃ (c : Shat → ℂ) (g : ℂ → Shat) (q : Circle → Shat) (A U : Shat → ℝ) (ϖ : Set Shat → Shat
      → Shat → Shat → Prop), (ϖ = ϖ₀ ∨ ϖ = revPos ϖ₀) ∧ IsChart (closure (cap.cuffDisc Θ)) c g
        ∧ IsBdParam Δ q ∧
      PadOrder q g (cap.emb '' cuffEnds P₀ b Θ) (endMap cap P₀ D.P b) A U ∧ (∀ E, IsClosedDisc E
        → E ⊆ closure (cap.cuffDisc Θ) → SameOn ϖ (pullPos c planePos) E) ∧
      ∀ a a' a'', a ≠ a' → a' ≠ a'' → a ≠ a'' → (ϖ Δ (q a) (q a') (q a'') ↔ CircleCyclic a a' a'')
        := by
  have hT := cap.isClosedSurface
  have hCd := cap.cuffDisc_closedDisc Θ hΘ
  obtain ⟨c₀, g₀, hch₀⟩ := hCd.exists_isChart
  obtain ⟨c, g, hch, hP⟩ := hM.exists_cuff_padOrder hS hΘ hch₀
  obtain ⟨ϖ, h1, h2, h3⟩ := exists_chart_sign hT hpart hh hC hCd hch
  have hΔG : Δ ∈ 𝓖 := hh _ hC Δ hsub
  obtain ⟨q, hqc, hqi, hqr, hq⟩ := h2.dir Δ hΔG hΔ
  have hYC : cap.emb '' cuffEnds P₀ b Θ ⊆ discBd (closure (cap.cuffDisc Θ)) := by
    rw [cap.cuffDisc_bd Θ hΘ]
    exact image_mono fun y hy => (hM.cuffEnds_subset hS hΘ hy).1
  have hbd : ∀ {a}, q a ∈ cap.emb '' cuffEnds P₀ b Θ → q a ∈ discBd Δ ∩ discBd (closure
    (cap.cuffDisc Θ)) := fun {a} ha => ⟨hY ha, hYC ha⟩
  obtain ⟨A, U, hO⟩ := hP q hqi (by rw [hqr]; exact hY) fun a a' a'' ha ha' ha'' n1 n2 n3 => by
    have m1 : q a ≠ q a' := fun h => n1 (hqi h)
    have m2 : q a' ≠ q a'' := fun h => n2 (hqi h)
    have m3 : q a ≠ q a'' := fun h => n3 (hqi h)
    exact (hq a a' a'' n1 n2 n3).symm.trans ((h2.agree Δ hΔG _ hC hΔ hCd hsub _ _ _ (hbd ha)
      (hbd ha') (hbd ha'') m1 m2 m3).trans
      ((h3 _ hCd (Subset.refl _) _ _ _ (hbd ha).2 (hbd ha').2 (hbd ha'').2 m1 m2 m3).trans
        (chart_cyc hch (hbd ha).2 (hbd ha').2 (hbd ha'').2)))
  exact ⟨c, g, q, A, U, ϖ, h1, hch, ⟨hqc, hqi, hqr⟩, hO, h3, hq⟩

/-- **The data of an edge of size 2.** -/
theorem IsMatchSetting.exists_two_data [Nonempty S] (hM : D.IsMatchSetting P₀ n b)
  (hS : IsSurface S) {e : Set S} (he : e ∈ P₀.Γ.E) (h2 : (tilde e).ncard
    = 2) {C Δ : Set Shat} {c : Shat → ℂ} {g : ℂ → Shat}
    (hch : IsChart C c g) (hV : cap.emb '' tilde e ⊆ discBd C) {q : Circle → Shat}
      (hq : IsBdParam Δ q) (hY : cap.emb '' tilde (b e) ⊆ discBd Δ) :
    ∃ A U : Shat → ℝ, PadOrder q g (cap.emb '' tilde (b e)) (endMap cap P₀ D.P b) A U := by
  have hbe := hM.edge.mem e he
  obtain ⟨v₀, v₁, hl⟩ := List.length_eq_two.mp ((P₀.Γ.length_γ_eq he).trans h2)
  obtain ⟨y₀, y₁, hl'⟩ := List.length_eq_two.mp ((D.P.Γ.length_γ_eq hbe).trans
    ((hM.edge.size e he).trans h2))
  have hnv : v₀ ≠ v₁ := by
    have := P₀.Γ.γ_nodup e he
    rw [hl] at this
    simpa using this
  have hset : tilde (b e) = {y₀, y₁} := by
    rw [← D.P.Γ.γ_set _ hbe, hl']
    ext x
    simp
  have hsetv : tilde e = {v₀, v₁} := by
    rw [← P₀.Γ.γ_set _ he, hl]
    ext x
    simp
  have hmem : ∀ y ∈ tilde (b e), ∃ a, q a = cap.emb y := fun y hy => by
    have : cap.emb y ∈ range q := by rw [hq.2.2]; exact hY (mem_image_of_mem _ hy)
    exact this
  obtain ⟨a₀, ha₀⟩ := hmem y₀ (by rw [hset]; simp)
  obtain ⟨a₁, ha₁⟩ := hmem y₁ (by rw [hset]; simp)
  have e₀ : endMap cap P₀ D.P b (q a₀) = cap.emb v₀ := by
    rw [ha₀, endMap_emb]
    have := hM.endVertex_getElem hS he (i := 0) (by simp [hl]) (by simp [hl'])
    simpa [hl, hl'] using congrArg cap.emb this
  have e₁ : endMap cap P₀ D.P b (q a₁) = cap.emb v₁ := by
    rw [ha₁, endMap_emb]
    have := hM.endVertex_getElem hS he (i := 1) (by simp [hl]) (by simp [hl'])
    simpa [hl, hl'] using congrArg cap.emb this
  have hsetq : cap.emb '' tilde (b e) = {q a₀, q a₁} := by rw [hset, image_pair, ha₀, ha₁]
  rw [hsetq]
  refine padOrder_of_pair hch hq.2.1 ?_ ?_
  · rintro y (rfl | rfl)
    · rw [e₀]
      exact hV (mem_image_of_mem _ (by rw [hsetv]; simp))
    · rw [e₁]
      exact hV (mem_image_of_mem _ (by rw [hsetv]; simp))
  · rw [e₀, e₁]
    exact fun h => hnv (cap.isEmbedding.injective h)

/-- **The data of an edge of size 3**, once the two triples are compared. -/
theorem IsMatchSetting.exists_three_data [Nonempty S] (hM : D.IsMatchSetting P₀ n b)
  (hS : IsSurface S) {e : Set S} (he : e ∈ P₀.Γ.E) {C Δ : Set Shat} {c : Shat → ℂ} {g : ℂ → Shat}
    (hch : IsChart C c g)
    {v₀ v₁ v₂ y₀ y₁ y₂ : S} (hl : P₀.Γ.γ e = [v₀, v₁, v₂]) (hl' : D.P.Γ.γ (b e) = [y₀, y₁, y₂])
      (hV : cap.emb '' tilde e ⊆ discBd C) {q : Circle → Shat} (hq : IsBdParam Δ q)
        (hY : cap.emb '' tilde (b e) ⊆ discBd Δ)
    (hcheck : ∀ a₀ a₁ a₂, q a₀ = cap.emb y₀ → q a₁ = cap.emb y₁ → q a₂ = cap.emb y₂ →
      (CircleCyclic a₀ a₁ a₂ ↔ CircleCyclic (toCircle (c (cap.emb v₀))) (toCircle (c (cap.emb v₁)))
        (toCircle (c (cap.emb v₂))))) :
    ∃ A U : Shat → ℝ, PadOrder q g (cap.emb '' tilde (b e)) (endMap cap P₀ D.P b) A U := by
  have hbe := hM.edge.mem e he
  have hnv := P₀.Γ.γ_nodup e he
  have hny := D.P.Γ.γ_nodup _ hbe
  rw [hl] at hnv
  rw [hl'] at hny
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil,
    not_false_eq_true, and_true] at hnv hny
  obtain ⟨⟨n01, n02⟩, n12⟩ := hnv
  obtain ⟨⟨m01, m02⟩, m12⟩ := hny
  have hset : tilde (b e) = {y₀, y₁, y₂} := by
    rw [← D.P.Γ.γ_set _ hbe, hl']
    ext x
    simp
  have hsetv : tilde e = {v₀, v₁, v₂} := by
    rw [← P₀.Γ.γ_set _ he, hl]
    ext x
    simp
  have hmem : ∀ y ∈ tilde (b e), ∃ a, q a = cap.emb y := fun y hy => by
    have : cap.emb y ∈ range q := by rw [hq.2.2]; exact hY (mem_image_of_mem _ hy)
    exact this
  obtain ⟨a₀, ha₀⟩ := hmem y₀ (by rw [hset]; simp)
  obtain ⟨a₁, ha₁⟩ := hmem y₁ (by rw [hset]; simp)
  obtain ⟨a₂, ha₂⟩ := hmem y₂ (by rw [hset]; simp)
  have hend : ∀ (i : ℕ) (hi : i < (P₀.Γ.γ e).length) (hi' : i < (D.P.Γ.γ
    (b e)).length), endMap cap P₀ D.P b (cap.emb (D.P.Γ.γ (b e))[i]) = cap.emb (P₀.Γ.γ e)[i]
      := fun i hi hi' => by
    rw [endMap_emb, hM.endVertex_getElem hS he hi hi']
  have e₀ : endMap cap P₀ D.P b (q a₀) = cap.emb v₀ := by
    have := hend 0 (by simp [hl]) (by simp [hl'])
    simpa [hl, hl', ha₀] using this
  have e₁ : endMap cap P₀ D.P b (q a₁) = cap.emb v₁ := by
    have := hend 1 (by simp [hl]) (by simp [hl'])
    simpa [hl, hl', ha₁] using this
  have e₂ : endMap cap P₀ D.P b (q a₂) = cap.emb v₂ := by
    have := hend 2 (by simp [hl]) (by simp [hl'])
    simpa [hl, hl', ha₂] using this
  have hemb := cap.isEmbedding.injective
  have hsetq : cap.emb '' tilde (b e) = {q a₀, q a₁, q a₂} := by
    rw [hset, image_insert_eq, image_pair, ha₀, ha₁, ha₂]
  rw [hsetq]
  have hne : ∀ {x y : S} {p p' : Circle}, q p = cap.emb x → q p' = cap.emb y → x ≠ y → p ≠ p'
    := fun e1 e2 h he => h (hemb (by rw [← e1, ← e2, he]))
  refine padOrder_of_triple hch hq.2.1 (hne ha₀ ha₁ m01) (hne ha₁ ha₂ m12)
    (hne ha₀ ha₂ m02) ?_ ?_ ?_ ?_ ?_
  · rintro y (rfl | rfl | rfl)
    · rw [e₀]
      exact hV (mem_image_of_mem _ (by rw [hsetv]; simp))
    · rw [e₁]
      exact hV (mem_image_of_mem _ (by rw [hsetv]; simp))
    · rw [e₂]
      exact hV (mem_image_of_mem _ (by rw [hsetv]; simp))
  · rw [e₀, e₁]
    exact fun h => n01 (hemb h)
  · rw [e₁, e₂]
    exact fun h => n12 (hemb h)
  · rw [e₀, e₂]
    exact fun h => n02 (hemb h)
  · rw [e₀, e₁, e₂]
    exact hcheck a₀ a₁ a₂ ha₀ ha₁ ha₂

omit [T2Space S] in
theorem edge_disc (Γ : Painting S) {e : Set S} (he : e ∈ Γ.E) (h3 : (tilde e).ncard
  = 3) : IsClosedDisc (closure e) ∧ tilde e ⊆ discBd (closure e) := by
  rcases Γ.edge_shape e he with h' | h'
  · have := h'.1
    omega
  · exact ⟨h'.2.2.1, h'.2.2.2⟩

omit [T2Space S] [T2Space Shat] in
/-- A triple that is positive for an orientation of `Σ` is positive for the orientation carried to
`Σ̂`. -/
theorem pos_emb [Nonempty S] {o : SurfaceOrientation S} {ω : SurfaceOrientation Shat}
    (hω : ∀ Δ, IsClosedDisc Δ → Δ ⊆ range cap.emb → SameOn ω.pos (pullPos
      (capBack cap) o.pos) Δ) {X : Set S} (hX : IsClosedDisc X) {x y z : S} (hx : x ∈ discBd X)
        (hy : y ∈ discBd X) (hz : z ∈ discBd X) (n1 : x ≠ y)
    (n2 : y ≠ z) (n3 : x ≠ z) (h : o.pos X x y z) : ω.pos (cap.emb '' X) (cap.emb x) (cap.emb y)
      (cap.emb z) := by
  have hbd := (discBd_emb cap hX).2
  have hinj := cap.isEmbedding.injective
  have hmem {w : S} (hw : w ∈ discBd X) : cap.emb w ∈ discBd (cap.emb '' X) := by
    rw [hbd]
    exact mem_image_of_mem _ hw
  have hs := hω _ (discBd_emb cap hX).1 (image_subset_range _ _) (cap.emb x) (cap.emb y)
    (cap.emb z) (hmem hx) (hmem hy) (hmem hz) (fun e => n1 (hinj e)) (fun e => n2 (hinj e))
    (fun e => n3 (hinj e))
  refine hs.2 ?_
  change o.pos (capBack cap '' (cap.emb '' X)) (capBack cap (cap.emb x)) (capBack cap (cap.emb y))
    (capBack cap (cap.emb z))
  have him : capBack cap '' (cap.emb '' X) = X := by
    rw [image_image]
    simp [capBack_emb]
  rw [him, capBack_emb, capBack_emb, capBack_emb]
  exact h

/-- **The data of an edge when `Σ` is oriented.** The hypothesis on orientations compares the disc
of `β(e)` with the disc of `e`. -/
theorem IsMatchSetting.exists_edge_data_oriented [Nonempty S] (hM : D.IsMatchSetting P₀ n b)
  (hS : IsSurface S) {o : SurfaceOrientation S} {ω : SurfaceOrientation Shat}
    (ho : ∀ P ∈ ({P₀, D.P} : Set _), ∀ e ∈ P.Γ.E, (tilde e).ncard = 3 → ∀ a b c : S, P.Γ.γ e
      = [a, b, c] → o.pos (closure e) a b c)
    (hω : ∀ Δ, IsClosedDisc Δ → Δ ⊆ range cap.emb → SameOn ω.pos (pullPos
      (capBack cap) o.pos) Δ) {e : Set S} (he : e ∈ P₀.Γ.E) {C Δ : Set Shat} (hCd : IsClosedDisc C)
        (hV : cap.emb '' tilde e ⊆ discBd C)
    (hC3 : (tilde e).ncard = 3 → C = cap.emb '' closure e) (hΔ : IsClosedDisc Δ)
      (hY : cap.emb '' tilde (b e) ⊆ discBd Δ) (hsub : (tilde (b e)).ncard = 3
        → Δ ⊆ cap.emb '' closure (b e)) :
    ∃ (c : Shat → ℂ) (g : ℂ → Shat) (q : Circle → Shat) (A U : Shat → ℝ) (ϖ : Set Shat → Shat
      → Shat → Shat → Prop), (ϖ = ω.pos ∨ ϖ = revPos ω.pos) ∧ IsChart C c g ∧ IsBdParam Δ q ∧
      PadOrder q g (cap.emb '' tilde (b e)) (endMap cap P₀ D.P b) A U ∧ (∀ E, IsClosedDisc E
        → E ⊆ C → SameOn ϖ (pullPos c planePos) E) ∧
      ∀ a a' a'', a ≠ a' → a' ≠ a'' → a ≠ a'' → (ϖ Δ (q a) (q a') (q a'') ↔ CircleCyclic a a' a'')
        := by
  have hT := cap.isClosedSurface
  obtain ⟨c, g, hch⟩ := hCd.exists_isChart
  have hω₀ := ω.isPartial univ
  obtain ⟨ϖ, h1, h2, h3⟩ := exists_chart_sign hT hω₀ (fun _ _ _ _ => mem_univ _)
    (mem_univ C) hCd hch
  obtain ⟨q, hqc, hqi, hqr, hq⟩ := h2.dir Δ (mem_univ _) hΔ
  have hqp : IsBdParam Δ q := ⟨hqc, hqi, hqr⟩
  suffices h : ∃ A U : Shat → ℝ, PadOrder q g (cap.emb '' tilde (b e)) (endMap cap P₀ D.P b) A U by
    obtain ⟨A, U, hO⟩ := h
    exact ⟨c, g, q, A, U, ϖ, h1, hch, hqp, hO, h3, hq⟩
  rcases P₀.Γ.size_cases he with h2' | h3'
  · exact hM.exists_two_data hS he h2' hch hV hqp hY
  have hbe := hM.edge.mem e he
  have hbs : (tilde (b e)).ncard = 3 := (hM.edge.size e he).trans h3'
  obtain ⟨v₀, v₁, v₂, hl⟩ := List.length_eq_three.mp ((P₀.Γ.length_γ_eq he).trans h3')
  obtain ⟨y₀, y₁, y₂, hl'⟩ := List.length_eq_three.mp ((D.P.Γ.length_γ_eq hbe).trans hbs)
  refine hM.exists_three_data hS he hch hl hl' hV hqp hY fun a₀ a₁ a₂ e₀ e₁ e₂ => ?_
  have hnv := P₀.Γ.γ_nodup e he
  have hny := D.P.Γ.γ_nodup _ hbe
  rw [hl] at hnv
  rw [hl'] at hny
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil,
    not_false_eq_true, and_true] at hnv hny
  obtain ⟨⟨n01, n02⟩, n12⟩ := hnv
  obtain ⟨⟨m01, m02⟩, m12⟩ := hny
  have hemb := cap.isEmbedding.injective
  have dt : tilde (b e) = {y₀, y₁, y₂} := by
    rw [← D.P.Γ.γ_set _ hbe, hl']
    ext x
    simp
  have dv : tilde e = {v₀, v₁, v₂} := by
    rw [← P₀.Γ.γ_set _ he, hl]
    ext x
    simp
  obtain ⟨hFd, hFt⟩ := edge_disc D.P.Γ hbe hbs
  obtain ⟨hEd, hEt⟩ := edge_disc P₀.Γ he h3'
  have hy₀ : y₀ ∈ discBd (closure (b e)) := hFt (by rw [dt]; simp)
  have hy₁ : y₁ ∈ discBd (closure (b e)) := hFt (by rw [dt]; simp)
  have hy₂ : y₂ ∈ discBd (closure (b e)) := hFt (by rw [dt]; simp)
  have hv₀ : v₀ ∈ discBd (closure e) := hEt (by rw [dv]; simp)
  have hv₁ : v₁ ∈ discBd (closure e) := hEt (by rw [dv]; simp)
  have hv₂ : v₂ ∈ discBd (closure e) := hEt (by rw [dv]; simp)
  have hmemP : P₀ ∈ ({P₀, D.P} : Set _) := by simp
  have hmemD : D.P ∈ ({P₀, D.P} : Set _) := by simp
  have posF := pos_emb hω hFd hy₀ hy₁ hy₂ m01 m12 m02 (ho D.P hmemD _ hbe hbs _ _ _ hl')
  have posC := pos_emb hω hEd hv₀ hv₁ hv₂ n01 n12 n02 (ho P₀ hmemP _ he h3' _ _ _ hl)
  have hF := discBd_emb cap hFd
  have hE := discBd_emb cap hEd
  have bdF {y} (h : y ∈ discBd (closure (b e))) :
      cap.emb y ∈ discBd (cap.emb '' closure (b e)) := by
    rw [hF.2]
    exact mem_image_of_mem _ h
  have bdE {y} (h : y ∈ discBd (closure e)) :
      cap.emb y ∈ discBd (cap.emb '' closure e) := by
    rw [hE.2]
    exact mem_image_of_mem _ h
  have ne : ∀ {x y : S}, x ≠ y → cap.emb x ≠ cap.emb y := fun h h' => h (hemb h')
  have hsw : ∀ X : Set Shat, IsClosedDisc X → ∀ {x y z}, x ∈ discBd X → y ∈ discBd X → z ∈ discBd X
    → x ≠ y → y ≠ z → x ≠ z → ω.pos X x y z → ¬ ω.pos X x z y := fun X hX {x y z} hx hy hz n1 n2 n3
      h =>
    ((hω₀.dir X (mem_univ _) hX).swap hx hy hz n1 n2 n3).1 h
  have hbridge : ϖ (cap.emb '' closure (b e)) (cap.emb y₀) (cap.emb y₁) (cap.emb y₂) ↔ ϖ
    (cap.emb '' closure e) (cap.emb v₀) (cap.emb v₁) (cap.emb v₂) := by
    rcases h1 with rfl | rfl
    · exact iff_of_true posF posC
    · exact iff_of_false (hsw _ hF.1 (bdF hy₀) (bdF hy₁) (bdF hy₂) (ne m01) (ne m12) (ne m02) posF)
        (hsw _ hE.1 (bdE hv₀) (bdE hv₁) (bdE hv₂) (ne n01) (ne n12) (ne n02) posC)
  have hna : a₀ ≠ a₁ ∧ a₁ ≠ a₂ ∧ a₀ ≠ a₂ := by
    refine ⟨fun h => m01 (hemb ?_), fun h => m12 (hemb ?_), fun h => m02 (hemb ?_)⟩
    · rw [← e₀, ← e₁, h]
    · rw [← e₁, ← e₂, h]
    · rw [← e₀, ← e₂, h]
  have hCe := hC3 h3'
  subst hCe
  have hbdΔ : ∀ {y}, y ∈ tilde (b e) → cap.emb y ∈ discBd Δ := fun h => hY (mem_image_of_mem _ h)
  have t₀ : y₀ ∈ tilde (b e) := by rw [dt]; simp
  have t₁ : y₁ ∈ tilde (b e) := by rw [dt]; simp
  have t₂ : y₂ ∈ tilde (b e) := by rw [dt]; simp
  have step := h2.agree Δ (mem_univ _) _ (mem_univ _) hΔ hF.1 (hsub hbs) _ _ _ ⟨hbdΔ t₀, bdF hy₀⟩
    ⟨hbdΔ t₁, bdF hy₁⟩ ⟨hbdΔ t₂, bdF hy₂⟩ (ne m01) (ne m12) (ne m02)
  have h0 := hq a₀ a₁ a₂ hna.1 hna.2.1 hna.2.2
  rw [e₀, e₁, e₂] at h0
  exact h0.symm.trans (step.trans (hbridge.trans ((h3 _ hCd (Subset.refl _) _ _ _ (bdE hv₀)
    (bdE hv₁) (bdE hv₂) (ne n01) (ne n12) (ne n02)).trans (chart_cyc hch (bdE hv₀) (bdE hv₁)
      (bdE hv₂)))))

/-- **The data of an edge with no orientation to respect.** With three ends, we choose the direction
of the parameter of `Δ` so that it agrees with the chart. -/
theorem IsMatchSetting.exists_edge_data_free [Nonempty S] (hM : D.IsMatchSetting P₀ n b)
  (hS : IsSurface S) {e : Set S} (he : e ∈ P₀.Γ.E) {C Δ : Set Shat} (hCd : IsClosedDisc C)
    (hV : cap.emb '' tilde e ⊆ discBd C)
    (hΔ : IsClosedDisc Δ) (hY : cap.emb '' tilde (b e) ⊆ discBd Δ) :
    ∃ (c : Shat → ℂ) (g : ℂ → Shat) (q : Circle → Shat) (A U : Shat → ℝ), IsChart C c g
      ∧ IsBdParam Δ q ∧ PadOrder q g (cap.emb '' tilde (b e)) (endMap cap P₀ D.P b) A U := by
  obtain ⟨c, g, hch⟩ := hCd.exists_isChart
  obtain ⟨pos, hp⟩ := exists_local_orientation hΔ
  have hmemΔ : Δ ∈ {X | X ⊆ Δ} := Subset.refl Δ
  have hdir := hp.dir Δ hmemΔ hΔ
  obtain ⟨qp, hcp, hip, hrp, hp₁⟩ := hdir
  obtain ⟨qm, hcm, him, hrm, hm₁⟩ := hp.rev.dir Δ hmemΔ hΔ
  have hdir := hp.dir Δ hmemΔ hΔ
  have hqp : IsBdParam Δ qp := ⟨hcp, hip, hrp⟩
  have hqm : IsBdParam Δ qm := ⟨hcm, him, hrm⟩
  rcases P₀.Γ.size_cases he with h2' | h3'
  · obtain ⟨A, U, hO⟩ := hM.exists_two_data hS he h2' hch hV hqp hY
    exact ⟨c, g, qp, A, U, hch, hqp, hO⟩
  have hbe := hM.edge.mem e he
  have hbs : (tilde (b e)).ncard = 3 := (hM.edge.size e he).trans h3'
  obtain ⟨v₀, v₁, v₂, hl⟩ := List.length_eq_three.mp ((P₀.Γ.length_γ_eq he).trans h3')
  obtain ⟨y₀, y₁, y₂, hl'⟩ := List.length_eq_three.mp ((D.P.Γ.length_γ_eq hbe).trans hbs)
  have hny := D.P.Γ.γ_nodup _ hbe
  rw [hl'] at hny
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil,
    not_false_eq_true, and_true] at hny
  obtain ⟨⟨m01, m02⟩, m12⟩ := hny
  have hemb := cap.isEmbedding.injective
  have dt : tilde (b e) = {y₀, y₁, y₂} := by
    rw [← D.P.Γ.γ_set _ hbe, hl']
    ext x
    simp
  have t₀ : y₀ ∈ tilde (b e) := by rw [dt]; simp
  have t₁ : y₁ ∈ tilde (b e) := by rw [dt]; simp
  have t₂ : y₂ ∈ tilde (b e) := by rw [dt]; simp
  have ne : ∀ {x y : S}, x ≠ y → cap.emb x ≠ cap.emb y := fun h h' => h (hemb h')
  have hna : ∀ {p : Circle → Shat} {a₀ a₁ a₂ : Circle}, p a₀ = cap.emb y₀ → p a₁ = cap.emb y₁
    → p a₂ = cap.emb y₂ → a₀ ≠ a₁ ∧ a₁ ≠ a₂ ∧ a₀ ≠ a₂ := fun {p a₀ a₁ a₂} e₀ e₁ e₂ => by
    refine ⟨fun h => m01 (hemb ?_), fun h => m12 (hemb ?_), fun h => m02 (hemb ?_)⟩
    · rw [← e₀, ← e₁, h]
    · rw [← e₁, ← e₂, h]
    · rw [← e₀, ← e₂, h]
  have hbdΔ : ∀ {y}, y ∈ tilde (b e) → cap.emb y ∈ discBd Δ := fun h => hY (mem_image_of_mem _ h)
  by_cases hd : pos Δ (cap.emb y₀) (cap.emb y₁) (cap.emb y₂) ↔ CircleCyclic (toCircle (c
    (cap.emb v₀))) (toCircle (c (cap.emb v₁))) (toCircle (c (cap.emb v₂)))
  · obtain ⟨A, U, hO⟩ := hM.exists_three_data hS he hch hl hl' hV hqp hY fun a₀ a₁ a₂ e₀ e₁ e₂ => by
      obtain ⟨n1, n2, n3⟩ := hna e₀ e₁ e₂
      have h0 := hp₁ a₀ a₁ a₂ n1 n2 n3
      rw [e₀, e₁, e₂] at h0
      exact h0.symm.trans hd
    exact ⟨c, g, qp, A, U, hch, hqp, hO⟩
  · obtain ⟨A, U, hO⟩ := hM.exists_three_data hS he hch hl hl' hV hqm hY fun a₀ a₁ a₂ e₀ e₁ e₂ => by
      obtain ⟨n1, n2, n3⟩ := hna e₀ e₁ e₂
      have h0 := hm₁ a₀ a₁ a₂ n1 n2 n3
      rw [e₀, e₁, e₂] at h0
      have hs := hdir.swap (hbdΔ t₀) (hbdΔ t₂) (hbdΔ t₁) (ne m02) (ne fun h => m12 h.symm) (ne m01)
      have h0' : pos Δ (cap.emb y₀) (cap.emb y₂) (cap.emb y₁) ↔ CircleCyclic a₀ a₁ a₂ := h0
      rw [← h0', hs]
      tauto
    exact ⟨c, g, qm, A, U, hch, hqm, hO⟩

theorem IsMatchSetting.endVertex_mem (hM : D.IsMatchSetting P₀ n b) (hS : IsSurface S) {e : Set S}
  (he : e ∈ P₀.Γ.E) {x : S} (hx : x ∈ tilde (b e)) : endVertex P₀ D.P b x ∈ tilde e := by
  obtain ⟨v, hv, h⟩ := exists_isEndOf hM.edge he hx
  rwa [hM.endVertex_eq hS h]

/-- **The last step.** The discs given by `exists_realizing_discs` are the discs we want, because
the end classes are the sets of ends sent to one vertex. -/
theorem IsMatchSetting.finish_feasibility [Nonempty S] (hM : D.IsMatchSetting P₀ n b)
  (hS : IsSurface S) {Δ C : DiscIndex S P₀ → Set Shat} (hΔ : ∀ i, IsClosedDisc (Δ i))
    (hΔΔ : ∀ i j, i ≠ j → Disjoint (Δ i) (Δ j))
    (hC : ∀ i, IsClosedDisc (C i)) (hCC : ∀ i j, i ≠ j → C i ∩ C j ⊆ cap.emb '' P₀.Γ.V)
      (hVC : ∀ i, cap.emb '' P₀.Γ.V ∩ C i ⊆ discBd (C i)) (hC₀ : ∀ Θ, C (.inl Θ) = closure
        (cap.cuffDisc Θ.1))
    (hsub : ∀ e, cap.emb '' closure e.1 ⊆ C (.inr e)) {c : DiscIndex S P₀ → Shat
      → ℂ} {g : DiscIndex S P₀ → ℂ → Shat} {q : DiscIndex S P₀ → Circle
        → Shat} {A U : DiscIndex S P₀ → Shat → ℝ} (hch : ∀ i, IsChart (C i) (c i) (g i))
    (hq : ∀ i, IsBdParam (Δ i) (q i)) (hO : ∀ i, PadOrder (q i) (g i) (discEnds cap b P₀ i)
      (endMap cap P₀ D.P b) (A i) (U i))
    (H : ¬ IsOrientableSurface Shat ∨ ∃ ω : SurfaceOrientation Shat, ∀ i, ∃ ϖ, (ϖ = ω.pos ∨ ϖ
      = revPos ω.pos) ∧ (∀ E, IsClosedDisc E → E ⊆ C i → SameOn ϖ (pullPos (c i) planePos) E) ∧
      ∀ a a' a'', a ≠ a' → a' ≠ a'' → a ≠ a'' → (ϖ (Δ i) (q i a) (q i a')
        (q i a'') ↔ CircleCyclic a a' a'')) :
    ∃ Dv : S → Set Shat, (∀ v ∈ P₀.Γ.V, IsClosedDisc (Dv v)) ∧ (∀ v ∈ P₀.Γ.V, ∀ v' ∈ P₀.Γ.V, v ≠ v'
      → Disjoint (Dv v) (Dv v')) ∧ ∀ v ∈ P₀.Γ.V, Dv v ∩ ⋃ i, Δ i = endClass cap P₀ D.P b v := by
  have hT := cap.isClosedSurface
  have hconn : ConnectedSpace Shat := cap.connected
  have := finite_discIndex hS P₀
  have hemb := cap.isEmbedding.injective
  have hφ : ∀ i, ∀ y ∈ discEnds cap b P₀ i, endMap cap P₀ D.P b y ∈ cap.emb '' P₀.Γ.V ∩ C i := by
    rintro (Θ | e)
    · rintro _ ⟨x, ⟨e, he, heΘ, hx⟩, rfl⟩
      have hm := hM.endVertex_mem hS he hx
      rw [endMap_emb, hC₀ Θ]
      refine ⟨mem_image_of_mem _ (P₀.Γ.tilde_subset_V he hm), ?_⟩
      have hΘc : IsClosed Θ.1 := (IsOArc.isCompact ((cuff_statement S hS).2.2 Θ.1 Θ.2)).isClosed
      rw [cap.closure_cuffDisc Θ.2]
      exact Or.inr (mem_image_of_mem _ (closure_minimal heΘ hΘc hm.1))
    · rintro _ ⟨x, hx, rfl⟩
      have hm := hM.endVertex_mem hS e.2.1 hx
      rw [endMap_emb]
      exact ⟨mem_image_of_mem _ (P₀.Γ.tilde_subset_V e.2.1 hm), hsub e (mem_image_of_mem _ hm.1)⟩
  obtain ⟨D', h1, h2, h3⟩ := exists_realizing_discs hT hΔ (fun i j h => hΔΔ i j h) hC hch
    (P₀.Γ.finite_V.image _) hCC hVC hφ hq hO H
  refine ⟨fun v => D' (cap.emb v), fun v hv => h1 _ (mem_image_of_mem _ hv), fun v hv v' hv' hne
    => h2 _ (mem_image_of_mem _ hv) _ (mem_image_of_mem _ hv') fun h => hne (hemb h), fun v hv
      => ?_⟩
  rw [h3 _ (mem_image_of_mem _ hv)]
  ext y
  simp only [mem_iUnion, mem_ofPred_eq]
  constructor
  · rintro ⟨i, hy, hyv⟩
    have hall : ∃ e ∈ P₀.Γ.E, ∃ x ∈ tilde (b e), y = cap.emb x := by
      rcases i with Θ | e
      · obtain ⟨x, ⟨e, he, -, hx⟩, rfl⟩ := hy
        exact ⟨e, he, x, hx, rfl⟩
      · obtain ⟨x, hx, rfl⟩ := hy
        exact ⟨e.1, e.2.1, x, hx, rfl⟩
    obtain ⟨e, he, x, hx, rfl⟩ := hall
    rw [endMap_emb] at hyv
    obtain ⟨v', -, h⟩ := exists_isEndOf hM.edge he hx
    have hvv : v' = v := by
      rw [← hM.endVertex_eq hS h]
      exact hemb hyv
    subst hvv
    exact ⟨x, h, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    have hend := hM.endVertex_eq hS hx
    obtain ⟨e, he, i, hi, hi', -, h2'⟩ := hx
    have hxt : x ∈ tilde (b e) := by
      rw [← D.P.Γ.γ_set _ (hM.edge.mem e he), mem_ofPred_eq, ← h2']
      exact List.getElem_mem _
    rw [show endMap cap P₀ D.P b (cap.emb x) = cap.emb v by rw [endMap_emb, hend]]
    by_cases hB : Painting.IsBorder e
    · obtain ⟨s, -, Θ, hΘ, hsΘ, hes, -⟩ := hM.exists_cuff_of_border hS he hB
      have heΘ : e ⊆ Θ := hes.trans hsΘ
      exact ⟨.inl ⟨Θ, hΘ⟩, ⟨x, ⟨e, he, heΘ, hxt⟩, rfl⟩, rfl⟩
    · exact ⟨.inr ⟨e, he, isInternal_iff_not_border.2 hB⟩, ⟨x, hxt, rfl⟩, rfl⟩

end TangleDatum

/-- **Steps (2) and (3) of the proof of Graph Minors XIX, (15.2)**, pages 381 and 382. -/
theorem theorem152Feasibility : Theorem152FeasibilityStatement.{w} := by
  intro S Shat _ _ _ _ β cap χ P₀ D n b horient hM Δ hΔ hends hdis hcuff hedge
  have hS := χ.isSurface
  have hS₀ : Nonempty S := by
    have := χ.connected
    infer_instance
  obtain ⟨C, hC, hCC, hVC, hC₀, hC₃, hsub⟩ := TangleDatum.exists_pads hS P₀ cap
  have hV : ∀ e : {e : Set S // e ∈ P₀.Γ.E ∧ Painting.IsInternal e}, cap.emb '' tilde e.1 ⊆ discBd
    (C (.inr e)) := fun e => by
    rintro _ ⟨x, hx, rfl⟩
    exact hVC _ ⟨mem_image_of_mem _ (P₀.Γ.tilde_subset_V e.2.1 hx),
      hsub e (mem_image_of_mem _ hx.1)⟩
  by_cases hor : IsOrientableSurface Shat
  · obtain ⟨o, ho⟩ := horient.resolve_left (not_not.2 (isOrientable_of_embedding cap.isEmbedding
      hor))
    obtain ⟨ω, hω⟩ := exists_cap_orientation hS cap o
    have key : ∀ i, ∃ (c : Shat → ℂ) (g : ℂ → Shat) (q : Circle → Shat) (A U : Shat → ℝ)
      (ϖ : Set Shat → Shat → Shat → Shat → Prop), (ϖ = ω.pos ∨ ϖ = revPos ω.pos) ∧ IsChart
        (C i) c g ∧ IsBdParam (Δ i) q ∧
        PadOrder q g (TangleDatum.discEnds cap b P₀ i) (TangleDatum.endMap cap P₀ D.P b) A U ∧
          (∀ E, IsClosedDisc E → E ⊆ C i → SameOn ϖ (pullPos c planePos) E) ∧
        ∀ a a' a'', a ≠ a' → a' ≠ a'' → a ≠ a'' → (ϖ (Δ i) (q a) (q a')
          (q a'') ↔ CircleCyclic a a' a'') := by
      rintro (Θ | e)
      · rw [hC₀ Θ]
        exact hM.exists_cuff_data hS Θ.2 (hΔ _) (hcuff Θ) (hends (.inl Θ)) (ω.isPartial univ)
          (fun _ _ _ _ => mem_univ _) (mem_univ _)
      · exact hM.exists_edge_data_oriented hS ho hω e.2.1 (hC _) (hV e) (hC₃ e) (hΔ _) (hends
          (.inr e)) (hedge e)
    choose c g q A U ϖ h1 h2 h3 h4 h5 h6 using key
    exact hM.finish_feasibility hS hΔ hdis hC hCC hVC hC₀ hsub h2 h3 h4 (Or.inr ⟨ω,
      fun i => ⟨ϖ i, h1 i, h5 i, h6 i⟩⟩)
  · have key : ∀ i, ∃ (c : Shat → ℂ) (g : ℂ → Shat) (q : Circle → Shat) (A U : Shat → ℝ), IsChart
      (C i) c g ∧ IsBdParam (Δ i) q ∧
        PadOrder q g (TangleDatum.discEnds cap b P₀ i) (TangleDatum.endMap cap P₀ D.P b) A U := by
      rintro (Θ | e)
      · rw [hC₀ Θ]
        have hF := cap.cuffDisc_closedDisc Θ.1 Θ.2
        obtain ⟨pos, hp⟩ := exists_local_orientation hF
        obtain ⟨c, g, q, A, U, -, -, h2, h3, h4, -, -⟩ := hM.exists_cuff_data hS Θ.2 (hΔ _)
          (hcuff Θ) (hends (.inl Θ)) hp (fun _ h _ hs => hs.trans h) (Subset.refl _)
        exact ⟨c, g, q, A, U, h2, h3, h4⟩
      · exact hM.exists_edge_data_free hS e.2.1 (hC _) (hV e) (hΔ _) (hends (.inr e))
    choose c g q A U h2 h3 h4 using key
    exact hM.finish_feasibility hS hΔ hdis hC hCC hVC hC₀ hsub h2 h3 h4 (Or.inl hor)

end GraphMinor.GM19
