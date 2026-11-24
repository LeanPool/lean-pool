/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Matched
public import LeanPool.GraphMinor.GM11.EdgeSides
public import LeanPool.GraphMinor.GM07.DiscPlace
import LeanPool.GraphMinor.GM06.Section3Dual

/-!
# Removing the middle of each edge

For step 2 of (9.1), page 243: "Let $H' = (U(H) - Y, V(H) \cup Z)$ ... Then $H'$ is a forest in
$\Sigma$, and its components are in a natural correspondence with
$V(H)$." Here we remove from each edge `f` of a graph `H` the middle part of `f`. Each edge of the
new drawing joins a vertex of `H` to one of the new
vertices, and each new vertex has just one edge.
-/

public section

namespace GraphMinor.GM07

open Set Topology Function GraphMinor.Surface GraphMinor.GM11 unitInterval

universe u

variable {S : Type u} [TopologicalSpace S]

/-- A graph in which each edge has one end in `P`, and each vertex in `P` has one edge, is a forest.
-/
theorem isGraphForest_of_leaves {α β : Type*} (G : Graph α β) (P : Set α)
  (h1 : ∀ {e x y}, G.IsLink e x y → (x ∈ P ∧ y ∉ P) ∨ (x ∉ P ∧ y ∈ P))
    (h2 : ∀ x ∈ P, ∀ {e f y z}, G.IsLink e x y → G.IsLink f x z → e = f) : IsGraphForest G := by
  -- The end of a walk with distinct ends lies on one of its edges.
  have hlast : ∀ {a b : α} (W : GraphWalk G a b), a ≠ b → ∃ e ∈ W.edges, ∃ y, G.IsLink e b y := by
    intro a b W
    induction W with
    | nil _ => exact fun h => absurd rfl h
    | @cons a' b' c' e hl rest ih =>
      intro _
      by_cases hbc : b' = c'
      · subst hbc
        exact ⟨e, by simp [GraphWalk.edges], a', hl.symm⟩
      · obtain ⟨e', he', y, hy⟩ := ih hbc
        exact ⟨e', by simp [GraphWalk.edges, he'], y, hy⟩
  intro u W hW
  cases W with
  | nil hv => rfl
  | @cons _ b _ e hl rest =>
    exfalso
    have hnodup : (GraphWalk.edges (.cons hl rest)).Nodup := hW.2
    have he : e ∉ rest.edges := by
      simp only [GraphWalk.edges, List.nodup_cons] at hnodup
      exact hnodup.1
    rcases h1 hl with ⟨hu, hb⟩ | ⟨hu, hb⟩
    · have hne : b ≠ u := fun h => hb (h ▸ hu)
      obtain ⟨e', he', y, hy⟩ := hlast rest hne
      rw [h2 u hu hl hy] at he
      exact he he'
    · cases rest with
      | nil _ => exact hu hb
      | @cons _ c _ e₂ hl₂ rest₂ =>
        have := h2 b hb hl.symm hl₂
        apply he
        rw [this]
        simp [GraphWalk.edges]

/-- `γ` runs along the edge `f` of `H`, from one end to the other. -/
structure EdgeParam (H : Drawing S) (f : Set S) (γ : I → S) : Prop where
  cont : Continuous γ
  mem0 : γ 0 ∈ H.V
  mem1 : γ 1 ∈ H.V
  inj : InjOn γ (Ioo 0 1)
  img : γ '' Ioo 0 1 = f

/-- The same edge, the other way. -/
theorem EdgeParam.rev {H : Drawing S} {f : Set S} {γ : I → S} (h : EdgeParam H f γ) : EdgeParam H f
  (γ ∘ σ) where
  cont := h.cont.comp continuous_symm
  mem0 := by simpa using h.mem1
  mem1 := by simpa using h.mem0
  inj := by
    intro x hx y hy he
    have hm : ∀ {z : I}, z ∈ Ioo (0 : I) 1 → σ z ∈ Ioo (0 : I) 1 := fun {z} hz => by
      constructor
      · rw [← unitInterval.symm_one, unitInterval.symm_lt_symm]
        exact hz.2
      · rw [← unitInterval.symm_zero, unitInterval.symm_lt_symm]
        exact hz.1
    simpa using h.inj (hm hx) (hm hy) he
  img := by
    rw [← h.img, image_comp]
    congr 1
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      constructor
      · rw [← unitInterval.symm_one, unitInterval.symm_lt_symm]
        exact hy.2
      · rw [← unitInterval.symm_zero, unitInterval.symm_lt_symm]
        exact hy.1
    · intro hz
      refine ⟨σ z, ⟨?_, ?_⟩, by simp⟩
      · rw [← unitInterval.symm_one, unitInterval.symm_lt_symm]
        exact hz.2
      · rw [← unitInterval.symm_zero, unitInterval.symm_lt_symm]
        exact hz.1

variable {H : Drawing S} {f : Set S} {γ : I → S}

theorem EdgeParam.mem_edge (h : EdgeParam H f γ) {y : I} (h0 : 0 < y) (h1 : y < 1) : γ y ∈ f :=
  h.img ▸ mem_image_of_mem γ ⟨h0, h1⟩

theorem EdgeParam.not_V (h : EdgeParam H f γ) (hf : f ∈ H.E) {y : I} (h0 : 0 < y)
  (h1 : y < 1) : γ y ∉ H.V :=
  (hf.2.1 (h.mem_edge h0 h1)).2

theorem EdgeParam.pos_of_ne (h : EdgeParam H f γ) {y : I} (hy : γ y ∉ H.V) : 0 < y
  ∧ y < 1 := by
  constructor
  · rw [unitInterval.pos_iff_ne_zero]
    rintro rfl
    exact hy h.mem0
  · rw [unitInterval.lt_one_iff_ne_one]
    rintro rfl
    exact hy h.mem1

theorem EdgeParam.injOn_Ico (h : EdgeParam H f γ) (hf : f ∈ H.E) {τ : I} (hτ : τ < 1) : InjOn γ
  (Icc 0 τ) := by
  have hcase : ∀ {y : I}, y ∈ Icc 0 τ → y ≠ 0 → y ∈ Ioo (0 : I) 1 := fun {y} hy h0 =>
    ⟨unitInterval.pos_iff_ne_zero.mpr h0, hy.2.trans_lt hτ⟩
  intro x hx y hy he
  by_cases hx0 : x = 0
  · by_cases hy0 : y = 0
    · rw [hx0, hy0]
    · have := hcase hy hy0
      rw [hx0] at he
      exact absurd h.mem0 (he ▸ h.not_V hf this.1 this.2)
  · by_cases hy0 : y = 0
    · have := hcase hx hx0
      rw [hy0] at he
      exact absurd h.mem0 (he.symm ▸ h.not_V hf this.1 this.2)
    · exact h.inj (hcase hx hx0) (hcase hy hy0) he

theorem EdgeParam.line [T2Space S] (h : EdgeParam H f γ) (hf : f ∈ H.E) {τ : I} (h0 : 0 < τ)
  (h1 : τ < 1) :
    IsLineWithEnds (γ '' Icc 0 τ) (γ 0) (γ τ) := by
  have ha : IsArcMap (subArc γ 0 τ) := by
    refine ⟨h.cont.comp (continuous_lerpI _ _), ?_⟩
    intro x y he
    have hm : ∀ z, lerpI 0 τ z ∈ Icc 0 τ := fun z => by
      rw [← range_lerpI h0.le]
      exact mem_range_self z
    exact lerpI_injective h0.ne (h.injOn_Ico hf h1 (hm x) (hm y) he)
  have := isLineWithEnds_range_of_arc ha
  rwa [range_subArc _ h0.le, subArc_zero, subArc_one] at this

theorem EdgeParam.isPathConnected_Ioo (h : EdgeParam H f γ) {τ : I} (h0 : 0 < τ) : IsPathConnected
  (γ '' Ioo 0 τ) := by
  have hc : Continuous fun x : ℝ => γ (projIcc 0 1 zero_le_one x) := h.cont.comp continuous_projIcc
  have hconv : IsPathConnected (Ioo (0 : ℝ) τ.1) := (convex_Ioo _ _).isPathConnected
    (nonempty_Ioo.mpr h0)
  have himg := hconv.image hc
  convert himg using 1
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.1, ⟨hy.1, hy.2⟩, ?_⟩
    change γ (projIcc 0 1 zero_le_one y.1) = _
    rw [projIcc_val]
  · rintro ⟨y, hy, rfl⟩
    have hmem : y ∈ Icc (0 : ℝ) 1 := ⟨hy.1.le, hy.2.le.trans τ.2.2⟩
    refine ⟨⟨y, hmem⟩, ⟨hy.1, hy.2⟩, ?_⟩
    change _ = γ (projIcc 0 1 zero_le_one y)
    rw [projIcc_of_mem zero_le_one hmem]

theorem EdgeParam.closure_Ioo [T2Space S] (h : EdgeParam H f γ) {τ : I} (h0 : 0 < τ) : closure
  (γ '' Ioo 0 τ) = γ '' Icc 0 τ := by
  apply Subset.antisymm
  · exact closure_minimal (image_mono Ioo_subset_Icc_self) (isCompact_Icc.image h.cont).isClosed
  · rw [← _root_.closure_Ioo h0.ne]
    exact image_closure_subset_closure_image h.cont

/-- The set `γ((0, τ))` is open in `U(H) - V(H)` and its subsets. -/
theorem EdgeParam.sep [T2Space S] (h : EdgeParam H f γ) (hf : f ∈ H.E) {τ : I} (h1 : τ < 1) :
    ∃ O, IsOpen O ∧ ∀ x ∈ H.U \ H.V, x ∈ O ↔ x ∈ γ '' Ioo 0 τ := by
  refine ⟨(H.U \ f)ᶜ ∩ (γ '' Icc τ 1)ᶜ, (isClosed_U_sdiff_edge H hf).isOpen_compl.inter
    (isCompact_Icc.image h.cont).isClosed.isOpen_compl, fun x hx => ?_⟩
  constructor
  · rintro ⟨h2, h3⟩
    have hxf : x ∈ f := by
      by_contra hn
      exact h2 ⟨hx.1, hn⟩
    rw [← h.img] at hxf
    obtain ⟨y, hy, rfl⟩ := hxf
    refine ⟨y, ⟨hy.1, ?_⟩, rfl⟩
    by_contra hn
    exact h3 ⟨y, ⟨not_lt.mp hn, hy.2.le⟩, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    have hy1 : y < 1 := hy.2.trans h1
    refine ⟨fun h2 => h2.2 (h.mem_edge hy.1 hy1), ?_⟩
    rintro ⟨y', hy', he⟩
    by_cases hy'1 : y' = 1
    · rw [hy'1] at he
      exact h.not_V hf hy.1 hy1 (he ▸ h.mem1)
    · have hlt : y' < 1 := unitInterval.lt_one_iff_ne_one.mpr hy'1
      have := h.inj ⟨hy.1.trans_le (hy.2.le.trans hy'.1), hlt⟩ ⟨hy.1, hy1⟩ he
      exact absurd (this ▸ hy'.1) (not_le.mpr hy.2)

/-- The arc components of a union of pieces, each open in the union. -/
theorem arcComponentsIn_eq_pieces {F : Set S} {𝓟 : Set (Set S)} (hcov : ⋃₀ 𝓟 = F)
  (hpc : ∀ P ∈ 𝓟, IsPathConnected P)
    (hsep : ∀ P ∈ 𝓟, ∃ O, IsOpen O ∧ ∀ x ∈ F, x ∈ O ↔ x ∈ P) (hdisj : ∀ P ∈ 𝓟, ∀ Q ∈ 𝓟, P ≠ Q
      → Disjoint P Q) : arcComponentsIn F = 𝓟 := by
  have hsub : ∀ P ∈ 𝓟, P ⊆ F := fun P hP => hcov ▸ subset_sUnion_of_mem hP
  have key : ∀ {D P : Set S}, D ⊆ F → IsPreconnected D → P ∈ 𝓟 → (D ∩ P).Nonempty → D ⊆ P := by
    intro D P hD hc hP hne
    choose! O hO hOF using hsep
    let O' : Set S := ⋃ Q ∈ 𝓟 \ {P}, O Q
    have hO' : IsOpen O' := isOpen_biUnion fun Q hQ => hO Q hQ.1
    have hcover : D ⊆ O P ∪ O' := fun x hx => by
      have hxF := hD hx
      rw [← hcov] at hxF
      obtain ⟨Q, hQ, hxQ⟩ := hxF
      by_cases hQP : Q = P
      · exact .inl ((hOF P hP x (hD hx)).mpr (hQP ▸ hxQ))
      · exact .inr (mem_iUnion₂.mpr ⟨Q, ⟨hQ, hQP⟩, (hOF Q hQ x (hD hx)).mpr hxQ⟩)
    have hempty : D ∩ (O P ∩ O') = ∅ := by
      rw [eq_empty_iff_forall_notMem]
      rintro x ⟨hxD, hx1, hx2⟩
      obtain ⟨Q, hQ, hx3⟩ := mem_iUnion₂.mp hx2
      have h4 := (hOF P hP x (hD hxD)).mp hx1
      have h5 := (hOF Q hQ.1 x (hD hxD)).mp hx3
      exact disjoint_left.mp (hdisj P hP Q hQ.1 (Ne.symm hQ.2)) h4 h5
    have h1 : D ⊆ O P := by
      rcases isPreconnected_iff_subset_of_disjoint.mp hc _ _ (hO P hP) hO' hcover hempty with h1 |
        h1
      · exact h1
      · obtain ⟨x, hxD, hxP⟩ := hne
        have h2 : x ∈ D ∩ (O P ∩ O') := ⟨hxD, (hOF P hP x (hD hxD)).mpr hxP, h1 hxD⟩
        rw [hempty] at h2
        exact h2.elim
    exact fun x hx => (hOF P hP x (hD hx)).mp (h1 hx)
  ext P
  constructor
  · rintro ⟨hne, hPF, hpcP, hmax⟩
    obtain ⟨x, hx⟩ := hne
    have hxF := hPF hx
    rw [← hcov] at hxF
    obtain ⟨Q, hQ, hxQ⟩ := hxF
    have hPQ : P ⊆ Q := key hPF hpcP.isConnected.isPreconnected hQ ⟨x, hx, hxQ⟩
    rw [hmax Q (hsub Q hQ) (hpc Q hQ) hPQ] at hQ
    exact hQ
  · intro hP
    refine ⟨(hpc P hP).nonempty, hsub P hP, hpc P hP, fun D hD hpcD hPD => ?_⟩
    obtain ⟨x, hx⟩ := (hpc P hP).nonempty
    exact (key hD hpcD.isConnected.isPreconnected hP ⟨x, hPD hx, hx⟩).antisymm hPD

/-- Each edge `f` of `H` has two halves `(f, false)` and `(f, true)`. The half `q` runs along `β q`
from an end of `f` to the point `β q (τ q)`, which will
be a new vertex. -/
structure IsSplit (H : Drawing S) (β : Set S × Bool → I → S) (τ : Set S × Bool → I) : Prop where
  param : ∀ q : Set S × Bool, q.1 ∈ H.E → EdgeParam H q.1 (β q)
  pos : ∀ q : Set S × Bool, q.1 ∈ H.E → 0 < τ q
  lt : ∀ q : Set S × Bool, q.1 ∈ H.E → τ q < 1
  apart : ∀ f ∈ H.E, Disjoint (β (f, false) '' Ioc 0 (τ (f, false))) (β (f, true) '' Ioc 0 (τ
    (f, true)))

/-- The halves of the edges of `H`. -/
@[expose] def halves (H : Drawing S) : Set (Set S × Bool) := {q | q.1 ∈ H.E}

theorem halves_finite (H : Drawing S) : (halves H).Finite := by
  have : halves H = H.E ×ˢ univ := by
    ext q
    simp [halves]
  rw [this]
  exact H.finite_edges.prod finite_univ

variable {β : Set S × Bool → I → S} {τ : Set S × Bool → I}

/-- The part of a half that is not its first end. -/
@[expose] def halfRest (β : Set S × Bool → I → S) (τ : Set S × Bool → I) (q : Set S × Bool) : Set S
  := β q '' Ioc 0 (τ q)

theorem IsSplit.halfRest_subset (h : IsSplit H β τ) {q : Set S × Bool}
  (hq : q ∈ halves H) : halfRest β τ q ⊆ q.1 := by
  rintro _ ⟨y, hy, rfl⟩
  exact (h.param q hq).mem_edge hy.1 (hy.2.trans_lt (h.lt q hq))

theorem IsSplit.disjoint_rest (h : IsSplit H β τ) {q q' : Set S × Bool} (hq : q ∈ halves H)
  (hq' : q' ∈ halves H) (hne : q ≠ q') :
    Disjoint (halfRest β τ q) (halfRest β τ q') := by
  obtain ⟨f, b⟩ := q
  obtain ⟨f', b'⟩ := q'
  by_cases hf : f = f'
  · subst hf
    have hb : b ≠ b' := fun he => hne (by rw [he])
    have := h.apart f hq
    cases b <;> cases b'
    · exact absurd rfl hb
    · exact this
    · exact this.symm
    · exact absurd rfl hb
  · exact (GraphMinor.GM06.disjoint_edges_of_ne H hq hq' hf).mono (h.halfRest_subset hq)
      (h.halfRest_subset hq')

theorem IsSplit.mark_mem (h : IsSplit H β τ) {q : Set S × Bool} (hq : q ∈ halves H) : β q
  (τ q) ∈ halfRest β τ q :=
  ⟨τ q, ⟨h.pos q hq, le_rfl⟩, rfl⟩

theorem IsSplit.mark_not_V (h : IsSplit H β τ) {q : Set S × Bool} (hq : q ∈ halves H) : β q
  (τ q) ∉ H.V :=
  (h.param q hq).not_V hq (h.pos q hq) (h.lt q hq)

theorem IsSplit.mark_inj (h : IsSplit H β τ) {q q' : Set S × Bool} (hq : q ∈ halves H)
  (hq' : q' ∈ halves H) (he : β q (τ q) = β q' (τ q')) : q = q' := by
  by_contra hne
  exact disjoint_left.mp (h.disjoint_rest hq hq' hne) (h.mark_mem hq) (he ▸ h.mark_mem hq')

omit [TopologicalSpace S] in
/-- A point of a closed half is its first end, or lies in the rest of the half. -/
theorem mem_closed_half {q : Set S × Bool} {x : S} (hx : x ∈ β q '' Icc 0
  (τ q)) : x = β q 0 ∨ x ∈ halfRest β τ q := by
  obtain ⟨y, hy, rfl⟩ := hx
  by_cases h0 : y = 0
  · exact .inl (by rw [h0])
  · exact .inr ⟨y, ⟨unitInterval.pos_iff_ne_zero.mpr h0, hy.2⟩, rfl⟩

theorem IsSplit.piece_cases (h : IsSplit H β τ) {x : S} (hx : x ∈
  (H.V ∪ ⋃ q ∈ halves H, β q '' Icc 0 (τ q)) \ (H.V ∪ (fun q => β q (τ q)) '' halves H)) :
    ∃ q ∈ halves H, x ∈ β q '' Ioo 0 (τ q) := by
  obtain ⟨h1 | h1, h2⟩ := hx
  · exact absurd (.inl h1) h2
  · obtain ⟨q, hq, y, hy, rfl⟩ := mem_iUnion₂.mp h1
    refine ⟨q, hq, y, ⟨?_, ?_⟩, rfl⟩
    · rw [unitInterval.pos_iff_ne_zero]
      rintro rfl
      exact h2 (.inl (h.param q hq).mem0)
    · refine lt_of_le_of_ne hy.2 ?_
      rintro rfl
      exact h2 (.inr ⟨q, hq, rfl⟩)

theorem IsSplit.piece_off (h : IsSplit H β τ) {q : Set S × Bool} (hq : q ∈ halves H) {x : S}
  (hx : x ∈ β q '' Ioo 0 (τ q)) : x ∉ H.V ∪ (fun q => β q (τ q)) '' halves H := by
  obtain ⟨y, hy, rfl⟩ := hx
  have hτ := h.lt q hq
  have hp := h.param q hq
  rintro (h1 | ⟨q', hq', he⟩)
  · exact hp.not_V hq hy.1 (hy.2.trans hτ) h1
  · have hmem : β q y ∈ halfRest β τ q := ⟨y, ⟨hy.1, hy.2.le⟩, rfl⟩
    have heq : q' = q := by
      by_contra hne
      have he' : β q' (τ q') = β q y := he
      exact disjoint_left.mp (h.disjoint_rest hq' hq hne) (h.mark_mem hq') (by rw [he']; exact hmem)
    subst heq
    have := hp.inj ⟨h.pos q' hq', hτ⟩ ⟨hy.1, hy.2.trans hτ⟩ he
    exact absurd (this ▸ hy.2) (lt_irrefl _)

theorem IsSplit.arcComponents (h : IsSplit H β τ) [T2Space S] :
    arcComponentsIn ((H.V ∪ ⋃ q ∈ halves H, β q '' Icc 0 (τ q)) \ (H.V ∪ (fun q => β q
      (τ q)) '' halves H)) = (fun q => β q '' Ioo 0 (τ q)) '' halves H := by
  refine arcComponentsIn_eq_pieces ?_ ?_ ?_ ?_
  · ext x
    constructor
    · rintro ⟨_, ⟨q, hq, rfl⟩, hx⟩
      obtain ⟨y, hy, he⟩ := id hx
      exact ⟨.inr (mem_iUnion₂.mpr ⟨q, hq, y, ⟨hy.1.le, hy.2.le⟩, he⟩), h.piece_off hq hx⟩
    · intro hx
      obtain ⟨q, hq, hxq⟩ := h.piece_cases hx
      exact ⟨_, ⟨q, hq, rfl⟩, hxq⟩
  · rintro _ ⟨q, hq, rfl⟩
    exact (h.param q hq).isPathConnected_Ioo (h.pos q hq)
  · rintro _ ⟨q, hq, rfl⟩
    obtain ⟨O, hO, hOx⟩ := (h.param q hq).sep hq (h.lt q hq)
    refine ⟨O, hO, fun x hx => hOx x ?_⟩
    obtain ⟨q', hq', y, hy, rfl⟩ := h.piece_cases hx
    exact hq'.2.1 ((h.param q' hq').mem_edge hy.1 (hy.2.trans (h.lt q' hq')))
  · rintro _ ⟨q, hq, rfl⟩ _ ⟨q', hq', rfl⟩ hne
    have hqq : q ≠ q' := fun he => hne (by rw [he])
    exact (h.disjoint_rest hq hq' hqq).mono (image_mono Ioo_subset_Ioc_self)
      (image_mono Ioo_subset_Ioc_self)

theorem IsSplit.cap (h : IsSplit H β τ) {q : Set S × Bool} (hq : q ∈ halves H) :
    β q '' Icc 0 (τ q) ∩ (H.V ∪ (fun q => β q (τ q)) '' halves H) = {β q 0, β q (τ q)} := by
  ext x
  constructor
  · rintro ⟨h1, h2⟩
    rcases mem_closed_half h1 with rfl | h3
    · exact .inl rfl
    · have hrest := h.halfRest_subset hq h3
      rcases h2 with h4 | ⟨q', hq', rfl⟩
      · exact absurd h4 (hq.2.1 hrest).2
      · have : q' = q := by
          by_contra hne
          exact disjoint_left.mp (h.disjoint_rest hq' hq hne) (h.mark_mem hq') h3
        subst this
        exact .inr rfl
  · rintro (rfl | rfl)
    · exact ⟨⟨0, ⟨le_rfl, (h.pos q hq).le⟩, rfl⟩, Or.inl (h.param q hq).mem0⟩
    · exact ⟨⟨τ q, ⟨(h.pos q hq).le, le_rfl⟩, rfl⟩, Or.inr ⟨q, hq, rfl⟩⟩

/-- `H` with the middle of each edge removed. -/
@[expose] def IsSplit.drawing [T2Space S] (h : IsSplit H β τ) : Drawing S where
  U := H.V ∪ ⋃ q ∈ halves H, β q '' Icc 0 (τ q)
  V := H.V ∪ (fun q => β q (τ q)) '' halves H
  V_subset_U := by
    refine union_subset subset_union_left ?_
    rintro _ ⟨q, hq, rfl⟩
    exact .inr (mem_iUnion₂.mpr ⟨q, hq, τ q, ⟨(h.pos q hq).le, le_rfl⟩, rfl⟩)
  isClosed_U := H.finite_V.isClosed.union ((halves_finite H).isClosed_biUnion fun q hq =>
    (isCompact_Icc.image (h.param q hq).cont).isClosed)
  finite_V := H.finite_V.union ((halves_finite H).image _)
  finite_edges := by
    rw [h.arcComponents]
    exact (halves_finite H).image _
  edge_cond := by
    rw [h.arcComponents]
    rintro _ ⟨q, hq, rfl⟩
    have hp := h.param q hq
    left
    refine ⟨β q 0, β q (τ q), fun he => h.mark_not_V hq (he ▸ hp.mem0), ?_, ?_⟩
    · rw [hp.closure_Ioo (h.pos q hq), h.cap hq]
    · rw [hp.closure_Ioo (h.pos q hq)]
      exact hp.line hq (h.pos q hq) (h.lt q hq)

variable [T2Space S]

theorem IsSplit.drawing_E (h : IsSplit H β τ) : h.drawing.E = (fun q => β q '' Ioo 0
  (τ q)) '' halves H := h.arcComponents

theorem IsSplit.drawing_U (h : IsSplit H β τ) : h.drawing.U = H.V ∪ ⋃ q ∈ halves H, β q '' Icc 0
  (τ q) := rfl

theorem IsSplit.drawing_V (h : IsSplit H β τ) : h.drawing.V = H.V ∪ (fun q => β q
  (τ q)) '' halves H := rfl

/-- The links of the split drawing. -/
theorem IsSplit.link (h : IsSplit H β τ) {e : Set S} {x y : S} (hl : h.drawing.toGraph.IsLink e x
  y) :
    ∃ q ∈ halves H, e = β q '' Ioo 0 (τ q) ∧ ((x = β q 0 ∧ y = β q (τ q)) ∨ (x = β q (τ q) ∧ y
      = β q 0)) := by
  obtain ⟨he, -, -, hcap⟩ := hl
  rw [h.drawing_E] at he
  obtain ⟨q, hq, rfl⟩ := he
  refine ⟨q, hq, rfl, ?_⟩
  have hp := h.param q hq
  have hcap' : closure (β q '' Ioo 0 (τ q)) ∩ h.drawing.V = {β q 0, β q (τ q)} := by
    rw [hp.closure_Ioo (h.pos q hq), h.drawing_V, h.cap hq]
  rw [hcap'] at hcap
  have hne : β q 0 ≠ β q (τ q) := fun he => h.mark_not_V hq (he ▸ hp.mem0)
  have hx : x ∈ ({β q 0, β q (τ q)} : Set S) := by rw [hcap]; simp
  have hy : y ∈ ({β q 0, β q (τ q)} : Set S) := by rw [hcap]; simp
  have h1 : β q 0 ∈ ({x, y} : Set S) := by rw [← hcap]; simp
  have h2 : β q (τ q) ∈ ({x, y} : Set S) := by rw [← hcap]; simp
  simp only [mem_insert_iff, mem_singleton_iff] at hx hy h1 h2
  grind

theorem IsSplit.isGraphForest (h : IsSplit H β τ) : IsGraphForest h.drawing.toGraph := by
  refine isGraphForest_of_leaves _ ((fun q => β q (τ q)) '' halves H) (fun {e x y} hl
    => ?_) fun x hx {e f y z} hl hl' => ?_
  · obtain ⟨q, hq, -, hc⟩ := h.link hl
    have hnot : β q 0 ∉ (fun q => β q (τ q)) '' halves H := by
      rintro ⟨q', hq', he⟩
      have he' : β q' (τ q') = β q 0 := he
      exact h.mark_not_V hq' (by rw [he']; exact (h.param q hq).mem0)
    rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact .inr ⟨hnot, q, hq, rfl⟩
    · exact .inl ⟨⟨q, hq, rfl⟩, hnot⟩
  · obtain ⟨q₀, hq₀, rfl⟩ := hx
    have hown : ∀ {e y}, h.drawing.toGraph.IsLink e (β q₀ (τ q₀)) y → e = β q₀ '' Ioo 0 (τ q₀)
      := fun {e y} hl => by
      obtain ⟨q, hq, rfl, hc⟩ := h.link hl
      have hm : β q₀ (τ q₀) = β q (τ q) := by
        rcases hc with ⟨h1, -⟩ | ⟨h1, -⟩
        · exact absurd (by rw [h1]; exact (h.param q hq).mem0) (h.mark_not_V hq₀)
        · exact h1
      rw [h.mark_inj hq₀ hq hm]
    rw [hown hl, hown hl']

/-- The vertex of `H` that a vertex of the split drawing belongs to. -/
@[expose] noncomputable def splitOwner (H : Drawing S) (β : Set S × Bool → I → S) (τ : Set S × Bool
  → I) (x : S) : S :=
  open Classical in if h : ∃ q ∈ halves H, x = β q (τ q) then β h.choose 0 else x

omit [T2Space S] in
theorem IsSplit.owner_mark (h : IsSplit H β τ) {q : Set S × Bool} (hq : q ∈ halves H) : splitOwner
  H β τ (β q (τ q)) = β q 0 := by
  classical
  have hex : ∃ q' ∈ halves H, β q (τ q) = β q' (τ q') := ⟨q, hq, rfl⟩
  rw [splitOwner, dite_eq_left hex]
  exact congrArg (fun r => β r 0) (h.mark_inj hq hex.choose_spec.1 hex.choose_spec.2).symm

omit [T2Space S] in
theorem IsSplit.owner_V (h : IsSplit H β τ) {x : S} (hx : x ∈ H.V) : splitOwner H β τ x = x := by
  classical
  rw [splitOwner, dite_eq_right]
  rintro ⟨q, hq, rfl⟩
  exact h.mark_not_V hq hx

theorem IsSplit.owner_walk (h : IsSplit H β τ) {x y : S} (W : GraphWalk h.drawing.toGraph x y) :
  splitOwner H β τ x = splitOwner H β τ y := by
  induction W with
  | nil _ => rfl
  | cons hl _ ih =>
    rw [← ih]
    obtain ⟨q, hq, -, hc⟩ := h.link hl
    rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [h.owner_mark hq, h.owner_V (h.param q hq).mem0]
    · rw [h.owner_mark hq, h.owner_V (h.param q hq).mem0]

theorem IsSplit.owner_mem (h : IsSplit H β τ) {x : S} (hx : x ∈ h.drawing.V) : splitOwner H β τ x ∈
  H.V := by
  rcases hx with hx | ⟨q, hq, rfl⟩
  · rw [h.owner_V hx]
    exact hx
  · change splitOwner H β τ (β q (τ q)) ∈ _
    rw [h.owner_mark hq]
    exact (h.param q hq).mem0

/-- The half `q` as an edge of the split drawing. -/
theorem IsSplit.link_half (h : IsSplit H β τ) {q : Set S × Bool} (hq : q ∈ halves H) :
    h.drawing.toGraph.IsLink (β q '' Ioo 0 (τ q)) (β q 0) (β q (τ q)) := by
  have hp := h.param q hq
  refine ⟨?_, .inl hp.mem0, .inr ⟨q, hq, rfl⟩, ?_⟩
  · rw [h.drawing_E]
    exact ⟨q, hq, rfl⟩
  · rw [hp.closure_Ioo (h.pos q hq), h.drawing_V, h.cap hq]

/-- Two vertices with one owner are joined by a path. -/
theorem IsSplit.exists_simple_walk (h : IsSplit H β τ) {x y : S} (hx : x ∈ h.drawing.V)
  (hy : y ∈ h.drawing.V) (he : splitOwner H β τ x = splitOwner H β τ y)
    (hne : x ≠ y) : ∃ W : GraphWalk h.drawing.toGraph x y, W.IsSimple := by
  have hmarkV : ∀ {q : Set S × Bool}, q ∈ halves H → β q 0 ≠ β q (τ q) := fun {q} hq he'
    => h.mark_not_V hq (he' ▸ (h.param q hq).mem0)
  have hV₀ : ∀ {q : Set S × Bool}, q ∈ halves H → β q 0 ∈ h.drawing.V := fun {q} hq => .inl
    (h.param q hq).mem0
  rcases hx with hx | ⟨q, hq, rfl⟩ <;> rcases hy with hy | ⟨q', hq', rfl⟩
  · rw [h.owner_V hx, h.owner_V hy] at he
    exact absurd he hne
  · change splitOwner H β τ x = splitOwner H β τ (β q' (τ q')) at he
    rw [h.owner_V hx, h.owner_mark hq'] at he
    subst he
    refine ⟨.cons (h.link_half hq') (.nil (.inr ⟨q', hq', rfl⟩)), ?_⟩
    simpa [GraphWalk.IsSimple, GraphWalk.support] using hmarkV hq'
  · change splitOwner H β τ (β q (τ q)) = splitOwner H β τ y at he
    rw [h.owner_V hy, h.owner_mark hq] at he
    subst he
    exact ⟨.cons (h.link_half hq).symm (.nil (hV₀ hq)), by simpa [GraphWalk.IsSimple,
      GraphWalk.support] using (hmarkV hq).symm⟩
  · change splitOwner H β τ (β q (τ q)) = splitOwner H β τ (β q' (τ q')) at he
    rw [h.owner_mark hq, h.owner_mark hq'] at he
    have h1 : h.drawing.toGraph.IsLink (β q' '' Ioo 0 (τ q')) (β q 0) (β q' (τ q'))
      := he ▸ h.link_half hq'
    refine ⟨.cons (h.link_half hq).symm (.cons h1 (.nil (.inr ⟨q', hq', rfl⟩))), ?_⟩
    have h2 : β q 0 ≠ β q' (τ q') := he ▸ hmarkV hq'
    simpa [GraphWalk.IsSimple, GraphWalk.support, hne, h2] using (hmarkV hq).symm

/-- Three inner points of the unit interval. -/
@[expose] noncomputable def quarter₁ : I := ⟨1 / 4, by norm_num, by norm_num⟩
/-- See `quarter₁`. -/
@[expose] noncomputable def quarter₂ : I := ⟨1 / 2, by norm_num, by norm_num⟩
/-- See `quarter₁`. -/
@[expose] noncomputable def quarter₃ : I := ⟨3 / 4, by norm_num, by norm_num⟩

theorem quarter₁_pos : (0 : I) < quarter₁ := by
  rw [← Subtype.coe_lt_coe]
  norm_num [quarter₁]

theorem quarter_lt₁₂ : quarter₁ < quarter₂ := by
  rw [← Subtype.coe_lt_coe]
  norm_num [quarter₁, quarter₂]

theorem quarter_lt₂₃ : quarter₂ < quarter₃ := by
  rw [← Subtype.coe_lt_coe]
  norm_num [quarter₂, quarter₃]

theorem quarter₃_lt : quarter₃ < 1 := by
  rw [← Subtype.coe_lt_coe]
  norm_num [quarter₃]

omit [T2Space S] in
theorem EdgeParam.subset_U (hγ : EdgeParam H f γ) (hf : f ∈ H.E) (y : I) : γ y ∈ H.U := by
  have h1 : Ioo (0 : I) 1 ⊆ γ ⁻¹' H.U := fun z hz => by
    have := hγ.mem_edge hz.1 hz.2
    exact (hf.2.1 this).1
  have h2 : closure (Ioo (0 : I) 1) ⊆ γ ⁻¹' H.U := closure_minimal h1
    (H.isClosed_U.preimage hγ.cont)
  rw [_root_.closure_Ioo zero_ne_one] at h2
  exact h2 ⟨unitInterval.nonneg y, unitInterval.le_one y⟩

/-- An edge run from its head to its tail. -/
theorem exists_oriented_param (hf : f ∈ H.E) {p m : S} (hpm : ({p, m} : Set S) = tilde f) : ∃ γ : I
  → S, EdgeParam H f γ ∧ γ 0 = p ∧ γ 1 = m := by
  obtain ⟨γ, h1, h2, h3, h4, h5⟩ := exists_edge_param H hf
  have hγ : EdgeParam H f γ := ⟨h1, h2, h3, h4, h5⟩
  have hcl : closure f = γ '' Icc 0 1 := by
    rw [← h5]
    exact hγ.closure_Ioo zero_lt_one
  have ht : tilde f = {γ 0, γ 1} := by
    ext x
    constructor
    · rintro ⟨hx, hxf⟩
      rw [hcl] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      by_cases hy0 : y = 0
      · exact .inl (by rw [hy0])
      · by_cases hy1 : y = 1
        · exact .inr (by rw [hy1]; rfl)
        · exact absurd (hγ.mem_edge (unitInterval.pos_iff_ne_zero.mpr hy0)
            (unitInterval.lt_one_iff_ne_one.mpr hy1)) hxf
    · rintro (rfl | rfl)
      · exact ⟨hcl ▸ ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩, fun hx => (hf.2.1 hx).2 h2⟩
      · exact ⟨hcl ▸ ⟨1, ⟨zero_le_one, le_rfl⟩, rfl⟩, fun hx => (hf.2.1 hx).2 h3⟩
  rw [ht] at hpm
  have h6 : p ∈ ({γ 0, γ 1} : Set S) := by rw [← hpm]; simp
  have h7 : m ∈ ({γ 0, γ 1} : Set S) := by rw [← hpm]; simp
  have h8 : γ 0 ∈ ({p, m} : Set S) := by rw [hpm]; simp
  have h9 : γ 1 ∈ ({p, m} : Set S) := by rw [hpm]; simp
  simp only [mem_insert_iff, mem_singleton_iff] at h6 h7 h8 h9
  by_cases hc : γ 0 = p ∧ γ 1 = m
  · exact ⟨γ, hγ, hc.1, hc.2⟩
  · refine ⟨γ ∘ σ, hγ.rev, ?_, ?_⟩
    · simp only [comp_apply, unitInterval.symm_zero]
      grind
    · simp only [comp_apply, unitInterval.symm_one]
      grind

end GraphMinor.GM07
