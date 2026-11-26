/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section5Tangle
import LeanPool.GraphMinor.GM14.DiscSlope
import LeanPool.GraphMinor.Surface.AddCrosscap
import LeanPool.GraphMinor.Surface.DiscGrow

/-!
# Graph Minors XII, (5.3)

We prove that the tangle induced in `Γ` by a respectful tangle of `Γ₁` is respectful, under the
hypotheses of (5.3). The first case, of an `O`-arc with at most one point in `Σ₂`, is
`respect_of_inside`.
-/

public section

namespace GraphMinor.GM12

open Set Topology Metric GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM10 Hypergraph

universe u

variable {S T : Type u} [TopologicalSpace S] [T2Space S] [TopologicalSpace T] [T2Space T]
  {n : ℕ} {C : Fin n → Set S} {P₁ P₂ : Set S} {ι : P₁ → T} {D : Fin n → Set T}
  {Γ : Drawing S} {Γ₁ : Drawing T} {θ : ℕ}
  {𝒯 : Set (Hypergraph T (Set T) × Hypergraph T (Set T))}

theorem mem_closure_diff_iff {X : Type*} [TopologicalSpace X] {Y : Set X} (hY : IsClosed Y)
  (x : X) :
    x ∈ closure (univ \ Y) ↔ x ∉ Y ∨ x ∈ frontier Y := by
  rw [frontier_eq_closure_inter_closure, compl_eq_univ_sdiff, hY.closure_eq]
  constructor
  · intro hx
    by_cases hxY : x ∈ Y
    · exact .inr ⟨hxY, hx⟩
    · exact .inl hxY
  · rintro (hx | hx)
    · exact subset_closure ⟨mem_univ x, hx⟩
    · exact hx.2

omit [T2Space S] [T2Space T] in
theorem isOArc_capUp_of_subset (h : IsCappedSplit C P₁ P₂ ι D) {F : Set S} (hO : IsOArc F)
    (hF : F ⊆ P₁) : IsOArc (capUp ι F) := by
  have hpre : IsOArc ((↑) ⁻¹' F : Set P₁) := by
    apply isOArc_of_image IsEmbedding.subtypeVal
    rw [Subtype.image_preimage_coe, inter_eq_right.mpr hF]
    exact hO
  exact isOArc_image h.isEmbedding hpre

omit [T2Space T] in
/-- An `O`-arc with at most one point in `Σ₂` lies in `Σ₁`, because it has no isolated point and
the complement of `Σ₁` is open. -/
theorem subset_of_subsingleton (h : IsCappedSplit C P₁ P₂ ι D) {F : Set S} (hO : IsOArc F)
    (hF : (F ∩ P₂).Subsingleton) : F ⊆ P₁ := by
  obtain ⟨e⟩ := hO
  intro x hx
  by_contra hn
  have hx₂ : x ∈ P₂ := (show x ∈ P₁ ∪ P₂ from h.union ▸ mem_univ x).resolve_left hn
  let U : Set Circle := {w | (e w).1 ∉ P₁}
  have hU : IsOpen U := by
    have hc : Continuous fun w => (e w).1 := continuous_subtype_val.comp e.continuous
    exact (h.isClosed₁.preimage hc).isOpen_compl
  let w₀ := e.symm ⟨x, hx⟩
  have hw₀ : (e w₀).1 = x := by simp [w₀]
  have hUs : U = {w₀} := by
    apply Subset.antisymm
    · intro w hw
      have hw₂ : (e w).1 ∈ P₂ :=
        (show (e w).1 ∈ P₁ ∪ P₂ from h.union ▸ mem_univ _).resolve_left hw
      have := hF ⟨(e w).2, hw₂⟩ ⟨hx, hx₂⟩
      exact e.injective (Subtype.ext (this.trans hw₀.symm))
    · rintro w rfl
      change (e w₀).1 ∉ P₁
      rwa [hw₀]
  have huniv : U = univ := by
    apply IsClopen.eq_univ ⟨?_, hU⟩ ⟨w₀, ?_⟩
    · rw [hUs]
      exact isClosed_singleton
    · rw [hUs]
      rfl
  have hall : ∀ w : Circle, w = w₀ := fun w => by
    have : w ∈ U := huniv ▸ mem_univ w
    rw [hUs] at this
    exact this
  have hne : Circle.exp Real.pi ≠ 1 := by
    intro he
    have := congrArg (fun z : Circle => (z : ℂ)) he
    simp only [Circle.coe_exp, Circle.coe_one] at this
    rw [Complex.exp_pi_mul_I] at this
    norm_num at this
  exact hne ((hall _).trans (hall _).symm)

/-- The first case of the proof of (5.3): an `O`-arc inside `Σ₁`. -/
theorem respect_of_inside [ConnectedSpace T] (h : IsCappedSplit C P₁ P₂ ι D)
  (hΓ : IsCappedDrawing ι Γ Γ₁)
    (hN : ∀ k, Γ.IsNormal (C k)) (H : CapSetup (fun k => closure (D k)) Γ₁ θ 𝒯)
    {F : Set S} (hO : IsOArc F) (hFN : Γ.IsNormal F) (hsmall : (F ∩ Γ.V).ncard < θ) (hFP : F ⊆ P₁) :
    ∃ Δ : Set S, IsClosedDisc Δ ∧ subBd Δ = F ∧
      ((PaintingOrDrawing.drawing Γ).inter Δ, (PaintingOrDrawing.drawing Γ).interOutside Δ) ∈
        inducedAcross ι Γ Γ₁ θ 𝒯 := by
  have hι := h.isEmbedding
  have hιi := hι.injective
  have hS := h.surface_hat
  have hSS := h.surface.1
  have hcount : (capUp ι F ∩ Γ₁.V).ncard = (F ∩ Γ.V).ncard := by
    rw [← capUp_inter_V hιi hΓ, ncard_capUp hιi (inter_subset_left.trans hFP)]
  have hNT : Γ₁.IsNormal (capUp ι F) := by
    rintro _ ⟨⟨p, hp, rfl⟩, hpU⟩
    rw [hΓ.1] at hpU
    rw [hΓ.2]
    exact ⟨p, hFN ⟨hp, (mem_capUp_val hιi).mp hpU⟩, rfl⟩
  obtain ⟨Δ₁, hΔ₁, hbd, hmem⟩ := H.respect.2 _ (isOArc_capUp_of_subset h hO hFP) hNT
    (by change (capUp ι F ∩ Γ₁.V).ncard < θ; rwa [hcount])
  have hfr : frontier Δ₁ = capUp ι F := by rw [← subBd_eq_frontier, hbd]
  have hbΔ : discBd Δ₁ = capUp ι F := by
    rw [← IsClosedDisc.frontier_eq_discBd hS hΔ₁, hfr]
  have hoff : ∀ k, Disjoint Δ₁ (D k) := by
    intro k
    have := off_cap H hS hΔ₁ hmem (by rw [hfr]; rwa [hcount]) k (by
      rw [(cap_closure h k).2.2, hbΔ]
      exact (h.D_off k).mono_right (capUp_subset_range _))
    rwa [(cap_closure h k).2.2] at this
  have hr : Δ₁ ⊆ range ι := by
    intro x hx
    by_contra hn
    have : x ∈ ⋃ m, D m := h.compl ▸ hn
    obtain ⟨m, hm⟩ := mem_iUnion.mp this
    exact Set.disjoint_left.mp (hoff m) hx hm
  have : Nonempty T := ⟨(hΔ₁.isPathConnected.nonempty).some⟩
  obtain ⟨hΔd, hΔb⟩ := disc_capDown h hΔ₁ hr
  have hbF : discBd (capDown ι Δ₁) = F := by
    rw [hΔb, hbΔ, capDown_capUp hιi hFP]
  have hsub : subBd (capDown ι Δ₁) = F := by
    rw [subBd_eq_frontier, IsClosedDisc.frontier_eq_discBd hSS hΔd, hbF]
  have hfrS : frontier (capDown ι Δ₁) = F := by rw [← subBd_eq_frontier, hsub]
  have hcl := hΔd.isClosed
  have hiff : ∀ p : P₁, ι p ∈ Δ₁ ↔ p.1 ∈ capDown ι Δ₁ := by
    intro p
    constructor
    · intro hp
      exact ⟨p, hp, rfl⟩
    · rintro ⟨q, hq, he⟩
      rwa [← Subtype.ext he]
  refine ⟨capDown ι Δ₁, hΔd, hsub, mem_inducedAcross h hΓ hN hcl ?_ ?_ hiff ?_ hmem⟩
  · rw [hfrS]
    exact hFN
  · rw [hfrS]
    exact hsmall
  · intro p
    rw [mem_closure_diff_iff hΔ₁.isClosed, mem_closure_diff_iff hcl, hfr, hfrS, mem_capUp_val hιi,
      hiff p]

/-- A connected set that meets a closed set and misses its frontier lies in it. -/
theorem subset_of_frontier {X : Type*} [TopologicalSpace X] {A Y : Set X} (hA : IsPreconnected A)
    (hY : IsClosed Y) (hne : (A ∩ Y).Nonempty) (hd : ∀ x ∈ A, x ∉ frontier Y) : A ⊆ Y := by
  obtain ⟨x, hxA, hxY⟩ := hne
  have hsub : A ⊆ interior Y ∪ Yᶜ := fun y hy => by
    by_cases hyY : y ∈ Y
    · refine .inl ?_
      by_contra hn
      exact hd y hy ⟨subset_closure hyY, hn⟩
    · exact .inr hyY
  have hxi : x ∈ interior Y := by
    by_contra hn
    exact hd x hxA ⟨subset_closure hxY, hn⟩
  have := hA.subset_left_of_subset_union isOpen_interior hY.isOpen_compl
    (Set.disjoint_left.mpr fun _ h₁ h₂ => h₂ (interior_subset h₁)) hsub ⟨x, hxA, hxi⟩
  exact this.trans interior_subset

local notation "𝕀" => unitInterval

omit [T2Space S] in
theorem exists_level_near {Y : Type*} [TopologicalSpace Y] {b : Y × 𝕀 → S} (hb : Continuous b)
    {F : Set S} (hF : IsClosed F) {y : Y} (hy : b (y, 0) ∉ F) :
    ∃ ε : 𝕀, ε ≠ 0 ∧ ∀ s ≤ ε, b (y, s) ∉ F := by
  have hopen : IsOpen {s : 𝕀 | b (y, s) ∉ F} :=
    (hF.preimage (hb.comp (Continuous.prodMk_right y))).isOpen_compl
  have hnh : {s : 𝕀 | b (y, s) ∉ F} ∈ 𝓝 (⊥ : 𝕀) := hopen.mem_nhds hy
  obtain ⟨a, ha, hsub⟩ := (nhds_bot_basis (α := 𝕀)).mem_iff.mp hnh
  obtain ⟨ε, h0, hε⟩ := exists_between ha
  exact ⟨ε, ne_of_gt h0, fun s hs => hsub (lt_of_le_of_lt hs hε)⟩

omit [T2Space S] in
/-- Near level zero, the fibres over a finite set of points off `F` miss `F`. -/
theorem exists_level_fibre {Y : Type*} [TopologicalSpace Y] {b : Y × 𝕀 → S} (hb : Continuous b)
    (hi : Function.Injective b) {F W : Set S} (hF : IsClosed F) (hW : W.Finite)
      (hWF : Disjoint W F) :
    ∃ ε : 𝕀, ε ≠ 0 ∧ ∀ y s, b (y, 0) ∈ W → s ≤ ε → b (y, s) ∉ F := by
  induction W, hW using Set.Finite.induction_on with
  | empty => exact ⟨1, one_ne_zero, fun y s hy => hy.elim⟩
  | @insert w W _ _ ih =>
    obtain ⟨ε, h0, hε⟩ := ih (hWF.mono_left (subset_insert _ _))
    by_cases hr : ∃ y, b (y, 0) = w
    · obtain ⟨y, rfl⟩ := hr
      obtain ⟨ε', h0', hε'⟩ := exists_level_near hb hF (y := y)
        (Set.disjoint_left.mp hWF (mem_insert _ _))
      refine ⟨min ε ε', ?_, ?_⟩
      · rcases min_choice ε ε' with he | he <;> rw [he] <;> assumption
      · intro y' s hy' hs
        rcases hy' with hy' | hy'
        · have : y' = y := congrArg Prod.fst (hi hy')
          subst this
          exact hε' s (hs.trans (min_le_right _ _))
        · exact hε y' s hy' (hs.trans (min_le_left _ _))
    · refine ⟨ε, h0, fun y s hy' hs => ?_⟩
      rcases hy' with hy' | hy'
      · exact (hr ⟨y, hy'⟩).elim
      · exact hε y s hy' hs

omit [T2Space S] in
/-- Below some level, the collar misses a finite set of points off `Σ₂`. -/
theorem exists_level_off {Y : Type*} [TopologicalSpace Y] {b : Y × 𝕀 → S}
  (hb : IsOuterCollar P₂ b) {Q : Set S}
    (hQ : Q.Finite) (hQP : Disjoint Q P₂) {ε₀ : 𝕀} (hε₀ : ε₀ ≠ 0) :
    ∃ ε : 𝕀, ε ≠ 0 ∧ ε ≤ ε₀ ∧ ∀ q ∈ Q, q ∉ b '' {p | p.2 ≤ ε} := by
  induction Q, hQ using Set.Finite.induction_on with
  | empty => exact ⟨ε₀, hε₀, le_rfl, fun q hq => hq.elim⟩
  | @insert w W _ _ ih =>
    obtain ⟨ε, h0, hle, hε⟩ := ih (hQP.mono_left (subset_insert _ _))
    by_cases hr : w ∈ range b
    · obtain ⟨⟨y, s⟩, rfl⟩ := hr
      have hs : s ≠ 0 := by
        rintro rfl
        exact Set.disjoint_left.mp hQP (mem_insert _ _) (hb.zero y)
      obtain ⟨m, hm0, hm⟩ := exists_between (unitInterval.pos_iff_ne_zero.mpr hs)
      refine ⟨min ε m, ?_, (min_le_left _ _).trans hle, ?_⟩
      · rcases min_choice ε m with he | he <;> rw [he]
        · exact h0
        · exact ne_of_gt hm0
      · rintro q (rfl | hq) ⟨p, hp, he⟩
        · have : p = (y, s) := hb.inj he
          subst this
          exact absurd (lt_of_le_of_lt ((show s ≤ min ε m from hp).trans (min_le_right _ _)) hm)
            (lt_irrefl _)
        · exact hε q hq ⟨p, show p.2 ≤ ε from le_trans hp (min_le_left _ _), he⟩
    · refine ⟨ε, h0, hle, ?_⟩
      rintro q (rfl | hq)
      · exact fun ⟨p, _, he⟩ => hr ⟨p, he⟩
      · exact hε q hq

@[expose] public section

/-- Condition (iii) of (5.3), with the length of a curve read as the number of vertices on its
image. -/
def CurvesNull (Γ : Drawing S) (P₂ : Set S) (θ : ℕ) : Prop :=
  ∀ c : C(Circle, S), (∀ x, c x ∈ P₂) → Γ.IsNormal (range c) → (range c ∩ Γ.V).ncard < θ →
    ClosedCurveIsNullHomotopicIn P₂ c

end

variable {φ : C(Circle, S)} {J : Finset (Set Circle)} {a b' : Set Circle → 𝕀 → Circle}
  {R : Set Circle → Set S} {Δ₁ : Set Circle → Set T} {Δg : Set Circle → Set S}

omit [T2Space T] in
/-- The homotopy of the proof of (5.3). We replace the pieces in `J` by lines on the common
boundary,
and we push the rest of the curve across the collar. Then (iii) applies, and Graph Minors XI (7.2)
gives a disc in the subset of the null-homotopy. -/
theorem exists_disc_of_pieces [NeZero n] (h : IsCappedSplit C P₁ P₂ ι D) (hN : ∀ k, Γ.IsNormal
  (C k))
    (hφ : Function.Injective φ) (hFN : Γ.IsNormal (range φ)) (hsmall : (range φ ∩ Γ.V).ncard < θ)
    (hiii : CurvesNull Γ P₂ θ) {β : (Fin n × Circle) × 𝕀 → S} (hβ : IsOuterCollar P₂ β)
    (hβ0 : ∀ y, β (y, 0) ∈ C y.1) {ε : 𝕀}
    (hfib : ∀ y s, β (y, 0) ∈ Γ.V → β (y, 0) ∉ range φ → s ≤ ε → β (y, s) ∉ range φ)
    (hP : Pieces C P₂ ι Γ Γ₁ 𝒯 φ J a b' R Δ₁ Δg)
    (hJ : ∀ x, (∀ G ∈ J, x ∉ G) → φ x ∈ P₂ ∪ β '' {p | p.2 ≤ ε}) :
    ∃ Δ, Δ ⊆ P₂ ∪ β '' {p | p.2 ≤ ε} ∪ ⋃ G ∈ J, Δg G ∧ IsClosedDisc Δ ∧ discBd Δ = range φ := by
  classical
  have hP₂ := h.isClosed₂
  have hA : IsClosed (φ ⁻¹' P₂) := hP₂.preimage φ.continuous
  set Z := P₂ ∪ β '' {p | p.2 ≤ ε} ∪ ⋃ G ∈ J, Δg G with hZdef
  have hZ₁ : P₂ ∪ β '' {p | p.2 ≤ ε} ⊆ Z := subset_union_left
  have hφZ : ∀ x, φ x ∈ Z := by
    intro x
    by_cases hx : ∀ G ∈ J, x ∉ G
    · exact hZ₁ (hJ x hx)
    · push Not at hx
      obtain ⟨G, hG, hxG⟩ := hx
      refine .inr (mem_biUnion hG ((hP.piece G hG).sub_L ?_))
      exact ⟨x, (hP.gap G hG).subset_range hxG, rfl⟩
  have hZg : ∀ G ∈ J, Δg G ⊆ Z := fun G hG => subset_biUnion_of_mem (u
    := Δg) hG |>.trans subset_union_right
  obtain ⟨c, hc1, hc2, hc3, hc4⟩ := exists_curve hφ hA h.C_sub₂ hP hφZ hZg
  have hcN : ∀ x, c x ∈ P₂ ∪ β '' {p | p.2 ≤ ε} := by
    intro x
    by_cases hx : ∀ G ∈ J, x ∉ G
    · rw [hc1 x hx]
      exact hJ x hx
    · push Not at hx
      obtain ⟨G, hG, hxG⟩ := hx
      obtain ⟨k, hk⟩ := hc2 G hG x hxG
      exact .inl (h.C_sub₂ k hk)
  obtain ⟨c', h1, h2, h3, h4⟩ := exists_push hβ hP₂ hcN
  have hmemC : ∀ x, c x ∉ P₂ → (∀ G ∈ J, x ∉ G) := by
    intro x hx G hG hxG
    obtain ⟨k, hk⟩ := hc2 G hG x hxG
    exact hx (h.C_sub₂ k hk)
  have hshape : ∀ x, c' x ∈ range φ ∨ ∃ k, c' x ∈ C k := by
    intro x
    by_cases hx : c x ∈ P₂
    · rw [h1 x hx]
      by_cases hxJ : ∀ G ∈ J, x ∉ G
      · exact .inl ⟨x, (hc1 x hxJ).symm⟩
      · push Not at hxJ
        obtain ⟨G, hG, hxG⟩ := hxJ
        exact .inr (hc2 G hG x hxG)
    · obtain ⟨p, -, he⟩ := (hcN x).resolve_left hx
      rw [h2 x p he.symm]
      exact .inr ⟨_, hβ0 p.1⟩
  have hnorm : Γ.IsNormal (range c') := by
    rintro _ ⟨⟨x, rfl⟩, hU⟩
    rcases hshape x with hx | ⟨k, hk⟩
    · exact hFN ⟨hx, hU⟩
    · exact hN k ⟨hk, hU⟩
  have hsubV : range c' ∩ Γ.V ⊆ range c ∩ Γ.V := by
    rintro _ ⟨⟨x, rfl⟩, hV⟩
    refine ⟨?_, hV⟩
    by_cases hx : c x ∈ P₂
    · exact ⟨x, (h1 x hx).symm⟩
    · obtain ⟨p, hple, he⟩ := (hcN x).resolve_left hx
      have hv := h2 x p he.symm
      rw [hv] at hV ⊢
      by_cases hvF : β (p.1, 0) ∈ range φ
      · obtain ⟨x', hx'⟩ := hvF
        have hoff : ∀ G ∈ J, x' ∉ G := by
          intro G hG hxG
          refine Set.disjoint_left.mp (hP.gap G hG).disjoint hxG ?_
          change φ x' ∈ P₂
          rw [hx']
          exact hβ.zero _
        exact ⟨x', by rw [hc1 x' hoff, hx']⟩
      · exfalso
        apply hfib p.1 p.2 hV hvF hple
        have : β (p.1, p.2) = c x := he
        rw [this, hc1 x (hmemC x hx)]
        exact ⟨x, rfl⟩
  have hcount : (range c' ∩ Γ.V).ncard < θ :=
    lt_of_le_of_lt (ncard_le_ncard hsubV (Γ.finite_V.subset inter_subset_right))
      (lt_of_le_of_lt hc3 hsmall)
  obtain ⟨z, hz, hnull⟩ := hiii c' h3 hnorm hcount
  have hhom : ClosedCurvesHomotopicIn Z φ (ContinuousMap.const Circle z) :=
    (hc4.trans (closedCurvesHomotopicIn_mono h4 hZ₁)).trans
      (closedCurvesHomotopicIn_mono hnull (subset_union_left.trans hZ₁))
  have hO : IsOArc (range φ) := ⟨(φ.continuous.isClosedEmbedding hφ).isEmbedding.toHomeomorph⟩
  have hSS := h.surface.1
  have hbdS : Disjoint (range φ) (bd S) := by
    refine Set.disjoint_left.mpr fun x _ hx => hx (hSS.2.2 x)
  have hnO : IsNullHomotopicOArcIn Z (range φ) := by
    let e : Circle ≃ₜ range φ := (φ.continuous.isClosedEmbedding hφ).isEmbedding.toHomeomorph
    refine ⟨e, z, hZ₁ (.inl hz), ?_⟩
    have he : (⟨fun x => (e x).1, continuous_subtype_val.comp e.continuous⟩ : C(Circle, S)) = φ :=
      ContinuousMap.ext fun x => rfl
    rw [he]
    exact hhom
  obtain ⟨Δ, hΔZ, hΔ, hb⟩ := (epstein S Z (range φ) (IsClosedSurface.isSurface hSS) h.surface.2 hO
    (by rintro _ ⟨x, rfl⟩; exact hφZ x) hbdS).1 hnO
  exact ⟨Δ, hΔZ, hΔ, hb⟩

/-- The end of the proof of (5.3). The sides from (5.4) and the vertices of `F` on the common
boundary
cover the side of `Δ`, so [5, Theorem (6.2)] shows that this side is the small one. -/
theorem mem_of_sides (h : IsCappedSplit C P₁ P₂ ι D) (hΓ : IsCappedDrawing ι Γ Γ₁)
    (hN : ∀ k, Γ.IsNormal (C k)) (hT : IsTangle Γ₁.toHypergraph θ 𝒯) {F Δ : Set S}
    (hFN : Γ.IsNormal F) (hsmall : (F ∩ Γ.V).ncard < θ) (hΔ : IsClosed Δ) (hfr : frontier Δ = F)
    (J : Finset (Set Circle)) (Δ₁ : Set Circle → Set T)
    (hmem : ∀ G ∈ J, ((PaintingOrDrawing.drawing Γ₁).inter (Δ₁ G),
      (PaintingOrDrawing.drawing Γ₁).interOutside (Δ₁ G)) ∈ 𝒯)
    (hLF : ∀ G ∈ J, ∀ x ∈ frontier (Δ₁ G), x ∈ range ι → x ∈ capUp ι F)
    (hcV : ∀ p : P₁, p.1 ∈ Γ.V → p.1 ∈ Δ → p.1 ∈ F ∧ p.1 ∈ P₂ ∨ ∃ G ∈ J, ι p ∈ Δ₁ G)
    (hcE : ∀ e ∈ Γ₁.E, e ⊆ capUp ι Δ → ∃ G ∈ J, e ⊆ Δ₁ G) :
    ((PaintingOrDrawing.drawing Γ).inter Δ, (PaintingOrDrawing.drawing Γ).interOutside Δ) ∈
      inducedAcross ι Γ Γ₁ θ 𝒯 := by
  classical
  have hι := h.isEmbedding
  have hιi := hι.injective
  have hcP : CompactSpace P₁ := h.manifold₁.1
  have hclUp : ∀ {X : Set S}, IsClosed X → IsClosed (capUp ι X) := fun hX =>
    ((hX.preimage continuous_subtype_val).isCompact.image hι.continuous).isClosed
  set Q₁ := capUp ι Δ with hQ₁
  set Q₂ := capUp ι (closure (univ \ Δ)) with hQ₂
  have hmid : ∀ p : P₁, ι p ∈ Q₁ → ι p ∈ Q₂ → p.1 ∈ F := by
    intro p h₁ h₂
    have h₁' := (mem_capUp_val hιi).mp h₁
    have h₂' := (mem_capUp_val hιi).mp h₂
    rw [← hfr, frontier_eq_closure_inter_closure, compl_eq_univ_sdiff]
    exact ⟨subset_closure h₁', h₂'⟩
  have hF2 : ∀ p : P₁, p.1 ∈ F → ι p ∈ Q₁ ∩ Q₂ := by
    intro p hp
    have hp' : p.1 ∈ frontier Δ := hfr ▸ hp
    have hp2 := (mem_closure_diff_iff hΔ p.1).mpr (.inr hp')
    exact ⟨(mem_capUp_val hιi).mpr (frontier_subset_closure hp' |> hΔ.closure_subset),
      (mem_capUp_val hιi).mpr hp2⟩
  have hcov : ∀ p : P₁, ι p ∈ Q₁ ∪ Q₂ := by
    intro p
    by_cases hp : p.1 ∈ Δ
    · exact .inl ⟨p, hp, rfl⟩
    · exact .inr ⟨p, (mem_closure_diff_iff hΔ p.1).mpr (.inl hp), rfl⟩
  have hF₁ : F ∩ Γ.V ∩ P₁ ⊆ P₁ := inter_subset_right
  set Y₀ := capUp ι (F ∩ Γ.V ∩ P₁) with hY₀
  have hY₀V : Y₀ ⊆ Γ₁.V := by
    rw [hΓ.2]
    exact capUp_mono (inter_subset_left.trans inter_subset_right)
  have hY₀c : Y₀.ncard < θ := by
    rw [hY₀, ncard_capUp hιi hF₁]
    exact lt_of_le_of_lt (ncard_le_ncard inter_subset_left (Γ.finite_V.subset inter_subset_right))
      hsmall
  have hsub : Γ₁.V ∩ (Q₁ ∩ Q₂) ⊆ Y₀ := by
    rintro y ⟨hy, ⟨p, hp, rfl⟩, h₂⟩
    rw [hΓ.2] at hy
    exact ⟨p, ⟨⟨hmid p ⟨p, hp, rfl⟩ h₂, (mem_capUp_val hιi).mp hy⟩, p.2⟩, rfl⟩
  let side : Set Circle → Hypergraph T (Set T) × Hypergraph T (Set T) := fun G =>
    ((PaintingOrDrawing.drawing Γ₁).inter (Δ₁ G), (PaintingOrDrawing.drawing Γ₁).interOutside
      (Δ₁ G))
  have hq : ((PaintingOrDrawing.drawing Γ₁).inter Q₁, (PaintingOrDrawing.drawing Γ₁).inter Q₂) ∈ 𝒯
    := by
    refine mem_of_cover hT (hclUp hΔ) (hclUp isClosed_closure) ?_ ?_ ?_ ?_
      (((PaintingOrDrawing.drawing Γ₁).inter Y₀, (PaintingOrDrawing.drawing Γ₁).inter univ) ::
        J.toList.map side) ?_ ?_ ?_ ?_
    · intro y hy
      rw [hΓ.2] at hy
      obtain ⟨p, -, rfl⟩ := hy
      exact hcov p
    · intro e he y hy
      have hyU := (he.2.1 hy).1
      rw [hΓ.1] at hyU
      obtain ⟨p, -, rfl⟩ := hyU
      exact hcov p
    · intro e he y hy h₁ h₂
      obtain ⟨f, hf, hfP, rfl⟩ := exists_edge_capUp h hΓ hN he
      obtain ⟨p, hp, rfl⟩ := hy
      have hpF := hmid p h₁ h₂
      exact (hf.2.1 hp).2 (hFN ⟨hpF, (hf.2.1 hp).1⟩)
    · exact lt_of_le_of_lt (ncard_le_ncard hsub (Γ₁.finite_V.subset hY₀V)) hY₀c
    · intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact mem_vertices hT hY₀V hY₀c
      · obtain ⟨G, hG, rfl⟩ := List.mem_map.mp hp
        exact hmem G (Finset.mem_toList.mp hG)
    · intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · rintro y ⟨⟨hyV, hy⟩, -⟩
        obtain ⟨q, hq, rfl⟩ := hy
        exact ⟨hyV, hF2 q hq.1.1⟩
      · obtain ⟨G, hG, rfl⟩ := List.mem_map.mp hp
        intro y hy
        obtain ⟨hyF, hyV⟩ := inter_outside_subset hy
        have hyV' : y ∈ Γ₁.V := hyV
        have hyr : y ∈ range ι := by
          rw [hΓ.2] at hyV'
          exact capUp_subset_range _ hyV'
        obtain ⟨q, hq, rfl⟩ := hLF G (Finset.mem_toList.mp hG) y hyF hyr
        exact ⟨hyV', hF2 q hq⟩
    · rintro y ⟨hyV, ⟨p, hp, rfl⟩⟩
      have hpV : p.1 ∈ Γ.V := by
        rw [hΓ.2] at hyV
        exact (mem_capUp_val hιi).mp hyV
      rcases hcV p hpV hp with ⟨hF, -⟩ | ⟨G, hG, hpG⟩
      · exact ⟨_, List.mem_cons_self, ⟨hyV, ⟨p, ⟨⟨hF, hpV⟩, p.2⟩, rfl⟩⟩⟩
      · refine ⟨side G, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨G, Finset.mem_toList.mpr hG,
          rfl⟩), ?_⟩
        exact ⟨hyV, hpG⟩
    · intro e he heQ
      obtain ⟨G, hG, heG⟩ := hcE e he heQ
      refine ⟨side G, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨G, Finset.mem_toList.mpr hG,
        rfl⟩), ?_⟩
      exact ⟨he, heG⟩
  exact mem_inducedAcross h hΓ hN hΔ (by rw [hfr]; exact hFN) (by rw [hfr]; exact hsmall)
    (fun p => mem_capUp_val hιi) (fun p => mem_capUp_val hιi) hq

/-- The piece of the curve in a gap is a line of `Σ₁` to which (5.4) applies. -/
theorem exists_piece_of_gap [ConnectedSpace T] (h : IsCappedSplit C P₁ P₂ ι D)
    (hΓ : IsCappedDrawing ι Γ Γ₁) (hN : ∀ k, Γ.IsNormal (C k))
    (H : CapSetup (fun k => closure (D k)) Γ₁ θ 𝒯) (hφ : Function.Injective φ)
    (hFN : Γ.IsNormal (range φ)) (hsmall : (range φ ∩ Γ.V).ncard < θ) {G : Set Circle}
    {a₀ b₀ : 𝕀 → Circle} (hG : IsGap (φ ⁻¹' P₂) G a₀ b₀) :
    ∃ R Δ₁ Δ, PieceData C ι Γ Γ₁ 𝒯 (φ '' range a₀) (φ (a₀ 0)) (φ (a₀ 1)) R Δ₁ Δ := by
  have harc : IsArcMap (φ ∘ a₀) :=
    ⟨φ.continuous.comp hG.two.arc_left.1, hφ.comp hG.two.arc_left.2⟩
  have hL : IsLineWithEnds (φ '' range a₀) (φ (a₀ 0)) (φ (a₀ 1)) := by
    have := harc.isLineWithEnds
    rwa [range_comp] at this
  have h01 : (0 : 𝕀) ≠ 1 := zero_ne_one
  have hst : φ (a₀ 0) ≠ φ (a₀ 1) := fun he => h01 (hG.two.arc_left.2 (hφ he))
  have hsubF : φ '' range a₀ ⊆ range φ := image_subset_range _ _
  have hmeet : ∀ x ∈ φ '' range a₀, x ∈ P₂ → x = φ (a₀ 0) ∨ x = φ (a₀ 1) := by
    rintro _ ⟨_, ⟨r, rfl⟩, rfl⟩ hr
    by_cases h0 : r = 0
    · exact .inl (by rw [h0])
    by_cases h1 : r = 1
    · exact .inr (by rw [h1])
    exact (hG.off r h0 h1 hr).elim
  have hLP : φ '' range a₀ ⊆ P₁ := by
    refine hL.subset_closure_diff.trans (closure_minimal ?_ h.isClosed₁)
    rintro x ⟨hx, hn⟩
    refine (show x ∈ P₁ ∪ P₂ from h.union ▸ mem_univ x).resolve_right fun hx₂ => hn ?_
    exact hmeet x hx hx₂
  exact exists_piece h hΓ hN H hL hst (fun x hx => hFN ⟨hsubF hx.1, hx.2⟩)
    (lt_of_le_of_lt (ncard_le_ncard (inter_subset_inter_left _ hsubF)
      (Γ.finite_V.subset inter_subset_right)) hsmall) hLP hG.zero hG.one hmeet

/-- The second case of the proof of (5.3): an `O`-arc with at least two points in `Σ₂`. -/
theorem respect_of_cross [NeZero n] [ConnectedSpace T] (h : IsCappedSplit C P₁ P₂ ι D)
    (hΓ : IsCappedDrawing ι Γ Γ₁) (hN : ∀ k, Γ.IsNormal (C k)) (hT : IsTangle Γ₁.toHypergraph θ 𝒯)
    (H : CapSetup (fun k => closure (D k)) Γ₁ θ 𝒯) (hiii : CurvesNull Γ P₂ θ)
    (hφ : Function.Injective φ) (hFN : Γ.IsNormal (range φ)) (hsmall : (range φ ∩ Γ.V).ncard < θ)
    {x₀ y₀ : Circle} (hx₀ : φ x₀ ∈ P₂) (hy₀ : φ y₀ ∈ P₂) (hxy : x₀ ≠ y₀) :
    ∃ Δ : Set S, IsClosedDisc Δ ∧ subBd Δ = range φ ∧
      ((PaintingOrDrawing.drawing Γ).inter Δ, (PaintingOrDrawing.drawing Γ).interOutside Δ) ∈
        inducedAcross ι Γ Γ₁ θ 𝒯 := by
  classical
  have hι := h.isEmbedding
  have hιi := hι.injective
  have hSS := h.surface.1
  have hFc : IsClosed (range φ) := (isCompact_range φ.continuous).isClosed
  obtain ⟨β, hβ, hβP, hsurj, hβ0, hopen⟩ := exists_outerCollar h
  set A := φ ⁻¹' P₂ with hAdef
  have hA : IsClosed A := h.isClosed₂.preimage φ.continuous
  -- The fibres over the vertices off `F`.
  set W₀ := (Γ.V ∩ ⋃ k, C k) \ range φ with hW₀
  have hW₀f : W₀.Finite := (Γ.finite_V.subset inter_subset_left).subset sdiff_subset
  obtain ⟨ε₀, hε₀, hfib₀⟩ := exists_level_fibre hβ.cont hβ.inj hFc hW₀f disjoint_sdiff_left
  have hyv : ∀ v, ∃ y, v ∈ W₀ → β (y, 0) = v := by
    intro v
    by_cases hv : v ∈ W₀
    · obtain ⟨k, hk⟩ := mem_iUnion.mp hv.1.2
      obtain ⟨w, hw⟩ := hsurj k v hk
      exact ⟨(k, w), fun _ => hw⟩
    · exact ⟨(0, 1), fun hn => (hv hn).elim⟩
  choose yv hyv using hyv
  -- A point of each edge in `Σ₁`.
  have hpt : ∀ f, ∃ x, f ∈ Γ.E → x ∈ f := by
    intro f
    by_cases hf : f ∈ Γ.E
    · obtain ⟨x, hx⟩ := hf.1
      exact ⟨x, fun _ => hx⟩
    · exact ⟨φ 1, fun hn => (hf hn).elim⟩
  choose pt hpt using hpt
  set Q := ((fun v => β (yv v, ε₀)) '' W₀) ∪ (pt '' {f | f ∈ Γ.E ∧ f ⊆ P₁}) ∪ (Γ.V \ P₂) with hQ
  have hfin : {f | f ∈ Γ.E ∧ f ⊆ P₁}.Finite :=
    Γ.toHypergraph.edgeSet_finite.subset fun _ h => h.1
  have hQf : Q.Finite :=
    ((hW₀f.image _).union (hfin.image _)).union (Γ.finite_V.subset sdiff_subset)
  have hQP : Disjoint Q P₂ := by
    refine Set.disjoint_left.mpr ?_
    rintro _ (((⟨v, -, rfl⟩ | ⟨f, ⟨hf, hfP⟩, rfl⟩)) | hx) hx₂
    · exact hβ.pos _ _ hε₀ hx₂
    · rcases edge_side h hN hf with ⟨-, hd⟩ | ⟨-, hd⟩
      · exact Set.disjoint_left.mp hd (hpt f hf) hx₂
      · exact Set.disjoint_left.mp hd (hpt f hf) (hfP (hpt f hf))
    · exact hx.2 hx₂
  obtain ⟨ε, hε, hle, hQε⟩ := exists_level_off hβ hQf hQP hε₀
  -- A compact set of points of the circle off the collar, covered by finitely many gaps.
  set W := P₂ ∪ β '' {p | p.2 < ε} with hWdef
  have hWo : IsOpen W := hopen ε hε
  set K := (φ ⁻¹' W)ᶜ with hKdef
  have hKc : IsCompact K := (hWo.preimage φ.continuous).isClosed_compl.isCompact
  have hgap : ∀ z, ∃ G, z ∈ K → (∃ a b, IsGap A G a b) ∧ z ∈ G := by
    intro z
    by_cases hz : z ∈ K
    · have hzA : z ∉ A := fun hA' => hz (.inl hA')
      obtain ⟨G, a, b, hG, hzG⟩ := exists_gap hA hx₀ hy₀ hxy hzA
      exact ⟨G, fun _ => ⟨⟨a, b, hG⟩, hzG⟩⟩
    · exact ⟨∅, fun hn => (hz hn).elim⟩
  choose G' hG' using hgap
  obtain ⟨t, htK, hcov⟩ := hKc.elim_nhds_subcover G' fun z hz => by
    obtain ⟨⟨a, b, hG⟩, hzG⟩ := hG' z hz
    exact hG.isOpen.mem_nhds hzG
  set J := t.image G' with hJdef
  have hJg : ∀ G ∈ J, ∃ a b, IsGap A G a b := by
    intro G hG
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hG
    exact (hG' z (htK z hz)).1
  have hdata : ∀ G : Set Circle, ∃ (a b : 𝕀 → Circle) (R : Set S) (Δ₁ : Set T) (Δg : Set S), G ∈ J →
      IsGap A G a b ∧ PieceData C ι Γ Γ₁ 𝒯 (φ '' range a) (φ (a 0)) (φ (a 1)) R Δ₁ Δg := by
    intro G
    by_cases hG : G ∈ J
    · obtain ⟨a, b, hg⟩ := hJg G hG
      obtain ⟨R, Δ₁, Δg, hd⟩ := exists_piece_of_gap h hΓ hN H hφ hFN hsmall hg
      exact ⟨a, b, R, Δ₁, Δg, fun _ => ⟨hg, hd⟩⟩
    · exact ⟨fun _ => 1, fun _ => 1, ∅, ∅, ∅, fun hn => (hG hn).elim⟩
  choose a b R Δ₁ Δg hab using hdata
  have hP : Pieces C P₂ ι Γ Γ₁ 𝒯 φ J a b R Δ₁ Δg :=
    ⟨fun G hG => (hab G hG).1, fun G hG => (hab G hG).2⟩
  have hJ : ∀ x, (∀ G ∈ J, x ∉ G) → φ x ∈ P₂ ∪ β '' {p | p.2 ≤ ε} := by
    intro x hx
    have hxK : x ∉ K := by
      intro hK
      obtain ⟨z, hz⟩ := mem_iUnion.mp (hcov hK)
      obtain ⟨hzt, hxz⟩ := mem_iUnion.mp hz
      exact hx _ (Finset.mem_image_of_mem _ hzt) hxz
    have hxW : φ x ∈ W := by
      by_contra hn
      exact hxK hn
    rcases hxW with hx' | ⟨p, hp, he⟩
    · exact .inl hx'
    · exact .inr ⟨p, le_of_lt (show p.2 < ε from hp), he⟩
  have hfib : ∀ y s, β (y, 0) ∈ Γ.V → β (y, 0) ∉ range φ → s ≤ ε → β (y, s) ∉ range φ := by
    intro y s hv hn hs
    exact hfib₀ y s ⟨⟨hv, mem_iUnion.mpr ⟨_, hβ0 y⟩⟩, hn⟩ (hs.trans hle)
  obtain ⟨Δ, hΔZ, hΔ, hb⟩ := exists_disc_of_pieces h hN hφ hFN hsmall hiii hβ hβ0 hfib hP hJ
  have hfr : frontier Δ = range φ := by rw [IsClosedDisc.frontier_eq_discBd hSS hΔ, hb]
  have hcl := hΔ.isClosed
  refine ⟨Δ, hΔ, by rw [subBd_eq_frontier, hfr], ?_⟩
  have hoff : ∀ x ∈ Δ, x ∉ P₂ → x ∈ Q → ∃ G ∈ J, x ∈ Δg G := by
    intro x hx hx₂ hxQ
    rcases hΔZ hx with (hx' | hx') | hx'
    · exact (hx₂ hx').elim
    · exact (hQε x hxQ hx').elim
    · obtain ⟨G, hG, hxG⟩ := mem_iUnion₂.mp hx'
      exact ⟨G, hG, hxG⟩
  have hLF : ∀ G ∈ J, ∀ x ∈ frontier (Δ₁ G), x ∈ range ι → x ∈ capUp ι (range φ)
    := fun G hG x hx hr =>
    capUp_mono (image_subset_range _ _) ((hab G hG).2.frontier₁ x hx hr)
  have hlift : ∀ G ∈ J, ∀ A' : Set T, IsPreconnected A' → A' ⊆ range ι →
      (∀ q : P₁, ι q ∈ A' → q.1 ∉ range φ) → (A' ∩ Δ₁ G).Nonempty → A' ⊆ Δ₁ G := by
    intro G hG A' hc hr hmiss hne
    refine subset_of_frontier hc (hab G hG).2.disc₁.isClosed hne fun y hy hf => ?_
    obtain ⟨q, hq, rfl⟩ := hLF G hG y hf (hr hy)
    exact hmiss q hy hq
  refine mem_of_sides h hΓ hN hT hFN hsmall hcl hfr J Δ₁ (fun G hG => (hab G hG).2.mem) hLF ?_ ?_
  · intro p hpV hpΔ
    by_cases hp2 : p.1 ∈ P₂
    · by_cases hpF : p.1 ∈ range φ
      · exact .inl ⟨hpF, hp2⟩
      · right
        have hpm : p.1 ∈ P₁ ∩ P₂ := ⟨p.2, hp2⟩
        rw [h.inter] at hpm
        have hpW : p.1 ∈ W₀ := ⟨⟨hpV, hpm⟩, hpF⟩
        have hy0 := hyv _ hpW
        set y := yv p.1 with hy
        have hmissF : ∀ s ≤ ε₀, β (y, s) ∉ range φ := fun s hs =>
          hfib₀ y s (hy0.symm ▸ hpW) hs
        have hτ : Continuous fun s : 𝕀 => β (y, s) := hβ.cont.comp (Continuous.prodMk_right y)
        have hA₁ : (fun s : 𝕀 => β (y, s)) '' Iic ε₀ ⊆ Δ := by
          refine subset_of_frontier (isPreconnected_Iic.image _ hτ.continuousOn) hcl
            ⟨p.1, ⟨0, show (⊥ : 𝕀) ≤ ε₀ from bot_le, hy0⟩, hpΔ⟩ ?_
          rintro _ ⟨s, hs, rfl⟩
          rw [hfr]
          exact hmissF s hs
        have hpv : β (y, ε₀) ∈ Δ := hA₁ ⟨ε₀, le_rfl, rfl⟩
        have hpv2 : β (y, ε₀) ∉ P₂ := hβ.pos _ _ hε₀
        have hpvQ : β (y, ε₀) ∈ Q := .inl (.inl ⟨p.1, hpW, rfl⟩)
        obtain ⟨G, hG, hpG⟩ := hoff _ hpv hpv2 hpvQ
        refine ⟨G, hG, ?_⟩
        have hτ' : Continuous fun s : 𝕀 => ι ⟨β (y, s), hβP _⟩ :=
          hι.continuous.comp (hτ.subtype_mk _)
        refine hlift G hG ((fun s : 𝕀 => ι ⟨β (y, s), hβP _⟩) '' Iic ε₀)
          (isPreconnected_Iic.image _ hτ'.continuousOn)
          (by rintro _ ⟨s, -, rfl⟩; exact ⟨_, rfl⟩) ?_ ?_
          ⟨0, show (⊥ : 𝕀) ≤ ε₀ from bot_le, ?_⟩
        · rintro q ⟨s, hs, he⟩
          have : q = ⟨β (y, s), hβP _⟩ := (hιi he).symm
          rw [this]
          exact hmissF s hs
        · exact ⟨_, ⟨ε₀, le_rfl, rfl⟩, (hab G hG).2.sub₁ ⟨⟨_, hβP _⟩, hpG, rfl⟩⟩
        · exact congrArg ι (Subtype.ext hy0)
    · right
      obtain ⟨G, hG, hpG⟩ := hoff p.1 hpΔ hp2 (.inr ⟨hpV, hp2⟩)
      exact ⟨G, hG, (hab G hG).2.sub₁ ⟨p, hpG, rfl⟩⟩
  · intro e he heQ
    obtain ⟨f, hf, hfP, rfl⟩ := exists_edge_capUp h hΓ hN he
    have hfΔ : f ⊆ Δ := fun x hx => (mem_capUp_val hιi).mp (heQ (val_mem_capUp (hfP hx) hx))
    have hptf := hpt f hf
    have hpt2 : pt f ∉ P₂ := by
      rcases edge_side h hN hf with ⟨-, hd⟩ | ⟨-, hd⟩
      · exact Set.disjoint_left.mp hd hptf
      · exact (Set.disjoint_left.mp hd hptf (hfP hptf)).elim
    obtain ⟨G, hG, hpG⟩ := hoff _ (hfΔ hptf) hpt2 (.inl (.inr ⟨f, ⟨hf, hfP⟩, rfl⟩))
    refine ⟨G, hG, hlift G hG _ he.2.2.1.isConnected.isPreconnected (capUp_subset_range _) ?_ ?_⟩
    · intro q hq hqF
      have hqf := (mem_capUp_val hιi).mp hq
      exact (hf.2.1 hqf).2 (hFN ⟨hqF, (hf.2.1 hqf).1⟩)
    · exact ⟨_, val_mem_capUp (hfP hptf) hptf, (hab G hG).2.sub₁ ⟨⟨_, hfP hptf⟩, hpG, rfl⟩⟩

/-- **Graph Minors XII, (5.4)** (page 255), for a `Γ`-normal line `F` in `Σ₁` with ends `s, t` on
the common boundary `⋃ k, C k` and no other point on it: there is a `Γ`-normal line `R` in
`⋃ k, C k` with the same ends as `F` and at most as many vertices of `Γ`, bounding with `F` a
closed disc `Δ ⊆ Σ₁` whose capped separation lies in `𝒯`. -/
theorem theorem_5_4_proof [ConnectedSpace T] (h : IsCappedSplit C P₁ P₂ ι D)
    (hΓ : IsCappedDrawing ι Γ Γ₁) (hN : ∀ k, Γ.IsNormal (C k)) (hT : IsTangle Γ₁.toHypergraph θ 𝒯)
    (hR : (PaintingOrDrawing.drawing Γ₁).IsRespectful θ 𝒯)
    (hi : ∀ k l, k ≠ l → ∀ F : Set S, IsLine F → Γ.IsNormal F → F ⊆ P₁ →
      (F ∩ C k).Nonempty → (F ∩ C l).Nonempty → θ ≤ (F ∩ Γ.V).ncard)
    (hm : ∀ k, θ ≤ (Γ.V ∩ C k).ncard)
    (hf : ∀ k, ∀ X ⊆ capUp ι (Γ.V ∩ C k), X.ncard ≤ θ → IsFreeSet Γ₁.toHypergraph 𝒯 θ X)
    {F : Set S} {s t : S} (hF : IsLineWithEnds F s t) (hst : s ≠ t) (hFN : Γ.IsNormal F)
    (hsmall : (F ∩ Γ.V).ncard < θ) (hFP : F ⊆ P₁)
    (hs : s ∈ ⋃ k, C k) (ht : t ∈ ⋃ k, C k)
    (hmeet : ∀ x ∈ F, x ∈ ⋃ k, C k → x = s ∨ x = t) :
    ∃ R : Set S, ∃ Δ : Set S, ∃ Δ₁ : Set T,
      IsLineWithEnds R s t ∧ Γ.IsNormal R ∧ R ⊆ ⋃ k, C k ∧
      (R ∩ Γ.V).ncard ≤ (F ∩ Γ.V).ncard ∧
      IsClosedDisc Δ ∧ Δ ⊆ P₁ ∧ discBd Δ = F ∪ R ∧
      IsClosedDisc Δ₁ ∧ capUp ι Δ ⊆ Δ₁ ∧
      (∀ x ∈ frontier Δ₁, x ∈ range ι → x ∈ capUp ι F) ∧
      ((PaintingOrDrawing.drawing Γ₁).inter Δ₁,
        (PaintingOrDrawing.drawing Γ₁).interOutside Δ₁) ∈ 𝒯 := by
  have H := capSetup h hΓ hN hT hR hi hm hf
  obtain ⟨R, Δ₁, Δ, hd⟩ := exists_piece h hΓ hN H hF hst hFN hsmall hFP
    (h.inter ▸ hs).2 (h.inter ▸ ht).2
    (fun x hxF hxP₂ => hmeet x hxF (h.inter ▸ ⟨hFP hxF, hxP₂⟩))
  obtain ⟨k, hk⟩ := hd.on
  exact ⟨R, Δ, Δ₁, hd.line, fun x hx => hN k ⟨hk hx.1, hx.2⟩, hk.trans (subset_iUnion C k),
    hd.count, hd.disc, hd.sub_P, hd.bd, hd.disc₁, hd.sub₁, hd.frontier₁, hd.mem⟩

/-- **Graph Minors XII, (5.3)** (pages 254–255). -/
theorem theorem_5_3_proof [NeZero n] [ConnectedSpace T] (h : IsCappedSplit C P₁ P₂ ι D)
    (hΓ : IsCappedDrawing ι Γ Γ₁) (hN : ∀ k, Γ.IsNormal (C k)) (hT : IsTangle Γ₁.toHypergraph θ 𝒯)
    (hR : (PaintingOrDrawing.drawing Γ₁).IsRespectful θ 𝒯)
    (hi : ∀ k l, k ≠ l → ∀ F : Set S, IsLine F → Γ.IsNormal F → F ⊆ P₁ →
      (F ∩ C k).Nonempty → (F ∩ C l).Nonempty → θ ≤ (F ∩ Γ.V).ncard)
    (hm : ∀ k, θ ≤ (Γ.V ∩ C k).ncard)
    (hf : ∀ k, ∀ X ⊆ capUp ι (Γ.V ∩ C k), X.ncard ≤ θ → IsFreeSet Γ₁.toHypergraph 𝒯 θ X)
    (hiii : CurvesNull Γ P₂ θ) :
    (PaintingOrDrawing.drawing Γ).IsRespectful θ (inducedAcross ι Γ Γ₁ θ 𝒯) := by
  have H := capSetup h hΓ hN hT hR hi hm hf
  refine ⟨h.surface.2, fun F hO hFN hsmall => ?_⟩
  by_cases hs : (F ∩ P₂).Subsingleton
  · exact respect_of_inside h hΓ hN H hO hFN hsmall (subset_of_subsingleton h hO hs)
  · obtain ⟨u, hu, v, hv, huv⟩ := not_subsingleton_iff.mp hs
    obtain ⟨e⟩ := hO
    let φ : C(Circle, S) := ⟨fun x => (e x).1, continuous_subtype_val.comp e.continuous⟩
    have hφ : Function.Injective φ := fun x y hxy => e.injective (Subtype.ext hxy)
    have hr : range φ = F := by
      ext x
      constructor
      · rintro ⟨w, rfl⟩
        exact (e w).2
      · intro hx
        exact ⟨e.symm ⟨x, hx⟩, by simp [φ]⟩
    have hu' : φ (e.symm ⟨u, hu.1⟩) = u := by simp [φ]
    have hv' : φ (e.symm ⟨v, hv.1⟩) = v := by simp [φ]
    have := respect_of_cross h hΓ hN hT H hiii (φ := φ) hφ
      (by rw [hr]; exact hFN) (by rw [hr]; exact hsmall)
      (x₀ := e.symm ⟨u, hu.1⟩) (y₀ := e.symm ⟨v, hv.1⟩) (by rw [hu']; exact hu.2)
      (by rw [hv']; exact hv.2) (fun he => huv (by rw [← hu', ← hv', he]))
    rwa [hr] at this

end GraphMinor.GM12
