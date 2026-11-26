/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.CuffLayers

/-!
# Sets that reach out from `A(C)`

Graph Minors VII, (5.9), page 234: "there is a solid, connected, $G$-normal set $X \subseteq \Sigma$
with $y \in X$ and $A(C) \subseteq X$, with $$ |V(G) \cap X| \le j + |V(G) \cap A(C)| \le
\frac{1}{2}v + k(C) + 2 + vk(C) \le 2kv - 1 < \alpha(G) $$ since $k(C) \le 2k - 2$. Hence $X$
surrounds $C$".
-/

@[expose] public section

namespace GraphMinor.GM07

open Set Topology Function GraphMinor.Surface GraphMinor.GM11

universe u

variable {S : Type u} [TopologicalSpace S]

/-- A line is connected. -/
theorem isPreconnected_of_isLine {Y : Type*} [TopologicalSpace Y] {L : Set Y} {u v : Y}
  (h : IsLineWithEnds L u v) : IsPreconnected L := by
  obtain ⟨f, -, -⟩ := id h
  have h3 : range (fun t => (f t).1) = L := by
    rw [show (fun t => (f t).1) = Subtype.val ∘ f from rfl, f.surjective.range_comp,
      Subtype.range_coe]
  exact h3 ▸ isPreconnected_range (by fun_prop)

/-- "Hence `X` surrounds `C`": a solid connected `G`-normal set with few vertices that holds a set
surrounding `C` surrounds `C`, by (5.3). -/
theorem surrounds_of_superset (hS : IsSurface S) [ConnectedSpace S] (hcyl : ¬ Nonempty
  (S ≃ₜ SurfaceModel 0 0 2)) {G : Drawing S} {C F X : Set S} {r r' : ℕ} (hF : IsScriptASet G r C F)
    (hFX : F ⊆ X) (hsol : IsSolid X) (hcon : IsConnected X) (hn : G.IsNormal X)
    (hcard : (G.V ∩ X).ncard ≤ r') (hα : r' < alpha G) (hα' : r + r' < alpha G) : IsScriptASet G r'
      C X := by
  have hC : C ∈ cuffs S := hF.2.2.2.1.1
  have hnear : IsNearPlanar X := by
    by_contra hnp
    have h1 : IsAlphaCandidate G X := ⟨hsol, hcon, hn, hnp⟩
    have h2 : alpha G ≤ (X ∩ G.V).ncard := Nat.sInf_le ⟨X, h1, rfl⟩
    rw [inter_comm] at h2
    omega
  have hnotp : ¬ IsPlanar X := fun ⟨Δ, h1, h2⟩ => hF.2.2.2.1.2.2 ⟨Δ, h1, hFX.trans h2⟩
  rcases hnear with h | ⟨C₁, hC₁, h⟩
  · exact absurd h hnotp
  · by_cases he : C₁ = C
    · subst he
      exact ⟨hsol, hcon, hn, ⟨hC₁, h, hnotp⟩, hcard⟩
    · exfalso
      obtain ⟨x, hx⟩ := hF.2.1.nonempty
      have h3 : x ∈ scriptA G r C := ⟨F, ⟨hF.1, hF.2.1, hF.2.2.1, hF.2.2.2.1, hF.2.2.2.2⟩, hx⟩
      have h4 : x ∈ scriptA G r' C₁ := ⟨X, ⟨hsol, hcon, hn, ⟨hC₁, h, hnotp⟩, hcard⟩, hFX hx⟩
      have h5 := theorem_5_3_proof hS hcyl G hC hC₁ (Ne.symm he) hα'
      exact (h5 ▸ (⟨h3, h4⟩ : x ∈ scriptA G r C ∩ scriptA G r' C₁) : x ∈ (∅ : Set S))

variable {T : Type u} [TopologicalSpace T] {C : Set S} {j : S → T} {D : Set T}

/-- **The set `X` of page 234.** A path in `Σ + CHat` from a cuff disc `E` to a point `t` off it,
which meets `G` off the inside of `E` in at most `n` vertices, gives a set `X` that surrounds `C`,
holds `t` and the boundary of `E`,
and has at most `n` more vertices. -/
theorem exists_reach_of_path (hS : IsSurface S) [ConnectedSpace S] (hcyl : ¬ Nonempty
  (S ≃ₜ SurfaceModel 0 0 2)) (hC : C ∈ cuffs S) (hc : IsCappedCuff C T j D)
    (hns : ¬ IsSphere T) {G : Drawing S} {ra n : ℕ} {E : Set T} (hd : IsCuffDisc G j D ra E)
    {δ : unitInterval → T} (hδ : Continuous δ) (h0 : δ 0 ∈ E) (h1 : δ 1 ∉ E) {X' : Set S}
      (hX'V : X' ⊆ G.V) (hX'c : X'.ncard ≤ n) (hnorm : ∀ z ∈ G.U, j z ∉ discInt E → j z ∈ range δ
        → z ∈ X') (hα : ra + n < alpha G) (hα' : ra + (ra + n) < alpha G) :
    ∃ z X, δ 1 = j z ∧ IsScriptASet G (ra + n) C X ∧ z ∈ X ∧ j ⁻¹' discBd E ⊆ X := by
  classical
  have hT := hc.isSurface
  have : T2Space T := hT.2.1
  have hman := hT.2.2
  have hS2 : T2Space S := hS.2.1
  obtain ⟨hΔ, hDE, hn, hcount⟩ := id hd
  have hj := hc.isEmbedding
  have hclS : IsClosed {τ | δ τ ∈ E} := hΔ.isClosed.preimage hδ
  have hne : {τ | δ τ ∈ E}.Nonempty := ⟨0, h0⟩
  let σ := sSup {τ | δ τ ∈ E}
  have hσ : δ σ ∈ E := hclS.csSup_mem hne (OrderTop.bddAbove _)
  have haft : ∀ τ, σ < τ → δ τ ∉ E := fun τ h3 h4 => absurd (le_sSup (show τ ∈ {τ | δ τ ∈ E} from
    h4)) (not_le.mpr h3)
  have hσ1 : σ < 1 := lt_of_le_of_ne le_top fun h3 => h1 (h3 ▸ hσ)
  -- the part after the last time in `E`
  have hbd : δ σ ∈ discBd E := by
    refine frontier_disc_subset hman hΔ ?_
    rw [frontier_eq_closure_inter_closure]
    refine ⟨subset_closure hσ, ?_⟩
    have h3 : σ ∈ closure (Ioi σ) := by
      rw [closure_Ioi' (a := σ) ⟨1, hσ1⟩]
      exact self_mem_Ici
    exact map_mem_closure hδ h3 fun τ hτ => haft τ hτ
  have hσv : (0 : ℝ) ≤ σ.1 ∧ σ.1 < 1 := ⟨σ.2.1, hσ1⟩
  let f : unitInterval → unitInterval := fun u => ⟨σ.1 + (1 - σ.1) * u.1, by
    have := u.2.1
    have := u.2.2
    constructor <;> nlinarith [hσv.1, hσv.2]⟩
  have hfc : Continuous f := by
    refine Continuous.subtype_mk ?_ _
    fun_prop
  let δ' : unitInterval → T := δ ∘ f
  have hδ'c : Continuous δ' := hδ.comp hfc
  have hf0 : f 0 = σ := Subtype.ext (by simp [f])
  have hf1 : f 1 = 1 := Subtype.ext (by simp [f])
  have hne' : δ' 0 ≠ δ' 1 := by
    simp only [δ', comp_apply, hf0, hf1]
    exact fun h3 => h1 (h3 ▸ hσ)
  obtain ⟨e, hec, hei, he0, he1, her⟩ := exists_arc_of_path hδ'c hne'
  simp only [δ', comp_apply, hf0, hf1] at he0 he1
  have hoff : ∀ {x}, x ∈ range e → x ∉ E ∨ x = δ σ := fun {x} hx => by
    obtain ⟨u, rfl⟩ := her hx
    by_cases hu : u = 0
    · subst hu
      exact .inr (by simp [δ', hf0])
    · refine .inl (haft _ ?_)
      have h3 : (0 : ℝ) < u.1 := lt_of_le_of_ne u.2.1 fun h => hu (Subtype.ext h.symm)
      change σ.1 < σ.1 + (1 - σ.1) * u.1
      nlinarith [hσv.2]
  have hrδ : range e ⊆ range δ := fun x hx => by
    obtain ⟨u, rfl⟩ := her hx
    exact ⟨f u, rfl⟩
  have hbr := discBd_subset_range hc hDE
  have hrj : range e ⊆ range j := fun x hx => by
    rcases hoff hx with h3 | h3
    · exact compl_disc_subset_range hc hDE h3
    · exact h3 ▸ hbr hbd
  have hl : IsLineWithEnds (range e) (δ σ) (δ 1) := by
    obtain ⟨u₀, hu₀⟩ := hbr hbd
    have : CompactSpace unitInterval := inferInstance
    have hem : IsEmbedding e := (hec.isClosedEmbedding hei).isEmbedding
    refine ⟨(hem.toHomeomorph), ?_, ?_⟩
    · exact he0
    · exact he1
  obtain ⟨u₀, hu₀⟩ := hbr hbd
  obtain ⟨z, hz⟩ := hrj (show δ 1 ∈ range e from ⟨1, he1⟩)
  rw [← hu₀, ← hz] at hl
  have hL' := pull_line hj hl hrj
  set L' := j ⁻¹' range e with hL'def
  set F := j ⁻¹' discBd E with hFdef
  have hu₀F : u₀ ∈ F := by
    change j u₀ ∈ discBd E
    rw [hu₀]
    exact hbd
  have hO := isOArc_preimage_bd hc hΔ hDE
  have hsol : IsSolid (F ∪ L') := theorem_11_6_proof hS (isSolid_of_isOArc hS hO)
    (isSolid_of_isLineWithEnds hS hL')
  have hLp : IsPreconnected L' := isPreconnected_of_isLine hL'
  have hcon : IsConnected (F ∪ L') := (isConnected_of_isOArc hO).union ⟨u₀, hu₀F, hL'.left_mem⟩
    ⟨⟨u₀, hL'.left_mem⟩, hLp⟩
  have hcase : ∀ {w}, w ∈ L' → w ∈ G.U → w ∈ X' ∨ w ∈ F := fun {w} hw hU => by
    rcases hoff hw with h3 | h3
    · exact .inl (hnorm w hU (fun h4 => h3 h4.1) (hrδ hw))
    · refine .inr ?_
      change j w ∈ discBd E
      rw [h3]
      exact hbd
  have hnormal : G.IsNormal (F ∪ L') := by
    rintro w ⟨hw | hw, hU⟩
    · exact hn ⟨hw, hU⟩
    · rcases hcase hw hU with h3 | h3
      · exact hX'V h3
      · exact hn ⟨h3, hU⟩
  have hcard : (G.V ∩ (F ∪ L')).ncard ≤ ra + n := by
    have hsub : G.V ∩ (F ∪ L') ⊆ (G.V ∩ F) ∪ X' := by
      rintro w ⟨hV, hw | hw⟩
      · exact .inl ⟨hV, hw⟩
      · rcases hcase hw (G.V_subset_U hV) with h3 | h3
        · exact .inr h3
        · exact .inl ⟨hV, h3⟩
    have hfin : ((G.V ∩ F) ∪ X').Finite := (G.finite_V.subset inter_subset_left).union
      (G.finite_V.subset hX'V)
    have h3 := ncard_le_ncard hsub hfin
    have h4 := ncard_union_le (G.V ∩ F) X'
    omega
  refine ⟨z, F ∪ L', hz.symm, surrounds_of_superset hS hcyl (hd.isScriptASet hS hC hc hns)
    subset_union_left hsol hcon hnormal hcard hα hα', .inr hL'.right_mem, subset_union_left⟩

/-- **Reaching out along a connected set of a closed surface.** Let `Σ + CHat` sit in a closed
surface `W`, by `i`, and let `A` be a path-connected set of `W` from a cuff disc `E`, that meets `G`
off the inside of `E` in at most `n` vertices. Then
`A` stays in `Σ + CHat`, and each point of `A` is in `E` or in a set `X` as on page 234. -/
theorem exists_reach_in_closed {W : Type} [TopologicalSpace W]
  (hS : IsSurface S) [ConnectedSpace S] {a b c : ℕ} (habc : 3 ≤ 3 * a + 3 * b + c) (hm : Nonempty
    (S ≃ₜ SurfaceModel a b c)) (hcyl : ¬ Nonempty (S ≃ₜ SurfaceModel 0 0 2)) (hC : C ∈ cuffs S)
    (hc : IsCappedCuff C T j D) (hbT : bd T = j '' (bd S \ C)) {G : Drawing S}
      (hG : G.IsProper) {ra n : ℕ} {E : Set T} (hd : IsCuffDisc G j D ra E) {i : T → W}
        (hi : IsClosedEmbedding i) (hopen : IsOpen (i '' (bd T)ᶜ))
    {A : Set W} (hA : IsPathConnected A) {p : T} (hpE : p ∈ E) (hpA : i p ∈ A) {X' : Set S}
      (hX'V : X' ⊆ G.V) (hX'c : X'.ncard ≤ n) (hnorm : ∀ z ∈ G.U, j z ∉ discInt E → i (j z) ∈ A
        → z ∈ X') (hα : ra + n < alpha G) (hα' : ra + (ra + n) < alpha G)
    (hα₂ : ∀ C₁ ∈ cuffs S, C₁ ≠ C → ra + n + (G.V ∩ C₁).ncard < alpha G) {y : W} (hy : y ∈ A) :
    ∃ t, y = i t ∧ t ∉ bd T ∧ (t ∈ E ∨ ∃ z X, t = j z ∧ IsScriptASet G (ra + n) C X ∧ z ∈ X
      ∧ j ⁻¹' discBd E ⊆ X) := by
  classical
  have hT := hc.isSurface
  have : T2Space T := hT.2.1
  have : T2Space S := hS.2.1
  have : Nonempty T := ⟨p⟩
  have hii := hi.injective
  have hns : ¬ IsSphere T := not_isSphere_cap hS habc hm hc
  have hα₁ : ∀ C₁ ∈ cuffs S, C₁ ≠ C → ra + (G.V ∩ C₁).ncard < alpha G := fun C₁ h1 h2 => by
    have := hα₂ C₁ h1 h2
    omega
  obtain ⟨γ, hγ⟩ := hA.joinedIn _ hpA _ hy
  have hrange : ∀ τ, γ τ ∈ A := hγ
  -- the claim for a time up to which `γ` stays in `Σ + CHat`
  have key : ∀ τ : unitInterval, (∀ τ', τ' ≤ τ → γ τ' ∈ range i) → ∃ t, γ τ = i t ∧ t ∉ bd T ∧
    (t ∈ E ∨ ∃ z X, t = j z ∧ IsScriptASet G (ra + n) C X ∧ z ∈ X ∧ j ⁻¹' discBd E ⊆ X) := fun τ hτ
      => by
    obtain ⟨t, ht⟩ := hτ τ le_rfl
    refine ⟨t, ht.symm, ?_⟩
    by_cases htE : t ∈ E
    · exact ⟨fun hb => disjoint_left.mp (hd.disjoint_bd hS habc hm hcyl hG hC hc hbT (r
        := ra) hα₁) htE hb, .inl htE⟩
    let g : unitInterval → unitInterval := fun u => ⟨u.1 * τ.1, by
      have := u.2.1
      have := u.2.2
      have := τ.2.1
      have := τ.2.2
      constructor <;> nlinarith⟩
    have hgc : Continuous g := by
      refine Continuous.subtype_mk ?_ _
      fun_prop
    have hgle : ∀ u, g u ≤ τ := fun u => by
      change u.1 * τ.1 ≤ τ.1
      nlinarith [u.2.2, τ.2.1]
    let δ : unitInterval → T := fun u => invFun i (γ (g u))
    have hδi : ∀ u, i (δ u) = γ (g u) := fun u => invFun_eq (hτ _ (hgle u))
    have hδc : Continuous δ := by
      rw [hi.isEmbedding.continuous_iff]
      have : (i ∘ δ) = γ ∘ g := funext hδi
      rw [this]
      exact γ.continuous.comp hgc
    have hg0 : g 0 = 0 := Subtype.ext (by simp [g])
    have hg1 : g 1 = τ := Subtype.ext (by simp [g])
    have hδ0 : δ 0 = p := hii (by rw [hδi, hg0, γ.source])
    have hδ1 : δ 1 = t := hii (by rw [hδi, hg1, ht])
    obtain ⟨z, X, h1, h2, h3, h4⟩ := exists_reach_of_path hS hcyl hC hc hns hd hδc (hδ0 ▸ hpE)
      (hδ1 ▸ htE) hX'V hX'c (fun w hw h5 h6 => hnorm w hw h5 (by
      obtain ⟨u, hu⟩ := h6
      rw [← hu, hδi]
      exact hrange _)) hα hα'
    rw [hδ1] at h1
    refine ⟨fun hb => ?_, .inr ⟨z, X, h1, h2, h3, h4⟩⟩
    rw [hbT, h1] at hb
    obtain ⟨w, hw, he⟩ := hb
    have hwz : w = z := hc.isEmbedding.injective he
    subst hwz
    exact off_other_cuffs hS habc hm hcyl hG hC hα₂ (⟨X, ⟨h2.1, h2.2.1, h2.2.2.1, h2.2.2.2.1,
      h2.2.2.2.2⟩, h3⟩) hw.1 hw.2
  let P : Set unitInterval := {τ | ∀ τ', τ' ≤ τ → γ τ' ∈ range i}
  have hPd : ∀ {x y}, y ≤ x → x ∈ P → y ∈ P := fun {x y} h h1 τ' h2 => h1 τ' (h2.trans h)
  have hPc : IsClosed P := by
    rw [← closure_subset_iff_isClosed]
    intro x hx τ' h1
    rcases h1.lt_or_eq with h2 | rfl
    · obtain ⟨y, hy1, hy2⟩ := mem_closure_iff.mp hx _ isOpen_Ioi h2
      exact hy2 τ' (le_of_lt hy1)
    · have h3 : γ τ' ∈ closure (γ '' P) := image_closure_subset_closure_image γ.continuous
        (mem_image_of_mem γ hx)
      exact closure_minimal (by
        rintro _ ⟨y, hy, rfl⟩
        exact hy y le_rfl) hi.isClosed_range h3
  have hPo : IsOpen P := by
    refine isOpen_iff_mem_nhds.mpr fun x hx => ?_
    have hO : IsOpen (γ ⁻¹' (i '' (bd T)ᶜ)) := hopen.preimage γ.continuous
    have hxO : x ∈ γ ⁻¹' (i '' (bd T)ᶜ) := by
      obtain ⟨t, h1, h2, -⟩ := key x hx
      exact ⟨t, h2, h1.symm⟩
    obtain ⟨ε, hε, hb⟩ := Metric.isOpen_iff.mp hO x hxO
    refine Filter.mem_of_superset (Metric.ball_mem_nhds x hε) fun y hy τ' h1 => ?_
    rcases le_total τ' x with h2 | h2
    · exact hx τ' h2
    · have h3 : τ' ∈ Metric.ball x ε := by
        have h4 : (x : ℝ) ≤ τ' := h2
        have h5 : (τ' : ℝ) ≤ y := h1
        rw [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq] at hy ⊢
        rw [abs_of_nonneg (by linarith)]
        rw [abs_of_nonneg (by linarith)] at hy
        linarith
      obtain ⟨t, -, ht⟩ := hb h3
      exact ⟨t, ht⟩
  have h0P : (0 : unitInterval) ∈ P := fun τ' h1 => by
    rw [le_antisymm h1 bot_le]
    exact ⟨p, by
      rw [show (0 : unitInterval) = ⊥ from rfl, ← show (0 : unitInterval) = ⊥ from rfl, γ.source]⟩
  have h1P : P = univ := IsClopen.eq_univ ⟨hPc, hPo⟩ ⟨0, h0P⟩
  obtain ⟨t, h1, h2⟩ := key 1 (show (1 : unitInterval) ∈ P from h1P ▸ mem_univ _)
  exact ⟨t, by rw [← h1, γ.target], h2⟩

end GraphMinor.GM07
