/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

import LeanPool.GraphMinor.GM07.Section46Final
public import LeanPool.GraphMinor.GM07.CuffGlue
public import LeanPool.GraphMinor.GM07.Section11c

/-!
# The collars around the cuffs and conditions (i) and (ii) of (4.6)

Graph Minors VII, (5.9), pages 235-237. A collar around one cuff `C` is what the first half of the
proof of (5.9) gives at `C`. Here we put the collars of all the cuffs together and prove the claims
(a) and (b) of the paper, in the form of conditions (i) and (ii) of (4.6) for the collapsed graph
`G'`.
-/

@[expose] public section

namespace GraphMinor.GM07

open Set Topology Function Metric GraphMinor.Surface GraphMinor.GM11

universe u

variable {S : Type u} [TopologicalSpace S] {ι : Type*}

/-- The collar of one cuff `C`. The boxes `φ` run from `C` to level `2`. The set `Mo` is the side of
the circuit `AC` (the circuit `B_β(C)` of the paper) that has `C`, and `AC` carries the arcs `reach`
back to `A(C)`. The sets `Mo₂` and `Mo₃` are the parts of `Mo` outside `N(C)` and outside the boxes.
-/
structure IsCuffCollar (G : Drawing S) (C : Set S) (r v : ℕ) (Mo AC Mo₂ Mo₃ : Set S) (φ : ι → ℝ × ℝ
  → S) (g f : ι → ℝ → ℝ) (Tr : S → Drawing S) : Prop where
  box : IsBoxSystem φ
  data : ∀ i, IsCollapseData (g i) (f i)
  bottom : ∀ i p, p ∈ cuffBox → (φ i p ∈ bd S ↔ p.2 = 0)
  bottomC : ∀ i p, p ∈ cuffBox → p.2 = 0 → φ i p ∈ C
  allBottom : C ⊆ boxBottom φ
  graphU : ∀ i p, p ∈ cuffBox → p.2 = f i p.1 → φ i p ∈ G.U → φ i p ∈ G.V
  graphV : ∀ i p, p ∈ cuffBox → p.2 = f i p.1 → φ i p ∈ G.V → φ i (g i p.1, 0) ∈ G.V ∩ C ∧ φ i p ∈
    (Tr (φ i (g i p.1, 0))).V
  corner : ∀ x ∈ G.V ∩ C, ∃ i e, (e = (0 : ℝ) ∨ e = 1) ∧ φ i (e, 0) = x ∧ φ i (e, 1) ∈ G.V
  cornerV : ∀ i e, (e = (0 : ℝ) ∨ e = 1) → φ i (e, 0) ∈ G.V ∩ C
  gstrict : ∀ i, ∀ m ∈ Icc (0 : ℝ) 1, ∀ m' ∈ Icc (0 : ℝ) 1, g i m = g i m' → 0 < g i m → g i m < 1
    → m = m'
  tree : ∀ x ∈ G.V ∩ C, (Tr x).IsSubdrawing G ∧ IsGraphForest (Tr x).toGraph ∧ x ∈ (Tr x).V ∧
    (∀ a ∈ (Tr x).U, ∃ i p, p ∈ cuffBox ∧ φ i p = a ∧ p.2 ≤ f i p.1 ∧ φ i (g i p.1, 0) = x) ∧ ∀ a ∈
      (Tr x).V, ∀ b ∈ (Tr x).V, Nonempty (GraphWalk (Tr x).toGraph a b)
  closedMo : IsClosed Mo
  openMo : IsOpen (Mo \ AC)
  cMo : C ⊆ Mo
  inMo : ∀ i p, p ∈ cuffBox → φ i p ∈ Mo \ AC
  circ : ∃ A : Drawing S, A.IsSubdrawing G ∧ A.IsCircuit ∧ A.U = AC
  surrounds : SurroundsCuff AC C
  planarMo : IsPlanarInCappedCuff C Mo
  reach : ∀ y ∈ AC, y ∈ G.V → ∃ X, IsScriptASet G r C X ∧ y ∈ X
  inner : ∀ F : Set S, IsOArc F → G.IsNormal F → (G.V ∩ F).ncard ≤ v → SurroundsCuff F C →
    (∀ z ∈ F, ¬ IsBelowGraph φ f z) → False
  mo₂ : Mo₂ ⊆ Mo
  mo₃ : Mo₃ ⊆ Mo
  above₂ : ∀ z ∈ Mo₂, z ∈ G.U → ∀ i p, p ∈ cuffBox → φ i p = z → f i p.1 < p.2
  off₃ : ∀ z ∈ Mo₃, ∀ i, z ∉ φ i '' cuffBox
  touch : ∀ (ρ : S → S) (A B : Set S), Continuous ρ → (∀ x ∈ A, ∀ y, ρ y = ρ x → y = x) →
    (∀ x ∈ G.V ∩ C, ∀ a ∈ (Tr x).U, ρ a = x) → (∀ z ∈ A, ρ z ∈ B → z ∈ G.U → z ∈ G.V) →
      (∀ Z : Set S, Z ⊆ A ∩ G.V → ρ '' Z ⊆ B → Z.ncard < v) → (∀ z ∈ Mo₂, z ∈ G.U → z ∈ A) →
        (∀ z ∈ Mo₃, z ∈ G.U → z ∈ A ∧ ρ z = z) → IsOArc B → (B ∩ (G.V ∩ C)).Nonempty
          → IsNullHomotopicOArc B ∨ (IsNullHomotopicOArcInCappedCuff C B ∧ G.V ∩ C ⊆ B)

theorem lineEnds_subset [T2Space S] {L : Set S} {p q : S} (hl : IsLineWithEnds L p q) : lineEnds L
  ⊆ {p, q} := by
  rintro z ⟨w, hw⟩
  by_contra hz
  simp only [mem_insert_iff, mem_singleton_iff, not_or] at hz
  have hzL : z ∈ L := hw.left_mem
  obtain ⟨L₁, L₂, h₁, h₂, hu, hi⟩ := hl.split hzL (Ne.symm (Ne.symm hz.1)) hz.2
  have hY : IsPreconnected (L \ {z}) := by
    refine hw.isPreconnected_diff.subset_closure (sdiff_subset_sdiff_right (by simp)) fun y hy => ?_
    have h1 : y ∈ closure (L \ {z, w}) := hw.subset_closure_diff hy.1
    exact h1
  have hd : Disjoint (L \ {z}) (L₁ ∩ L₂) := by
    rw [hi, disjoint_right]
    rintro _ rfl h
    exact h.2 rfl
  rcases GM12.subset_side h₁.isCompact.isClosed h₂.isCompact.isClosed hY
    (sdiff_subset.trans hu.ge) hd with h3 | h3
  · have h4 : q ∈ L₁ ∩ L₂ := ⟨h3 ⟨hl.right_mem, Ne.symm hz.2⟩, h₂.right_mem⟩
    rw [hi] at h4
    exact hz.2 h4.symm
  · have h4 : p ∈ L₁ ∩ L₂ := ⟨h₁.left_mem, h3 ⟨hl.left_mem, Ne.symm hz.1⟩⟩
    rw [hi] at h4
    exact hz.1 h4.symm

/-- Along a curve from one of finitely many disjoint closed sets to another, there is a part that
runs from one set to another and misses all of them in between. -/
theorem exists_gap_between_sets {K : Type*} [Finite K] {τ : ℝ → S} (hτ : ContinuousOn τ
  (Icc 0 1)) {Mo : K → Set S} (hcl : ∀ c, IsClosed (Mo c)) (hdis : ∀ c c', c ≠ c' → Disjoint (Mo c)
    (Mo c')) {c₀ c₁ : K} (hne : c₀ ≠ c₁) (h0 : τ 0 ∈ Mo c₀) (h1 : τ 1 ∈ Mo c₁) :
    ∃ t₁ t₂ c₂, 0 ≤ t₁ ∧ t₁ < t₂ ∧ t₂ ≤ 1 ∧ c₂ ≠ c₀ ∧ τ t₁ ∈ Mo c₀ ∧ τ t₂ ∈ Mo c₂
      ∧ ∀ t ∈ Ioo t₁ t₂, ∀ c, τ t ∉ Mo c := by
  classical
  have hmem01 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 ∧ (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨⟨le_rfl, zero_le_one⟩,
    zero_le_one, le_rfl⟩
  have hc₀ : IsCompact {t | t ∈ Icc (0 : ℝ) 1 ∧ τ t ∈ Mo c₀} := isCompact_Icc.of_isClosed_subset
      (hτ.preimage_isClosed_of_isClosed isClosed_Icc (hcl c₀)) (fun _ ht => ht.1)
  obtain ⟨t₁, ht₁, hmax⟩ := hc₀.exists_isMaxOn ⟨0, hmem01.1, h0⟩ continuous_id.continuousOn
  let Y : Set S := ⋃ c, ⋃ _ : c ≠ c₀, Mo c
  have hYc : IsClosed Y := isClosed_iUnion_of_finite fun c => by
    by_cases h : c ≠ c₀
    · simpa [h] using hcl c
    · simp [h]
  have hc₁ : IsCompact {t | t ∈ Icc t₁ 1 ∧ τ t ∈ Y} :=
    isCompact_Icc.of_isClosed_subset
      ((hτ.mono (Icc_subset_Icc_left ht₁.1.1)).preimage_isClosed_of_isClosed isClosed_Icc hYc)
      (fun _ ht => ht.1)
  have h1Y : τ 1 ∈ Y := mem_iUnion₂.mpr ⟨c₁, hne.symm, h1⟩
  obtain ⟨t₂, ht₂, hmin⟩ := hc₁.exists_isMinOn ⟨1, ⟨ht₁.1.2, le_rfl⟩, h1Y⟩
    continuous_id.continuousOn
  obtain ⟨c₂, hc₂, ht₂Y⟩ := mem_iUnion₂.mp ht₂.2
  have hlt : t₁ < t₂ := by
    refine lt_of_le_of_ne ht₂.1.1 fun h => ?_
    rw [← h] at ht₂Y
    exact disjoint_left.mp (hdis _ _ hc₂) ht₂Y ht₁.2
  refine ⟨t₁, t₂, c₂, ht₁.1.1, hlt, ht₂.1.2, hc₂, ht₁.2, ht₂Y, fun t ht c hc => ?_⟩
  have htI : t ∈ Icc (0 : ℝ) 1 := ⟨ht₁.1.1.trans ht.1.le, ht.2.le.trans ht₂.1.2⟩
  by_cases h : c = c₀
  · subst h
    exact absurd (hmax ⟨htI, hc⟩) (not_le.mpr ht.1)
  · have h2 : τ t ∈ Y := mem_iUnion₂.mpr ⟨c, h, hc⟩
    exact absurd (hmin ⟨⟨ht.1.le, htI.2⟩, h2⟩) (not_le.mpr ht.2)

/-- An end of a gap that lies in the open part of a set is impossible. -/
theorem gap_end_off {τ : ℝ → S} {t₁ t₂ t : ℝ} (hlt : t₁ < t₂) (hτ : ContinuousOn τ (Icc t₁ t₂))
  (ht : t ∈ Icc t₁ t₂) {W : Set S} (hW : IsOpen W) (hoff : ∀ s ∈ Ioo t₁ t₂, τ s ∉ W) : τ t ∉ W := by
  intro h
  have h1 : τ t ∈ closure (τ '' Ioo t₁ t₂) := by
    have hc : ContinuousOn τ (closure (Ioo t₁ t₂)) := by rwa [closure_Ioo hlt.ne]
    exact hc.image_closure (mem_image_of_mem τ (by rwa [closure_Ioo hlt.ne]))
  obtain ⟨z, hz, hz'⟩ := mem_closure_iff.mp h1 W hW h
  obtain ⟨s, hs, rfl⟩ := hz'
  exact hoff s hs hz

section Glue

variable [T2Space S] {G G₁ G' : Drawing S} {r v : ℕ} {ι : cuffs S → Type*} {Mo AC Mo₂ Mo₃ : cuffs S
  → Set S} {φ : ∀ c, ι c → ℝ × ℝ → S} {g f : ∀ c, ι c → ℝ → ℝ} {Tr : cuffs S → S → Drawing S}

/-- All the boxes together. -/
abbrev allφ (φ : ∀ c, ι c → ℝ × ℝ → S) : (Σ c, ι c) → ℝ × ℝ → S := fun i => φ i.1 i.2

/-- All the height functions together. -/
abbrev allf (f : ∀ c, ι c → ℝ → ℝ) : (Σ c, ι c) → ℝ → ℝ := fun i => f i.1 i.2

omit [T2Space S] in
theorem exists_cuff_of_bd {x : S} (hx : x ∈ bd S) : ∃ c : cuffs S, x ∈ c.1 := by
  have h : x ∈ ⋃₀ cuffs S := (sUnion_cuffs (S := S)).symm ▸ hx
  obtain ⟨C, hC, hxC⟩ := h
  exact ⟨⟨C, hC⟩, hxC⟩

omit [T2Space S] in
theorem mem_scriptA_of_isScriptASet {C X : Set S} {y : S} (hX : IsScriptASet G r C X)
  (hy : y ∈ X) : y ∈ scriptA G r C :=
  ⟨X, hX, hy⟩

/-- Collars of different cuffs are disjoint. This uses (5.3) for the circuits, and then the fact
that a set that is open and closed is everything. -/
theorem collars_disjoint (hS : IsSurface S) [ConnectedSpace S] (hcyl : ¬ Nonempty
  (S ≃ₜ SurfaceModel 0 0 2)) (h : ∀ c, IsCuffCollar G c.1 r v (Mo c) (AC c) (Mo₂ c) (Mo₃ c) (φ c)
    (g c) (f c) (Tr c)) (hα : r + r < alpha G) {c c' : cuffs S} (hne : c ≠ c') : Disjoint (Mo c)
      (Mo c') := by
  have hne' : c.1 ≠ c'.1 := fun he => hne (Subtype.ext he)
  have hA : ∀ {c c' : cuffs S}, c ≠ c' → Disjoint (AC c) (AC c') := fun {c c'} hne => by
    obtain ⟨A, hA, hAc, hAU⟩ := (h c).circ
    obtain ⟨A', hA', hAc', hAU'⟩ := (h c').circ
    have hV : Disjoint A.V A'.V := by
      rw [disjoint_left]
      intro y hy hy'
      obtain ⟨X, hX, hyX⟩ := (h c).reach y (hAU ▸ A.V_subset_U hy) (hA.1 hy)
      obtain ⟨X', hX', hyX'⟩ := (h c').reach y (hAU' ▸ A'.V_subset_U hy') (hA'.1 hy')
      have h5 := theorem_5_3_proof hS hcyl G c.2 c'.2 (fun he => hne (Subtype.ext he)) hα
      exact (eq_empty_iff_forall_notMem.mp h5 y) ⟨mem_scriptA_of_isScriptASet hX hyX,
        mem_scriptA_of_isScriptASet hX' hyX'⟩
    rw [← hAU, ← hAU']
    exact disjoint_U_of_disjoint_V hA hA' hV
  have hAM : ∀ {c c' : cuffs S}, c ≠ c' → Disjoint (AC c) (Mo c') := fun {c c'} hne => by
    obtain ⟨A, -, hAc, hAU⟩ := (h c).circ
    have hconn : IsPreconnected (AC c) := by
      exact hAU ▸ (isConnected_of_isOArc (IsCircuit.isOArc_U hAc)).isPreconnected
    have hO1 : IsOpen (Mo c' \ AC c') := (h c').openMo
    have hO2 : IsOpen (Mo c')ᶜ := (h c').closedMo.isOpen_compl
    have hdj : Disjoint (Mo c' \ AC c') (Mo c')ᶜ := disjoint_left.mpr fun x hx hx' => hx' hx.1
    have hsub : AC c ⊆ (Mo c' \ AC c') ∪ (Mo c')ᶜ := fun x hx => by
      by_cases hxM : x ∈ Mo c'
      · exact .inl ⟨hxM, disjoint_left.mp (hA hne) hx⟩
      · exact .inr hxM
    rcases hconn.subset_or_subset hO1 hO2 hdj hsub with h1 | h1
    · exfalso
      have h2 : IsPlanarInCappedCuff c'.1 (AC c) := (h c').planarMo.mono (h1.trans sdiff_subset)
      exact hcyl (surroundsCuff_and_planarInCappedCuff_imp_cylinder hS c.2 c'.2 (fun he => hne
        (Subtype.ext he)) (hAU ▸ (IsCircuit.isOArc_U hAc)) (h c).surrounds h2)
    · exact disjoint_left.mpr fun x hx hx' => h1 hx hx'
  rw [disjoint_iff_inter_eq_empty]
  by_contra hne₀
  have hclo : IsClopen (Mo c ∩ Mo c') := by
    refine ⟨(h c).closedMo.inter (h c').closedMo, ?_⟩
    have heq : Mo c ∩ Mo c' = (Mo c \ AC c) ∩ (Mo c' \ AC c') := by
      ext x
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨⟨h1, fun h3 => disjoint_left.mp (hAM hne) h3 h2⟩, h2,
          fun h3 => disjoint_left.mp (hAM hne.symm) h3 h1⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1.1, h2.1⟩
    rw [heq]
    exact (h c).openMo.inter (h c').openMo
  have huniv := hclo.eq_univ (nonempty_iff_ne_empty.mpr hne₀)
  obtain ⟨A, -, hAc, hAU⟩ := (h c).circ
  have hne₁ : (AC c).Nonempty := by
    rw [← hAU]
    exact (isConnected_of_isOArc (IsCircuit.isOArc_U hAc)).nonempty
  obtain ⟨x, hx⟩ := hne₁
  have h2 : x ∈ Mo c ∩ Mo c' := huniv ▸ mem_univ x
  exact disjoint_left.mp (hAM hne) hx h2.2

/-- All the graph lifts together. -/
noncomputable def allTr (G : Drawing S) (Tr : cuffs S → S → Drawing S) : S → Drawing S := by
  classical
  exact fun x => if h : ∃ c : cuffs S, x ∈ c.1 then Tr h.choose x else G

omit [T2Space S] in
theorem allTr_eq {c : cuffs S} {x : S} (hx : x ∈ c.1) (hd : ∀ c c' : cuffs S, c ≠ c'
  → Disjoint c.1 c'.1) : allTr G Tr x = Tr c x := by
  classical
  have h : ∃ c : cuffs S, x ∈ c.1 := ⟨c, hx⟩
  have h2 : h.choose = c := by
    by_contra hne
    exact disjoint_left.mp (hd _ _ hne) h.choose_spec hx
  rw [allTr, dite_eq_left h, h2]

omit [T2Space S] in
/-- The collars together make a frame. -/
theorem collars_frame (h : ∀ c, IsCuffCollar G c.1 r v (Mo c) (AC c) (Mo₂ c) (Mo₃ c) (φ c) (g c)
  (f c) (Tr c)) (hdis : ∀ c c' : cuffs S, c ≠ c' → Disjoint (Mo c) (Mo c')) : IsCollapseFrame G
    (allφ φ) (fun i => g i.1 i.2) (allf f) (allTr G Tr) := by
  classical
  have hdc : ∀ c c' : cuffs S, c ≠ c' → Disjoint c.1 c'.1 := fun c c' hne => (hdis c c' hne).mono
    (h c).cMo (h c').cMo
  refine ⟨⟨fun i => (h i.1).box.cont i.2, fun i => (h i.1).box.inj i.2, ?_, ?_⟩, fun i =>
    (h i.1).data i.2, fun i => (h i.1).bottom i.2, ?_, fun i => (h i.1).graphU i.2, fun i p hp he
      hv => ?_, ?_, ?_⟩
  · rintro ⟨c, a⟩ ⟨c', a'⟩ p p' hp hp' he
    by_cases hcc : c = c'
    · subst hcc
      rcases (h c).box.meet a a' p p' hp hp' he with ⟨rfl, h1⟩ | h1
      · exact .inl ⟨rfl, h1⟩
      · exact .inr h1
    · have he' : φ c a p = φ c' a' p' := he
      have h1 := ((h c).inMo a p hp).1
      rw [he'] at h1
      exact absurd h1 (disjoint_left.mp (hdis c c' hcc).symm ((h c').inMo a' p' hp').1)
  · have heq : (⋃ i : Σ c, ι c, allφ φ i '' {p ∈ cuffBox | p.2 < 2}) = ⋃ c, ⋃ a, φ c a '' {p ∈
      cuffBox | p.2 < 2} := iUnion_sigma _
    rw [heq]
    exact isOpen_iUnion fun c => (h c).box.isOpen
  · intro x hx
    obtain ⟨c, hc⟩ := exists_cuff_of_bd hx
    obtain ⟨a, ha⟩ := mem_iUnion.mp ((h c).allBottom hc)
    exact mem_iUnion.mpr ⟨⟨c, a⟩, ha⟩
  · obtain ⟨h1, h2⟩ := (h i.1).graphV i.2 p hp he hv
    refine ⟨⟨h1.1, cuff_subset_bd i.1.2 h1.2⟩, ?_⟩
    rw [allTr_eq h1.2 hdc]
    exact h2
  · intro x hx
    obtain ⟨c, hc⟩ := exists_cuff_of_bd hx.2
    obtain ⟨a, e, h1, h2, h3⟩ := (h c).corner x ⟨hx.1, hc⟩
    exact ⟨⟨c, a⟩, e, h1, h2, h3⟩
  · intro x hx
    obtain ⟨c, hc⟩ := exists_cuff_of_bd hx.2
    rw [allTr_eq hc hdc]
    obtain ⟨h1, h2, h3, h4, h5⟩ := (h c).tree x ⟨hx.1, hc⟩
    refine ⟨h1, h2, h3, fun a ha => ?_, h5⟩
    obtain ⟨i, p, hp, h6, h7, h8⟩ := h4 a ha
    exact ⟨⟨c, i⟩, p, hp, h6, h7, h8⟩

variable {ρ : S → S} {Ψ : unitInterval × S → S}

omit [T2Space S] in
/-- A point above the graphs, that `ρ` sends to a `G'`-normal set, and that is on `G`, is a vertex
of `G`. -/
theorem IsGlued.normal_up {ι' : Type*} {φ' : ι' → ℝ × ℝ → S} {g' f' : ι' → ℝ → ℝ} {Tr' : S
  → Drawing S} (hg : IsGlued G G₁ G' ρ Ψ φ' g' f' Tr') {B : Set S} (hB : G'.IsNormal B) {z : S}
    (hz : IsAboveGraph φ' f' z) (hzB : ρ z ∈ B) (hzU : z ∈ G.U) : z ∈ G.V := by
  have h1 : ρ z ∈ G'.U := by
    rw [hg.col.imU]
    exact mem_image_of_mem ρ (hg.upU z hz hzU)
  have h2 : ρ z ∈ G'.V := hB ⟨hzB, h1⟩
  rw [hg.col.imV] at h2
  obtain ⟨w, hw, he⟩ := h2
  have h3 : w = z := hg.col.inj z hz w he
  exact hg.downV z hz (h3 ▸ hw)

/-- **Claim (a)** of the proof of (5.9), which is condition (i) of (4.6) for `G'`. -/
theorem claim_a (hS : IsSurface S) [ConnectedSpace S] (hcyl : ¬ Nonempty (S ≃ₜ SurfaceModel 0 0 2))
  (h : ∀ c, IsCuffCollar G c.1 r v (Mo c) (AC c) (Mo₂ c) (Mo₃ c) (φ c) (g c) (f c) (Tr c))
    (hdis : ∀ c c' : cuffs S, c ≠ c' → Disjoint (Mo c) (Mo c')) [Finite (cuffs S)]
      (hg : IsGlued G G₁ G' ρ Ψ (allφ φ) (fun i => g i.1 i.2) (allf f) (allTr G Tr)) (hα : r +
        (r + v) < alpha G) (hα' : r + v + r < alpha G) {B : Set S} (hB : G'.IsNormal B)
          (hI : IsIArc B) (hc : (G'.V ∩ B).ncard ≤ v) : ∃ C ∈ cuffs S, lineEnds B ⊆ C := by
  classical
  obtain ⟨p, q, hp, hq, hl⟩ := hI
  obtain ⟨c₀, hc₀⟩ := exists_cuff_of_bd hp
  obtain ⟨c₁, hc₁⟩ := exists_cuff_of_bd hq
  by_cases hcc : c₀ = c₁
  · subst hcc
    refine ⟨c₀.1, c₀.2, (lineEnds_subset hl).trans ?_⟩
    rintro z (rfl | rfl)
    · exact hc₀
    · exact hc₁
  exfalso
  obtain ⟨τ, hτ⟩ := exists_isParam hl
  have h01 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 ∧ (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨⟨le_rfl, zero_le_one⟩,
    zero_le_one, le_rfl⟩
  obtain ⟨t₁, t₂, c₂, h0, hlt, h1, hc₂, ht₁, ht₂, hgap⟩ :=
    exists_gap_between_sets hτ.cont (fun c => (h c).closedMo) hdis hcc
      (by rw [hτ.zero]; exact (h c₀).cMo hc₀)
      (by rw [hτ.one]; exact (h c₁).cMo hc₁)
  have hsub : Icc t₁ t₂ ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc h0 h1
  have hcont := hτ.cont.mono hsub
  have hoffMo : ∀ t ∈ Icc t₁ t₂, ∀ c, τ t ∉ Mo c \ AC c := fun t ht c => gap_end_off hlt hcont ht
    (h c).openMo fun s hs hs' => hgap s hs c hs'.1
  have hoffBox : ∀ t ∈ Icc t₁ t₂, ∀ i : Σ c, ι c, τ t ∉ allφ φ i '' cuffBox := fun t ht i => by
    rintro ⟨p', hp', he⟩
    exact hoffMo t ht i.1 (he ▸ (h i.1).inMo i.2 p' hp')
  have hab : ∀ t ∈ Icc t₁ t₂, IsAboveGraph (allφ φ) (allf f) (τ t) := fun t ht i p' hp' he
    => absurd (mem_image_of_mem _ hp') (he ▸ hoffBox t ht i)
  have hρ : ∀ t ∈ Icc t₁ t₂, ρ (τ t) = τ t := fun t ht => hg.voff _ (hoffBox t ht)
  have hτB : ∀ t ∈ Icc t₁ t₂, τ t ∈ B := fun t ht => hτ.mem (hsub ht)
  set L₀ : Set S := τ '' Icc t₁ t₂ with hL₀
  have hl₀ : IsLineWithEnds L₀ (τ t₁) (τ t₂) := isLineWithEnds_image (isLine_Icc hlt) hcont
    (hτ.inj.mono hsub)
  have hnorm : ∀ z ∈ L₀, z ∈ G.U → z ∈ G.V := by
    rintro _ ⟨t, ht, rfl⟩ hU
    exact hg.normal_up hB (hab t ht) (by rw [hρ t ht]; exact hτB t ht) hU
  have ht₁m : t₁ ∈ Icc t₁ t₂ := ⟨le_rfl, hlt.le⟩
  have ht₂m : t₂ ∈ Icc t₁ t₂ := ⟨hlt.le, le_rfl⟩
  have hAU : ∀ c, AC c ⊆ G.U := fun c => by
    obtain ⟨A, hA, -, hAU⟩ := (h c).circ
    exact hAU ▸ hA.U_subset
  have hu : τ t₁ ∈ AC c₀ := by
    by_contra hn
    exact hoffMo t₁ ht₁m c₀ ⟨ht₁, hn⟩
  have hu' : τ t₂ ∈ AC c₂ := by
    by_contra hn
    exact hoffMo t₂ ht₂m c₂ ⟨ht₂, hn⟩
  obtain ⟨X₁, hX₁, huX⟩ := (h c₀).reach _ hu (hnorm _ (mem_image_of_mem τ ht₁m) (hAU _ hu))
  obtain ⟨X₂, hX₂, huX'⟩ := (h c₂).reach _ hu' (hnorm _ (mem_image_of_mem τ ht₂m) (hAU _ hu'))
  have hcard₀ : (G.V ∩ L₀).ncard ≤ v := by
    refine le_trans (ncard_le_ncard ?_ (G'.finite_V.subset inter_subset_left)) hc
    rintro _ ⟨hV, t, ht, rfl⟩
    refine ⟨?_, hτB t ht⟩
    rw [hg.col.imV]
    exact ⟨τ t, hg.upV _ (hab t ht) hV, hρ t ht⟩
  obtain ⟨hs₁, hc₁', hn₁, -, hk₁⟩ := id hX₁
  have hX : IsScriptASet G (r + v) c₀.1 (X₁ ∪ L₀) := by
    refine surrounds_of_superset hS hcyl hX₁ subset_union_left (theorem_11_6_proof hS hs₁
      (isSolid_of_isLineWithEnds hS hl₀)) (hc₁'.union ⟨_, huX, hl₀.left_mem⟩ ⟨⟨_, hl₀.left_mem⟩,
        GM12.line_conn hl₀⟩) ?_ ?_ (by omega) hα
    · rintro z ⟨hz | hz, hzU⟩
      · exact hn₁ ⟨hz, hzU⟩
      · exact hnorm z hz hzU
    · rw [inter_union_distrib_left]
      exact (ncard_union_le _ _).trans (add_le_add hk₁ hcard₀)
  have h5 := theorem_5_3_proof hS hcyl G c₀.2 c₂.2 (fun he => hc₂ (Subtype.ext he).symm) hα'
  exact (eq_empty_iff_forall_notMem.mp h5 (τ t₂)) ⟨mem_scriptA_of_isScriptASet hX (.inr
    (mem_image_of_mem τ ht₂m)), mem_scriptA_of_isScriptASet hX₂ huX'⟩

omit [T2Space S] in
/-- A curve that is pushed by a homotopy to a null-homotopic `O`-arc: if `F` is null-homotopic and
`ρ` maps `F` homeomorphically to `B`, then `B` is null-homotopic. -/
theorem nullHomotopic_of_push {F B : Set S} (hc : Continuous Ψ) (h0 : ∀ x, Ψ (0, x) = x)
  (h1 : ∀ x, Ψ (1, x) = ρ x) (e : F ≃ₜ B) (he : ∀ x, (e x : S) = ρ x)
    (hF : IsNullHomotopicOArc F) : IsNullHomotopicOArc B := by
  obtain ⟨ψ, hψ⟩ := hF
  refine ⟨ψ.trans e, closedCurveIsNullHomotopicIn_of_homotopic ?_ hψ⟩
  refine ⟨⟨fun p => Ψ (unitInterval.symm p.2, (ψ p.1).1), by fun_prop⟩, fun _ => mem_univ _,
    fun x => ?_, fun x => ?_⟩
  · change Ψ (unitInterval.symm 0, _) = _
    rw [unitInterval.symm_zero, h1]
    exact (he (ψ x)).symm
  · change Ψ (unitInterval.symm 1, _) = _
    rw [unitInterval.symm_one, h0]
    rfl

/-- **Claim (b)** of the proof of (5.9), which is condition (ii) of (4.6) for `G'`. -/
theorem claim_b (hS : IsSurface S) (h : ∀ c, IsCuffCollar G c.1 r v (Mo c)
  (AC c) (Mo₂ c) (Mo₃ c) (φ c) (g c) (f c) (Tr c)) (hdis : ∀ c c' : cuffs S, c ≠ c' → Disjoint
    (Mo c) (Mo c')) [Finite (cuffs S)] [∀ c, Finite (ι c)] (hF : IsCollapseFrame G (allφ φ) (fun i
      => g i.1 i.2) (allf f) (allTr G Tr)) (hg : IsGlued G G₁ G' ρ Ψ (allφ φ) (fun i => g i.1 i.2)
        (allf f) (allTr G Tr)) (hα : v < alpha G) {B : Set S} (hB : G'.IsNormal B) (hO : IsOArc B)
          (hc : (G'.V ∩ B).ncard ≤ v) : IsNullHomotopicOArc B ∨ ∃ C ∈ cuffs S,
            IsNullHomotopicOArcInCappedCuff C B ∧ G'.V ∩ C ⊆ B := by
  classical
  have : CompactSpace S := hS.1
  have hdc : ∀ c c' : cuffs S, c ≠ c' → Disjoint c.1 c'.1 := fun c c' hne => (hdis c c' hne).mono
    (h c).cMo (h c').cMo
  have hρeq : ρ = fun x => Ψ (1, x) := funext fun x => (hg.col.one x).symm
  have hρc : Continuous ρ := by
    rw [hρeq]
    have := hg.col.contΨ
    fun_prop
  set A : Set S := {x | IsAboveGraph (allφ φ) (allf f) x} with hA
  have hinj : ∀ x ∈ A, ∀ y, ρ y = ρ x → y = x := hg.col.inj
  have hnorm : ∀ z ∈ A, ρ z ∈ B → z ∈ G.U → z ∈ G.V := fun z hz h1 h2 => hg.normal_up hB hz h1 h2
  by_cases hX : (B ∩ (G.V ∩ bd S)).Nonempty
  · obtain ⟨x₀, hx₀B, hx₀⟩ := hX
    obtain ⟨c, hc₀⟩ := exists_cuff_of_bd hx₀.2
    have hx₀V : x₀ ∈ G'.V ∩ B := ⟨(hg.bdV.symm ▸ hx₀ : x₀ ∈ G'.V ∩ bd S).1, hx₀B⟩
    have hcount : ∀ Z : Set S, Z ⊆ A ∩ G.V → ρ '' Z ⊆ B → Z.ncard < v := fun Z hZ hZB => by
      have hi : InjOn ρ Z := fun a ha b hb he => (hinj a (hZ ha).1 b he.symm).symm
      rw [← hi.ncard_image]
      have hsub : ρ '' Z ⊆ (G'.V ∩ B) \ {x₀} := by
        rintro _ ⟨z, hz, rfl⟩
        refine ⟨⟨?_, hZB (mem_image_of_mem ρ hz)⟩, fun he => (hg.above_iff z).mp (hZ hz).1 ?_⟩
        · rw [hg.col.imV]
          exact mem_image_of_mem ρ (hg.upV z (hZ hz).1 (hZ hz).2)
        · have he' : ρ z = x₀ := he
          rw [he']
          exact hx₀.2
      have hfin : ((G'.V ∩ B) \ {x₀}).Finite := (G'.finite_V.subset inter_subset_left).subset
        sdiff_subset
      have h1 := ncard_le_ncard hsub hfin
      rw [ncard_sdiff_singleton_of_mem hx₀V] at h1
      have h2 : 0 < (G'.V ∩ B).ncard := (ncard_pos (G'.finite_V.subset inter_subset_left)).mpr ⟨_,
        hx₀V⟩
      omega
    have hoffOther : ∀ z ∈ Mo c, ∀ (i : Σ c, ι c), ∀ p, p ∈ cuffBox → allφ φ i p = z → i.1 = c
      := fun z hz i p hp he => by
      by_contra hne
      exact disjoint_left.mp (hdis _ _ hne) (he ▸ ((h i.1).inMo i.2 p hp).1) hz
    have hab : ∀ z ∈ Mo₂ c, z ∈ G.U → z ∈ A := fun z hz hU i p hp he => by
      obtain ⟨c', a⟩ := i
      have hcc : c' = c := hoffOther z ((h c).mo₂ hz) ⟨c', a⟩ p hp he
      subst hcc
      exact (h c').above₂ z hz hU a p hp he
    have hoff3 : ∀ z ∈ Mo₃ c, ∀ i : Σ c, ι c, z ∉ allφ φ i '' cuffBox := fun z hz i => by
      rintro ⟨p, hp, he⟩
      obtain ⟨c', a⟩ := i
      have hcc : c' = c := hoffOther z ((h c).mo₃ hz) ⟨c', a⟩ p hp he
      subst hcc
      exact (h c').off₃ z hz a ⟨p, hp, he⟩
    have hid : ∀ z ∈ Mo₃ c, z ∈ G.U → z ∈ A ∧ ρ z = z := fun z hz _ => ⟨fun i p hp he => absurd
      (mem_image_of_mem _ hp) (he ▸ hoff3 z hz i), hg.voff z (hoff3 z hz)⟩
    have htree : ∀ x ∈ G.V ∩ c.1, ∀ a ∈ (Tr c x).U, ρ a = x := fun x hx a ha => by
      have hxb : x ∈ G.V ∩ bd S := ⟨hx.1, cuff_subset_bd c.2 hx.2⟩
      obtain ⟨-, -, -, h4, -⟩ := hg.col.tree x hxb
      exact h4 a (by rw [allTr_eq hx.2 hdc]; exact ha)
    rcases (h c).touch ρ A B hρc hinj htree hnorm hcount hab hid hO ⟨x₀, hx₀B, hx₀.1, hc₀⟩ with h1
      | ⟨h1, h2⟩
    · exact .inl h1
    · refine .inr ⟨c.1, c.2, h1, fun z hz => h2 ⟨?_, hz.2⟩⟩
      have h3 : z ∈ G'.V ∩ bd S := ⟨hz.1, cuff_subset_bd c.2 hz.2⟩
      exact (hg.bdV ▸ h3 : z ∈ G.V ∩ bd S).1
  -- Now `B` misses the vertices on the boundary, and we lift it to an `O`-arc off the part below
  -- the graphs.
  have hXoff : ∀ z ∈ B, z ∈ G.V → z ∉ bd S := fun z hz hV hb => hX ⟨z, hz, hV, hb⟩
  have hdata := hF.data
  have hBo := isOpen_below hF.box hdata
  set Y : Set S := {z | ρ z ∈ B ∧ ¬ IsBelowGraph (allφ φ) (allf f) z} with hY
  have hYcl : IsClosed Y := (hO.isCompact.isClosed.preimage hρc).inter hBo.isClosed_compl
  have hcorner : ∀ (i : Σ c, ι c) (e : ℝ), (e = 0 ∨ e = 1) → allφ φ i (e, 0) ∉ B := fun i e he hb
    => by
    have h1 := (h i.1).cornerV i.2 e he
    exact hXoff _ hb h1.1 (cuff_subset_bd i.1.2 h1.2)
  have hgraph : ∀ z ∈ Y, z ∉ A → ∃ (i : Σ c, ι c) (p : ℝ × ℝ), p ∈ cuffBox ∧ allφ φ i p = z ∧ p.2
    = allf f i p.1 := fun z hz hzA => by
    simp only [hA, mem_ofPred_eq, IsAboveGraph] at hzA
    push Not at hzA
    obtain ⟨i, p, hp, he, hle⟩ := hzA
    refine ⟨i, p, hp, he, le_antisymm hle (not_lt.mp fun hlt => hz.2 ⟨i, p, hp, he, hlt⟩)⟩
  have hgmid : ∀ (i : Σ c, ι c) (p : ℝ × ℝ), p ∈ cuffBox → p.2 = allf f i p.1 → ρ (allφ φ i p) ∈ B
    → ρ (allφ φ i p) = allφ φ i (g i.1 i.2 p.1, 0) ∧ 0 < g i.1 i.2 p.1 ∧ g i.1 i.2 p.1 < 1
      := fun i p hp hgr hb => by
    have h1 : ρ (allφ φ i p) = allφ φ i (g i.1 i.2 p.1, 0) := by
      rw [hg.val i p hp, boxCollapse_under (hdata i) hp hgr.le]
    rw [h1] at hb
    have hm := (hdata i).gmem hp.1
    refine ⟨h1, lt_of_le_of_ne hm.1 fun he => ?_, lt_of_le_of_ne hm.2 fun he => ?_⟩
    · exact hcorner i 0 (.inl rfl) (by rw [← he] at hb; exact hb)
    · exact hcorner i 1 (.inr rfl) (by rw [he] at hb; exact hb)
  have hinjY : InjOn ρ Y := fun z hz z' hz' he => by
    by_cases hza : z ∈ A
    · exact (hinj z hza z' he.symm).symm
    by_cases hza' : z' ∈ A
    · exact hinj z' hza' z he
    obtain ⟨i, p, hp, rfl, hgr⟩ := hgraph z hz hza
    obtain ⟨i', p', hp', rfl, hgr'⟩ := hgraph z' hz' hza'
    obtain ⟨h1, h2, h3⟩ := hgmid i p hp hgr hz.1
    obtain ⟨h1', h2', h3'⟩ := hgmid i' p' hp' hgr' hz'.1
    rw [h1, h1'] at he
    have hbx : (g i.1 i.2 p.1, (0 : ℝ)) ∈ cuffBox := ⟨⟨h2.le, h3.le⟩, le_rfl, by norm_num⟩
    have hbx' : (g i'.1 i'.2 p'.1, (0 : ℝ)) ∈ cuffBox := ⟨⟨h2'.le, h3'.le⟩, le_rfl, by norm_num⟩
    rcases hF.box.meet i i' _ _ hbx hbx' he with ⟨rfl, h4⟩ | ⟨-, h4, -⟩
    · have h5 : g i.1 i.2 p.1 = g i.1 i.2 p'.1 := congrArg Prod.fst h4
      have h6 := (h i.1).gstrict i.2 p.1 hp.1 p'.1 hp'.1 h5 h2 h3
      have h7 : p.2 = p'.2 := by
        rw [hgr, hgr', h6]
      rw [show p = p' from Prod.ext h6 h7]
    · rcases h4 with h4 | h4
      · exact absurd h4 h2.ne'
      · exact absurd h4 h3.ne
  have hsurj : ∀ y ∈ B, ∃ z ∈ Y, ρ z = y := fun y hy => by
    by_cases hyb : y ∈ boxBottom (allφ φ)
    · obtain ⟨i, m₀, hm₀, rfl⟩ := mem_iUnion.mp hyb
      have hne0 : m₀ ≠ 0 := fun he => hcorner i 0 (.inl rfl) (by rw [he] at hy; exact hy)
      have hne1 : m₀ ≠ 1 := fun he => hcorner i 1 (.inr rfl) (by rw [he] at hy; exact hy)
      have hsubI : Icc (g i.1 i.2 0) (g i.1 i.2 1) ⊆ g i.1 i.2 '' Icc 0 1
        := intermediate_value_Icc zero_le_one (hdata i).gcont
      rw [(hdata i).g0, (hdata i).g1] at hsubI
      obtain ⟨m, hm, hgm⟩ := hsubI hm₀
      have hfm := (hdata i).f1 m hm
      have hp : (m, allf f i m) ∈ cuffBox := ⟨hm, by linarith [hfm.1], by linarith [hfm.2]⟩
      have hm0 : m ≠ 0 := fun he => hne0 (by rw [← hgm, he]; exact (hdata i).g0)
      have hm1 : m ≠ 1 := fun he => hne1 (by rw [← hgm, he]; exact (hdata i).g1)
      have hval : ρ (allφ φ i (m, allf f i m)) = allφ φ i (m₀, 0) := by
        rw [hg.val i _ hp, boxCollapse_under (hdata i) hp le_rfl]
        change allφ φ i (g i.1 i.2 m, 0) = _
        rw [hgm]
      refine ⟨_, ⟨?_, ?_⟩, hval⟩
      · rwa [hval]
      · rintro ⟨i', p', hp', he, hlt⟩
        rcases hF.box.meet i' i p' _ hp' hp he with ⟨rfl, h1⟩ | ⟨-, -, h1, -⟩
        · rw [h1] at hlt
          exact lt_irrefl _ hlt
        · rcases h1 with h1 | h1
          · exact hm0 h1
          · exact hm1 h1
    · obtain ⟨x, hx, he⟩ := hF.box.surj_above hdata hg.val hg.voff hyb
      exact ⟨x, ⟨he ▸ hy, not_below_of_above hx⟩, he⟩
  have hYimg : ρ '' Y = B := by
    refine subset_antisymm ?_ fun y hy => ?_
    · rintro _ ⟨z, hz, rfl⟩
      exact hz.1
    · obtain ⟨z, hz, he⟩ := hsurj y hy
      exact ⟨z, hz, he⟩
  have hYc : CompactSpace Y := isCompact_iff_compactSpace.mp hYcl.isCompact
  let e₀ : Y → B := fun z => ⟨ρ z.1, z.2.1⟩
  have he₀ : Bijective e₀ := by
    refine ⟨fun z z' he => Subtype.ext (hinjY z.2 z'.2 (congrArg Subtype.val he)), fun y => ?_⟩
    obtain ⟨z, hz, he⟩ := hsurj y.1 y.2
    exact ⟨⟨z, hz⟩, Subtype.ext he⟩
  have he₀c : Continuous e₀ := by
    fun_prop
  let e : Y ≃ₜ B := he₀c.homeoOfEquivCompactToT2 (f := Equiv.ofBijective e₀ he₀)
  have hYO : IsOArc Y := by
    obtain ⟨ψ⟩ := hO
    exact ⟨ψ.trans e.symm⟩
  have hYU : ∀ z ∈ Y, z ∈ G.U → z ∈ G.V := fun z hz hU => by
    by_cases hza : z ∈ A
    · exact hnorm z hza hz.1 hU
    · obtain ⟨i, p, hp, rfl, hgr⟩ := hgraph z hz hza
      exact hF.graphU i p hp hgr hU
  have hYA : ∀ z ∈ Y, z ∈ G.V → z ∈ A := fun z hz hV => by
    by_contra hza
    obtain ⟨i, p, hp, rfl, hgr⟩ := hgraph z hz hza
    obtain ⟨h1, h2, h3⟩ := hgmid i p hp hgr hz.1
    obtain ⟨h4, -⟩ := hF.graphV i p hp hgr hV
    have h5 := hz.1
    rw [h1] at h5
    exact hXoff _ h5 h4.1 h4.2
  have hcard : (G.V ∩ Y).ncard ≤ v := by
    have hi : InjOn ρ (G.V ∩ Y) := hinjY.mono inter_subset_right
    rw [← hi.ncard_image]
    refine le_trans (ncard_le_ncard ?_ (G'.finite_V.subset inter_subset_left)) hc
    rintro _ ⟨z, ⟨hV, hz⟩, rfl⟩
    refine ⟨?_, hz.1⟩
    rw [hg.col.imV]
    exact mem_image_of_mem ρ (hg.upV z (hYA z hz hV) hV)
  have hnear : IsNearPlanar Y := by
    by_contra hn
    have h1 := alpha_le_of_candidate (G := G) (X := Y) ⟨isSolid_of_isOArc hS hYO,
      isConnected_of_isOArc hYO, fun z hz => hYU z hz.1 hz.2, hn⟩
    rw [inter_comm] at h1
    omega
  have hpush : IsPlanar Y → IsNullHomotopicOArc B := fun hp => by
    have h1 := (isPlanar_iff_isNullHomotopicOArc_of_isOArc hS hYO).mp hp
    exact nullHomotopic_of_push hg.col.contΨ hg.col.zero hg.col.one e (fun x => rfl) h1
  by_cases hp : IsPlanar Y
  · exact .inl (hpush hp)
  rcases hnear with hn | ⟨C, hC, hn⟩
  · exact absurd hn hp
  exact ((h ⟨C, hC⟩).inner Y hYO (fun z hz => hYU z hz.1 hz.2) hcard ⟨hC, hn,
    hp⟩ fun z hz hz' => hz.2 (by
    obtain ⟨i, p, hp', he, hlt⟩ := hz'
    exact ⟨⟨⟨C, hC⟩, i⟩, p, hp', he, hlt⟩)).elim

/-- The end of the proof of (5.9): the collars let us apply (4.6) to `G'`, and a forest of `G'`
lifts to `G`. -/
theorem isGFeasible_of_collars [T1Space S] (hS : IsSurface S) [ConnectedSpace S] (hcuffs : 2 ≤
  (cuffs S).ncard) (hcyl : ¬ Nonempty (S ≃ₜ SurfaceModel 0 0 2)) {k : ℕ} {H : Drawing S}
    (hG : G.IsProper) (hbd_card : (G.V ∩ bd S).ncard ≤ 2 * k) (h : ∀ c, IsCuffCollar G c.1 r
      (vSurface S k) (Mo c) (AC c) (Mo₂ c) (Mo₃ c) (φ c) (g c) (f c) (Tr c)) [∀ c, Finite (ι c)]
        (hα₀ : r + r < alpha G) (hα : r + (r + vSurface S k) < alpha G)
          (hα' : r + vSurface S k + r < alpha G) (hα₁ : vSurface S k < alpha G)
            (hiii : ∀ C ∈ cuffs S, 2 ≤ (G.V ∩ C).ncard) (hH : IsSurfaceForest H)
              (hbd_eq : G.V ∩ bd S = H.V ∩ bd S) : IsGFeasible G H := by
  have : CompactSpace S := hS.1
  have : Finite (cuffs S) := (finite_of_ncard_pos (by omega) : (cuffs S).Finite).to_subtype
  have : Nonempty S := ConnectedSpace.toNonempty
  have hdis : ∀ c c' : cuffs S, c ≠ c' → Disjoint (Mo c) (Mo c') := fun c c' hne
    => collars_disjoint hS hcyl h hα₀ hne
  have hF := collars_frame h hdis
  have hbd : IsClosed (bd S) := (cuff_statement.{u} S hS).1
  obtain ⟨G₁, G', ρ, Ψ, hg⟩ := hF.exists_collapse hbd
  have hbdV := hg.bdV
  have hproper : G'.IsProper := by
    rintro z ⟨hzb, hzU⟩
    rw [hg.col.imU] at hzU
    obtain ⟨a, ha, rfl⟩ := hzU
    rw [hg.col.imV]
    refine ⟨a, ?_, rfl⟩
    by_contra hn
    exact (hg.above_iff a).mp (hg.col.off ⟨ha, hn⟩) hzb
  have hfe : IsGFeasible G' H := by
    refine theorem_4_6_proof hS hcuffs k G' H hproper (by rw [hbdV]; exact hbd_card)
      (fun B h1 h2 h3 => claim_a hS hcyl h hdis hg hα hα' h1 h2 h3)
      (fun B h1 h2 h3 => claim_b hS h hdis hF hg hα₁ h1 h2 h3) (fun C hC => ?_) hH
      (by rw [hbdV]; exact hbd_eq)
    have hsub : G.V ∩ C ⊆ G'.V ∩ C := fun z hz => by
      have h1 : z ∈ G'.V ∩ bd S := hbdV ▸ (⟨hz.1, cuff_subset_bd hC hz.2⟩ : z ∈ G.V ∩ bd S)
      exact ⟨h1.1, hz.2⟩
    exact (hiii C hC).trans (ncard_le_ncard hsub (G'.finite_V.subset inter_subset_left))
  exact hg.col.isGFeasible hS hG hH hbd_eq.symm hfe

end Glue

end GraphMinor.GM07
