/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM17.CutPaint
public import Mathlib.Analysis.Complex.Cardinality
public import Mathlib.SetTheory.Cardinal.Continuum
public import Mathlib.Analysis.Real.Cardinality

/-!
# One side of a cut is a cut-side painting

We show that the painting of `CutSetup.exists_painting` together with an injection of the surface
into the cut surface is a cut-side
painting (`CutSetup.cutSide`). The injection is the inverse of `ψ` off the arc `F`. The rest of the
surface, which may be large, goes
injectively into the inside of a lift of `F`, which has as many points as the surface
(`exists_inj_line`).
-/

@[expose] public section

namespace GraphMinor.GM17

open Set Topology GraphMinor.Surface Cardinal

variable {Y S : Type} [TopologicalSpace Y] [TopologicalSpace S]

/-- A surface has at most continuum many points. -/
theorem mk_le_continuum (hS : IsSurface S) : #S ≤ 𝔠 := by
  have hc : CompactSpace S := hS.1
  choose U O j k hU hO hx hj hk hm hm' hl hl' using fun x : S => (hS.2.2 x).exists_chart
  obtain ⟨t, ht⟩ := CompactSpace.elim_nhds_subcover U fun x => (hU x).mem_nhds (hx x)
  have hex : ∀ z : S, ∃ x ∈ t, z ∈ U x := fun z => by
    have hz : z ∈ ⋃ x ∈ t, U x := ht ▸ mem_univ z
    obtain ⟨x, hxt, hz⟩ := mem_iUnion₂.mp hz
    exact ⟨x, hxt, hz⟩
  choose i hi hi' using hex
  let f : S → t × ℂ := fun z => (⟨i z, hi z⟩, j (i z) z)
  have hf : Function.Injective f := by
    intro z z' he
    have h1 : i z = i z' := congrArg (fun p => (p.1 : S)) (congrArg Prod.fst he)
    have h2 : j (i z) z = j (i z') z' := congrArg Prod.snd he
    rw [← h1] at h2
    have h3 := hl (i z) (hi' z)
    have h4 := hl (i z) (h1 ▸ hi' z' : z' ∈ U (i z))
    rw [← h3, ← h4, h2]
  calc #S ≤ #(t × ℂ) := mk_le_of_injective hf
    _ = #t * 𝔠 := by rw [mk_prod, mk_complex]; simp
    _ ≤ ℵ₀ * 𝔠 := mul_le_mul_left (mk_le_aleph0) _
    _ = 𝔠 := aleph0_mul_continuum

/-- A surface goes injectively into the inside of any line. -/
theorem exists_inj_line (hS : IsSurface S) {K : Set Y} {u v : Y}
  (hK : IsLineWithEnds K u v) :
    ∃ j : S → Y, Function.Injective j ∧ ∀ x, j x ∈ K ∧ j x ≠ u ∧ j x ≠ v := by
  obtain ⟨a, ha, rfl, rfl, rfl⟩ := hK.exists_arc
  have h1 : #S ≤ #(Ioo (0 : ℝ) 1) := by
    rw [mk_Ioo_real zero_lt_one]
    exact mk_le_continuum hS
  obtain ⟨e⟩ := Cardinal.le_def _ _ |>.mp h1
  have hmem : ∀ x, (e x : ℝ) ∈ Icc (0 : ℝ) 1 := fun x => ⟨(e x).2.1.le, (e x).2.2.le⟩
  refine ⟨fun x => a ⟨e x, hmem x⟩, fun x x' h => ?_, fun x => ⟨mem_range_self _, fun h => ?_,
    fun h => ?_⟩⟩
  · exact e.injective (Subtype.ext (congrArg (fun t : unitInterval => (t : ℝ)) (ha.2 h)))
  · exact (e x).2.1.ne (congrArg Subtype.val (ha.2 h)).symm
  · exact (e x).2.2.ne (congrArg Subtype.val (ha.2 h))

theorem isPreconnected_line {L : Set S} {u v : S} (hL : IsLineWithEnds L u v) : IsPreconnected L
  := by
  obtain ⟨a, ha, rfl, -, -⟩ := hL.exists_arc
  exact isPreconnected_range ha.1

/-- A cuff contains every connected part of the boundary that meets it. -/
theorem subset_cuff {Φ P : Set Y} (hΦ : Φ ∈ cuffs Y) (hP : IsPreconnected P)
  (hb : P ⊆ bd Y) {x : Y} (hx : x ∈ Φ) (hxP : x ∈ P) : P ⊆ Φ := by
  obtain ⟨p, -, rfl⟩ := hΦ
  rw [connectedComponentIn_eq hx]
  exact hP.subset_connectedComponentIn hxP hb

/-- Each node on the boundary is an end of a border cell. -/
theorem exists_cell_node [T2Space S] (hS : IsSurface S) {Γ : Painting S} {n : S} (hn : n ∈ Γ.N)
  (hb : n ∈ bd S) : ∃ c ∈ Γ.C, n ∈ tilde c := by
  have hΘ : connectedComponentIn (bd S) n ∈ cuffs S := ⟨n, hb, rfl⟩
  have hO := (cuff_statement.{0} S hS).2.2 _ hΘ
  have hnΘ : n ∈ connectedComponentIn (bd S) n := mem_connectedComponentIn hb
  obtain ⟨φ⟩ := id hO
  have h1 : ∃ m ∈ connectedComponentIn (bd S) n, m ≠ n := by
    by_contra hcon
    push Not at hcon
    have h2 := hcon _ (φ 1).2
    have h3 := hcon _ (φ (Circle.exp Real.pi)).2
    have h4 : φ 1 = φ (Circle.exp Real.pi) := Subtype.ext (h2.trans h3.symm)
    have h5 := congrArg (fun z : Circle => (z : ℂ)) (φ.injective h4)
    norm_num at h5
  obtain ⟨m, hm, hne⟩ := h1
  obtain ⟨A, B, hA, -, hu, -⟩ := hO.lines hnΘ hm hne.symm
  have hAb : A ⊆ bd S := fun z hz => connectedComponentIn_subset _ _ (hu.subset (Or.inl hz))
  obtain ⟨c, hc, -, -, h2, -⟩ := exists_border_cell hA hAb (subset_univ _) hn fun _ _ => .inl
    (subset_univ _)
  exact ⟨c, hc, h2⟩

private theorem cut_cuff_node_order
    {Y : Type}
    {S : Type}
    [TopologicalSpace Y]
    [TopologicalSpace S]
    {Γ : Painting S}
    {ψ : Y → S}
    {F : Set S}
    {n₁ : S}
    {n₂ : S}
    {Ks : Set (Set Y)}
    {e₁ : Set Y → Y}
    {e₂ : Set Y → Y}
    (h : CutSetup Γ ψ F n₁ n₂ Ks e₁ e₂)
    [T2Space S]
    [T2Space Y]
    (Γ' : Painting Y)
    (hN : Γ'.N = ψ ⁻¹' keepNodes Γ F n₁ n₂)
    (σ : S → Y)
    (hσ₁ : ∀ x ∈ range ψ \ F, ψ (σ x) = x)
    (ι : S → Y)
    (A : Set S)
    (hA : A = {n | n ∈ Γ.N \ F ∧ ∃ c ∈ keepCells Γ ψ F, n ∈ tilde c})
    (hιR : ∀ x ∈ range ψ \ F, ι x = σ x)
    (hAR : ∀ n ∈ A, n ∈ range ψ \ F)
    (hOS : ∀ C ∈ cuffs S, IsOArc C)
    (hOY : ∀ C ∈ cuffs Y, IsOArc C)
    (hactive : ∀ n ∈ Γ.N, n ∉ F → n ∈ range ψ \ F → n ∈ bd S → n ∈ A)
    (hlift : ∀ {L : Set S} {u v : S}, IsLineWithEnds L u v → L ⊆ bd S →
      Disjoint L F → u ∈ range ψ \ F →
      L ⊆ range ψ \ F ∧ IsLineWithEnds (σ '' L) (σ u) (σ v) ∧ σ '' L ⊆ bd Y)
    (hcuffb : ∀ {Θ : Set S}, Θ ∈ cuffs S → Θ ⊆ bd S)
    (hfull : ∀ Θ ∈ cuffs S, ∀ a ∈ Θ, a ∈ range ψ \ F → Disjoint Θ F →
      ∀ Φ ∈ cuffs Y, σ a ∈ Φ → ∀ y ∈ Γ'.N, y ∈ Φ → ∃ m ∈ A ∩ Θ, y = ι m)
    (hFnode : ∀ (Θ : Set S), ∀ p ∈ Θ, Θ ∈ cuffs S → p ∈ F → p ∈ F ∩ (Γ.N ∩ Θ)) :
    ∀ Φ ∈ cuffs Y, ∀ x₁ ∈ Γ'.N ∩ Φ, ∀ x₂ ∈ Γ'.N ∩ Φ, ∀ x₃ ∈ Γ'.N ∩ Φ, ∀ x₄ ∈ Γ'.N ∩ Φ,
      GM19.InOrderOn Φ x₁ x₂ x₃ x₄ → ∀ n₁ ∈ A, x₁ = ι n₁ → ∀ n₃ ∈ A, x₃ = ι n₃ → ∀
      Θ ∈ cuffs S, n₁ ∈ Θ → n₃ ∈ Θ → (∃ a ∈ F ∩ (Γ.N ∩ Θ), ∃ b ∈ F ∩ (Γ.N ∩ Θ), GM19.InOrderOn Θ
      n₁ a n₃ b) ∨ (∃ n₂ ∈ A ∩ Θ, x₂ = ι n₂ ∧
      ∃ b ∈ F ∩ (Γ.N ∩ Θ) ∪ {m | m ∈ A ∩ Θ ∧
      x₄ = ι m}, GM19.InOrderOn Θ n₁ n₂ n₃ b) ∨ ∃ n₄ ∈ {n | n ∈ Γ.N \ F ∧ ∃ c ∈ keepCells Γ ψ F, n
      ∈ tilde c} ∩ Θ, x₄ = ι n₄ ∧ ∃ a ∈ F ∩ (Γ.N ∩ Θ) ∪ {m | m ∈ {n | n ∈ Γ.N \ F ∧ ∃ c ∈
      keepCells Γ ψ F, n ∈ tilde c} ∩ Θ ∧ x₂ = ι m}, GM19.InOrderOn Θ n₁ a n₃ n₄ := by
  subst A
  let A : Set S := {n | n ∈ Γ.N \ F ∧ ∃ c ∈ keepCells Γ ψ F, n ∈ tilde c}
  intro Φ hΦ x₁ hx₁ x₂ hx₂ x₃ hx₃ x₄ hx₄ hord a ha hxa e he hxe Θ hΘ haΘ heΘ
  have haR := hAR a ha
  have heR := hAR e he
  have hO := hOS Θ hΘ
  rw [hιR a haR] at hxa
  rw [hιR e heR] at hxe
  subst hxa hxe
  have hb₀ : ∀ y ∈ Γ'.N ∩ Φ, ∃ b, b ∈ (F ∩ (Γ.N ∩ Θ)) ∪ {m ∈ A ∩ Θ | y = ι m} := fun y hy => by
    by_cases hd : Disjoint Θ F
    · obtain ⟨m, hm, hm'⟩ := hfull Θ hΘ a haΘ haR hd Φ hΦ hx₁.2 y hy.1 hy.2
      exact ⟨m, .inr ⟨hm, hm'⟩⟩
    · obtain ⟨p, hp, hpF⟩ := not_disjoint_iff.mp hd
      exact ⟨p, .inl (hFnode Θ p hp hΘ hpF)⟩
  by_cases hae : a = e
  · subst hae
    right
    rcases eq_of_inOrder hord with hx | hx
    · left
      obtain ⟨b, hb⟩ := hb₀ x₄ hx₄
      have hbΘ : b ∈ Θ := by
        rcases hb with hb | hb
        · exact hb.2.2
        · exact hb.1.2
      exact ⟨a, ⟨ha, haΘ⟩, by rw [hx, hιR a haR], b, hb, inOrder_three hO haΘ hbΘ⟩
    · right
      obtain ⟨b, hb⟩ := hb₀ x₂ hx₂
      have hbΘ : b ∈ Θ := by
        rcases hb with hb | hb
        · exact hb.2.2
        · exact hb.1.2
      exact ⟨a, ⟨ha, haΘ⟩, by rw [hx, hιR a haR], b, hb, inOrderOn_cyclic2
        (inOrder_three hO haΘ hbΘ)⟩
  have hon : ∀ {L : Set S} {u v : S}, IsLineWithEnds L u v → L ⊆ Θ → Disjoint L F → u ∈ range ψ \ F
    → ∀ y ∈ Γ'.N, y ∈ σ '' L → ∃ n ∈ A ∩ Θ, y = ι n ∧ n ∈ L := by
    intro L u v hL hs hd hu y hyN hy
    obtain ⟨hLR, -, -⟩ := hlift hL (hs.trans (hcuffb hΘ)) hd hu
    obtain ⟨n, hn, rfl⟩ := hy
    have hmk : ψ (σ n) ∈ keepNodes Γ F n₁ n₂ := by
      have h1 := hyN
      rw [hN] at h1
      exact h1
    rw [hσ₁ n (hLR hn)] at hmk
    exact ⟨n, ⟨hactive n (h.keepNodes_subset hmk) (disjoint_left.mp hd hn) (hLR hn) (hcuffb hΘ
      (hs hn)), hs hn⟩, (hιR n (hLR hn)).symm, hn⟩
  obtain ⟨L₁, L₂, hL₁, hL₂, hu₁₂, -⟩ := hO.lines haΘ heΘ hae
  by_cases hex : ∃ L L' : Set S, IsLineWithEnds L a e ∧ IsLineWithEnds L' a e ∧ L ∪ L' = Θ
    ∧ Disjoint L F
  swap
  · left
    have d₁ : ¬ Disjoint L₁ F := fun d => hex ⟨L₁, L₂, hL₁, hL₂, hu₁₂, d⟩
    have d₂ : ¬ Disjoint L₂ F := fun d =>
      hex ⟨L₂, L₁, hL₂, hL₁, (union_comm _ _).trans hu₁₂, d⟩
    obtain ⟨p, hp, hpF⟩ := not_disjoint_iff.mp d₁
    obtain ⟨q, hq, hqF⟩ := not_disjoint_iff.mp d₂
    have hpΘ : p ∈ Θ := hu₁₂ ▸ .inl hp
    have hqΘ : q ∈ Θ := hu₁₂ ▸ .inr hq
    exact ⟨p, hFnode Θ p hpΘ hΘ hpF, q, hFnode Θ q hqΘ hΘ hqF, inOrder_of_lines hO hL₁ hL₂ hu₁₂
      hp hq⟩
  obtain ⟨L, L', hL, hL', hu, hd⟩ := hex
  right
  have hLΘ : L ⊆ Θ := fun z hz => hu ▸ .inl hz
  obtain ⟨hLR, hLl, hLb⟩ := hlift hL (hLΘ.trans (hcuffb hΘ)) hd haR
  have hsub : σ '' L ⊆ Φ := subset_cuff hΦ (isPreconnected_line hLl) hLb hx₁.2 hLl.left_mem
  obtain ⟨Lc, hLc, huc, hic⟩ := oarc_split (hOY Φ hΦ) hLl hsub
  have htail : ∀ y ∈ Γ'.N ∩ Φ, y ∈ Lc → ∃ b, b ∈ (F ∩ (Γ.N ∩ Θ)) ∪ {m ∈ A ∩ Θ | y = ι m} ∧ b ∈ L'
    := by
    intro y hy hyc
    by_cases hd' : Disjoint L' F
    · have hdΘ : Disjoint Θ F := by
        rw [← hu]
        exact disjoint_union_left.mpr ⟨hd, hd'⟩
      obtain ⟨m, hm, hm'⟩ := hfull Θ hΘ a haΘ haR hdΘ Φ hΦ hx₁.2 y hy.1 hy.2
      refine ⟨m, .inr ⟨hm, hm'⟩, ?_⟩
      rcases (hu ▸ hm.2 : m ∈ L ∪ L') with hmL | hmL
      · have hym : y ∈ σ '' L := by
          rw [hm', hιR m (hLR hmL)]
          exact mem_image_of_mem _ hmL
        have h1 : y ∈ σ '' L ∩ Lc := ⟨hym, hyc⟩
        rw [hic] at h1
        have h2 : m = a ∨ m = e := by
          rw [hm', hιR m (hLR hmL)] at h1
          rcases h1 with h1 | h1
          · left
            rw [← hσ₁ m (hLR hmL), h1, hσ₁ a haR]
          · right
            rw [← hσ₁ m (hLR hmL), h1, hσ₁ e heR]
        rcases h2 with rfl | rfl
        · exact hL'.left_mem
        · exact hL'.right_mem
      · exact hmL
    · obtain ⟨p, hp, hpF⟩ := not_disjoint_iff.mp hd'
      exact ⟨p, .inl (hFnode Θ p (hu ▸ .inr hp) hΘ hpF), hp⟩
  rcases mem_of_inOrder hord hLl hLc huc with ⟨h₂, h₄⟩ | ⟨h₂, h₄⟩
  · left
    obtain ⟨n₂', hn₂', hx₂e, hn₂L⟩ := hon hL hLΘ hd haR x₂ hx₂.1 h₂
    obtain ⟨b, hb, hbL⟩ := htail x₄ hx₄ h₄
    exact ⟨n₂', hn₂', hx₂e, b, hb, inOrder_of_lines hO hL hL' hu hn₂L hbL⟩
  · right
    obtain ⟨n₄', hn₄', hx₄e, hn₄L⟩ := hon hL hLΘ hd haR x₄ hx₄.1 h₄
    obtain ⟨b, hb, hbL⟩ := htail x₂ hx₂ h₂
    exact ⟨n₄', hn₄', hx₄e, b, hb,
      inOrder_of_lines hO hL' hL ((union_comm _ _).trans hu) hbL hn₄L⟩

private theorem preconnected_set_respects_cut_range
    {Y : Type}
    {S : Type}
    [TopologicalSpace Y]
    [TopologicalSpace S]
    {Γ : Painting S}
    {ψ : Y → S}
    {F : Set S}
    {n₁ : S}
    {n₂ : S}
    {Ks : Set (Set Y)}
    {e₁ : Set Y → Y}
    {e₂ : Set Y → Y}
    (h : CutSetup Γ ψ F n₁ n₂ Ks e₁ e₂)
    (hrc : IsClosed (range ψ))
    {L : Set S}
    (hL : IsPreconnected L)
    (hd : Disjoint L F)
    (hne : (L ∩ (range ψ \ F)).Nonempty) :
    L ⊆ (range ψ \ F) := by
  let R := range ψ \ F
  have hsub : L ⊆ R ∪ (range ψ)ᶜ := fun x hx => by
    by_cases hr : x ∈ range ψ
    · exact .inl ⟨hr, disjoint_left.mp hd hx⟩
    · exact .inr hr
  rcases hL.subset_or_subset h.map.isOpen hrc.isOpen_compl (disjoint_left.mpr fun x hx hx'
    => hx' hx.1) hsub with h1 | h1
  · exact h1
  · obtain ⟨z, hz, hz'⟩ := hne
    exact absurd hz'.1 (h1 hz)

/-- One part of the cut surface carries a cut-side painting for the cells in it. -/
theorem CutSetup.cutSide {Γ : Painting S} {ψ : Y → S} {F : Set S} {n₁ n₂ : S} {Ks : Set
  (Set Y)} {e₁ e₂ : Set Y → Y} (h : CutSetup Γ ψ F n₁ n₂ Ks e₁ e₂)
    [Nonempty Y] {K₀ : Set Y} (hK₀ : K₀ ∈ Ks) : ∃ (ι : S → Y) (Γ' : Painting Y), IsCutSidePainting
      S Γ F (keepCells Γ ψ F) Y ι Γ' := by
  classical
  have ht2S := h.t2
  have ht2 := h.t2Y
  have hcY := h.compY
  obtain ⟨D, Γ', hD, hN, hC⟩ := h.exists_painting
  obtain ⟨σ, hσc, hσ₁, hσ₂⟩ := h.map.exists_sec
  obtain ⟨j, hj, hjm⟩ := exists_inj_line h.surfS (h.lift.line K₀ hK₀)
  let R : Set S := range ψ \ F
  let ι : S → Y := fun x => if x ∈ R then σ x else j x
  have hιR : ∀ x ∈ R, ι x = σ x := fun x hx => ite_eq_left hx
  have hιn : ∀ x, x ∉ R → ι x = j x := fun x hx => ite_eq_right hx
  have hK₀F : ∀ y ∈ K₀, ψ y ∈ F := fun y hy => (show y ∈ ψ ⁻¹' F from h.lift.cover ▸ ⟨K₀, hK₀, hy⟩)
  have hσF : ∀ x ∈ R, ψ (σ x) ∉ F := fun x hx => by
    rw [hσ₁ x hx]
    exact hx.2
  have hinj : Function.Injective ι := by
    intro x x' he
    by_cases hx : x ∈ R <;> by_cases hx' : x' ∈ R
    · rw [hιR x hx, hιR x' hx'] at he
      rw [← hσ₁ x hx, he, hσ₁ x' hx']
    · rw [hιR x hx, hιn x' hx'] at he
      exact absurd (hK₀F _ (hjm x').1) (he ▸ hσF x hx)
    · rw [hιn x hx, hιR x' hx'] at he
      exact absurd (hK₀F _ (hjm x).1) (he ▸ hσF x' hx')
    · rw [hιn x hx, hιn x' hx'] at he
      exact hj he
  have hrc : IsClosed (range ψ) := (isCompact_range h.map.cont).isClosed
  have hclR : ∀ c ∈ keepCells Γ ψ F, closure c ⊆ range ψ := fun c hc => closure_minimal (fun x hx
    => (hc.2 hx).1) hrc
  have himg : ∀ c ∈ keepCells Γ ψ F, ι '' c = ψ ⁻¹' c := fun c hc => by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [hιR x (hc.2 hx), mem_preimage, hσ₁ x (hc.2 hx)]
      exact hx
    · intro hy
      have hyR : ψ y ∈ R := hc.2 hy
      exact ⟨ψ y, hy, by rw [hιR _ hyR, hσ₂ y hyR.2]⟩
  let A : Set S := {n ∈ Γ.N \ F | ∃ c ∈ keepCells Γ ψ F, n ∈ tilde c}
  have hAR : ∀ n ∈ A, n ∈ R := fun n hn => by
    obtain ⟨c, hc, hnc⟩ := hn.2
    exact ⟨hclR c hc hnc.1, hn.1.2⟩
  have hOS := (cuff_statement.{0} S h.surfS).2.2
  have hOY := (cuff_statement.{0} Y h.surfY).2.2
  have hbdR : ∀ x ∈ R, σ x ∈ bd Y ↔ x ∈ bd S := fun x hx => by
    rw [h.map.mem_bd_iff (hσF x hx), hσ₁ x hx]
  have hactive : ∀ n ∈ Γ.N, n ∉ F → n ∈ R → n ∈ bd S → n ∈ A := fun n hn hnF hnR hnb => by
    obtain ⟨c, hc, hnt⟩ := exists_cell_node h.surfS hn hnb
    refine ⟨⟨hn, hnF⟩, c, ⟨hc, ?_⟩, hnt⟩
    refine (h.side hc).resolve_right fun hd => ?_
    obtain ⟨z, hz, hzc⟩ := mem_closure_iff.mp hnt.1 R h.map.isOpen hnR
    exact disjoint_left.mp hd hzc hz.1
  have hconnR : ∀ {L : Set S}, IsPreconnected L → Disjoint L F → (L ∩ R).Nonempty → L ⊆ R
    := fun {L} hL hd hne => by
    exact preconnected_set_respects_cut_range (Y := Y) (S := S) (Γ := Γ) (ψ := ψ) (F := F) (n₁ :=
      n₁) (n₂ := n₂) (Ks := Ks) (e₁ := e₁) (e₂ := e₂) h hrc (L := L) hL hd hne
  have hlift : ∀ {L : Set S} {u v : S}, IsLineWithEnds L u v → L ⊆ bd S → Disjoint L F → u ∈ R
    → L ⊆ R ∧ IsLineWithEnds (σ '' L) (σ u) (σ v) ∧ σ '' L ⊆ bd Y := by
    intro L u v hL hLb hd hu
    have hLR := hconnR (isPreconnected_line hL) hd ⟨u, hL.left_mem, hu⟩
    refine ⟨hLR, ?_, ?_⟩
    · obtain ⟨a, ha, hr, rfl, rfl⟩ := hL.exists_arc
      have hmem : ∀ t, a t ∈ R := fun t => hLR (hr ▸ mem_range_self t)
      have harc : IsArcMap (σ ∘ a) := ⟨hσc.comp_continuous ha.1 hmem, fun s t he => ha.2 (by
        have := congrArg ψ he
        simpa only [Function.comp, hσ₁ _ (hmem _)] using this)⟩
      have hline := harc.isLineWithEnds
      rwa [range_comp, hr] at hline
    · rintro _ ⟨x, hx, rfl⟩
      exact (hbdR x (hLR hx)).mpr (hLb hx)
  have hcuffb : ∀ {Θ : Set S}, Θ ∈ cuffs S → Θ ⊆ bd S := fun {Θ} hΘ => by
    obtain ⟨x, -, rfl⟩ := hΘ
    exact connectedComponentIn_subset _ _
  have hcuffY : ∀ {Θ : Set Y}, Θ ∈ cuffs Y → Θ ⊆ bd Y := fun {Θ} hΘ => by
    obtain ⟨x, -, rfl⟩ := hΘ
    exact connectedComponentIn_subset _ _
  have hfull : ∀ Θ ∈ cuffs S, ∀ a ∈ Θ, a ∈ R → Disjoint Θ F → ∀ Φ ∈ cuffs Y, σ a ∈ Φ
    → ∀ y ∈ Γ'.N, y ∈ Φ → ∃ m ∈ A ∩ Θ, y = ι m := by
    intro Θ hΘ a haΘ haR hd Φ hΦ hσa y hyN hyΦ
    have hΘc : IsPreconnected Θ := by
      obtain ⟨x, -, rfl⟩ := hΘ
      exact isPreconnected_connectedComponentIn
    have hΘR := hconnR hΘc hd ⟨a, haΘ, haR⟩
    have hX : IsOArc (σ '' Θ) := (hOS Θ hΘ).image (hσc.mono hΘR) h.map.cont.continuousOn fun x hx
      => hσ₁ x (hΘR hx)
    have hs : σ '' Θ ⊆ Φ := subset_cuff hΦ (hΘc.image _ (hσc.mono hΘR)) (by
      rintro _ ⟨x, hx, rfl⟩
      exact (hbdR x (hΘR hx)).mpr (hcuffb hΘ hx)) hσa (mem_image_of_mem _ haΘ)
    obtain ⟨φ⟩ := hOY Φ hΦ
    have heq := oarc_eq φ hX hs
    obtain ⟨m, hm, rfl⟩ := (heq ▸ hyΦ : y ∈ σ '' Θ)
    have hmF : m ∉ F := disjoint_left.mp hd hm
    have hmk : ψ (σ m) ∈ keepNodes Γ F n₁ n₂ := by
      have h1 := hyN
      rw [hN] at h1
      exact h1
    rw [hσ₁ m (hΘR hm)] at hmk
    have hmN : m ∈ Γ.N := h.keepNodes_subset hmk
    exact ⟨m, ⟨hactive m hmN hmF (hΘR hm) (hcuffb hΘ hm), hm⟩, (hιR m (hΘR hm)).symm⟩
  have hFnode : ∀ Θ, ∀ p ∈ Θ, Θ ∈ cuffs S → p ∈ F → p ∈ F ∩ (Γ.N ∩ Θ) := fun Θ p hp hΘ hF => by
    have h1 : p ∈ ({n₁, n₂} : Set S) := h.bdF ▸ ⟨hF, hcuffb hΘ hp⟩
    refine ⟨hF, ?_, hp⟩
    rcases h1 with rfl | rfl
    · exact h.n₁_N
    · exact h.n₂_N
  refine ⟨ι, Γ', ⟨hinj, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rintro _ ⟨c, hc, rfl⟩
    change ι '' c ∈ Γ'.C
    rw [himg c hc, hC]
    exact .inl ⟨c, hc, rfl⟩
  · rw [hC]
    exact ⟨_, .inr ⟨K₀, hK₀, rfl⟩⟩
  · rintro _ ⟨n, hn, rfl⟩
    rw [hιR n (hAR n hn), hN, mem_preimage, hσ₁ n (hAR n hn)]
    exact .inl hn.1
  · intro c hc n hn
    rw [himg c hc]
    obtain ⟨τ, -, h2, h3, h4, h5, -, -⟩ := h.exists_lift hc
    by_cases hnR : n ∈ R
    · rw [hιR n hnR, h5]
      constructor
      · rintro ⟨x, hx, he⟩
        have h6 : x = n := by
          have := congrArg ψ he
          rwa [h3 x hx.1, hσ₁ n hnR] at this
        exact h6 ▸ hx
      · intro hx
        refine ⟨n, hx, ?_⟩
        have h6 := hσ₂ (τ n) (by rw [h3 n hx.1]; exact hn)
        rw [h3 n hx.1] at h6
        exact h6.symm
    · have hnr : n ∉ range ψ := fun hr => hnR ⟨hr, hn⟩
      constructor
      · intro hm
        exfalso
        rw [hιn n hnR] at hm
        have h6 : j n ∈ h.Z ∩ K₀ := ⟨.inl (mem_iUnion₂.mpr ⟨c, hc, hm.1⟩), (hjm n).1⟩
        rcases h.Z_inter hK₀ h6 with h7 | h7
        · exact (hjm n).2.1 h7
        · exact (hjm n).2.2 h7
      · intro hm
        exact absurd (hclR c hc hm.1) hnr
  · intro c hc
    rw [himg c hc]
    constructor
    · rintro ⟨y, hy, hyb⟩
      exact ⟨ψ y, hy, (h.map.mem_bd_iff (hc.2 hy).2).mp hyb⟩
    · rintro ⟨x, hx, hxb⟩
      obtain ⟨y, rfl⟩ := (hc.2 hx).1
      exact ⟨y, hx, (h.map.mem_bd_iff (hc.2 hx).2).mpr hxb⟩
  · intro n hn
    rw [hιR n (hAR n hn)]
    exact hbdR n (hAR n hn)
  · intro d hd hni
    rw [hC] at hd
    rcases hd with ⟨c, hc, rfl⟩ | ⟨K, hK, rfl⟩
    · exact absurd ⟨c, hc, himg c hc⟩ hni
    · have hb1 := (hD K hK).2.1 (h.lift.line K hK).left_mem
      have hb2 := (hD K hK).2.1 (h.lift.line K hK).right_mem
      simp only [(disc_diff_two (hD K hK).1 hb1 hb2).2.1]
      rw [disjoint_left]
      rintro y (rfl | rfl) ⟨n, hn, he⟩
      · have h1 := hσF n (hAR n hn)
        rw [← hιR n (hAR n hn), he, h.lift.end₁ K hK] at h1
        exact h1 h.n₁_mem.1
      · have h1 := hσF n (hAR n hn)
        rw [← hιR n (hAR n hn), he, h.lift.end₂ K hK] at h1
        exact h1 h.n₂_mem.1
  · intro Φ hΦ a ha hai b hb hbi
    have haR := hAR a ha
    have hbR := hAR b hb
    rw [hιR a haR] at hai
    rw [hιR b hbR] at hbi
    have hab : a ≠ b := by
      rintro rfl
      exact hbi hai
    have haB : a ∈ bd S := (hbdR a haR).mp (hcuffY hΦ hai)
    have hΘ : connectedComponentIn (bd S) a ∈ cuffs S := ⟨a, haB, rfl⟩
    refine ⟨_, hΘ, mem_connectedComponentIn haB, ?_⟩
    by_cases hbΘ : b ∈ connectedComponentIn (bd S) a
    swap
    · exact .inl hbΘ
    refine .inr ⟨hbΘ, ?_⟩
    have haΘ : a ∈ connectedComponentIn (bd S) a := mem_connectedComponentIn haB
    set Θ := connectedComponentIn (bd S) a with hΘdef
    obtain ⟨L₁, L₂, hL₁, hL₂, hu, -⟩ := (hOS Θ hΘ).lines haΘ hbΘ hab
    have hfree : ∀ {L : Set S}, IsLineWithEnds L a b → L ⊆ Θ → ¬ Disjoint L F := fun {L} hL hs hd
      => by
      obtain ⟨-, h2, h3⟩ := hlift hL (hs.trans (hcuffb hΘ)) hd haR
      exact hbi (subset_cuff hΦ (isPreconnected_line h2) h3 hai h2.left_mem h2.right_mem)
    obtain ⟨p, hp, hpF⟩ := not_disjoint_iff.mp (hfree hL₁ fun z hz => hu ▸ .inl hz)
    obtain ⟨q, hq, hqF⟩ := not_disjoint_iff.mp (hfree hL₂ fun z hz => hu ▸ .inr hz)
    have hpΘ : p ∈ Θ := hu ▸ .inl hp
    have hqΘ : q ∈ Θ := hu ▸ .inr hq
    exact ⟨p, hFnode Θ p hpΘ hΘ hpF, q, hFnode Θ q hqΘ hΘ hqF, inOrder_of_lines
      (hOS Θ hΘ) hL₁ hL₂ hu hp hq⟩
  · exact cut_cuff_node_order (Y := Y) (S := S) (Γ := Γ) (ψ := ψ) (F := F) (n₁ := n₁) (n₂ := n₂)
      (Ks := Ks) (e₁ := e₁) (e₂ := e₂) h Γ' hN σ hσ₁ ι A rfl hιR hAR hOS hOY hactive hlift hcuffb
      hfull hFnode
end GraphMinor.GM17
