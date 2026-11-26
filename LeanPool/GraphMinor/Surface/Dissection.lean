/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.ChartCells
public import LeanPool.GraphMinor.Surface.PushOff

/-!
# Dissections of closed surfaces

`IsDissection V E 𝓕` says that the closed discs in `𝓕` cover the space, that their boundaries lie in
the graph
`(V, E)`, that their interiors miss the graph and each other, and that a point off `V` lies in at
most two of them.
`exists_dissection` builds one around a given graph in a connected closed surface.
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology Metric

universe u

variable {X : Type u} [TopologicalSpace X]

/-- A cutting of the space into closed discs along a graph. -/
structure IsDissection (V : Set X) (E 𝓕 : Set (Set X)) : Prop where
  graph : IsGraph V E
  fin : 𝓕.Finite
  disc : ∀ Φ ∈ 𝓕, IsClosedDisc Φ
  cover : ⋃₀ 𝓕 = univ
  bd : ∀ Φ ∈ 𝓕, discBd Φ ⊆ ⋃₀ E
  int : ∀ Φ ∈ 𝓕, Disjoint (discInt Φ) (⋃₀ E)
  disj : ∀ Φ ∈ 𝓕, ∀ Φ' ∈ 𝓕, Φ ≠ Φ' → Disjoint (discInt Φ) Φ'
  count : ∀ x ∉ V, {Φ ∈ 𝓕 | x ∈ Φ}.encard ≤ 2

variable [T2Space X] {V : Set X} {E : Set (Set X)}

/-- Closed discs with boundary in a closed set `G`, whose interiors miss `G` and meet, are equal. -/
theorem eq_of_int_meet (hman : ∀ x : X, IsManifoldPoint x) {G Φ Φ' : Set X} (h1 : IsClosedDisc Φ)
    (h2 : IsClosedDisc Φ') (b1 : discBd Φ ⊆ G) (b2 : discBd Φ' ⊆ G) (i1 : Disjoint (discInt Φ) G)
    (i2 : Disjoint (discInt Φ') G) {z : X} (hz : z ∈ discInt Φ) (hz' : z ∈ Φ') : Φ = Φ' := by
  have hzG : z ∉ G := Set.disjoint_left.mp i1 hz
  have hz2 : z ∈ discInt Φ' := ⟨hz', fun h => hzG (b2 h)⟩
  have s1 : discInt Φ ⊆ discInt Φ' := by
    rcases h2.side hman h1.isPreconnected_discInt (i1.mono_right b2) with h | h
    · exact h
    · exact absurd hz' (Set.disjoint_left.mp h hz)
  have s2 : discInt Φ' ⊆ discInt Φ := by
    rcases h1.side hman h2.isPreconnected_discInt (i2.mono_right b1) with h | h
    · exact h
    · exact absurd hz.1 (Set.disjoint_left.mp h hz2)
  apply subset_antisymm
  · exact h1.subset_closure_discInt.trans (closure_minimal (s1.trans (discInt_subset Φ'))
    h2.isClosed)
  · exact h2.subset_closure_discInt.trans (closure_minimal (s2.trans (discInt_subset Φ))
    h1.isClosed)

/-- The cells of finitely many discs, whose interiors cover the space, form a dissection. -/
theorem isDissection_of_cells (hman : ∀ x : X, IsManifoldPoint x) (hg : IsGraph V E) {𝓑 : Set
  (Set X)} (h𝓑 : 𝓑.Finite)
    (hd : ∀ B ∈ 𝓑, IsClosedDisc B) (𝓒 : Set X → Set (Set X)) (hc : ∀ B ∈ 𝓑, IsCells V B (⋃₀ E)
      (𝓒 B)) (hin : ∀ x, ∃ B ∈ 𝓑, x ∈ discInt B) :
    IsDissection V E (⋃ B ∈ 𝓑, 𝓒 B) := by
  have hmem : ∀ {Φ}, Φ ∈ (⋃ B ∈ 𝓑, 𝓒 B) → ∃ B ∈ 𝓑, Φ ∈ 𝓒 B := fun {Φ} h => by simpa using h
  have hdisc : ∀ Φ ∈ (⋃ B ∈ 𝓑, 𝓒 B), IsClosedDisc Φ := fun Φ h => by
    obtain ⟨B, hB, hΦ⟩ := hmem h
    exact (hc B hB).disc Φ hΦ
  have hbd : ∀ Φ ∈ (⋃ B ∈ 𝓑, 𝓒 B), discBd Φ ⊆ ⋃₀ E := fun Φ h => by
    obtain ⟨B, hB, hΦ⟩ := hmem h
    exact (hc B hB).bd Φ hΦ
  have hint : ∀ Φ ∈ (⋃ B ∈ 𝓑, 𝓒 B), Disjoint (discInt Φ) (⋃₀ E) := fun Φ h => by
    obtain ⟨B, hB, hΦ⟩ := hmem h
    exact (hc B hB).int Φ hΦ
  have key : ∀ Φ ∈ (⋃ B ∈ 𝓑, 𝓒 B), ∀ Φ' ∈ (⋃ B ∈ 𝓑, 𝓒 B), ∀ z ∈ discInt Φ, z ∈ Φ' → Φ = Φ'
    := fun Φ h Φ' h' z hz hz' =>
    eq_of_int_meet hman (hdisc Φ h) (hdisc Φ' h') (hbd Φ h) (hbd Φ' h') (hint Φ h)
      (hint Φ' h') hz hz'
  refine ⟨hg, h𝓑.biUnion fun B hB => (hc B hB).fin, hdisc, ?_, hbd, hint, ?_, ?_⟩
  · refine eq_univ_of_forall fun x => ?_
    obtain ⟨B, hB, hx⟩ := hin x
    have h1 : x ∈ ⋃₀ 𝓒 B := by rw [(hc B hB).cover]; exact hx.1
    obtain ⟨Φ, hΦ, hxΦ⟩ := h1
    exact ⟨Φ, mem_biUnion hB hΦ, hxΦ⟩
  · intro Φ h Φ' h' hne
    exact Set.disjoint_left.mpr fun z hz hz' => hne (key Φ h Φ' h' z hz hz')
  · intro x hxV
    obtain ⟨B, hB, hx⟩ := hin x
    refine (encard_le_encard ?_).trans ((hc B hB).count x hxV)
    rintro Φ ⟨h, hxΦ⟩
    have h1 := (hdisc Φ h).subset_closure_discInt hxΦ
    obtain ⟨z, hz, hz'⟩ := mem_closure_iff.mp h1 _ ((hd B hB).isOpen_discInt hman) hx
    have h2 : z ∈ ⋃₀ 𝓒 B := by rw [(hc B hB).cover]; exact hz.1
    obtain ⟨Ψ, hΨ, hzΨ⟩ := h2
    have h3 := key Φ h Ψ (mem_biUnion hB hΨ) z hz' hzΨ
    exact ⟨h3 ▸ hΨ, hxΦ⟩

omit [T2Space X] in
theorem IsOArc.exists_three {P : Set X} (hP : IsOArc P) : ∃ a b d, a ∈ P ∧ b ∈ P ∧ d ∈ P ∧ a ≠ b
  ∧ a ≠ d ∧ b ≠ d := by
  obtain ⟨φ⟩ := id hP
  have key : ∀ θ θ' : ℝ, θ ∈ Icc (0 : ℝ) 5 → θ' ∈ Icc (0 : ℝ) 5 → θ < θ' →
      (φ (Circle.exp θ)).1 ≠ (φ (Circle.exp θ')).1 := fun θ θ' h1 h2 h3 he => by
    obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp (φ.injective (Subtype.ext he))
    have hpi := Real.pi_gt_three
    rcases le_or_gt 0 m with h4 | h4
    · have h5 : (0 : ℝ) ≤ m := by exact_mod_cast h4
      nlinarith
    · have h5 : (m : ℝ) ≤ -1 := by exact_mod_cast (by omega : m ≤ -1)
      nlinarith [h1.1, h2.2]
  exact ⟨_, _, _, (φ (Circle.exp 0)).2, (φ (Circle.exp 1)).2, (φ (Circle.exp 2)).2,
    key 0 1 (by norm_num) (by norm_num) (by norm_num), key 0 2 (by norm_num) (by norm_num)
      (by norm_num),
    key 1 2 (by norm_num) (by norm_num) (by norm_num)⟩

omit [T2Space X] in
/-- A dissection of a connected closed surface around a given graph. The hypothesis `hZ` says that
the graph
hangs well on a set that stays connected when a point is removed, as soon as this set meets each `C
∈ 𝓒c` twice. -/
theorem exists_dissection (hT : IsClosedSurface X) [ConnectedSpace X] {V₀ : Set X} {E₀ : Set
  (Set X)}
    (hg : IsGraph V₀ E₀) (hno : V₀ ⊆ ⋃₀ E₀) {𝓒c : Set (Set X)} (hfin : 𝓒c.Finite)
      (hconn : ∀ C ∈ 𝓒c, TwoConn C)
    (h3 : ∀ C ∈ 𝓒c, ∃ a b d, a ∈ C ∧ b ∈ C ∧ d ∈ C ∧ a ≠ b ∧ a ≠ d ∧ b ≠ d)
    (hZ : ∀ G : Set X, TwoConn G → (∀ C ∈ 𝓒c, ∃ x y, x ∈ G ∩ C ∧ y ∈ G ∩ C ∧ x ≠ y) → TwoConn
      (G ∪ ⋃₀ E₀)) :
    ∃ (V : Set X) (E 𝓕 : Set (Set X)), V₀ ⊆ V ∧ ⋃₀ E₀ ⊆ ⋃₀ E ∧ IsDissection V E 𝓕 := by
  classical
  obtain ⟨hcpt, ht2, hint⟩ := id hT
  have hman : ∀ x : X, IsManifoldPoint x := fun x => (hint x).isManifoldPoint
  obtain ⟨x₀⟩ : Nonempty X := inferInstance
  obtain ⟨U, h, g, c, -, -⟩ := (hint x₀).exists_ballChart (W := univ) isOpen_univ (mem_univ _) (R
    := 3) (by norm_num)
  obtain ⟨L, hL, hLu⟩ := hg.exists_list
  obtain ⟨P, D, hPO, hPt, -, -, -, -, -⟩ := exists_tame_curve' hman c L hL
  have hgrE : gr V₀ E₀ = ⋃₀ E₀ := union_eq_right.mpr hno
  rw [hLu, ← hgrE] at hPt
  obtain ⟨V1, E1, hV1, hg1, hgr1, hno1⟩ := hg.add_curve hPO hPt
  obtain ⟨u, w, -, hu, hw, -, huw, -, -⟩ := hPO.exists_three
  have hch : ∀ C : Set X, ∃ a b d : X, C ∈ 𝓒c → a ∈ C ∧ b ∈ C ∧ d ∈ C ∧ a ≠ b ∧ a ≠ d ∧ b ≠ d
    := fun C => by
    by_cases hC : C ∈ 𝓒c
    · obtain ⟨a, b, d, h'⟩ := h3 C hC
      exact ⟨a, b, d, fun _ => h'⟩
    · exact ⟨x₀, x₀, x₀, fun h' => absurd h' hC⟩
  choose a b d hcd using hch
  let Pairs : Set (X × X) := insert (u, w) ((fun C => (a C, b C)) '' 𝓒c ∪ (fun C =>
    (a C, d C)) '' 𝓒c ∪
    (fun C => (b C, d C)) '' 𝓒c)
  have hPf : Pairs.Finite := (((hfin.image _).union (hfin.image _)).union (hfin.image _)).insert _
  have hPne : ∀ p ∈ Pairs, p.1 ≠ p.2 := by
    rintro p (rfl | ((⟨C, hC, rfl⟩ | ⟨C, hC, rfl⟩) | ⟨C, hC, rfl⟩))
    · exact huw
    · exact (hcd C hC).2.2.2.1
    · exact (hcd C hC).2.2.2.2.1
    · exact (hcd C hC).2.2.2.2.2
  obtain ⟨V, E, G, 𝓑, hVV, hPG, hgE, hnoE, hgrG, hTC, hGc, h𝓑, hB, hin⟩ := exists_skeleton hT hg1
    (hno1 hno)
    (G₀ := P) (Z := ⋃₀ E₀) (by rw [hgr1, hgrE, union_comm]) hPO.twoConn hPO.isCompact.isClosed hPf
      hPne
    (u := u) (w := w) (.inl rfl) hu hw
  have hgrE2 : gr V E = ⋃₀ E := union_eq_right.mpr hnoE
  have hmeet : ∀ C ∈ 𝓒c, ∃ x y, x ∈ G ∩ C ∧ y ∈ G ∩ C ∧ x ≠ y := by
    intro C hC
    by_contra hcon
    push Not at hcon
    obtain ⟨ha, hb, hd', hab, had, hbd⟩ := hcd C hC
    obtain ⟨c0, hc0⟩ : ∃ c0, ∀ z ∈ G ∩ C, z = c0 := by
      by_cases hne : (G ∩ C).Nonempty
      · obtain ⟨c0, hc0⟩ := hne
        exact ⟨c0, fun z hz => hcon z c0 hz hc0⟩
      · exact ⟨x₀, fun z hz => absurd ⟨z, hz⟩ hne⟩
    have hpair : ∃ p q, (p, q) ∈ Pairs ∧ p ∈ C ∧ q ∈ C ∧ p ≠ c0 ∧ q ≠ c0 := by
      by_cases h1 : a C = c0
      · exact ⟨b C, d C, .inr (.inr ⟨C, hC, rfl⟩), hb, hd', fun h' => hab (h1.trans h'.symm),
          fun h' => had (h1.trans h'.symm)⟩
      · by_cases h2 : b C = c0
        · exact ⟨a C, d C, .inr (.inl (.inr ⟨C, hC, rfl⟩)), ha, hd', h1,
            fun h' => hbd (h2.trans h'.symm)⟩
        · exact ⟨a C, b C, .inr (.inl (.inl ⟨C, hC, rfl⟩)), ha, hb, h1, h2⟩
    obtain ⟨p, q, hpq, hpC, hqC, hpc, hqc⟩ := hpair
    have hdisjG : Disjoint (C \ {c0}) G := Set.disjoint_left.mpr fun z hz hzG => hz.2
      (hc0 z ⟨hzG, hz.1⟩)
    obtain ⟨B, hBm, hpB⟩ := hin p
    obtain ⟨hdB, hbB, hpp⟩ := hB B hBm
    rcases hdB.side hman (hconn C hC c0) (hdisjG.mono_right hbB) with h1 | h1
    · exact hpp (p, q) hpq ⟨hpB.1, (h1 ⟨hqC, hqc⟩).1⟩
    · exact Set.disjoint_left.mp h1 ⟨hpC, hpc⟩ hpB.1
  have hTC2 : TwoConn (⋃₀ E) := by
    rw [← hgrE2, hgrG]
    exact hZ G hTC hmeet
  have hsub : G ⊆ ⋃₀ E := fun z hz => hgrE2 ▸ hgrG ▸ Or.inl hz
  have hcells : ∀ B : Set X, ∃ 𝓒, B ∈ 𝓑 → IsCells V B (⋃₀ E) 𝓒 := fun B => by
    by_cases hBm : B ∈ 𝓑
    · obtain ⟨hdB, hbB, -⟩ := hB B hBm
      obtain ⟨𝓒, h𝓒⟩ := exists_cells hman hgE hTC2 hdB (hbB.trans hsub) (hgrE2 ▸ hbB.trans hsub)
      exact ⟨𝓒, fun _ => h𝓒⟩
    · exact ⟨∅, fun h' => absurd h' hBm⟩
  choose 𝓒 h𝓒 using hcells
  refine ⟨V, E, _, hV1.trans hVV, ?_, isDissection_of_cells hman hgE h𝓑 (fun B hBm =>
    (hB B hBm).1) 𝓒 h𝓒 hin⟩
  rw [← hgrE2, hgrG]
  exact subset_union_right

end GraphMinor.Surface
