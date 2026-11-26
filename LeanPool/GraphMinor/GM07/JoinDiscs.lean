/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.StarDisc

/-!
# Joining two closed discs that touch in a point

Two closed discs `A` and `B` of a closed surface that meet in one point `p` of their boundaries lie
in one
closed disc, which adds only a small neighbourhood of `p` (`exists_join`). This is the step that
makes a chain of
discs into one disc in the thickening of a forest in Graph Minors VII, (3.4), claim (1) (page 220).

We take a star disc `R` around `p` for the drawing made of the two boundaries. Then `bd(A)` is a
chord of `R`, and one
side of it lies in `A`, and the same holds for `B`. The union of `A` with the other side of its
chord is a disc. So
is `B` without the side in `R`, and these two discs meet in an arc of `bd(R)`. So `disc_union`
applies.
-/

@[expose] public section

namespace GraphMinor.GM07

open Set Topology Metric GraphMinor.Surface GraphMinor.GM11

variable {S : Type} [TopologicalSpace S]

private theorem disc_inter_collar_eq_boundary_arc
    {S : Type} [TopologicalSpace S]
    {A : Set S}
    (hsubA : discBd A ⊆ A)
    (ℓA : Set S)
    (EA : Set S)
    (disA : Disjoint (EA \ ℓA) A)
    (hℓAE : ℓA ⊆ EA)
    (hℓAb : ℓA ⊆ discBd A) :
    A ∩ EA = ℓA := by
  ext x
  constructor
  · rintro ⟨h1, h2⟩
    by_contra h3
    exact disjoint_left.mp disA ⟨h2, h3⟩ h1
  · exact fun h => ⟨hsubA (hℓAb h), hℓAE h⟩

/-- **Joining two discs at a point.** -/
theorem exists_join (hS : IsClosedSurface S) {A B : Set S} (hA : IsClosedDisc A)
  (hB : IsClosedDisc B) {p : S}
    (hAB : A ∩ B = {p}) (hpA : p ∈ discBd A) (hpB : p ∈ discBd B) {W : Set S} (hW : IsOpen W)
      (hpW : p ∈ W) :
    ∃ D, IsClosedDisc D ∧ A ∪ B ⊆ D ∧ D ⊆ A ∪ B ∪ W ∧ p ∈ discInt D ∧
      (discBd A ∪ discBd B) \ W ⊆ discBd D ∧
      discBd D ⊆ discBd A ∪ discBd B ∪ W := by
  classical
  have ht2 : T2Space S := hS.2.1
  have hbA := hA.isOArc_discBd
  have hbB := hB.isOArc_discBd
  have hsubB : discBd B ⊆ B := GM11.discBd_subset B
  -- The drawing made of the two boundaries.
  obtain ⟨ΓA, hAU, hAV⟩ := exists_loop_drawing hbA hpA
  obtain ⟨ΓB, hBU, hBV⟩ := exists_loop_drawing hbB hpB
  have hmeet : ΓA.U ∩ ΓB.U ⊆ ΓA.V ∩ ΓB.V := by
    rw [hAU, hBU, hAV, hBV]
    rintro x ⟨h1, h2⟩
    have : x ∈ A ∩ B := ⟨GM11.discBd_subset A h1, hsubB h2⟩
    rw [hAB] at this
    exact ⟨this, this⟩
  let Γ := ΓA.glue ΓB hmeet
  have hΓU : Γ.U = discBd A ∪ discBd B := by
    change ΓA.U ∪ ΓB.U = _
    rw [hAU, hBU]
  have hΓV : p ∈ Γ.V := Or.inl (hAV ▸ rfl)
  have hinV : ∀ x, x ∈ discBd A ∩ discBd B → x ∈ Γ.V := fun x hx => Or.inl (by
    have : x ∈ A ∩ B := ⟨GM11.discBd_subset A hx.1, hsubB hx.2⟩
    rw [hAB] at this
    rw [hAV]
    exact this)
  have nA : IsGammaNice Γ (discBd A) :=
    nice_of_cover hbA.isCompact.isClosed hbB.isCompact.isClosed (le_of_eq hΓU)
      (hΓU ▸ subset_union_left) hinV
  have nB : IsGammaNice Γ (discBd B) :=
    nice_of_cover hbB.isCompact.isClosed hbA.isCompact.isClosed
      (le_of_eq (hΓU.trans (union_comm _ _)))
      (hΓU ▸ subset_union_right) fun x hx => hinV x ⟨hx.2, hx.1⟩
  obtain ⟨wA, hwA, hwAp⟩ := hbA.exists_ne p
  obtain ⟨wB, hwB, hwBp⟩ := hbB.exists_ne p
  have hW' : IsOpen (W \ {wA, wB}) := hW.sdiff (Set.toFinite _).isClosed
  have hpW' : p ∈ W \ {wA, wB} := ⟨hpW, by rintro (e | e); exacts [hwAp e.symm, hwBp e.symm]⟩
  obtain ⟨R, hR, hRW⟩ := exists_starDisc hS Γ hΓV hW' hpW'
  have hRW₁ : R ⊆ W := hRW.trans sdiff_subset
  have hwAR : wA ∉ R := fun h => (hRW h).2 (.inl rfl)
  have hwBR : wB ∉ R := fun h => (hRW h).2 (.inr rfl)
  obtain ⟨ℓA, s, t, ΔA, EA, cA, cA', lA, hst, eA, dA, dEA, uA, iA, lcA, lcA', ucA, icA, bΔA, bEA,
    hbdA, pA, ΔAA, disA⟩ :=
    exists_disc_sides hS hR hA hpA hwA hwAR nA
  obtain ⟨ℓB, s', t', ΔB, EB, cB, cB', lB, hst', eB, dB, dEB, uB, iB, lcB, lcB', ucB, icB, bΔB,
    bEB, hbdB, pB, ΔBB, disB⟩ :=
    exists_disc_sides hS hR hB hpB hwB hwBR nB
  have hRc : IsClosed R := hR.disc.isClosed
  have hpi : p ∈ discInt R := hR.mem
  have hpbd : p ∉ discBd R := hpi.2
  have hbR : discBd R ⊆ R := GM11.discBd_subset R
  have hℓAE : ℓA ⊆ EA := fun x hx => ((iA ▸ hx : x ∈ ΔA ∩ EA)).2
  have hℓAb : ℓA ⊆ discBd A := fun x hx => (eA ▸ hx : x ∈ discBd A ∩ R).1
  have hℓBb : ℓB ⊆ discBd B := fun x hx => (eB ▸ hx : x ∈ discBd B ∩ R).1
  have hℓBR : ℓB ⊆ R := fun x hx => (eB ▸ hx : x ∈ discBd B ∩ R).2
  have hbEA : ℓA ⊆ discBd EA := fun x hx => bEA ▸ Or.inr hx
  obtain ⟨d1, b1⟩ := disc_union A EA ℓA s t hA dEA lA
    (disc_inter_collar_eq_boundary_arc (GM11.discBd_subset A) ℓA EA disA hℓAE hℓAb) hℓAb hbEA
  -- The part of `B` in `R`.
  have hBR : ∀ x ∈ B, x ∈ R → x ∈ ΔB := fun x h1 h2 => by
    by_contra h3
    have h4 : x ∈ ΔB ∪ EB := uB ▸ h2
    rcases h4 with h4 | h4
    · exact h3 h4
    · have h5 : x ∉ ℓB := fun h6 => h3 ((iB ▸ h6 : x ∈ ΔB ∩ EB).1)
      exact disjoint_left.mp disB ⟨h4, h5⟩ h1
  have hsubR : ΔB ⊆ R := fun x hx => uB ▸ Or.inl hx
  have hcBR : cB ⊆ discBd R := fun x hx => ucB ▸ Or.inl hx
  have hbm : discBd ΔB ∩ discBd B = ℓB := by
    ext x
    constructor
    · rintro ⟨h1, h2⟩
      rw [bΔB] at h1
      rcases h1 with h1 | h1
      · rw [eB]
        exact ⟨h2, hbR (hcBR h1)⟩
      · exact h1
    · exact fun h => ⟨bΔB ▸ Or.inr h, hℓBb h⟩
  obtain ⟨d2, b2, m2⟩ := disc_difference ΔB B ℓB s' t' dB hB ΔBB lB hbm
  set B' : Set S := closure (B \ ΔB) with hB'
  have hBc : IsClosed B := hB.isClosed
  have hB'B : B' ⊆ B := closure_minimal sdiff_subset hBc
  have hends : ∀ x, x ∈ ℓB → x ∈ discBd R → x = s' ∨ x = t' := fun x h1 h2 => by
    have : x ∈ ℓB ∩ discBd R := ⟨h1, h2⟩
    rw [hbdB] at this
    exact this
  have hcBm : discBd ΔB \ (ℓB \ {s', t'}) = cB := by
    ext x
    constructor
    · rintro ⟨h1, h2⟩
      rw [bΔB] at h1
      rcases h1 with h1 | h1
      · exact h1
      · have h3 : x ∈ ({s', t'} : Set S) := by
          by_contra h3
          exact h2 ⟨h1, h3⟩
        rcases h3 with rfl | rfl
        · exact lcB.left_mem
        · exact lcB.right_mem
    · intro h
      refine ⟨bΔB ▸ Or.inl h, fun h1 => h1.2 ?_⟩
      exact hends x h1.1 (hcBR h)
  rw [hcBm] at m2
  have hΔE : ΔB ⊆ EA := fun x hx => by
    have h1 : x ∈ ΔA ∪ EA := uA ▸ hsubR hx
    rcases h1 with h1 | h1
    · have h2 : x ∈ A ∩ B := ⟨ΔAA h1, ΔBB hx⟩
      rw [hAB] at h2
      exact hℓAE (by rw [mem_singleton_iff.mp h2]; exact pA)
    · exact h1
  have hpΔ : p ∈ ΔB := (iB ▸ pB : p ∈ ΔB ∩ EB).1
  have hmid : (A ∪ EA) ∩ B' = cB := by
    ext x
    constructor
    · rintro ⟨h1 | h1, h2⟩
      · have h3 : x ∈ A ∩ B := ⟨h1, hB'B h2⟩
        rw [hAB] at h3
        have h4 : x = p := h3
        rw [h4] at h2
        have h5 : p ∈ cB := m2 ▸ ⟨h2, hpΔ⟩
        exact (hpbd (hcBR h5)).elim
      · have h3 : x ∈ R := uA ▸ Or.inr h1
        exact m2 ▸ ⟨h2, hBR x (hB'B h2) h3⟩
    · intro h
      have h1 : x ∈ B' ∩ ΔB := m2 ▸ h
      exact ⟨.inr (hΔE h1.2), h1.1⟩
  have hcbd : cB ⊆ discBd (A ∪ EA) := fun x hx => by
    rw [b1]
    have h1 : x ∈ cA ∪ cA' := ucA ▸ hcBR hx
    have hxΔ : x ∈ ΔB := (m2 ▸ hx : x ∈ B' ∩ ΔB).2
    have hxp : x ≠ p := fun e => hpbd (e ▸ hcBR hx)
    have hxb : x ∈ discBd EA := by
      rcases h1 with h1 | h1
      · have h2 : x ∈ ΔA := by
          have : x ∈ discBd ΔA := bΔA ▸ Or.inl h1
          exact GM11.discBd_subset _ this
        have h3 : x ∈ A ∩ B := ⟨ΔAA h2, ΔBB hxΔ⟩
        rw [hAB] at h3
        exact (hxp h3).elim
      · exact bEA ▸ Or.inl h1
    refine ⟨.inr hxb, fun h2 => h2.2 ?_⟩
    have h3 : x ∈ ℓA ∩ discBd R := ⟨h2.1, hcBR hx⟩
    rw [hbdA] at h3
    exact h3
  have hcbd' : cB ⊆ discBd B' := fun x hx => by
    rw [b2]
    have h1 : x ∈ discBd ΔB := bΔB ▸ Or.inl hx
    refine ⟨.inl h1, fun h2 => h2.2 ?_⟩
    exact hends x h2.1 (hcBR hx)
  obtain ⟨d3, b3⟩ := disc_union (A ∪ EA) B' cB s' t' d1 d2 lcB hmid hcbd hcbd'
  have hne₁ : p ≠ s ∧ p ≠ t := ⟨fun e => hpbd (by
    have : s ∈ ℓA ∩ discBd R := by rw [hbdA]; exact .inl rfl
    rw [e]
    exact this.2), fun e => hpbd (by
    have : t ∈ ℓA ∩ discBd R := by rw [hbdA]; exact .inr rfl
    rw [e]
    exact this.2)⟩
  have hne₂ : p ≠ s' ∧ p ≠ t' := ⟨fun e => hpbd (by
    have : s' ∈ ℓB ∩ discBd R := by rw [hbdB]; exact .inl rfl
    rw [e]
    exact this.2), fun e => hpbd (by
    have : t' ∈ ℓB ∩ discBd R := by rw [hbdB]; exact .inr rfl
    rw [e]
    exact this.2)⟩
  have hEAR : EA ⊆ R := fun x hx => uA ▸ Or.inr hx
  have hbEsub : discBd EA ⊆ R := GM11.discBd_subset EA |>.trans hEAR
  have hbΔsub : discBd ΔB ⊆ R := (GM11.discBd_subset ΔB).trans hsubR
  have hcBnW : ∀ x, x ∉ W → x ∉ cB := fun x hx h => hx (hRW₁ (hbR (hcBR h)))
  refine ⟨(A ∪ EA) ∪ B', d3, ?_, ?_, ⟨?_, ?_⟩, ?_, ?_⟩
  · rintro x (h | h)
    · exact .inl (.inl h)
    · by_cases h1 : x ∈ ΔB
      · exact .inl (.inr (hΔE h1))
      · exact .inr (subset_closure ⟨h, h1⟩)
  · rintro x ((h | h) | h)
    · exact .inl (.inl h)
    · exact .inr (hRW₁ (hEAR h))
    · exact .inl (.inr (hB'B h))
  · exact .inl (.inl (GM11.discBd_subset A hpA))
  · rw [b3]
    rintro ⟨h1 | h1, -⟩
    · rw [b1] at h1
      exact h1.2 ⟨pA, by rintro (e | e); exacts [hne₁.1 e, hne₁.2 e]⟩
    · rw [b2] at h1
      exact h1.2 ⟨pB, by rintro (e | e); exacts [hne₂.1 e, hne₂.2 e]⟩
  · rintro x ⟨h1 | h1, h2⟩
    · rw [b3, b1]
      exact ⟨.inl ⟨.inl h1, fun h3 => h2 (hRW₁ (eA ▸ h3.1 : x ∈ discBd A ∩ R).2)⟩,
        fun h3 => hcBnW x h2 h3.1⟩
    · rw [b3, b2]
      exact ⟨.inr ⟨.inr h1, fun h3 => h2 (hRW₁ (eB ▸ h3.1 : x ∈ discBd B ∩ R).2)⟩,
        fun h3 => hcBnW x h2 h3.1⟩
  · intro x hx
    rw [b3] at hx
    rcases hx.1 with h1 | h1
    · rw [b1] at h1
      rcases h1.1 with h2 | h2
      · exact .inl (.inl h2)
      · exact .inr (hRW₁ (hbEsub h2))
    · rw [b2] at h1
      rcases h1.1 with h2 | h2
      · exact .inr (hRW₁ (hbΔsub h2))
      · exact .inl (.inr h2)

/-- **Joining two discs along a line.** Two disjoint closed discs and a line between their
boundaries lie in one closed
disc, which adds no point of the closed set `Z`, and keeps the points of `Z` on the two boundaries
on its boundary. -/
theorem exists_merge (hS : IsClosedSurface S) {D₁ D₂ L Z : Set S} {p q : S} (h₁ : IsClosedDisc D₁)
  (h₂ : IsClosedDisc D₂)
    (hd : Disjoint D₁ D₂) (hL : IsLineWithEnds L p q) (hp : p ∈ discBd D₁) (hq : q ∈ discBd D₂)
    (hLD : L ∩ (D₁ ∪ D₂) ⊆ {p, q}) (hZ : IsClosed Z) (hLZ : Disjoint L Z) :
    ∃ D, IsClosedDisc D ∧ D₁ ∪ D₂ ⊆ D ∧ D ⊆ D₁ ∪ D₂ ∪ Zᶜ ∧ L ⊆ discInt D ∧ discInt D₁ ⊆ discInt D
      ∧ discInt D₂ ⊆ discInt D ∧
      (discBd D₁ ∪ discBd D₂) ∩ Z ⊆ discBd D ∧ discBd D ⊆ discBd D₁ ∪ discBd D₂ ∪ Zᶜ := by
  have ht2 : T2Space S := hS.2.1
  have hman : ∀ x : S, IsManifoldPoint x := fun x => (hS.2.2 x).isManifoldPoint
  have hpD₁ : p ∈ D₁ := GM11.discBd_subset D₁ hp
  have hqD₂ : q ∈ D₂ := GM11.discBd_subset D₂ hq
  have hpq : p ≠ q := fun e => disjoint_left.mp hd hpD₁ (e ▸ hqD₂)
  have hpZ : p ∉ Z := disjoint_left.mp hLZ hL.left_mem
  have hqZ : q ∉ Z := disjoint_left.mp hLZ hL.right_mem
  have hc₁ := h₁.isClosed
  have hc₂ := h₂.isClosed
  have hZ₁ : IsClosed (D₁ ∪ D₂ ∪ Z) := (hc₁.union hc₂).union hZ
  have hLZ₁ : L ∩ (D₁ ∪ D₂ ∪ Z) ⊆ {p, q} := by
    rintro x ⟨hxL, hx | hx⟩
    · exact hLD ⟨hxL, hx⟩
    · exact (disjoint_left.mp hLZ hxL hx).elim
  obtain ⟨E, -, -, hE, hLE, hEZ, hpE, hqE, hbL, -⟩ := exists_edge_lens hS hL hpq hZ₁ hLZ₁
  have hEm : ∀ z ∈ E, z ∈ D₁ ∪ D₂ ∪ Z → z = p ∨ z = q := fun z h1 h2 => hEZ ⟨h1, h2⟩
  have hED₁ : D₁ ∩ E = {p} := by
    ext z
    constructor
    · rintro ⟨h1, h2⟩
      rcases hEm z h2 (.inl (.inl h1)) with e | e
      · exact e
      · exact (disjoint_left.mp hd h1 (e ▸ hqD₂)).elim
    · rintro rfl
      exact ⟨hpD₁, hLE hL.left_mem⟩
  have hW₁ : IsOpen (D₂ ∪ Z)ᶜ := (hc₂.union hZ).isOpen_compl
  have hpW₁ : p ∈ (D₂ ∪ Z)ᶜ := by
    rintro (h | h)
    · exact disjoint_left.mp hd hpD₁ h
    · exact hpZ h
  obtain ⟨D', d', hsub', hsup', hpi', hb', hb''⟩ := exists_join hS h₁ hE hED₁ hp hpE hW₁ hpW₁
  have hqbd : q ∈ discBd D' := hb' ⟨.inr hqE, fun h => h (.inl hqD₂)⟩
  have hD'D₂ : D' ∩ D₂ = {q} := by
    ext z
    constructor
    · rintro ⟨h1, h2⟩
      rcases hsup' h1 with (h3 | h3) | h3
      · exact (disjoint_left.mp hd h3 h2).elim
      · rcases hEm z h3 (.inl (.inr h2)) with e | e
        · exact (disjoint_left.mp hd hpD₁ (e ▸ h2)).elim
        · exact e
      · exact (h3 (.inl h2)).elim
    · rintro rfl
      exact ⟨GM11.discBd_subset D' hqbd, hqD₂⟩
  obtain ⟨D, d, hsub, hsup, hqi, hb, hb₂⟩ := exists_join hS d' h₂ hD'D₂ hqbd hq hZ.isOpen_compl hqZ
  have hD'D : D' ⊆ D := subset_union_left.trans hsub
  have hEoff : ∀ z ∈ E, z ∈ Z → False := fun z h1 h2 => by
    rcases hEm z h1 (.inr h2) with e | e
    · exact hpZ (e ▸ h2)
    · exact hqZ (e ▸ h2)
  refine ⟨D, d, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro z (h | h)
    · exact hD'D (hsub' (.inl h))
    · exact hsub (.inr h)
  · intro z hz
    by_cases hzZ : z ∈ Z
    · rcases hsup hz with (h1 | h1) | h1
      · rcases hsup' h1 with (h2 | h2) | h2
        · exact .inl (.inl h2)
        · exact (hEoff z h2 hzZ).elim
        · exact (h2 (.inr hzZ)).elim
      · exact .inl (.inr h1)
      · exact (h1 hzZ).elim
    · exact .inr hzZ
  · intro z hz
    by_cases h1 : z = p
    · rw [h1]
      exact discInt_mono hman d' hD'D hpi'
    by_cases h2 : z = q
    · rw [h2]
      exact hqi
    have h3 : z ∉ discBd E := fun h => by
      rcases hbL ⟨h, hz⟩ with e | e
      · exact h1 e
      · exact h2 e
    exact discInt_mono hman hE (subset_union_right.trans (hsub'.trans hD'D)) ⟨hLE hz, h3⟩
  · exact discInt_mono hman h₁ (subset_union_left.trans (hsub'.trans hD'D))
  · exact discInt_mono hman h₂ (subset_union_right.trans hsub)
  · rintro z ⟨h | h, hzZ⟩
    · exact hb ⟨.inl (hb' ⟨.inl h, fun h3 => h3 (.inr hzZ)⟩), fun h3 => h3 hzZ⟩
    · exact hb ⟨.inr h, fun h3 => h3 hzZ⟩
  · intro z hz
    by_cases hzZ : z ∈ Z
    · rcases hb₂ hz with (h1 | h1) | h1
      · rcases hb'' h1 with (h2 | h2) | h2
        · exact .inl (.inl h2)
        · exact (hEoff z (GM11.discBd_subset E h2) hzZ).elim
        · exact (h2 (.inr hzZ)).elim
      · exact .inl (.inr h1)
      · exact (h1 hzZ).elim
    · exact .inr hzZ

variable {V ι : Type}

/-- Two vertices are joined by a walk that uses only the edges in `E`, for a graph with ends `a` and
`b`. -/
def Reach (a b : ι → V) (E : Set ι) : V → V → Prop :=
  Relation.ReflTransGen fun x y => ∃ i ∈ E, (a i = x ∧ b i = y) ∨ (a i = y ∧ b i = x)

theorem Reach.symm {a b : ι → V} {E : Set ι} {x y : V} (h : Reach a b E x y) : Reach a b E y x := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih =>
    obtain ⟨i, hi, h1⟩ := hs
    exact Relation.ReflTransGen.head ⟨i, hi, h1.symm⟩ ih

theorem Reach.mono {a b : ι → V} {E E' : Set ι} (hE : E ⊆ E') {x y : V}
  (h : Reach a b E x y) : Reach a b E' x y := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih =>
    obtain ⟨i, hi, h1⟩ := hs
    exact ih.tail ⟨i, hE hi, h1⟩

/-- **Discs around a forest.** Let closed discs `c₀ v`, pairwise disjoint, be joined by pairwise
disjoint lines `L i` from
the disc of `a i` to the disc of `b i`, along a graph without cycles. Then the discs and lines of
each component
of the graph lie in one closed disc, and these discs are pairwise disjoint. They add no point of
`Z`, and they
keep the points of `Z` on the boundaries of the `c₀ v`, and only those. -/
theorem exists_forest_discs [Finite V] [Finite ι] (hS : IsClosedSurface S) {c₀ : V → Set S} {L : ι
  → Set S} {p q : ι → S} {a b : ι → V}
    {Z : Set S} (hd : ∀ v, IsClosedDisc (c₀ v)) (hdj : ∀ u v, u ≠ v → Disjoint (c₀ u) (c₀ v))
    (hL : ∀ i, IsLineWithEnds (L i) (p i) (q i)) (hp : ∀ i, p i ∈ discBd (c₀ (a i)))
      (hq : ∀ i, q i ∈ discBd (c₀ (b i)))
    (hLc : ∀ i v, L i ∩ c₀ v ⊆ {p i, q i}) (hLL : ∀ i j, i ≠ j → Disjoint (L i) (L j))
      (hZ : IsClosed Z)
    (hLZ : ∀ i, Disjoint (L i) Z) (hfor : ∀ (E : Set ι) (i : ι), i ∉ E → ¬ Reach a b E (a i)
      (b i)) :
    ∃ c : V → Set S, (∀ v, IsClosedDisc (c v)) ∧ (∀ u v, c u = c v → Reach a b univ u v) ∧
      (∀ u v, c u ≠ c v → Disjoint (c u) (c v)) ∧ (∀ i, L i ⊆ discInt (c (a i)) ∧ c (a i) = c
        (b i)) ∧
      (∀ v, c₀ v ⊆ c v ∧ discInt (c₀ v) ⊆ discInt (c v)) ∧ (∀ v, c v ∩ Z ⊆ ⋃ w, c₀ w) ∧
      (∀ v, discBd (c₀ v) ∩ Z ⊆ discBd (c v)) ∧ ∀ v, discBd (c v) ∩ Z ⊆ ⋃ w, discBd (c₀ w) := by
  classical
  have ht2 : T2Space S := hS.2.1
  have := Fintype.ofFinite ι
  have hne : ∀ v, (c₀ v).Nonempty := fun v => by
    obtain ⟨e⟩ := hd v
    exact ⟨_, (e ⟨0, by simp [ClosedUnitDisc]⟩).2⟩
  suffices H : ∀ E : Finset ι, ∃ c : V → Set S, (∀ v, IsClosedDisc (c v)) ∧ (∀ u v, c u = c v
    → Reach a b (E : Set ι) u v) ∧
      (∀ u v, c u ≠ c v → Disjoint (c u) (c v)) ∧ (∀ i, i ∉ E → p i ∈ discBd (c (a i))
        ∧ q i ∈ discBd (c (b i))) ∧
      (∀ i, i ∉ E → ∀ v, L i ∩ c v ⊆ {p i, q i}) ∧ (∀ i ∈ E, L i ⊆ discInt (c (a i)) ∧ c (a i) = c
        (b i)) ∧
      (∀ v, c₀ v ⊆ c v ∧ discInt (c₀ v) ⊆ discInt (c v)) ∧ (∀ v, c v ∩ Z ⊆ ⋃ w, c₀ w) ∧
      (∀ v, discBd (c₀ v) ∩ Z ⊆ discBd (c v)) ∧ ∀ v, discBd (c v) ∩ Z ⊆ ⋃ w, discBd (c₀ w) by
    obtain ⟨c, h1, h2, h3, -, -, h6, h7, h8, h9, h10⟩ := H Finset.univ
    exact ⟨c, h1, fun u v h => (h2 u v h).mono (by simp), h3, fun i => h6 i (Finset.mem_univ i),
      h7, h8, h9, h10⟩
  intro E
  induction E using Finset.induction_on with
  | empty =>
    refine ⟨c₀, hd, fun u v h => ?_, fun u v h => hdj u v fun e => h (congrArg c₀ e),
      fun i _ => ⟨hp i, hq i⟩, fun i _ => hLc i,
      by simp, fun v => ⟨subset_rfl, subset_rfl⟩, fun v => ?_, fun v => inter_subset_left, fun v
        => ?_⟩
    · by_cases e : u = v
      · rw [e]
        exact Relation.ReflTransGen.refl
      · obtain ⟨x, hx⟩ := hne u
        exact (disjoint_left.mp (hdj u v e) hx (h ▸ hx)).elim
    · exact fun x hx => mem_iUnion.mpr ⟨v, hx.1⟩
    · exact fun x hx => mem_iUnion.mpr ⟨v, hx.1⟩
  | insert i E hiE ih =>
    obtain ⟨c, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := ih
    set D₁ := c (a i) with hD₁
    set D₂ := c (b i) with hD₂
    have hne12 : D₁ ≠ D₂ := fun e => hfor (E : Set ι) i (by simpa using hiE) (h2 _ _ e)
    let Merged : V → Prop := fun v => c v = D₁ ∨ c v = D₂
    let Z' : Set S := Z ∪ (⋃ j ∈ {j : ι | j ∉ E ∧ j ≠ i}, L j) ∪ ⋃ w ∈ {w : V | ¬ Merged w}, c w
    have hZ' : IsClosed Z' := (hZ.union ((Set.toFinite _).isClosed_biUnion fun j _ =>
      (hL j).isCompact.isClosed)).union
      ((Set.toFinite _).isClosed_biUnion fun w _ => (h1 w).isClosed)
    have hsubL : ∀ j, j ∉ E → j ≠ i → L j ⊆ Z' := fun j h h' x hx => .inl (.inr
      (mem_iUnion₂.mpr ⟨j, ⟨h, h'⟩, hx⟩))
    have hsubc : ∀ w, ¬ Merged w → c w ⊆ Z' := fun w h x hx => .inr (mem_iUnion₂.mpr ⟨w, h, hx⟩)
    have hsubZ : Z ⊆ Z' := fun x hx => .inl (.inl hx)
    have hdisj : ∀ w, ¬ Merged w → Disjoint (c w) D₁ ∧ Disjoint (c w) D₂ := fun w h =>
      ⟨h3 _ _ fun e => h (.inl e), h3 _ _ fun e => h (.inr e)⟩
    have hLZ' : Disjoint (L i) Z' := by
      refine disjoint_left.mpr fun x hx hxZ => ?_
      rcases hxZ with (h | h) | h
      · exact disjoint_left.mp (hLZ i) hx h
      · obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp h
        exact disjoint_left.mp (hLL i j hj.2.symm) hx hxj
      · obtain ⟨w, hw, hxw⟩ := mem_iUnion₂.mp h
        rcases h5 i hiE w ⟨hx, hxw⟩ with e | e
        · exact disjoint_left.mp (hdisj w hw).1 hxw (e ▸ GM11.discBd_subset _ (h4 i hiE).1)
        · exact disjoint_left.mp (hdisj w hw).2 hxw (e ▸ GM11.discBd_subset _ (h4 i hiE).2)
    have hLD : L i ∩ (D₁ ∪ D₂) ⊆ {p i, q i} := by
      rintro x ⟨hx, h | h⟩
      · exact h5 i hiE _ ⟨hx, h⟩
      · exact h5 i hiE _ ⟨hx, h⟩
    obtain ⟨D, d, hsub, hsup, hLi, hint₁, hint₂, hbdin, hbdout⟩ := exists_merge hS (h1 (a i)) (h1
      (b i)) (h3 _ _ hne12) (hL i)
      (h4 i hiE).1 (h4 i hiE).2 hLD hZ' hLZ'
    have hmsub : ∀ v, Merged v → c v ⊆ D := by
      rintro v (e | e)
      · rw [e]
        exact subset_union_left.trans hsub
      · rw [e]
        exact subset_union_right.trans hsub
    have hmint : ∀ v, Merged v → discInt (c v) ⊆ discInt D := by
      rintro v (e | e)
      · rwa [e]
      · rwa [e]
    have hZoff : ∀ x ∈ D, x ∈ Z' → ∃ v, Merged v ∧ x ∈ c v := fun x hx hxZ => by
      rcases hsup hx with (h | h) | h
      · exact ⟨a i, .inl rfl, h⟩
      · exact ⟨b i, .inr rfl, h⟩
      · exact (h hxZ).elim
    have hbin : ∀ v, Merged v → discBd (c v) ∩ Z' ⊆ discBd D := by
      rintro v (e | e) x hx
      · exact hbdin ⟨.inl (by rw [← hD₁, ← e]; exact hx.1), hx.2⟩
      · exact hbdin ⟨.inr (by rw [← hD₂, ← e]; exact hx.1), hx.2⟩
    let c' : V → Set S := fun v => if Merged v then D else c v
    have hc1 : ∀ {v}, Merged v → c' v = D := fun h => ite_eq_left h
    have hc2 : ∀ {v}, ¬ Merged v → c' v = c v := fun h => ite_eq_right h
    have hmem : ∀ {v}, Merged v ∨ ¬ Merged v := em _
    have hRE : (E : Set ι) ⊆ ((insert i E : Finset ι) : Set ι) := by simp
    have hconn : ∀ w, Merged w → Reach a b ((insert i E : Finset ι) : Set ι) w (a i) := by
      rintro w (e | e)
      · exact (h2 w (a i) e).mono hRE
      · refine ((h2 w (b i) e).mono hRE).tail ?_
        exact ⟨i, by simp, .inr ⟨rfl, rfl⟩⟩
    have hDne : (D₁).Nonempty := by
      obtain ⟨x, hx⟩ := hne (a i)
      exact ⟨x, (h7 (a i)).1 hx⟩
    have hoffD : ∀ w, ¬ Merged w → D ≠ c w := fun w hw e => by
      obtain ⟨x, hx⟩ := hDne
      exact disjoint_left.mp (hdisj w hw).1 (e ▸ (subset_union_left.trans hsub hx)) hx
    have hdisjD : ∀ w, ¬ Merged w → Disjoint D (c w) := fun w hw => disjoint_left.mpr fun x hx hxw
      => by
      obtain ⟨v, hv, hxv⟩ := hZoff x hx (hsubc w hw hxw)
      rcases hv with e | e
      · exact disjoint_left.mp (hdisj w hw).1 hxw (e ▸ hxv)
      · exact disjoint_left.mp (hdisj w hw).2 hxw (e ▸ hxv)
    refine ⟨c', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro v
      by_cases h : Merged v
      · rw [hc1 h]
        exact d
      · rw [hc2 h]
        exact h1 v
    · intro u v e
      by_cases hu : Merged u <;> by_cases hv : Merged v
      · exact (hconn u hu).trans (hconn v hv).symm
      · rw [hc1 hu, hc2 hv] at e
        exact (hoffD v hv e).elim
      · rw [hc2 hu, hc1 hv] at e
        exact (hoffD u hu e.symm).elim
      · rw [hc2 hu, hc2 hv] at e
        exact (h2 u v e).mono hRE
    · intro u v e
      by_cases hu : Merged u <;> by_cases hv : Merged v
      · exact (e (by rw [hc1 hu, hc1 hv])).elim
      · rw [hc1 hu, hc2 hv]
        exact hdisjD v hv
      · rw [hc2 hu, hc1 hv]
        exact (hdisjD u hu).symm
      · rw [hc2 hu, hc2 hv] at e ⊢
        exact h3 u v e
    · intro j hj
      have hj' : j ∉ E := fun h => hj (Finset.mem_insert_of_mem h)
      have hji : j ≠ i := fun h => hj (h ▸ Finset.mem_insert_self _ _)
      obtain ⟨g1, g2⟩ := h4 j hj'
      constructor
      · by_cases hv : Merged (a j)
        · rw [hc1 hv]
          exact hbin _ hv ⟨g1, hsubL j hj' hji (hL j).left_mem⟩
        · rw [hc2 hv]
          exact g1
      · by_cases hv : Merged (b j)
        · rw [hc1 hv]
          exact hbin _ hv ⟨g2, hsubL j hj' hji (hL j).right_mem⟩
        · rw [hc2 hv]
          exact g2
    · intro j hj v x hx
      have hj' : j ∉ E := fun h => hj (Finset.mem_insert_of_mem h)
      have hji : j ≠ i := fun h => hj (h ▸ Finset.mem_insert_self _ _)
      by_cases hv : Merged v
      · have hx2 : x ∈ D := (hc1 hv) ▸ hx.2
        obtain ⟨w, -, hxw⟩ := hZoff x hx2 (hsubL j hj' hji hx.1)
        exact h5 j hj' w ⟨hx.1, hxw⟩
      · exact h5 j hj' v ⟨hx.1, (hc2 hv) ▸ hx.2⟩
    · intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hjE
      · rw [hc1 (show Merged (a j) from .inl rfl), hc1 (show Merged (b j) from .inr rfl)]
        exact ⟨hLi, rfl⟩
      · obtain ⟨g1, g2⟩ := h6 j hjE
        by_cases hv : Merged (a j)
        · have hv' : Merged (b j) := by
            change c (b j) = _ ∨ c (b j) = _
            rw [← g2]
            exact hv
          rw [hc1 hv, hc1 hv']
          exact ⟨g1.trans (hmint _ hv), rfl⟩
        · have hv' : ¬ Merged (b j) := by
            change ¬ (c (b j) = _ ∨ c (b j) = _)
            rw [← g2]
            exact hv
          rw [hc2 hv, hc2 hv']
          exact ⟨g1, g2⟩
    · intro v
      by_cases hv : Merged v
      · rw [hc1 hv]
        exact ⟨(h7 v).1.trans (hmsub v hv), (h7 v).2.trans (hmint v hv)⟩
      · rw [hc2 hv]
        exact h7 v
    · intro v x hx
      by_cases hv : Merged v
      · have hx2 : x ∈ D := (hc1 hv) ▸ hx.1
        obtain ⟨w, -, hxw⟩ := hZoff x hx2 (hsubZ hx.2)
        exact h8 w ⟨hxw, hx.2⟩
      · exact h8 v ⟨(hc2 hv) ▸ hx.1, hx.2⟩
    · intro v x hx
      have hxv := h9 v hx
      by_cases hv : Merged v
      · rw [hc1 hv]
        exact hbin v hv ⟨hxv, hsubZ hx.2⟩
      · rw [hc2 hv]
        exact hxv
    · intro v x hx
      by_cases hv : Merged v
      · have hx2 : x ∈ discBd D := (hc1 hv) ▸ hx.1
        rcases hbdout hx2 with (h | h) | h
        · exact h10 _ ⟨h, hx.2⟩
        · exact h10 _ ⟨h, hx.2⟩
        · exact (h (hsubZ hx.2)).elim
      · exact h10 v ⟨(hc2 hv) ▸ hx.1, hx.2⟩

end GraphMinor.GM07
