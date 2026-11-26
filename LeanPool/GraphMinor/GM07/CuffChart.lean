/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.CuffCells
public import LeanPool.GraphMinor.Surface.FanSquare

/-!
# Charts of the cells

Graph Minors VII, (5.9), page 235. A cell of the annulus around a cuff is a closed disc with a
boundary in four parts. We give it a chart from the unit square, which on each side of the square is
a given parametrization of that part. Two neighbouring cells use the same parametrization of their
common side, so their charts agree there.
-/

@[expose] public section

namespace GraphMinor.GM07

open Set Topology Function Metric GraphMinor.Surface GraphMinor.GM11

universe u

variable {T : Type u} [TopologicalSpace T] [T2Space T]

/-- A parametrization of a line by the interval `[0,1]`. -/
structure IsParam (L : Set T) (u v : T) (p : ℝ → T) : Prop where
  cont : ContinuousOn p (Icc 0 1)
  inj : InjOn p (Icc 0 1)
  image : p '' Icc 0 1 = L
  zero : p 0 = u
  one : p 1 = v

omit [T2Space T] in
theorem exists_isParam {L : Set T} {u v : T} (h : IsLineWithEnds L u v) : ∃ p, IsParam L u v p := by
  obtain ⟨f, h0, h1⟩ := h
  let p : ℝ → T := fun s => (f (projIcc 0 1 zero_le_one s)).1
  have hc : Continuous p := continuous_subtype_val.comp (f.continuous.comp continuous_projIcc)
  refine ⟨p, hc.continuousOn, fun a ha b hb he => ?_, ?_, ?_, ?_⟩
  · have h2 := f.injective (Subtype.ext he)
    have h3 := congrArg Subtype.val h2
    rwa [projIcc_of_mem zero_le_one ha, projIcc_of_mem zero_le_one hb] at h3
  · ext y
    constructor
    · rintro ⟨s, -, rfl⟩
      exact (f _).2
    · intro hy
      refine ⟨(f.symm ⟨y, hy⟩).1, (f.symm ⟨y, hy⟩).2, ?_⟩
      simp [p, projIcc_val]
  · change (f (projIcc 0 1 zero_le_one 0)).1 = u
    rw [projIcc_left]
    exact h0
  · change (f (projIcc 0 1 zero_le_one 1)).1 = v
    rw [projIcc_right]
    exact h1

omit [T2Space T] in
theorem IsParam.symm_eq {L : Set T} {u v : T} {p : ℝ → T} (h : IsParam L u v p) {s s' : ℝ}
  (hs : s ∈ Icc (0 : ℝ) 1) (hs' : s' ∈ Icc (0 : ℝ) 1) (he : p s = p s') : s = s' := h.inj hs hs' he

omit [T2Space T] in
theorem IsParam.mem {L : Set T} {u v : T} {p : ℝ → T} (h : IsParam L u v p) {s : ℝ} (hs : s ∈ Icc
  (0 : ℝ) 1) : p s ∈ L := h.image ▸ mem_image_of_mem p hs

omit [T2Space T] in
theorem IsParam.exists_of_mem {L : Set T} {u v : T} {p : ℝ → T} (h : IsParam L u v p) {y : T}
  (hy : y ∈ L) : ∃ s ∈ Icc (0 : ℝ) 1, p s = y := by
  rw [← h.image] at hy
  exact hy

/-- The four sides of the unit square. -/
theorem frontier_unitSq : frontier unitSq = {z | z ∈ unitSq ∧ (z.re = 0 ∨ z.re = 1 ∨ z.im = 0
  ∨ z.im = 1)} := by
  have hcl : IsClosed unitSq := isClosed_Icc.reProdIm isClosed_Icc
  rw [frontier, hcl.closure_eq, unitSq, Complex.interior_reProdIm, interior_Icc]
  ext z
  constructor
  · rintro ⟨hz, h5⟩
    refine ⟨hz, ?_⟩
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hz
    by_contra hne
    push Not at hne
    obtain ⟨h6, h7, h8, h9⟩ := hne
    exact h5 ⟨⟨lt_of_le_of_ne h1 h6.symm, lt_of_le_of_ne h2 h7⟩, lt_of_le_of_ne h3 h8.symm,
      lt_of_le_of_ne h4 h9⟩
  · rintro ⟨hz, h5⟩
    refine ⟨hz, ?_⟩
    rintro ⟨⟨h6, h7⟩, h8, h9⟩
    have h6' : 0 < z.re := h6
    have h7' : z.re < 1 := h7
    have h8' : 0 < z.im := h8
    have h9' : z.im < 1 := h9
    rcases h5 with h5 | h5 | h5 | h5 <;> linarith

variable {D E R a b l l' : Set T} {x x' t t' : T}

/-- The boundary map of a cell, on the sides of the square. -/
noncomputable def cellBd (pl pr pb pt : ℝ → T) (z : ℂ) : T :=
  if z.re = 0 then pl z.im else if z.re = 1 then pr z.im else if z.im = 0 then pb z.re else pt z.re

section Bd

variable {pl pr pb pt : ℝ → T} (h : IsCell D E R a b l l' x x' t t') (hl : IsParam l x t pl)
  (hr : IsParam l' x' t' pr) (hb : IsParam a x x' pb) (ht : IsParam b t t' pt)

include hb ht hl hr

omit [TopologicalSpace T] [T2Space T] hl hr hb ht in
theorem cellBd_left {z : ℂ} (hz : z.re = 0) : cellBd pl pr pb pt z = pl z.im := ite_eq_left hz

omit [TopologicalSpace T] [T2Space T] hl hr hb ht in
theorem cellBd_right {z : ℂ} (hz : z.re = 1) : cellBd pl pr pb pt z = pr z.im := by
  simp [cellBd, hz]

omit [T2Space T] ht in
theorem cellBd_low {z : ℂ} (hz : z.im = 0) : cellBd pl pr pb pt z = pb z.re := by
  by_cases h0 : z.re = 0
  · rw [cellBd, ite_eq_left h0, hz, h0, hl.zero, hb.zero]
  · by_cases h1 : z.re = 1
    · rw [cellBd, ite_eq_right h0, ite_eq_left h1, hz, h1, hr.zero, hb.one]
    · simp [cellBd, h0, h1, hz]

omit [T2Space T] hb in
theorem cellBd_high {z : ℂ} (hz : z.im = 1) : cellBd pl pr pb pt z = pt z.re := by
  by_cases h0 : z.re = 0
  · rw [cellBd, ite_eq_left h0, hz, h0, hl.one, ht.zero]
  · by_cases h1 : z.re = 1
    · rw [cellBd, ite_eq_right h0, ite_eq_left h1, hz, h1, hr.one, ht.one]
    · simp [cellBd, h0, h1, hz]

omit [T2Space T] in
theorem continuousOn_cellBd : ContinuousOn (cellBd pl pr pb pt) (frontier unitSq) := by
  have hs : frontier unitSq = ({z | z ∈ unitSq ∧ z.re = 0} ∪ {z | z ∈ unitSq ∧ z.re = 1}) ∪
    ({z | z ∈ unitSq ∧ z.im = 0} ∪ {z | z ∈ unitSq ∧ z.im = 1}) := by
    rw [frontier_unitSq]
    ext z
    simp only [mem_ofPred_eq, mem_union]
    tauto
  have hcl : IsClosed unitSq := isClosed_Icc.reProdIm isClosed_Icc
  have hc : ∀ {g : ℂ → ℝ}, Continuous g → ∀ c : ℝ, IsClosed {z | z ∈ unitSq ∧ g z = c} := fun hg c
    => hcl.inter (isClosed_eq hg continuous_const)
  have him {A : Set ℂ} (hA : A ⊆ unitSq) : MapsTo Complex.im A (Icc 0 1) :=
    fun _ hz => (hA hz).2
  have hre {A : Set ℂ} (hA : A ⊆ unitSq) : MapsTo Complex.re A (Icc 0 1) :=
    fun _ hz => (hA hz).1
  have h1 : ContinuousOn (cellBd pl pr pb pt) {z | z ∈ unitSq ∧ z.re = 0} :=
    (hl.cont.comp Complex.continuous_im.continuousOn
      (him (A := {z | z ∈ unitSq ∧ z.re = 0}) fun _ hz => hz.1)).congr fun _ hz =>
        cellBd_left hz.2
  have h2 : ContinuousOn (cellBd pl pr pb pt) {z | z ∈ unitSq ∧ z.re = 1} :=
    (hr.cont.comp Complex.continuous_im.continuousOn
      (him (A := {z | z ∈ unitSq ∧ z.re = 1}) fun _ hz => hz.1)).congr fun _ hz =>
        cellBd_right hz.2
  have h3 : ContinuousOn (cellBd pl pr pb pt) {z | z ∈ unitSq ∧ z.im = 0} :=
    (hb.cont.comp Complex.continuous_re.continuousOn
      (hre (A := {z | z ∈ unitSq ∧ z.im = 0}) fun _ hz => hz.1)).congr fun _ hz =>
        cellBd_low (pt := pt) hl hr hb hz.2
  have h4 : ContinuousOn (cellBd pl pr pb pt) {z | z ∈ unitSq ∧ z.im = 1} :=
    (ht.cont.comp Complex.continuous_re.continuousOn
      (hre (A := {z | z ∈ unitSq ∧ z.im = 1}) fun _ hz => hz.1)).congr fun _ hz =>
        cellBd_high (pb := pb) hl hr ht hz.2
  rw [hs]
  exact (h1.union_of_isClosed h2 (hc Complex.continuous_re 0) (hc Complex.continuous_re
    1)).union_of_isClosed (h3.union_of_isClosed h4 (hc Complex.continuous_im 0)
      (hc Complex.continuous_im 1)) ((hc Complex.continuous_re 0).union
        (hc Complex.continuous_re 1)) ((hc Complex.continuous_im 0).union
          (hc Complex.continuous_im 1))

include h

omit [T2Space T] in
theorem cellBd_sides {z z' : ℂ} (hz : z ∈ frontier unitSq) (hz' : z' ∈ frontier unitSq)
  (he : cellBd pl pr pb pt z = cellBd pl pr pb pt z') : z = z' := by
  rw [frontier_unitSq] at hz hz'
  obtain ⟨⟨hzr, hzi⟩, hs⟩ := hz
  obtain ⟨⟨hzr', hzi'⟩, hs'⟩ := hz'
  have hL := cellBd_left (pl := pl) (pr := pr) (pb := pb) (pt := pt) (z := z)
  have hL' := cellBd_left (pl := pl) (pr := pr) (pb := pb) (pt := pt) (z := z')
  have hR (hz : z.re = 1) : cellBd pl pr pb pt z = pr z.im := cellBd_right hz
  have hR' (hz' : z'.re = 1) : cellBd pl pr pb pt z' = pr z'.im := cellBd_right hz'
  have hB := cellBd_low (pt := pt) hl hr hb (z := z)
  have hB' := cellBd_low (pt := pt) hl hr hb (z := z')
  have hT := cellBd_high (pb := pb) hl hr ht (z := z)
  have hT' := cellBd_high (pb := pb) hl hr ht (z := z')
  have hmeet : ∀ {A B : Set T} {c : T}, A ∩ B = {c} → ∀ {w}, w ∈ A → w ∈ B → w = c
    := fun {A B c} h1 {w} h2 h3 => by
    have h4 : w ∈ A ∩ B := ⟨h2, h3⟩
    rwa [h1] at h4
  have hlr : ∀ {w}, w ∈ l → w ∈ l' → False := fun {w} h1 h2 => disjoint_left.mp h.ll h1 h2
  have hab : ∀ {w}, w ∈ a → w ∈ b → False := fun {w} h1 h2 => disjoint_left.mp h.ab h1 h2
  have hzero : ∀ {P : Set T} {u v : T} {p : ℝ → T}, IsParam P u v p → ∀ {s}, s ∈ Icc (0 : ℝ) 1
    → p s = u → s = 0 := fun {P u v p} hp {s} hs h1 => hp.inj hs ⟨le_rfl, zero_le_one⟩
      (h1.trans hp.zero.symm)
  have hone : ∀ {P : Set T} {u v : T} {p : ℝ → T}, IsParam P u v p → ∀ {s}, s ∈ Icc (0 : ℝ) 1 → p s
    = v → s = 1 := fun {P u v p} hp {s} hs h1 => hp.inj hs ⟨zero_le_one, le_rfl⟩
      (h1.trans hp.one.symm)
  rcases hs with hs | hs | hs | hs <;> rcases hs' with hs' | hs' | hs' | hs'
  · rw [hL hs, hL' hs'] at he
    exact Complex.ext (hs.trans hs'.symm) (hl.inj hzi hzi' he)
  · rw [hL hs, hR' hs'] at he
    exact (hlr (hl.mem hzi) (he ▸ hr.mem hzi')).elim
  · rw [hL hs, hB' hs'] at he
    have h1 := hmeet h.al (hb.mem hzr') (he ▸ hl.mem hzi)
    exact Complex.ext (hs.trans (hzero hb hzr' h1).symm) ((hzero hl hzi
      (he.trans h1)).trans hs'.symm)
  · rw [hL hs, hT' hs'] at he
    have h1 := hmeet h.bl (ht.mem hzr') (he ▸ hl.mem hzi)
    exact Complex.ext (hs.trans (hzero ht hzr' h1).symm) ((hone hl hzi
      (he.trans h1)).trans hs'.symm)
  · rw [hR hs, hL' hs'] at he
    exact (hlr (hl.mem hzi') (he ▸ hr.mem hzi)).elim
  · rw [hR hs, hR' hs'] at he
    exact Complex.ext (hs.trans hs'.symm) (hr.inj hzi hzi' he)
  · rw [hR hs, hB' hs'] at he
    have h1 := hmeet h.ar (hb.mem hzr') (he ▸ hr.mem hzi)
    exact Complex.ext (hs.trans (hone hb hzr' h1).symm) ((hzero hr hzi
      (he.trans h1)).trans hs'.symm)
  · rw [hR hs, hT' hs'] at he
    have h1 := hmeet h.br (ht.mem hzr') (he ▸ hr.mem hzi)
    exact Complex.ext (hs.trans (hone ht hzr' h1).symm) ((hone hr hzi (he.trans h1)).trans hs'.symm)
  · rw [hB hs, hL' hs'] at he
    have h1 := hmeet h.al (hb.mem hzr) (he.symm ▸ hl.mem hzi')
    exact Complex.ext ((hzero hb hzr h1).trans hs'.symm) (hs.trans (hzero hl hzi'
      (he.symm.trans h1)).symm)
  · rw [hB hs, hR' hs'] at he
    have h1 := hmeet h.ar (hb.mem hzr) (he.symm ▸ hr.mem hzi')
    exact Complex.ext ((hone hb hzr h1).trans hs'.symm) (hs.trans (hzero hr hzi'
      (he.symm.trans h1)).symm)
  · rw [hB hs, hB' hs'] at he
    exact Complex.ext (hb.inj hzr hzr' he) (hs.trans hs'.symm)
  · rw [hB hs, hT' hs'] at he
    exact (hab (hb.mem hzr) (he.symm ▸ ht.mem hzr')).elim
  · rw [hT hs, hL' hs'] at he
    have h1 := hmeet h.bl (ht.mem hzr) (he.symm ▸ hl.mem hzi')
    exact Complex.ext ((hzero ht hzr h1).trans hs'.symm) (hs.trans (hone hl hzi'
      (he.symm.trans h1)).symm)
  · rw [hT hs, hR' hs'] at he
    have h1 := hmeet h.br (ht.mem hzr) (he.symm ▸ hr.mem hzi')
    exact Complex.ext ((hone ht hzr h1).trans hs'.symm) (hs.trans (hone hr hzi'
      (he.symm.trans h1)).symm)
  · rw [hT hs, hB' hs'] at he
    exact (hab (hb.mem hzr') (he ▸ ht.mem hzr)).elim
  · rw [hT hs, hT' hs'] at he
    exact Complex.ext (ht.inj hzr hzr' he) (hs.trans hs'.symm)

omit [T2Space T] in
theorem cellBd_image : cellBd pl pr pb pt '' frontier unitSq = discBd R := by
  have hIm : ∀ {P : Set T} {u v : T} {p : ℝ → T}, IsParam P u v p → ∀ y ∈ P, ∃ s ∈ Icc
    (0 : ℝ) 1, p s = y := fun hp y hy => hp.exists_of_mem hy
  have hmemz : ∀ {m w : ℝ}, m ∈ Icc (0 : ℝ) 1 → w ∈ Icc (0 : ℝ) 1 → (⟨m, w⟩ : ℂ) ∈ unitSq
    := fun h1 h2 => ⟨h1, h2⟩
  rw [h.bd_eq, frontier_unitSq]
  ext y
  constructor
  · rintro ⟨z, ⟨⟨hzr, hzi⟩, hs⟩, rfl⟩
    rcases hs with hs | hs | hs | hs
    · rw [cellBd_left hs]
      exact .inr (hl.mem hzi)
    · rw [cellBd_right hs]
      exact .inl (.inl (.inr (hr.mem hzi)))
    · rw [cellBd_low (pt := pt) hl hr hb hs]
      exact .inl (.inl (.inl (hb.mem hzr)))
    · rw [cellBd_high (pb := pb) hl hr ht hs]
      exact .inl (.inr (ht.mem hzr))
  · rintro (((hy | hy) | hy) | hy)
    · obtain ⟨s, hs, rfl⟩ := hIm hb y hy
      exact ⟨⟨s, 0⟩, ⟨hmemz hs ⟨le_rfl, zero_le_one⟩, .inr (.inr (.inl rfl))⟩,
        cellBd_low (pt := pt) hl hr hb rfl⟩
    · obtain ⟨s, hs, rfl⟩ := hIm hr y hy
      exact ⟨⟨1, s⟩, ⟨hmemz ⟨zero_le_one, le_rfl⟩ hs, .inr (.inl rfl)⟩,
        cellBd_right rfl⟩
    · obtain ⟨s, hs, rfl⟩ := hIm ht y hy
      exact ⟨⟨s, 1⟩, ⟨hmemz hs ⟨zero_le_one, le_rfl⟩, .inr (.inr (.inr rfl))⟩,
        cellBd_high (pb := pb) hl hr ht rfl⟩
    · obtain ⟨s, hs, rfl⟩ := hIm hl y hy
      exact ⟨⟨0, s⟩, ⟨hmemz ⟨le_rfl, zero_le_one⟩ hs, .inl rfl⟩, cellBd_left rfl⟩

omit [T2Space T] in
/-- **The chart of a cell.** -/
theorem exists_cell_chart : ∃ ξ : ℂ → T, ContinuousOn ξ unitSq ∧ InjOn ξ unitSq ∧ ξ '' unitSq = R
  ∧ ∀ z ∈ frontier unitSq, ξ z = cellBd pl pr pb pt z := by
  classical
  obtain ⟨hU, hUb⟩ := unitSq_disc
  obtain ⟨e⟩ := hU.isOArc_discBd
  obtain ⟨h₀, g₀, c₀, hg₀⟩ := exists_chart_extending hU e
  obtain ⟨hR, gR, cR⟩ := h.disc.exists_isChart
  have hfr : ∀ w : Circle, (e w).1 ∈ frontier unitSq := fun w => hUb ▸ (e w).2
  have hβR : ∀ z ∈ frontier unitSq, cellBd pl pr pb pt z ∈ discBd R := fun z hz
    => cellBd_image h hl hr hb ht ▸ mem_image_of_mem _ hz
  have hsubR := Surface.discBd_subset R
  let ψ : Circle → ℂ := fun w => hR (cellBd pl pr pb pt (e w).1)
  have hψc : Continuous ψ := by
    have h1 : Continuous fun w : Circle => cellBd pl pr pb pt (e w).1 :=
      (continuousOn_cellBd hl hr hb ht).comp_continuous (continuous_subtype_val.comp e.continuous)
        hfr
    exact cR.hc.comp_continuous h1 fun w => hsubR (hβR _ (hfr w))
  have hψi : Injective ψ := fun w w' he => by
    have h1 := cR.gh (hsubR (hβR _ (hfr w)))
    have h2 := cR.gh (hsubR (hβR _ (hfr w')))
    have h3 : cellBd pl pr pb pt (e w).1 = cellBd pl pr pb pt (e w').1 := by
      rw [← h1, ← h2]
      exact congrArg gR he
    exact e.injective (Subtype.ext (cellBd_sides h hl hr hb ht (hfr w) (hfr w') h3))
  obtain ⟨hB, hBb⟩ := closedBall_disc (s := 1) one_pos
  have hψr : range ψ = discBd (closedBall (0 : ℂ) 1) := by
    rw [hBb, ← cR.bd]
    ext y
    constructor
    · rintro ⟨w, rfl⟩
      exact mem_image_of_mem hR (hβR _ (hfr w))
    · rintro ⟨r, hr', rfl⟩
      rw [← cellBd_image h hl hr hb ht] at hr'
      obtain ⟨z, hz, rfl⟩ := hr'
      refine ⟨e.symm ⟨z, hUb ▸ hz⟩, ?_⟩
      simp [ψ]
  let φ : Circle ≃ₜ discBd (closedBall (0 : ℂ) 1) := ((hψc.isClosedEmbedding
    hψi).isEmbedding.toHomeomorph).trans (Homeomorph.setCongr hψr)
  have hφ : ∀ w, (φ w).1 = ψ w := fun w => rfl
  obtain ⟨h₁, g₁, c₁, hg₁⟩ := exists_chart_extending hB φ
  refine ⟨fun z => gR (g₁ (h₀ z)), ?_, ?_, ?_, ?_⟩
  · exact cR.gc.comp (c₁.gc.comp c₀.hc c₀.hm) fun z hz => c₁.gm (c₀.hm hz)
  · intro z hz z' hz' he
    have h1 := c₁.hg (c₀.hm hz)
    have h2 := c₁.hg (c₀.hm hz')
    have h3 := cR.hg (c₁.gm (c₀.hm hz))
    have h4 := cR.hg (c₁.gm (c₀.hm hz'))
    have h5 : g₁ (h₀ z) = g₁ (h₀ z') := by
      rw [← h3, ← h4]
      exact congrArg hR he
    have h6 : h₀ z = h₀ z' := by
      rw [← h1, ← h2]
      exact congrArg h₁ h5
    rw [← c₀.gh hz, ← c₀.gh hz', h6]
  · ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact cR.gm (c₁.gm (c₀.hm hz))
    · intro hy
      have h1 := cR.hm hy
      have h2 := c₁.hm h1
      refine ⟨g₀ (h₁ (hR y)), c₀.gm h2, ?_⟩
      simp only
      rw [c₀.hg h2, c₁.gh h1, cR.gh hy]
  · intro z hz
    obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, Circle.exp θ = e.symm ⟨z, hUb ▸ hz⟩ := Circle.exp_surjective _
    have hzw : z = (e (Circle.exp θ)).1 := by
      rw [hθ]
      simp
    have hmem : eC θ ∈ closedBall (0 : ℂ) 1 := by
      rw [eC_eq_cis', mem_closedBall_zero_iff]
      simp [cis']
    have h1 : h₀ z = eC θ := by
      rw [hzw, ← hg₀ θ, c₀.hg hmem]
    simp only
    rw [h1, hg₁ θ, hφ]
    change gR (hR (cellBd pl pr pb pt (e (Circle.exp θ)).1)) = _
    rw [cR.gh (hsubR (hβR _ (hfr _))), ← hzw]

end Bd

end GraphMinor.GM07
