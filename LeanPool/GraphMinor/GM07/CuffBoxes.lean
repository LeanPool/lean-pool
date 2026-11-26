/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.CuffMenger

/-!
# Boxes around the cuffs

Graph Minors VII, (5.9), page 235: the move from `G` to `G'`. We cut the part of the surface near
the cuffs into boxes `[0,1] × [0,2]`, with the cuff at level `0`.
Two boxes meet only along their vertical sides. A map of each box into itself that fixes the top,
and that agrees on the sides, gives a map of the surface. It is homotopic to the identity by the
straight line homotopy in each box.
-/

@[expose] public section

namespace GraphMinor.GM07

open Set Topology Function GraphMinor.Surface GraphMinor.GM11

universe u

/-- The box `[0,1] × [0,2]`. -/
def cuffBox : Set (ℝ × ℝ) := Icc 0 1 ×ˢ Icc 0 2

/-- The straight line from `p` to `q` in the plane. -/
def boxLine (τ : ℝ) (p q : ℝ × ℝ) : ℝ × ℝ := ((1 - τ) * p.1 + τ * q.1, (1 - τ) * p.2 + τ * q.2)

theorem isCompact_cuffBox : IsCompact cuffBox := isCompact_Icc.prod isCompact_Icc

theorem boxLine_self (τ : ℝ) (p : ℝ × ℝ) : boxLine τ p p = p :=
  Prod.ext (by simp only [boxLine]; ring) (by simp only [boxLine]; ring)

theorem boxLine_zero (p q : ℝ × ℝ) : boxLine 0 p q = p :=
  Prod.ext (by simp only [boxLine]; ring) (by simp only [boxLine]; ring)

theorem boxLine_one (p q : ℝ × ℝ) : boxLine 1 p q = q :=
  Prod.ext (by simp only [boxLine]; ring) (by simp only [boxLine]; ring)

theorem boxLine_mem {τ : ℝ} (h0 : 0 ≤ τ) (h1 : τ ≤ 1) {p q : ℝ × ℝ} (hp : p ∈ cuffBox)
  (hq : q ∈ cuffBox) : boxLine τ p q ∈ cuffBox := by
  obtain ⟨⟨h2, h3⟩, h4, h5⟩ := hp
  obtain ⟨⟨h6, h7⟩, h8, h9⟩ := hq
  have h10 : 0 ≤ 1 - τ := by linarith
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> simp only [boxLine] <;> nlinarith

variable {S : Type u} [TopologicalSpace S] {ι : Type*}

/-- Boxes in the surface. They are one to one, they meet only along vertical sides, and the part
below the top is open in the surface. -/
structure IsBoxSystem (φ : ι → ℝ × ℝ → S) : Prop where
  cont : ∀ i, ContinuousOn (φ i) cuffBox
  inj : ∀ i, InjOn (φ i) cuffBox
  meet : ∀ i i' p p', p ∈ cuffBox → p' ∈ cuffBox → φ i p = φ i' p' → (i = i' ∧ p = p') ∨ (p.2
    = p'.2 ∧ (p.1 = 0 ∨ p.1 = 1) ∧ (p'.1 = 0 ∨ p'.1 = 1) ∧ ∀ w ∈ Icc (0 : ℝ) 2, φ i (p.1, w) = φ i'
      (p'.1, w))
  isOpen : IsOpen (⋃ i, φ i '' {p ∈ cuffBox | p.2 < 2})

/-- A map of each box into itself, which fixes the top, and which on the sides only changes the
level by `ℓ`. -/
structure IsBoxMap (r : ι → ℝ × ℝ → ℝ × ℝ) (ℓ : ℝ → ℝ) : Prop where
  cont : ∀ i, ContinuousOn (r i) cuffBox
  maps : ∀ i, MapsTo (r i) cuffBox cuffBox
  top : ∀ i p, p ∈ cuffBox → p.2 = 2 → r i p = p
  side : ∀ i m w, (m = 0 ∨ m = 1) → w ∈ Icc (0 : ℝ) 2 → r i (m, w) = (m, ℓ w)

variable {φ : ι → ℝ × ℝ → S} {r : ι → ℝ × ℝ → ℝ × ℝ} {ℓ : ℝ → ℝ}

/-- The value of the homotopy does not depend on the box. -/
theorem IsBoxSystem.well_defined (h : IsBoxSystem φ) (hr : IsBoxMap r ℓ) {i i' : ι} {p p' : ℝ × ℝ}
  (hp : p ∈ cuffBox) (hp' : p' ∈ cuffBox) (he : φ i p = φ i' p') (τ : ℝ) (h0 : 0 ≤ τ) (h1 : τ
    ≤ 1) : φ i (boxLine τ p (r i p)) = φ i' (boxLine τ p' (r i' p')) := by
  rcases h.meet i i' p p' hp hp' he with ⟨rfl, rfl⟩ | ⟨hw, hm, hm', hf⟩
  · rfl
  · have h2 : r i p = (p.1, ℓ p.2) := hr.side i p.1 p.2 hm hp.2
    have h3 : r i' p' = (p'.1, ℓ p'.2) := hr.side i' p'.1 p'.2 hm' hp'.2
    have h4 : ∀ m : ℝ, ((1 - τ) * m + τ * m) = m := fun m => by ring
    have h5 : (p.1, ℓ p.2) ∈ cuffBox := h2 ▸ hr.maps i hp
    have hq : (1 - τ) * p.2 + τ * ℓ p.2 ∈ Icc (0 : ℝ) 2 := (boxLine_mem h0 h1 hp h5).2
    rw [h2, h3]
    simp only [boxLine, h4]
    rw [← hw]
    exact hf _ hq

/-- **The homotopy of a box map.** -/
theorem IsBoxSystem.exists_homotopy [Finite ι] [T2Space S] (h : IsBoxSystem φ) (hr : IsBoxMap r ℓ) :
    ∃ Ψ : unitInterval × S → S, Continuous Ψ ∧ (∀ x, Ψ (0, x) = x) ∧ (∀ i p τ, p ∈ cuffBox → Ψ
      (τ, φ i p) = φ i (boxLine τ p (r i p))) ∧ ∀ x τ, (∀ i, x ∉ φ i '' cuffBox) → Ψ (τ, x) = x
        := by
  classical
  have hnU : ∀ i, IsCompact (φ i '' cuffBox) := fun i => isCompact_cuffBox.image_of_continuousOn
    (h.cont i)
  obtain ⟨θ, hθ⟩ : ∃ θ : ι → S → ℝ × ℝ, ∀ i, ContinuousOn (θ i) (φ i '' cuffBox) ∧ LeftInvOn (θ i)
    (φ i) cuffBox := by
    by_cases hne : Nonempty (ℝ × ℝ)
    · have := fun i => Surface.exists_inv_of_compactOn isCompact_cuffBox (h.cont i) (h.inj i)
      choose θ hθ₁ hθ₂ using this
      exact ⟨θ, fun i => ⟨hθ₁ i, hθ₂ i⟩⟩
    · exact absurd ⟨(0, 0)⟩ hne
  let Ψ : unitInterval × S → S := fun q => if hx : ∃ i, q.2 ∈ φ i '' cuffBox then φ hx.choose
    (boxLine q.1 (θ hx.choose q.2) (r hx.choose (θ hx.choose q.2))) else q.2
  have hval : ∀ i p (τ : unitInterval), p ∈ cuffBox → Ψ (τ, φ i p) = φ i (boxLine τ p (r i p))
    := fun i p τ hp => by
    have hx : ∃ i', φ i p ∈ φ i' '' cuffBox := ⟨i, mem_image_of_mem _ hp⟩
    simp only [Ψ, dite_eq_left hx]
    have hs := hx.choose_spec
    generalize hx.choose = i₀ at hs ⊢
    obtain ⟨p', hp', he⟩ := hs
    rw [← he, (hθ _).2 hp']
    exact h.well_defined hr hp' hp he τ τ.2.1 τ.2.2
  have hoff : ∀ x τ, (∀ i, x ∉ φ i '' cuffBox) → Ψ (τ, x) = x := fun x τ hx => by
    have : ¬ ∃ i, x ∈ φ i '' cuffBox := by
      push Not
      exact hx
    simp only [Ψ, dite_eq_right this]
  let O : Set S := ⋃ i, φ i '' {p ∈ cuffBox | p.2 < 2}
  have hcov : ∀ i : Option ι, IsClosed (match i with
    | some i => (univ : Set unitInterval) ×ˢ (φ i '' cuffBox)
    | none => univ ×ˢ Oᶜ) := fun i => by
    rcases i with _ | i
    · exact isClosed_univ.prod h.isOpen.isClosed_compl
    · exact isClosed_univ.prod (hnU i).isClosed
  have hcont : Continuous Ψ := by
    refine LocallyFinite.continuous (locallyFinite_of_finite _) ?_ hcov ?_
    · ext q
      simp only [mem_iUnion, mem_univ, iff_true]
      by_cases hq : q.2 ∈ O
      · obtain ⟨i, p, hp, he⟩ := mem_iUnion.mp hq
        exact ⟨some i, mem_univ _, p, hp.1, he⟩
      · exact ⟨none, mem_univ _, hq⟩
    · rintro (_ | i)
      · refine continuous_snd.continuousOn.congr fun q hq => ?_
        by_cases hx : ∃ i, q.2 ∈ φ i '' cuffBox
        · obtain ⟨i, p, hp, he⟩ := hx
          have h2 : p.2 = 2 := by
            by_contra hne
            exact hq.2 (mem_iUnion.mpr ⟨i, p, ⟨hp, lt_of_le_of_ne hp.2.2 hne⟩, he⟩)
          obtain ⟨τ, x⟩ := q
          simp only at he
          subst he
          rw [hval i p τ hp, hr.top i p hp h2, boxLine_self]
        · push Not at hx
          exact hoff q.2 q.1 hx
      · have hg : ContinuousOn (fun q : unitInterval × S => φ i (boxLine q.1 (θ i q.2) (r i
          (θ i q.2)))) (univ ×ˢ (φ i '' cuffBox)) := by
          have hθm : ∀ x ∈ φ i '' cuffBox, θ i x ∈ cuffBox := by
            rintro _ ⟨p, hp, rfl⟩
            rw [(hθ i).2 hp]
            exact hp
          have h2 : ContinuousOn (fun q : unitInterval × S => θ i q.2) (univ ×ˢ (φ i '' cuffBox))
            := (hθ i).1.comp continuousOn_snd fun q hq => hq.2
          have h3 : ContinuousOn (fun q : unitInterval × S => r i (θ i q.2)) (univ ×ˢ
            (φ i '' cuffBox)) := (hr.cont i).comp h2 fun q hq => hθm _ hq.2
          refine (h.cont i).comp ?_ fun q hq => boxLine_mem q.1.2.1 q.1.2.2 (hθm _ hq.2) (hr.maps i
            (hθm _ hq.2))
          have hτ : ContinuousOn (fun q : unitInterval × S => (q.1 : ℝ)) (univ ×ˢ (φ i '' cuffBox))
            := (continuous_subtype_val.comp continuous_fst).continuousOn
          simp only [boxLine]
          exact ((continuousOn_const.sub hτ).mul h2.fst |>.add (hτ.mul h3.fst)).prodMk
            ((continuousOn_const.sub hτ).mul h2.snd |>.add (hτ.mul h3.snd))
        refine hg.congr fun q hq => ?_
        obtain ⟨τ, x⟩ := q
        obtain ⟨p, hp, rfl⟩ := hq.2
        simp only
        rw [hval i p τ hp, (hθ i).2 hp]
  refine ⟨Ψ, hcont, fun x => ?_, fun i p τ hp => hval i p τ hp, hoff⟩
  by_cases hx : ∃ i, x ∈ φ i '' cuffBox
  · obtain ⟨i, p, hp, rfl⟩ := hx
    rw [hval i p 0 hp]
    simp [boxLine_zero]
  · push Not at hx
    exact hoff x 0 hx

/-- The fraction of the way from the graph of `f` to the top of the box. -/
noncomputable def boxLevel (f : ℝ → ℝ) (p : ℝ × ℝ) : ℝ := max 0 ((p.2 - f p.1) / (2 - f p.1))

/-- The map of a box: everything under the graph of `f` goes to the bottom, by `g`, and the part
above the graph of `f` is stretched over the box. The map `g` of the bottom fades out towards the
top. -/
noncomputable def boxCollapse (g f : ℝ → ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (boxLevel f p * p.1 + (1 - boxLevel f p) * g p.1, 2 * boxLevel f p)

/-- The conditions on the functions `g` and `f` of a box. -/
structure IsCollapseData (g f : ℝ → ℝ) : Prop where
  gcont : ContinuousOn g (Icc 0 1)
  fcont : ContinuousOn f (Icc 0 1)
  gmono : MonotoneOn g (Icc 0 1)
  g0 : g 0 = 0
  g1 : g 1 = 1
  f1 : ∀ m ∈ Icc (0 : ℝ) 1, 1 ≤ f m ∧ f m ≤ 3 / 2
  f0 : f 0 = 1
  f1' : f 1 = 1

section Collapse

variable {g f : ℝ → ℝ}

theorem IsCollapseData.gmem (h : IsCollapseData g f) {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1) : g m ∈ Icc
  (0 : ℝ) 1 :=
  ⟨h.g0 ▸ h.gmono ⟨le_rfl, zero_le_one⟩ hm hm.1, h.g1 ▸ h.gmono hm ⟨zero_le_one, le_rfl⟩ hm.2⟩

theorem IsCollapseData.level_mem (h : IsCollapseData g f) {p : ℝ × ℝ}
  (hp : p ∈ cuffBox) : boxLevel f p ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨h1, h2⟩ := h.f1 p.1 hp.1
  have h3 : 0 < 2 - f p.1 := by linarith
  refine ⟨le_max_left _ _, max_le zero_le_one ?_⟩
  rw [div_le_one h3]
  linarith [hp.2.2]

theorem boxLevel_eq_zero (h : IsCollapseData g f) {p : ℝ × ℝ} (hp : p ∈ cuffBox) : boxLevel f p
  = 0 ↔ p.2 ≤ f p.1 := by
  obtain ⟨h1, h2⟩ := h.f1 p.1 hp.1
  have h3 : 0 < 2 - f p.1 := by linarith
  simp only [boxLevel]
  rw [max_eq_left_iff, div_le_iff₀ h3]
  constructor <;> intro h4 <;> linarith

theorem boxLevel_of_lt (h : IsCollapseData g f) {p : ℝ × ℝ} (hp : p ∈ cuffBox) (hlt : f p.1
  ≤ p.2) : boxLevel f p = (p.2 - f p.1) / (2 - f p.1) := by
  obtain ⟨h1, h2⟩ := h.f1 p.1 hp.1
  have h3 : 0 < 2 - f p.1 := by linarith
  exact max_eq_right (div_nonneg (by linarith) h3.le)

theorem continuousOn_boxLevel (h : IsCollapseData g f) : ContinuousOn (boxLevel f) cuffBox := by
  have h1 : ContinuousOn (fun p : ℝ × ℝ => f p.1) cuffBox := h.fcont.comp continuousOn_fst fun p hp
    => hp.1
  have h2 : ContinuousOn (fun p : ℝ × ℝ => (p.2 - f p.1) / (2 - f p.1)) cuffBox :=
    (continuousOn_snd.sub h1).div (continuousOn_const.sub h1) fun p hp => by
    have := (h.f1 p.1 hp.1).2
    linarith
  exact continuous_max.comp_continuousOn (continuousOn_const.prodMk h2)

theorem continuousOn_boxCollapse (h : IsCollapseData g f) : ContinuousOn (boxCollapse g f) cuffBox
  := by
  have h1 := continuousOn_boxLevel h
  have h2 : ContinuousOn (fun p : ℝ × ℝ => g p.1) cuffBox := h.gcont.comp continuousOn_fst fun p hp
    => hp.1
  exact (h1.mul continuousOn_fst |>.add ((continuousOn_const.sub h1).mul h2)).prodMk
    (continuousOn_const.mul h1)

theorem boxCollapse_mem (h : IsCollapseData g f) {p : ℝ × ℝ} (hp : p ∈ cuffBox) : boxCollapse g f p
  ∈ cuffBox := by
  obtain ⟨h1, h2⟩ := h.level_mem hp
  obtain ⟨h3, h4⟩ := h.gmem hp.1
  obtain ⟨h5, h6⟩ := hp.1
  have h7 : 0 ≤ 1 - boxLevel f p := by linarith
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> simp only [boxCollapse] <;> nlinarith

theorem boxCollapse_top (h : IsCollapseData g f) {p : ℝ × ℝ} (hp : p ∈ cuffBox) (h2 : p.2
  = 2) : boxCollapse g f p = p := by
  obtain ⟨h3, h4⟩ := h.f1 p.1 hp.1
  have h5 : boxLevel f p = 1 := by
    rw [boxLevel_of_lt h hp (by linarith), h2]
    exact div_self (by linarith)
  refine Prod.ext ?_ ?_ <;> simp only [boxCollapse, h5, h2] <;> ring

/-- The level on the sides of a box. -/
noncomputable def sideLevel (w : ℝ) : ℝ := 2 * max 0 (w - 1)

theorem boxCollapse_side (h : IsCollapseData g f) {m w : ℝ} (hm : m = 0 ∨ m = 1) : boxCollapse g f
  (m, w) = (m, sideLevel w) := by
  have hf : f m = 1 := by
    rcases hm with rfl | rfl
    · exact h.f0
    · exact h.f1'
  have hg : g m = m := by
    rcases hm with rfl | rfl
    · exact h.g0
    · exact h.g1
  refine Prod.ext ?_ ?_
  · simp only [boxCollapse, hg]
    ring
  · simp only [boxCollapse, boxLevel, sideLevel, hf]
    norm_num

/-- Above the graph of `f`, the map of the box is one to one. -/
theorem boxCollapse_inj (h : IsCollapseData g f) {p q : ℝ × ℝ} (hp : p ∈ cuffBox)
  (hq : q ∈ cuffBox) (hpf : f p.1 < p.2) (hqf : f q.1 < q.2) (he : boxCollapse g f p
    = boxCollapse g f q) : p = q := by
  have h1 : boxLevel f p = boxLevel f q := by
    have := congrArg Prod.snd he
    simp only [boxCollapse] at this
    linarith
  have hl : 0 < boxLevel f p := lt_of_le_of_ne (h.level_mem hp).1 fun h2 => absurd
    ((boxLevel_eq_zero h hp).mp h2.symm) (not_le.mpr hpf)
  have hl1 := (h.level_mem hp).2
  have h2 : p.1 = q.1 := by
    have h3 := congrArg Prod.fst he
    simp only [boxCollapse, ← h1] at h3
    by_contra hne
    rcases lt_or_gt_of_ne hne with h4 | h4
    · have h5 := h.gmono hp.1 hq.1 h4.le
      nlinarith
    · have h5 := h.gmono hq.1 hp.1 h4.le
      nlinarith
  have hfe : f p.1 = f q.1 := by rw [h2]
  obtain ⟨h3, h4⟩ := h.f1 p.1 hp.1
  have h5 : 0 < 2 - f p.1 := by linarith
  have h6 := boxLevel_of_lt h hp hpf.le
  have h7 := boxLevel_of_lt h hq hqf.le
  rw [h1, h7, ← hfe] at h6
  have h8 : q.2 - f p.1 = p.2 - f p.1 := by
    rwa [div_left_inj₀ h5.ne'] at h6
  exact Prod.ext h2 (by linarith)

/-- Each point of the box above the bottom comes from above the graph of `f`. -/
theorem boxCollapse_surj (h : IsCollapseData g f) {q : ℝ × ℝ} (hq : q ∈ cuffBox)
  (h0 : 0 < q.2) : ∃ p ∈ cuffBox, f p.1 < p.2 ∧ boxCollapse g f p = q := by
  set l := q.2 / 2 with hl
  have hl0 : 0 < l := by positivity
  have hl1 : l ≤ 1 := by
    have := hq.2.2
    rw [hl]
    linarith
  let G : ℝ → ℝ := fun m => l * m + (1 - l) * g m
  have hGc : ContinuousOn G (Icc 0 1) := (continuousOn_const.mul continuousOn_id).add
    (continuousOn_const.mul h.gcont)
  have hG0 : G 0 = 0 := by simp [G, h.g0]
  have hG1 : G 1 = 1 := by simp only [G, h.g1]; ring
  have hsub : Icc (G 0) (G 1) ⊆ G '' Icc 0 1 := intermediate_value_Icc zero_le_one hGc
  obtain ⟨m, hm, hmq⟩ := hsub (by rw [hG0, hG1]; exact hq.1)
  obtain ⟨h3, h4⟩ := h.f1 m hm
  have h5 : 0 < 2 - f m := by linarith
  let w := f m + l * (2 - f m)
  have hw : w ∈ Icc (0 : ℝ) 2 := by
    simp only [w]
    constructor <;> nlinarith
  have hp : (m, w) ∈ cuffBox := ⟨hm, hw⟩
  have hgt : f m < w := by
    simp only [w]
    nlinarith
  have hlev : boxLevel f (m, w) = l := by
    rw [boxLevel_of_lt h hp hgt.le]
    simp only [w]
    field_simp
    ring
  refine ⟨(m, w), hp, hgt, Prod.ext ?_ ?_⟩
  · simp only [boxCollapse, hlev]
    exact hmq
  · simp only [boxCollapse, hlev, hl]
    ring

end Collapse

section System

variable {g f : ι → ℝ → ℝ}

/-- The bottoms of the boxes. -/
def boxBottom (φ : ι → ℝ × ℝ → S) : Set S := ⋃ i, (fun m : ℝ => φ i (m, 0)) '' Icc 0 1

/-- A point of the surface that is not under the graph of `f` in any box. -/
def IsAboveGraph (φ : ι → ℝ × ℝ → S) (f : ι → ℝ → ℝ) (x : S) : Prop := ∀ i p, p ∈ cuffBox → φ i p
  = x → f i p.1 < p.2

theorem isBoxMap_collapse (hd : ∀ i, IsCollapseData (g i) (f i)) : IsBoxMap (fun i => boxCollapse
  (g i) (f i)) sideLevel :=
  ⟨fun i => continuousOn_boxCollapse (hd i), fun i _ hp => boxCollapse_mem (hd i) hp, fun i _ hp h2
    => boxCollapse_top (hd i) hp h2, fun i _ _ hm _ => boxCollapse_side (hd i) hm⟩

/-- A point above the graph that goes to a side of the box was on that side. -/
theorem side_of_boxCollapse {g₀ f₀ : ℝ → ℝ} (h : IsCollapseData g₀ f₀) {p : ℝ × ℝ}
  (hp : p ∈ cuffBox) (hpf : f₀ p.1 < p.2) (hs : (boxCollapse g₀ f₀ p).1 = 0 ∨
    (boxCollapse g₀ f₀ p).1 = 1) : p.1 = 0 ∨ p.1 = 1 := by
  have hl : 0 < boxLevel f₀ p := lt_of_le_of_ne (h.level_mem hp).1 fun h2 => absurd
    ((boxLevel_eq_zero h hp).mp h2.symm) (not_le.mpr hpf)
  obtain ⟨-, hl1⟩ := h.level_mem hp
  obtain ⟨h3, h4⟩ := h.gmem hp.1
  obtain ⟨h5, h6⟩ := hp.1
  have h7 : 0 ≤ 1 - boxLevel f₀ p := by linarith
  simp only [boxCollapse] at hs
  rcases hs with hs | hs
  · left
    have h8 : boxLevel f₀ p * p.1 = 0 := by nlinarith [mul_nonneg h7 h3, mul_nonneg hl.le h5]
    exact (mul_eq_zero.mp h8).resolve_left hl.ne'
  · right
    have h8 : boxLevel f₀ p * (1 - p.1) = 0 := by
      nlinarith [mul_nonneg h7 (sub_nonneg.mpr h4), mul_nonneg hl.le (sub_nonneg.mpr h6)]
    have := (mul_eq_zero.mp h8).resolve_left hl.ne'
    linarith

theorem sideLevel_inj {w w' : ℝ} (h1 : 1 < w) (h2 : 1 < w') (he : sideLevel w = sideLevel w') : w
  = w' := by
  simp only [sideLevel] at he
  rw [max_eq_right (by linarith), max_eq_right (by linarith)] at he
  linarith

variable [T2Space S]

omit [T2Space S] in
/-- The map of the surface at the end of the homotopy is one to one on the points above the graphs.
-/
theorem IsBoxSystem.inj_above (h : IsBoxSystem φ) (hd : ∀ i, IsCollapseData (g i) (f i)) {ρ : S
  → S} (hρ : ∀ i p, p ∈ cuffBox → ρ (φ i p) = φ i (boxCollapse (g i) (f i) p)) (hρ' : ∀ x,
    (∀ i, x ∉ φ i '' cuffBox) → ρ x = x) {x y : S} (hx : IsAboveGraph φ f x)
      (hy : IsAboveGraph φ f y) (he : ρ x = ρ y) : x = y := by
  by_cases hxb : ∃ i, x ∈ φ i '' cuffBox
  · obtain ⟨i, p, hp, rfl⟩ := hxb
    by_cases hyb : ∃ i, y ∈ φ i '' cuffBox
    · obtain ⟨i', q, hq, rfl⟩ := hyb
      rw [hρ i p hp, hρ i' q hq] at he
      have hpf := hx i p hp rfl
      have hqf := hy i' q hq rfl
      rcases h.meet i i' _ _ (boxCollapse_mem (hd i) hp) (boxCollapse_mem
        (hd i') hq) he with ⟨rfl, h1⟩ | ⟨h1, h2, h3, h4⟩
      · rw [boxCollapse_inj (hd i) hp hq hpf hqf h1]
      · have hm := side_of_boxCollapse (hd i) hp hpf h2
        have hm' := side_of_boxCollapse (hd i') hq hqf h3
        have hp' : p = (p.1, p.2) := rfl
        have hq' : q = (q.1, q.2) := rfl
        have h5 := boxCollapse_side (w := p.2) (hd i) hm
        have h6 := boxCollapse_side (w := q.2) (hd i') hm'
        rw [← hp'] at h5
        rw [← hq'] at h6
        rw [h5, h6] at h1 h4
        have hf1 : f i p.1 = 1 := by
          rcases hm with hm | hm <;> rw [hm]
          · exact (hd i).f0
          · exact (hd i).f1'
        have hf2 : f i' q.1 = 1 := by
          rcases hm' with hm' | hm' <;> rw [hm']
          · exact (hd i').f0
          · exact (hd i').f1'
        have h7 : p.2 = q.2 := sideLevel_inj (hf1 ▸ hpf) (hf2 ▸ hqf) h1
        have h8 := h4 p.2 hp.2
        rw [hp', h8, h7]
    · push Not at hyb
      rw [hρ i p hp, hρ' y hyb] at he
      exact absurd (mem_image_of_mem (φ i) (boxCollapse_mem (hd i) hp)) (he ▸ hyb i)
  · push Not at hxb
    by_cases hyb : ∃ i, y ∈ φ i '' cuffBox
    · obtain ⟨i, q, hq, rfl⟩ := hyb
      rw [hρ i q hq, hρ' x hxb] at he
      exact absurd (mem_image_of_mem (φ i) (boxCollapse_mem (hd i) hq)) (he ▸ hxb i)
    · push Not at hyb
      rwa [hρ' x hxb, hρ' y hyb] at he

omit [T2Space S] in
/-- Each point off the bottoms comes from a point above the graphs. -/
theorem IsBoxSystem.surj_above (h : IsBoxSystem φ) (hd : ∀ i, IsCollapseData (g i) (f i)) {ρ : S
  → S} (hρ : ∀ i p, p ∈ cuffBox → ρ (φ i p) = φ i (boxCollapse (g i) (f i) p)) (hρ' : ∀ x,
    (∀ i, x ∉ φ i '' cuffBox) → ρ x = x) {y : S} (hy : y ∉ boxBottom φ) : ∃ x, IsAboveGraph φ f x
      ∧ ρ x = y := by
  by_cases hyb : ∃ i, y ∈ φ i '' cuffBox
  · obtain ⟨i, q, hq, rfl⟩ := hyb
    have hq0 : 0 < q.2 := by
      refine lt_of_le_of_ne hq.2.1 fun h0 => hy (mem_iUnion.mpr ⟨i, q.1, hq.1, ?_⟩)
      change φ i (q.1, 0) = φ i q
      rw [h0]
    obtain ⟨p, hp, hpf, hpe⟩ := boxCollapse_surj (hd i) hq hq0
    refine ⟨φ i p, fun i' p' hp' he => ?_, by rw [hρ i p hp, hpe]⟩
    rcases h.meet i' i p' p hp' hp he with ⟨rfl, rfl⟩ | ⟨h1, h2, h3, -⟩
    · exact hpf
    · have hf1 : f i' p'.1 = 1 := by
        rcases h2 with hm | hm <;> rw [hm]
        · exact (hd i').f0
        · exact (hd i').f1'
      have hf2 : f i p.1 = 1 := by
        rcases h3 with hm | hm <;> rw [hm]
        · exact (hd i).f0
        · exact (hd i).f1'
      rw [hf1, h1, ← hf2]
      exact hpf
  · push Not at hyb
    exact ⟨y, fun i p hp he => absurd (mem_image_of_mem (φ i) hp) (he ▸ hyb i), hρ' y hyb⟩

omit [T2Space S] in
/-- The points above the graphs do not go to the bottoms, and the other points of the boxes do. -/
theorem IsBoxSystem.not_bottom_above (h : IsBoxSystem φ) (hd : ∀ i, IsCollapseData (g i)
  (f i)) {ρ : S → S} (hρ : ∀ i p, p ∈ cuffBox → ρ (φ i p) = φ i (boxCollapse (g i) (f i) p))
    (hρ' : ∀ x, (∀ i, x ∉ φ i '' cuffBox) → ρ x = x) {x : S} (hx : IsAboveGraph φ f x) : ρ x ∉
      boxBottom φ := by
  rintro hb
  obtain ⟨i', m, hm, he⟩ := mem_iUnion.mp hb
  have hb0 : (m, (0 : ℝ)) ∈ cuffBox := ⟨hm, by norm_num, by norm_num⟩
  by_cases hxb : ∃ i, x ∈ φ i '' cuffBox
  · obtain ⟨i, p, hp, rfl⟩ := hxb
    rw [hρ i p hp] at he
    have hl : 0 < boxLevel (f i) p := lt_of_le_of_ne ((hd i).level_mem hp).1 fun h2 => absurd
      ((boxLevel_eq_zero (hd i) hp).mp h2.symm) (not_le.mpr (hx i p hp rfl))
    have hlev : 0 < (boxCollapse (g i) (f i) p).2 := by
      simp only [boxCollapse]
      linarith
    rcases h.meet i' i _ _ hb0 (boxCollapse_mem (hd i) hp) he with ⟨-, h1⟩ | ⟨h1, -⟩
    · rw [← h1] at hlev
      simp at hlev
    · simp only at h1
      linarith
  · push Not at hxb
    rw [hρ' x hxb] at he
    exact hxb i' (he ▸ mem_image_of_mem _ hb0)

end System

end GraphMinor.GM07
