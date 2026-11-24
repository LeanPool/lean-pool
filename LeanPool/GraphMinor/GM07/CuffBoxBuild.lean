/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.CuffChart

/-!
# The boxes around one cuff

Graph Minors VII, (5.9), page 235. Each cell of the annulus between `D` and `E` gets a chart from
the square `[0,1] × [0,1]`. Above level `1` we follow the rays of a collar of `E`, up to level `2`.
Two neighbouring boxes agree on their common side.
-/

@[expose] public section

namespace GraphMinor.GM07

open Set Topology Function Metric GraphMinor.Surface GraphMinor.GM11

universe u

variable {T : Type u} [TopologicalSpace T] [T2Space T] {ι : Type*}

/-- The data of a box around a cuff. `S k` is the common side over the line `q k`. -/
structure IsCuffBoxes (D E Δ : Set T) (q : ι → Set T) (x t : ι → T) (F : Set (CellRec T ι))
  (Φ : CellRec T ι → ℝ × ℝ → T) (S : ι → ℝ → T) (μ : CellRec T ι → ℝ → T) : Prop where
  cont : ∀ c ∈ F, ContinuousOn (Φ c) cuffBox
  inj : ∀ c ∈ F, InjOn (Φ c) cuffBox
  mapsΔ : ∀ c ∈ F, MapsTo (Φ c) cuffBox Δ
  sideInj : ∀ k, InjOn (S k) (Icc 0 2)
  left : ∀ c ∈ F, ∀ w ∈ Icc (0 : ℝ) 2, Φ c (0, w) = S c.i w
  right : ∀ c ∈ F, ∀ w ∈ Icc (0 : ℝ) 2, Φ c (1, w) = S c.i' w
  top : ∀ c ∈ F, ∀ m ∈ Icc (0 : ℝ) 1, Φ c (m, 1) = μ c m
  param : ∀ c ∈ F, IsParam c.b (t c.i) (t c.i') (μ c)
  sideIn : ∀ k, ∀ w ∈ Icc (0 : ℝ) 1, S k w ∈ q k
  sideOf : ∀ k, ∀ y ∈ q k, ∃ w ∈ Icc (0 : ℝ) 1, S k w = y
  sideOne : ∀ k, S k 1 = t k
  sideZero : ∀ k, S k 0 = x k
  inE : ∀ c ∈ F, ∀ p ∈ cuffBox, Φ c p ∈ E ↔ p.2 ≤ 1
  inR : ∀ c ∈ F, ∀ p ∈ cuffBox, p.2 ≤ 1 → Φ c p ∈ c.R
  onBd : ∀ c ∈ F, ∀ p ∈ cuffBox, Φ c p ∈ discBd E ↔ p.2 = 1
  inD : ∀ c ∈ F, ∀ p ∈ cuffBox, Φ c p ∈ D ↔ p.2 = 0
  bdΔ : ∀ c ∈ F, ∀ p ∈ cuffBox, Φ c p ∈ discBd Δ ↔ p.2 = 2
  cover : ∀ y ∈ Δ \ discInt D, ∃ c ∈ F, ∃ p ∈ cuffBox, Φ c p = y
  meet : ∀ c ∈ F, ∀ c' ∈ F, ∀ p p', p ∈ cuffBox → p' ∈ cuffBox → Φ c p = Φ c' p' → (c = c' ∧ p
    = p') ∨ (p.2 = p'.2 ∧ (p.1 = 0 ∨ p.1 = 1) ∧ (p'.1 = 0 ∨ p'.1 = 1) ∧ ∀ w ∈ Icc (0 : ℝ) 2, Φ c
      (p.1, w) = Φ c' (p'.1, w))

variable {D E Δ : Set T} {q : ι → Set T} {x t : ι → T}

/-- The point of level `w` over the point `y` of the boundary of `E`. -/
noncomputable def rayPoint (col : ℂ → T) (pi : T → Circle) (w : ℝ) (y : T) : T := col ((w : ℂ) *
  (pi y : ℂ))

/-- The map of a box. -/
noncomputable def boxMap (ξ : ℂ → T) (col : ℂ → T) (pi : T → Circle) (m : ℝ → T) (p : ℝ × ℝ) : T :=
  if p.2 ≤ 1 then ξ ⟨p.1, p.2⟩ else rayPoint col pi p.2 (m p.1)

/-- The side over a line. -/
noncomputable def lineSide (col : ℂ → T) (pi : T → Circle) (r : ℝ → T) (y : T) (w : ℝ) : T :=
  if w ≤ 1 then r w else rayPoint col pi w y

private theorem collar_ray_eq
    {T : Type u}
    (col : ℂ → T)
    (hcinj : InjOn col (closedBall 0 2))
    (hmemb : ∀ {w : ℝ} (u : Circle), w ∈ Icc 0 2 → (w : ℂ) * (u : ℂ) ∈ closedBall 0 2)
    (hnm : ∀ {w : ℝ} (u : Circle), 0 ≤ w → ‖(w : ℂ) * (u : ℂ)‖ = w)
    {w : ℝ}
    {w' : ℝ}
    {u : Circle}
    {u' : Circle}
    (hw : w ∈ Icc 0 2)
    (hw' : w' ∈ Icc 0 2)
    (he : col (↑w * ↑u) = col (↑w' * ↑u')) :
    w = w' ∧ (0 < w → u = u') := by
  have h1 := hcinj (hmemb u hw) (hmemb u' hw') he
  have h2 : w = w' := by
    have := congrArg norm h1
    rwa [hnm u hw.1, hnm u' hw'.1] at this
  refine ⟨h2, fun h0 => ?_⟩
  subst h2
  have h3 : (w : ℂ) ≠ 0 := by exact_mod_cast h0.ne'
  exact Circle.ext (mul_left_cancel₀ h3 h1)

private theorem cuff_box_injective
    {T : Type u}
    [TopologicalSpace T]
    {ι : Type*}
    {E : Set T}
    {x : ι → T}
    {t : ι → T}
    (F : Set (CellRec T ι))
    (col : ℂ → T)
    (pi : T → Circle)
    (hpiinj : InjOn pi (discBd E))
    (hray : ∀ {w w' : ℝ} {u u' : Circle}, w ∈ Icc 0 2 → w' ∈ Icc 0 2 → col (↑w * ↑u) = col (↑w' *
      ↑u') → w = w' ∧ (0 < w → u = u'))
    (r : ι → ℝ → T)
    (μ : CellRec T ι → ℝ → T)
    (α : CellRec T ι → ℝ → T)
    (hμα : ∀ c ∈ F, IsParam c.b (t c.i) (t c.i') (μ c) ∧ IsParam c.a (x c.i) (x c.i') (α c))
    (ξ : CellRec T ι → ℂ → T)
    (hξ : ∀ c ∈ F, ContinuousOn (ξ c) unitSq ∧ InjOn (ξ c) unitSq ∧ ξ c '' unitSq = c.R ∧ ∀ z ∈
      frontier unitSq, ξ c z = cellBd (r c.i) (r c.i') (α c) (μ c) z)
    (Φ : CellRec T ι → ℝ × ℝ → T)
    (hsq : ∀ {p : ℝ × ℝ}, p ∈ cuffBox → p.2 ≤ 1 → { re := p.1, im := p.2 } ∈ unitSq)
    (hΦlow : ∀ (c : CellRec T ι) {p : ℝ × ℝ}, p.2 ≤ 1 → Φ c p = ξ c { re := p.1, im := p.2 })
    (hΦhigh : ∀ (c : CellRec T ι) {p : ℝ × ℝ}, ¬p.2 ≤ 1 → Φ c p = rayPoint col pi p.2 (μ c p.1))
    (hR : ∀ c ∈ F, ∀ p ∈ cuffBox, p.2 ≤ 1 → Φ c p ∈ c.R)
    (hRE : ∀ c ∈ F, c.R ⊆ E)
    (hmemray : ∀ (w : ℝ) (y : T), rayPoint col pi w y = col (↑w * ↑(pi y)))
    (hμE : ∀ c ∈ F, ∀ m ∈ Icc 0 1, μ c m ∈ discBd E)
    (hinE : ∀ c ∈ F, ∀ p ∈ cuffBox, Φ c p ∈ E ↔ p.2 ≤ 1)
    (c : CellRec T ι)
    (hc : c ∈ F)
    (p : ℝ × ℝ)
    (hp : p ∈ cuffBox)
    (p' : ℝ × ℝ)
    (hp' : p' ∈ cuffBox)
    (he : Φ c p = Φ c p') :
    p = p' := by
  by_cases h1 : p.2 ≤ 1 <;> by_cases h2 : p'.2 ≤ 1
  · rw [hΦlow c h1, hΦlow c h2] at he
    have h3 := (hξ c hc).2.1 (hsq hp h1) (hsq hp' h2) he
    exact Prod.ext (congrArg Complex.re h3) (congrArg Complex.im h3)
  · exact absurd ((hinE c hc p' hp').mp (he ▸ hRE c hc (hR c hc p hp h1))) h2
  · exact absurd ((hinE c hc p hp).mp (he.symm ▸ hRE c hc (hR c hc p' hp' h2))) h1
  · rw [hΦhigh c h1, hΦhigh c h2, hmemray, hmemray] at he
    obtain ⟨h3, h4⟩ := hray hp.2 hp'.2 he
    have h5 := h4 (by linarith [not_le.mp h1])
    have h6 := (hμα c hc).1.inj hp.1 hp'.1 (hpiinj (hμE c hc _ hp.1) (hμE c hc _ hp'.1) h5)
    exact Prod.ext h6 h3

private theorem cuff_side_injective
    {T : Type u}
    [TopologicalSpace T]
    {ι : Type*}
    {E : Set T}
    {q : ι → Set T}
    {x : ι → T}
    {t : ι → T}
    (col : ℂ → T)
    (pi : T → Circle)
    (hmemb : ∀ {w : ℝ} (u : Circle), w ∈ Icc 0 2 → (w : ℂ) * (u : ℂ) ∈ closedBall 0 2)
    (hnm : ∀ {w : ℝ} (u : Circle), 0 ≤ w → ‖(w : ℂ) * (u : ℂ)‖ = w)
    (hray : ∀ {w w' : ℝ} {u u' : Circle}, w ∈ Icc 0 2 → w' ∈ Icc 0 2 → col (↑w * ↑u) = col (↑w' *
      ↑u') → w = w' ∧ (0 < w → u = u'))
    (hE' : ∀ {z : ℂ}, z ∈ closedBall 0 2 → (col z ∈ E ↔ ‖z‖ ≤ 1))
    (r : ι → ℝ → T)
    (hr : ∀ (k : ι), IsParam (q k) (x k) (t k) (r k))
    (S : ι → ℝ → T)
    (hSlow : ∀ (k : ι) {w : ℝ}, w ≤ 1 → S k w = r k w)
    (hShigh : ∀ (k : ι) {w : ℝ}, ¬w ≤ 1 → S k w = rayPoint col pi w (t k))
    (hmemray : ∀ (w : ℝ) (y : T), rayPoint col pi w y = col (↑w * ↑(pi y)))
    (hrE : ∀ (k : ι), ∀ w ∈ Icc 0 1, r k w ∈ E)
    (k : ι)
    (w : ℝ)
    (hw : w ∈ Icc 0 2)
    (w' : ℝ)
    (hw' : w' ∈ Icc 0 2)
    (he : S k w = S k w') :
    w = w' := by
  have hoffS : ∀ w ∈ Icc (0 : ℝ) 2, ¬ w ≤ 1 → S k w ∉ E := fun w hw h1 => by
    rw [hShigh k h1, hmemray, hE' (hmemb _ hw), hnm _ hw.1]
    exact h1
  by_cases h1 : w ≤ 1 <;> by_cases h2 : w' ≤ 1
  · rw [hSlow k h1, hSlow k h2] at he
    exact (hr k).inj ⟨hw.1, h1⟩ ⟨hw'.1, h2⟩ he
  · have h3 := hrE k w ⟨hw.1, h1⟩
    rw [← hSlow k h1, he] at h3
    exact absurd h3 (hoffS w' hw' h2)
  · have h3 := hrE k w' ⟨hw'.1, h2⟩
    rw [← hSlow k h2, ← he] at h3
    exact absurd h3 (hoffS w hw h1)
  · rw [hShigh k h1, hShigh k h2, hmemray, hmemray] at he
    exact (hray hw hw' he).1

private theorem cuff_box_continuous
    {T : Type u}
    [TopologicalSpace T]
    {ι : Type*}
    {E : Set T}
    {x : ι → T}
    {t : ι → T}
    (F : Set (CellRec T ι))
    (col : ℂ → T)
    (hcc : ContinuousOn col (closedBall 0 2))
    (pi : T → Circle)
    (hpic : ContinuousOn pi (discBd E))
    (hcolp : ∀ y ∈ discBd E, col ↑(pi y) = y)
    (hmemb : ∀ {w : ℝ} (u : Circle), w ∈ Icc 0 2 → (w : ℂ) * (u : ℂ) ∈ closedBall 0 2)
    (r : ι → ℝ → T)
    (μ : CellRec T ι → ℝ → T)
    (α : CellRec T ι → ℝ → T)
    (hμα : ∀ c ∈ F, IsParam c.b (t c.i) (t c.i') (μ c) ∧ IsParam c.a (x c.i) (x c.i') (α c))
    (ξ : CellRec T ι → ℂ → T)
    (hξ : ∀ c ∈ F, ContinuousOn (ξ c) unitSq ∧ InjOn (ξ c) unitSq ∧ ξ c '' unitSq = c.R ∧ ∀ z ∈
      frontier unitSq, ξ c z = cellBd (r c.i) (r c.i') (α c) (μ c) z)
    (Φ : CellRec T ι → ℝ × ℝ → T)
    (hsq : ∀ {p : ℝ × ℝ}, p ∈ cuffBox → p.2 ≤ 1 → { re := p.1, im := p.2 } ∈ unitSq)
    (hΦlow : ∀ (c : CellRec T ι) {p : ℝ × ℝ}, p.2 ≤ 1 → Φ c p = ξ c { re := p.1, im := p.2 })
    (hΦhigh : ∀ (c : CellRec T ι) {p : ℝ × ℝ}, ¬p.2 ≤ 1 → Φ c p = rayPoint col pi p.2 (μ c p.1))
    (htop : ∀ c ∈ F, ∀ m ∈ Icc 0 1, Φ c (m, 1) = μ c m)
    (hμE : ∀ c ∈ F, ∀ m ∈ Icc 0 1, μ c m ∈ discBd E)
    (c : CellRec T ι)
    (hc : c ∈ F) :
    ContinuousOn (Φ c) cuffBox := by
  have hto : Continuous fun p : ℝ × ℝ => (⟨p.1, p.2⟩ : ℂ) :=
    Complex.equivRealProdCLM.symm.continuous
  have hsplit : cuffBox = {p | p ∈ cuffBox ∧ p.2 ≤ 1} ∪ {p | p ∈ cuffBox ∧ 1 ≤ p.2} := by
    ext p
    simp only [mem_union, mem_ofPred_eq]
    constructor
    · intro h1
      rcases le_total p.2 1 with h2 | h2
      · exact .inl ⟨h1, h2⟩
      · exact .inr ⟨h1, h2⟩
    · rintro (h1 | h1) <;> exact h1.1
  have hcb : IsClosed cuffBox := isCompact_cuffBox.isClosed
  have hlowMaps : MapsTo (fun p : ℝ × ℝ => (⟨p.1, p.2⟩ : ℂ))
      {p | p ∈ cuffBox ∧ p.2 ≤ 1} unitSq := fun _ hp => hsq hp.1 hp.2
  have h1 : ContinuousOn (Φ c) {p | p ∈ cuffBox ∧ p.2 ≤ 1} :=
    ((hξ c hc).1.comp hto.continuousOn hlowMaps).congr fun _ hp => hΦlow c hp.2
  have hμm : ∀ p : ℝ × ℝ, p ∈ {p | p ∈ cuffBox ∧ 1 ≤ p.2} → μ c p.1 ∈ discBd E := fun p hp
    => hμE c hc _ hp.1.1
  have hfst : MapsTo Prod.fst {p : ℝ × ℝ | p ∈ cuffBox ∧ 1 ≤ p.2} (Icc 0 1) :=
    fun _ hp => hp.1.1
  have h3 : ContinuousOn (fun p : ℝ × ℝ => μ c p.1) {p | p ∈ cuffBox ∧ 1 ≤ p.2} :=
    (hμα c hc).1.cont.comp continuous_fst.continuousOn hfst
  have h4 : ContinuousOn (fun p : ℝ × ℝ => ((pi (μ c p.1) : Circle) : ℂ)) {p | p ∈ cuffBox ∧ 1
    ≤ p.2} := continuous_subtype_val.comp_continuousOn (hpic.comp h3 hμm)
  have h5 : ContinuousOn (fun p : ℝ × ℝ => ((p.2 : ℝ) : ℂ) * ((pi (μ c p.1) : Circle) : ℂ)) {p |
    p ∈ cuffBox ∧ 1 ≤ p.2} := (Complex.continuous_ofReal.comp continuous_snd).continuousOn.mul h4
  have h2 : ContinuousOn (Φ c) {p | p ∈ cuffBox ∧ 1 ≤ p.2} := by
    refine (hcc.comp h5 fun p hp => hmemb _ hp.1.2).congr fun p hp => ?_
    by_cases h6 : p.2 ≤ 1
    · have h7 : p.2 = 1 := le_antisymm h6 hp.2
      have h8 : p = (p.1, 1) := Prod.ext rfl h7
      rw [h8, htop c hc _ hp.1.1]
      simp only [comp_apply, Complex.ofReal_one, one_mul]
      exact (hcolp _ (hμE c hc _ hp.1.1)).symm
    · rw [hΦhigh c h6]
      rfl
  rw [hsplit]
  exact h1.union_of_isClosed h2 (hcb.inter (isClosed_le continuous_snd continuous_const))
    (hcb.inter (isClosed_le continuous_const continuous_snd))

private theorem cuff_boxes_overlap_on_sides
    {T : Type u}
    [TopologicalSpace T]
    {ι : Type*}
    {D : Set T}
    {E : Set T}
    {q : ι → Set T}
    {x : ι → T}
    {t : ι → T}
    (hq : ∀ (k : ι), IsCrossLine D E (q k) (x k) (t k))
    (F : Set (CellRec T ι))
    (hF : IsCellFamily D E q x t univ F)
    (col : ℂ → T)
    (pi : T → Circle)
    (hpiinj : InjOn pi (discBd E))
    (hray : ∀ {w w' : ℝ} {u u' : Circle}, w ∈ Icc 0 2 → w' ∈ Icc 0 2 → col (↑w * ↑u) = col (↑w' *
      ↑u') → w = w' ∧ (0 < w → u = u'))
    (μ : CellRec T ι → ℝ → T)
    (Φ : CellRec T ι → ℝ × ℝ → T)
    (S : ι → ℝ → T)
    (hΦhigh : ∀ (c : CellRec T ι) {p : ℝ × ℝ}, ¬p.2 ≤ 1 → Φ c p = rayPoint col pi p.2 (μ c p.1))
    (hShigh : ∀ (k : ι) {w : ℝ}, ¬w ≤ 1 → S k w = rayPoint col pi w (t k))
    (htop : ∀ c ∈ F, ∀ m ∈ Icc 0 1, Φ c (m, 1) = μ c m)
    (hR : ∀ c ∈ F, ∀ p ∈ cuffBox, p.2 ≤ 1 → Φ c p ∈ c.R)
    (hRE : ∀ c ∈ F, c.R ⊆ E)
    (hmemray : ∀ (w : ℝ) (y : T), rayPoint col pi w y = col (↑w * ↑(pi y)))
    (hμE : ∀ c ∈ F, ∀ m ∈ Icc 0 1, μ c m ∈ discBd E)
    (hinE : ∀ c ∈ F, ∀ p ∈ cuffBox, Φ c p ∈ E ↔ p.2 ≤ 1)
    (hinj : ∀ c ∈ F, InjOn (Φ c) cuffBox)
    (hsideE : ∀ c ∈ F, ∀ (k : ι), k = c.i ∨ k = c.i' → ∃ e, (e = 0 ∨ e = 1) ∧ ∀ w ∈ Icc 0 2, Φ c
      (e, w) = S k w)
    (hSof : ∀ (k : ι), ∀ y ∈ q k, ∃ w ∈ Icc 0 1, S k w = y)
    (hboxe : ∀ {e w : ℝ}, e = 0 ∨ e = 1 → w ∈ Icc 0 2 → (e, w) ∈ cuffBox)
    (c : CellRec T ι)
    (hc : c ∈ F)
    (c' : CellRec T ι)
    (hc' : c' ∈ F)
    (p : ℝ × ℝ)
    (p' : ℝ × ℝ)
    (hp : p ∈ cuffBox)
    (hp' : p' ∈ cuffBox)
    (he : Φ c p = Φ c' p') :
    c = c' ∧ p = p' ∨ p.2 = p'.2 ∧ (p.1 = 0 ∨ p.1 = 1) ∧ (p'.1 = 0 ∨ p'.1 = 1) ∧ ∀ w ∈ Icc 0 2, Φ
      c (p.1, w) = Φ c' (p'.1, w) := by
  by_cases hne : c = c'
  · subst hne
    exact .inl ⟨rfl, hinj c hc hp hp' he⟩
  right
  have hfin : ∀ {k : ι} {w₀ : ℝ}, (k = c.i ∨ k = c.i') → (k = c'.i ∨ k = c'.i') → w₀ ∈ Icc
    (0 : ℝ) 2 → Φ c p = S k w₀ → Φ c' p' = S k w₀ → p.2 = p'.2 ∧ (p.1 = 0 ∨ p.1 = 1) ∧ (p'.1 = 0
      ∨ p'.1 = 1) ∧ ∀ w ∈ Icc (0 : ℝ) 2, Φ c (p.1, w) = Φ c' (p'.1, w) := fun {k w₀} h1 h2 hw h3 h4
        => by
    obtain ⟨e, he0, heS⟩ := hsideE c hc k h1
    obtain ⟨e', he0', heS'⟩ := hsideE c' hc' k h2
    have h5 : p = (e, w₀) := hinj c hc hp (hboxe he0 hw) (h3.trans (heS w₀ hw).symm)
    have h6 : p' = (e', w₀) := hinj c' hc' hp' (hboxe he0' hw) (h4.trans (heS' w₀ hw).symm)
    subst h5 h6
    exact ⟨rfl, he0, he0', fun w hw' => (heS w hw').trans (heS' w hw').symm⟩
  by_cases h1 : p.2 ≤ 1
  · have h2 : p'.2 ≤ 1 := (hinE c' hc' p' hp').mp (he ▸ hRE c hc (hR c hc p hp h1))
    obtain ⟨k, hk, hk', hw⟩ := hF.meet c hc c' hc' hne _ (hR c hc p hp h1)
      (he ▸ hR c' hc' p' hp' h2)
    obtain ⟨w₀, hw₀, h3⟩ := hSof k _ hw
    exact hfin hk hk' ⟨hw₀.1, by linarith [hw₀.2]⟩ h3.symm (he.symm.trans h3.symm)
  · have h2 : ¬ p'.2 ≤ 1 := fun h2 => h1 ((hinE c hc p hp).mp (he.symm ▸ hRE c' hc'
      (hR c' hc' p' hp' h2)))
    have he' := he
    rw [hΦhigh c h1, hΦhigh c' h2, hmemray, hmemray] at he'
    obtain ⟨h3, h4⟩ := hray hp.2 hp'.2 he'
    have h5 := hpiinj (hμE c hc _ hp.1) (hμE c' hc' _ hp'.1) (h4 (by linarith [not_le.mp h1]))
    have hRm : ∀ c ∈ F, ∀ m ∈ Icc (0 : ℝ) 1, μ c m ∈ c.R := fun c hc m hm =>
      htop c hc m hm ▸ hR c hc _ ⟨hm, zero_le_one, by norm_num⟩ le_rfl
    obtain ⟨k, hk, hk', hw⟩ := hF.meet c hc c' hc' hne _ (hRm c hc _ hp.1)
      (h5 ▸ hRm c' hc' _ hp'.1)
    have h6 : μ c p.1 = t k := by
      have h7 : μ c p.1 ∈ q k ∩ discBd E := ⟨hw, hμE c hc _ hp.1⟩
      rwa [(hq k).top] at h7
    have hup : ∀ {c₀}, c₀ ∈ F → (k = c₀.i ∨ k = c₀.i') → ∀ {p₀ : ℝ × ℝ}, p₀ ∈ cuffBox → ¬ p₀.2
      ≤ 1 → μ c₀ p₀.1 = t k → Φ c₀ p₀ = S k p₀.2 := fun {c₀} hc₀ hk₀ {p₀} hp₀ h7 h8 => by
      rw [hΦhigh c₀ h7, hShigh k h7, h8]
    exact hfin (w₀ := p.2) hk hk' hp.2 (hup hc hk hp h1 h6) (by
      rw [h3]
      exact hup hc' hk' hp' h2 (h5 ▸ h6))

private theorem cuff_box_mem_inner_disc
    {T : Type u}
    [TopologicalSpace T]
    {ι : Type*}
    {D : Set T}
    {E : Set T}
    {q : ι → Set T}
    {x : ι → T}
    {t : ι → T}
    (hDE : D ⊆ E \ discBd E)
    (F : Set (CellRec T ι))
    (hF : IsCellFamily D E q x t univ F)
    (μ : CellRec T ι → ℝ → T)
    (α : CellRec T ι → ℝ → T)
    (hμα : ∀ c ∈ F, IsParam c.b (t c.i) (t c.i') (μ c) ∧ IsParam c.a (x c.i) (x c.i') (α c))
    (Φ : CellRec T ι → ℝ × ℝ → T)
    (hR : ∀ c ∈ F, ∀ p ∈ cuffBox, p.2 ≤ 1 → Φ c p ∈ c.R)
    (hinE : ∀ c ∈ F, ∀ p ∈ cuffBox, Φ c p ∈ E ↔ p.2 ≤ 1)
    (hinj : ∀ c ∈ F, InjOn (Φ c) cuffBox)
    (hlow0 : ∀ c ∈ F, ∀ m ∈ Icc 0 1, Φ c (m, 0) = α c m)
    (haD : ∀ c ∈ F, ∀ {y : T}, y ∈ c.a → y ∈ D)
    (c : CellRec T ι)
    (hc : c ∈ F)
    (p : ℝ × ℝ)
    (hp : p ∈ cuffBox) :
    Φ c p ∈ D ↔ p.2 = 0 := by
  constructor
  · intro h1
    have h2 : p.2 ≤ 1 := (hinE c hc p hp).mp (hDE h1).1
    have h3 : Φ c p ∈ c.R ∩ D := ⟨hR c hc p hp h2, h1⟩
    rw [(hF.cell c hc).botCap] at h3
    obtain ⟨m, hm, h4⟩ := (hμα c hc).2.exists_of_mem h3
    have h5 := hinj c hc hp
      (⟨hm, le_rfl, by norm_num⟩ : (m, (0 : ℝ)) ∈ cuffBox) (by rw [hlow0 c hc m hm, h4])
    rw [h5]
  · intro h1
    have h8 : p = (p.1, 0) := Prod.ext rfl h1
    rw [h8, hlow0 c hc _ hp.1]
    exact haD c hc ((hμα c hc).2.mem hp.1)

private theorem cuff_boxes_cover_annulus
    {T : Type u}
    [TopologicalSpace T]
    {ι : Type*}
    {D : Set T}
    {E : Set T}
    {Δ : Set T}
    {q : ι → Set T}
    {x : ι → T}
    {t : ι → T}
    (F : Set (CellRec T ι))
    (hF : IsCellFamily D E q x t univ F)
    (pE : Circle ≃ₜ ↑(discBd E))
    (col : ℂ → T)
    (col' : T → ℂ)
    (hcm' : MapsTo col' Δ (closedBall 0 2))
    (hcr : RightInvOn col' col Δ)
    (pi : T → Circle)
    (hpi : ∀ (y : T) (h : y ∈ discBd E), pi y = pE.symm ⟨y, h⟩)
    (hE' : ∀ {z : ℂ}, z ∈ closedBall 0 2 → (col z ∈ E ↔ ‖z‖ ≤ 1))
    (r : ι → ℝ → T)
    (μ : CellRec T ι → ℝ → T)
    (α : CellRec T ι → ℝ → T)
    (hμα : ∀ c ∈ F, IsParam c.b (t c.i) (t c.i') (μ c) ∧ IsParam c.a (x c.i) (x c.i') (α c))
    (ξ : CellRec T ι → ℂ → T)
    (hξ : ∀ c ∈ F, ContinuousOn (ξ c) unitSq ∧ InjOn (ξ c) unitSq ∧ ξ c '' unitSq = c.R ∧ ∀ z ∈
      frontier unitSq, ξ c z = cellBd (r c.i) (r c.i') (α c) (μ c) z)
    (Φ : CellRec T ι → ℝ × ℝ → T)
    (hΦlow : ∀ (c : CellRec T ι) {p : ℝ × ℝ}, p.2 ≤ 1 → Φ c p = ξ c { re := p.1, im := p.2 })
    (hΦhigh : ∀ (c : CellRec T ι) {p : ℝ × ℝ}, ¬p.2 ≤ 1 → Φ c p = rayPoint col pi p.2 (μ c p.1))
    (hmemray : ∀ (w : ℝ) (y : T), rayPoint col pi w y = col (↑w * ↑(pi y)))
    (hlow0 : ∀ c ∈ F, ∀ m ∈ Icc 0 1, Φ c (m, 0) = α c m)
    (y : T)
    (hy : y ∈ Δ \ discInt D) :
    ∃ c ∈ F, ∃ p ∈ cuffBox, Φ c p = y := by
  by_cases hyE : y ∈ E
  · by_cases hyD : y ∈ D
    · have hb : y ∈ discBd D := by
        by_contra h1
        exact hy.2 ⟨hyD, h1⟩
      obtain ⟨c, hc, h1⟩ := hF.botCover y hb
      obtain ⟨m, hm, h2⟩ := (hμα c hc).2.exists_of_mem h1
      exact ⟨c, hc, (m, 0), ⟨hm, le_rfl, by norm_num⟩, by rw [hlow0 c hc m hm, h2]⟩
    · rcases hF.cover y hyE with h1 | ⟨c, hc, h1⟩
      · exact absurd h1 hyD
      · rw [← (hξ c hc).2.2.1] at h1
        obtain ⟨z, hz, rfl⟩ := h1
        exact ⟨c, hc, (z.re, z.im), ⟨hz.1, hz.2.1, by linarith [hz.2.2]⟩, by rw [hΦlow c hz.2.2]⟩
  · have hz2 := hcm' hy.1
    have hcz := hcr hy.1
    set z := col' y with hz
    have hn : ¬ ‖z‖ ≤ 1 := fun h1 => hyE (hcz ▸ (hE' hz2).mpr h1)
    have hn2 : ‖z‖ ≤ 2 := by simpa using hz2
    have hnp : ‖z‖ ≠ 0 := by
      have := not_le.mp hn
      linarith
    obtain ⟨u, hu⟩ : ∃ u : Circle, (‖z‖ : ℂ) * (u : ℂ) = z := by
      refine ⟨⟨z / ‖z‖, ?_⟩, ?_⟩
      · rw [Submonoid.unitSphere, Submonoid.mem_mk, Subsemigroup.mem_mk,
          mem_sphere_zero_iff_norm, norm_div, Complex.norm_real, norm_norm]
        exact div_self hnp
      · change (‖z‖ : ℂ) * (z / ‖z‖) = z
        have : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast hnp
        field_simp
    obtain ⟨c, hc, hb⟩ := hF.topCover (pE u).1 (pE u).2
    obtain ⟨m, hm, h2⟩ := (hμα c hc).1.exists_of_mem hb
    refine ⟨c, hc, (m, ‖z‖), ⟨hm, norm_nonneg _, hn2⟩, ?_⟩
    rw [hΦhigh c hn, hmemray]
    simp only
    rw [h2, hpi _ (pE u).2]
    simp only [Subtype.coe_eta, Homeomorph.symm_apply_apply, hu]
    exact hcz

private theorem cuff_box_meets_middle_boundary
    {T : Type u}
    [TopologicalSpace T]
    {ι : Type*}
    {D : Set T}
    {E : Set T}
    {q : ι → Set T}
    {x : ι → T}
    {t : ι → T}
    (F : Set (CellRec T ι))
    (hF : IsCellFamily D E q x t univ F)
    (hsph : discBd E ⊆ E)
    (μ : CellRec T ι → ℝ → T)
    (α : CellRec T ι → ℝ → T)
    (hμα : ∀ c ∈ F, IsParam c.b (t c.i) (t c.i') (μ c) ∧ IsParam c.a (x c.i) (x c.i') (α c))
    (Φ : CellRec T ι → ℝ × ℝ → T)
    (htop : ∀ c ∈ F, ∀ m ∈ Icc 0 1, Φ c (m, 1) = μ c m)
    (hR : ∀ c ∈ F, ∀ p ∈ cuffBox, p.2 ≤ 1 → Φ c p ∈ c.R)
    (hμE : ∀ c ∈ F, ∀ m ∈ Icc 0 1, μ c m ∈ discBd E)
    (hinE : ∀ c ∈ F, ∀ p ∈ cuffBox, Φ c p ∈ E ↔ p.2 ≤ 1)
    (hinj : ∀ c ∈ F, InjOn (Φ c) cuffBox)
    (c : CellRec T ι)
    (hc : c ∈ F)
    (p : ℝ × ℝ)
    (hp : p ∈ cuffBox) :
    Φ c p ∈ discBd E ↔ p.2 = 1 := by
  constructor
  · intro h1
    have h2 : p.2 ≤ 1 := (hinE c hc p hp).mp (hsph h1)
    have h3 : Φ c p ∈ c.R ∩ discBd E := ⟨hR c hc p hp h2, h1⟩
    rw [(hF.cell c hc).topCap] at h3
    obtain ⟨m, hm, h4⟩ := (hμα c hc).1.exists_of_mem h3
    have h5 := hinj c hc hp
      (⟨hm, zero_le_one, by norm_num⟩ : (m, (1 : ℝ)) ∈ cuffBox) (by rw [htop c hc m hm, h4])
    rw [h5]
  · intro h1
    have h8 : p = (p.1, 1) := Prod.ext rfl h1
    rw [h8, htop c hc _ hp.1]
    exact hμE c hc _ hp.1

private theorem cuff_box_agrees_on_left_side
    {T : Type u}
    [TopologicalSpace T]
    {ι : Type*}
    {t : ι → T}
    (F : Set (CellRec T ι))
    (col : ℂ → T)
    (pi : T → Circle)
    (r : ι → ℝ → T)
    (μ : CellRec T ι → ℝ → T)
    (α : CellRec T ι → ℝ → T)
    (ξ : CellRec T ι → ℂ → T)
    (hξ : ∀ c ∈ F, ContinuousOn (ξ c) unitSq ∧ InjOn (ξ c) unitSq ∧ ξ c '' unitSq = c.R ∧ ∀ z ∈
      frontier unitSq, ξ c z = cellBd (r c.i) (r c.i') (α c) (μ c) z)
    (Φ : CellRec T ι → ℝ × ℝ → T)
    (S : ι → ℝ → T)
    (hfr : ∀ {m w : ℝ}, m ∈ Icc 0 1 → w ∈ Icc 0 1 → m = 0 ∨ m = 1 ∨ w = 0 ∨ w = 1 → { re := m, im
      := w } ∈ frontier unitSq)
    (hΦlow : ∀ (c : CellRec T ι) {p : ℝ × ℝ}, p.2 ≤ 1 → Φ c p = ξ c { re := p.1, im := p.2 })
    (hΦhigh : ∀ (c : CellRec T ι) {p : ℝ × ℝ}, ¬p.2 ≤ 1 → Φ c p = rayPoint col pi p.2 (μ c p.1))
    (hSlow : ∀ (k : ι) {w : ℝ}, w ≤ 1 → S k w = r k w)
    (hShigh : ∀ (k : ι) {w : ℝ}, ¬w ≤ 1 → S k w = rayPoint col pi w (t k))
    (hμ0 : ∀ c ∈ F, μ c 0 = t c.i)
    (hz01 : (0 : ℝ) ∈ Icc 0 1)
    (c : CellRec T ι)
    (hc : c ∈ F)
    (w : ℝ)
    (hw : w ∈ Icc 0 2) :
    Φ c (0, w) = S c.i w := by
  by_cases h1 : w ≤ 1
  · rw [hΦlow c h1, hSlow _ h1]
    simp only
    rw [(hξ c hc).2.2.2 _ (hfr hz01 ⟨hw.1, h1⟩ (.inl rfl))]
    exact cellBd_left rfl
  · rw [hΦhigh c h1, hShigh _ h1]
    simp only [hμ0 c hc]

private theorem cuff_box_agrees_on_right_side
    {T : Type u}
    [TopologicalSpace T]
    {ι : Type*}
    {t : ι → T}
    (F : Set (CellRec T ι))
    (col : ℂ → T)
    (pi : T → Circle)
    (r : ι → ℝ → T)
    (μ : CellRec T ι → ℝ → T)
    (α : CellRec T ι → ℝ → T)
    (ξ : CellRec T ι → ℂ → T)
    (hξ : ∀ c ∈ F, ContinuousOn (ξ c) unitSq ∧ InjOn (ξ c) unitSq ∧ ξ c '' unitSq = c.R ∧ ∀ z ∈
      frontier unitSq, ξ c z = cellBd (r c.i) (r c.i') (α c) (μ c) z)
    (Φ : CellRec T ι → ℝ × ℝ → T)
    (S : ι → ℝ → T)
    (hfr : ∀ {m w : ℝ}, m ∈ Icc 0 1 → w ∈ Icc 0 1 → m = 0 ∨ m = 1 ∨ w = 0 ∨ w = 1 → { re := m, im
      := w } ∈ frontier unitSq)
    (hΦlow : ∀ (c : CellRec T ι) {p : ℝ × ℝ}, p.2 ≤ 1 → Φ c p = ξ c { re := p.1, im := p.2 })
    (hΦhigh : ∀ (c : CellRec T ι) {p : ℝ × ℝ}, ¬p.2 ≤ 1 → Φ c p = rayPoint col pi p.2 (μ c p.1))
    (hSlow : ∀ (k : ι) {w : ℝ}, w ≤ 1 → S k w = r k w)
    (hShigh : ∀ (k : ι) {w : ℝ}, ¬w ≤ 1 → S k w = rayPoint col pi w (t k))
    (hμ1 : ∀ c ∈ F, μ c 1 = t c.i')
    (ho01 : (1 : ℝ) ∈ Icc 0 1)
    (c : CellRec T ι)
    (hc : c ∈ F)
    (w : ℝ)
    (hw : w ∈ Icc 0 2) :
    Φ c (1, w) = S c.i' w := by
  by_cases h1 : w ≤ 1
  · rw [hΦlow c h1, hSlow _ h1]
    simp only
    rw [(hξ c hc).2.2.2 _ (hfr ho01 ⟨hw.1, h1⟩ (.inr (.inl rfl)))]
    exact cellBd_right rfl
  · rw [hΦhigh c h1, hShigh _ h1]
    simp only [hμ1 c hc]

/-- **The boxes around one cuff.** -/
theorem exists_cuff_boxes [Finite ι] (hman : ∀ x : T, IsManifoldPoint x) (hD : IsClosedDisc D)
  (hE : IsClosedDisc E) (hΔ : IsClosedDisc Δ) (hDE : D ⊆ E \ discBd E) (hEΔ : E ⊆ Δ \ discBd Δ)
    (hq : ∀ k, IsCrossLine D E (q k) (x k) (t k)) (hdis : ∀ k k', k ≠ k' → Disjoint (q k)
      (q k')) {i₀ i₁ : ι} (hi : i₀ ≠ i₁) :
    ∃ F Φ S μ, IsCellFamily D E q x t univ F ∧ IsCuffBoxes D E Δ q x t F Φ S μ := by
  classical
  obtain ⟨F, hF⟩ := exists_cell_family hman hD hE hDE hq hdis hi
  obtain ⟨pE⟩ := hE.isOArc_discBd
  obtain ⟨col, col', hcc, hcc', hcm, hcm', hcl, hcr, hc1, hc2, hcp⟩ := exists_disc_collar hE hΔ hEΔ
    pE
  have hcinj : InjOn col (closedBall 0 2) := fun a ha b hb he => by
    rw [← hcl ha, ← hcl hb, he]
  have hsph : discBd E ⊆ E := Surface.discBd_subset E
  let pi : T → Circle := fun y => if h : y ∈ discBd E then pE.symm ⟨y, h⟩ else 1
  have hpi : ∀ y (h : y ∈ discBd E), pi y = pE.symm ⟨y, h⟩ := fun y h => dite_eq_left h
  have hpic : ContinuousOn pi (discBd E) := by
    rw [continuousOn_iff_continuous_domRestrict]
    have : (discBd E).domRestrict pi = fun y => pE.symm y := by
      funext y
      exact hpi y.1 y.2
    rw [this]
    exact pE.symm.continuous
  have hpiinj : InjOn pi (discBd E) := fun a ha b hb he => by
    rw [hpi a ha, hpi b hb] at he
    exact congrArg Subtype.val (pE.symm.injective he)
  have hcolp : ∀ y ∈ discBd E, col (pi y : ℂ) = y := fun y hy => by
    rw [hcp, hpi y hy]
    simp
  have hnu : ∀ u : Circle, ‖(u : ℂ)‖ = 1 := fun u => Circle.norm_coe u
  have hmemb : ∀ {w : ℝ} (u : Circle), w ∈ Icc (0 : ℝ) 2 → (w : ℂ) * (u : ℂ) ∈ closedBall (0 : ℂ) 2
    := fun {w} u hw => by
    rw [mem_closedBall_zero_iff, norm_mul, hnu, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hw.1]
    exact hw.2
  have hnm : ∀ {w : ℝ} (u : Circle), 0 ≤ w → ‖(w : ℂ) * (u : ℂ)‖ = w := fun {w} u hw => by
    rw [norm_mul, hnu, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw]
  have hray : ∀ {w w' : ℝ} {u u' : Circle}, w ∈ Icc (0 : ℝ) 2 → w' ∈ Icc (0 : ℝ) 2 → col ((w : ℂ) *
    (u : ℂ)) = col ((w' : ℂ) * (u' : ℂ)) → w = w' ∧ (0 < w → u = u') := fun {w w' u u'} hw hw' he
      => by
    exact collar_ray_eq (T := T) col hcinj hmemb hnm (w := w) (w' := w') (u := u) (u' := u') hw
      hw' he
  have hE' : ∀ {z : ℂ}, z ∈ closedBall (0 : ℂ) 2 → (col z ∈ E ↔ ‖z‖ ≤ 1) := fun {z} hz => by
    rw [← hc1]
    constructor
    · rintro ⟨y, hy, he⟩
      have := hcinj (closedBall_subset_closedBall (by norm_num) hy) hz he
      simpa [this] using hy
    · intro h1
      exact ⟨z, by simpa using h1, rfl⟩
  have hΔ' : ∀ {z : ℂ}, z ∈ closedBall (0 : ℂ) 2 → (col z ∈ discBd Δ ↔ ‖z‖ = 2) := fun {z} hz => by
    rw [← hc2]
    constructor
    · rintro ⟨y, hy, he⟩
      have := hcinj (sphere_subset_closedBall hy) hz he
      simpa [this] using hy
    · intro h1
      exact ⟨z, by simpa using h1, rfl⟩
  have hparE : ∀ {c}, c ∈ F → ∀ {m}, m ∈ Icc (0 : ℝ) 1 → ∀ {μ₀ : ℝ → T}, IsParam c.b (t c.i)
    (t c.i') μ₀ → μ₀ m ∈ discBd E := fun {c} hc {m} hm {μ₀} h1 => by
    have h2 : μ₀ m ∈ c.R ∩ discBd E := by
      rw [(hF.cell c hc).topCap]
      exact h1.mem hm
    exact h2.2
  -- The choices of parametrizations and charts.
  have hlam : ∀ k, ∃ r, IsParam (q k) (x k) (t k) r := fun k => exists_isParam (hq k).line
  choose r hr using hlam
  have hb : ∀ c : CellRec T ι, ∃ μ₀ α, c ∈ F → IsParam c.b (t c.i) (t c.i') μ₀ ∧ IsParam c.a
    (x c.i) (x c.i') α := fun c => by
    by_cases hc : c ∈ F
    · obtain ⟨μ₀, h1⟩ := exists_isParam (hF.cell c hc).top
      obtain ⟨α, h2⟩ := exists_isParam (hF.cell c hc).bottom
      exact ⟨μ₀, α, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨fun _ => x c.i, fun _ => x c.i, fun h => absurd h hc⟩
  choose μ α hμα using hb
  have hξ : ∀ c : CellRec T ι, ∃ ξ : ℂ → T, c ∈ F → ContinuousOn ξ unitSq ∧ InjOn ξ unitSq
    ∧ ξ '' unitSq = c.R ∧ ∀ z ∈ frontier unitSq, ξ z = cellBd (r c.i) (r c.i') (α c) (μ c) z
      := fun c => by
    by_cases hc : c ∈ F
    · obtain ⟨ξ, h1⟩ := exists_cell_chart (hF.cell c hc) (hr c.i) (hr c.i') (hμα c hc).2
        (hμα c hc).1
      exact ⟨ξ, fun _ => h1⟩
    · exact ⟨fun _ => x c.i, fun h => absurd h hc⟩
  choose ξ hξ using hξ
  let Φ : CellRec T ι → ℝ × ℝ → T := fun c => boxMap (ξ c) col pi (μ c)
  let S : ι → ℝ → T := fun k => lineSide col pi (r k) (t k)
  have hsq : ∀ {p : ℝ × ℝ}, p ∈ cuffBox → p.2 ≤ 1 → (⟨p.1, p.2⟩ : ℂ) ∈ unitSq := fun {p} hp h1
    => ⟨hp.1, hp.2.1, h1⟩
  have hfr : ∀ {m w : ℝ}, m ∈ Icc (0 : ℝ) 1 → w ∈ Icc (0 : ℝ) 1 → (m = 0 ∨ m = 1 ∨ w = 0 ∨ w = 1) →
    (⟨m, w⟩ : ℂ) ∈ frontier unitSq := fun h1 h2 h3 => by
    rw [frontier_unitSq]
    exact ⟨⟨h1, h2⟩, h3⟩
  have hΦlow : ∀ c {p : ℝ × ℝ}, p.2 ≤ 1 → Φ c p = ξ c ⟨p.1, p.2⟩ := fun c {p} h1 => ite_eq_left h1
  have hΦhigh : ∀ c {p : ℝ × ℝ}, ¬ p.2 ≤ 1 → Φ c p = rayPoint col pi p.2 (μ c p.1) := fun c {p} h1
    => ite_eq_right h1
  have hSlow : ∀ k {w : ℝ}, w ≤ 1 → S k w = r k w := fun k {w} h1 => ite_eq_left h1
  have hShigh : ∀ k {w : ℝ}, ¬ w ≤ 1 → S k w = rayPoint col pi w (t k) := fun k {w} h1
    => ite_eq_right h1
  have htE : ∀ k, t k ∈ discBd E := fun k => by
    have h1 : t k ∈ q k ∩ discBd E := by
      rw [(hq k).top]
      rfl
    exact h1.2
  have hrD : ∀ k, x k ∈ D := fun k => Surface.discBd_subset _ (hq k).xbd
  have hμ0 : ∀ c ∈ F, μ c 0 = t c.i := fun c hc => (hμα c hc).1.zero
  have hμ1 : ∀ c ∈ F, μ c 1 = t c.i' := fun c hc => (hμα c hc).1.one
  have hz01 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have ho01 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hleft : ∀ c ∈ F, ∀ w ∈ Icc (0 : ℝ) 2, Φ c (0, w) = S c.i w := fun c hc w hw => by
    exact cuff_box_agrees_on_left_side (T := T) (ι := ι) (t := t) F col pi r μ α ξ hξ Φ S hfr
      hΦlow hΦhigh hSlow hShigh hμ0 hz01 c hc w hw
  have hright : ∀ c ∈ F, ∀ w ∈ Icc (0 : ℝ) 2, Φ c (1, w) = S c.i' w := fun c hc w hw => by
    exact cuff_box_agrees_on_right_side (T := T) (ι := ι) (t := t) F col pi r μ α ξ hξ Φ S hfr
      hΦlow hΦhigh hSlow hShigh hμ1 ho01 c hc w hw
  have htop : ∀ c ∈ F, ∀ m ∈ Icc (0 : ℝ) 1, Φ c (m, 1) = μ c m := fun c hc m hm => by
    rw [hΦlow c le_rfl]
    simp only
    rw [(hξ c hc).2.2.2 _ (hfr hm ho01 (.inr (.inr (.inr rfl))))]
    exact cellBd_high (hr _) (hr _) (hμα c hc).1 rfl
  have hR : ∀ c ∈ F, ∀ p ∈ cuffBox, p.2 ≤ 1 → Φ c p ∈ c.R := fun c hc p hp h1 => by
    rw [hΦlow c h1, ← (hξ c hc).2.2.1]
    exact mem_image_of_mem _ (hsq hp h1)
  have hRE : ∀ c ∈ F, c.R ⊆ E := fun c hc => (hF.cell c hc).subE
  have hmemray : ∀ w y, rayPoint col pi w y = col ((w : ℂ) * (pi y : ℂ)) := fun _ _ => rfl
  have hμE : ∀ c ∈ F, ∀ m ∈ Icc (0 : ℝ) 1, μ c m ∈ discBd E := fun c hc m hm => hparE hc hm
    (hμα c hc).1
  have hinE : ∀ c ∈ F, ∀ p ∈ cuffBox, Φ c p ∈ E ↔ p.2 ≤ 1 := fun c hc p hp => by
    by_cases h1 : p.2 ≤ 1
    · exact ⟨fun _ => h1, fun _ => hRE c hc (hR c hc p hp h1)⟩
    · rw [hΦhigh c h1, hmemray, hE' (hmemb _ hp.2), hnm _ hp.2.1]
  have hoff : ∀ c ∈ F, ∀ p ∈ cuffBox, ¬ p.2 ≤ 1 → Φ c p ∉ E := fun c hc p hp h1 h2 => h1
    ((hinE c hc p hp).mp h2)
  have hinj : ∀ c ∈ F, InjOn (Φ c) cuffBox := fun c hc p hp p' hp' he => by
    exact cuff_box_injective (T := T) (ι := ι) (E := E) (x := x) (t := t) F col pi hpiinj hray r μ
      α hμα ξ hξ Φ hsq hΦlow hΦhigh hR hRE hmemray hμE hinE c hc p hp p' hp' he
  have hsideE : ∀ c ∈ F, ∀ k, (k = c.i ∨ k = c.i') → ∃ e : ℝ, (e = 0 ∨ e = 1) ∧ ∀ w ∈ Icc
    (0 : ℝ) 2, Φ c (e, w) = S k w := fun c hc k hk => by
    rcases hk with rfl | rfl
    · exact ⟨0, .inl rfl, hleft c hc⟩
    · exact ⟨1, .inr rfl, hright c hc⟩
  have hSmem : ∀ k, ∀ w ∈ Icc (0 : ℝ) 1, S k w ∈ q k := fun k w hw => by
    rw [hSlow k hw.2]
    exact (hr k).mem hw
  have hSof : ∀ k, ∀ y ∈ q k, ∃ w ∈ Icc (0 : ℝ) 1, S k w = y := fun k y hy => by
    obtain ⟨w, hw, rfl⟩ := (hr k).exists_of_mem hy
    exact ⟨w, hw, hSlow k hw.2⟩
  have hS1 : ∀ k, S k 1 = t k := fun k => by
    rw [hSlow k le_rfl]
    exact (hr k).one
  have hS0 : ∀ k, S k 0 = x k := fun k => by
    rw [hSlow k zero_le_one]
    exact (hr k).zero
  have hrE : ∀ k, ∀ w ∈ Icc (0 : ℝ) 1, r k w ∈ E := fun k w hw => (hq k).sub ((hr k).mem hw)
  have hSinj : ∀ k, InjOn (S k) (Icc 0 2) := fun k w hw w' hw' he => by
    exact cuff_side_injective (T := T) (ι := ι) (E := E) (q := q) (x := x) (t := t) col pi hmemb
      hnm hray hE' r hr S hSlow hShigh hmemray hrE k w hw w' hw' he
  have hboxe : ∀ {e w : ℝ}, (e = 0 ∨ e = 1) → w ∈ Icc (0 : ℝ) 2 → (e, w) ∈ cuffBox
    := fun {e w} h1 h2 => by
    refine ⟨?_, h2⟩
    rcases h1 with rfl | rfl
    · exact hz01
    · exact ho01
  have hcont : ∀ c ∈ F, ContinuousOn (Φ c) cuffBox := fun c hc => by
    exact cuff_box_continuous (T := T) (ι := ι) (E := E) (x := x) (t := t) F col hcc pi hpic hcolp
      hmemb r μ α hμα ξ hξ Φ hsq hΦlow hΦhigh htop hμE c hc
  have hmeet : ∀ c ∈ F, ∀ c' ∈ F, ∀ p p', p ∈ cuffBox → p' ∈ cuffBox → Φ c p = Φ c' p' → (c = c'
    ∧ p = p') ∨ (p.2 = p'.2 ∧ (p.1 = 0 ∨ p.1 = 1) ∧ (p'.1 = 0 ∨ p'.1 = 1) ∧ ∀ w ∈ Icc
      (0 : ℝ) 2, Φ c (p.1, w) = Φ c' (p'.1, w)) := fun c hc c' hc' p p' hp hp' he => by
    exact cuff_boxes_overlap_on_sides (T := T) (ι := ι) (D := D) (E := E) (q := q) (x := x) (t :=
      t) hq F hF col pi hpiinj hray μ Φ S hΦhigh hShigh htop hR hRE hmemray hμE hinE hinj hsideE
      hSof hboxe c hc c' hc' p p' hp hp' he
  have hbd : ∀ c ∈ F, ∀ p ∈ cuffBox, Φ c p ∈ discBd E ↔ p.2 = 1 := fun c hc p hp => by
    exact cuff_box_meets_middle_boundary (T := T) (ι := ι) (D := D) (E := E) (q := q) (x := x) (t
      := t) F hF hsph μ α hμα Φ htop hR hμE hinE hinj c hc p hp
  have hlow0 : ∀ c ∈ F, ∀ m ∈ Icc (0 : ℝ) 1, Φ c (m, 0) = α c m := fun c hc m hm => by
    rw [hΦlow c zero_le_one]
    simp only
    rw [(hξ c hc).2.2.2 _ (hfr hm hz01 (.inr (.inr (.inl rfl))))]
    exact cellBd_low (hr _) (hr _) (hμα c hc).2 rfl
  have haD : ∀ c ∈ F, ∀ {y}, y ∈ c.a → y ∈ D := fun c hc {y} hy => Surface.discBd_subset _
    ((hF.cell c hc).aBd hy)
  have hin0 : ∀ c ∈ F, ∀ p ∈ cuffBox, Φ c p ∈ D ↔ p.2 = 0 := fun c hc p hp => by
    exact cuff_box_mem_inner_disc (T := T) (ι := ι) (D := D) (E := E) (q := q) (x := x) (t := t)
      hDE F hF μ α hμα Φ hR hinE hinj hlow0 haD c hc p hp
  have hinΔ : ∀ c ∈ F, ∀ p ∈ cuffBox, Φ c p ∈ discBd Δ ↔ p.2 = 2 := fun c hc p hp => by
    by_cases h1 : p.2 ≤ 1
    · refine ⟨fun h2 => absurd h2 (hEΔ (hRE c hc (hR c hc p hp h1))).2, fun h2 => ?_⟩
      linarith
    · rw [hΦhigh c h1, hmemray, hΔ' (hmemb _ hp.2), hnm _ hp.2.1]
  have hmaps : ∀ c ∈ F, MapsTo (Φ c) cuffBox Δ := fun c hc p hp => by
    by_cases h1 : p.2 ≤ 1
    · exact (hEΔ (hRE c hc (hR c hc p hp h1))).1
    · rw [hΦhigh c h1, hmemray]
      exact hcm (hmemb _ hp.2)
  have hcover : ∀ y ∈ Δ \ discInt D, ∃ c ∈ F, ∃ p ∈ cuffBox, Φ c p = y := fun y hy => by
    exact cuff_boxes_cover_annulus (T := T) (ι := ι) (D := D) (E := E) (Δ := Δ) (q := q) (x := x)
      (t := t) F hF pE col col' hcm' hcr pi hpi hE' r μ α hμα ξ hξ Φ hΦlow hΦhigh hmemray hlow0 y
      hy
  exact ⟨F, Φ, S, μ, hF, hcont, hinj, hmaps, hSinj, hleft, hright, htop,
    fun c hc => (hμα c hc).1, hSmem, hSof, hS1, hS0, hinE, hR, hbd, hin0, hinΔ, hcover, hmeet⟩

end GraphMinor.GM07
