/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.SideEnds
public import LeanPool.GraphMinor.GM19.CapOrient

/-!
# The order of the ends around a cuff

The pad of a cuff `Θ` is the disc pasted onto it. We rotate a chart of the pad so that a vertex of
the frame sits at the point `1` of the circle, and read each side by an interval of `[0, 1]`
(`exists_side_lift`). Different sides have intervals that do not overlap, and along one side the
vertices come in the order of the ends (`IsMatchSetting.lineCoord_endVertex_le`). So the order data
of the pad
hold for any parametrization of the disc of the cuff that has the cyclic order of the chart
(`exists_cuff_padOrder`). This is the part of step (2) of the proof of Graph Minors XIX, (15.2),
page 381, about
border edges.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Metric Topology GraphMinor.Surface GraphMinor.GM11

universe w

local notation "𝕀" => unitInterval

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
  {cap : IsCappedSurface S Shat} {β : Type w} {χ : ColourScheme S β}

/-- Rotate a chart of a disc. -/
theorem chart_rotate {T : Type} [TopologicalSpace T] {C : Set T} {c : T → ℂ} {g : ℂ → T}
    (h : IsChart C c g) (u : Circle) :
    IsChart C (fun x => (u : ℂ)⁻¹ * c x) (fun z => g ((u : ℂ) * z)) := by
  have hu : (u : ℂ) ≠ 0 := Circle.coe_ne_zero u
  have hn : ∀ z : ℂ, ‖(u : ℂ) * z‖ = ‖z‖ := fun z => by rw [norm_mul, Circle.norm_coe, one_mul]
  have hn' (z : ℂ) : ‖(u : ℂ)⁻¹ * z‖ = ‖z‖ := by
    rw [norm_mul, norm_inv, Circle.norm_coe, inv_one, one_mul]
  refine ⟨continuousOn_const.mul h.hc, h.gc.comp (continuousOn_const.mul continuousOn_id) fun z hz
    => ?_, fun x hx => ?_, fun z hz => h.gm ?_, fun x hx => ?_, fun z hz => ?_, ?_⟩
  · simpa [hn] using hz
  · have := h.hm hx
    simpa [hn'] using this
  · simpa [hn] using hz
  · show g ((u : ℂ) * ((u : ℂ)⁻¹ * c x)) = x
    rw [mul_inv_cancel_left₀ hu]
    exact h.gh hx
  · have hz' : (u : ℂ) * z ∈ closedBall (0 : ℂ) 1 := by simpa [hn] using hz
    change (u : ℂ)⁻¹ * c (g ((u : ℂ) * z)) = z
    rw [h.hg hz', inv_mul_cancel_left₀ hu]
  · ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      have : c x ∈ sphere (0 : ℂ) 1 := by rw [← h.bd]; exact mem_image_of_mem c hx
      have h1 : ‖c x‖ = 1 := by simpa using this
      simp [h1]
    · intro hz
      have hz1 : ‖z‖ = 1 := by simpa using hz
      have : (u : ℂ) * z ∈ c '' discBd C := by
        rw [h.bd]
        simp [hz1]
      obtain ⟨x, hx, he⟩ := this
      refine ⟨x, hx, ?_⟩
      change (u : ℂ)⁻¹ * c x = z
      rw [he, inv_mul_cancel_left₀ hu]

/-- The point of the circle at a point of the plane off `0`. -/
noncomputable def toCircle (z : ℂ) : Circle := open Classical in if h : z = 0 then 1 else unitOf z h

theorem coe_toCircle {z : ℂ} (hz : ‖z‖ = 1) : (toCircle z : ℂ) = z := by
  have h0 : z ≠ 0 := fun h => by simp [h] at hz
  rw [toCircle, dite_eq_right h0, coe_unitOf, hz]
  simp

theorem continuousOn_toCircle : ContinuousOn toCircle {z | z ≠ 0} := by
  rw [continuousOn_iff_continuous_domRestrict]
  have : ({z : ℂ | z ≠ 0}).domRestrict toCircle = fun z : {z : ℂ // z ≠ 0} => unitOf z.1 z.2 := by
    funext z
    change toCircle z.1 = _
    rw [toCircle, dite_eq_right z.2]
  rw [this]
  exact continuous_unitOf

theorem Frame.exists_vertex_of_side (hS : IsSurface S) {Φ : Frame S} {s Θ : Set S}
  (hs : s ∈ Φ.sides) (hΘ : Θ ∈ cuffs S) (hsΘ : s ⊆ Θ) : ∃ n ∈ Φ.V, n ∈ Θ := by
  by_contra hno
  push Not at hno
  have hO : IsOArc Θ := (cuff_statement S hS).2.2 _ hΘ
  have hcl : IsClosed Θ := hO.isCompact.isClosed
  have hpc : IsPathConnected Θ := by
    obtain ⟨f⟩ := hO
    have : Θ = range fun w : Circle => (f w).1 := by
      ext x
      exact ⟨fun hx => ⟨f.symm ⟨x, hx⟩, by simp⟩, fun ⟨w, hw⟩ => hw ▸ (f w).2⟩
    rw [this]
    exact isPathConnected_range (continuous_subtype_val.comp f.continuous)
  have hsub : Θ ⊆ bd S \ Φ.V := fun x hx => ⟨cuff_subset_bd ⟨Θ, hΘ⟩ hx, fun hv => hno x hv hx⟩
  have he : Θ = s := hs.2.2.2 Θ hsub hpc hsΘ
  have ht : tilde s = ∅ := by
    rw [tilde, ← he, hcl.closure_eq, sdiff_self]
  have h2 := (Φ.side_shape s hs).1
  rw [ht, ncard_empty] at h2
  omega

/-- A side of a cuff, read by an interval of `[0, 1]`. -/
theorem Frame.exists_side_pos (Φ : Frame S) {s Θ : Set S} (hs : s ∈ Φ.sides)
  (hsΘ : closure s ⊆ Θ) {κ : S → Circle} (hκc : ContinuousOn κ Θ) (hκi : InjOn κ Θ)
    (hκ1 : ∀ x ∈ s, κ x ≠ 1) :
    ∃ (u w : S) (σ : 𝕀 ≃ₜ closure s) (l : ℝ → ℝ), Φ.γ s = [u, w] ∧ (σ 0).1 = u ∧ (σ 1).1 = w
      ∧ ContinuousOn l (Icc 0 1) ∧ (StrictMonoOn l (Icc 0 1) ∨ StrictAntiOn l (Icc 0 1)) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, l t ∈ Icc (0 : ℝ) 1 ∧ ee (l t) = κ (linePoint σ t)) ∧ ∀ t ∈ Ioo
        (0 : ℝ) 1, linePoint σ t ∈ s := by
  obtain ⟨u, w, hγ, f, h0, h1⟩ := Φ.exists_march hs
  have hset : tilde s = {u, w} := by
    rw [← Φ.γ_set s hs, hγ]
    ext x
    simp
  have hint : ∀ t ∈ Ioo (0 : ℝ) 1, linePoint f t ∈ s := fun t ht => by
    by_contra hn
    have hx : linePoint f t ∈ tilde s := ⟨linePoint_mem f t, hn⟩
    rw [hset] at hx
    have hl : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
    rcases hx with hx | hx
    · have h2 : linePoint f t = linePoint f 0 := by
        rw [hx, ← h0]
        simp [linePoint]
      have := injOn_linePoint f hl (left_mem_Icc.mpr zero_le_one) h2
      linarith [ht.1]
    · have h2 : linePoint f t = linePoint f 1 := by
        rw [show linePoint f t = w from hx, ← h1]
        simp [linePoint]
      have := injOn_linePoint f hl (right_mem_Icc.mpr zero_le_one) h2
      linarith [ht.2]
  have hc : ContinuousOn (fun t => κ (linePoint f t)) (Icc 0 1) := hκc.comp
    (continuous_linePoint f).continuousOn fun t _ => hsΘ (linePoint_mem f t)
  have hi : InjOn (fun t => κ (linePoint f t)) (Icc 0 1) := fun a ha b hb he
    => injOn_linePoint f ha hb (hκi (hsΘ (linePoint_mem f a)) (hsΘ (linePoint_mem f b)) he)
  obtain ⟨l, hl1, hl2, hl3⟩ := exists_side_lift hc hi fun t ht => hκ1 _ (hint t ht)
  exact ⟨u, w, f, l, hγ, h0, h1, hl1, hl2, hl3, hint⟩

namespace TangleDatum

variable {D : TangleDatum cap χ} {P₀ : ColouredPainting χ} {n : ℕ} {b : Set S → Set S}

/-- **The order data of a cuff.** After a rotation of the chart, the order data of the pad of `Θ`
hold for each parametrization `q` whose cyclic order on the ends is the cyclic order of the chart.
-/
theorem IsMatchSetting.exists_cuff_padOrder [Nonempty S] (hM : D.IsMatchSetting P₀ n b)
  (hS : IsSurface S) {Θ : Set S} (hΘ : Θ ∈ cuffs S) {c : Shat → ℂ} {g : ℂ → Shat} (hch : IsChart
    (closure (cap.cuffDisc Θ)) c g) :
    ∃ (c' : Shat → ℂ) (g' : ℂ → Shat), IsChart (closure (cap.cuffDisc Θ)) c' g' ∧ ∀ q : Circle
      → Shat, Function.Injective q → cap.emb '' cuffEnds P₀ b Θ ⊆ range q →
      (∀ a a' a'', q a ∈ cap.emb '' cuffEnds P₀ b Θ → q a' ∈ cap.emb '' cuffEnds P₀ b Θ
        → q a'' ∈ cap.emb '' cuffEnds P₀ b Θ → a ≠ a' → a' ≠ a'' → a ≠ a'' →
        (CircleCyclic a a' a'' ↔ CircleCyclic (toCircle (c' (q a))) (toCircle (c' (q a')))
          (toCircle (c' (q a''))))) →
      ∃ A U : Shat → ℝ, PadOrder q g' (cap.emb '' cuffEnds P₀ b Θ) (fun x => cap.emb
        (endVertex P₀ D.P b (capBack cap x))) A U := by
  classical
  let Y := cuffEnds P₀ b Θ
  by_cases hY : Y.Nonempty
  swap
  · refine ⟨c, g, hch, fun q _ _ _ => ⟨0, 0, ?_⟩⟩
    have hE : ∀ x, x ∉ cap.emb '' cuffEnds P₀ b Θ := by
      rintro _ ⟨y, hy, rfl⟩
      exact hY ⟨y, hy⟩
    exact ⟨(hM.finite_cuffEnds Θ).image _, fun x hx => absurd hx (hE x), fun x hx => absurd hx
      (hE x), fun x hx => absurd hx (hE x), fun x hx => absurd hx (hE x), fun x hx => absurd hx
        (hE x),
      fun x hx => absurd hx (hE x), fun a _ _ ha => absurd ha (hE _)⟩
  obtain ⟨y₀, e₀, he₀, heΘ, hy₀⟩ := hY
  obtain ⟨s₀, hs₀, hs₀Θ, -⟩ := exists_side_of_cuffEnds hS hM.edge hΘ he₀ heΘ
  obtain ⟨n₀, hn₀, hn₀Θ⟩ := Frame.exists_vertex_of_side hS hs₀ hΘ hs₀Θ
  have hcl : IsClosed Θ := ((cuff_statement S hS).2.2 _ hΘ).isCompact.isClosed
  have hCbd : discBd (closure (cap.cuffDisc Θ)) = cap.emb '' Θ := cap.cuffDisc_bd Θ hΘ
  have hΘC : ∀ x ∈ Θ, cap.emb x ∈ discBd (closure (cap.cuffDisc Θ)) := by
    intro x hx
    rw [hCbd]
    exact mem_image_of_mem _ hx
  have hnorm : ∀ (c₁ : Shat → ℂ) (g₁ : ℂ → Shat), IsChart (closure (cap.cuffDisc Θ)) c₁ g₁
    → ∀ x ∈ Θ, ‖c₁ (cap.emb x)‖ = 1 := fun c₁ g₁ h₁ x hx => by
    have : c₁ (cap.emb x) ∈ sphere (0 : ℂ) 1 := by rw [← h₁.bd]; exact mem_image_of_mem _ (hΘC x hx)
    simpa using this
  let u : Circle := toCircle (c (cap.emb n₀))
  have hu : (u : ℂ) = c (cap.emb n₀) := coe_toCircle (hnorm _ _ hch n₀ hn₀Θ)
  have hch' := chart_rotate hch u
  refine ⟨_, _, hch', fun q hqinj hsub hcyc => ?_⟩
  let c' : Shat → ℂ := fun x => (u : ℂ)⁻¹ * c x
  let g' : ℂ → Shat := fun z => g ((u : ℂ) * z)
  have hch'' : IsChart (closure (cap.cuffDisc Θ)) c' g' := hch'
  let κ : S → Circle := fun x => toCircle (c' (cap.emb x))
  have hκe : ∀ x ∈ Θ, (κ x : ℂ) = c' (cap.emb x) := fun x hx => coe_toCircle (hnorm _ _ hch'' x hx)
  have hΘS : ∀ x ∈ Θ, cap.emb x ∈ closure (cap.cuffDisc Θ) := fun x hx => Surface.discBd_subset _
    (hΘC x hx)
  have hκc : ContinuousOn κ Θ := by
    refine continuousOn_toCircle.comp (hch''.hc.comp cap.isEmbedding.continuous.continuousOn hΘS)
      fun x hx => ?_
    have := hnorm _ _ hch'' x hx
    intro h0
    rw [show c' (cap.emb x) = 0 from h0] at this
    simp at this
  have hκi : InjOn κ Θ := fun x hx y hy he => by
    have h1 : c' (cap.emb x) = c' (cap.emb y) := by rw [← hκe x hx, ← hκe y hy, he]
    have h2 : cap.emb x = cap.emb y := by rw [← hch''.gh (hΘS x hx), ← hch''.gh (hΘS y hy), h1]
    exact cap.isEmbedding.injective h2
  have hκn : κ n₀ = 1 := by
    apply Circle.ext
    rw [hκe n₀ hn₀Θ]
    change (u : ℂ)⁻¹ * c (cap.emb n₀) = _
    rw [← hu, inv_mul_cancel₀ (Circle.coe_ne_zero u)]
    rfl
  let Sd := {s : Set S // s ∈ χ.Φ.sides ∧ s ⊆ Θ}
  have hsd : ∀ s : Sd, _ := fun s : Sd => χ.Φ.exists_side_pos s.2.1 (closure_minimal s.2.2 hcl) hκc
    hκi fun x hx he => (s.2.1.2.1 hx).2 ((hκi (s.2.2 hx) hn₀Θ (he.trans hκn.symm)) ▸ hn₀)
  choose uu ww σ l hγ h0 h1 hlc hlm hl hint using hsd
  let pos : Sd → S → ℝ := fun s x => l s (lineCoord (σ s) x)
  have hpos : ∀ (s : Sd), ∀ x ∈ closure s.1, pos s x ∈ Icc (0 : ℝ) 1 ∧ ee (pos s x) = κ x
    := fun s x hx => by
    have := hl s _ (lineCoord_mem (σ s) x)
    rwa [linePoint_coord (σ s) hx] at this
  have hend : ∀ y : {y // y ∈ Y}, ∃ s : Sd, ∃ e ∈ P₀.Γ.E, e ⊆ s.1 ∧ b e ⊆ s.1 ∧
    (s.1 ∉ χ.Φ.longSides → b e = s.1) ∧ y.1 ∈ tilde (b e) := fun y => by
    obtain ⟨e, he, heΘ, hy⟩ := y.2
    obtain ⟨s, hs, hsΘ, h1, h2, h3⟩ := exists_side_of_cuffEnds hS hM.edge hΘ he heΘ
    exact ⟨⟨s, hs, hsΘ⟩, e, he, h1, h2, h3, hy⟩
  choose sd ed hed hes hbs hsh hyt using hend
  have hyc : ∀ y : {y // y ∈ Y}, y.1 ∈ closure (sd y).1 := fun y => closure_mono (hbs y) (hyt y).1
  have hvc : ∀ y : {y // y ∈ Y}, endVertex P₀ D.P b y.1 ∈ closure (sd y).1 := fun y => by
    obtain ⟨v, hv, hv'⟩ := exists_isEndOf hM.edge (hed y) (hyt y)
    rw [hM.endVertex_eq hS hv']
    exact closure_mono (hes y) hv.1
  let A₀ : S → ℝ := fun y => if h : y ∈ Y then pos (sd ⟨y, h⟩) y else 0
  let U₀ : S → ℝ := fun y => if h : y ∈ Y then pos (sd ⟨y, h⟩) (endVertex P₀ D.P b y) else 0
  have hA₀ : ∀ y : {y // y ∈ Y}, A₀ y.1 = pos (sd y) y.1 := fun y => dite_eq_left y.2
  have hU₀ : ∀ y : {y // y ∈ Y}, U₀ y.1 = pos (sd y) (endVertex P₀ D.P b y.1) := fun y
    => dite_eq_left y.2
  have hee : ∀ y : {y // y ∈ Y}, ee (A₀ y.1) = κ y.1 := by
    intro y
    rw [hA₀]
    exact (hpos _ _ (hyc y)).2
  have hYΘ : ∀ y ∈ Y, y ∈ Θ := fun y hy => (hM.cuffEnds_subset hS hΘ hy).1
  have hinj : ∀ y y' : {y // y ∈ Y}, A₀ y.1 = A₀ y'.1 → y.1 = y'.1 := fun y y' he => hκi
    (hYΘ _ y.2) (hYΘ _ y'.2) (by rw [← hee, ← hee, he])
  have hwin : ∀ y y' : {y // y ∈ Y}, y.1 ≠ y'.1 → A₀ y.1 < A₀ y'.1 + 1 := fun y y' hne => by
    by_contra hn
    have h1' : A₀ y.1 ∈ Icc (0 : ℝ) 1 := by rw [hA₀]; exact (hpos _ _ (hyc y)).1
    have h2' : A₀ y'.1 ∈ Icc (0 : ℝ) 1 := by rw [hA₀]; exact (hpos _ _ (hyc y')).1
    have e1 : A₀ y.1 = 1 := le_antisymm h1'.2 (by linarith [h2'.1])
    have e2 : A₀ y'.1 = 0 := le_antisymm (by linarith [h1'.2]) h2'.1
    refine hne (hκi (hYΘ _ y.2) (hYΘ _ y'.2) ?_)
    rw [← hee, ← hee, e1, e2]
    simp [ee]
  have hback : ∀ {y}, capBack cap (cap.emb y) = y := fun {y} => capBack_emb cap y
  refine ⟨fun x => A₀ (capBack cap x), fun x => U₀ (capBack cap x),
    (hM.finite_cuffEnds Θ).image _, hsub, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    show A₀ (capBack cap (cap.emb y)) ∈ _
    rw [hback, hA₀ ⟨y, hy⟩]
    exact (hpos _ _ (hyc ⟨y, hy⟩)).1
  · rintro _ ⟨y, hy, rfl⟩
    show U₀ (capBack cap (cap.emb y)) ∈ _
    rw [hback, hU₀ ⟨y, hy⟩]
    exact (hpos _ _ (hvc ⟨y, hy⟩)).1
  · rintro _ ⟨y, hy, rfl⟩
    change g' (ee (U₀ (capBack cap (cap.emb y)))) = cap.emb (endVertex P₀ D.P b (capBack cap
      (cap.emb y)))
    rw [hback, hU₀ ⟨y, hy⟩, (hpos _ _ (hvc ⟨y, hy⟩)).2]
    have hv := hvc ⟨y, hy⟩
    have hvΘ : endVertex P₀ D.P b y ∈ Θ := closure_minimal (sd ⟨y, hy⟩).2.2 hcl hv
    rw [hκe _ hvΘ]
    exact hch''.gh (hΘS _ hvΘ)
  · rintro _ ⟨y, hy, rfl⟩ _ ⟨y', hy', rfl⟩ hlt
    show U₀ (capBack cap (cap.emb y)) ≤ U₀ (capBack cap (cap.emb y'))
    change A₀ (capBack cap (cap.emb y)) < A₀ (capBack cap (cap.emb y')) at hlt
    rw [hback, hback] at hlt ⊢
    let Y₁ : {y // y ∈ Y} := ⟨y, hy⟩
    let Y₂ : {y // y ∈ Y} := ⟨y', hy'⟩
    rw [hA₀ Y₁, hA₀ Y₂] at hlt
    rw [hU₀ Y₁, hU₀ Y₂]
    by_cases hss : sd Y₁ = sd Y₂
    · have e₂ := hes Y₂
      have b₂ := hbs Y₂
      have s₂ := hsh Y₂
      have u₂ := hvc Y₂
      have y₂ := hyc Y₂
      rw [← hss] at e₂ b₂ s₂ u₂ y₂
      rw [show pos (sd Y₂) y' = pos (sd Y₁) y' by rw [hss]] at hlt
      rw [show pos (sd Y₂) (endVertex P₀ D.P b y') =
        pos (sd Y₁) (endVertex P₀ D.P b y') by rw [hss]]
      set s := sd Y₁
      have hc1 := lineCoord_mem (σ s) y
      have hc2 := lineCoord_mem (σ s) y'
      have hc3 := lineCoord_mem (σ s) (endVertex P₀ D.P b y)
      have hc4 := lineCoord_mem (σ s) (endVertex P₀ D.P b y')
      have key : ∀ {x x' : {y // y ∈ Y}}, (x = Y₁ ∧ x' = Y₂ ∨ x = Y₂ ∧ x' = Y₁) → lineCoord
        (σ s) x.1 < lineCoord (σ s) x'.1 → lineCoord (σ s) (endVertex P₀ D.P b x.1) ≤ lineCoord
          (σ s) (endVertex P₀ D.P b x'.1) := by
        rintro x x' (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) h
        · exact hM.lineCoord_endVertex_le hS s.2.1 (hγ s) (σ s) (h0 s) (h1 s) hΘ s.2.2 (hed _)
            (hed _) (hes _) e₂ (hbs _) b₂ (hsh _) s₂ (hyt _) (hyt _) h
        · exact hM.lineCoord_endVertex_le hS s.2.1 (hγ s) (σ s) (h0 s) (h1 s) hΘ s.2.2 (hed _)
            (hed _) e₂ (hes _) b₂ (hbs _) s₂ (hsh _) (hyt _) (hyt _) h
      rcases hlm s with hm | hm
      · have h3 : lineCoord (σ s) y < lineCoord (σ s) y' := (hm.lt_iff_lt hc1 hc2).mp hlt
        exact hm.monotoneOn hc3 hc4 (key (Or.inl ⟨rfl, rfl⟩) h3)
      · have h3 : lineCoord (σ s) y' < lineCoord (σ s) y := (hm.lt_iff_gt hc1 hc2).mp hlt
        exact hm.antitoneOn hc4 hc3 (key (Or.inr ⟨rfl, rfl⟩) h3)
    · by_contra hn
      refine false_of_overlap (hlc (sd Y₁)) (hlc (sd Y₂)) (hlm _) (hlm _) (fun t ht =>
        (hl _ t ht).2) (fun t ht => (hl _ t ht).2) (fun t ht t' ht' he => ?_) (lineCoord_mem _ _)
          (lineCoord_mem _ _)
        (lineCoord_mem _ _) (lineCoord_mem _ _) hlt (not_le.mp hn)
      have h1' := hint (sd Y₁) t ht
      have h2' := hint (sd Y₂) t' ht'
      have heq := hκi ((sd Y₁).2.2 h1') ((sd Y₂).2.2 h2') he
      rw [heq] at h1'
      exact hss (Subtype.ext (arcComponent_eq (sd Y₁).2.1 (sd Y₂).2.1 h1' h2'))
  · rintro _ ⟨y, hy, rfl⟩ _ ⟨y', hy', rfl⟩ he
    have he' : A₀ y = A₀ y' := by
      have : A₀ (capBack cap (cap.emb y)) = A₀ (capBack cap (cap.emb y')) := he
      rwa [hback, hback] at this
    rw [show y = y' from hinj ⟨y, hy⟩ ⟨y', hy'⟩ he']
  · intro a a' a'' ha ha' ha'' h1' h2' h3'
    rw [hcyc a a' a'' ha ha' ha'' h1' h2' h3']
    obtain ⟨y, hy, hye⟩ := ha
    obtain ⟨y', hy', hye'⟩ := ha'
    obtain ⟨y'', hy'', hye''⟩ := ha''
    have hne : ∀ {p p' : Circle} {r r' : S}, cap.emb r = q p → cap.emb r' = q p' → p ≠ p' → r ≠ r'
      := fun e1 e2 hp h => hp (hqinj (by rw [← e1, ← e2, h]))
    have n1 := hne hye hye' h1'
    have n2 := hne hye' hye'' h2'
    have n3 := hne hye hye'' h3'
    have hval : ∀ {p : Circle} {r : S} (hr : r ∈ Y), cap.emb r = q p → A₀ (capBack cap (q p))
      = A₀ r ∧ toCircle (c' (q p)) = ee (A₀ r) := fun {p r} hr he => by
      rw [← he, hback]
      exact ⟨rfl, (hee ⟨r, hr⟩).symm⟩
    obtain ⟨v1, w1⟩ := hval hy hye
    obtain ⟨v2, w2⟩ := hval hy' hye'
    obtain ⟨v3, w3⟩ := hval hy'' hye''
    rw [w1, w2, w3]
    change _ ↔ CycOrder (A₀ (capBack cap (q a))) (A₀ (capBack cap (q a'))) (A₀ (capBack cap
      (q a'')))
    rw [v1, v2, v3]
    let Y₁ : {y // y ∈ Y} := ⟨y, hy⟩
    let Y₂ : {y // y ∈ Y} := ⟨y', hy'⟩
    let Y₃ : {y // y ∈ Y} := ⟨y'', hy''⟩
    exact circleCyclic_ee_iff (hwin Y₁ Y₂ n1) (hwin Y₂ Y₁ n1.symm) (hwin Y₂ Y₃ n2)
      (hwin Y₃ Y₂ n2.symm) (hwin Y₁ Y₃ n3) (hwin Y₃ Y₁ n3.symm) (fun h => n1 (hinj Y₁ Y₂ h)) (fun h
        => n2 (hinj Y₂ Y₃ h))
      (fun h => n3 (hinj Y₁ Y₃ h))

end TangleDatum

end GraphMinor.GM19
