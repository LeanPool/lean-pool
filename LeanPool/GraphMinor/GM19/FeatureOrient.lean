/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section4b
public import LeanPool.GraphMinor.GM19.CircleLift
public import LeanPool.GraphMinor.GM19.FeatureDissect
public import LeanPool.GraphMinor.GM17.PasteCuff

/-!
# Two orientations of a connected surface are equal or opposite

A homeomorphism of a connected surface either keeps every orientation or reverses every orientation.
This costs at most a factor of
two in (5.2). A homeomorphism of the circle keeps all cyclic orders or reverses all of them, so two
orientations are equal or opposite on
each closed disc (`disc_sign`). Two nested discs with three common boundary points have the same
sign (`sign_of_common`). A disc inside
the interior of another is compared by a chord that runs along its boundary (`sign_of_inner`). Then
the discs with sign plus and the
discs with sign minus split the interior of the surface into two open sets, and this interior is
connected (`isPreconnected_compl_bd`).
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology Function Metric GraphMinor.Surface

universe u

local notation "𝕀" => unitInterval

theorem circle_angle_unique {s t : ℝ} (hs0 : 0 < s) (hs1 : s < 2 * Real.pi) (ht0 : 0 < t)
  (ht1 : t < 2 * Real.pi)
    (h : Circle.exp s = Circle.exp t) : s = t :=
  CircleOrder.exp_eq_of_angles hs0 hs1 ht0 ht1 h

theorem cyclic_not_swap {a b c : Circle} (h : CircleCyclic a b c) : ¬ CircleCyclic a c b :=
  CircleOrder.not_circleCyclic_both h

/-- The cyclic order after a lift that goes up. -/
theorem cyclic_of_mono {τ : Circle ≃ₜ Circle} {L : ℝ → ℝ} (hc : Continuous L) (hm : StrictMono L)
    (hl : ∀ t, τ (Circle.exp t) = Circle.exp (L t)) {a b c : Circle} (h : CircleCyclic a b c) :
    CircleCyclic (τ a) (τ b) (τ c) :=
  CircleCyclic.map_increasing_lift hc hm hl h

/-- The cyclic order after a lift that goes down. -/
theorem cyclic_of_anti {τ : Circle ≃ₜ Circle} {L : ℝ → ℝ} (hc : Continuous L) (hm : StrictAnti L)
    (hl : ∀ t, τ (Circle.exp t) = Circle.exp (L t)) {a b c : Circle} (h : CircleCyclic a b c) :
    CircleCyclic (τ a) (τ c) (τ b) :=
  CircleCyclic.map_decreasing_lift hc hm hl h

/-- A homeomorphism of the circle keeps all cyclic orders or reverses all of them. -/
theorem circle_dichotomy (τ : Circle ≃ₜ Circle) :
    (∀ a b c : Circle, a ≠ b → b ≠ c → a ≠ c → (CircleCyclic (τ a) (τ b)
      (τ c) ↔ CircleCyclic a b c)) ∨
      ∀ a b c : Circle, a ≠ b → b ≠ c → a ≠ c → (CircleCyclic (τ a) (τ b)
        (τ c) ↔ ¬ CircleCyclic a b c) := by
  rcases circleCyclic_homeomorph τ with h | h
  · exact .inl fun a b c hab hbc hac ↦ (h a b c hab hbc hac).symm
  · refine .inr fun a b c hab hbc hac ↦ (h a c b hac hbc.symm hab).symm.trans ?_
    exact ⟨fun h' h'' ↦ CircleOrder.not_circleCyclic_both h'' h',
      fun h' ↦ (circleCyclic_or hab hac hbc).resolve_left h'⟩

variable {S : Type u} [TopologicalSpace S]

/-- The orientations `ω` and `ω'` agree on the closed disc `Δ`. -/
def SignSame (ω ω' : SurfaceOrientation S) (Δ : Set S) : Prop :=
  ∀ a b c : S, a ∈ discBd Δ → b ∈ discBd Δ → c ∈ discBd Δ → a ≠ b → b ≠ c → a ≠ c →
    (ω'.pos Δ a b c ↔ ω.pos Δ a b c)

/-- The orientations `ω` and `ω'` are opposite on the closed disc `Δ`. -/
def SignOpp (ω ω' : SurfaceOrientation S) (Δ : Set S) : Prop :=
  ∀ a b c : S, a ∈ discBd Δ → b ∈ discBd Δ → c ∈ discBd Δ → a ≠ b → b ≠ c → a ≠ c →
    (ω'.pos Δ a b c ↔ ¬ ω.pos Δ a b c)

variable [T2Space S]

/-- Two orientations are equal or opposite on each closed disc. -/
theorem disc_sign (ω ω' : SurfaceOrientation S) {Δ : Set S} (hΔ : IsClosedDisc Δ) : SignSame ω ω' Δ
  ∨ SignOpp ω ω' Δ := by
  obtain ⟨φ, hφc, hφi, hφr, hφ⟩ := ω.isDirection Δ hΔ
  obtain ⟨φ', hφc', hφi', hφr', hφ'⟩ := ω'.isDirection Δ hΔ
  have he := (hφc.isClosedEmbedding hφi).isEmbedding
  have he' := (hφc'.isClosedEmbedding hφi').isEmbedding
  let τ : Circle ≃ₜ Circle := he.toHomeomorph.trans ((Homeomorph.setCongr
    (hφr.trans hφr'.symm)).trans he'.toHomeomorph.symm)
  have hτ : ∀ z, φ' (τ z) = φ z := fun z ↦ by
    have := congrArg Subtype.val (he'.toHomeomorph.apply_symm_apply ((Homeomorph.setCongr
      (hφr.trans hφr'.symm)) (he.toHomeomorph z)))
    exact this
  have hpar : ∀ x ∈ discBd Δ, ∃ z, φ z = x := fun x hx ↦ by
    rw [← hφr] at hx
    exact hx
  have key : ∀ a b c : Circle, a ≠ b → b ≠ c → a ≠ c → (ω'.pos Δ (φ a) (φ b) (φ c) ↔ CircleCyclic
    (τ a) (τ b) (τ c)) := by
    intro a b c hab hbc hac
    rw [← hτ, ← hτ, ← hτ]
    exact hφ' _ _ _ (τ.injective.ne hab) (τ.injective.ne hbc) (τ.injective.ne hac)
  rcases circle_dichotomy τ with h | h
  · left
    intro a b c ha hb hc hab hbc hac
    obtain ⟨a, rfl⟩ := hpar a ha
    obtain ⟨b, rfl⟩ := hpar b hb
    obtain ⟨c, rfl⟩ := hpar c hc
    have h1 : a ≠ b := fun h' ↦ hab (by rw [h'])
    have h2 : b ≠ c := fun h' ↦ hbc (by rw [h'])
    have h3 : a ≠ c := fun h' ↦ hac (by rw [h'])
    rw [key a b c h1 h2 h3, h a b c h1 h2 h3, hφ a b c h1 h2 h3]
  · right
    intro a b c ha hb hc hab hbc hac
    obtain ⟨a, rfl⟩ := hpar a ha
    obtain ⟨b, rfl⟩ := hpar b hb
    obtain ⟨c, rfl⟩ := hpar c hc
    have h1 : a ≠ b := fun h' ↦ hab (by rw [h'])
    have h2 : b ≠ c := fun h' ↦ hbc (by rw [h'])
    have h3 : a ≠ c := fun h' ↦ hac (by rw [h'])
    rw [key a b c h1 h2 h3, h a b c h1 h2 h3, hφ a b c h1 h2 h3]

/-- Two nested closed discs with three common boundary points have the same sign. -/
theorem sign_of_common (ω ω' : SurfaceOrientation S) {Δ₁ Δ₂ : Set S} (h₁ : IsClosedDisc Δ₁)
  (h₂ : IsClosedDisc Δ₂) (hs : Δ₁ ⊆ Δ₂)
    {a b c : S} (ha : a ∈ discBd Δ₁ ∩ discBd Δ₂) (hb : b ∈ discBd Δ₁ ∩ discBd Δ₂)
      (hc : c ∈ discBd Δ₁ ∩ discBd Δ₂)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    (SignSame ω ω' Δ₁ ↔ SignSame ω ω' Δ₂) ∧ (SignOpp ω ω' Δ₁ ↔ SignOpp ω ω' Δ₂) := by
  have e1 := ω.agree Δ₁ Δ₂ h₁ h₂ hs a b c ha hb hc hab hbc hac
  have e2 := ω'.agree Δ₁ Δ₂ h₁ h₂ hs a b c ha hb hc hab hbc hac
  refine ⟨⟨fun h ↦ ?_, fun h ↦ ?_⟩, ⟨fun h ↦ ?_, fun h ↦ ?_⟩⟩
  · rcases disc_sign ω ω' h₂ with h' | h'
    · exact h'
    · have := h a b c ha.1 hb.1 hc.1 hab hbc hac
      have := h' a b c ha.2 hb.2 hc.2 hab hbc hac
      tauto
  · rcases disc_sign ω ω' h₁ with h' | h'
    · exact h'
    · have := h a b c ha.2 hb.2 hc.2 hab hbc hac
      have := h' a b c ha.1 hb.1 hc.1 hab hbc hac
      tauto
  · rcases disc_sign ω ω' h₂ with h' | h'
    · have := h a b c ha.1 hb.1 hc.1 hab hbc hac
      have := h' a b c ha.2 hb.2 hc.2 hab hbc hac
      tauto
    · exact h'
  · rcases disc_sign ω ω' h₁ with h' | h'
    · have := h a b c ha.2 hb.2 hc.2 hab hbc hac
      have := h' a b c ha.1 hb.1 hc.1 hab hbc hac
      tauto
    · exact h'

/-- A chord cuts a closed disc into two closed discs with the sign of the disc. -/
theorem chord_sign (ω ω' : SurfaceOrientation S) {Δ F : Set S} {s t : S} (hΔ : IsClosedDisc Δ)
  (hF : F ⊆ Δ) (hst : s ≠ t)
    (hl : IsLineWithEnds F s t) (hm : F ∩ discBd Δ = {s, t}) :
    ∃ Δ₁ Δ₂ : Set S, IsClosedDisc Δ₁ ∧ IsClosedDisc Δ₂ ∧ Δ₁ ∪ Δ₂ = Δ ∧ Δ₁ ∩ Δ₂ = F ∧ F ⊆ discBd Δ₁
      ∧ F ⊆ discBd Δ₂ ∧
      componentsIn (Δ \ F) = {Δ₁ \ F, Δ₂ \ F} ∧ (Δ₁ \ F).Nonempty ∧ (Δ₂ \ F).Nonempty ∧
      ((SignSame ω ω' Δ₁ ↔ SignSame ω ω' Δ) ∧ (SignOpp ω ω' Δ₁ ↔ SignOpp ω ω' Δ)) ∧
      ((SignSame ω ω' Δ₂ ↔ SignSame ω ω' Δ) ∧ (SignOpp ω ω' Δ₂ ↔ SignOpp ω ω' Δ)) := by
  obtain ⟨A₁, A₂, Δ₁, Δ₂, hA, hc, d1, d2, hu, hi, b1, b2, hc2⟩ := disc_iArc Δ F s t hΔ hF hst hl hm
  have hs : s ∈ F ∩ discBd Δ := hm ▸ .inl rfl
  have ht : t ∈ F ∩ discBd Δ := hm ▸ .inr rfl
  have hA₁ : A₁ ∈ componentsIn (discBd Δ \ {s, t}) := hc ▸ .inl rfl
  have hA₂ : A₂ ∈ componentsIn (discBd Δ \ {s, t}) := hc ▸ .inr rfl
  have part : ∀ {A G : Set S}, A ∈ componentsIn (discBd Δ \ {s, t}) → IsClosedDisc G → G ⊆ Δ
    → discBd G = A ∪ F →
      (G \ F).Nonempty ∧ ((SignSame ω ω' G ↔ SignSame ω ω' Δ) ∧ (SignOpp ω ω' G ↔ SignOpp ω ω' Δ))
        := by
    intro A G hA hG hGΔ hb
    obtain ⟨y, hy, rfl⟩ := hA
    have hyA := mem_connectedComponentIn hy
    have hbG : discBd G ⊆ G := Subtype.coe_image_subset _ _
    have hyb : y ∈ discBd G := hb ▸ .inl hyA
    have hyF : y ∉ F := fun h' ↦ hy.2 (hm ▸ ⟨h', hy.1⟩)
    refine ⟨⟨y, hbG hyb, hyF⟩, ?_⟩
    have hsb : s ∈ discBd G := hb ▸ .inr hs.1
    have htb : t ∈ discBd G := hb ▸ .inr ht.1
    exact sign_of_common ω ω' hG hΔ hGΔ ⟨hsb, hs.2⟩ ⟨htb, ht.2⟩ ⟨hyb,
      hy.1⟩ hst (fun h' ↦ hy.2 (.inr h'.symm)) (fun h' ↦ hy.2 (.inl h'.symm))
  have p1 := part hA₁ d1 (hu ▸ subset_union_left) b1
  have p2 := part hA₂ d2 (hu ▸ subset_union_right) b2
  exact ⟨Δ₁, Δ₂, d1, d2, hu, hi, b1 ▸ subset_union_right, b2 ▸ subset_union_right, hc2, p1.1,
    p2.1, p1.2, p2.2⟩

/-- A closed disc inside the interior of a closed disc has the sign of the larger disc. Straight
chords through the two discs
in the model of `exists_disc_collar` give half discs that are nested and share a boundary segment.
-/
theorem sign_of_inner (ω ω' : SurfaceOrientation S) {D Δ : Set S} (hD : IsClosedDisc D)
  (hΔ : IsClosedDisc Δ)
    (hin : D ⊆ Δ \ discBd Δ) :
    (SignSame ω ω' D ↔ SignSame ω ω' Δ) ∧ (SignOpp ω ω' D ↔ SignOpp ω ω' Δ) := by
  obtain ⟨p⟩ := hD.isOArc_discBd
  obtain ⟨c, c', hc, hc', hm, hm', hl, hr, hD1, hbd, hp⟩ := exists_disc_collar hD hΔ hin p
  have hcinj : InjOn c (closedBall 0 2) := hl.injOn
  have hb1 : closedBall (0 : ℂ) 1 ⊆ closedBall 0 2 := closedBall_subset_closedBall (by norm_num)
  have hbdD : discBd D = c '' sphere 0 1 := by
    apply Subset.antisymm
    · intro x hx
      refine ⟨(p.symm ⟨x, hx⟩ : Circle), by simp, ?_⟩
      rw [hp]
      simp
    · rintro _ ⟨z, hz, rfl⟩
      have hw := hp ⟨z, hz⟩
      simp only at hw
      rw [hw]
      exact (p _).2
  have hline : ∀ r : ℝ, 0 < r → r ≤ 2 → ∃ F : Set S, F = c '' {z : ℂ | z.im = 0 ∧ |z.re| ≤ r}
    ∧ IsLineWithEnds F (c ((-r : ℝ) : ℂ)) (c ((r : ℝ) : ℂ)) := by
    intro r hr0 hr2
    let a : 𝕀 → ℂ := fun u ↦ (((2 * (u : ℝ) - 1) * r : ℝ) : ℂ)
    have hab : ∀ u, ‖a u‖ ≤ 2 := fun u ↦ by
      simp only [a, Complex.norm_real, Real.norm_eq_abs, abs_mul]
      have h1 : |2 * (u : ℝ) - 1| ≤ 1 := abs_le.mpr ⟨by linarith [u.2.1], by linarith [u.2.2]⟩
      rw [abs_of_pos hr0]
      nlinarith [abs_nonneg (2 * (u : ℝ) - 1)]
    have hac : Continuous a := by
      simp only [a]
      fun_prop
    have hmem : ∀ u, a u ∈ closedBall (0 : ℂ) 2 := fun u ↦ mem_closedBall_zero_iff.mpr (hab u)
    have harc : IsArcMap (c ∘ a) := by
      refine ⟨hc.comp_continuous hac hmem, fun u v h' ↦ ?_⟩
      have h2 := hcinj (hmem u) (hmem v) h'
      have h3 : (2 * (u : ℝ) - 1) * r = (2 * (v : ℝ) - 1) * r := Complex.ofReal_injective h2
      have h4 := mul_right_cancel₀ hr0.ne' h3
      exact Subtype.ext (by linarith)
    have hl' := harc.isLineWithEnds
    have e0 : (c ∘ a) 0 = c ((-r : ℝ) : ℂ) := by simp [a]
    have e1 : (c ∘ a) 1 = c ((r : ℝ) : ℂ) := by
      change c (((2 * ((1 : 𝕀) : ℝ) - 1) * r : ℝ) : ℂ) = _
      congr 2
      change (2 * (1 : ℝ) - 1) * r = r
      ring
    rw [e0, e1] at hl'
    refine ⟨range (c ∘ a), ?_, hl'⟩
    rw [range_comp]
    congr 1
    ext z
    constructor
    · rintro ⟨u, rfl⟩
      simp only [a, mem_ofPred_eq, Complex.ofReal_re, Complex.ofReal_im, true_and, abs_mul]
      have h1 : |2 * (u : ℝ) - 1| ≤ 1 := abs_le.mpr ⟨by linarith [u.2.1], by linarith [u.2.2]⟩
      rw [abs_of_pos hr0]
      nlinarith [abs_nonneg (2 * (u : ℝ) - 1)]
    · rintro ⟨h1, h2⟩
      obtain ⟨h3, h4⟩ := abs_le.mp h2
      refine ⟨⟨(z.re / r + 1) / 2, ?_, ?_⟩, ?_⟩
      · have : -1 ≤ z.re / r := by rw [le_div_iff₀ hr0]; linarith
        linarith
      · have : z.re / r ≤ 1 := by rw [div_le_iff₀ hr0]; linarith
        linarith
      · apply Complex.ext
        · simp only [a, Complex.ofReal_re]
          field_simp
          ring
        · simp [a, h1]
  have hnorm : ∀ z : ℂ, z.im = 0 → ‖z‖ = |z.re| := fun z hz ↦ by
    have : z = (z.re : ℂ) := Complex.ext rfl (by simp [hz])
    rw [this]
    simp
  have hRb : ∀ r : ℝ, r ≤ 2 → {z : ℂ | z.im = 0 ∧ |z.re| ≤ r} ⊆ closedBall 0 2 := fun r hr z hz ↦
    mem_closedBall_zero_iff.mpr (by rw [hnorm z hz.1]; exact hz.2.trans hr)
  have hcap : ∀ r : ℝ, 0 < r → r ≤ 2 → (c '' {z : ℂ | z.im = 0 ∧ |z.re| ≤ r}) ∩ c '' sphere 0 r
    = {c ((-r : ℝ) : ℂ), c ((r : ℝ) : ℂ)} := by
    intro r hr0 hr2
    have hsph : sphere (0 : ℂ) r ⊆ closedBall 0 2 := fun z hz ↦
      mem_closedBall_zero_iff.mpr ((mem_sphere_zero_iff_norm.mp hz).le.trans hr2)
    apply Subset.antisymm
    · rintro _ ⟨⟨z, hz, rfl⟩, w, hw, he⟩
      obtain rfl := hcinj (hsph hw) (hRb r hr2 hz) he
      have h1 : |w.re| = r := by rw [← hnorm w hz.1]; exact mem_sphere_zero_iff_norm.mp hw
      rcases abs_eq hr0.le |>.mp h1 with h2 | h2
      · right
        have : w = (r : ℂ) := Complex.ext (by simpa using h2) (by simpa using hz.1)
        rw [this]; rfl
      · left
        have : w = ((-r : ℝ) : ℂ) := Complex.ext (by simpa using h2) (by simpa using hz.1)
        rw [this]
    · have h1 : ∀ w : ℂ, w = ((r : ℝ) : ℂ) ∨ w = ((-r : ℝ) : ℂ) → c w ∈ (c '' {z : ℂ | z.im = 0
      ∧ |z.re| ≤ r}) ∩ c '' sphere 0 r := by
        rintro _ (rfl | rfl)
        · refine ⟨⟨_, ⟨by simp, by simp [abs_of_pos hr0]⟩, rfl⟩, _, ?_, rfl⟩
          simp [abs_of_pos hr0]
        · refine ⟨⟨_, ⟨by simp, by simp [abs_of_pos hr0]⟩, rfl⟩, _, ?_, rfl⟩
          simp [abs_of_pos hr0]
      rintro x (rfl | rfl)
      · exact h1 _ (.inr rfl)
      · exact h1 _ (.inl rfl)
  have hne : ∀ r : ℝ, 0 < r → r ≤ 2 → c ((-r : ℝ) : ℂ) ≠ c ((r : ℝ) : ℂ) := fun r hr0 hr2 h' ↦ by
    have h1 : (-r : ℝ) = r := by
      have := hcinj (x₁ := ((-r : ℝ) : ℂ)) (x₂ := ((r : ℝ) : ℂ)) (by simp [abs_of_pos hr0, hr2])
        (by simp [abs_of_pos hr0, hr2]) h'
      exact Complex.ofReal_injective this
    linarith
  obtain ⟨F, hFe, hlF⟩ := hline 2 (by norm_num) le_rfl
  obtain ⟨F₁, hF₁e, hlF₁⟩ := hline 1 one_pos (by norm_num)
  have hFΔ : F ⊆ Δ := by
    rw [hFe]
    rintro _ ⟨z, hz, rfl⟩
    exact hm (hRb 2 le_rfl hz)
  have hF₁D : F₁ ⊆ D := by
    rw [hF₁e, ← hD1]
    refine image_mono fun z hz ↦ mem_closedBall_zero_iff.mpr ?_
    rw [hnorm z hz.1]
    exact hz.2
  have hF₁F : F₁ ⊆ F := by
    rw [hFe, hF₁e]
    exact image_mono fun z hz ↦ ⟨hz.1, hz.2.trans (by norm_num)⟩
  have hm2 : F ∩ discBd Δ = {c ((-(2 : ℝ) : ℝ) : ℂ), c (((2 : ℝ) : ℝ) : ℂ)} := by
    rw [hFe, ← hbd]
    exact hcap 2 (by norm_num) le_rfl
  have hm1 : F₁ ∩ discBd D = {c ((-(1 : ℝ) : ℝ) : ℂ), c (((1 : ℝ) : ℝ) : ℂ)} := by
    rw [hF₁e, hbdD]
    exact hcap 1 one_pos (by norm_num)
  obtain ⟨D₁, D₂, d1, -, hDu, -, hF₁b, -, hDc, ⟨y, hy⟩, -, hsD, -⟩ := chord_sign ω ω' hD hF₁D
    (hne 1 one_pos (by norm_num)) hlF₁ hm1
  obtain ⟨Δ₁, Δ₂, g1, g2, -, -, hFb1, hFb2, hΔc, -, -, hs1, hs2⟩ := chord_sign ω ω' hΔ hFΔ (hne 2
    (by norm_num) le_rfl) hlF hm2
  have hcomp1 : IsPreconnected (D₁ \ F₁) := by
    have : D₁ \ F₁ ∈ componentsIn (D \ F₁) := hDc ▸ .inl rfl
    obtain ⟨q, -, e⟩ := this
    exact e ▸ isPreconnected_connectedComponentIn
  have hDΔ : D ⊆ Δ := fun x hx ↦ (hin hx).1
  have hD₁D : D₁ ⊆ D := hDu ▸ subset_union_left
  have hsub : D₁ \ F₁ ⊆ Δ \ F := by
    rintro x ⟨hx, hxF⟩
    refine ⟨hDΔ (hD₁D hx), fun hF ↦ hxF ?_⟩
    rw [hFe] at hF
    obtain ⟨z, hz, rfl⟩ := hF
    have hxD := hD₁D hx
    rw [← hD1] at hxD
    obtain ⟨w, hw, he⟩ := hxD
    obtain rfl := hcinj (hb1 hw) (hRb 2 le_rfl hz) he
    rw [hF₁e]
    exact ⟨w, ⟨hz.1, by rw [← hnorm w hz.1]; exact mem_closedBall_zero_iff.mp hw⟩, rfl⟩
  have hfin : ∀ G : Set S, IsClosedDisc G → F ⊆ discBd G → connectedComponentIn (Δ \ F) y = G \ F →
      (SignSame ω ω' D₁ ↔ SignSame ω ω' G) ∧ (SignOpp ω ω' D₁ ↔ SignOpp ω ω' G) := by
    intro G hG hFG hcc
    have hbG : discBd G ⊆ G := Subtype.coe_image_subset _ _
    have hsubG : D₁ ⊆ G := fun x hx ↦ by
      by_cases hxF : x ∈ F₁
      · exact hbG (hFG (hF₁F hxF))
      · have := hcomp1.subset_connectedComponentIn hy hsub ⟨hx, hxF⟩
        rw [hcc] at this
        exact this.1
    have hmem : ∀ r : ℝ, |r| ≤ 1 → c (r : ℂ) ∈ discBd D₁ ∩ discBd G := fun r hr ↦ by
      have : c (r : ℂ) ∈ F₁ := by
        rw [hF₁e]
        exact ⟨_, ⟨by simp, by simpa using hr⟩, rfl⟩
      exact ⟨hF₁b this, hFG (hF₁F this)⟩
    have hinj : ∀ r r' : ℝ, |r| ≤ 1 → |r'| ≤ 1 → r ≠ r' → c (r : ℂ) ≠ c (r' : ℂ)
      := fun r r' h1 h2 hn he ↦ by
      have hm1' : (r : ℂ) ∈ closedBall (0 : ℂ) 2 := mem_closedBall_zero_iff.mpr
        (by simpa using h1.trans (by norm_num))
      have hm2' : (r' : ℂ) ∈ closedBall (0 : ℂ) 2 := mem_closedBall_zero_iff.mpr
        (by simpa using h2.trans (by norm_num))
      exact hn (Complex.ofReal_injective (hcinj hm1' hm2' he))
    have a1 : |(-1 : ℝ)| ≤ 1 := by simp
    have a2 : |(0 : ℝ)| ≤ 1 := by simp
    have a3 : |(1 : ℝ)| ≤ 1 := by simp
    exact sign_of_common ω ω' d1 hG hsubG (hmem _ a1) (hmem _ a2) (hmem _ a3) (hinj _ _ a1 a2
      (by norm_num))
      (hinj _ _ a2 a3 (by norm_num)) (hinj _ _ a1 a3 (by norm_num))
  have hyΔ := hsub hy
  have hmemc : connectedComponentIn (Δ \ F) y ∈ ({Δ₁ \ F, Δ₂ \ F} : Set (Set S))
    := hΔc ▸ ⟨y, hyΔ, rfl⟩
  rcases hmemc with h' | h'
  · have := hfin Δ₁ g1 hFb1 h'
    exact ⟨hsD.1.symm.trans (this.1.trans hs1.1), hsD.2.symm.trans (this.2.trans hs1.2)⟩
  · have := hfin Δ₂ g2 hFb2 h'
    exact ⟨hsD.1.symm.trans (this.1.trans hs2.1), hsD.2.symm.trans (this.2.trans hs2.2)⟩

omit [T2Space S] in
/-- A closed disc around an interior point, inside a given open set. -/
theorem exists_disc_around_interior {x : S} (hx : IsInteriorPoint x) {W : Set S} (hW : IsOpen W)
  (hxW : x ∈ W) :
    ∃ D, IsClosedDisc D ∧ D ⊆ W ∧ x ∈ discInt D := by
  obtain ⟨U, h, g, c, hUW, hg0⟩ := hx.exists_ballChart hW hxW (R := 2) (by norm_num)
  obtain ⟨hZ, hbdZ⟩ := isClosedDisc_closedBall
  have hsub : closedBall (0 : ℂ) 1 ⊆ ball 0 2 := closedBall_subset_ball (by norm_num)
  obtain ⟨d, hb⟩ := c.image_disc hZ hsub
  refine ⟨_, d, ?_, ⟨0, mem_closedBall_self zero_le_one, hg0⟩, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact hUW (c.gm (hsub hz))
  · rw [hb, hbdZ]
    rintro ⟨z, hz, he⟩
    have h1 := c.hg (hsub (sphere_subset_closedBall hz))
    have h2 := c.hg (mem_ball_self (by norm_num : (0 : ℝ) < 2))
    rw [he] at h1
    rw [hg0] at h2
    have : z = 0 := h1.symm.trans h2
    rw [this] at hz
    simp at hz

omit [T2Space S] in
/-- The interior of a connected surface is connected. Each collar of a cuff, without the cuff, is
connected, so it lies on one
side of a splitting of the interior. Adding the collars makes a splitting of the surface. -/
theorem isPreconnected_compl_bd (hS : IsSurface S) [ConnectedSpace S] : IsPreconnected (bd S)ᶜ := by
  classical
  obtain ⟨hcpt, ht2, hman⟩ := id hS
  obtain ⟨hbdc, hfin, hO⟩ := cuff_statement.{u} S hS
  have hcol : ∀ C ∈ cuffs S, ∃ R T : Set S, IsOpen R ∧ C ⊆ R ∧ R \ C = T ∧ IsPreconnected T ∧ T ⊆
    (bd S)ᶜ ∧ T.Nonempty := by
    intro C hC
    obtain ⟨φ⟩ := hO C hC
    have hUo : IsOpen (⋃₀ (cuffs S \ {C}))ᶜ := ((hfin.subset sdiff_subset).isClosed_sUnion fun C'
      hC' ↦
      (hO C' hC'.1).isCompact.isClosed).isOpen_compl
    have hCU : C ⊆ (⋃₀ (cuffs S \ {C}))ᶜ := by
      intro x hx
      rw [mem_compl_iff]
      rintro ⟨C', ⟨hC', hne⟩, hxC'⟩
      exact Set.disjoint_left.mp (cuffs_disjoint hC hC' (Ne.symm hne)) hx hxC'
    obtain ⟨b, hbc, hbi, hbU, hb0, hbo⟩ := exists_collar hS hC φ hUo hCU
    have hb0' : ∀ x ∈ C, ∃ w, b (w, 0) = x := fun x hx ↦ ⟨φ.symm ⟨x, hx⟩, by rw [hb0]; simp⟩
    have hbC : ∀ w t, b (w, t) ∈ C → t = 0 := fun w t h' ↦ by
      have h1 := hb0 (φ.symm ⟨_, h'⟩)
      rw [Homeomorph.apply_symm_apply] at h1
      exact congrArg Prod.snd (hbi h1) |>.symm
    obtain ⟨T, hTdef⟩ : ∃ T : Set S, T = b '' (univ ×ˢ {t : 𝕀 | t ≠ 0 ∧ t ≠ 1}) := ⟨_, rfl⟩
    have hT : (range b \ b '' {x | x.2 = 1}) \ C = T := by
      rw [hTdef]
      ext x
      constructor
      · rintro ⟨⟨⟨⟨w, t⟩, rfl⟩, h1⟩, h2⟩
        refine ⟨(w, t), ⟨mem_univ _, fun h3 ↦ h2 (by
          have h3' : t = 0 := h3
          rw [h3', hb0]
          exact (φ w).2), fun h3 ↦ h1 ⟨(w, t), h3, rfl⟩⟩, rfl⟩
      · rintro ⟨⟨w, t⟩, ⟨-, h0, h1⟩, rfl⟩
        refine ⟨⟨⟨_, rfl⟩, ?_⟩, fun h' ↦ h0 (hbC w t h')⟩
        rintro ⟨⟨w', t'⟩, h2, h3⟩
        have := congrArg Prod.snd (hbi h3)
        exact h1 (this.symm.trans h2)
    refine ⟨_, T, hbo, ?_, hT, ?_, ?_, ?_⟩ <;> try rw [hTdef]
    · intro x hx
      obtain ⟨w, rfl⟩ := hb0' x hx
      refine ⟨⟨_, rfl⟩, ?_⟩
      rintro ⟨⟨w', t'⟩, h2, h3⟩
      have := congrArg Prod.snd (hbi h3)
      have h4 : t' = 1 := h2
      have h5 : t' = 0 := this
      exact zero_ne_one (h5.symm.trans h4)
    · have hI : IsPreconnected {t : 𝕀 | t ≠ 0 ∧ t ≠ 1} := by
        apply OrdConnected.isPreconnected
        refine ⟨fun x hx y hy z hz ↦ ⟨fun h0 ↦ ?_, fun h1 ↦ ?_⟩⟩
        · rw [h0] at hz
          exact hx.1 (le_antisymm hz.1 unitInterval.nonneg')
        · rw [h1] at hz
          exact hy.2 (le_antisymm unitInterval.le_one' hz.2)
      exact (isPreconnected_univ.prod hI).image _ hbc.continuousOn
    · rintro _ ⟨⟨w, t⟩, ⟨-, h0, -⟩, rfl⟩ hbdx
      have hxb : b (w, t) ∈ ⋃₀ cuffs S := sUnion_cuffs (S := S) ▸ hbdx
      obtain ⟨C', hC', hxC'⟩ := hxb
      by_cases hCC : C' = C
      · exact h0 (hbC w t (hCC ▸ hxC'))
      · exact (mem_compl_iff _ _).mp (hbU ⟨_, rfl⟩) ⟨C', ⟨hC', hCC⟩, hxC'⟩
    · have h12 : (1 / 2 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
      obtain ⟨w⟩ : Nonempty Circle := inferInstance
      refine ⟨_, (w, ⟨1 / 2, h12⟩), ⟨mem_univ _, fun h' ↦ ?_, fun h' ↦ ?_⟩, rfl⟩
      · have : (1 / 2 : ℝ) = 0 := congrArg Subtype.val h'
        norm_num at this
      · have : (1 / 2 : ℝ) = 1 := congrArg Subtype.val h'
        norm_num at this
  choose! R T hR hCR hRT hTp hTb hTne using hcol
  rw [isPreconnected_iff_subset_of_disjoint]
  intro u v hu hv hsub hdis
  have hcompl : IsOpen (bd S)ᶜ := hbdc.isOpen_compl
  have hTuv : ∀ C ∈ cuffs S, T C ⊆ u ∨ T C ⊆ v := fun C hC ↦ by
    refine isPreconnected_iff_subset_of_disjoint.mp (hTp C hC) u v hu hv ((hTb C hC).trans hsub) ?_
    apply Subset.antisymm _ (empty_subset _)
    rintro x ⟨hxT, hxu, hxv⟩
    have : x ∈ (bd S)ᶜ ∩ (u ∩ v) := ⟨hTb C hC hxT, hxu, hxv⟩
    rwa [hdis] at this
  have hbdC : ∀ C ∈ cuffs S, C ⊆ bd S := fun C hC ↦ sUnion_cuffs (S := S) ▸ subset_sUnion_of_mem hC
  let A : Set S := ((bd S)ᶜ ∩ u) ∪ ⋃ C ∈ {C ∈ cuffs S | T C ⊆ u}, R C
  let B : Set S := ((bd S)ᶜ ∩ v) ∪ ⋃ C ∈ {C ∈ cuffs S | T C ⊆ v}, R C
  have hAo : IsOpen A := (hcompl.inter hu).union (isOpen_biUnion fun C hC ↦ hR C hC.1)
  have hBo : IsOpen B := (hcompl.inter hv).union (isOpen_biUnion fun C hC ↦ hR C hC.1)
  have hcov : (univ : Set S) ⊆ A ∪ B := by
    intro x _
    by_cases hx : x ∈ bd S
    · have hxb : x ∈ ⋃₀ cuffs S := sUnion_cuffs (S := S) ▸ hx
      obtain ⟨C, hC, hxC⟩ := hxb
      rcases hTuv C hC with h' | h'
      · exact .inl (.inr (mem_biUnion (show C ∈ {C ∈ cuffs S | T C ⊆ u} from ⟨hC,
          h'⟩) (hCR C hC hxC)))
      · exact .inr (.inr (mem_biUnion (show C ∈ {C ∈ cuffs S | T C ⊆ v} from ⟨hC,
          h'⟩) (hCR C hC hxC)))
    · rcases hsub hx with h' | h'
      · exact .inl (.inl ⟨hx, h'⟩)
      · exact .inr (.inl ⟨hx, h'⟩)
  have hemp : ∀ x, x ∈ (bd S)ᶜ → x ∈ u → x ∈ v → False := fun x h1 h2 h3 ↦ by
    have : x ∈ (bd S)ᶜ ∩ (u ∩ v) := ⟨h1, h2, h3⟩
    rw [hdis] at this
    exact this
  have hRmem : ∀ C ∈ cuffs S, ∀ x ∈ R C, x ∈ C ∨ x ∈ T C := fun C hC x hx ↦ by
    by_cases h' : x ∈ C
    · exact .inl h'
    · exact .inr (hRT C hC ▸ ⟨hx, h'⟩)
  have hdisj : (univ : Set S) ∩ (A ∩ B) = ∅ := by
    apply Subset.antisymm _ (empty_subset _)
    rintro x ⟨-, hxA, hxB⟩
    have side : ∀ {w : Set S}, x ∈ ((bd S)ᶜ ∩ w) ∪ (⋃ C ∈ {C ∈ cuffs S | T C ⊆ w}, R C) →
        (x ∈ (bd S)ᶜ ∧ x ∈ w) ∨ ∃ C ∈ cuffs S, T C ⊆ w ∧ x ∈ C := by
      intro w h'
      rcases h' with h' | h'
      · exact .inl h'
      · obtain ⟨C, hC, hxC⟩ := mem_iUnion₂.mp h'
        rcases hRmem C hC.1 x hxC with h2 | h2
        · exact .inr ⟨C, hC.1, hC.2, h2⟩
        · exact .inl ⟨hTb C hC.1 h2, hC.2 h2⟩
    rcases side hxA with ⟨h1, h2⟩ | ⟨C, hC, hTu, hxC⟩ <;> rcases side hxB with ⟨h3, h4⟩ | ⟨C', hC',
      hTv, hxC'⟩
    · exact hemp x h1 h2 h4
    · exact h1 (hbdC C' hC' hxC')
    · exact h3 (hbdC C hC hxC)
    · have hCC : C = C' := by
        by_contra hne
        exact Set.disjoint_left.mp (cuffs_disjoint hC hC' hne) hxC hxC'
      subst hCC
      obtain ⟨y, hy⟩ := hTne C hC
      exact hemp y (hTb C hC hy) (hTu hy) (hTv hy)
  rcases isPreconnected_iff_subset_of_disjoint.mp isPreconnected_univ A B hAo hBo hcov hdisj with
    h' | h'
  · left
    intro x hx
    rcases h' (mem_univ x) with h2 | h2
    · exact h2.2
    · obtain ⟨C, hC, hxC⟩ := mem_iUnion₂.mp h2
      rcases hRmem C hC.1 x hxC with h3 | h3
      · exact absurd (hbdC C hC.1 h3) hx
      · exact hC.2 h3
  · right
    intro x hx
    rcases h' (mem_univ x) with h2 | h2
    · exact h2.2
    · obtain ⟨C, hC, hxC⟩ := mem_iUnion₂.mp h2
      rcases hRmem C hC.1 x hxC with h3 | h3
      · exact absurd (hbdC C hC.1 h3) hx
      · exact hC.2 h3

omit [T2Space S] in
/-- **Two orientations of a connected surface are equal on all closed discs, or opposite on all
closed discs.** -/
theorem orientation_dichotomy (hS : IsSurface S) [ConnectedSpace S] (ω ω' : SurfaceOrientation S) :
    (∀ Δ, IsClosedDisc Δ → SignSame ω ω' Δ) ∨ ∀ Δ, IsClosedDisc Δ → SignOpp ω ω' Δ := by
  classical
  obtain ⟨hcpt, ht2, hman⟩ := id hS
  have hclash : ∀ {Δ Δ' : Set S} {x : S}, IsClosedDisc Δ → IsClosedDisc Δ' → SignSame ω ω' Δ
    → SignOpp ω ω' Δ' → x ∈ (bd S)ᶜ →
      x ∈ discInt Δ → x ∈ discInt Δ' → False := by
    intro Δ Δ' x d d' hs ho hx hx1 hx2
    have hint : IsInteriorPoint x := by
      by_contra h'
      exact hx h'
    obtain ⟨D, hD, hsub, -⟩ := exists_disc_around_interior hint ((d.isOpen_discInt hman).inter
      (d'.isOpen_discInt hman)) ⟨hx1, hx2⟩
    have s1 := ((sign_of_inner ω ω' hD d fun y hy ↦ (hsub hy).1).1).2 hs
    have s2 := ((sign_of_inner ω ω' hD d' fun y hy ↦ (hsub hy).2).2).2 ho
    obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := hD.isOArc_discBd.exists_three
    have h1 := s1 a b c ha hb hc hab hbc hac
    have h2 := s2 a b c ha hb hc hab hbc hac
    tauto
  let P : Set S := ⋃₀ {O | ∃ Δ, IsClosedDisc Δ ∧ SignSame ω ω' Δ ∧ O = discInt Δ}
  let N : Set S := ⋃₀ {O | ∃ Δ, IsClosedDisc Δ ∧ SignOpp ω ω' Δ ∧ O = discInt Δ}
  have hPo : IsOpen P := isOpen_sUnion fun O ⟨Δ, d, _, e⟩ ↦ e ▸ d.isOpen_discInt hman
  have hNo : IsOpen N := isOpen_sUnion fun O ⟨Δ, d, _, e⟩ ↦ e ▸ d.isOpen_discInt hman
  have hcov : (bd S)ᶜ ⊆ P ∪ N := fun x hx ↦ by
    have hint : IsInteriorPoint x := by
      by_contra h'
      exact hx h'
    obtain ⟨D, hD, -, hxD⟩ := exists_disc_around_interior hint isOpen_univ (mem_univ x)
    rcases disc_sign ω ω' hD with h' | h'
    · exact .inl ⟨_, ⟨D, hD, h', rfl⟩, hxD⟩
    · exact .inr ⟨_, ⟨D, hD, h', rfl⟩, hxD⟩
  have hdis : (bd S)ᶜ ∩ (P ∩ N) = ∅ := by
    apply Subset.antisymm _ (empty_subset _)
    rintro x ⟨hx, ⟨_, ⟨Δ, d, hs, rfl⟩, hxΔ⟩, ⟨_, ⟨Δ', d', ho, rfl⟩, hxΔ'⟩⟩
    exact hclash d d' hs ho hx hxΔ hxΔ'
  have hmeet : ∀ Δ, IsClosedDisc Δ → ∃ x, x ∈ (bd S)ᶜ ∧ x ∈ discInt Δ := by
    intro Δ d
    obtain ⟨h, g, c⟩ := d.exists_isChart
    have hne : (discInt Δ).Nonempty := by
      rw [c.discInt_eq]
      exact ⟨g 0, 0, mem_ball_self one_pos, rfl⟩
    obtain ⟨y, hy⟩ := hne
    have hcl := mem_closure_compl_bd (hman y)
    obtain ⟨x, hx1, hx2⟩ := mem_closure_iff.mp hcl _ (d.isOpen_discInt hman) hy
    exact ⟨x, hx2, hx1⟩
  rcases isPreconnected_iff_subset_of_disjoint.mp (isPreconnected_compl_bd hS) P N hPo hNo hcov
    hdis with h' | h'
  · left
    intro Δ d
    rcases disc_sign ω ω' d with h2 | h2
    · exact h2
    · obtain ⟨x, hx, hxΔ⟩ := hmeet Δ d
      obtain ⟨_, ⟨Δ', d', hs, rfl⟩, hxΔ'⟩ := h' hx
      exact (hclash d' d hs h2 hx hxΔ' hxΔ).elim
  · right
    intro Δ d
    rcases disc_sign ω ω' d with h2 | h2
    · obtain ⟨x, hx, hxΔ⟩ := hmeet Δ d
      obtain ⟨_, ⟨Δ', d', ho, rfl⟩, hxΔ'⟩ := h' hx
      exact (hclash d d' h2 ho hx hxΔ hxΔ').elim
    · exact h2

omit [T2Space S] in
/-- The image of a closed disc under a homeomorphism of the surface. -/
theorem homeo_image_disc (e : S ≃ₜ S) {Δ : Set S} (hΔ : IsClosedDisc Δ) : IsClosedDisc (e '' Δ)
  ∧ discBd (e '' Δ) = e '' discBd Δ :=
  hΔ.image e.continuous.continuousOn e.symm.continuous.continuousOn fun x _ ↦ e.symm_apply_apply x

/-- The orientation that a homeomorphism pulls back. -/
noncomputable def pullOrientation (ω : SurfaceOrientation S) (e : S ≃ₜ S) : SurfaceOrientation S
  where
  pos Δ a b c := ω.pos (e '' Δ) (e a) (e b) (e c)
  isDirection Δ hΔ := by
    obtain ⟨d, hb⟩ := homeo_image_disc e hΔ
    obtain ⟨φ, h1, h2, h3, h4⟩ := ω.isDirection _ d
    refine ⟨fun z ↦ e.symm (φ z), e.symm.continuous.comp h1, e.symm.injective.comp h2, ?_,
      fun a b c hab hbc hac ↦ ?_⟩
    · rw [range_comp', h3, hb, image_image]
      simp
    · simpa using h4 a b c hab hbc hac
  agree Δ₁ Δ₂ h₁ h₂ hs a b c ha hb hc hab hbc hac := by
    obtain ⟨d₁, b₁⟩ := homeo_image_disc e h₁
    obtain ⟨d₂, b₂⟩ := homeo_image_disc e h₂
    have hm : ∀ {x}, x ∈ discBd Δ₁ ∩ discBd Δ₂ → e x ∈ discBd (e '' Δ₁) ∩ discBd (e '' Δ₂)
      := fun {x} hx ↦ by
      rw [b₁, b₂]
      exact ⟨mem_image_of_mem _ hx.1, mem_image_of_mem _ hx.2⟩
    exact ω.agree _ _ d₁ d₂ (image_mono hs) _ _ _ (hm ha) (hm hb) (hm hc) (e.injective.ne hab)
      (e.injective.ne hbc)
      (e.injective.ne hac)

/-- `f` reverses the orientation `ω` on each closed disc. -/
def IsReversedBy (ω : SurfaceOrientation S) (f : S ≃ₜ S) : Prop :=
  ∀ Δ : Set S, IsClosedDisc Δ → ∀ a b c : S, a ∈ discBd Δ → b ∈ discBd Δ → c ∈ discBd Δ →
    a ≠ b → b ≠ c → a ≠ c → (ω.pos (f '' Δ) (f a) (f b) (f c) ↔ ¬ ω.pos Δ a b c)

omit [T2Space S] in
/-- A homeomorphism of a connected surface keeps every orientation or reverses every orientation. -/
theorem homeo_orientation (hS : IsSurface S) [ConnectedSpace S] (e : S ≃ₜ S) :
    (∀ ω : SurfaceOrientation S, ω.IsPreservedBy e) ∨ ∀ ω : SurfaceOrientation S, IsReversedBy ω e
      := by
  by_cases h : ∀ ω : SurfaceOrientation S, ω.IsPreservedBy e
  · exact .inl h
  push Not at h
  obtain ⟨ω₀, hω₀⟩ := h
  have hrev : IsReversedBy ω₀ e := by
    rcases orientation_dichotomy hS ω₀ (pullOrientation ω₀ e) with h' | h'
    · exact absurd (fun Δ d a b c ha hb hc hab hbc hac ↦ h' Δ d a b c ha hb hc hab hbc hac) hω₀
    · exact fun Δ d a b c ha hb hc hab hbc hac ↦ h' Δ d a b c ha hb hc hab hbc hac
  refine .inr fun ω Δ d a b c ha hb hc hab hbc hac ↦ ?_
  obtain ⟨d', hb'⟩ := homeo_image_disc e d
  have hm : ∀ {x}, x ∈ discBd Δ → e x ∈ discBd (e '' Δ) := fun {x} hx ↦ hb' ▸ mem_image_of_mem _ hx
  have h0 := hrev Δ d a b c ha hb hc hab hbc hac
  have ne1 := e.injective.ne hab
  have ne2 := e.injective.ne hbc
  have ne3 := e.injective.ne hac
  rcases orientation_dichotomy hS ω₀ ω with h' | h'
  · have h1 := h' Δ d a b c ha hb hc hab hbc hac
    have h2 := h' _ d' _ _ _ (hm ha) (hm hb) (hm hc) ne1 ne2 ne3
    tauto
  · have h1 := h' Δ d a b c ha hb hc hab hbc hac
    have h2 := h' _ d' _ _ _ (hm ha) (hm hb) (hm hc) ne1 ne2 ne3
    tauto

omit [T2Space S] in
/-- Two reversing homeomorphisms in a row keep the orientation. -/
theorem preserved_of_reversed {ω : SurfaceOrientation S} {e₁ e₂ : S ≃ₜ S} (h₁ : IsReversedBy ω e₁)
  (h₂ : IsReversedBy ω e₂) :
    ω.IsPreservedBy (e₁.trans e₂) := by
  intro Δ d a b c ha hb hc hab hbc hac
  obtain ⟨d', hb'⟩ := homeo_image_disc e₁ d
  have hm : ∀ {x}, x ∈ discBd Δ → e₁ x ∈ discBd (e₁ '' Δ) := fun {x} hx ↦ hb' ▸ mem_image_of_mem _
    hx
  have h3 := h₂ _ d' _ _ _ (hm ha) (hm hb) (hm hc) (e₁.injective.ne hab) (e₁.injective.ne hbc)
    (e₁.injective.ne hac)
  have h4 := h₁ Δ d a b c ha hb hc hab hbc hac
  have e5 : (e₁.trans e₂) '' Δ = e₂ '' (e₁ '' Δ) := by
    rw [image_image]
    rfl
  rw [e5]
  change ω.pos (e₂ '' (e₁ '' Δ)) (e₂ (e₁ a)) (e₂ (e₁ b)) (e₂ (e₁ c)) ↔ _
  tauto

end GraphMinor.GM19
