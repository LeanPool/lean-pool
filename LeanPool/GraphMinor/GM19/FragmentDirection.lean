/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.FragmentChord
public import LeanPool.GraphMinor.GM19.CircleLift

/-!
# Directions of a circle

A direction of the boundary of a closed disc comes from a parametrization by the circle. Two
directions of one `O`-arc are equal or
reverse (`IsDirectionOf.same_or_reverse`), since a homeomorphism of the circle keeps or reverses the
cyclic order. We then consider
relations given only on a family of discs (`IsPartialOrientation`). Two of them on a closed disc
that are equal on one subdisc are equal
on every subdisc, by `exists_nested_chord`.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology Metric Filter GraphMinor.Surface

theorem exp_eq_of_angles {s t : ℝ} (hs : 0 < s) (hs' : s < 2 * Real.pi) (ht : 0 < t)
  (ht' : t < 2 * Real.pi)
    (h : Circle.exp s = Circle.exp t) : s = t := by
  obtain ⟨m, hm⟩ := Circle.exp_eq_exp.1 h
  have hpi := Real.pi_pos
  have h1 : (m : ℝ) * (2 * Real.pi) < 2 * Real.pi := by linarith
  have h2 : -(2 * Real.pi) < (m : ℝ) * (2 * Real.pi) := by linarith
  have h3 : (m : ℝ) < 1 := by nlinarith
  have h4 : (-1 : ℝ) < m := by nlinarith
  have h5 : m = 0 := by
    have h6 : m < 1 := by exact_mod_cast h3
    have h7 : -1 < m := by exact_mod_cast h4
    omega
  rw [hm, h5]
  simp

/-- Three points of the circle do not lie in both cyclic orders. -/
theorem not_circleCyclic_both {a b c : Circle} (h : CircleCyclic a b c)
  (h' : CircleCyclic a c b) : False := by
  obtain ⟨s, t, hs, hst, ht, hb, hc⟩ := h
  obtain ⟨s', t', hs', hst', ht', hc', hb'⟩ := h'
  have h1 : Circle.exp s = Circle.exp t' := mul_left_cancel (hb.symm.trans hb')
  have h2 : Circle.exp t = Circle.exp s' := mul_left_cancel (hc.symm.trans hc')
  have hpos : 0 < t' := hs'.trans hst'
  have hpos' : 0 < t := hs.trans hst
  have e1 := exp_eq_of_angles hs (hst.trans ht) hpos ht' h1
  have e2 := exp_eq_of_angles hpos' ht hs' (hst'.trans ht') h2
  linarith

theorem circleCyclic_inv {a b c : Circle} (h : CircleCyclic a b c) : CircleCyclic a⁻¹ c⁻¹ b⁻¹ := by
  obtain ⟨s, t, hs, hst, ht, rfl, rfl⟩ := h
  have hpi := Real.pi_pos
  refine ⟨2 * Real.pi - t, 2 * Real.pi - s, by linarith, by linarith, by linarith, ?_, ?_⟩
  · rw [Circle.exp_sub, Circle.exp_two_pi]
    simp [mul_comm]
  · rw [Circle.exp_sub, Circle.exp_two_pi]
    simp [mul_comm]

theorem exists_angle_of_circle (a : Circle) : ∃ α : ℝ, a = Circle.exp α := ⟨Complex.arg a,
  (Circle.exp_arg a).symm⟩

/-- A homeomorphism of the circle with an increasing lift keeps the cyclic order. -/
theorem circleCyclic_map_mono {τ : Circle ≃ₜ Circle} {L : ℝ → ℝ} (hc : Continuous L)
  (hm : StrictMono L)
    (hl : ∀ t, τ (Circle.exp t) = Circle.exp (L t)) {a b c : Circle} (h : CircleCyclic a b c) :
      CircleCyclic (τ a) (τ b) (τ c) := by
  obtain ⟨s, t, hs, hst, ht, rfl, rfl⟩ := h
  obtain ⟨α, rfl⟩ := exists_angle_of_circle a
  have hpi := Real.pi_pos
  have hsmall : L (α + t) < L α + 2 * Real.pi := by
    by_contra hn
    push Not at hn
    have hle : L α ≤ L (α + t) := (hm (by linarith : α < α + t)).le
    obtain ⟨y, hy, hLy⟩ := intermediate_value_Icc (by linarith : α ≤ α + t) hc.continuousOn
      (show L α + 2 * Real.pi ∈ Icc (L α) (L (α + t)) from ⟨by linarith, hn⟩)
    have h1 : Circle.exp y = Circle.exp α := τ.injective (by
      rw [hl, hl, hLy, Circle.exp_add, Circle.exp_two_pi, mul_one])
    have h2 : α < y := by
      rcases hy.1.eq_or_lt with h | h
      · rw [← h] at hLy
        linarith
      · exact h
    have h3 : Circle.exp (y - α) = Circle.exp 0 := by
      rw [Circle.exp_sub, h1, Circle.exp_zero]
      simp
    obtain ⟨m, hm'⟩ := Circle.exp_eq_exp.1 h3
    have h4 : y - α < 2 * Real.pi := by linarith [hy.2]
    have h5 : (m : ℝ) * (2 * Real.pi) = y - α := by linarith
    have h6 : (0 : ℝ) < m := by
      by_contra hn'
      push Not at hn'
      nlinarith
    have h7 : (m : ℝ) < 1 := by nlinarith
    have h8 : (0 : ℤ) < m := by exact_mod_cast h6
    have h9 : m < (1 : ℤ) := by exact_mod_cast h7
    omega
  have h1 : L α < L (α + s) := hm (by linarith)
  have h2 : L (α + s) < L (α + t) := hm (by linarith)
  refine ⟨L (α + s) - L α, L (α + t) - L α, by linarith, by linarith, by linarith, ?_, ?_⟩
  · rw [← Circle.exp_add, hl, hl, ← Circle.exp_add]
    congr 1
    ring
  · rw [← Circle.exp_add, hl, hl, ← Circle.exp_add]
    congr 1
    ring

/-- A homeomorphism of the circle with a decreasing lift reverses the cyclic order. -/
theorem circleCyclic_map_anti {τ : Circle ≃ₜ Circle} {L : ℝ → ℝ} (hc : Continuous L)
  (hm : StrictAnti L)
    (hl : ∀ t, τ (Circle.exp t) = Circle.exp (L t)) {a b c : Circle} (h : CircleCyclic a b c) :
      CircleCyclic (τ a) (τ c) (τ b) := by
  let τ' : Circle ≃ₜ Circle := (Homeomorph.inv Circle).trans τ
  have hl' : ∀ t, τ' (Circle.exp t) = Circle.exp (L (-t)) := fun t ↦ by
    change τ (Circle.exp t)⁻¹ = _
    rw [← Circle.exp_neg, hl]
  have := circleCyclic_map_mono (τ := τ') (L := fun t ↦ L (-t)) (by fun_prop) (fun s t h ↦ hm
    (neg_lt_neg h)) hl' (circleCyclic_inv h)
  simpa [τ'] using this

theorem circle_map_or (τ : Circle ≃ₜ Circle) :
    (∀ a b c : Circle, a ≠ b → b ≠ c → a ≠ c → (CircleCyclic a b c ↔ CircleCyclic (τ a) (τ b)
      (τ c))) ∨
    (∀ a b c : Circle, a ≠ b → b ≠ c → a ≠ c → (CircleCyclic a b c ↔ CircleCyclic (τ a) (τ c)
      (τ b))) := by
  obtain ⟨L, hc, hm, hl⟩ := exists_circle_lift τ
  have hne : ∀ {x y : Circle}, x ≠ y → τ x ≠ τ y := fun h h' ↦ h (τ.injective h')
  rcases hm with hm | hm
  · refine Or.inl fun a b c hab hbc hac ↦ ⟨circleCyclic_map_mono hc hm hl, fun h ↦ ?_⟩
    rcases circleCyclic_or hab hac hbc with h' | h'
    · exact h'
    · exact (not_circleCyclic_both h (circleCyclic_map_mono hc hm hl h')).elim
  · refine Or.inr fun a b c hab hbc hac ↦ ⟨circleCyclic_map_anti hc hm hl, fun h ↦ ?_⟩
    rcases circleCyclic_or hab hac hbc with h' | h'
    · exact h'
    · exact (not_circleCyclic_both h (circleCyclic_map_anti hc hm hl h')).elim

variable {X : Type} [TopologicalSpace X] [T2Space X]

/-- `r` is a direction of the set `F`: a cyclic order that comes from a parametrization of `F` by
the circle. -/
def IsDirectionOf (F : Set X) (r : X → X → X → Prop) : Prop :=
  ∃ φ : Circle → X, Continuous φ ∧ Function.Injective φ ∧ range φ = F ∧
    ∀ a b c : Circle, a ≠ b → b ≠ c → a ≠ c → (r (φ a) (φ b) (φ c) ↔ CircleCyclic a b c)

omit [T2Space X] in
theorem IsDirectionOf.swap {F : Set X} {r : X → X → X → Prop} (h : IsDirectionOf F r) {a b c : X}
  (ha : a ∈ F) (hb : b ∈ F) (hc : c ∈ F)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) : r a b c ↔ ¬ r a c b := by
  obtain ⟨φ, -, hi, rfl, hφ⟩ := h
  obtain ⟨a, rfl⟩ := ha
  obtain ⟨b, rfl⟩ := hb
  obtain ⟨c, rfl⟩ := hc
  have hab' : a ≠ b := fun h ↦ hab (by rw [h])
  have hac' : a ≠ c := fun h ↦ hac (by rw [h])
  have hbc' : b ≠ c := fun h ↦ hbc (by rw [h])
  rw [hφ a b c hab' hbc' hac', hφ a c b hac' hbc'.symm hab']
  exact ⟨fun h h' ↦ not_circleCyclic_both h h', fun h ↦ (circleCyclic_or hab' hac'
    hbc').resolve_right h⟩

theorem IsDirectionOf.same_or_reverse {F : Set X} {r r' : X → X → X → Prop} (h : IsDirectionOf F r)
  (h' : IsDirectionOf F r') :
    (∀ a b c, a ∈ F → b ∈ F → c ∈ F → a ≠ b → b ≠ c → a ≠ c → (r a b c ↔ r' a b c)) ∨
    (∀ a b c, a ∈ F → b ∈ F → c ∈ F → a ≠ b → b ≠ c → a ≠ c → (r a b c ↔ r' a c b)) := by
  obtain ⟨φ, hc, hi, rfl, hφ⟩ := h
  obtain ⟨φ', hc', hi', hr, hφ'⟩ := h'
  let e : Circle ≃ₜ range φ := (hc.isClosedEmbedding hi).isEmbedding.toHomeomorph
  let e' : Circle ≃ₜ range φ' := (hc'.isClosedEmbedding hi').isEmbedding.toHomeomorph
  let τ : Circle ≃ₜ Circle := e.trans ((Homeomorph.setCongr hr.symm).trans e'.symm)
  have hτ : ∀ x, φ' (τ x) = φ x := fun x ↦ by
    have : (e' (τ x)).1 = (e x).1 := by
      change (e' (e'.symm (Homeomorph.setCongr hr.symm (e x)))).1 = _
      rw [e'.apply_symm_apply]
      rfl
    exact this
  have hne : ∀ {x y : Circle}, x ≠ y → τ x ≠ τ y := fun h h' ↦ h (τ.injective h')
  rcases circle_map_or τ with hm | hm
  · refine Or.inl ?_
    rintro _ _ _ ⟨a, rfl⟩ ⟨b, rfl⟩ ⟨c, rfl⟩ hab hbc hac
    have hab' : a ≠ b := fun h ↦ hab (by rw [h])
    have hac' : a ≠ c := fun h ↦ hac (by rw [h])
    have hbc' : b ≠ c := fun h ↦ hbc (by rw [h])
    rw [hφ a b c hab' hbc' hac', ← hτ a, ← hτ b, ← hτ c, hφ' _ _ _ (hne hab') (hne hbc') (hne hac')]
    exact hm a b c hab' hbc' hac'
  · refine Or.inr ?_
    rintro _ _ _ ⟨a, rfl⟩ ⟨b, rfl⟩ ⟨c, rfl⟩ hab hbc hac
    have hab' : a ≠ b := fun h ↦ hab (by rw [h])
    have hac' : a ≠ c := fun h ↦ hac (by rw [h])
    have hbc' : b ≠ c := fun h ↦ hbc (by rw [h])
    rw [hφ a b c hab' hbc' hac', ← hτ a, ← hτ b, ← hτ c, hφ' _ _ _ (hne hac') (hne hbc'.symm)
      (hne hab')]
    exact hm a b c hab' hbc' hac'

/-- The relation `pos` is a direction of the boundary of each disc of `𝓕`, and nested discs of `𝓕`
agree on common boundary points.
So `pos` is an orientation, restricted to the discs of `𝓕`. -/
structure IsPartialOrientation (𝓕 : Set (Set X)) (pos : Set X → X → X → X → Prop) : Prop where
  dir : ∀ Δ ∈ 𝓕, IsClosedDisc Δ → IsDirectionOf (discBd Δ) (pos Δ)
  agree : ∀ Δ₁ ∈ 𝓕, ∀ Δ₂ ∈ 𝓕, IsClosedDisc Δ₁ → IsClosedDisc Δ₂ → Δ₁ ⊆ Δ₂ → ∀ a b c : X,
    a ∈ discBd Δ₁ ∩ discBd Δ₂ → b ∈ discBd Δ₁ ∩ discBd Δ₂ → c ∈ discBd Δ₁ ∩ discBd Δ₂ →
    a ≠ b → b ≠ c → a ≠ c → (pos Δ₁ a b c ↔ pos Δ₂ a b c)

omit [T2Space X] in
theorem SurfaceOrientation.isPartial (ω : SurfaceOrientation X) (𝓕 : Set
  (Set X)) : IsPartialOrientation 𝓕 ω.pos :=
  ⟨fun Δ _ hΔ ↦ ω.isDirection Δ hΔ, fun Δ₁ _ Δ₂ _ h₁ h₂ ↦ ω.agree Δ₁ Δ₂ h₁ h₂⟩

omit [T2Space X] in
theorem IsPartialOrientation.mono {𝓕 𝓖 : Set (Set X)} {pos : Set X → X → X → X → Prop}
  (h : IsPartialOrientation 𝓕 pos) (hs : 𝓖 ⊆ 𝓕) :
    IsPartialOrientation 𝓖 pos :=
  ⟨fun Δ hΔ ↦ h.dir Δ (hs hΔ), fun Δ₁ h₁ Δ₂ h₂ ↦ h.agree Δ₁ (hs h₁) Δ₂ (hs h₂)⟩

/-- The reverse of `pos`. -/
def revPos (pos : Set X → X → X → X → Prop) : Set X → X → X → X → Prop := fun Δ a b c ↦ pos Δ a c b

omit [T2Space X] in
theorem IsPartialOrientation.rev {𝓕 : Set (Set X)} {pos : Set X → X → X → X → Prop}
  (h : IsPartialOrientation 𝓕 pos) :
    IsPartialOrientation 𝓕 (revPos pos) := by
  refine ⟨fun Δ hΔ hd ↦ ?_, fun Δ₁ h₁ Δ₂ h₂ hd₁ hd₂ hs a b c ha hb hc hab hbc hac ↦
    h.agree Δ₁ h₁ Δ₂ h₂ hd₁ hd₂ hs a c b ha hc hb hac hbc.symm hab⟩
  obtain ⟨φ, hc, hi, hr, hφ⟩ := h.dir Δ hΔ hd
  refine ⟨fun x ↦ φ x⁻¹, by fun_prop, fun x y he ↦ inv_injective (hi he), ?_,
    fun a b c hab hbc hac ↦ ?_⟩
  · rw [← hr]
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y⁻¹, rfl⟩
    · rintro ⟨y, rfl⟩
      exact ⟨y⁻¹, by simp⟩
  · have hne : ∀ {x y : Circle}, x ≠ y → x⁻¹ ≠ y⁻¹ := fun h h' ↦ h (inv_injective h')
    change pos Δ (φ a⁻¹) (φ c⁻¹) (φ b⁻¹) ↔ _
    rw [hφ _ _ _ (hne hac) (hne hbc.symm) (hne hab)]
    refine ⟨fun h ↦ ?_, circleCyclic_inv⟩
    simpa using circleCyclic_inv h

/-- The relations `pos` and `pos'` are equal on the boundary of `Δ`. -/
def SameOn (pos pos' : Set X → X → X → X → Prop) (Δ : Set X) : Prop :=
  ∀ a b c, a ∈ discBd Δ → b ∈ discBd Δ → c ∈ discBd Δ → a ≠ b → b ≠ c → a ≠ c →
    (pos Δ a b c ↔ pos' Δ a b c)

theorem sameOn_iff_triple {pos pos' : Set X → X → X → X → Prop} {Δ : Set X} (h : IsDirectionOf
  (discBd Δ) (pos Δ))
    (h' : IsDirectionOf (discBd Δ) (pos' Δ)) {a b c : X} (ha : a ∈ discBd Δ) (hb : b ∈ discBd Δ)
      (hc : c ∈ discBd Δ) (hab : a ≠ b)
    (hbc : b ≠ c) (hac : a ≠ c) : SameOn pos pos' Δ ↔ (pos Δ a b c ↔ pos' Δ a b c) := by
  refine ⟨fun hs ↦ hs a b c ha hb hc hab hbc hac, fun he ↦ ?_⟩
  rcases h.same_or_reverse h' with h₁ | h₁
  · exact h₁
  · have h₂ := h₁ a b c ha hb hc hab hbc hac
    have h₃ := h'.swap ha hc hb hac hbc.symm hab
    have h₄ := h'.swap ha hb hc hab hbc hac
    tauto

theorem sameOn_of_notSame {pos pos' : Set X → X → X → X → Prop} {Δ : Set X} (h : IsDirectionOf
  (discBd Δ) (pos Δ))
    (h' : IsDirectionOf (discBd Δ) (pos' Δ)) (hn : ¬ SameOn pos pos' Δ) : SameOn pos
      (revPos pos') Δ :=
  (h.same_or_reverse h').resolve_left hn

/-- Nested discs with three common boundary points are alike for the comparison of two relations. -/
theorem sameOn_nested_triple {𝓕 : Set (Set X)} {pos pos' : Set X → X → X → X → Prop}
  (h : IsPartialOrientation 𝓕 pos)
    (h' : IsPartialOrientation 𝓕 pos') {Δ₁ Δ₂ : Set X} (h₁ : Δ₁ ∈ 𝓕) (h₂ : Δ₂ ∈ 𝓕)
      (hd₁ : IsClosedDisc Δ₁) (hd₂ : IsClosedDisc Δ₂)
    (hs : Δ₁ ⊆ Δ₂) (ht : HasTriple (discBd Δ₁ ∩ discBd Δ₂)) : SameOn pos pos' Δ₁ ↔ SameOn pos pos'
      Δ₂ := by
  obtain ⟨a, b, c, ha, hb, hc, hab, hbc, hac⟩ := ht
  rw [sameOn_iff_triple (h.dir _ h₁ hd₁) (h'.dir _ h₁ hd₁) ha.1 hb.1 hc.1 hab hbc hac,
    sameOn_iff_triple (h.dir _ h₂ hd₂) (h'.dir _ h₂ hd₂) ha.2 hb.2 hc.2 hab hbc hac,
    h.agree _ h₁ _ h₂ hd₁ hd₂ hs a b c ha hb hc hab hbc hac, h'.agree _ h₁ _ h₂ hd₁ hd₂ hs a b c ha
      hb hc hab hbc hac]

theorem sameOn_of_subset_discInt {𝓕 : Set (Set X)} {pos pos' : Set X → X → X → X → Prop}
  (hh : ∀ Δ ∈ 𝓕, ∀ Δ' ⊆ Δ, Δ' ∈ 𝓕)
    (h : IsPartialOrientation 𝓕 pos) (h' : IsPartialOrientation 𝓕 pos') {D₀ D₁ : Set X}
      (h₁ : D₁ ∈ 𝓕) (hd₀ : IsClosedDisc D₀)
    (hd₁ : IsClosedDisc D₁) (hs : D₀ ⊆ discInt D₁) : SameOn pos pos' D₀ ↔ SameOn pos pos' D₁ := by
  obtain ⟨Δ, hΔ, h₀Δ, hΔ₁, t₁, t₂⟩ := exists_nested_chord hd₀ hd₁ hs
  have hF : Δ ∈ 𝓕 := hh D₁ h₁ Δ hΔ₁
  have hF₀ : D₀ ∈ 𝓕 := hh Δ hF D₀ h₀Δ
  exact (sameOn_nested_triple h h' hF₀ hF hd₀ hΔ h₀Δ t₁).trans (sameOn_nested_triple h h' hF h₁ hΔ
    hd₁ hΔ₁ t₂)

/-- A closed disc has a smaller closed disc in its inside. -/
theorem exists_inner_disc {D : Set X} (hD : IsClosedDisc D) : ∃ D', IsClosedDisc D'
  ∧ D' ⊆ discInt D := by
  obtain ⟨h, g, c⟩ := hD.exists_isChart
  have hb : Convex ℝ (closedBall (0 : ℂ) (1 / 2)) := convex_closedBall _ _
  obtain ⟨hZ, -⟩ := isClosedDisc_of_convex hb (by
    rw [interior_closedBall _ (by norm_num)]
    exact ⟨0, by simp⟩) isBounded_closedBall isClosed_closedBall
  have hs : closedBall (0 : ℂ) (1 / 2) ⊆ closedBall 0 1 := closedBall_subset_closedBall
    (by norm_num)
  refine ⟨g '' closedBall 0 (1 / 2), (isClosedDisc_image_injOn hZ (c.gc.mono hs)
    (c.hg.injOn.mono hs)).1, ?_⟩
  rw [c.discInt_eq]
  exact image_mono (closedBall_subset_ball (by norm_num))

/-- Two relations are equal on a subdisc if and only if they are equal on the disc. This is the step
that makes orientations rigid. -/
theorem sameOn_of_subset (hman : ∀ x : X, IsManifoldPoint x) {𝓕 : Set (Set X)} {pos pos' : Set X
  → X → X → X → Prop}
    (hh : ∀ Δ ∈ 𝓕, ∀ Δ' ⊆ Δ, Δ' ∈ 𝓕) (h : IsPartialOrientation 𝓕 pos)
      (h' : IsPartialOrientation 𝓕 pos') {D₀ D₁ : Set X} (h₁ : D₁ ∈ 𝓕)
    (hd₀ : IsClosedDisc D₀) (hd₁ : IsClosedDisc D₁) (hs : D₀ ⊆ D₁) : SameOn pos pos' D₀ ↔ SameOn
      pos pos' D₁ := by
  obtain ⟨D', hD', hin⟩ := exists_inner_disc hd₀
  have hF₀ : D₀ ∈ 𝓕 := hh D₁ h₁ D₀ hs
  rw [← sameOn_of_subset_discInt hh h h' hF₀ hD' hd₀ hin]
  exact sameOn_of_subset_discInt hh h h' h₁ hD' hd₁ (hin.trans (discInt_mono hman hd₀ hs))

omit [T2Space X] in
/-- Around an interior point there is a closed disc inside any given open set. -/
theorem exists_small_disc {y : X} (hy : IsInteriorPoint y) {W : Set X} (hW : IsOpen W)
  (hyW : y ∈ W) :
    ∃ E : Set X, IsClosedDisc E ∧ y ∈ discInt E ∧ E ⊆ W := by
  obtain ⟨U, h, g, c, hU, hg0⟩ := hy.exists_ballChart hW hyW (R := 2) two_pos
  obtain ⟨hZ, hbd⟩ := isClosedDisc_closedBall
  have hsub : Metric.closedBall (0 : ℂ) 1 ⊆ Metric.ball 0 2 :=
    Metric.closedBall_subset_ball (by norm_num)
  obtain ⟨hE, hEb⟩ := c.image_disc hZ hsub
  refine ⟨_, hE, ⟨⟨0, by simp, hg0⟩, fun hy' ↦ ?_⟩, image_subset_iff.2 fun z hz ↦ hU (c.gm
    (hsub hz))⟩
  rw [hEb, hbd] at hy'
  obtain ⟨z, hz, hzy⟩ := hy'
  have hz' : ‖z‖ = 1 := by simpa using hz
  have h₁ : z = 0 := by
    have ha := c.hg (show z ∈ Metric.ball (0 : ℂ) 2 from hsub (Metric.sphere_subset_closedBall hz))
    have hb := c.hg (show (0 : ℂ) ∈ Metric.ball (0 : ℂ) 2 by simp)
    rw [← ha, hzy, ← hg0, hb]
  rw [h₁] at hz'
  simp at hz'

/-- **Rigidity.** Two relations on the discs of a connected open set of interior points are equal on
all discs or on none. -/
theorem sameOn_const (hman : ∀ x : X, IsManifoldPoint x) {G : Set X} (hG : IsOpen G)
  (hGc : IsPreconnected G)
    (hint : ∀ x ∈ G, IsInteriorPoint x) {pos pos' : Set X → X → X → X → Prop}
      (h : IsPartialOrientation {Δ | Δ ⊆ G} pos)
    (h' : IsPartialOrientation {Δ | Δ ⊆ G} pos') {D₁ D₂ : Set X} (hd₁ : IsClosedDisc D₁)
      (hd₂ : IsClosedDisc D₂) (hs₁ : D₁ ⊆ G)
    (hs₂ : D₂ ⊆ G) : SameOn pos pos' D₁ ↔ SameOn pos pos' D₂ := by
  have hh : ∀ Δ ∈ {Δ | Δ ⊆ G}, ∀ Δ' ⊆ Δ, Δ' ∈ {Δ | Δ ⊆ G} := fun Δ hΔ Δ' hs ↦ hs.trans hΔ
  have key : ∀ {D D' : Set X}, IsClosedDisc D → IsClosedDisc D' → D ⊆ G → D' ⊆ G →
    (discInt D ∩ discInt D').Nonempty →
      (SameOn pos pos' D ↔ SameOn pos pos' D') := by
    intro D D' hD hD' hs hs' ⟨x, hx, hx'⟩
    obtain ⟨E, hE, hxE, hEW⟩ := exists_small_disc (hint x (hs (discInt_subset D hx)))
      ((hD.isOpen_discInt hman).inter (hD'.isOpen_discInt hman)) ⟨hx, hx'⟩
    rw [← sameOn_of_subset_discInt hh h h' hs hE hD (hEW.trans inter_subset_left),
      ← sameOn_of_subset_discInt hh h h' hs' hE hD' (hEW.trans inter_subset_right)]
  let Z : Prop → Set X := fun p ↦ ⋃₀ {U | ∃ D, IsClosedDisc D ∧ D ⊆ G ∧ U = discInt D ∧
    (SameOn pos pos' D ↔ p)}
  have hop : ∀ p, IsOpen (Z p) := fun p ↦ isOpen_sUnion (by
    rintro _ ⟨D, hD, -, rfl, -⟩
    exact hD.isOpen_discInt hman)
  have hmem : ∀ {D}, IsClosedDisc D → D ⊆ G → ∀ {x}, x ∈ discInt D → x ∈ Z (SameOn pos pos' D)
    := fun hD hs _ hx ↦
    ⟨_, ⟨_, hD, hs, rfl, Iff.rfl⟩, hx⟩
  have hdisj : Disjoint (Z True) (Z False) := by
    refine disjoint_left.2 ?_
    rintro x ⟨_, ⟨D, hD, hs, rfl, ht⟩, hx⟩ ⟨_, ⟨D', hD', hs', rfl, hf⟩, hx'⟩
    have := key hD hD' hs hs' ⟨x, hx, hx'⟩
    tauto
  have hcov : G ⊆ Z True ∪ Z False := by
    intro x hx
    obtain ⟨E, hE, hxE, hEW⟩ := exists_small_disc (hint x hx) hG hx
    by_cases hc : SameOn pos pos' E
    · exact Or.inl ⟨_, ⟨E, hE, hEW, rfl, by simpa using hc⟩, hxE⟩
    · exact Or.inr ⟨_, ⟨E, hE, hEW, rfl, by simpa using hc⟩, hxE⟩
  have hex : ∀ {D}, IsClosedDisc D → D ⊆ G → ∀ p, G ⊆ Z p → (SameOn pos pos' D ↔ p) := by
    intro D hD hs p hp
    obtain ⟨x, hx⟩ := hD.nonempty_discInt
    obtain ⟨_, ⟨D', hD', hs', rfl, he⟩, hx'⟩ := hp (hs (discInt_subset D hx))
    exact (key hD hD' hs hs' ⟨x, hx, hx'⟩).trans he
  rcases hGc.subset_or_subset (hop _) (hop _) hdisj hcov with hZ | hZ
  · exact (hex hd₁ hs₁ _ hZ).trans (hex hd₂ hs₂ _ hZ).symm
  · exact (hex hd₁ hs₁ _ hZ).trans (hex hd₂ hs₂ _ hZ).symm

end GraphMinor.GM19
