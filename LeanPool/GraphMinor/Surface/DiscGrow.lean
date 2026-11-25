/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.ArcErase
public import LeanPool.GraphMinor.Surface.Gluing
public import LeanPool.GraphMinor.Surface.DiscUnion
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Growing a closed disc along chords

Let `Y` be a set of a surface in which every `O`-arc bounds a closed disc. This file shows that a
closed disc `D ⊆ Y` can be made to swallow an `O`-arc `P ⊆ Y` that leaves `D` only finitely
often (`exists_disc_cover`).

The step is `exists_disc_of_chord`. A chord `ℓ` of `D` outside `D` makes two `O`-arcs with the two
arcs
of `bd D`. The disc bounded by the first one either contains `D`, or it meets `D` exactly in the
first arc of `bd D`, and then its union with `D` is a closed disc by `disc_union`.
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology Metric

local notation "𝕀" => unitInterval

universe u

variable {S : Type u} [TopologicalSpace S]

/-- The range of an arc is a line. -/
theorem IsArcMap.isLineWithEnds [T2Space S] {a : 𝕀 → S} (ha : IsArcMap a) :
    IsLineWithEnds (range a) (a 0) (a 1) := by
  have hemb : IsEmbedding a := (ha.1.isClosedEmbedding ha.2).isEmbedding
  exact ⟨hemb.toHomeomorph, rfl, rfl⟩

/-- A line is the range of an arc. -/
theorem IsLineWithEnds.exists_arc {L : Set S} {u v : S} (h : IsLineWithEnds L u v) :
    ∃ a : 𝕀 → S, IsArcMap a ∧ range a = L ∧ a 0 = u ∧ a 1 = v := by
  obtain ⟨f, h0, h1⟩ := h
  refine ⟨fun t => (f t).1, ⟨continuous_subtype_val.comp f.continuous,
    fun s t he => f.injective (Subtype.ext he)⟩, ?_, h0, h1⟩
  ext x
  constructor
  · rintro ⟨t, rfl⟩
    exact (f t).2
  · intro hx
    exact ⟨f.symm ⟨x, hx⟩, by simp⟩

/-- Every point of the circle is at a unique angle from `u`, in `[0, 2π)`. -/
theorem exists_circle_angle (u w : Circle) : ∃ t ∈ Ico (0 : ℝ) (2 * Real.pi), w = u * Circle.exp t
  := by
  have hpi := Real.pi_pos
  have h := Complex.arg_mem_Ioc ((u⁻¹ * w : Circle) : ℂ)
  have he := Circle.exp_arg (u⁻¹ * w)
  have he' : w = u * Circle.exp (Complex.arg ((u⁻¹ * w : Circle) : ℂ)) := by
    rw [he]
    simp
  by_cases h0 : 0 ≤ Complex.arg ((u⁻¹ * w : Circle) : ℂ)
  · exact ⟨_, ⟨h0, by linarith [h.2]⟩, he'⟩
  · refine ⟨Complex.arg ((u⁻¹ * w : Circle) : ℂ) + 2 * Real.pi, ⟨by linarith [h.1], ?_⟩, ?_⟩
    · linarith
    · rw [Circle.exp_add_two_pi]
      exact he'

/-- The two arcs of the circle from `1` to the point at angle `θ`. -/
theorem circle_two_arcs {θ : ℝ} (hθ : θ ∈ Ioo 0 (2 * Real.pi)) :
    IsArcMap (fun r : 𝕀 => Circle.exp (r.1 * θ)) ∧
    IsArcMap (fun r : 𝕀 => Circle.exp (2 * Real.pi - r.1 * (2 * Real.pi - θ))) ∧
    (∀ s t : 𝕀, Circle.exp (s.1 * θ) = Circle.exp (2 * Real.pi - t.1 * (2 * Real.pi - θ)) →
      (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1)) ∧
    ∀ w : Circle, (∃ r : 𝕀, Circle.exp (r.1 * θ) = w) ∨
      ∃ r : 𝕀, Circle.exp (2 * Real.pi - r.1 * (2 * Real.pi - θ)) = w := by
  have hpi := Real.pi_pos
  obtain ⟨h1, h2⟩ := hθ
  have hθ' : 0 < 2 * Real.pi - θ := by linarith
  refine ⟨⟨by fun_prop, ?_⟩, ⟨by fun_prop, ?_⟩, ?_, ?_⟩
  · intro s t he
    have hin : ∀ r : 𝕀, r.1 * θ ∈ Icc (0 : ℝ) θ := fun r =>
      ⟨mul_nonneg r.2.1 h1.le, by nlinarith [r.2.2]⟩
    have := Circle.exp_injOn_Icc (a := 0) (b := θ) (by linarith) (hin s) (hin t) he
    exact Subtype.ext (mul_right_cancel₀ h1.ne' this)
  · intro s t he
    have hin : ∀ r : 𝕀, 2 * Real.pi - r.1 * (2 * Real.pi - θ) ∈ Icc θ (2 * Real.pi) :=
      fun r => ⟨by nlinarith [r.2.2], by nlinarith [r.2.1]⟩
    have h5 := Circle.exp_injOn_Icc (a := θ) (b := 2 * Real.pi) (by linarith) (hin s) (hin t) he
    exact Subtype.ext (mul_right_cancel₀ hθ'.ne' (by linarith))
  · intro s t he
    obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp he
    have hs0 := s.2.1
    have hs1 := s.2.2
    have ht0 := t.2.1
    have ht1 := t.2.2
    have h3 : s.1 * θ + t.1 * (2 * Real.pi - θ) = 2 * Real.pi * (m + 1) := by linarith
    have h4 : 0 ≤ s.1 * θ + t.1 * (2 * Real.pi - θ) := by positivity
    have h5 : s.1 * θ + t.1 * (2 * Real.pi - θ) ≤ 2 * Real.pi := by nlinarith
    have h6 : (0 : ℝ) ≤ m + 1 := by
      by_contra hc
      nlinarith
    have h7 : (m : ℝ) + 1 ≤ 1 := by
      by_contra hc
      nlinarith
    have h6' : 0 ≤ m + 1 := by exact_mod_cast h6
    have h7' : m + 1 ≤ 1 := by exact_mod_cast h7
    obtain h | h : m + 1 = 0 ∨ m + 1 = 1 := by omega
    · left
      have h8 : (m : ℝ) + 1 = 0 := by exact_mod_cast h
      rw [h8, mul_zero] at h3
      have h9 : 0 ≤ s.1 * θ := by positivity
      have h10 : 0 ≤ t.1 * (2 * Real.pi - θ) := by positivity
      have h11 : s.1 * θ = 0 := by linarith
      have h12 : t.1 * (2 * Real.pi - θ) = 0 := by linarith
      exact ⟨Subtype.ext ((mul_eq_zero.mp h11).resolve_right h1.ne'),
        Subtype.ext ((mul_eq_zero.mp h12).resolve_right hθ'.ne')⟩
    · right
      have h8 : (m : ℝ) + 1 = 1 := by exact_mod_cast h
      rw [h8, mul_one] at h3
      have h9 : s.1 * θ ≤ θ := by nlinarith
      have h10 : t.1 * (2 * Real.pi - θ) ≤ 2 * Real.pi - θ := by nlinarith
      have h11 : s.1 * θ = 1 * θ := by linarith
      have h12 : t.1 * (2 * Real.pi - θ) = 1 * (2 * Real.pi - θ) := by linarith
      exact ⟨Subtype.ext (mul_right_cancel₀ h1.ne' h11), Subtype.ext (mul_right_cancel₀ hθ'.ne'
        h12)⟩
  · intro w
    obtain ⟨x, hx, rfl⟩ := exists_circle_angle 1 w
    rw [one_mul]
    rcases le_total x θ with h | h
    · refine .inl ⟨⟨x / θ, div_nonneg hx.1 h1.le, (div_le_one h1).mpr h⟩, ?_⟩
      change Circle.exp (x / θ * θ) = _
      rw [div_mul_cancel₀ _ h1.ne']
    · refine .inr ⟨⟨(2 * Real.pi - x) / (2 * Real.pi - θ), div_nonneg (by linarith [hx.2]) hθ'.le,
        (div_le_one hθ').mpr (by linarith)⟩, ?_⟩
      change Circle.exp (2 * Real.pi - (2 * Real.pi - x) / (2 * Real.pi - θ) * (2 * Real.pi - θ))
        = _
      rw [div_mul_cancel₀ _ hθ'.ne']
      congr 1
      ring

/-- Two arcs of the circle with the given ends. -/
structure IsTwoArcs {X : Type*} [TopologicalSpace X] (a b : 𝕀 → X) : Prop where
  arc_left : IsArcMap a
  arc_right : IsArcMap b
  zero : b 0 = a 0
  one : b 1 = a 1
  meet : ∀ s t, a s = b t → (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1)

/-- The two arcs of the circle between `u` and the point at angle `θ` from `u`. -/
theorem circle_two_arcs' (u : Circle) {θ : ℝ} (hθ : θ ∈ Ioo 0 (2 * Real.pi)) :
    ∃ a b : 𝕀 → Circle, IsTwoArcs a b ∧ (∀ r : 𝕀, a r = u * Circle.exp (r.1 * θ)) ∧
      (∀ r : 𝕀, b r = u * Circle.exp (2 * Real.pi - r.1 * (2 * Real.pi - θ))) ∧
      range a ∪ range b = univ := by
  obtain ⟨h1, h2, h3, h4⟩ := circle_two_arcs hθ
  have hmul : Continuous fun w : Circle => u * w := by fun_prop
  have hinj : Function.Injective fun w : Circle => u * w := mul_right_injective u
  refine ⟨fun r => u * Circle.exp (r.1 * θ),
    fun r => u * Circle.exp (2 * Real.pi - r.1 * (2 * Real.pi - θ)), ⟨⟨hmul.comp h1.1, hinj.comp
      h1.2⟩,
      ⟨hmul.comp h2.1, hinj.comp h2.2⟩, ?_, ?_, ?_⟩, fun _ => rfl, fun _ => rfl, ?_⟩
  · simp
  · simp
  · intro s t he
    exact h3 s t (hinj he)
  · rw [eq_univ_iff_forall]
    intro w
    rcases h4 (u⁻¹ * w) with ⟨r, hr⟩ | ⟨r, hr⟩
    · exact .inl ⟨r, by simp [hr]⟩
    · exact .inr ⟨r, by simp [hr]⟩

/-- Two points of an `O`-arc split it into two arcs. -/
theorem IsOArc.exists_arcs {F : Set S} (hF : IsOArc F) {x y : S} (hx : x ∈ F) (hy : y ∈ F)
    (hxy : x ≠ y) :
    ∃ a b : 𝕀 → S, IsTwoArcs a b ∧ a 0 = x ∧ a 1 = y ∧ range a ∪ range b = F := by
  obtain ⟨φ⟩ := hF
  let u : Circle := φ.symm ⟨x, hx⟩
  let v : Circle := φ.symm ⟨y, hy⟩
  have huv : u ≠ v := fun h => hxy (congrArg Subtype.val (φ.symm.injective h))
  obtain ⟨θ, hθ, hv⟩ := exists_circle_angle u v
  have hθ0 : θ ≠ 0 := fun h => huv (by simpa [h] using hv.symm)
  obtain ⟨a, b, hab, ha, hb, hr⟩ := circle_two_arcs' u (θ := θ)
    ⟨lt_of_le_of_ne hθ.1 hθ0.symm, hθ.2⟩
  have hc : Continuous fun w : Circle => (φ w).1 := continuous_subtype_val.comp φ.continuous
  have hi : Function.Injective fun w : Circle => (φ w).1 := fun _ _ h =>
    φ.injective (Subtype.ext h)
  refine ⟨fun r => (φ (a r)).1, fun r => (φ (b r)).1, ⟨⟨hc.comp hab.1.1, hi.comp hab.1.2⟩,
    ⟨hc.comp hab.2.1, hi.comp hab.2.2⟩, congrArg (fun w => (φ w).1) hab.3,
    congrArg (fun w => (φ w).1) hab.4, ?_⟩, ?_, ?_, ?_⟩
  · exact fun s t he => hab.5 s t (hi he)
  · simp [ha, u]
  · simp [ha, ← hv, v]
  · ext z
    constructor
    · rintro (⟨r, rfl⟩ | ⟨r, rfl⟩) <;> exact (φ _).2
    · intro hz
      have : φ.symm ⟨z, hz⟩ ∈ range a ∪ range b := hr ▸ mem_univ _
      rcases this with ⟨r, hr'⟩ | ⟨r, hr'⟩
      · exact .inl ⟨r, by simp [hr']⟩
      · exact .inr ⟨r, by simp [hr']⟩

/-- A proper closed set of the circle with at least two points: the part of the complement around
`z`
is the inside of an arc `a` with ends in `T`, and `b` is the other arc. -/
theorem exists_circle_chord {T : Set Circle} (hT : IsClosed T) {z x y : Circle} (hz : z ∉ T)
    (hx : x ∈ T) (hy : y ∈ T) (hxy : x ≠ y) :
    ∃ a b : 𝕀 → Circle, IsTwoArcs a b ∧ range a ∪ range b = univ ∧ a 0 ∈ T ∧ a 1 ∈ T ∧
      (∀ r, r ≠ 0 → r ≠ 1 → a r ∉ T) ∧ z ∈ range a := by
  have hpi := Real.pi_pos
  let A : Set ℝ := Icc 0 (2 * Real.pi) ∩ (fun t : ℝ => z * Circle.exp t) ⁻¹' T
  have hAc : IsCompact A :=
    isCompact_Icc.inter_right (hT.preimage (by fun_prop))
  obtain ⟨tx, htx, hx'⟩ := exists_circle_angle z x
  obtain ⟨ty, hty, hy'⟩ := exists_circle_angle z y
  have htxA : tx ∈ A := ⟨⟨htx.1, htx.2.le⟩, by change z * Circle.exp tx ∈ T; rwa [← hx']⟩
  have htyA : ty ∈ A := ⟨⟨hty.1, hty.2.le⟩, by change z * Circle.exp ty ∈ T; rwa [← hy']⟩
  obtain ⟨t₂, ht₂⟩ := hAc.exists_isLeast ⟨tx, htxA⟩
  obtain ⟨t₁, ht₁⟩ := hAc.exists_isGreatest ⟨tx, htxA⟩
  have htne : tx ≠ ty := fun h => hxy (by rw [hx', hy', h])
  have hlt : t₂ < t₁ := by
    rcases lt_or_gt_of_ne htne with h | h
    · exact (ht₂.2 htxA).trans_lt (h.trans_le (ht₁.2 htyA))
    · exact (ht₂.2 htyA).trans_lt (h.trans_le (ht₁.2 htxA))
  have hmem : ∀ t, t ∈ A → t ≠ 0 := fun t ht h => hz (by
    have : z * Circle.exp t ∈ T := ht.2
    rwa [h, Circle.exp_zero, mul_one] at this)
  have ht₂0 : 0 < t₂ := lt_of_le_of_ne ht₂.1.1.1 (hmem _ ht₂.1).symm
  have ht₁2 : t₁ < 2 * Real.pi := by
    refine lt_of_le_of_ne ht₁.1.1.2 fun h => hz ?_
    have : z * Circle.exp t₁ ∈ T := ht₁.1.2
    rwa [h, Circle.exp_two_pi, mul_one] at this
  set θ := t₂ - t₁ + 2 * Real.pi with hθdef
  have hθ : θ ∈ Ioo 0 (2 * Real.pi) := ⟨by linarith, by linarith⟩
  set u := z * Circle.exp (t₁ - 2 * Real.pi) with hu
  obtain ⟨a, b, hab, ha, hb, hr⟩ := circle_two_arcs' u hθ
  have hval : ∀ r : ℝ, u * Circle.exp (r * θ) = z * Circle.exp (t₁ - 2 * Real.pi + r * θ) := by
    intro r
    rw [hu, mul_assoc, ← Circle.exp_add]
  refine ⟨a, b, hab, hr, ?_, ?_, ?_, ?_⟩
  · rw [ha, hval]
    simp only [Set.Icc.coe_zero, zero_mul, add_zero, Circle.exp_sub_two_pi]
    exact ht₁.1.2
  · rw [ha, hval]
    have : t₁ - 2 * Real.pi + ((1 : 𝕀) : ℝ) * θ = t₂ := by simp [hθdef]
    rw [this]
    exact ht₂.1.2
  · intro r h0 h1 hmemT
    have hr0 : 0 < r.1 := lt_of_le_of_ne r.2.1 fun h => h0 (Subtype.ext h.symm)
    have hr1 : r.1 < 1 := lt_of_le_of_ne r.2.2 fun h => h1 (Subtype.ext h)
    rw [ha, hval] at hmemT
    set τ := t₁ - 2 * Real.pi + r.1 * θ with hτ
    have hτ1 : t₁ - 2 * Real.pi < τ := by
      have := mul_pos hr0 hθ.1
      linarith
    have hτ2 : τ < t₂ := by
      have := mul_lt_mul_of_pos_right hr1 hθ.1
      simp only [one_mul] at this
      linarith
    rcases lt_trichotomy τ 0 with h | h | h
    · have hm : τ + 2 * Real.pi ∈ A := ⟨⟨by linarith, by linarith⟩, by
        change z * Circle.exp (τ + 2 * Real.pi) ∈ T
        rwa [Circle.exp_add_two_pi]⟩
      have := ht₁.2 hm
      linarith
    · rw [h, Circle.exp_zero, mul_one] at hmemT
      exact hz hmemT
    · have hm : τ ∈ A := ⟨⟨h.le, by linarith⟩, hmemT⟩
      have := ht₂.2 hm
      linarith
  · have h0 : 0 < 2 * Real.pi - t₁ := by linarith
    refine ⟨⟨(2 * Real.pi - t₁) / θ, div_nonneg h0.le hθ.1.le, ?_⟩, ?_⟩
    · rw [div_le_one hθ.1]
      linarith
    · rw [ha, hval]
      simp only
      rw [div_mul_cancel₀ _ hθ.1.ne']
      simp

/-! ### The inside of a closed disc -/

/-- A closed disc minus its boundary. -/
def discInt (D : Set S) : Set S := D \ discBd D

private theorem interior_eq_discInt_of_frontier {S : Type*} [TopologicalSpace S]
    {D : Set S} (hClosed : IsClosed D) (hfr : frontier D = discBd D) :
    interior D = discInt D := by
  ext x
  simp only [discInt, mem_sdiff, ← hfr, frontier, hClosed.closure_eq]
  exact ⟨fun hx ↦ ⟨interior_subset hx, fun h ↦ h.2 hx⟩,
    fun ⟨hxD, hnf⟩ ↦ by_contra fun hni ↦ hnf ⟨hxD, hni⟩⟩

theorem interior_eq_discInt_complex {Δ : Set ℂ} (hΔ : IsClosedDisc Δ) :
    interior Δ = discInt Δ :=
  interior_eq_discInt_of_frontier hΔ.isCompact.isClosed (complex_disc_frontier hΔ)

theorem interior_eq_discInt_euclideanPlane {D : Set EuclideanPlane} (hD : IsClosedDisc D) :
    interior D = discInt D :=
  interior_eq_discInt_of_frontier hD.isCompact.isClosed (plane_disc_frontier hD)

theorem IsChart.discInt_eq {D : Set S} {h : S → ℂ} {g : ℂ → S} (c : IsChart D h g) :
    discInt D = g '' ball 0 1 := by
  obtain ⟨h1, h2⟩ := c.union_ball
  ext x
  constructor
  · rintro ⟨hx, hb⟩
    rw [← h1] at hx
    exact hx.resolve_right hb
  · intro hx
    exact ⟨h1 ▸ .inl hx, Set.disjoint_left.mp h2 hx⟩

theorem IsClosedDisc.isOpen_discInt (hman : ∀ x : S, IsManifoldPoint x) {D : Set S}
    (hD : IsClosedDisc D) : IsOpen (discInt D) := by
  obtain ⟨h, g, c⟩ := hD.exists_isChart
  rw [c.discInt_eq]
  exact c.isOpen_image_ball hman

theorem IsClosedDisc.isPreconnected_discInt {D : Set S} (hD : IsClosedDisc D) :
    IsPreconnected (discInt D) := by
  obtain ⟨h, g, c⟩ := hD.exists_isChart
  rw [c.discInt_eq]
  exact (convex_ball (0 : ℂ) 1).isPreconnected.image g (c.gc.mono ball_subset_closedBall)

theorem IsClosedDisc.nonempty_discInt {D : Set S} (hD : IsClosedDisc D) : (discInt D).Nonempty := by
  obtain ⟨h, g, c⟩ := hD.exists_isChart
  rw [c.discInt_eq]
  exact ⟨g 0, 0, by simp, rfl⟩

theorem IsClosedDisc.subset_closure_discInt {D : Set S} (hD : IsClosedDisc D) :
    D ⊆ closure (discInt D) := by
  obtain ⟨h, g, c⟩ := hD.exists_isChart
  rw [c.discInt_eq, ← c.g_closedBall]
  have : closedBall (0 : ℂ) 1 = closure (ball 0 1) := (closure_ball 0 one_ne_zero).symm
  rw [this]
  exact ContinuousOn.image_closure (by rw [← this]; exact c.gc)

theorem IsClosedDisc.isClosed [T2Space S] {D : Set S} (hD : IsClosedDisc D) : IsClosed D :=
  hD.isCompact.isClosed

theorem discInt_subset (D : Set S) : discInt D ⊆ D := sdiff_subset

/-- A connected set that misses the boundary of a closed disc is inside the disc or disjoint from
it. -/
theorem IsClosedDisc.side [T2Space S] (hman : ∀ x : S, IsManifoldPoint x) {D C : Set S}
    (hD : IsClosedDisc D) (hC : IsPreconnected C) (hbd : Disjoint C (discBd D)) :
    C ⊆ discInt D ∨ Disjoint C D := by
  have hcover : C ⊆ discInt D ∪ Dᶜ := fun x hx => by
    by_cases h : x ∈ D
    · exact .inl ⟨h, Set.disjoint_left.mp hbd hx⟩
    · exact .inr h
  have hdisj : Disjoint (discInt D) Dᶜ := Set.disjoint_left.mpr fun x hx hx' => hx' hx.1
  rcases hC.subset_or_subset (hD.isOpen_discInt hman) hD.isClosed.isOpen_compl hdisj hcover with h
    | h
  · exact .inl h
  · exact .inr (Set.disjoint_left.mpr fun x hx hx' => h hx hx')

/-- **A chord of a closed disc.** See the module docstring. -/
theorem exists_disc_of_chord [T2Space S] (hman : ∀ x : S, IsManifoldPoint x) {Y D : Set S}
    (hDY : D ⊆ Y) (hD : IsClosedDisc D)
    (H : ∀ F : Set S, F ⊆ Y → IsOArc F → ∃ Δ : Set S, Δ ⊆ Y ∧ IsClosedDisc Δ ∧ discBd Δ = F)
    {ℓ : 𝕀 → S} (hℓ : IsArcMap ℓ) (hℓY : range ℓ ⊆ Y) (h0 : ℓ 0 ∈ discBd D) (h1 : ℓ 1 ∈ discBd D)
    (hmeet : ∀ r, ℓ r ∈ D → r = 0 ∨ r = 1) :
    ∃ D₁ : Set S, D₁ ⊆ Y ∧ IsClosedDisc D₁ ∧ D ⊆ D₁ ∧ range ℓ ⊆ D₁ ∧
      discBd D₁ ⊆ discBd D ∪ range ℓ := by
  have hne : ℓ 0 ≠ ℓ 1 := fun h => zero_ne_one (hℓ.2 h)
  obtain ⟨a, b, hab, ha0, ha1, hr⟩ := (hD.isOArc_discBd).exists_arcs h0 h1 hne
  have hbdD : discBd D ⊆ D := discBd_subset D
  have haD : range a ⊆ discBd D := hr ▸ subset_union_left
  have hbD : range b ⊆ discBd D := hr ▸ subset_union_right
  have hmeetℓ : ∀ s t, a s = ℓ t → (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1) := by
    intro s t he
    rcases hmeet t (hbdD (haD ⟨s, he⟩)) with rfl | rfl
    · exact .inl ⟨hab.1.2 (by rw [he, ha0]), rfl⟩
    · exact .inr ⟨hab.1.2 (by rw [he, ha1]), rfl⟩
  have hO : IsOArc (range a ∪ range ℓ) :=
    oArc_of_two_arcs hab.1 hℓ ha0 ha1 hmeetℓ
  have hsubY : range a ∪ range ℓ ⊆ Y :=
    union_subset (haD.trans (hbdD.trans hDY)) hℓY
  obtain ⟨Δ, hΔY, hΔ, hΔb⟩ := H _ hsubY hO
  have hsubΔ : range a ∪ range ℓ ⊆ Δ := hΔb ▸ discBd_subset Δ
  -- the inside of `D` misses the boundary of `Δ`
  have hdisj : Disjoint (discInt D) (discBd Δ) := by
    rw [hΔb, Set.disjoint_left]
    rintro x ⟨hx, hx'⟩ (⟨s, rfl⟩ | ⟨t, rfl⟩)
    · exact hx' (haD ⟨s, rfl⟩)
    · rcases hmeet t hx with rfl | rfl
      · exact hx' h0
      · exact hx' h1
  rcases hΔ.side hman hD.isPreconnected_discInt hdisj with hin | hout
  · refine ⟨Δ, hΔY, hΔ, ?_, subset_union_right.trans hsubΔ, ?_⟩
    · exact hD.subset_closure_discInt.trans
        (closure_minimal (hin.trans (discInt_subset Δ)) hΔ.isClosed)
    · rw [hΔb]
      exact union_subset_union_left _ haD
  -- the other arc of `D` lies outside `Δ`
  have hbout : ∀ t, t ≠ 0 → t ≠ 1 → b t ∉ Δ := by
    intro t ht0 ht1 hmem
    have hbt : b t ∉ discBd Δ := by
      rw [hΔb]
      rintro (⟨s, hs⟩ | ⟨r, hr'⟩)
      · rcases hab.5 s t hs with ⟨-, rfl⟩ | ⟨-, rfl⟩
        · exact ht0 rfl
        · exact ht1 rfl
      · have hbDt : b t ∈ D := hbdD (hbD ⟨t, rfl⟩)
        rw [← hr'] at hbDt
        rcases hmeet r hbDt with rfl | rfl
        · apply ht0
          apply hab.2.2
          rw [← hr', hab.3, ha0]
        · apply ht1
          apply hab.2.2
          rw [← hr', hab.4, ha1]
    have hint : b t ∈ discInt Δ := ⟨hmem, hbt⟩
    have hbtcl : b t ∈ closure (discInt D) := hD.subset_closure_discInt (hbdD (hbD ⟨t, rfl⟩))
    obtain ⟨w, hw1, hw2⟩ := mem_closure_iff.mp hbtcl _ (hΔ.isOpen_discInt hman) hint
    exact Set.disjoint_left.mp hout hw2 hw1.1
  have hinter : Δ ∩ D = range a := by
    ext x
    constructor
    · rintro ⟨hx, hx'⟩
      by_cases hb : x ∈ discBd D
      · rw [← hr] at hb
        rcases hb with hb | ⟨t, rfl⟩
        · exact hb
        · by_cases ht0 : t = 0
          · subst ht0
            exact ⟨0, hab.3.symm⟩
          by_cases ht1 : t = 1
          · subst ht1
            exact ⟨1, hab.4.symm⟩
          exact absurd hx (hbout t ht0 ht1)
      · exact absurd hx (Set.disjoint_left.mp hout ⟨hx', hb⟩)
    · intro hx
      exact ⟨hsubΔ (.inl hx), hbdD (haD hx)⟩
  have hu := disc_union.{u} Δ D (range a) (a 0) (a 1) hΔ hD hab.1.isLineWithEnds hinter
    (hΔb ▸ subset_union_left) haD
  refine ⟨Δ ∪ D, union_subset hΔY hDY, hu.1, subset_union_right, ?_, ?_⟩
  · exact (subset_union_right.trans hsubΔ).trans subset_union_left
  · rw [hu.2, hΔb]
    rintro x ⟨(h | h) | h, -⟩
    · exact .inl (haD h)
    · exact .inr h
    · exact .inl h

/-- **A closed disc swallows an `O`-arc.** Let `D ⊆ Y` be a closed disc and `P ⊆ Y` an `O`-arc that
meets `D` in at least two points, such that `P \ D` is a finite union of connected sets. Then some
closed disc of `Y` contains `D` and `P`. Each step adds one chord, and the chord removes at least
one of the connected sets. -/
theorem exists_disc_cover [T2Space S] (hman : ∀ x : S, IsManifoldPoint x) {Y P : Set S}
    (H : ∀ F : Set S, F ⊆ Y → IsOArc F → ∃ Δ : Set S, Δ ⊆ Y ∧ IsClosedDisc Δ ∧ discBd Δ = F)
    (hPY : P ⊆ Y) (hP : IsOArc P) {x y : S} (hx : x ∈ P) (hy : y ∈ P) (hxy : x ≠ y)
    (n : ℕ) : ∀ (D : Set S) (F : Set (Set S)), D ⊆ Y → IsClosedDisc D → x ∈ D → y ∈ D → F.Finite →
      F.ncard ≤ n → (∀ J ∈ F, IsPreconnected J) → ⋃₀ F = P \ D →
      ∃ D' : Set S, D' ⊆ Y ∧ IsClosedDisc D' ∧ D ⊆ D' ∧ P ⊆ D' := by
  obtain ⟨φ⟩ := id hP
  let j : Circle → S := fun w => (φ w).1
  have hjc : Continuous j := continuous_subtype_val.comp φ.continuous
  have hji : Function.Injective j := fun _ _ h => φ.injective (Subtype.ext h)
  have hjemb : IsEmbedding j := (hjc.isClosedEmbedding hji).isEmbedding
  have hjr : range j = P := by
    ext z
    constructor
    · rintro ⟨w, rfl⟩
      exact (φ w).2
    · intro hz
      exact ⟨φ.symm ⟨z, hz⟩, by simp [j]⟩
  induction n with
  | zero =>
    intro D F hDY hD hxD hyD hF hc h1 h2
    have hF0 : F = ∅ := (Set.ncard_eq_zero hF).mp (Nat.le_zero.mp hc)
    rw [hF0, sUnion_empty] at h2
    exact ⟨D, hDY, hD, subset_rfl, sdiff_eq_empty.mp h2.symm⟩
  | succ n ih =>
    intro D F hDY hD hxD hyD hF hc h1 h2
    by_cases hsub : P ⊆ D
    · exact ⟨D, hDY, hD, subset_rfl, hsub⟩
    obtain ⟨z, hzP, hzD⟩ := not_subset.mp hsub
    rw [← hjr] at hzP
    obtain ⟨z', rfl⟩ := hzP
    have hx' : x ∈ range j := hjr ▸ hx
    have hy' : y ∈ range j := hjr ▸ hy
    obtain ⟨x', rfl⟩ := hx'
    obtain ⟨y', rfl⟩ := hy'
    have hT : IsClosed (j ⁻¹' D) := hD.isClosed.preimage hjc
    obtain ⟨a, b, hab, hcov, ha0, ha1, hamid, hzr⟩ := exists_circle_chord hT (z := z') (x := x')
      (y := y') hzD hxD hyD fun h => hxy (congrArg j h)
    let ℓ : 𝕀 → S := fun r => j (a r)
    have hℓ : IsArcMap ℓ := ⟨hjc.comp hab.1.1, hji.comp hab.1.2⟩
    have hℓP : range ℓ ⊆ P := by
      rintro _ ⟨r, rfl⟩
      exact hjr ▸ mem_range_self _
    have hmeet : ∀ r, ℓ r ∈ D → r = 0 ∨ r = 1 := fun r hr => by
      by_contra hcon
      push Not at hcon
      exact hamid r hcon.1 hcon.2 hr
    have hbdend : ∀ r₀ : 𝕀, ℓ r₀ ∈ D → r₀ ∈ closure (Ioo (0 : 𝕀) 1) → ℓ r₀ ∈ discBd D := by
      intro r₀ h3 h4
      by_contra hcon
      have hopen := (hD.isOpen_discInt hman).preimage hℓ.1
      obtain ⟨r, hr1, hr2⟩ := mem_closure_iff.mp h4 _ hopen ⟨h3, hcon⟩
      rcases hmeet r hr1.1 with rfl | rfl
      · exact lt_irrefl _ hr2.1
      · exact lt_irrefl _ hr2.2
    have hcl : closure (Ioo (0 : 𝕀) 1) = Icc 0 1 := closure_Ioo zero_ne_one
    obtain ⟨D₁, hD₁Y, hD₁, hDD₁, hℓD₁, hbdD₁⟩ := exists_disc_of_chord hman hDY hD H hℓ
      (hℓP.trans hPY) (hbdend 0 ha0 (hcl ▸ ⟨le_rfl, zero_le_one⟩))
      (hbdend 1 ha1 (hcl ▸ ⟨zero_le_one, le_rfl⟩)) hmeet
    classical
    let F₁ : Set (Set S) := {J ∈ F | Disjoint J D₁}
    have hF₁sub : F₁ ⊆ F := fun J hJ => hJ.1
    have hF₁fin : F₁.Finite := hF.subset hF₁sub
    obtain ⟨J₀, hJ₀, hzJ₀⟩ : j z' ∈ ⋃₀ F := by
      rw [h2]
      exact ⟨hjr ▸ mem_range_self _, hzD⟩
    have hzD₁ : j z' ∈ D₁ := by
      obtain ⟨r, rfl⟩ := hzr
      exact hℓD₁ ⟨r, rfl⟩
    have hJ₀F₁ : J₀ ∉ F₁ := fun h => Set.disjoint_left.mp h.2 hzJ₀ hzD₁
    have hcount : F₁.ncard ≤ n := by
      have h5 : F₁.ncard < F.ncard := Set.ncard_lt_ncard
        ⟨hF₁sub, fun h => hJ₀F₁ (h hJ₀)⟩ hF
      omega
    have hU : ⋃₀ F₁ = P \ D₁ := by
      ext w
      constructor
      · rintro ⟨J, hJ, hw⟩
        have h6 : w ∈ P \ D := h2 ▸ mem_sUnion_of_mem hw hJ.1
        exact ⟨h6.1, fun h => Set.disjoint_left.mp hJ.2 hw h⟩
      · rintro ⟨hwP, hwD₁⟩
        have hwD : w ∉ D := fun h => hwD₁ (hDD₁ h)
        obtain ⟨J, hJ, hwJ⟩ : w ∈ ⋃₀ F := by
          rw [h2]
          exact ⟨hwP, hwD⟩
        have hJP : J ⊆ P \ D := by
          rw [← h2]
          exact subset_sUnion_of_mem hJ
        refine ⟨J, ⟨hJ, ?_⟩, hwJ⟩
        have hJ'p : IsPreconnected (j ⁻¹' J) := by
          rw [← hjemb.isInducing.isPreconnected_image,
            image_preimage_eq_of_subset (by rw [hjr]; exact hJP.trans sdiff_subset)]
          exact h1 J hJ
        have hJℓ : Disjoint J (range ℓ) := by
          rw [Set.disjoint_left]
          rintro v hv ⟨r, rfl⟩
          have hvend : r ≠ 0 ∧ r ≠ 1 := by
            constructor
            · rintro rfl
              exact (hJP hv).2 ha0
            · rintro rfl
              exact (hJP hv).2 ha1
          have hw' : w ∈ range j := hjr ▸ hwP
          obtain ⟨w', rfl⟩ := hw'
          have hsep := hJ'p (range b)ᶜ (range a)ᶜ (isCompact_range hab.2.1).isClosed.isOpen_compl
            (isCompact_range hab.1.1).isClosed.isOpen_compl ?_ ?_ ?_
          · obtain ⟨u, -, h7, h8⟩ := hsep
            have : u ∈ range a ∪ range b := hcov ▸ mem_univ u
            exact this.elim h8 h7
          · intro u hu
            by_cases hua : u ∈ range a
            · refine .inl ?_
              obtain ⟨s, rfl⟩ := hua
              rintro ⟨t, ht⟩
              have hs01 : s ≠ 0 ∧ s ≠ 1 := by
                constructor
                · rintro rfl
                  exact (hJP hu).2 ha0
                · rintro rfl
                  exact (hJP hu).2 ha1
              rcases hab.5 s t ht.symm with ⟨h9, -⟩ | ⟨h9, -⟩
              · exact hs01.1 h9
              · exact hs01.2 h9
            · exact .inr hua
          · refine ⟨a r, hv, ?_⟩
            rintro ⟨t, ht⟩
            rcases hab.5 r t ht.symm with ⟨h9, -⟩ | ⟨h9, -⟩
            · exact hvend.1 h9
            · exact hvend.2 h9
          · refine ⟨w', hwJ, ?_⟩
            rintro ⟨t, ht⟩
            exact hwD₁ (hℓD₁ ⟨t, by change j (a t) = j w'; rw [ht]⟩)
        have hJbd : Disjoint J (discBd D₁) := by
          rw [Set.disjoint_left]
          intro v hv hv'
          rcases hbdD₁ hv' with h7 | h7
          · exact (hJP hv).2 (discBd_subset D h7)
          · exact Set.disjoint_left.mp hJℓ hv h7
        rcases hD₁.side hman (h1 J hJ) hJbd with h7 | h7
        · exact absurd (h7 hwJ).1 hwD₁
        · exact h7
    obtain ⟨D', h3, h4, h5, h6⟩ := ih D₁ F₁ hD₁Y hD₁ (hDD₁ hxD) (hDD₁ hyD) hF₁fin hcount
      (fun J hJ => h1 J hJ.1) hU
    exact ⟨D', h3, h4, hDD₁.trans h5, h6⟩

end GraphMinor.Surface
