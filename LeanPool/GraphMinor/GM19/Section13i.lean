/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section13h

/-!
# Graph Minors XIX, Section 13: pushing curves into a disc

The proof of (13.6) speaks of arcs that are homotopic in `Δ₀ \ {h}` to a curve in `Δ'_v`, with
`Δ'_v` simply-connected. This file has
the plain facts behind it: a set homeomorphic to a convex set is simply-connected, so lines and a
closed disc less a boundary point
are (`isSimplyConnectedSet_of_convex`), "homotopic to a curve in `Y`" is kept by joining paths
(`PushesInto.trans`), and a loop that
runs once around an `O`-arc and is null-homotopic makes the `O`-arc null-homotopic
(`null_oArc_of_loop`).
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM11 unitInterval

universe u

section Convex

variable {T : Type*} [TopologicalSpace T] {E : Type*} [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

/-- A set homeomorphic to a nonempty convex set is simply-connected. -/
theorem isSimplyConnectedSet_of_convex {A : Set E} {X : Set T} (hA : Convex ℝ A) (hne : A.Nonempty)
  (e : A ≃ₜ X) :
    IsSimplyConnectedSet X := by
  refine ⟨?_, fun φ hφ ↦ ?_⟩
  · have hpc : PathConnectedSpace A := isPathConnected_iff_pathConnectedSpace.mp
      (hA.isPathConnected hne)
    have hpc' : PathConnectedSpace X := e.surjective.pathConnectedSpace e.continuous
    exact isPathConnected_iff_pathConnectedSpace.mpr hpc'
  obtain ⟨c, hc⟩ := hne
  let c0 : A := ⟨c, hc⟩
  refine ⟨(e c0).1, (e c0).2, ?_⟩
  let lift : C(Circle, A) :=
    ⟨fun x ↦ e.symm ⟨φ x, hφ (mem_range_self x)⟩, e.symm.continuous.comp
      (φ.continuous.subtype_mk _)⟩
  have hmem : ∀ p : Circle × I, (1 - (p.2 : ℝ)) • (lift p.1).1 + (p.2 : ℝ) • c ∈ A := fun p ↦
    hA (lift p.1).2 hc (sub_nonneg.mpr p.2.2.2) p.2.2.1 (sub_add_cancel 1 (p.2 : ℝ))
  let Ψ : C(Circle × I, T) :=
    ⟨fun p ↦ (e ⟨(1 - (p.2 : ℝ)) • (lift p.1).1 + (p.2 : ℝ) • c, hmem p⟩).1,
      continuous_subtype_val.comp (e.continuous.comp
        ((Continuous.add
          (Continuous.smul (continuous_const.sub (continuous_subtype_val.comp continuous_snd))
            (continuous_subtype_val.comp (lift.continuous.comp continuous_fst)))
          (Continuous.smul (continuous_subtype_val.comp continuous_snd)
            continuous_const)).subtype_mk hmem))⟩
  refine ⟨Ψ, fun p ↦ (e ⟨_, hmem p⟩).2, fun x ↦ ?_, fun x ↦ ?_⟩
  · have hx : (⟨(1 - ((x, (0 : I)).2 : ℝ)) • (lift (x, (0 : I)).1).1 + ((x,
      (0 : I)).2 : ℝ) • c, hmem (x, 0)⟩ : A) = lift x := by
      ext
      simp
    change (e ⟨_, hmem (x, 0)⟩).1 = φ x
    rw [hx]
    exact congrArg Subtype.val (e.apply_symm_apply _)
  · have hx : (⟨(1 - ((x, (1 : I)).2 : ℝ)) • (lift (x, (1 : I)).1).1 + ((x,
      (1 : I)).2 : ℝ) • c, hmem (x, 1)⟩ : A) = c0 := by
      ext
      simp [c0]
    change (e ⟨_, hmem (x, 1)⟩).1 = (e c0).1
    rw [hx]

/-- A line is simply-connected. -/
theorem _root_.GraphMinor.Surface.IsLineWithEnds.isSimplyConnectedSet {L : Set T} {a b : T}
  (h : IsLineWithEnds L a b) : IsSimplyConnectedSet L := by
  obtain ⟨f, -, -⟩ := h
  exact isSimplyConnectedSet_of_convex (E := ℝ) (A := Icc 0 1) (convex_Icc 0 1) ⟨0, by simp⟩ f

/-- There is a path along a line from one end to the other. -/
theorem _root_.GraphMinor.Surface.IsLineWithEnds.exists_path {L : Set T} {a b : T}
  (h : IsLineWithEnds L a b) : ∃ p : Path a b, ∀ t, p t ∈ L := by
  obtain ⟨f, h0, h1⟩ := h
  exact ⟨⟨⟨fun t ↦ (f t).1, by fun_prop⟩, h0, h1⟩, fun t ↦ (f t).2⟩

/-- The closed unit disc less a point of its boundary is convex. -/
theorem convex_closedUnitDisc_diff {c : EuclideanPlane} (hc : c ∈ UnitCircle) : Convex ℝ
  (ClosedUnitDisc \ {c}) := by
  have hs : StrictConvex ℝ (Metric.closedBall (0 : EuclideanPlane) 1)
    := strictConvex_closedBall ℝ 0 1
  have hcs : ‖c‖ = 1 := by simpa [UnitCircle] using hc
  intro x hx y hy a b ha hb hab
  refine ⟨convex_closedUnitDisc hx.1 hy.1 ha hb hab, fun he ↦ ?_⟩
  have he' : a • x + b • y = c := he
  rcases ha.eq_or_lt with rfl | ha'
  · rw [zero_add] at hab
    subst hab
    apply hy.2
    simpa using he'
  rcases hb.eq_or_lt with rfl | hb'
  · rw [add_zero] at hab
    subst hab
    apply hx.2
    simpa using he'
  have hne : x ≠ y := by
    rintro rfl
    apply hx.2
    rw [← add_smul, hab, one_smul] at he'
    exact he'
  have hi := hs hx.1 hy.1 hne ha' hb' hab
  rw [interior_closedBall _ one_ne_zero, Metric.mem_ball, dist_zero_right, he', hcs] at hi
  exact lt_irrefl _ hi

/-- A closed disc less a point of its boundary is simply-connected. -/
theorem isSimplyConnectedSet_disc_diff {Δ : Set T} (hΔ : IsClosedDisc Δ) {h : T}
  (hh : h ∈ discBd Δ) : IsSimplyConnectedSet (Δ \ {h}) := by
  obtain ⟨e⟩ := hΔ
  have hb := disc_boundary Δ e
  obtain ⟨c, hc, hce⟩ : ∃ c : ClosedUnitDisc, c.1 ∈ UnitCircle ∧ (e c).1 = h := by
    rw [hb] at hh
    obtain ⟨c, hc, rfl⟩ := hh
    exact ⟨c, hc, rfl⟩
  have hA := convex_closedUnitDisc_diff hc
  have hne : (ClosedUnitDisc \ {c.1}).Nonempty := ⟨0, zero_mem_closedUnitDisc, fun h0 ↦ by
    have : ‖c.1‖ = 1 := by simpa [UnitCircle] using hc
    rw [← h0] at this
    simp at this⟩
  let f : (ClosedUnitDisc \ {c.1} : Set EuclideanPlane) ≃ₜ (Δ \ {h} : Set T) :=
    { toFun := fun a ↦ ⟨(e ⟨a.1, a.2.1⟩).1, (e ⟨a.1, a.2.1⟩).2, fun hm ↦ by
        have : e ⟨a.1, a.2.1⟩ = e c := Subtype.ext (hm.trans hce.symm)
        exact a.2.2 (congrArg Subtype.val (e.injective this))⟩
      invFun := fun x ↦ ⟨(e.symm ⟨x.1, x.2.1⟩).1, (e.symm ⟨x.1, x.2.1⟩).2, fun hm ↦ by
        have : e.symm ⟨x.1, x.2.1⟩ = c := Subtype.ext hm
        apply x.2.2
        have h₂ := congrArg (fun w ↦ (e w).1) this
        simpa [hce] using h₂⟩
      left_inv := fun a ↦ by simp
      right_inv := fun x ↦ by simp
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  exact isSimplyConnectedSet_of_convex hA hne f

end Convex

section Push

variable {T : Type*} [TopologicalSpace T]

/-- Every path along `L` from `a` to `b` is homotopic in `Z` to a path in `Y`. -/
def PushesInto (Z Y L : Set T) (a b : T) : Prop :=
  ∀ (ha : a ∈ Z) (hb : b ∈ Z) (p : Path (⟨a, ha⟩ : Z) ⟨b, hb⟩), (∀ t, (p t).1 ∈ L) →
    ∃ q : Path (⟨a, ha⟩ : Z) ⟨b, hb⟩, (∀ t, (q t).1 ∈ Y) ∧ p.Homotopic q

variable {Z Y L L₁ L₂ : Set T} {a b c : T}

/-- A set in `Y` pushes into `Y`. -/
theorem PushesInto.of_subset (h : L ⊆ Y) : PushesInto Z Y L a b := fun _ _ p hp ↦
  ⟨p, fun t ↦ h (hp t), Path.Homotopic.refl p⟩

/-- A path in `Z` staying in `L` from `a` to `b`, as a path of `Z`. -/
theorem exists_path_in (hL : L ⊆ Z) {p : Path a b} (hp : ∀ t, p t ∈ L) (ha : a ∈ Z) (hb : b ∈ Z) :
    ∃ p' : Path (⟨a, ha⟩ : Z) ⟨b, hb⟩, ∀ t, (p' t).1 = p t :=
  ⟨pathCod p ha hb fun t ↦ hL (hp t), fun _ ↦ rfl⟩

/-- Joining: if `L₁` from `a` to `c` and `L₂` from `c` to `b` push into `Y`, and `L` is
simply-connected, then `L` pushes into `Y`. -/
theorem PushesInto.trans (h₁ : PushesInto Z Y L₁ a c) (h₂ : PushesInto Z Y L₂ c b)
  (hL : IsSimplyConnectedSet L) (hLZ : L ⊆ Z)
    (hs₁ : L₁ ⊆ L) (hs₂ : L₂ ⊆ L) {p₁ : Path a c} {p₂ : Path c b} (hp₁ : ∀ t, p₁ t ∈ L₁)
      (hp₂ : ∀ t, p₂ t ∈ L₂) :
    PushesInto Z Y L a b := by
  intro ha hb p hp
  have hc : c ∈ Z := hLZ (hs₁ (by simpa using hp₁ 1))
  obtain ⟨r₁, hr₁⟩ := exists_path_in (hs₁.trans hLZ) hp₁ ha hc
  obtain ⟨r₂, hr₂⟩ := exists_path_in (hs₂.trans hLZ) hp₂ hc hb
  obtain ⟨q₁, hq₁, ho₁⟩ := h₁ ha hc r₁ fun t ↦ by rw [hr₁]; exact hp₁ t
  obtain ⟨q₂, hq₂, ho₂⟩ := h₂ hc hb r₂ fun t ↦ by rw [hr₂]; exact hp₂ t
  refine ⟨q₁.trans q₂, fun t ↦ ?_, ?_⟩
  · rw [Path.trans_apply]
    split_ifs
    · exact hq₁ _
    · exact hq₂ _
  · have haL : a ∈ L := hs₁ (by simpa using hp₁ 0)
    have hbL : b ∈ L := hs₂ (by simpa using hp₂ 1)
    have hh := homotopic_of_mem hL hLZ p (r₁.trans r₂) haL hbL hp (fun t ↦ by
      rw [Path.trans_apply]
      split_ifs
      · rw [hr₁]; exact hs₁ (hp₁ _)
      · rw [hr₂]; exact hs₂ (hp₂ _))
    exact hh.trans (ho₁.hcomp ho₂)

/-- A loop that runs once around `F`, read on the circle, is a homeomorphism onto `F`. -/
theorem exists_homeo_of_loop [T2Space T] {F : Set T} (ℓ : C(I, T)) (h01 : ℓ 0 = ℓ 1) (hr : range ℓ
  = F)
    (hinj : ∀ s t, ℓ s = ℓ t → s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0)) :
    ∃ φ : Circle ≃ₜ F, ∀ t, (φ (arcParam 1 t)).1 = ℓ t := by
  let g : C(Circle, T) := loopLift 1 ℓ h01
  have hmem : ∀ z, g z ∈ F := fun z ↦ by
    obtain ⟨t, rfl⟩ := arcParam_surjective 1 z
    rw [← hr]
    exact ⟨t, (loopLift_apply 1 ℓ h01 t).symm⟩
  let g' : Circle → F := fun z ↦ ⟨g z, hmem z⟩
  have hc : Continuous g' := g.continuous.subtype_mk _
  have hbij : Function.Bijective g' := by
    constructor
    · intro x y hxy
      obtain ⟨s, rfl⟩ := arcParam_surjective 1 x
      obtain ⟨t, rfl⟩ := arcParam_surjective 1 y
      have he : ℓ s = ℓ t := by
        have := congrArg Subtype.val hxy
        simpa [g', g] using this
      have h₀₁ : arcParam (1 : Circle) 0 = arcParam 1 1 := by
        simp [arcParam_apply]
      rcases hinj s t he with rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rfl
      · exact h₀₁
      · exact h₀₁.symm
    · rintro ⟨y, hy⟩
      rw [← hr] at hy
      obtain ⟨t, rfl⟩ := hy
      exact ⟨arcParam 1 t, Subtype.ext (loopLift_apply 1 ℓ h01 t)⟩
  have : T2Space F := inferInstance
  refine ⟨hc.homeoOfEquivCompactToT2 (f := Equiv.ofBijective g' hbij), fun t ↦ ?_⟩
  exact loopLift_apply 1 ℓ h01 t

/-- If a loop in `Z` runs once around the `O`-arc `F` and is null-homotopic in `Z`, then `F` is. -/
theorem null_oArc_of_loop [T2Space T] {F : Set T} {a : Z} (p : Path a a) (hr : range (fun t ↦
  (p t).1) = F)
    (hinj : ∀ s t, (p s).1 = (p t).1 → s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0)) (hn : p.Homotopic
      (Path.refl a)) :
    IsNullHomotopicOArcIn Z F := by
  let ℓ : C(I, T) := ⟨fun t ↦ (p t).1, by fun_prop⟩
  obtain ⟨φ, hφ⟩ := exists_homeo_of_loop ℓ (by simp [ℓ]) hr hinj
  refine ⟨φ, a.1, a.2, closedCurvesHomotopicIn_of_path 1 _ _ p (Path.refl a) (fun t ↦ (hφ t).symm)
    (fun t ↦ by simp) hn⟩

/-- Two injective paths with the same ends, meeting only at the ends: the loop formed by the first
and then the reverse of the second runs once around. -/
theorem loop_trans_injective {u v : T} (p q : Path u v) (hp : Function.Injective p)
  (hq : Function.Injective q)
    (hm : ∀ s t, p s = q t → (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1)) (s t : I)
    (h : (p.trans q.symm) s = (p.trans q.symm) t) : s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0) := by
  have key : ∀ {x y : I} (hx : (x : ℝ) ≤ 1 / 2) (hy : ¬ (y : ℝ) ≤ 1 / 2), (p.trans q.symm) x =
    (p.trans q.symm) y → x = 0 ∧ y = 1 := by
    intro x y hx hy he
    rw [Path.trans_apply, Path.trans_apply, dite_eq_left hx, dite_eq_right hy, Path.symm_apply]
      at he
    rcases hm _ _ he with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · have h₁' := congrArg Subtype.val h₁
      have h₂' := congrArg Subtype.val h₂
      simp only [Icc.coe_zero, coe_symm_eq] at h₁' h₂'
      constructor
      · apply Subtype.ext
        simp only [Icc.coe_zero]
        linarith
      · apply Subtype.ext
        simp only [Icc.coe_one]
        linarith
    · have h₂' := congrArg Subtype.val h₂
      simp only [Icc.coe_one, coe_symm_eq] at h₂'
      exfalso
      apply hy
      linarith
  by_cases hs : (s : ℝ) ≤ 1 / 2 <;> by_cases ht : (t : ℝ) ≤ 1 / 2
  · rw [Path.trans_apply, Path.trans_apply, dite_eq_left hs, dite_eq_left ht] at h
    have := congrArg Subtype.val (hp h)
    refine Or.inl (Subtype.ext ?_)
    simp only at this
    linarith
  · obtain ⟨h₁, h₂⟩ := key hs ht h
    exact Or.inr (Or.inl ⟨h₁, h₂⟩)
  · obtain ⟨h₁, h₂⟩ := key ht hs h.symm
    exact Or.inr (Or.inr ⟨h₂, h₁⟩)
  · rw [Path.trans_apply, Path.trans_apply, dite_eq_right hs, dite_eq_right ht, Path.symm_apply,
      Path.symm_apply] at h
    have := congrArg Subtype.val (hq h)
    refine Or.inl (Subtype.ext ?_)
    simp only [coe_symm_eq] at this
    linarith

end Push

end GraphMinor.GM19
