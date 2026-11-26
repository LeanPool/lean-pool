/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.CuffOrder
public import LeanPool.GraphMinor.GM12.Section4ThinArcDisc

/-!
# Order data of the pads of edges

For the pad of an internal edge of `Γ₀` there are at most three ends, each with its own vertex. So
the order data are simple: we read each end at the place of its vertex (`padOrder_of_injOn`). With
two ends
there is nothing to check, and with three ends it is enough to compare one triple
(`padOrder_of_triple`). We also compare a given partial orientation with the orientation of a pad
read from its chart
(`exists_chart_sign`, `chart_cyc`), and we thicken lines into discs that meet only in given points
(`exists_thin_family`).
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Metric Topology GraphMinor.Surface

variable {T : Type} [TopologicalSpace T] [T2Space T]

theorem isPosParam_unit : IsPosParam (closedBall 0 1) fun w : Circle => (w : ℂ) := by
  have hc : Continuous fun _ : Circle => (1 : ℝ) := continuous_const
  have hp : ∀ _ : Circle, (0 : ℝ) < 1 := fun _ => one_pos
  have h := isPosParam_star hc hp
  have hid : ∀ z, starHomeo hc hp z = z := fun z => by
    rw [starHomeo_apply]
    by_cases hz : z = 0
    · simp [starMap, hz]
    · simp [starMap, hz]
  have hS : starDisc hc hp = closedBall 0 1 := by
    simp [starDisc, hid]
  rw [hS] at h
  simpa using h

omit [T2Space T] in
/-- The orientation of the plane on a pad, read off the chart. -/
theorem chart_cyc {C : Set T} {c : T → ℂ} {g : ℂ → T} (hch : IsChart C c g) {x y z : T}
  (hx : x ∈ discBd C) (hy : y ∈ discBd C) (hz : z ∈ discBd C) :
    pullPos c planePos C x y z ↔ CircleCyclic (toCircle (c x)) (toCircle (c y)) (toCircle (c z))
      := by
  have him : c '' C = closedBall 0 1 := by
    ext w
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact hch.hm hp
    · exact fun hw => ⟨g w, hch.gm hw, hch.hg hw⟩
  have hc : ∀ {p}, p ∈ discBd C → ((toCircle (c p) : Circle) : ℂ) = c p := fun {p} hp => by
    have : c p ∈ sphere (0 : ℂ) 1 := by rw [← hch.bd]; exact mem_image_of_mem c hp
    exact coe_toCircle (by simpa using this)
  change planePos (c '' C) (c x) (c y) (c z) ↔ _
  rw [him]
  have h := planePos_iff isClosedDisc_closedBall.1 isPosParam_unit (toCircle (c x)) (toCircle
    (c y)) (toCircle (c z))
  simp only [hc hx, hc hy, hc hz] at h
  exact h

/-- Either a partial orientation or its reverse agrees with the chart of a pad. -/
theorem exists_chart_sign (hT : IsClosedSurface T) {𝓖 : Set (Set T)} {ϖ₀ : Set T → T → T → T
  → Prop} (hpart : IsPartialOrientation 𝓖 ϖ₀) (hh : ∀ Δ ∈ 𝓖, ∀ Δ' ⊆ Δ, Δ' ∈ 𝓖) {C : Set T} {c : T
    → ℂ} {g : ℂ → T}
    (hC : C ∈ 𝓖) (hd : IsClosedDisc C) (hch : IsChart C c g) :
    ∃ ϖ, (ϖ = ϖ₀ ∨ ϖ = revPos ϖ₀) ∧ IsPartialOrientation 𝓖 ϖ ∧ ∀ D, IsClosedDisc D → D ⊆ C
      → SameOn ϖ (pullPos c planePos) D := by
  have hman : ∀ x : T, IsManifoldPoint x := fun x => (hT.2.2 x).isManifoldPoint
  let 𝓙 : Set (Set T) := {D | D ⊆ C}
  have hci : InjOn c C := fun x hx y hy h => by rw [← hch.gh hx, ← hch.gh hy, h]
  have hJ : IsPartialOrientation 𝓙 (pullPos c planePos) := (planeOrientation.isPartial univ).pull
    fun Δ hΔ => ⟨hch.hc.mono hΔ, hci.mono hΔ, mem_univ _⟩
  have hhJ : ∀ Δ ∈ 𝓙, ∀ Δ' ⊆ Δ, Δ' ∈ 𝓙 := fun Δ hΔ Δ' hs => hs.trans hΔ
  have hJG : 𝓙 ⊆ 𝓖 := fun D hD => hh C hC D hD
  have hd₂ := hJ.dir C (Subset.refl C) hd
  obtain ⟨ϖ, h1, h2, h3⟩ : ∃ ϖ, (ϖ = ϖ₀ ∨ ϖ = revPos ϖ₀) ∧ IsPartialOrientation 𝓖 ϖ ∧ SameOn ϖ
    (pullPos c planePos) C := by
    by_cases hs : SameOn ϖ₀ (pullPos c planePos) C
    · exact ⟨ϖ₀, Or.inl rfl, hpart, hs⟩
    · exact ⟨revPos ϖ₀, Or.inr rfl, hpart.rev, sameOn_rev_left (sameOn_of_notSame
        (hpart.dir C hC hd) hd₂ hs)⟩
  exact ⟨ϖ, h1, h2, fun D hD hs => (sameOn_of_subset hman hhJ (h2.mono hJG) hJ
    (Subset.refl C) hD hd hs).2 h3⟩

omit [T2Space T] in
/-- Order data when each end has its own vertex: each end sits at the place of its vertex. -/
theorem padOrder_of_injOn {C : Set T} {c : T → ℂ} {g : ℂ → T} (hch : IsChart C c g) {q : Circle
  → T} {Y : Set T} {φ : T → T} (hY : Y.Finite) (hsub : Y ⊆ range q) (hq : Function.Injective q)
    (hφ : ∀ y ∈ Y, φ y ∈ discBd C) (hi : InjOn φ Y) (hcyc : ∀ a b d, q a ∈ Y → q b ∈ Y → q d ∈ Y
      → a ≠ b → b ≠ d → a ≠ d → (CircleCyclic a b d ↔ CircleCyclic (toCircle (c (φ (q a))))
        (toCircle (c (φ (q b)))) (toCircle (c (φ (q d)))))) :
    ∃ A U : T → ℝ, PadOrder q g Y φ A U := by
  classical
  have hc : ∀ {p}, p ∈ discBd C → ((toCircle (c p) : Circle) : ℂ) = c p := fun {p} hp => by
    have : c p ∈ sphere (0 : ℂ) 1 := by rw [← hch.bd]; exact mem_image_of_mem c hp
    exact coe_toCircle (by simpa using this)
  have hex : ∀ y, ∃ s : ℝ, 0 ≤ s ∧ s < 1 ∧ toCircle (c (φ y)) = ee s := fun y => exists_ee _
  choose U hU0 hU1 hUe using hex
  have hinj : InjOn U Y := fun x hx y hy he => by
    have h1 : c (φ x) = c (φ y) := by rw [← hc (hφ x hx), ← hc (hφ y hy), hUe, hUe, he]
    have h2 : φ x = φ y := by
      rw [← hch.gh (Surface.discBd_subset _ (hφ x hx)),
        ← hch.gh (Surface.discBd_subset _ (hφ y hy)), h1]
    exact hi hx hy h2
  refine ⟨U, U, hY, hsub, fun y _ => ⟨hU0 y, (hU1 y).le⟩, fun y _ => ⟨hU0 y, (hU1 y).le⟩,
    fun y hy => ?_, fun x _ y _ h => h.le, hinj, fun a b d ha hb hd hab hbd had => ?_⟩
  · rw [← hUe, hc (hφ y hy)]
    exact hch.gh (Surface.discBd_subset _ (hφ y hy))
  · have hne : ∀ {p p' : Circle}, q p ∈ Y → q p' ∈ Y → p ≠ p' → U (q p) ≠ U (q p')
      := fun hp hp' h he => h (hq (hinj hp hp' he))
    rw [hcyc a b d ha hb hd hab hbd had, hUe, hUe, hUe]
    have hw : ∀ x y, U x < U y + 1 := fun x y => by linarith [hU1 x, hU0 y]
    exact circleCyclic_ee_iff (hw _ _) (hw _ _) (hw _ _) (hw _ _) (hw _ _) (hw _ _) (hne ha hb hab)
      (hne hb hd hbd) (hne ha hd had)

theorem circleCyclic_rotate_iff {a b c : Circle} : CircleCyclic a b c ↔ CircleCyclic b c a :=
  ⟨CircleCyclic.rotate, fun h => h.rotate.rotate⟩

theorem circleCyclic_swap_iff {a b c : Circle} (hab : a ≠ b) (hbc : b ≠ c)
  (hac : a ≠ c) : CircleCyclic a c b ↔ ¬ CircleCyclic a b c :=
  ⟨fun h h' => not_circleCyclic_both h' h, fun h => (circleCyclic_or hab hac hbc).resolve_left h⟩

/-- If one triple of points has the same cyclic order as another, then so does each reordering. -/
theorem cyclic_perm {a b c a' b' c' : Circle} (h1 : a ≠ b) (h2 : b ≠ c) (h3 : a ≠ c)
  (h1' : a' ≠ b') (h2' : b' ≠ c') (h3' : a' ≠ c') (h : CircleCyclic a b c ↔ CircleCyclic a' b' c') :
    (CircleCyclic b c a ↔ CircleCyclic b' c' a') ∧ (CircleCyclic c a b ↔ CircleCyclic c' a' b') ∧
      (CircleCyclic a c b ↔ CircleCyclic a' c' b') ∧ (CircleCyclic c b a ↔ CircleCyclic c' b' a') ∧
      (CircleCyclic b a c ↔ CircleCyclic b' a' c') := by
  have rot : ∀ {x y z x' y' z' : Circle}, (CircleCyclic x y z ↔ CircleCyclic x' y' z') →
    (CircleCyclic y z x ↔ CircleCyclic y' z' x') := fun h =>
    circleCyclic_rotate_iff.symm.trans (h.trans circleCyclic_rotate_iff)
  have r1 := rot h
  have s1 : CircleCyclic a c b ↔ CircleCyclic a' c' b' := (circleCyclic_swap_iff h1 h2 h3).trans
    ((not_congr h).trans (circleCyclic_swap_iff h1' h2' h3').symm)
  have s2 := rot s1
  exact ⟨r1, rot r1, s1, s2, rot s2⟩

omit [T2Space T] in
/-- Order data for three ends with their own vertices: one triple is enough. -/
theorem padOrder_of_triple {C : Set T} {c : T → ℂ} {g : ℂ → T} (hch : IsChart C c g) {q : Circle
  → T} {φ : T → T} (hq : Function.Injective q) {a₀ a₁ a₂ : Circle} (h01 : a₀ ≠ a₁) (h12 : a₁ ≠ a₂)
    (h02 : a₀ ≠ a₂)
    (hφ : ∀ y ∈ ({q a₀, q a₁, q a₂} : Set T), φ y ∈ discBd C) (n01 : φ (q a₀) ≠ φ (q a₁)) (n12 : φ
      (q a₁) ≠ φ (q a₂)) (n02 : φ (q a₀) ≠ φ (q a₂))
    (hbase : CircleCyclic a₀ a₁ a₂ ↔ CircleCyclic (toCircle (c (φ (q a₀)))) (toCircle (c (φ
      (q a₁)))) (toCircle (c (φ (q a₂))))) : ∃ A U : T → ℝ, PadOrder q g {q a₀, q a₁, q a₂} φ A U
        := by
  have hne : ∀ {x y}, x ∈ ({q a₀, q a₁, q a₂} : Set T) → y ∈ ({q a₀, q a₁, q a₂} : Set T)
    → φ x ≠ φ y → toCircle (c (φ x)) ≠ toCircle (c (φ y)) := fun {x y} hx hy hn he => by
    have hk : ∀ {p}, p ∈ discBd C → ((toCircle (c p) : Circle) : ℂ) = c p := fun {p} hp => by
      have : c p ∈ sphere (0 : ℂ) 1 := by rw [← hch.bd]; exact mem_image_of_mem c hp
      exact coe_toCircle (by simpa using this)
    have h1 : c (φ x) = c (φ y) := by rw [← hk (hφ x hx), ← hk (hφ y hy), he]
    exact hn (by rw [← hch.gh (Surface.discBd_subset _ (hφ x hx)),
      ← hch.gh (Surface.discBd_subset _ (hφ y hy)), h1])
  have m0 : q a₀ ∈ ({q a₀, q a₁, q a₂} : Set T) := by simp
  have m1 : q a₁ ∈ ({q a₀, q a₁, q a₂} : Set T) := by simp
  have m2 : q a₂ ∈ ({q a₀, q a₁, q a₂} : Set T) := by simp
  obtain ⟨p1, p2, p3, p4, p5⟩ := cyclic_perm h01 h12 h02 (hne m0 m1 n01) (hne m1 m2 n12)
    (hne m0 m2 n02) hbase
  refine padOrder_of_injOn hch (toFinite _) ?_ hq hφ ?_ ?_
  · rintro _ (rfl | rfl | rfl) <;> exact mem_range_self _
  · rintro x (rfl | rfl | rfl) y (rfl | rfl | rfl) he
    · rfl
    · exact absurd he n01
    · exact absurd he n02
    · exact absurd he.symm n01
    · rfl
    · exact absurd he n12
    · exact absurd he.symm n02
    · exact absurd he.symm n12
    · rfl
  · intro a b d ha hb hd hab hbd had
    have hm : ∀ {x}, q x ∈ ({q a₀, q a₁, q a₂} : Set T) → x = a₀ ∨ x = a₁ ∨ x = a₂ := fun {x} hx
      => by
      rcases hx with h | h | h
      · exact Or.inl (hq h)
      · exact Or.inr (Or.inl (hq h))
      · exact Or.inr (Or.inr (hq h))
    rcases hm ha with rfl | rfl | rfl <;> rcases hm hb with rfl | rfl | rfl <;>
      rcases hm hd with rfl | rfl | rfl <;>
      first
        | exact absurd rfl hab
        | exact absurd rfl hbd
        | exact absurd rfl had
        | exact hbase
        | exact p1
        | exact p2
        | exact p3
        | exact p4
        | exact p5

omit [T2Space T] in
/-- Order data for two ends with their own vertices. -/
theorem padOrder_of_pair {C : Set T} {c : T → ℂ} {g : ℂ → T} (hch : IsChart C c g) {q : Circle
  → T} {φ : T → T} (hq : Function.Injective q) {a₀ a₁ : Circle} (hφ : ∀ y ∈
    ({q a₀, q a₁} : Set T), φ y ∈ discBd C)
    (n01 : φ (q a₀) ≠ φ (q a₁)) : ∃ A U : T → ℝ, PadOrder q g {q a₀, q a₁} φ A U := by
  refine padOrder_of_injOn hch (toFinite _) ?_ hq hφ ?_ ?_
  · rintro _ (rfl | rfl) <;> exact mem_range_self _
  · rintro x (rfl | rfl) y (rfl | rfl) he
    · rfl
    · exact absurd he n01
    · exact absurd he.symm n01
    · rfl
  · intro a b d ha hb hd hab hbd had
    have hm : ∀ {x}, q x ∈ ({q a₀, q a₁} : Set T) → x = a₀ ∨ x = a₁ := fun {x} hx => by
      rcases hx with h | h
      · exact Or.inl (hq h)
      · exact Or.inr (hq h)
    rcases hm ha with rfl | rfl <;> rcases hm hb with rfl | rfl <;> rcases hm hd with rfl | rfl <;>
      first
        | exact absurd rfl hab
        | exact absurd rfl hbd
        | exact absurd rfl had

/-- **Thickening lines.** Let `Z` be closed sets that pairwise meet only in the finite set `V`.
Those that are lines, with ends `u i` and `w i` in `V` and no other point of `V`, thicken to closed
discs. The ends
stay on the boundary of the disc, and the sets still pairwise meet only in `V`. -/
theorem exists_thin_family (hT : IsClosedSurface T) {κ : Type} [Finite κ] {Z : κ → Set T}
  (hZ : ∀ i, IsClosed (Z i)) {V : Set T} (hV : IsClosed V) (hZZ : ∀ i j, i ≠ j
    → Z i ∩ Z j ⊆ V) {L : Set κ} {u w : κ → T}
    (hL : ∀ i ∈ L, IsLineWithEnds (Z i) (u i) (w i)) (hLV : ∀ i ∈ L, Z i ∩ V = {u i, w i}) :
    ∃ Z' : κ → Set T, (∀ i, IsClosed (Z' i)) ∧ (∀ i j, i ≠ j → Z' i ∩ Z' j ⊆ V) ∧ (∀ i, i ∉ L
      → Z' i = Z i) ∧ ∀ i ∈ L, IsClosedDisc (Z' i) ∧ Z' i ∩ V = {u i, w i} ∧
        ({u i, w i} : Set T) ⊆ discBd (Z' i) ∧ Z i ⊆ Z' i := by
  classical
  have := Fintype.ofFinite κ
  suffices H : ∀ 𝓐 : Finset κ, (∀ i ∈ 𝓐, i ∈ L) → ∃ Z' : κ → Set T, (∀ i, IsClosed (Z' i)) ∧
    (∀ i j, i ≠ j → Z' i ∩ Z' j ⊆ V) ∧ (∀ i, i ∉ 𝓐 → Z' i = Z i) ∧
      ∀ i ∈ 𝓐, IsClosedDisc (Z' i) ∧ Z' i ∩ V = {u i, w i} ∧ ({u i, w i} : Set T) ⊆ discBd (Z' i)
        ∧ Z i ⊆ Z' i by
    obtain ⟨Z', h1, h2, h3, h4⟩ := H (Finset.univ.filter (· ∈ L)) (fun i hi =>
      (Finset.mem_filter.mp hi).2)
    exact ⟨Z', h1, h2, fun i hi => h3 i fun h => hi (Finset.mem_filter.mp h).2,
      fun i hi => h4 i (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩)⟩
  intro 𝓐
  induction 𝓐 using Finset.induction_on with
  | empty => exact fun _ => ⟨Z, hZ, hZZ, fun _ _ => rfl, fun i hi => absurd hi
    (Finset.notMem_empty i)⟩
  | insert i₀ 𝓐 hi₀ ih =>
    intro hsub
    obtain ⟨Z', h1, h2, h3, h4⟩ := ih fun i hi => hsub i (Finset.mem_insert_of_mem hi)
    have hi₀L := hsub i₀ (Finset.mem_insert_self _ _)
    have hZ₀ : Z' i₀ = Z i₀ := h3 i₀ hi₀
    obtain ⟨a, ha, hr, ha0, ha1⟩ := (hL i₀ hi₀L).exists_arc
    let B : Set T := V ∪ ⋃ j : {j // j ≠ i₀}, Z' j.1
    have hB : IsClosed B := hV.union (isClosed_iUnion_of_finite fun j => h1 j.1)
    have hends : ({u i₀, w i₀} : Set T) ⊆ V := by
      rw [← hLV i₀ hi₀L]
      exact inter_subset_right
    have hmeet : range a ∩ B ⊆ {a 0, a 1} := by
      rintro x ⟨hxa, hxB⟩
      rw [ha0, ha1, ← hLV i₀ hi₀L]
      rw [hr] at hxa
      refine ⟨hxa, ?_⟩
      rcases hxB with h | h
      · exact h
      · obtain ⟨j, hj⟩ := mem_iUnion.mp h
        have := h2 i₀ j.1 j.2.symm
        rw [hZ₀] at this
        exact this ⟨hxa, hj⟩
    obtain ⟨D, hD, hDB, hbd, hrange⟩ :=
      GM12.exists_thin_disc_of_arc hT ha hB (by rw [ha0]; exact Or.inl (hends (by simp)))
        (by rw [ha1]; exact Or.inl (hends (by simp))) hmeet
    rw [ha0, ha1] at hDB hbd
    rw [hr] at hrange
    refine ⟨Function.update Z' i₀ D, fun i => ?_, fun i j hij => ?_, fun i hi => ?_, fun i hi => ?_⟩
    · by_cases h : i = i₀
      · subst h
        simpa using hD.isClosed
      · simpa [Function.update_of_ne h] using h1 i
    · have key : ∀ j, j ≠ i₀ → D ∩ Z' j ⊆ V := fun j hj x hx => by
        have : x ∈ D ∩ B := ⟨hx.1, Or.inr (mem_iUnion.mpr ⟨⟨j, hj⟩, hx.2⟩)⟩
        rw [hDB] at this
        exact hends this
      by_cases hi : i = i₀
      · subst hi
        rw [Function.update_self, Function.update_of_ne hij.symm]
        exact key j hij.symm
      · by_cases hj : j = i₀
        · subst hj
          rw [Function.update_self, Function.update_of_ne hi, inter_comm]
          exact key i hi
        · rw [Function.update_of_ne hi, Function.update_of_ne hj]
          exact h2 i j hij
    · have hne : i ≠ i₀ := fun h => hi (h ▸ Finset.mem_insert_self _ _)
      rw [Function.update_of_ne hne]
      exact h3 i fun h => hi (Finset.mem_insert_of_mem h)
    · by_cases h : i = i₀
      · subst h
        rw [Function.update_self]
        refine ⟨hD, ?_, hbd, hrange⟩
        apply Subset.antisymm
        · rintro x ⟨hx, hxV⟩
          have : x ∈ D ∩ B := ⟨hx, Or.inl hxV⟩
          rwa [hDB] at this
        · exact fun x hx => ⟨Surface.discBd_subset _ (hbd hx), hends hx⟩
      · rw [Function.update_of_ne h]
        exact h4 i ((Finset.mem_insert.mp hi).resolve_left h)

end GraphMinor.GM19
