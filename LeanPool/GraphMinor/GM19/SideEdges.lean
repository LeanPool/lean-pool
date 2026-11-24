/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.CuffAngle
public import LeanPool.GraphMinor.GM19.FreeFrame

/-!
# The edges along a long side

We read the cuff of a long side `S` through angles, with `S` at the angles from `0` to `π`. The
edges of `Γ` along `S` then come in order
`e₁, …, e_k`, and `e₀, e_{k+1}` are the short sides next to `S` (`exists_sideEdges`).
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM11 Real

universe w

variable {S : Type} [TopologicalSpace S] [T2Space S] {β : Type w}

/-- A finite set of reals in `[x, y]` that holds `x` and `y`, in order. -/
theorem exists_sorted {T : Set ℝ} (hT : T.Finite) {x y : ℝ} (hxy : x < y) (hx : x ∈ T) (hy : y ∈ T)
  (hs : T ⊆ Icc x y) :
    ∃ (k : ℕ) (t : ℕ → ℝ), 1 ≤ k ∧ t 0 = x ∧ t k = y ∧ (∀ i < k, t i < t (i + 1))
      ∧ ∀ z, z ∈ T ↔ ∃ i ≤ k, z = t i := by
  classical
  set F := hT.toFinset with hF
  have hmem : ∀ z, z ∈ F ↔ z ∈ T := fun z ↦ hT.mem_toFinset
  have hcard : 2 ≤ F.card := by
    have : ({x, y} : Finset ℝ) ⊆ F := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact (hmem _).2 hx
      · exact (hmem _).2 hy
    have h₂ := Finset.card_le_card this
    rwa [Finset.card_pair hxy.ne] at h₂
  obtain ⟨k, hk⟩ : ∃ k, F.card = k + 1 := ⟨F.card - 1, by omega⟩
  let o := F.orderEmbOfFin hk
  let t : ℕ → ℝ := fun i ↦ o ⟨min i k, by omega⟩
  have hto : ∀ i : Fin (k + 1), t i.1 = o i := fun i ↦ by
    simp only [t]
    congr 1
    exact Fin.ext (Nat.min_eq_left (by omega))
  have hmemt : ∀ i ≤ k, t i ∈ T := fun i hi ↦ by
    rw [hto ⟨i, by omega⟩]
    exact (hmem _).1 (Finset.orderEmbOfFin_mem F hk _)
  have hlast : t k = y := by
    apply le_antisymm (hs (hmemt k le_rfl)).2
    have hr : y ∈ range o := by
      rw [Finset.range_orderEmbOfFin]
      exact (hmem y).2 hy
    obtain ⟨j, rfl⟩ := hr
    rw [hto ⟨k, by omega⟩]
    exact o.monotone (by simp only [Fin.le_def]; omega)
  have h0 : t 0 = x := by
    apply le_antisymm _ (hs (hmemt 0 (by omega))).1
    have hr : x ∈ range o := by
      rw [Finset.range_orderEmbOfFin]
      exact (hmem x).2 hx
    obtain ⟨j, rfl⟩ := hr
    rw [hto ⟨0, by omega⟩]
    exact o.monotone (by simp only [Fin.le_def]; omega)
  refine ⟨k, t, by omega, h0, hlast, fun i hi ↦ ?_, fun z ↦ ?_⟩
  · refine o.strictMono ?_
    simp only [Fin.lt_def]
    omega
  · constructor
    · intro hz
      have hr : z ∈ range o := by
        rw [Finset.range_orderEmbOfFin]
        exact (hmem z).2 hz
      obtain ⟨i, rfl⟩ := hr
      refine ⟨i.1, by omega, ?_⟩
      simp only [t]
      congr 1
      ext
      simp only
      omega
    · rintro ⟨i, hi, rfl⟩
      exact (hmem _).1 (Finset.orderEmbOfFin_mem F hk _)

/-- A sorted sequence is increasing. -/
theorem sorted_lt {t : ℕ → ℝ} {k : ℕ} (h : ∀ i < k, t i < t (i + 1)) {i j : ℕ} (hij : i < j)
  (hj : j ≤ k) : t i < t j := by
  induction j with
  | zero => omega
  | succ j ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h' | rfl
    · exact (ih h' (by omega)).trans (h j (by omega))
    · exact h i (by omega)

theorem sorted_le {t : ℕ → ℝ} {k : ℕ} (h : ∀ i < k, t i < t (i + 1)) {i j : ℕ} (hij : i ≤ j)
  (hj : j ≤ k) : t i ≤ t j := by
  rcases Nat.lt_or_eq_of_le hij with h' | rfl
  · exact (sorted_lt h h' hj).le
  · exact le_rfl

/-- A point of `[t 0, t k]` is some `t i` or lies between two neighbours. -/
theorem sorted_cases {t : ℕ → ℝ} {k : ℕ} {y : ℝ} (hy₀ : t 0 ≤ y) (hy₁ : y ≤ t k) : (∃ i ≤ k, y
  = t i) ∨ ∃ i < k, y ∈ Ioo (t i) (t (i + 1)) := by
  induction k with
  | zero => exact Or.inl ⟨0, le_rfl, le_antisymm hy₁ hy₀⟩
  | succ k ih =>
    by_cases h : y ≤ t k
    · rcases ih h with ⟨i, hi, he⟩ | ⟨i, hi, hm⟩
      · exact Or.inl ⟨i, by omega, he⟩
      · exact Or.inr ⟨i, by omega, hm⟩
    · by_cases h' : y = t (k + 1)
      · exact Or.inl ⟨k + 1, le_rfl, h'⟩
      · exact Or.inr ⟨k, by omega, not_le.1 h, lt_of_le_of_ne hy₁ h'⟩

/-- **An arc of a cuff between two marked points with no marked point between is an arc component.**
-/
theorem ioo_mem_arcComponents {c W N : Set S} (f : Circle ≃ₜ c) {x₁ x₂ : ℝ} (h₁₂ : x₁ < x₂)
  (h₁ : cuffPoint f x₁ ∈ N) (h₂ : cuffPoint f x₂ ∈ N)
    (hmid : ∀ y ∈ Ioo x₁ x₂, cuffPoint f y ∈ W \ N) (hlocal : ∀ D, D ⊆ W \ N → IsPathConnected D →
      (D ∩ c).Nonempty → D ⊆ c) :
    cuffPoint f '' Ioo x₁ x₂ ∈ arcComponentsIn (W \ N) := by
  have hg := continuous_cuffAngle f
  have hne : (Ioo x₁ x₂).Nonempty := nonempty_Ioo.2 h₁₂
  have hpc : IsPathConnected (cuffPoint f '' Ioo x₁ x₂) := ((convex_Ioo x₁ x₂).isPathConnected
    hne).image hg
  refine ⟨hne.image _, ?_, hpc, fun Y hY hYp hsub ↦ ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact hmid y hy
  · apply Subset.antisymm _ hsub
    have hm : (x₁ + x₂) / 2 ∈ Ioo x₁ x₂ := ⟨by linarith, by linarith⟩
    have hmY : cuffPoint f ((x₁ + x₂) / 2) ∈ Y := hsub (mem_image_of_mem _ hm)
    have hYc : Y ⊆ c := hlocal Y hY hYp ⟨_, hmY, cuffAngle_mem f _⟩
    intro z hz
    obtain ⟨y, hy, rfl⟩ := exists_cuffAngle_eq f x₁ (hYc hz)
    have hNo : ∀ {u}, cuffPoint f u ∈ N → cuffPoint f u ∉ Y := fun hu hY' ↦ (hY hY').2 hu
    have hy₁ : x₁ < y := lt_of_le_of_ne hy.1 (by rintro rfl; exact hNo h₁ hz)
    by_cases hy₂ : y < x₂
    · exact mem_image_of_mem _ ⟨hy₁, hy₂⟩
    · exfalso
      have hy₃ : x₂ ≤ y := not_lt.1 hy₂
      rcases arc_of_preconnected f hYp.isConnected.isPreconnected hYc (x₁ := (x₁ + x₂) / 2) (x₂
        := y) (by linarith) (by linarith [hy.2]) hmY hz with h' | h'
      · exact hNo h₂ (h' x₂ ⟨hm.2.le, hy₃⟩)
      · have := h' (x₁ + 2 * π) ⟨hy.2.le, by linarith⟩
        rw [cuffAngle_add_two_pi] at this
        exact hNo h₁ this

/-- The edges along a long side, with the short sides next to it. -/
structure IsSideEdges (χ : ColourScheme S β) (Γ : Painting S) (side Θ : Set S) (f : Circle ≃ₜ Θ)
  (a b : S) (k : ℕ) (t : ℕ → ℝ) (e : ℕ → Set S) : Prop where
  head : (χ.Φ.γ side).head? = some a
  last : (χ.Φ.γ side).getLast? = some b
  ga : cuffPoint f 0 = a
  gb : cuffPoint f π = b
  side_eq : side = cuffPoint f '' Ioo 0 π
  k_pos : 1 ≤ k
  t0 : t 0 = 0
  tk : t k = π
  mono : ∀ i < k, t i < t (i + 1)
  e_eq : ∀ i < k, e (i + 1) = cuffPoint f '' Ioo (t i) (t (i + 1))
  mem : ∀ i ≤ k + 1, e i ∈ Γ.E
  all : ∀ c ∈ Γ.E, c ⊆ side → ∃ i, 1 ≤ i ∧ i ≤ k ∧ c = e i
  e_zero : ∃ d, π ≤ d ∧ d < 2 * π ∧ e 0 = cuffPoint f '' Ioo d (2 * π)
  e_last : ∃ c', π < c' ∧ c' ≤ 2 * π ∧ e (k + 1) = cuffPoint f '' Ioo π c'
  short : ∀ s ∈ χ.Φ.shortSides, (closure s ∩ closure side).Nonempty → s = e 0 ∨ s = e (k + 1)
  rest : ∀ s ∈ χ.Φ.shortSides, s ⊆ Θ → s ⊆ cuffPoint f '' Ioo π (2 * π)
  short_zero : e 0 ∈ χ.Φ.shortSides

private theorem frame_side_endpoints_follow_orientation
    {S : Type}
    [TopologicalSpace S]
    {β : Type w}
    (χ : ColourScheme S β)
    {side : Set S}
    (Θ : Set S)
    (u : S)
    (v : S)
    (huv : u ≠ v)
    (hset : closure side ∩ (χ.Φ.V ∩ Θ) = {u, v})
    (hline : IsLineWithEnds (closure side) u v)
    (hn2 : (tilde side).ncard = 2)
    (hnd : (χ.Φ.γ side).Nodup)
    (hgs : {v | v ∈ χ.Φ.γ side} = tilde side)
    (hu : u ∈ tilde side)
    (hv : v ∈ tilde side)
    (hts : tilde side = {u, v}) :
    ∃ a b, χ.Φ.γ side = [a, b] ∧ IsLineWithEnds (closure side) a b := by
  classical
  have hlen : (χ.Φ.γ side).length = 2 := by
    have h₁ : (χ.Φ.γ side).toFinset.card = 2 := by
      have hco : {v | v ∈ χ.Φ.γ side} = ((χ.Φ.γ side).toFinset : Set S) := by
        ext z
        simp
      rw [← hn2, ← hgs, hco, ncard_coe_finset]
    rw [← h₁]
    exact (List.toFinset_card_of_nodup hnd).symm
  obtain ⟨a, b, hl⟩ := List.length_eq_two.1 hlen
  refine ⟨a, b, hl, ?_⟩
  have hgs' : ({a, b} : Set S) = {u, v} := by
    rw [← hts, ← hgs, hl]
    ext z
    simp
  rcases Set.pair_eq_pair_iff.1 hgs' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hline
  · exact hline.symm

private theorem oriented_endpoints_are_tilde
    {S : Type}
    [TopologicalSpace S]
    {β : Type w}
    (χ : ColourScheme S β)
    {side : Set S}
    (hgs : {v | v ∈ χ.Φ.γ side} = tilde side)
    (a : S)
    (b : S)
    (hγ : χ.Φ.γ side = [a, b]) :
    tilde side = {a, b} := by
  rw [← hgs, hγ]
  ext z
  simp

private theorem side_equals_first_open_semicircle
    {S : Type}
    [TopologicalSpace S]
    {side : Set S}
    (a : S)
    (b : S)
    (htab : tilde side = {a, b})
    (g : ℝ → S)
    (ha : g 0 = a)
    (hb : g π = b)
    (himg : g '' Icc 0 π = closure side)
    (hpos : 0 < π)
    (hinj : ∀ {x y : ℝ}, x ∈ Ico 0 (2 * π) → y ∈ Ico 0 (2 * π) → g x = g y → x = y) :
    side = g '' Ioo 0 π := by
  ext z
  constructor
  · intro hz
    have hzc : z ∈ g '' Icc 0 π := himg ▸ subset_closure hz
    obtain ⟨y, hy, rfl⟩ := hzc
    have hna : ∀ {w}, w ∈ tilde side → g y ≠ w := fun hw he ↦ hw.2 (he ▸ hz)
    have hy₀ : y ≠ 0 := by
      rintro rfl
      exact hna (show a ∈ tilde side by rw [htab]; exact mem_insert _ _) ha
    have hy₁ : y ≠ π := by
      rintro rfl
      exact hna (show b ∈ tilde side by rw [htab]; exact mem_insert_of_mem _ rfl) hb
    exact ⟨y, ⟨lt_of_le_of_ne hy.1 hy₀.symm, lt_of_le_of_ne hy.2 hy₁⟩, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    have hyc : g y ∈ closure side := himg ▸ mem_image_of_mem g ⟨hy.1.le, hy.2.le⟩
    by_contra hn
    have : g y ∈ tilde side := ⟨hyc, hn⟩
    rw [htab] at this
    have hyo : y ∈ Ico 0 (2 * π) := ⟨hy.1.le, by linarith [hy.2]⟩
    rcases this with h' | h'
    · have := hinj hyo ⟨le_rfl, by linarith⟩ (h'.trans ha.symm)
      linarith [hy.1]
    · have := hinj hyo ⟨hpos.le, by linarith⟩ ((mem_singleton_iff.1 h').trans hb.symm)
      linarith [hy.2]

private theorem connected_boundary_set_stays_on_cuff
    {S : Type}
    [TopologicalSpace S]
    (Θ : Set S)
    (hΘ : Θ ∈ cuffs S) :
    ∀ {Y : Set S}, Y ⊆ bd S → IsPreconnected Y → (Y ∩ Θ).Nonempty → Y ⊆ Θ := by
  rintro Y hY hYc ⟨z, hzY, hzΘ⟩
  obtain ⟨x₀, hx₀, he⟩ := hΘ
  have hzΘ' : z ∈ connectedComponentIn (bd S) x₀ := by rwa [he]
  have h₁ := connectedComponentIn_eq hzΘ'
  rw [he] at h₁
  have h₂ := hYc.subset_connectedComponentIn hzY hY
  rwa [← h₁] at h₂

private theorem drawing_interior_component_stays_on_cuff
    {S : Type}
    [TopologicalSpace S]
    {Γ : Painting S}
    (Θ : Set S)
    (hΘb : Θ ⊆ bd S)
    (hconnΘ : ∀ {Y : Set S}, Y ⊆ bd S → IsPreconnected Y → (Y ∩ Θ).Nonempty → Y ⊆ Θ) :
    ∀ Y ⊆ Γ.U \ Γ.V, IsPathConnected Y → (Y ∩ Θ).Nonempty → Y ⊆ Θ := by
  rintro Y hY hYp ⟨z, hzY, hzΘ⟩
  obtain ⟨c, hc, hYc⟩ := exists_arcComp_superset hYp hY
  have hbdr := (Γ.border_edge c hc ⟨z, hYc hzY, hΘb hzΘ⟩).2
  exact hYc.trans (hconnΘ hbdr hc.2.2.1.isConnected.isPreconnected ⟨z, hYc hzY, hzΘ⟩)

private theorem finite_angles_of_drawing_vertices
    {S : Type}
    [TopologicalSpace S]
    {Γ : Painting S}
    (g : ℝ → S)
    (hpos : 0 < π)
    (hinj : ∀ {x y : ℝ}, x ∈ Ico 0 (2 * π) → y ∈ Ico 0 (2 * π) → g x = g y → x = y) :
    ({y | y ∈ Icc 0 π ∧ g y ∈ Γ.V}).Finite := by
  let T := {y | y ∈ Icc 0 π ∧ g y ∈ Γ.V}
  refine Set.Finite.of_finite_image (f := g) (Γ.finite_V.subset ?_) ?_
  · rintro _ ⟨y, hy, rfl⟩
    exact hy.2
  · intro x hx y hy he
    exact hinj ⟨hx.1.1, by linarith [hx.1.2]⟩ ⟨hy.1.1, by linarith [hy.1.2]⟩ he

private theorem finite_angles_of_frame_vertices
    {S : Type}
    [TopologicalSpace S]
    {β : Type w}
    (χ : ColourScheme S β)
    (g : ℝ → S)
    (hpos : 0 < π)
    (hinj : ∀ {x y : ℝ}, x ∈ Ico 0 (2 * π) → y ∈ Ico 0 (2 * π) → g x = g y → x = y) :
    ({y | y ∈ Icc π (2 * π) ∧ g y ∈ χ.Φ.V}).Finite := by
  let T' := {y | y ∈ Icc π (2 * π) ∧ g y ∈ χ.Φ.V}
  have hTo : (T' \ {2 * π}).Finite := by
    refine Set.Finite.of_finite_image (f := g) (χ.Φ.finite_V.subset ?_) ?_
    · rintro _ ⟨y, hy, rfl⟩
      exact hy.1.2
    · intro x hx y hy he
      have hx' : x ∈ Ico 0 (2 * π) := ⟨by linarith [hx.1.1.1], lt_of_le_of_ne hx.1.1.2 hx.2⟩
      have hy' : y ∈ Ico 0 (2 * π) := ⟨by linarith [hy.1.1.1], lt_of_le_of_ne hy.1.1.2 hy.2⟩
      exact hinj hx' hy' he
  exact (hTo.union (finite_singleton _)).subset fun z hz ↦ by
    by_cases h' : z = 2 * π
    · exact Or.inr h'
    · exact Or.inl ⟨hz, h'⟩

private theorem extreme_intervals_are_short_sides
    {S : Type}
    [TopologicalSpace S]
    {β : Type w}
    (χ : ColourScheme S β)
    {side : Set S}
    (hside : side ∈ χ.Φ.longSides)
    (a : S)
    (b : S)
    (htab : tilde side = {a, b})
    (g : ℝ → S)
    (hb : g π = b)
    (hgc : Continuous g)
    (hside_eq : side = g '' Ioo 0 π)
    (haV : a ∈ χ.Φ.V)
    (hbV : b ∈ χ.Φ.V)
    (hg2 : g (2 * π) = a)
    (q : ℕ)
    (w : ℕ → ℝ)
    (hw0 : w 0 = π)
    (hwq : w q = 2 * π)
    (hwm : ∀ i < q, w i < w (i + 1))
    (hwr : ∀ {i : ℕ}, i ≤ q → w i ∈ Icc π (2 * π))
    (hsidesR : ∀ {i : ℕ}, i < q → g '' Ioo (w i) (w (i + 1)) ∈ χ.Φ.sides)
    (hdisjR : ∀ {x y : ℝ}, x ∈ Ioo 0 π → y ∈ Ioo π (2 * π) → g x ≠ g y) :
    ∀ {i : ℕ}, i < q → i = 0 ∨ i + 1 = q → g '' Ioo (w i) (w (i + 1)) ∈ χ.Φ.shortSides := by
  intro i hi he
  refine ⟨hsidesR hi, fun hlong ↦ ?_⟩
  have hRne : g '' Ioo (w i) (w (i + 1)) ≠ side := by
    intro heq
    obtain ⟨y, hy⟩ := nonempty_Ioo.2 (hwm i hi)
    have hyR : y ∈ Ioo π (2 * π) := ⟨lt_of_le_of_lt (hwr (i := i) (by omega)).1 hy.1,
      lt_of_lt_of_le hy.2 (hwr (i := i + 1) (by omega)).2⟩
    have : g y ∈ side := heq ▸ mem_image_of_mem g hy
    rw [hside_eq] at this
    obtain ⟨x, hx, hxy⟩ := this
    exact hdisjR hx hyR hxy
  have hdis := χ.Φ.long_disjoint _ (hsidesR hi) _ hside.1 hRne hlong hside.2
  have hclI : ∀ {x y}, x < y → closure (g '' Ioo x y) ⊇ g '' Icc x y := fun {x y} hxy ↦ by
    rw [← closure_Ioo hxy.ne]
    exact image_closure_subset_closure_image hgc
  have hnotin : ∀ {z}, z ∈ χ.Φ.V → z ∉ g '' Ioo (w i) (w (i + 1)) := fun hz hzm ↦ by
    have hsi := hsidesR hi
    exact (hsi.2.1 hzm).2 hz
  rcases he with rfl | he
  · have hbt : b ∈ tilde (g '' Ioo (w 0) (w (0 + 1))) := by
      refine ⟨hclI (hwm 0 hi) ⟨w 0, ⟨le_rfl, (hwm 0 hi).le⟩, ?_⟩, hnotin hbV⟩
      rw [hw0]
      exact hb
    exact disjoint_left.1 hdis hbt (by rw [htab]; exact mem_insert_of_mem _ rfl)
  · have hat : a ∈ tilde (g '' Ioo (w i) (w (i + 1))) := by
      refine ⟨hclI (hwm i hi) ⟨w (i + 1), ⟨(hwm i hi).le, le_rfl⟩, ?_⟩, hnotin haV⟩
      rw [he, hwq]
      exact hg2
    exact disjoint_left.1 hdis hat (by rw [htab]; exact mem_insert _ _)

private theorem short_sides_on_cuff_are_intervals
    {S : Type}
    [TopologicalSpace S]
    {β : Type w}
    (χ : ColourScheme S β)
    {side : Set S}
    (hside : side ∈ χ.Φ.longSides)
    (Θ : Set S)
    (a : S)
    (b : S)
    (f : Circle ≃ₜ ↑Θ)
    (g : ℝ → S) (hg : g = cuffPoint f)
    (ha : g 0 = a)
    (hb : g π = b)
    (hside_eq : side = g '' Ioo 0 π)
    (haV : a ∈ χ.Φ.V)
    (hbV : b ∈ χ.Φ.V)
    (q : ℕ)
    (w : ℕ → ℝ)
    (hw0 : w 0 = π)
    (hwq : w q = 2 * π)
    (hmemT' : ∀ (z : ℝ), z ∈ ({y | y ∈ Icc π (2 * π) ∧ g y ∈ χ.Φ.V}) ↔ ∃ i ≤ q, z = w i)
    (hsidesR : ∀ {i : ℕ}, i < q → g '' Ioo (w i) (w (i + 1)) ∈ χ.Φ.sides) :
    ∀ s ∈ χ.Φ.shortSides, s ⊆ Θ → s ⊆ g '' Ioo π (2 * π) ∧ ∃ i < q, s = g '' Ioo (w i) (w (i + 1))
      := by
  subst g
  let g : ℝ → S := cuffPoint f
  let T' := {y | y ∈ Icc π (2 * π) ∧ g y ∈ χ.Φ.V}
  intro s hs hsub
  have hsne : s ≠ side := fun h ↦ hs.2 (h ▸ hside.2)
  have hsv : ∀ {z}, z ∈ s → z ∉ χ.Φ.V := fun hz ↦ (hs.1.2.1 hz).2
  have hang : ∀ {z}, z ∈ s → ∃ y ∈ Ioo π (2 * π), g y = z := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := exists_cuffAngle_eq f 0 (hsub hz)
    rw [zero_add] at hy
    have hy₀ : y ≠ 0 := by
      rintro rfl
      exact hsv hz (ha.symm ▸ haV)
    have hyπ : y ≠ π := by
      rintro rfl
      exact hsv hz (hb.symm ▸ hbV)
    by_cases hle : y < π
    · exfalso
      have hyside : g y ∈ side := hside_eq ▸ mem_image_of_mem g ⟨lt_of_le_of_ne hy.1 hy₀.symm, hle⟩
      exact hsne (GM11.arcComponent_eq hs.1 hside.1 hz hyside)
    · exact ⟨y, ⟨lt_of_le_of_ne (not_lt.1 hle) hyπ.symm, hy.2⟩, rfl⟩
  refine ⟨fun z hz ↦ by
    obtain ⟨y, hy, rfl⟩ := hang hz
    exact mem_image_of_mem g hy, ?_⟩
  obtain ⟨z, hz⟩ := hs.1.1
  obtain ⟨y, hy, rfl⟩ := hang hz
  rcases sorted_cases (t := w) (k := q) (y := y) (hw0.trans_le hy.1.le)
    (by rw [hwq]; exact hy.2.le) with ⟨i, hi, rfl⟩ | ⟨i, hi, hm⟩
  · exact absurd ((hmemT' _).2 ⟨i, hi, rfl⟩ : w i ∈ T').2 (hsv hz)
  · exact ⟨i, hi, GM11.arcComponent_eq hs.1 (hsidesR hi) hz (mem_image_of_mem g hm)⟩

private theorem successive_drawing_vertex_angles_bound_edge
    {S : Type}
    [TopologicalSpace S]
    [T2Space S]
    {Γ : Painting S}
    (Θ : Set S)
    (f : Circle ≃ₜ ↑Θ)
    (g : ℝ → S) (hg : g = cuffPoint f)
    (hΘb : Θ ⊆ bd S)
    (hlocalU : ∀ Y ⊆ Γ.U \ Γ.V, IsPathConnected Y → (Y ∩ Θ).Nonempty → Y ⊆ Θ)
    (k : ℕ)
    (t : ℕ → ℝ)
    (hmono : ∀ i < k, t i < t (i + 1))
    (hmemT : ∀ (z : ℝ), z ∈ ({y | y ∈ Icc 0 π ∧ g y ∈ Γ.V}) ↔ ∃ i ≤ k, z = t i)
    (hrange : ∀ {i : ℕ}, i ≤ k → t i ∈ Icc 0 π)
    (hgapT : ∀ {i : ℕ}, i < k → ∀ y ∈ Ioo (t i) (t (i + 1)), y ∉ ({y | y ∈ Icc 0 π ∧ g y ∈ Γ.V}))
    (e : ℕ → Set S)
    (hei : ∀ i < k, e (i + 1) = g '' Ioo (t i) (t (i + 1)))
    (i : ℕ)
    (hi : i < k) :
    e (i + 1) ∈ Γ.E := by
  subst g
  let g : ℝ → S := cuffPoint f
  let T := {y | y ∈ Icc 0 π ∧ g y ∈ Γ.V}
  rw [hei i hi]
  have h₁ : g (t i) ∈ Γ.V := ((hmemT _).2 ⟨i, by omega, rfl⟩ : t i ∈ T).2
  have h₂ : g (t (i + 1)) ∈ Γ.V := ((hmemT _).2 ⟨i + 1, by omega, rfl⟩ : t (i + 1) ∈ T).2
  refine ioo_mem_arcComponents f (hmono i hi) h₁ h₂ (fun y hy ↦ ?_) hlocalU
  have hyr : y ∈ Icc 0 π := ⟨(hrange (i := i) (by omega)).1.trans hy.1.le, hy.2.le.trans (hrange (i
    := i + 1) (by omega)).2⟩
  exact ⟨Γ.bd_subset (hΘb (cuffAngle_mem f y)), fun hV ↦ hgapT hi y hy ⟨hyr, hV⟩⟩

private theorem short_side_touching_long_side_is_extreme
    {S : Type}
    [TopologicalSpace S]
    [T2Space S]
    {β : Type w}
    (hS : IsSurface S)
    (χ : ColourScheme S β)
    {side : Set S}
    (Θ : Set S)
    (hΘ : Θ ∈ cuffs S)
    (hLΘ : closure side ⊆ Θ)
    (g : ℝ → S)
    (himg : g '' Icc 0 π = closure side)
    (hpos : 0 < π)
    (hgc : Continuous g)
    (hinj : ∀ {x y : ℝ}, x ∈ Ico 0 (2 * π) → y ∈ Ico 0 (2 * π) → g x = g y → x = y)
    (k : ℕ)
    (q : ℕ)
    (w : ℕ → ℝ)
    (hw0 : w 0 = π)
    (hwq : w q = 2 * π)
    (hwm : ∀ i < q, w i < w (i + 1))
    (hwr : ∀ {i : ℕ}, i ≤ q → w i ∈ Icc π (2 * π))
    (hshorts : ∀ s ∈ χ.Φ.shortSides, s ⊆ Θ → s ⊆ g '' Ioo π (2 * π) ∧ ∃ i < q, s = g '' Ioo (w i)
      (w (i + 1)))
    (e : ℕ → Set S)
    (he0 : e 0 = g '' Ioo (w (q - 1)) (w (q - 1 + 1)))
    (hek : e (k + 1) = g '' Ioo (w 0) (w (0 + 1)))
    (s : Set S)
    (hs : s ∈ χ.Φ.shortSides)
    (hne : (closure s ∩ closure side).Nonempty) :
    s = e 0 ∨ s = e (k + 1) := by
  obtain ⟨x, hx₁, hx₂⟩ := hne
  obtain ⟨Θ', hΘ', hsΘ', -⟩ := Frame.side_on_cuff hS χ.Φ hs.1
  have hxΘ' : x ∈ Θ' := closure_minimal hsΘ' (isClosed_cuff hS ⟨Θ', hΘ'⟩) hx₁
  have hsame : Θ' = Θ := cuffs_eq_of_mem hΘ' hΘ hxΘ' (hLΘ hx₂)
  subst hsame
  obtain ⟨-, i, hi, rfl⟩ := hshorts s hs hsΘ'
  have hcl : closure (g '' Ioo (w i) (w (i + 1))) ⊆ g '' Icc (w i) (w (i + 1)) :=
    closure_minimal (image_mono Ioo_subset_Icc_self) (isCompact_Icc.image hgc).isClosed
  obtain ⟨y', hy', rfl⟩ := hcl hx₁
  rw [← himg] at hx₂
  obtain ⟨y'', hy'', he⟩ := hx₂
  have hy'r : y' ∈ Icc π (2 * π) := ⟨(hwr (i := i) (by omega)).1.trans hy'.1, hy'.2.trans (hwr (i
    := i + 1) (by omega)).2⟩
  by_cases hy2 : y' = 2 * π
  · left
    have hiq : i + 1 = q := by
      by_contra hne
      have := sorted_lt hwm (show i + 1 < q by omega) le_rfl
      rw [hwq] at this
      linarith [hy'.2]
    have : i = q - 1 := by omega
    rw [he0, this]
  · right
    have heq := hinj ⟨by linarith [hy''.1, hpos], by linarith [hy''.2]⟩ ⟨by linarith [hy'r.1],
      lt_of_le_of_ne hy'r.2 hy2⟩ he
    have hy'π : y' = π := le_antisymm (by rw [← heq]; exact hy''.2) hy'r.1
    have hi0 : i = 0 := by
      by_contra hne
      have := sorted_lt hwm (show 0 < i by omega) (by omega)
      rw [hw0] at this
      linarith [hy'.1]
    rw [hek, hi0]

section

variable (hS : IsSurface S)
include hS

/-- **The edges along a long side.** -/
theorem exists_sideEdges (χ : ColourScheme S β) {Γ : Painting S} (hfit : Γ.Fits χ.Φ) {side : Set S}
  (hside : side ∈ χ.Φ.longSides) :
    ∃ (Θ : Set S) (_ : Θ ∈ cuffs S) (f : Circle ≃ₜ Θ) (a b : S) (k : ℕ) (t : ℕ → ℝ) (e : ℕ
      → Set S), side ⊆ Θ ∧ IsSideEdges χ Γ side Θ f a b k t e := by
  classical
  obtain ⟨Θ, hΘ, hsΘ, u, v, huv, hset, hline⟩ := Frame.side_on_cuff hS χ.Φ hside.1
  have hO : IsOArc Θ := ⟨cuffPar hS ⟨Θ, hΘ⟩⟩
  have hclΘ : IsClosed Θ := isClosed_cuff hS ⟨Θ, hΘ⟩
  have hLΘ : closure side ⊆ Θ := closure_minimal hsΘ hclΘ
  obtain ⟨hn2, -, -, hends⟩ := χ.Φ.side_shape side hside.1
  obtain ⟨x, y, hxy, hxyset⟩ := Set.ncard_eq_two.1 hn2
  have hnd := χ.Φ.γ_nodup side hside.1
  have hgs := χ.Φ.γ_set side hside.1
  have hu : u ∈ tilde side := by
    rw [← hends]
    exact ⟨v, hline⟩
  have hv : v ∈ tilde side := by
    rw [← hends]
    exact ⟨u, hline.symm⟩
  have hts : tilde side = {u, v} := by
    rw [hxyset] at hu hv ⊢
    rcases hu with rfl | hu <;> rcases hv with rfl | hv
    · exact absurd rfl huv
    · rw [mem_singleton_iff.1 hv]
    · rw [mem_singleton_iff.1 hu, pair_comm]
    · exact absurd ((mem_singleton_iff.1 hu).trans (mem_singleton_iff.1 hv).symm) huv
  have orderedEnds : ∃ a b, χ.Φ.γ side = [a, b] ∧ IsLineWithEnds (closure side) a b := by
    exact frame_side_endpoints_follow_orientation (S := S) (β := β) χ (side := side) Θ u v huv
      hset hline hn2 hnd hgs hu hv hts
  obtain ⟨a, b, hγ, hab⟩ := orderedEnds
  have htab : tilde side = {a, b} := by
    exact oriented_endpoints_are_tilde (S := S) (β := β) χ (side := side) hgs a b hγ
  obtain ⟨f, ha, hb, himg⟩ := exists_angle_of_line hO hab hLΘ
  set g := cuffPoint f with hg
  have hpos := Real.pi_pos
  have hgc : Continuous g := continuous_cuffAngle f
  have hinj : ∀ {x y}, x ∈ Ico 0 (2 * π) → y ∈ Ico 0 (2 * π) → g x = g y → x = y := fun hx hy he ↦
    cuffAngle_injOn f (a := 0) (by simpa using hx) (by simpa using hy) he
  have hab' : a ≠ b := (ends_of_line hab).2.2
  have hside_eq : side = g '' Ioo 0 π := by
    exact side_equals_first_open_semicircle (S := S) (side := side) a b htab g ha hb himg hpos
      hinj
  have haV : a ∈ χ.Φ.V := by
    have : a ∈ ({u, v} : Set S) := by rw [← hts, htab]; exact mem_insert _ _
    have h₂ : a ∈ closure side ∩ (χ.Φ.V ∩ Θ) := by rw [hset]; exact this
    exact h₂.2.1
  have hbV : b ∈ χ.Φ.V := by
    have : b ∈ ({u, v} : Set S) := by rw [← hts, htab]; exact mem_insert_of_mem _ rfl
    have h₂ : b ∈ closure side ∩ (χ.Φ.V ∩ Θ) := by rw [hset]; exact this
    exact h₂.2.1
  have hg2 : g (2 * π) = a := by
    have h₀ : g (2 * π) = g 0 := by
      have := cuffAngle_add_two_pi f 0
      rwa [zero_add] at this
    exact h₀.trans ha
  have hΘb : Θ ⊆ bd S := fun z hz ↦ cuff_subset_bd ⟨Θ, hΘ⟩ hz
  have hconnΘ : ∀ {Y : Set S}, Y ⊆ bd S → IsPreconnected Y → (Y ∩ Θ).Nonempty → Y ⊆ Θ := by
    exact connected_boundary_set_stays_on_cuff (S := S) Θ hΘ
  have hlocalU : ∀ Y, Y ⊆ Γ.U \ Γ.V → IsPathConnected Y → (Y ∩ Θ).Nonempty → Y ⊆ Θ := by
    exact drawing_interior_component_stays_on_cuff (S := S) (Γ := Γ) Θ hΘb hconnΘ
  have hlocalB : ∀ Y, Y ⊆ bd S \ χ.Φ.V → IsPathConnected Y → (Y ∩ Θ).Nonempty → Y ⊆ Θ
    := fun Y hY hYp hne ↦
    hconnΘ (fun w hw ↦ (hY hw).1) hYp.isConnected.isPreconnected hne
  -- The vertices of `Γ` along the side.
  set T : Set ℝ := {y ∈ Icc 0 π | g y ∈ Γ.V} with hT
  have hTf : T.Finite := by
    exact finite_angles_of_drawing_vertices (S := S) (Γ := Γ) g hpos hinj
  have h0T : 0 ∈ T := ⟨⟨le_rfl, hpos.le⟩, ha.symm ▸ hfit.V_subset haV⟩
  have hπT : π ∈ T := ⟨⟨hpos.le, le_rfl⟩, hb.symm ▸ hfit.V_subset hbV⟩
  obtain ⟨k, t, hk, h0, hkt, hmono, hmemT⟩ := exists_sorted hTf hpos h0T hπT (fun _ h => h.1)
  have hrange : ∀ {i}, i ≤ k → t i ∈ Icc 0 π := fun {i} hi ↦ by
    have : t i ∈ T := (hmemT _).2 ⟨i, hi, rfl⟩
    exact this.1
  have hgapT : ∀ {i}, i < k → ∀ y ∈ Ioo (t i) (t (i + 1)), y ∉ T := by
    intro i hi y hy hyT
    obtain ⟨j, hj, rfl⟩ := (hmemT y).1 hyT
    rcases Nat.lt_or_ge j (i + 1) with h' | h'
    · have := sorted_le hmono (show j ≤ i by omega) (by omega)
      linarith [hy.1]
    · have := sorted_le hmono h' hj
      linarith [hy.2]
  have hsubside : ∀ {i}, i < k → Ioo (t i) (t (i + 1)) ⊆ Ioo 0 π := fun {i} hi y hy ↦
    ⟨lt_of_le_of_lt (hrange (by omega)).1 hy.1, lt_of_lt_of_le hy.2 (hrange (by omega)).2⟩
  -- The vertices of the frame on the rest of the cuff.
  set T' : Set ℝ := {y ∈ Icc π (2 * π) | g y ∈ χ.Φ.V} with hT'
  have hT'f : T'.Finite := by
    exact finite_angles_of_frame_vertices (S := S) (β := β) χ g hpos hinj
  have hπT' : π ∈ T' := ⟨⟨le_rfl, by linarith⟩, hb.symm ▸ hbV⟩
  have h2πT' : 2 * π ∈ T' := ⟨⟨by linarith, le_rfl⟩, hg2.symm ▸ haV⟩
  obtain ⟨q, w, hq, hw0, hwq, hwm, hmemT'⟩ :=
    exists_sorted hT'f (by linarith : π < 2 * π) hπT' h2πT' (fun _ h => h.1)
  have hwr : ∀ {i}, i ≤ q → w i ∈ Icc π (2 * π) := fun {i} hi ↦ by
    have : w i ∈ T' := (hmemT' _).2 ⟨i, hi, rfl⟩
    exact this.1
  have hgapT' : ∀ {i}, i < q → ∀ y ∈ Ioo (w i) (w (i + 1)), y ∉ T' := by
    intro i hi y hy hyT
    obtain ⟨j, hj, rfl⟩ := (hmemT' y).1 hyT
    rcases Nat.lt_or_ge j (i + 1) with h' | h'
    · have := sorted_le hwm (show j ≤ i by omega) (by omega)
      linarith [hy.1]
    · have := sorted_le hwm h' hj
      linarith [hy.2]
  have hsidesR : ∀ {i}, i < q → g '' Ioo (w i) (w (i + 1)) ∈ χ.Φ.sides := fun {i} hi ↦ by
    have h₁ : g (w i) ∈ χ.Φ.V := ((hmemT' _).2 ⟨i, by omega, rfl⟩ : w i ∈ T').2
    have h₂ : g (w (i + 1)) ∈ χ.Φ.V := ((hmemT' _).2 ⟨i + 1, by omega, rfl⟩ : w (i + 1) ∈ T').2
    refine ioo_mem_arcComponents f (hwm i hi) h₁ h₂ (fun y hy ↦ ?_) hlocalB
    have hyr : y ∈ Icc π (2 * π) := ⟨(hwr (i := i) (by omega)).1.trans hy.1.le, hy.2.le.trans (hwr
      (i := i + 1) (by omega)).2⟩
    exact ⟨hΘb (cuffAngle_mem f y), fun hV ↦ hgapT' hi y hy ⟨hyr, hV⟩⟩
  have hdisjR : ∀ {x y}, x ∈ Ioo 0 π → y ∈ Ioo π (2 * π) → g x ≠ g y := fun hx hy he ↦ by
    have := hinj ⟨hx.1.le, by linarith [hx.2]⟩ ⟨by linarith [hy.1], hy.2⟩ he
    linarith [hx.2, hy.1]
  have hshortR : ∀ {i}, i < q → (i = 0 ∨ i + 1 = q) → g '' Ioo (w i) (w (i + 1)) ∈ χ.Φ.shortSides
    := by
    exact extreme_intervals_are_short_sides (S := S) (β := β) χ (side := side) hside a b htab g hb
      hgc hside_eq haV hbV hg2 q w hw0 hwq hwm hwr hsidesR hdisjR
  have hshorts : ∀ s ∈ χ.Φ.shortSides, s ⊆ Θ → s ⊆ g '' Ioo π (2 * π) ∧ ∃ i < q, s = g '' Ioo (w i)
    (w (i + 1)) := by
    exact short_sides_on_cuff_are_intervals (S := S) (β := β) χ (side
      := side) hside Θ a b f g rfl ha
      hb hside_eq haV hbV q w hw0 hwq hmemT' hsidesR
  let e : ℕ → Set S := fun i ↦ if i = 0 then g '' Ioo (w (q - 1)) (w (q - 1 + 1)) else if i
    = k + 1 then g '' Ioo (w 0) (w (0 + 1)) else g '' Ioo (t (i - 1)) (t i)
  have he0 : e 0 = g '' Ioo (w (q - 1)) (w (q - 1 + 1)) := ite_eq_left rfl
  have hek : e (k + 1) = g '' Ioo (w 0) (w (0 + 1)) := by
    change (if k + 1 = 0 then _ else if k + 1 = k + 1 then _ else _) = _
    rw [ite_eq_right (by omega), ite_eq_left rfl]
  have hei : ∀ i < k, e (i + 1) = g '' Ioo (t i) (t (i + 1)) := fun i hi ↦ by
    change (if i + 1 = 0 then _ else if i + 1 = k + 1 then _ else _) = _
    rw [ite_eq_right (by omega), ite_eq_right (by omega), Nat.add_sub_cancel]
  have hq1 : q - 1 + 1 = q := by omega
  have hmemE : ∀ i < k, e (i + 1) ∈ Γ.E := fun i hi ↦ by
    exact successive_drawing_vertex_angles_bound_edge (S := S) (Γ := Γ) Θ f g rfl hΘb
      hlocalU k t hmono hmemT hrange hgapT e hei i hi
  refine ⟨Θ, hΘ, f, a, b, k, t, e, hsΘ, ?_⟩
  refine
    { head := by rw [hγ]; rfl
      last := by rw [hγ]; rfl
      ga := ha
      gb := hb
      side_eq := hside_eq
      k_pos := hk
      t0 := h0
      tk := hkt
      mono := hmono
      e_eq := hei
      mem := fun i hi ↦ ?_
      all := fun c hc hsub ↦ ?_
      e_zero := ⟨w (q - 1), (hwr (by omega)).1, ?_, ?_⟩
      e_last := ⟨w 1, ?_, (hwr (i := 1) (by omega)).2, ?_⟩
      short := fun s hs hne ↦ ?_
      rest := fun s hs hsub ↦ (hshorts s hs hsub).1
      short_zero := by
        rw [he0]
        exact hshortR (by omega) (Or.inr hq1) }
  · rcases Nat.eq_zero_or_pos i with rfl | hi₀
    · rw [he0]
      exact hfit.short_sides (hshortR (by omega) (Or.inr hq1))
    · rcases eq_or_ne i (k + 1) with rfl | hik
      · rw [hek]
        exact hfit.short_sides (hshortR (by omega) (Or.inl rfl))
      · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
        exact hmemE j (by omega)
  · obtain ⟨z, hz⟩ := hc.1
    have hzs := hsub hz
    rw [hside_eq] at hzs
    obtain ⟨y, hy, rfl⟩ := hzs
    rcases sorted_cases (t := t) (k := k) (y := y) (h0.trans_le hy.1.le)
      (by rw [hkt]; exact hy.2.le) with ⟨i, hi, rfl⟩ | ⟨i, hi, hm⟩
    · exact absurd ((hmemT _).2 ⟨i, hi, rfl⟩ : t i ∈ T).2 fun hV ↦ Γ.disjoint_V hc hz hV
    · have hm' : g y ∈ e (i + 1) := by
        rw [hei i hi]
        exact mem_image_of_mem g hm
      exact ⟨i + 1, by omega, by omega, GM11.arcComponent_eq hc (hmemE i hi) hz hm'⟩
  · have := hwm (q - 1) (by omega)
    rw [hq1, hwq] at this
    exact this
  · rw [he0, hq1, hwq]
  · have := hwm 0 (by omega)
    rw [hw0] at this
    exact this
  · rw [hek, hw0]
  · exact short_side_touching_long_side_is_extreme (S := S) (β := β) hS χ (side := side) Θ hΘ hLΘ
      g himg hpos hgc hinj k q w hw0 hwq hwm hwr hshorts e he0 hek s hs hne

end

namespace IsSideEdges

variable {χ : ColourScheme S β} {Γ : Painting S} {side Θ : Set S} {f : Circle ≃ₜ Θ} {a b : S} {k :
  ℕ} {t : ℕ → ℝ} {e : ℕ → Set S}

omit [T2Space S] in
theorem e_eq' (h : IsSideEdges χ Γ side Θ f a b k t e) {l : ℕ} (h₁ : 1 ≤ l) (h₂ : l ≤ k) : e l
  = cuffPoint f '' Ioo (t (l - 1)) (t l) := by
  obtain ⟨j, rfl⟩ : ∃ j, l = j + 1 := ⟨l - 1, by omega⟩
  simpa using h.e_eq j (by omega)

omit [T2Space S] in
theorem t_range (h : IsSideEdges χ Γ side Θ f a b k t e) {i : ℕ} (hi : i ≤ k) : t i ∈ Icc 0 π := by
  constructor
  · rw [← h.t0]
    exact sorted_le h.mono (by omega) hi
  · rw [← h.tk]
    exact sorted_le h.mono hi le_rfl

omit [T2Space S] in
theorem ioo_subset (h : IsSideEdges χ Γ side Θ f a b k t e) {l : ℕ} (h₁ : 1 ≤ l) (h₂ : l ≤ k) : Ioo
  (t (l - 1)) (t l) ⊆ Ioo 0 π := fun _ hy ↦
  ⟨lt_of_le_of_lt (h.t_range (by omega)).1 hy.1, lt_of_lt_of_le hy.2 (h.t_range h₂).2⟩

omit [T2Space S] in
theorem subset_side (h : IsSideEdges χ Γ side Θ f a b k t e) {l : ℕ} (h₁ : 1 ≤ l) (h₂ : l
  ≤ k) : e l ⊆ side := by
  rw [h.e_eq' h₁ h₂, h.side_eq]
  exact image_mono (h.ioo_subset h₁ h₂)

omit [T2Space S] in
theorem lt_gap (h : IsSideEdges χ Γ side Θ f a b k t e) {l : ℕ} (h₁ : 1 ≤ l) (h₂ : l ≤ k) : t
  (l - 1) < t l := by
  obtain ⟨j, rfl⟩ : ∃ j, l = j + 1 := ⟨l - 1, by omega⟩
  simpa using h.mono j (by omega)

omit [T2Space S] in
/-- A point of each edge, at the middle of its angles. -/
theorem exists_point (h : IsSideEdges χ Γ side Θ f a b k t e) {l : ℕ} (h₁ : 1 ≤ l) (h₂ : l
  ≤ k) : ∃ x ∈ Ioo (t (l - 1)) (t l), cuffPoint f x ∈ e l := by
  obtain ⟨x, hx⟩ := nonempty_Ioo.2 (h.lt_gap h₁ h₂)
  exact ⟨x, hx, h.e_eq' h₁ h₂ ▸ mem_image_of_mem _ hx⟩

omit [T2Space S] in
theorem angle_of_mem (h : IsSideEdges χ Γ side Θ f a b k t e) {l : ℕ} (h₁ : 1 ≤ l) (h₂ : l
  ≤ k) {z : S} (hz : z ∈ e l) : ∃ x ∈ Ioo (t (l - 1)) (t l), cuffPoint f x = z := by
  rw [h.e_eq' h₁ h₂] at hz
  exact hz

omit [T2Space S] in
theorem pos_angle (h : IsSideEdges χ Γ side Θ f a b k t e) {l : ℕ} (h₁ : 1 ≤ l) (h₂ : l
  ≤ k) {x : ℝ} (hx : x ∈ Ioo (t (l - 1)) (t l)) : x ∈ Ioo 0 π :=
  h.ioo_subset h₁ h₂ hx

omit [T2Space S] in
/-- Two edges along the side in order have angles in order. -/
theorem lt_of_lt (h : IsSideEdges χ Γ side Θ f a b k t e) {l l' : ℕ} (hl : 1 ≤ l) (h₂ : l < l')
  (hl' : l' ≤ k) {x y : ℝ} (hx : x ∈ Ioo (t (l - 1)) (t l))
    (hy : y ∈ Ioo (t (l' - 1)) (t l')) : x < y := by
  have := sorted_le h.mono (show l ≤ l' - 1 by omega) (by omega)
  linarith [hx.2, hy.1]

omit [T2Space S] in
theorem injOn_edges (h : IsSideEdges χ Γ side Θ f a b k t e) {l l' : ℕ} (hl : 1 ≤ l) (h₂ : l < l')
  (hl' : l' ≤ k) : e l ≠ e l' := by
  intro he
  obtain ⟨x, hx, hxe⟩ := h.exists_point hl (by omega)
  rw [he] at hxe
  obtain ⟨y, hy, hye⟩ := h.angle_of_mem (by omega) hl' hxe
  have hlt := h.lt_of_lt hl h₂ hl' hx hy
  have hx₀ := h.pos_angle hl (by omega) hx
  have hy₀ := h.pos_angle (by omega) hl' hy
  have := cuffAngle_injOn f (a := 0) (x := y) (y := x) ⟨hy₀.1.le, by linarith [hy₀.2, Real.pi_pos]⟩
    ⟨hx₀.1.le, by linarith [hx₀.2, Real.pi_pos]⟩ hye
  linarith

omit [T2Space S] in
theorem inOrder (h : IsSideEdges χ Γ side Θ f a b k t e) {l l' : ℕ} (hl : 1 ≤ l) (h₂ : l < l')
  (hl' : l' ≤ k) {x y : S} (hx : x ∈ e l) (hy : y ∈ e l') : InOrderOn Θ a x y b := by
  obtain ⟨s₁, hs₁, rfl⟩ := h.angle_of_mem hl (by omega) hx
  obtain ⟨s₂, hs₂, rfl⟩ := h.angle_of_mem (by omega) hl' hy
  have h₁ := h.pos_angle hl (by omega) hs₁
  have h₃ := h.pos_angle (by omega) hl' hs₂
  exact ⟨f, 0, s₁, s₂, π, h₁.1.le, (h.lt_of_lt hl h₂ hl' hs₁ hs₂).le, h₃.2.le,
    by linarith [Real.pi_pos], h.ga, rfl, rfl, h.gb⟩

omit [T2Space S] in
/-- Each point of `side` lies on the closure of an edge of the side. -/
theorem side_subset_of_closed (h : IsSideEdges χ Γ side Θ f a b k t e) {J : Set S}
  (hJ : IsClosed J) (hsub : ∀ l, 1 ≤ l → l ≤ k → e l ⊆ J) : side ⊆ J := by
  have hg := continuous_cuffAngle f
  have hcl : ∀ l, 1 ≤ l → l ≤ k → cuffPoint f '' Icc (t (l - 1)) (t l) ⊆ J := by
    intro l h₁ h₂
    have hne := (h.lt_gap h₁ h₂).ne
    rw [← closure_Ioo hne]
    refine (image_closure_subset_closure_image hg).trans (closure_minimal ?_ hJ)
    rw [← h.e_eq' h₁ h₂]
    exact hsub l h₁ h₂
  rw [h.side_eq]
  rintro _ ⟨y, hy, rfl⟩
  rcases sorted_cases (t := t) (k := k) (y := y) (by rw [h.t0]; exact hy.1.le)
    (by rw [h.tk]; exact hy.2.le) with ⟨i, hi, rfl⟩ | ⟨i, hi, hm⟩
  · rcases Nat.eq_zero_or_pos i with rfl | hi₀
    · rw [h.t0] at hy
      exact absurd hy.1 (lt_irrefl _)
    · exact hcl i hi₀ hi (mem_image_of_mem _ ⟨(h.lt_gap hi₀ hi).le, le_rfl⟩)
  · refine hsub (i + 1) (by omega) (by omega) ?_
    rw [h.e_eq i hi]
    exact mem_image_of_mem _ hm

/-- **A connected set with points on two edges of the side holds the edges between them, or those
around the other way.** -/
theorem between (h : IsSideEdges χ Γ side Θ f a b k t e) {J : Set S} (hJ : IsPreconnected J)
  (hJΘ : J ⊆ Θ) {i j : ℕ} (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ k) (h₁ : e i ⊆ J)
    (h₂ : e j ⊆ J) : (∀ l, i ≤ l → l ≤ j → e l ⊆ J) ∨ ((∀ l, l ≤ i → e l ⊆ J) ∧ ∀ l, j ≤ l → l
      ≤ k + 1 → e l ⊆ J) := by
  obtain ⟨x, hx, hxe⟩ := h.exists_point hi (by omega)
  obtain ⟨y, hy, hye⟩ := h.exists_point (by omega) hj
  have hlt := h.lt_of_lt hi hij hj hx hy
  have hx₀ := h.pos_angle hi (by omega) hx
  have hy₀ := h.pos_angle (by omega) hj hy
  have hpos := Real.pi_pos
  rcases arc_of_preconnected f hJ hJΘ hlt.le (by linarith [hy₀.2, hx₀.1]) (h₁ hxe)
    (h₂ hye) with hc | hc
  · left
    intro l hl₁ hl₂
    rcases eq_or_lt_of_le hl₁ with rfl | hl₁
    · exact h₁
    rcases eq_or_lt_of_le hl₂ with rfl | hl₂
    · exact h₂
    rw [h.e_eq' (by omega) (by omega)]
    rintro _ ⟨z, hz, rfl⟩
    have h₃ := sorted_le h.mono (show i ≤ l - 1 by omega) (by omega)
    have h₄ := sorted_le h.mono (show l ≤ j - 1 by omega) (by omega)
    exact hc z ⟨by linarith [hx.2, hz.1], by linarith [hz.2, hy.1]⟩
  · right
    constructor
    · intro l hl
      rcases eq_or_lt_of_le hl with rfl | hl
      · exact h₁
      rcases Nat.eq_zero_or_pos l with rfl | hl₀
      · obtain ⟨d, hd₁, hd₂, hd⟩ := h.e_zero
        rw [hd]
        rintro _ ⟨z, hz, rfl⟩
        exact hc z ⟨by linarith [hz.1, hy₀.2], by linarith [hz.2, hx₀.1]⟩
      · rw [h.e_eq' hl₀ (by omega)]
        rintro _ ⟨z, hz, rfl⟩
        have hzp := h.pos_angle hl₀ (by omega) hz
        rw [← cuffAngle_add_two_pi]
        have h₃ := sorted_le h.mono (show l ≤ i - 1 by omega) (by omega)
        exact hc _ ⟨by linarith [hy₀.2, hzp.1], by linarith [hz.2, hx.1]⟩
    · intro l hl₁ hl₂
      rcases eq_or_lt_of_le hl₁ with rfl | hl₁
      · exact h₂
      rcases eq_or_lt_of_le hl₂ with rfl | hl₂
      · obtain ⟨c', hc₁, hc₂, hd⟩ := h.e_last
        rw [hd]
        rintro _ ⟨z, hz, rfl⟩
        exact hc z ⟨by linarith [hz.1, hy₀.2], by linarith [hz.2, hx₀.1]⟩
      · rw [h.e_eq' (by omega) (by omega)]
        rintro _ ⟨z, hz, rfl⟩
        have hzp := h.pos_angle (by omega) (by omega) hz
        have h₃ := sorted_le h.mono (show j ≤ l - 1 by omega) (by omega)
        exact hc z ⟨by linarith [hy.2, hz.1], by linarith [hzp.2, hx₀.1]⟩

/-- **A connected set with a point on an edge of the side and a short side holds what lies on one
way around.** -/
theorem between_short (h : IsSideEdges χ Γ side Θ f a b k t e) {J : Set S} (hJ : IsPreconnected J)
  (hJΘ : J ⊆ Θ) {i : ℕ} (hi : 1 ≤ i) (hik : i ≤ k) (h₁ : e i ⊆ J) {s : Set S}
    (hs : s ∈ χ.Φ.shortSides) (hsΓ : s ∈ Γ.E) (hsΘ : s ⊆ Θ) (h₂ : s ⊆ J) : (∀ l, i ≤ l → l ≤ k + 1
      → e l ⊆ J) ∨ ∀ l, l ≤ i → e l ⊆ J := by
  obtain ⟨x, hx, hxe⟩ := h.exists_point hi hik
  have hx₀ := h.pos_angle hi hik hx
  obtain ⟨z₀, hz₀⟩ := hs.1.1
  obtain ⟨y, hy, hye⟩ := h.rest s hs hsΘ hz₀
  have hpos := Real.pi_pos
  have hy₂ : cuffPoint f y ∈ J := by rw [hye]; exact h₂ hz₀
  have hlast := h.mem (k + 1) le_rfl
  have hzero := h.mem 0 (by omega)
  rcases arc_of_preconnected f hJ hJΘ (x₁ := x) (x₂ := y) (by linarith [hx₀.2, hy.1])
    (by linarith [hy.2, hx₀.1]) (h₁ hxe) hy₂ with hc | hc
  · left
    intro l hl₁ hl₂
    rcases eq_or_lt_of_le hl₁ with rfl | hl₁
    · exact h₁
    rcases eq_or_lt_of_le hl₂ with rfl | hl₂
    · obtain ⟨c', hc₁, hc₂, hd⟩ := h.e_last
      by_cases hin : y < c'
      · have hyl : cuffPoint f y ∈ e (k + 1) := by
          rw [hd]
          exact mem_image_of_mem _ ⟨hy.1, hin⟩
        have heq : e (k + 1) = s := GM11.arcComponent_eq hlast hsΓ hyl (hye ▸ hz₀)
        rw [heq]
        exact h₂
      · rw [hd]
        rintro _ ⟨z, hz, rfl⟩
        exact hc z ⟨by linarith [hz.1, hx₀.2], by linarith [hz.2, not_lt.1 hin]⟩
    · rw [h.e_eq' (by omega) (by omega)]
      rintro _ ⟨z, hz, rfl⟩
      have hzp := h.pos_angle (by omega) (by omega) hz
      have h₃ := sorted_le h.mono (show i ≤ l - 1 by omega) (by omega)
      exact hc z ⟨by linarith [hx.2, hz.1], by linarith [hzp.2, hy.1]⟩
  · right
    intro l hl
    rcases eq_or_lt_of_le hl with rfl | hl
    · exact h₁
    rcases Nat.eq_zero_or_pos l with rfl | hl₀
    · obtain ⟨d, hd₁, hd₂, hd⟩ := h.e_zero
      by_cases hin : d < y
      · have hyl : cuffPoint f y ∈ e 0 := by
          rw [hd]
          exact mem_image_of_mem _ ⟨hin, hy.2⟩
        have heq : e 0 = s := GM11.arcComponent_eq hzero hsΓ hyl (hye ▸ hz₀)
        rw [heq]
        exact h₂
      · rw [hd]
        rintro _ ⟨z, hz, rfl⟩
        exact hc z ⟨by linarith [hz.1, not_lt.1 hin], by linarith [hz.2, hx₀.1]⟩
    · rw [h.e_eq' hl₀ (by omega)]
      rintro _ ⟨z, hz, rfl⟩
      have hzp := h.pos_angle hl₀ (by omega) hz
      rw [← cuffAngle_add_two_pi]
      have h₃ := sorted_le h.mono (show l ≤ i - 1 by omega) (by omega)
      exact hc _ ⟨by linarith [hy.2, hzp.1], by linarith [hz.2, hx.1]⟩

/-- A connected subset of the side with points on two edges holds the edges between them. -/
theorem between_of_side (h : IsSideEdges χ Γ side Θ f a b k t e) {X : Set S}
  (hX : IsPreconnected X) (hXs : X ⊆ side) (hsΘ : side ⊆ Θ) {i j : ℕ} (hi : 1 ≤ i) (hij : i < j)
    (hj : j ≤ k) (h₁ : e i ⊆ X) (h₂ : e j ⊆ X) : ∀ l, i ≤ l → l ≤ j → e l ⊆ X := by
  rcases h.between hX (hXs.trans hsΘ) hi hij hj h₁ h₂ with hc | ⟨-, hc⟩
  · exact hc
  · exfalso
    obtain ⟨c', hc₁, hc₂, hd⟩ := h.e_last
    obtain ⟨y, hy⟩ := nonempty_Ioo.2 hc₁
    have hy' : cuffPoint f y ∈ e (k + 1) := by
      rw [hd]
      exact mem_image_of_mem _ hy
    have hys := hXs (hc (k + 1) (by omega) le_rfl hy')
    rw [h.side_eq] at hys
    obtain ⟨x, hx, he⟩ := hys
    have hpos := Real.pi_pos
    have := cuffAngle_injOn f (a := 0) (x := x) (y := y) ⟨hx.1.le, by linarith [hx.2]⟩ ⟨by linarith
      [hy.1], by rw [zero_add]; linarith [hy.2]⟩ he
    linarith [hx.2, hy.1]

end IsSideEdges

/-- **A long side touches a short side.** -/
theorem exists_short_touching (hS : IsSurface S) (χ : ColourScheme S β) {Γ : Painting S}
  (hfit : Γ.Fits χ.Φ) {side : Set S} (hside : side ∈ χ.Φ.longSides) :
    ∃ s ∈ χ.Φ.shortSides, (closure s ∩ closure side).Nonempty := by
  obtain ⟨Θ, -, f, a, b, k, t, e, -, hE⟩ := exists_sideEdges hS χ hfit hside
  obtain ⟨d, -, hd, he⟩ := hE.e_zero
  refine ⟨_, hE.short_zero, a, ?_, ?_⟩
  · have h₁ : (2 * π : ℝ) ∈ closure (Ioo d (2 * π)) := by
      rw [closure_Ioo hd.ne]
      exact ⟨hd.le, le_rfl⟩
    have h₂ := image_closure_subset_closure_image (continuous_cuffAngle f) (mem_image_of_mem _ h₁)
    have h₃ : cuffPoint f (2 * π) = a := by
      have := cuffAngle_add_two_pi f 0
      rw [zero_add] at this
      rw [this, hE.ga]
    rwa [← he, h₃] at h₂
  · have h₁ : (0 : ℝ) ∈ closure (Ioo 0 π) := by
      rw [closure_Ioo pi_pos.ne]
      exact ⟨le_rfl, pi_pos.le⟩
    have h₂ := image_closure_subset_closure_image (continuous_cuffAngle f) (mem_image_of_mem _ h₁)
    rwa [← hE.side_eq, hE.ga] at h₂

end GraphMinor.GM19
