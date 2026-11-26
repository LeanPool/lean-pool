/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.PadFlower
public import LeanPool.GraphMinor.GM19.Defs

/-!
# Coordinates on lines in a circle

The sides of a frame are lines in a cuff. To compare the order of the ends of the edges of `Γ` with
the order of the vertices of `Γ₀` around a cuff, for step (2) of the proof of Graph Minors XIX,
(15.2), page 381, we read each side by a coordinate in `[0, 1]`. A line in the circle that avoids a
base point lifts to an interval of the line (`exists_side_lift`). The order "in order on the cuff"
of the
paper is then the order of the coordinate along the side (`lineCoord_le_of_inOrder`), and two sides
have intervals that do not overlap (`false_of_overlap`).
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface

local notation "𝕀" => unitInterval

/-- A continuous injective map of `[0, 1]` to the circle that avoids `1` between its ends lifts to
`[0, 1]`. -/
theorem exists_side_lift {f : ℝ → Circle} (hf : ContinuousOn f (Icc 0 1)) (hi : InjOn f (Icc 0 1))
  (hne : ∀ t ∈ Ioo (0 : ℝ) 1, f t ≠ 1) :
    ∃ l : ℝ → ℝ, ContinuousOn l (Icc 0 1) ∧ (StrictMonoOn l (Icc 0 1) ∨ StrictAntiOn l (Icc 0 1))
      ∧ ∀ t ∈ Icc (0 : ℝ) 1, l t ∈ Icc (0 : ℝ) 1 ∧ ee (l t) = f t := by
  have hpi := Real.pi_pos
  let c : ℝ → ℝ := fun t => projIcc 0 1 zero_le_one t
  have hcc : Continuous c := continuous_subtype_val.comp continuous_projIcc
  have hcm : ∀ t, c t ∈ Icc (0 : ℝ) 1 := fun t => (projIcc 0 1 zero_le_one t).2
  have hce : ∀ t ∈ Icc (0 : ℝ) 1, c t = t := fun t ht => by simp [c, projIcc_of_mem zero_le_one ht]
  let g : ℝ → ℂ := fun t => f (c t)
  have hgc : Continuous g := continuous_induced_dom.comp (hf.comp_continuous hcc hcm)
  obtain ⟨L, hL⟩ := exists_isAngle hgc fun t => Circle.coe_ne_zero _
  have hLe : ∀ t ∈ Icc (0 : ℝ) 1, ee (L t / (2 * Real.pi)) = f t := fun t ht => by
    have h1 := hL.2 t
    have h2 : g t = f t := by simp only [g, hce t ht]
    apply Circle.ext
    rw [ee, mul_div_cancel₀ _ (by positivity), Circle.coe_exp, ← h2, h1]
    simp [g]
  let l₀ : ℝ → ℝ := fun t => L t / (2 * Real.pi)
  have hl₀c : Continuous l₀ := hL.1.div_const _
  have hint : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ n : ℤ, l₀ t ≠ n := fun t ht n h => by
    have h1 := hLe t ⟨ht.1.le, ht.2.le⟩
    have h2 : ee (n : ℝ) = 1 := by
      rw [ee, show 2 * Real.pi * (n : ℝ) = n * (2 * Real.pi) by ring, Circle.exp_int_mul_two_pi]
    exact hne t ht (by rw [← h1]; change ee (l₀ t) = 1; rw [h, h2])
  let k : ℤ := ⌊l₀ (1 / 2)⌋
  let l : ℝ → ℝ := fun t => l₀ t - k
  have hmid : l (1 / 2) ∈ Ioo (0 : ℝ) 1 := by
    have h1 : (k : ℝ) ≤ l₀ (1 / 2) := Int.floor_le _
    have h2 : l₀ (1 / 2) < k + 1 := Int.lt_floor_add_one _
    have h3 := hint (1 / 2) (by norm_num) k
    exact ⟨sub_pos.mpr (lt_of_le_of_ne h1 (Ne.symm h3)), by simp only [l]; linarith⟩
  have hlc : Continuous l := hl₀c.sub continuous_const
  have hnot : ∀ t ∈ Ioo (0 : ℝ) 1, l t ≠ 0 ∧ l t ≠ 1 := fun t ht => by
    constructor
    · intro h
      exact hint t ht k (by simp only [l] at h; linarith)
    · intro h
      refine hint t ht (k + 1) ?_
      simp only [l] at h
      push_cast
      linarith
  have hcross : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ v : ℝ, (v = 0 ∨ v = 1) → v ∉ uIcc (l t) (l (1 / 2))
    := fun t ht v hv hm => by
    obtain ⟨s, hs, hsv⟩ := intermediate_value_uIcc (hlc.continuousOn (s := uIcc t (1 / 2))) hm
    have hsI : s ∈ Ioo (0 : ℝ) 1 := by
      have h1 : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := by norm_num
      exact (ordConnected_Ioo.uIcc_subset ht h1) hs
    obtain ⟨h1, h2⟩ := hnot s hsI
    rcases hv with rfl | rfl
    · exact h1 hsv
    · exact h2 hsv
  have hIoo : ∀ t ∈ Ioo (0 : ℝ) 1, l t ∈ Ioo (0 : ℝ) 1 := fun t ht => by
    constructor
    · by_contra hn
      exact hcross t ht 0 (Or.inl rfl) (by rw [mem_uIcc]; exact Or.inl ⟨not_lt.mp hn, hmid.1.le⟩)
    · by_contra hn
      exact hcross t ht 1 (Or.inr rfl) (by rw [mem_uIcc]; exact Or.inr ⟨hmid.2.le, not_lt.mp hn⟩)
  have hIcc : ∀ t ∈ Icc (0 : ℝ) 1, l t ∈ Icc (0 : ℝ) 1 := by
    have hs : Icc (0 : ℝ) 1 ⊆ closure (Ioo 0 1) := by rw [closure_Ioo (by norm_num)]
    intro t ht
    have h1 := map_mem_closure hlc (hs ht) (t := Icc 0 1) fun x hx => ⟨(hIoo x hx).1.le,
      (hIoo x hx).2.le⟩
    rwa [isClosed_Icc.closure_eq] at h1
  have hee : ∀ t ∈ Icc (0 : ℝ) 1, ee (l t) = f t := fun t ht => by
    have h1 := ee_add (l t) k
    have h2 : ee (k : ℝ) = 1 := by
      rw [ee, show 2 * Real.pi * (k : ℝ) = k * (2 * Real.pi) by ring, Circle.exp_int_mul_two_pi]
    rw [sub_add_cancel, h2, mul_one] at h1
    rw [← h1]
    exact hLe t ht
  have hli : InjOn l (Icc 0 1) := fun x hx y hy he => hi hx hy (by rw [← hee x hx, ← hee y hy, he])
  exact ⟨l, hlc.continuousOn, ContinuousOn.strictMonoOn_of_injOn_Icc' zero_le_one hlc.continuousOn
    hli, fun t ht => ⟨hIcc t ht, hee t ht⟩⟩

variable {S : Type} [TopologicalSpace S] [T2Space S]

open Classical in
/-- The coordinate of a point on a line. -/
noncomputable def lineCoord {L : Set S} (σ : 𝕀 ≃ₜ L) (x : S) : ℝ :=
  if h : x ∈ L then (σ.symm ⟨x, h⟩).1 else 0

/-- The point of a line at a coordinate. -/
noncomputable def linePoint {L : Set S} (σ : 𝕀 ≃ₜ L) (t : ℝ) : S := (σ
  (projIcc 0 1 zero_le_one t)).1

omit [T2Space S] in
theorem continuous_linePoint {L : Set S} (σ : 𝕀 ≃ₜ L) : Continuous (linePoint σ) :=
  continuous_subtype_val.comp (σ.continuous.comp continuous_projIcc)

omit [T2Space S] in
theorem lineCoord_coe {L : Set S} (σ : 𝕀 ≃ₜ L) (t : 𝕀) : lineCoord σ (σ t).1 = t := by
  simp [lineCoord]

omit [T2Space S] in
theorem lineCoord_mem {L : Set S} (σ : 𝕀 ≃ₜ L) (x : S) : lineCoord σ x ∈ Icc (0 : ℝ) 1 := by
  unfold lineCoord
  split_ifs with h
  · exact (σ.symm ⟨x, h⟩).2
  · exact ⟨le_rfl, zero_le_one⟩

omit [T2Space S] in
theorem linePoint_coord {L : Set S} (σ : 𝕀 ≃ₜ L) {x : S} (h : x ∈ L) : linePoint σ (lineCoord σ x)
  = x := by
  simp only [linePoint, lineCoord, dite_eq_left h]
  simp

omit [T2Space S] in
theorem linePoint_mem {L : Set S} (σ : 𝕀 ≃ₜ L) (t : ℝ) : linePoint σ t ∈ L := (σ _).2

omit [T2Space S] in
theorem lineCoord_point {L : Set S} (σ : 𝕀 ≃ₜ L) {t : ℝ} (h : t ∈ Icc (0 : ℝ) 1) : lineCoord σ
  (linePoint σ t) = t := by
  have : projIcc 0 1 zero_le_one t = ⟨t, h⟩ := projIcc_of_mem _ h
  simp only [linePoint, this]
  exact lineCoord_coe σ ⟨t, h⟩

omit [T2Space S] in
theorem injOn_linePoint {L : Set S} (σ : 𝕀 ≃ₜ L) : InjOn (linePoint σ) (Icc 0 1)
  := fun x hx y hy he => by
  rw [← lineCoord_point σ hx, ← lineCoord_point σ hy, he]

omit [T2Space S] in
theorem continuousOn_lineCoord {L : Set S} (σ : 𝕀 ≃ₜ L) : ContinuousOn (lineCoord σ) L := by
  rw [continuousOn_iff_continuous_domRestrict]
  have : L.domRestrict (lineCoord σ) = fun x : L => (σ.symm x).1 := by
    funext x
    change lineCoord σ x.1 = _
    rw [lineCoord, dite_eq_left x.2]
  rw [this]
  exact continuous_subtype_val.comp σ.symm.continuous

omit [T2Space S] in
/-- Two parametrizations of a line with the same ends run the same way. -/
theorem lineCoord_lt_of_ends {L : Set S} (σ f : 𝕀 ≃ₜ L) (h0 : f 0 = σ 0) (h1 : f 1
  = σ 1) {t₁ t₂ : 𝕀} (ht : t₁ < t₂) : lineCoord σ (f t₁).1 < lineCoord σ (f t₂).1 := by
  let k : ℝ → ℝ := fun t => lineCoord σ (linePoint f t)
  have hk : ContinuousOn k (Icc 0 1) := (continuousOn_lineCoord σ).comp
    (continuous_linePoint f).continuousOn fun t _ => linePoint_mem f t
  have hi : InjOn k (Icc 0 1) := fun x hx y hy he => by
    have h2 : linePoint f x = linePoint f y := by
      rw [← linePoint_coord σ (linePoint_mem f x), ← linePoint_coord σ (linePoint_mem f y)]
      exact congrArg _ he
    exact injOn_linePoint f hx hy h2
  have hval : ∀ t : 𝕀, k t = lineCoord σ (f t).1 := fun t => by
    have : projIcc (0 : ℝ) 1 zero_le_one t.1 = t := projIcc_val _ t
    simp only [k, linePoint, this]
  have hk0 : k 0 = 0 := by
    have := hval 0
    rw [h0, lineCoord_coe] at this
    simpa using this
  have hk1 : k 1 = 1 := by
    have := hval 1
    rw [h1, lineCoord_coe] at this
    simpa using this
  rw [← hval, ← hval]
  rcases ContinuousOn.strictMonoOn_of_injOn_Icc' zero_le_one hk hi with hm | hm
  · exact hm t₁.2 t₂.2 ht
  · have := hm (left_mem_Icc.mpr zero_le_one) (right_mem_Icc.mpr zero_le_one) zero_lt_one
    rw [hk0, hk1] at this
    linarith

omit [T2Space S] in
/-- **In order on a cuff is in order along a side.** If `x` and `y` lie on the line from `u₀` to
`u₁` in a circle `Θ`, and `u₀, x, y, u₁` occur in order on `Θ`, then the coordinate of `x` is at
most that of `y`. -/
theorem lineCoord_le_of_inOrder {Θ L : Set S} (hsub : L ⊆ Θ) (σ : 𝕀 ≃ₜ L) {u₀ u₁ x y : S}
  (h : InOrderOn Θ u₀ x y u₁) (hu₀ : (σ 0).1 = u₀) (hu₁ : (σ 1).1 = u₁) (hne : u₀ ≠ u₁)
    (hx : x ∈ L) (hy : y ∈ L)
    (hx0 : x ≠ u₀) (hx1 : x ≠ u₁) (hy0 : y ≠ u₀) : lineCoord σ x ≤ lineCoord σ y := by
  obtain ⟨F, t₁, t₂, t₃, t₄, h12, h23, h34, h41, e₁, e₂, e₃, e₄⟩ := h
  have hpi := Real.pi_pos
  have hP : ∀ t, F (Circle.exp t) = ⟨cuffPoint F t, (F (Circle.exp t)).2⟩ := fun t => rfl
  let G : ℝ → Circle := fun t => (Circle.exp t₁)⁻¹ * F.symm ⟨linePoint σ t, hsub
    (linePoint_mem σ t)⟩
  have hGc : Continuous G := continuous_const.mul (F.symm.continuous.comp
    ((continuous_linePoint σ).subtype_mk _))
  have hGv : ∀ t' z (hz : z ∈ L), cuffPoint F t' = z → G (lineCoord σ z) = ee ((t' - t₁) /
    (2 * Real.pi)) := fun t' z hz he => by
    have h1 : (⟨linePoint σ (lineCoord σ z), hsub (linePoint_mem σ _)⟩ : Θ) = F (Circle.exp t')
      := Subtype.ext ((linePoint_coord σ hz).trans he.symm)
    simp only [G]
    rw [h1, Homeomorph.symm_apply_apply, ee, mul_div_cancel₀ _ (by positivity), sub_eq_neg_add,
      Circle.exp_add, Circle.exp_neg]
  have hG0 : G 0 = 1 := by
    have hz : u₀ ∈ L := hu₀ ▸ (σ 0).2
    have h0 : lineCoord σ u₀ = 0 := by rw [← hu₀, lineCoord_coe]; rfl
    have := hGv t₁ u₀ hz e₁
    rw [h0] at this
    rw [this]
    simp [ee]
  have hGi : InjOn G (Icc 0 1) := fun a ha b hb he => by
    have h1 := F.symm.injective (mul_left_cancel he)
    have h2 : linePoint σ a = linePoint σ b := congrArg (fun x : Θ => x.1) h1
    exact injOn_linePoint σ ha hb h2
  have hGne : ∀ t ∈ Ioc (0 : ℝ) 1, G t ≠ 1 := fun t ht he => by
    have := hGi ⟨ht.1.le, ht.2⟩ (left_mem_Icc.mpr zero_le_one) (he.trans hG0.symm)
    linarith [ht.1]
  obtain ⟨l, -, hm, hl⟩ := exists_side_lift hGc.continuousOn hGi fun t ht => hGne t ⟨ht.1, ht.2.le⟩
  have hu0 : lineCoord σ u₀ = 0 := by rw [← hu₀, lineCoord_coe]; rfl
  have hu1 : lineCoord σ u₁ = 1 := by rw [← hu₁, lineCoord_coe]; rfl
  have hu₀m : u₀ ∈ L := hu₀ ▸ (σ 0).2
  have hu₁m : u₁ ∈ L := hu₁ ▸ (σ 1).2
  have hpos : ∀ z ∈ L, z ≠ u₀ → 0 < lineCoord σ z := fun z hz hne => by
    refine lt_of_le_of_ne (lineCoord_mem σ z).1 fun h => hne ?_
    rw [← linePoint_coord σ hz, ← h, ← linePoint_coord σ hu₀m, hu0]
  have hd4 : (t₄ - t₁) / (2 * Real.pi) < 1 := by
    rw [div_lt_one (by positivity)]
    refine lt_of_le_of_ne (by linarith) fun he => hne ?_
    have : t₄ = t₁ + 2 * Real.pi := by linarith
    rw [← e₄, ← e₁, this]
    simp [cuffPoint]
  have hval : ∀ t' z (hz : z ∈ L), z ≠ u₀ → cuffPoint F t' = z → t₁ ≤ t' → t' ≤ t₄ → l
    (lineCoord σ z) = (t' - t₁) / (2 * Real.pi) := fun t' z hz hz0 he h1 h2 => by
    have hd0 : 0 ≤ (t' - t₁) / (2 * Real.pi) := div_nonneg (by linarith) (by positivity)
    have hd1 : (t' - t₁) / (2 * Real.pi) < 1 := by
      refine lt_of_le_of_lt ?_ hd4
      exact div_le_div_of_nonneg_right (by linarith) (by positivity)
    have hc := hpos z hz hz0
    have hm' := lineCoord_mem σ z
    have hl' := hl _ hm'
    have hne1 : ee (l (lineCoord σ z)) ≠ 1 := by
      rw [hl'.2]
      exact hGne _ ⟨hc, hm'.2⟩
    have h0 : l (lineCoord σ z) ≠ 0 := fun h => hne1 (by rw [h]; simp [ee])
    have h1' : l (lineCoord σ z) ≠ 1 := fun h => hne1 (by rw [h]; simp [ee])
    have hlt : l (lineCoord σ z) < 1 := lt_of_le_of_ne hl'.1.2 h1'
    have hgt : 0 < l (lineCoord σ z) := lt_of_le_of_ne hl'.1.1 (Ne.symm h0)
    by_contra hdiff
    refine ee_ne_of_window hdiff ?_ (by rw [hl'.2]; exact hGv t' z hz he)
    rw [abs_lt]
    constructor <;> linarith
  have hu₁0 : u₁ ≠ u₀ := hne.symm
  have v2 := hval t₂ x hx hx0 e₂ h12 (h23.trans h34)
  have v3 := hval t₃ y hy hy0 e₃ (h12.trans h23) h34
  have v4 := hval t₄ u₁ hu₁m hu₁0 e₄ (h12.trans (h23.trans h34)) le_rfl
  have hd23 : (t₂ - t₁) / (2 * Real.pi) ≤ (t₃ - t₁) / (2 * Real.pi) := div_le_div_of_nonneg_right
    (by linarith) (by positivity)
  have hd24 : (t₂ - t₁) / (2 * Real.pi) ≤ (t₄ - t₁) / (2 * Real.pi) := div_le_div_of_nonneg_right
    (by linarith) (by positivity)
  rcases hm with hm | hm
  · by_contra hn
    have := hm (lineCoord_mem σ y) (lineCoord_mem σ x) (not_le.mp hn)
    rw [v2, v3] at this
    linarith
  · exfalso
    have hlt : lineCoord σ x < 1 := by
      refine lt_of_le_of_ne (lineCoord_mem σ x).2 fun h => hx1 ?_
      rw [← linePoint_coord σ hx, h, ← linePoint_coord σ hu₁m, hu1]
    have := hm (lineCoord_mem σ x) (right_mem_Icc.mpr zero_le_one) hlt
    rw [v2, ← hu1, v4] at this
    linarith

/-- Two lines in the circle that lift to the line and do not meet between their ends have intervals
that do not overlap. -/
theorem false_of_overlap {l l' : ℝ → ℝ} {f f' : ℝ → Circle} (hc : ContinuousOn l (Icc 0 1))
  (hc' : ContinuousOn l' (Icc 0 1)) (hm : StrictMonoOn l (Icc 0 1) ∨ StrictAntiOn l (Icc 0 1))
    (hm' : StrictMonoOn l' (Icc 0 1) ∨ StrictAntiOn l' (Icc 0 1)) (he : ∀ t ∈ Icc (0 : ℝ) 1, ee
      (l t) = f t) (he' : ∀ t ∈ Icc (0 : ℝ) 1, ee (l' t) = f' t)
    (hd : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ t' ∈ Ioo (0 : ℝ) 1, f t ≠ f' t') {a b a' b' : ℝ} (ha : a ∈ Icc
      (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1) (ha' : a' ∈ Icc (0 : ℝ) 1) (hb' : b' ∈ Icc (0 : ℝ) 1)
    (h1 : l a < l' b') (h2 : l' a' < l b) : False := by
  have key : ∀ {m : ℝ → ℝ}, ContinuousOn m (Icc 0 1) → (StrictMonoOn m (Icc 0 1) ∨ StrictAntiOn m
    (Icc 0 1)) → ∃ A B : ℝ, A < B ∧ (∀ t ∈ Icc (0 : ℝ) 1, A ≤ m t ∧ m t ≤ B) ∧ ∀ p, A < p → p < B
      → ∃ t ∈ Ioo (0 : ℝ) 1, m t = p := by
    intro m hmc hmm
    have h0 := left_mem_Icc.mpr (zero_le_one' ℝ)
    have h1 := right_mem_Icc.mpr (zero_le_one' ℝ)
    rcases hmm with hmm | hmm
    · refine ⟨m 0, m 1, hmm h0 h1 zero_lt_one, fun t ht => ⟨hmm.monotoneOn h0 ht ht.1,
        hmm.monotoneOn ht h1 ht.2⟩, fun p hA hB => ?_⟩
      obtain ⟨t, ht, htp⟩ := intermediate_value_Icc zero_le_one hmc ⟨hA.le, hB.le⟩
      exact ⟨t, ⟨lt_of_le_of_ne ht.1 fun h => hA.ne (by rw [h, htp]),
        lt_of_le_of_ne ht.2 fun h => hB.ne (by rw [← h, htp])⟩, htp⟩
    · refine ⟨m 1, m 0, hmm h0 h1 zero_lt_one, fun t ht => ⟨hmm.antitoneOn ht h1 ht.2,
        hmm.antitoneOn h0 ht ht.1⟩, fun p hA hB => ?_⟩
      obtain ⟨t, ht, htp⟩ := intermediate_value_Icc' zero_le_one hmc ⟨hA.le, hB.le⟩
      exact ⟨t, ⟨lt_of_le_of_ne ht.1 fun h => hB.ne (by rw [h, htp]),
        lt_of_le_of_ne ht.2 fun h => hA.ne (by rw [← h, htp])⟩, htp⟩
  obtain ⟨A, B, hAB, hb1, hs⟩ := key hc hm
  obtain ⟨A', B', hAB', hb1', hs'⟩ := key hc' hm'
  have h3 : A < B' := by linarith [(hb1 a ha).1, (hb1' b' hb').2]
  have h4 : A' < B := by linarith [(hb1' a' ha').1, (hb1 b hb).2]
  let lo := max A A'
  let hi := min B B'
  have hlh : lo < hi := max_lt (lt_min hAB h3) (lt_min h4 hAB')
  let p := (lo + hi) / 2
  have hp1 : lo < p := by simp only [p]; linarith
  have hp2 : p < hi := by simp only [p]; linarith
  obtain ⟨t, ht, htp⟩ := hs p ((le_max_left _ _).trans_lt hp1) (hp2.trans_le (min_le_left _ _))
  obtain ⟨t', ht', htp'⟩ := hs' p ((le_max_right _ _).trans_lt hp1) (hp2.trans_le
    (min_le_right _ _))
  refine hd t ht t' ht' ?_
  rw [← he t ⟨ht.1.le, ht.2.le⟩, ← he' t' ⟨ht'.1.le, ht'.2.le⟩, htp, htp']

end GraphMinor.GM19
