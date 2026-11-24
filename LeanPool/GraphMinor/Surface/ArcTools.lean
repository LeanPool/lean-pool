/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.DiscMerge

/-!
# Pieces of arcs

Splitting a line at a point, joining two lines at a common end, and the piece of a line between two
parameters.
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology

local notation "𝕀" => unitInterval

universe u

variable {X : Type u} [TopologicalSpace X]

/-- The extension of a map of the unit interval to the real line. -/
noncomputable def extI (a : 𝕀 → X) (t : ℝ) : X := a (projIcc 0 1 zero_le_one t)

theorem continuous_extI {a : 𝕀 → X} (ha : Continuous a) : Continuous (extI a) :=
  ha.comp continuous_projIcc

omit [TopologicalSpace X] in
theorem extI_coe (a : 𝕀 → X) (t : 𝕀) : extI a t = a t := by
  unfold extI
  rw [projIcc_val]

omit [TopologicalSpace X] in
theorem extI_of_mem (a : 𝕀 → X) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : extI a t = a ⟨t, ht⟩
  := extI_coe a ⟨t, ht⟩

/-- The part of `a` between the parameters `s` and `r`. -/
noncomputable def pieceA (a : 𝕀 → X) (s r : ℝ) (u : 𝕀) : X := extI a (s + u * (r - s))

theorem mix_mem {s r : ℝ} (hs : 0 ≤ s) (hsr : s ≤ r) (hr : r ≤ 1) (u : 𝕀) : s + u * (r - s) ∈ Icc
  (0 : ℝ) 1 := by
  have h0 := u.2.1
  have h1 := u.2.2
  have h2 : (u : ℝ) * (r - s) ≤ 1 * (r - s) := mul_le_mul_of_nonneg_right h1 (by linarith)
  have h3 : 0 ≤ (u : ℝ) * (r - s) := mul_nonneg h0 (by linarith)
  constructor <;> linarith

theorem isArcMap_pieceA {a : 𝕀 → X} (ha : IsArcMap a) {s r : ℝ} (hs : 0 ≤ s) (hsr : s < r) (hr : r
  ≤ 1) :
    IsArcMap (pieceA a s r) := by
  refine ⟨(continuous_extI ha.1).comp (by fun_prop), fun u v he => ?_⟩
  have hu := mix_mem hs hsr.le hr u
  have hv := mix_mem hs hsr.le hr v
  simp only [pieceA, extI_of_mem a hu, extI_of_mem a hv] at he
  have h1 := congrArg Subtype.val (ha.2 he)
  have h2 : (u : ℝ) * (r - s) = v * (r - s) := by simpa using h1
  exact Subtype.ext (mul_right_cancel₀ (sub_pos.mpr hsr).ne' h2)

omit [TopologicalSpace X] in
theorem pieceA_zero (a : 𝕀 → X) (s r : ℝ) : pieceA a s r 0 = extI a s := by simp [pieceA]

omit [TopologicalSpace X] in
theorem pieceA_one (a : 𝕀 → X) (s r : ℝ) : pieceA a s r 1 = extI a r := by simp [pieceA]

omit [TopologicalSpace X] in
theorem range_pieceA (a : 𝕀 → X) {s r : ℝ} (_hs : 0 ≤ s) (hsr : s ≤ r) (hr : r ≤ 1) :
    range (pieceA a s r) = extI a '' Icc s r := by
  ext x
  constructor
  · rintro ⟨u, rfl⟩
    have h0 := u.2.1
    have h1 := u.2.2
    have h2 : (u : ℝ) * (r - s) ≤ 1 * (r - s) := mul_le_mul_of_nonneg_right h1 (by linarith)
    have h3 : 0 ≤ (u : ℝ) * (r - s) := mul_nonneg h0 (by linarith)
    exact ⟨_, ⟨by linarith, by linarith⟩, rfl⟩
  · rintro ⟨t, ⟨h1, h2⟩, rfl⟩
    rcases eq_or_lt_of_le hsr with rfl | hlt
    · have : t = s := le_antisymm h2 h1
      exact ⟨0, by simp [pieceA, this]⟩
    · have hd : 0 < r - s := sub_pos.mpr hlt
      refine ⟨⟨(t - s) / (r - s), div_nonneg (by linarith) hd.le, (div_le_one hd).mpr
        (by linarith)⟩, ?_⟩
      simp only [pieceA]
      congr 1
      field_simp
      ring

omit [TopologicalSpace X] in
theorem extI_injOn {a : 𝕀 → X} (ha : Function.Injective a) : InjOn (extI a) (Icc 0 1) := by
  intro s hs r hr he
  rw [extI_of_mem a hs, extI_of_mem a hr] at he
  exact congrArg Subtype.val (ha he)

/-- A line is split in two by a point that is not an end. -/
theorem IsLineWithEnds.split [T2Space X] {L : Set X} {u v x : X} (h : IsLineWithEnds L u v)
  (hx : x ∈ L)
    (hu : x ≠ u) (hv : x ≠ v) :
    ∃ L₁ L₂ : Set X, IsLineWithEnds L₁ u x ∧ IsLineWithEnds L₂ x v ∧ L₁ ∪ L₂ = L ∧ L₁ ∩ L₂ = {x}
      := by
  obtain ⟨a, ha, rfl, rfl, rfl⟩ := h.exists_arc
  obtain ⟨t, rfl⟩ := hx
  have h0 : (0 : ℝ) < t := lt_of_le_of_ne t.2.1 fun he => hu (congrArg a (Subtype.ext he.symm))
  have h1 : (t : ℝ) < 1 := lt_of_le_of_ne t.2.2 fun he => hv (congrArg a (Subtype.ext he))
  have a1 := isArcMap_pieceA ha le_rfl h0 h1.le
  have a2 := isArcMap_pieceA ha h0.le h1 le_rfl
  have e1 : extI a 0 = a 0 := extI_coe a 0
  have e2 : extI a 1 = a 1 := extI_coe a 1
  have e3 : extI a t = a t := extI_coe a t
  refine ⟨range (pieceA a 0 t), range (pieceA a t 1), ?_, ?_, ?_, ?_⟩
  · have := a1.isLineWithEnds
    rwa [pieceA_zero, pieceA_one, e1, e3] at this
  · have := a2.isLineWithEnds
    rwa [pieceA_zero, pieceA_one, e2, e3] at this
  · rw [range_pieceA a le_rfl h0.le h1.le, range_pieceA a h0.le h1.le le_rfl, ← image_union,
      Icc_union_Icc_eq_Icc h0.le h1.le]
    ext y
    constructor
    · rintro ⟨r, hr, rfl⟩
      exact ⟨⟨r, hr⟩, (extI_of_mem a hr).symm⟩
    · rintro ⟨r, rfl⟩
      exact ⟨r, r.2, extI_coe a r⟩
  · rw [range_pieceA a le_rfl h0.le h1.le, range_pieceA a h0.le h1.le le_rfl]
    ext y
    constructor
    · rintro ⟨⟨r, hr, rfl⟩, ⟨r', hr', he⟩⟩
      have h2 : r' = r := extI_injOn ha.2 ⟨h0.le.trans hr'.1, hr'.2⟩ ⟨hr.1, hr.2.trans h1.le⟩ he
      have h3 : r = t := le_antisymm hr.2 (h2 ▸ hr'.1)
      rw [h3]
      exact e3
    · rintro rfl
      exact ⟨⟨t, ⟨h0.le, le_rfl⟩, e3⟩, ⟨t, ⟨le_rfl, h1.le⟩, e3⟩⟩

theorem IsLineWithEnds.symm {L : Set X} {u v : X} (h : IsLineWithEnds L u v) : IsLineWithEnds L v u
  := by
  obtain ⟨f, h0, h1⟩ := h
  refine ⟨unitInterval.symmHomeomorph.trans f, ?_, ?_⟩ <;> simp [h0, h1]

/-- Two lines with one common point, an end of both, form a line. -/
theorem IsLineWithEnds.union [T2Space X] {L₁ L₂ : Set X} {u x v : X} (h₁ : IsLineWithEnds L₁ u x)
    (h₂ : IsLineWithEnds L₂ x v) (hi : L₁ ∩ L₂ = {x}) : IsLineWithEnds (L₁ ∪ L₂) u v := by
  obtain ⟨a, ha, rfl, rfl, e1⟩ := h₁.exists_arc
  obtain ⟨b, hb, rfl, e2, rfl⟩ := h₂.exists_arc
  let c : ℝ → X := fun t => if t ≤ 1 / 2 then extI a (2 * t) else extI b (2 * t - 1)
  have hc : Continuous c := by
    refine Continuous.if_le ((continuous_extI ha.1).comp (by fun_prop))
      ((continuous_extI hb.1).comp (by fun_prop)) continuous_id continuous_const fun t ht => ?_
    have : t = 1 / 2 := ht
    subst this
    norm_num
    have e3 : extI a 1 = a 1 := extI_coe a 1
    have e4 : extI b 0 = b 0 := extI_coe b 0
    rw [e3, e4, e1, e2]
  have hle : ∀ t : 𝕀, (t : ℝ) ≤ 1 / 2 → 2 * (t : ℝ) ∈ Icc (0 : ℝ) 1 := fun t h =>
    ⟨by linarith [t.2.1], by linarith⟩
  have hge : ∀ t : 𝕀, ¬ (t : ℝ) ≤ 1 / 2 → 2 * (t : ℝ) - 1 ∈ Icc (0 : ℝ) 1 := fun t h => by
    push Not at h
    exact ⟨by linarith, by linarith [t.2.2]⟩
  let e : 𝕀 → X := fun t => c t
  have hval : ∀ {y : X}, y ∈ range a → y ∈ range b → y = a 1 := fun {y} h1 h2 => by
    have : y ∈ range a ∩ range b := ⟨h1, h2⟩
    rw [hi] at this
    exact (mem_singleton_iff.mp this).trans e1.symm
  have hinj : Function.Injective e := by
    intro s t he
    simp only [e, c] at he
    by_cases h1 : (s : ℝ) ≤ 1 / 2 <;> by_cases h2 : (t : ℝ) ≤ 1 / 2
    · rw [ite_eq_left h1, ite_eq_left h2, extI_of_mem a (hle s h1), extI_of_mem a (hle t h2)] at he
      have := congrArg Subtype.val (ha.2 he)
      exact Subtype.ext (by simpa using this)
    · rw [ite_eq_left h1, ite_eq_right h2, extI_of_mem a (hle s h1), extI_of_mem b (hge t h2)] at he
      have e5 := hval ⟨_, rfl⟩ ⟨_, he.symm⟩
      have e6 := ha.2 e5
      have e7 := hb.2 (he.symm.trans (e5.trans (e1.trans e2.symm)))
      have e8 := congrArg Subtype.val e6
      have e9 := congrArg Subtype.val e7
      simp at e8 e9
      push Not at h2
      linarith
    · rw [ite_eq_right h1, ite_eq_left h2, extI_of_mem b (hge s h1), extI_of_mem a (hle t h2)] at he
      have e5 := hval ⟨_, rfl⟩ ⟨_, he⟩
      have e6 := ha.2 e5
      have e7 := hb.2 (he.trans (e5.trans (e1.trans e2.symm)))
      have e8 := congrArg Subtype.val e6
      have e9 := congrArg Subtype.val e7
      simp at e8 e9
      push Not at h1
      linarith
    · rw [ite_eq_right h1, ite_eq_right h2, extI_of_mem b (hge s h1), extI_of_mem b
      (hge t h2)] at he
      have := congrArg Subtype.val (hb.2 he)
      exact Subtype.ext (by simpa using this)
  have he : IsArcMap e := ⟨hc.comp continuous_subtype_val, hinj⟩
  have hr : range e = range a ∪ range b := by
    ext y
    constructor
    · rintro ⟨t, rfl⟩
      simp only [e, c]
      by_cases h1 : (t : ℝ) ≤ 1 / 2
      · rw [ite_eq_left h1, extI_of_mem a (hle t h1)]
        exact .inl ⟨_, rfl⟩
      · rw [ite_eq_right h1, extI_of_mem b (hge t h1)]
        exact .inr ⟨_, rfl⟩
    · rintro (⟨t, rfl⟩ | ⟨t, rfl⟩)
      · have hm : (t : ℝ) / 2 ∈ Icc (0 : ℝ) 1 := ⟨by linarith [t.2.1], by linarith [t.2.2]⟩
        refine ⟨⟨_, hm⟩, ?_⟩
        have h1 : (t : ℝ) / 2 ≤ 1 / 2 := by linarith [t.2.2]
        simp only [e, c, ite_eq_left h1]
        rw [show 2 * ((t : ℝ) / 2) = t by ring]
        exact extI_coe a t
      · by_cases ht : (t : ℝ) = 0
        · have ht' : t = 0 := Subtype.ext ht
          refine ⟨⟨1 / 2, by norm_num, by norm_num⟩, ?_⟩
          simp only [e, c]
          rw [ite_eq_left le_rfl, ht']
          norm_num
          exact (extI_coe a 1).trans (e1.trans e2.symm)
        · have hm : ((t : ℝ) + 1) / 2 ∈ Icc (0 : ℝ) 1 := ⟨by linarith [t.2.1], by linarith [t.2.2]⟩
          refine ⟨⟨_, hm⟩, ?_⟩
          have h1 : ¬ ((t : ℝ) + 1) / 2 ≤ 1 / 2 := by
            have := lt_of_le_of_ne t.2.1 (Ne.symm ht)
            linarith
          simp only [e, c, ite_eq_right h1]
          rw [show 2 * (((t : ℝ) + 1) / 2) - 1 = t by ring]
          exact extI_coe b t
  have hl := he.isLineWithEnds
  rw [hr] at hl
  have h0 : e 0 = a 0 := by
    simp only [e, c]
    rw [ite_eq_left (by norm_num)]
    simpa using extI_coe a 0
  have h1 : e 1 = b 1 := by
    simp only [e, c]
    rw [ite_eq_right (by norm_num)]
    norm_num
    exact extI_coe b 1
  rwa [h0, h1] at hl

end GraphMinor.Surface
