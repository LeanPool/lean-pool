/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson
-/

module

public import LeanPool.ScottMeasurement.Preference.Direct
public import Mathlib.Tactic.FieldSimp

/-!
# Scott's intransitive-indifference problem

The definitions reproduce conditions `(1_P)`--`(3_P)` in §2.  The elementary
direction of Theorem 2.1 is recorded here; the converse is supplied by the
finite linear-inequality engine.
-/

@[expose] public section

namespace Scott1964.MeasurementStructures

/-- A strict preference relation is represented with discrimination threshold `1`. -/
def RealizablePreference {A : Type u} (P : A → A → Prop) : Prop :=
  ∃ f : A → ℝ, ∀ x y, P x y ↔ f x ≥ f y + 1

/-- Scott 1964, condition `(1_P)`. -/
def PrefIrrefl {A : Type u} (P : A → A → Prop) : Prop :=
  ∀ x, ¬P x x

/-- Scott 1964, condition `(2_P)`. -/
def PrefQuadA {A : Type u} (P : A → A → Prop) : Prop :=
  ∀ x y z w, P x y → P z w → P x w ∨ P z y

/-- Scott 1964, condition `(3_P)`. -/
def PrefQuadB {A : Type u} (P : A → A → Prop) : Prop :=
  ∀ x y z w, P x y → P z x → P w y ∨ P z w

/-- Realization with a strict margin above the conventional unit threshold. -/
def RealizablePreferenceWithGap {A : Type u} (P : A → A → Prop) : Prop :=
  ∃ f : A → ℝ, ∃ ε > 0, ∀ x y, P x y ↔ f x ≥ f y + 1 + ε

/-- Scott's stronger conclusion following Theorem 2.1: the same unit
threshold may be taken strict on every preferred pair. -/
def StrictlyRealizablePreference {A : Type u} (P : A → A → Prop) : Prop :=
  ∃ f : A → ℝ, ∀ x y, P x y ↔ f x > f y + 1

theorem RealizablePreference.irrefl {A : Type u} {P : A → A → Prop}
    (hP : RealizablePreference P) : PrefIrrefl P := by
  rcases hP with ⟨f, hf⟩
  intro x hxx
  have := (hf x x).1 hxx
  linarith

theorem RealizablePreference.quadA {A : Type u} {P : A → A → Prop}
    (hP : RealizablePreference P) : PrefQuadA P := by
  rcases hP with ⟨f, hf⟩
  intro x y z w hxy hzw
  rw [hf] at hxy hzw
  by_cases hxw : f w + 1 ≤ f x
  · exact Or.inl ((hf x w).2 hxw)
  · apply Or.inr
    apply (hf z y).2
    have hlt : f x < f w + 1 := lt_of_not_ge hxw
    linarith

theorem RealizablePreference.quadB {A : Type u} {P : A → A → Prop}
    (hP : RealizablePreference P) : PrefQuadB P := by
  rcases hP with ⟨f, hf⟩
  intro x y z w hxy hzx
  rw [hf] at hxy hzx
  by_cases hwy : f y + 1 ≤ f w
  · exact Or.inl ((hf w y).2 hwy)
  · apply Or.inr
    apply (hf z w).2
    have hlt : f w < f y + 1 := lt_of_not_ge hwy
    linarith

theorem RealizablePreference.necessary {A : Type u} {P : A → A → Prop}
    (hP : RealizablePreference P) :
    PrefIrrefl P ∧ PrefQuadA P ∧ PrefQuadB P :=
  ⟨hP.irrefl, hP.quadA, hP.quadB⟩

/-- **Scott 1964, Theorem 2.1 (intransitive indifference).**

The nonemptiness assumption in the source is unnecessary here.
The converse uses the direct finite Scott--Suppes construction: quotient by
substitutability, order the quotient by the weak order `ScottWeakOrder`, and
represent its nested lower sections by a recursively constructed sequence. -/
theorem theorem_2_1 {A : Type u} [Finite A] (P : A → A → Prop) :
    RealizablePreference P ↔ PrefIrrefl P ∧ PrefQuadA P ∧ PrefQuadB P := by
  let := Fintype.ofFinite A
  constructor
  · exact RealizablePreference.necessary
  · rintro ⟨hirr, hA, hB⟩
    classical
    let : Preorder A :=
      {
      le x y := ScottWeakOrder P y x
      le_refl x := scottWeakOrder_refl P x
      le_trans x y z hxy hyz := (scottWeakOrder_trans P).trans z y x hyz hxy
      lt x y := ScottWeakOrder P y x ∧ ¬ScottWeakOrder P x y
      lt_iff_le_not_ge _ _ := Iff.rfl
      }
    let : Std.Total (α := A) (· ≤ ·) :=
      ⟨fun x y ↦ scottWeakOrder_total P hA hB y x⟩
    let Q := Antisymmetrization A (· ≤ ·)
    let : Finite Q :=
      Finite.of_surjective (toAntisymmetrization (α := A) (· ≤ ·))
        (fun q ↦ ⟨ofAntisymmetrization (· ≤ ·) q,
          toAntisymmetrization_ofAntisymmetrization (· ≤ ·) q⟩)
    let : Fintype Q := Fintype.ofFinite Q
    let PQ : Q → Q → Prop :=
      fun x y ↦ P (ofAntisymmetrization (· ≤ ·) x)
        (ofAntisymmetrization (· ≤ ·) y)
    have hPQ_forward {x y : Q} (hxy : PQ x y) : y < x := by
      let ox := ofAntisymmetrization (· ≤ ·) x
      let oy := ofAntisymmetrization (· ≤ ·) y
      have hle : y ≤ x := by
        rw [← toAntisymmetrization_ofAntisymmetrization (· ≤ ·) y,
          ← toAntisymmetrization_ofAntisymmetrization (· ≤ ·) x,
          toAntisymmetrization_le_toAntisymmetrization_iff]
        exact preference_implies_scottWeakOrder P hirr hA hxy
      refine lt_of_le_of_ne hle ?_
      intro heq
      have hback : ScottWeakOrder P oy ox := by
        have : x ≤ y := heq.ge
        rw [← toAntisymmetrization_ofAntisymmetrization (· ≤ ·) x,
          ← toAntisymmetrization_ofAntisymmetrization (· ≤ ·) y,
          toAntisymmetrization_le_toAntisymmetrization_iff] at this
        exact this
      exact hirr ox (hback.1 ox hxy)
    have hPQ_mono {x x' y y' : Q} (hxx' : x ≤ x') (hyy' : y' ≤ y)
        (hxy : PQ x y) : PQ x' y' := by
      have hx :
          ScottWeakOrder P (ofAntisymmetrization (· ≤ ·) x')
            (ofAntisymmetrization (· ≤ ·) x) := by
        have hq :
            toAntisymmetrization (· ≤ ·)
                (ofAntisymmetrization (· ≤ ·) x) ≤
              toAntisymmetrization (· ≤ ·)
                (ofAntisymmetrization (· ≤ ·) x') := by
          simpa only [toAntisymmetrization_ofAntisymmetrization] using hxx'
        change ScottWeakOrder P
          (ofAntisymmetrization (· ≤ ·) x')
          (ofAntisymmetrization (· ≤ ·) x) at hq
        exact hq
      have hy :
          ScottWeakOrder P (ofAntisymmetrization (· ≤ ·) y)
            (ofAntisymmetrization (· ≤ ·) y') := by
        have hq :
            toAntisymmetrization (· ≤ ·)
                (ofAntisymmetrization (· ≤ ·) y') ≤
              toAntisymmetrization (· ≤ ·)
                (ofAntisymmetrization (· ≤ ·) y) := by
          simpa only [toAntisymmetrization_ofAntisymmetrization] using hyy'
        change ScottWeakOrder P
          (ofAntisymmetrization (· ≤ ·) y)
          (ofAntisymmetrization (· ≤ ·) y') at hq
        exact hq
      exact scottWeakOrder_preference_scottWeakOrder P hx hxy hy
    obtain ⟨g, hg, -⟩ :=
      finite_staircase_representation Q PQ hPQ_forward hPQ_mono
    refine ⟨fun x ↦ g (toAntisymmetrization (· ≤ ·) x), fun x y ↦ ?_⟩
    let ox := ofAntisymmetrization (· ≤ ·)
      (toAntisymmetrization (· ≤ ·) x)
    let oy := ofAntisymmetrization (· ≤ ·)
      (toAntisymmetrization (· ≤ ·) y)
    have hx :
        PreferenceSubstitute P x ox := by
      apply (preferenceSubstitute_iff P).2
      constructor
      · have h :
            toAntisymmetrization (· ≤ ·) ox ≤
              toAntisymmetrization (· ≤ ·) x := by
          simp [ox]
        exact h
      · have h :
            toAntisymmetrization (· ≤ ·) x ≤
              toAntisymmetrization (· ≤ ·) ox := by
          simp [ox]
        exact h
    have hy :
        PreferenceSubstitute P y oy := by
      apply (preferenceSubstitute_iff P).2
      constructor
      · have h :
            toAntisymmetrization (· ≤ ·) oy ≤
              toAntisymmetrization (· ≤ ·) y := by
          simp [oy]
        exact h
      · have h :
            toAntisymmetrization (· ≤ ·) y ≤
              toAntisymmetrization (· ≤ ·) oy := by
          simp [oy]
        exact h
    rw [show P x y ↔ P ox oy from (hy.1 x).trans (hx.2 oy)]
    exact hg _ _

/-- Any positive discrimination threshold can be changed to `1` by a change
of units, as noted immediately before §1. -/
theorem realizablePreference_threshold_iff {A : Type u} (P : A → A → Prop)
    {c : ℝ} (hc : 0 < c) :
    (∃ f : A → ℝ, ∀ x y, P x y ↔ f x ≥ f y + c) ↔
      RealizablePreference P := by
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨fun x ↦ f x / c, ?_⟩
    intro x y
    rw [hf]
    constructor <;> intro h
    · rw [show f y / c + 1 = (f y + c) / c by field_simp]
      exact (div_le_div_iff_of_pos_right hc).2 h
    · rw [show f y / c + 1 = (f y + c) / c by field_simp] at h
      exact (div_le_div_iff_of_pos_right hc).1 h
  · rintro ⟨f, hf⟩
    refine ⟨fun x ↦ c * f x, ?_⟩
    intro x y
    rw [hf]
    constructor <;> intro h
    · nlinarith
    · nlinarith

/-- Rescaling any unit-threshold realization produces an arbitrary positive
margin above the unit threshold. -/
theorem RealizablePreference.withGap {A : Type u} {P : A → A → Prop}
    (hP : RealizablePreference P) : RealizablePreferenceWithGap P := by
  rcases hP with ⟨f, hf⟩
  refine ⟨fun x ↦ 2 * f x, 1, by norm_num, ?_⟩
  intro x y
  rw [hf]
  constructor <;> intro h <;> nlinarith

theorem realizablePreferenceWithGap_iff {A : Type u} (P : A → A → Prop) :
    RealizablePreferenceWithGap P ↔ RealizablePreference P := by
  constructor
  · rintro ⟨f, ε, hε, hf⟩
    exact (realizablePreference_threshold_iff P (by linarith : 0 < 1 + ε)).mp
      ⟨f, by simpa [add_assoc] using hf⟩
  · exact RealizablePreference.withGap

/-- On a finite set the boundary can be avoided altogether, as Scott notes
after Theorem 2.1: preferred pairs lie strictly beyond the same unit
threshold. -/
theorem RealizablePreference.strict_of_finite {A : Type u} [Finite A] [Nonempty A]
    {P : A → A → Prop} (hP : RealizablePreference P) :
    StrictlyRealizablePreference P := by
  let := Fintype.ofFinite A
  classical
  rcases hP with ⟨f, hf⟩
  let values : Finset ℝ :=
    (Finset.univ ×ˢ Finset.univ).image fun p : A × A ↦
      if P p.1 p.2 then 0 else max 0 (f p.1 - f p.2)
  have hvalues : values.Nonempty := by
    let a : A := Classical.choice ‹Nonempty A›
    exact ⟨if P a a then 0 else max 0 (f a - f a),
      Finset.mem_image.mpr ⟨(a, a), by simp, rfl⟩⟩
  let M : ℝ := values.max' hvalues
  have hM_nonneg : 0 ≤ M := by
    obtain ⟨v, hv⟩ := hvalues
    have hv_nonneg : 0 ≤ v := by
      rcases Finset.mem_image.mp hv with ⟨p, -, rfl⟩
      split <;> simp
    exact hv_nonneg.trans (Finset.le_max' values v hv)
  have hM_lt_one : M < 1 := by
    apply (Finset.max'_lt_iff values hvalues).mpr
    intro v hv
    rcases Finset.mem_image.mp hv with ⟨p, -, rfl⟩
    split_ifs with hp
    · norm_num
    · have hlt : f p.1 - f p.2 < 1 := by
        have := not_le.mp (mt (hf p.1 p.2).mpr hp)
        linarith
      exact max_lt (by norm_num) hlt
  have hbound {x y : A} (hxy : ¬P x y) : f x - f y ≤ M := by
    have hmem : max 0 (f x - f y) ∈ values := by
      exact Finset.mem_image.mpr ⟨(x, y), by simp, by simp [hxy]⟩
    exact (le_max_right 0 (f x - f y)).trans (Finset.le_max' values _ hmem)
  let s : ℝ := 1 + (1 - M) / 2
  have hs : 1 < s := by
    dsimp [s]
    linarith
  refine ⟨fun x ↦ s * f x, fun x y ↦ ?_⟩
  constructor
  · intro hxy
    have hdiff : 1 ≤ f x - f y := by
      have := (hf x y).mp hxy
      linarith
    have hspos : 0 < s := lt_trans (by norm_num) hs
    have : s ≤ s * (f x - f y) := by nlinarith
    dsimp
    nlinarith
  · intro hstrict
    by_contra hxy
    have hd := hbound hxy
    have hdiff_lt : f x - f y < 1 := by
      have := not_le.mp (mt (hf x y).mpr hxy)
      linarith
    have hspos : 0 < s := lt_trans (by norm_num) hs
    have hscaled : s * (f x - f y) ≤ 1 := by
      by_cases hd0 : f x - f y ≤ 0
      · nlinarith
      · have hprod : s * (f x - f y) ≤ s * M :=
          mul_le_mul_of_nonneg_left hd hspos.le
        dsimp [s] at hprod ⊢
        nlinarith [mul_nonneg (sub_nonneg.mpr hM_nonneg)
          (sub_nonneg.mpr (le_of_lt hM_lt_one))]
    dsimp at hstrict
    nlinarith

end Scott1964.MeasurementStructures
