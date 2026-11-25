/-
Copyright (c) 2026 DICTO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DICTO
-/

/- Modified for Lean Pool. -/

module

public import LeanPool.DehnInvariant.TensorInvariant
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.MeasureTheory.Measure.Basic

/-!
Lean study 2 of the shape-language canon (DICTO, 19 Nov 2026), part C: adding up a finitely-valued
angle
function against a measure, with values in ℝ ⊗[ℚ] (ℝ/ℚπ).

`tsum1 μ f = Σ over angle classes θ of μ{f = θ} ⊗ θ`.  Main result `tsum1_add`: if `f` and `g` are
constant on
the finitely many measurable classes of a classifier, are nonzero only on a set of finite measure,
and
`h = f + g` off a null set, then `tsum1 μ h = tsum1 μ f + tsum1 μ g`.
No `sorry`.
-/

@[expose] public section

open Set MeasureTheory TensorProduct

namespace DehnCanon.Library

/-- Σ over angle classes θ of (measure of the set where `f = θ`) ⊗ θ. -/
noncomputable def tsum1 {X : Type*} [MeasurableSpace X] (μ : Measure X) (f : X → Angle)
    : DehnSpace :=
  ∑ᶠ θ : Angle, (μ {x | f x = θ}).toReal ⊗ₜ[ℚ] θ

lemma tsum1_eq_sum {X : Type*} [MeasurableSpace X] (μ : Measure X) {κ : Type*} [Fintype κ] (c : X
    → κ)
    (hc : ∀ k, MeasurableSet (c ⁻¹' {k})) (φ : κ → Angle)
    (hfin : ∀ k, φ k ≠ 0 → μ (c ⁻¹' {k}) ≠ ⊤) :
    tsum1 μ (φ ∘ c) = ∑ k, (μ (c ⁻¹' {k})).toReal ⊗ₜ[ℚ] φ k := by
  classical
  unfold tsum1
  have hterm : ∀ θ : Angle, (μ {x | (φ ∘ c) x = θ}).toReal ⊗ₜ[ℚ] θ
      = ∑ k ∈ Finset.univ.filter (fun k => φ k = θ), (μ (c ⁻¹' {k})).toReal ⊗ₜ[ℚ] φ k := by
    intro θ
    by_cases hθ : θ = 0
    · subst hθ
      rw [TensorProduct.tmul_zero]
      symm; apply Finset.sum_eq_zero; intro k hk
      rw [(Finset.mem_filter.1 hk).2, TensorProduct.tmul_zero]
    · have hset : {x | (φ ∘ c) x = θ} = ⋃ k ∈ Finset.univ.filter (fun k => φ k = θ), c ⁻¹' {k} := by
        ext x
        simp only [mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and, mem_preimage,
          mem_singleton_iff, exists_prop]
        constructor
        · intro h; exact ⟨c x, h, rfl⟩
        · rintro ⟨k, hk, rfl⟩; exact hk
      have hd : (↑(Finset.univ.filter fun k => φ k = θ) : Set κ).PairwiseDisjoint
          (fun k => c ⁻¹' {k}) := by
        intro i _ j _ hij
        exact Disjoint.preimage c (Set.disjoint_singleton.2 hij)
      have hm := measure_biUnion_finset (μ := μ) hd (fun k _ => hc k)
      have hne : ∀ k ∈ Finset.univ.filter (fun k => φ k = θ), μ (c ⁻¹' {k}) ≠ ⊤ := by
        intro k hk; exact hfin k (by rw [(Finset.mem_filter.1 hk).2]; exact hθ)
      rw [hset, hm, ENNReal.toReal_sum hne, TensorProduct.sum_tmul]
      apply Finset.sum_congr rfl; intro k hk; rw [(Finset.mem_filter.1 hk).2]
  rw [finsum_congr hterm]
  rw [finsum_eq_sum_of_support_subset (s := Finset.univ.image φ)]
  · exact Finset.sum_fiberwise_of_maps_to
      (fun k _ => Finset.mem_image_of_mem φ (Finset.mem_univ k)) _
  · intro θ hθ
    rw [Function.mem_support] at hθ
    by_contra hnot
    apply hθ
    apply Finset.sum_eq_zero
    intro k hk
    exact absurd (Finset.mem_coe.2 (Finset.mem_image.2
      ⟨k, Finset.mem_univ k, (Finset.mem_filter.1 hk).2⟩)) hnot

lemma measure_eq_of_off_null {X : Type*} [MeasurableSpace X] {μ : Measure X} {s t Z : Set X}
    (hZ : μ Z = 0) (h1 : s ⊆ t ∪ Z) (h2 : t ⊆ s ∪ Z) : μ s = μ t := by
  apply le_antisymm
  · calc μ s ≤ μ (t ∪ Z) := measure_mono h1
      _ ≤ μ t + μ Z := measure_union_le _ _
      _ = μ t := by rw [hZ, add_zero]
  · calc μ t ≤ μ (s ∪ Z) := measure_mono h2
      _ ≤ μ s + μ Z := measure_union_le _ _
      _ = μ s := by rw [hZ, add_zero]

/-- Additivity of `tsum1` for functions that are constant on the classes of a finite measurable
classifier. -/
theorem tsum1_add {X : Type*} [MeasurableSpace X] (μ : Measure X) {κ : Type*} [Finite κ] (c : X
    → κ)
    (hc : ∀ k, MeasurableSet (c ⁻¹' {k})) (f g h : X → Angle)
    (hf : ∀ x y, c x = c y → f x = f y) (hg : ∀ x y, c x = c y → g x = g y)
    (hff : μ {x | f x ≠ 0} ≠ ⊤) (hgf : μ {x | g x ≠ 0} ≠ ⊤)
    (hZ : μ {x | h x ≠ f x + g x} = 0) :
    tsum1 μ h = tsum1 μ f + tsum1 μ g := by
  classical
  let := Fintype.ofFinite κ
  let rep : κ → Option X := fun k => if hk : ∃ x, c x = k then some (Classical.choose hk) else none
  let φ : (X → Angle) → κ → Angle := fun F k => (rep k).elim 0 F
  have hrep : ∀ F : X → Angle, (∀ x y, c x = c y → F x = F y) → F = φ F ∘ c := by
    intro F hF; funext x
    have hk : ∃ y, c y = c x := ⟨x, rfl⟩
    have h1 : rep (c x) = some (Classical.choose hk) := dite_eq_left hk
    change F x = (rep (c x)).elim 0 F
    rw [h1]
    exact hF _ _ (Classical.choose_spec hk).symm
  have hfin : ∀ F : X → Angle, (∀ x y, c x = c y → F x = F y) → μ {x | F x ≠ 0} ≠ ⊤ →
      ∀ k, φ F k ≠ 0 → μ (c ⁻¹' {k}) ≠ ⊤ := by
    intro F hF hFf k hk
    refine ((measure_mono ?_).trans_lt hFf.lt_top).ne
    intro x hx
    have hx' : c x = k := hx
    change F x ≠ 0
    have h2 := congrFun (hrep F hF) x
    rw [h2]
    change φ F (c x) ≠ 0
    rw [hx']; exact hk
  have hfg : ∀ x y, c x = c y → (f + g) x = (f + g) y := fun x y hxy => by
    change f x + g x = f y + g y
    rw [hf x y hxy, hg x y hxy]
  have hfgf : μ {x | (f + g) x ≠ 0} ≠ ⊤ := by
    refine ((measure_mono ?_).trans_lt (measure_union_lt_top hff.lt_top hgf.lt_top)).ne
    intro x hx
    by_contra hno
    have h1 : ¬ (f x ≠ 0) := fun h => hno (Or.inl h)
    have h2 : ¬ (g x ≠ 0) := fun h => hno (Or.inr h)
    apply hx
    change f x + g x = 0
    rw [not_not.1 h1, not_not.1 h2, add_zero]
  have hh : tsum1 μ h = tsum1 μ (f + g) := by
    unfold tsum1
    apply finsum_congr; intro θ
    congr 2
    apply measure_eq_of_off_null hZ
    · intro x hx
      by_cases hxz : h x = f x + g x
      · left; change (f + g) x = θ; rw [← hx]; exact hxz.symm
      · right; exact hxz
    · intro x hx
      by_cases hxz : h x = f x + g x
      · left; change h x = θ; rw [hxz]; exact hx
      · right; exact hxz
  have e1 : tsum1 μ f = ∑ k, (μ (c ⁻¹' {k})).toReal ⊗ₜ[ℚ] φ f k :=
    (congrArg (tsum1 μ) (hrep f hf)).trans (tsum1_eq_sum μ c hc (φ f) (hfin f hf hff))
  have e2 : tsum1 μ g = ∑ k, (μ (c ⁻¹' {k})).toReal ⊗ₜ[ℚ] φ g k :=
    (congrArg (tsum1 μ) (hrep g hg)).trans (tsum1_eq_sum μ c hc (φ g) (hfin g hg hgf))
  have e3 : tsum1 μ (f + g) = ∑ k, (μ (c ⁻¹' {k})).toReal ⊗ₜ[ℚ] φ (f + g) k :=
    (congrArg (tsum1 μ) (hrep (f + g) hfg)).trans
      (tsum1_eq_sum μ c hc (φ (f + g)) (hfin (f + g) hfg hfgf))
  have hφ : ∀ k, φ (f + g) k = φ f k + φ g k := by
    intro k
    change (rep k).elim 0 (f + g) = (rep k).elim 0 f + (rep k).elim 0 g
    cases rep k with
    | none => simp
    | some x => simp
  rw [hh, e1, e2, e3, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro k _
  rw [hφ, TensorProduct.tmul_add]

end DehnCanon.Library
