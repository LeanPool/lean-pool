/-
Copyright (c) 2026 DICTO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DICTO
-/

/- Modified for Lean Pool. -/

module

public import LeanPool.DehnInvariant.Dissection
public import LeanPool.DehnInvariant.EuclideanSpace
public import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
public import Mathlib.Analysis.Convex.Measure
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-! Volume under dissection and reflection, and the three-dimensional ℓ¹ ball. -/

@[expose] public section

open scoped RealInnerProductSpace Real Pointwise
open Set MeasureTheory Measure Module

namespace DehnCanon.Library

/-! ### Scissors congruence keeps volume -/

lemma vol_eq_of_sub_null {X : Type*} [MeasurableSpace X] {μ : Measure X} {s t z : Set X}
    (h1 : s ⊆ t) (h2 : t ⊆ s ∪ z) (hz : μ z = 0) : μ s = μ t :=
  measure_eq_of_off_null hz (h1.trans subset_union_left) h2

/-- **Volume is additive over a dissection into convex polytopes** (pairwise disjoint interiors). -/
theorem volume_iUnion_poly {κ : Type} [Fintype κ] {p : κ → Set R3} (hp : ∀ k, IsPoly (p k))
    (hd : Pairwise fun i j => Disjoint (interior (p i)) (interior (p j))) :
    volume (⋃ k, p k) = ∑ k, volume (p k) := by
  have hfr : ∀ k, volume (frontier (p k)) = 0 := fun k => Convex.addHaar_frontier volume (hp
      k).convex
  have hsub : ∀ k, p k ⊆ interior (p k) ∪ frontier (p k) := fun k =>
    subset_closure.trans (closure_eq_interior_union_frontier (p k)).subset
  have hint : ∀ k, volume (interior (p k)) = volume (p k) := fun k =>
    vol_eq_of_sub_null interior_subset (hsub k) (hfr k)
  have hU : volume (⋃ k, interior (p k)) = ∑ k, volume (interior (p k)) := by
    rw [measure_iUnion (fun i j hij => hd hij) (fun k => isOpen_interior.measurableSet),
        tsum_fintype]
  rw [← vol_eq_of_sub_null (iUnion_mono fun k => interior_subset)
    (t := ⋃ k, p k) (z := ⋃ k, frontier (p k)) ?_ (measure_iUnion_null hfr), hU]
  · exact Finset.sum_congr rfl fun k _ => hint k
  · intro x hx
    obtain ⟨k, hk⟩ := mem_iUnion.1 hx
    rcases hsub k hk with h | h
    · exact Or.inl (mem_iUnion.2 ⟨k, h⟩)
    · exact Or.inr (mem_iUnion.2 ⟨k, h⟩)

/-- An isometry of 3-space keeps volume. -/
lemma volume_image_isometry (g : R3 ≃ᵃⁱ[ℝ] R3) (s : Set R3) : volume (g '' s) = volume s := by
  set L := g.linearIsometryEquiv
  have hg : ∀ x, g x = L x + g 0 := by
    intro x
    have := g.map_vadd (0 : R3) x
    rw [vadd_eq_add, vadd_eq_add, add_zero] at this
    exact this
  have himg : g '' s = (fun y => y + g 0) '' (L '' s) := by
    rw [Set.image_image]; exact Set.image_congr (fun x _ => hg x)
  rw [himg, Set.image_add_right, measure_preimage_add_right, L.image_eq_preimage_symm]
  exact (L.symm.measurePreserving).measure_preimage_equiv (f := L.symm.toMeasurableEquiv) s

/-- **Scissors-congruent sets have the same volume.** -/
theorem volume_eq_of_scissorsCongruent {P Q : Set R3} (h : ScissorsCongruent P Q) :
    volume P = volume Q := by
  obtain ⟨κ, _, p, g, hp, hUP, hdP, hUQ, hdQ⟩ := h
  rw [← hUP, ← hUQ, volume_iUnion_poly hp hdP,
    volume_iUnion_poly (fun k => (hp k).image (g k)) hdQ]
  exact Finset.sum_congr rfl fun k _ => (volume_image_isometry (g k) (p k)).symm

/-- A copy scaled by `a > 0` and moved by an isometry has `a³` times the volume. -/
lemma volume_similar {a : ℝ} (ha : 0 < a) (g : R3 ≃ᵃⁱ[ℝ] R3) (P : Set R3) :
    volume (g '' (a • P)) = ENNReal.ofReal (a ^ 3) * volume P := by
  rw [volume_image_isometry, Measure.addHaar_smul, finrank_euclideanSpace_fin,
    abs_of_pos (pow_pos ha 3)]

/-! ### Volumes in `Fin 3 → ℝ` -/

/-- The sum norm |y₀| + |y₁| + |y₂|. -/
def l1 (y : Fin 3 → ℝ) : ℝ := |y 0| + |y 1| + |y 2|

lemma continuous_l1 : Continuous l1 := by unfold l1; fun_prop

lemma plane_null (i : Fin 3) (c : ℝ) : volume {y : Fin 3 → ℝ | y i = c} = 0 := by
  rw [volume_pi]; exact Measure.pi_hyperplane (fun _ : Fin 3 => (volume : Measure ℝ)) i c

lemma l1_rpow (y : Fin 3 → ℝ) : (∑ i, |y i| ^ (1 : ℝ)) ^ (1 / (1 : ℝ)) = l1 y := by
  simp [Real.rpow_one, Fin.sum_univ_three, l1]

lemma gamma_four : Real.Gamma 4 = 6 := by
  rw [show (4 : ℝ) = ((3 : ℕ) : ℝ) + 1 by norm_num, Real.Gamma_nat_eq_factorial]
  norm_num [Nat.factorial]

/-- The closed ball of the sum norm: (4/3) r³ (Mathlib's ℓᵖ ball with p = 1). -/
lemma vol_l1_le {r : ℝ} (hr : 0 ≤ r) :
    volume {y : Fin 3 → ℝ | l1 y ≤ r} = ENNReal.ofReal (4 / 3 * r ^ 3) := by
  have h := MeasureTheory.volume_sum_rpow_le (Fin 3) (p := 1) le_rfl r
  simp only [l1_rpow, Fintype.card_fin] at h
  rw [h, ← ENNReal.ofReal_pow hr, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  norm_num [Real.Gamma_two, gamma_four]
  ring

/-- The open ball of the sum norm: (4/3) r³. -/
lemma vol_l1_lt {r : ℝ} (hr : 0 ≤ r) :
    volume {y : Fin 3 → ℝ | l1 y < r} = ENNReal.ofReal (4 / 3 * r ^ 3) := by
  have h := MeasureTheory.volume_sum_rpow_lt (Fin 3) (p := 1) le_rfl r
  simp only [l1_rpow, Fintype.card_fin] at h
  rw [h, ← ENNReal.ofReal_pow hr, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  norm_num [Real.Gamma_two, gamma_four]
  ring

/-- Reflection in the coordinate plane `y i = 0`. -/
def refl (i : Fin 3) (y : Fin 3 → ℝ) : Fin 3 → ℝ := fun j => if j = i then -y j else y j

lemma mp_refl (i : Fin 3) : MeasurePreserving (refl i) := by
  have h := measurePreserving_pi (fun _ : Fin 3 => (volume : Measure ℝ)) (fun _ => volume)
    (f := fun j => if j = i then (Neg.neg : ℝ → ℝ) else id)
    (fun j => by
      split_ifs
      · exact Measure.measurePreserving_neg _
      · exact MeasurePreserving.id _)
  have he : refl i = fun a j => (if j = i then (Neg.neg : ℝ → ℝ) else id) (a j) := by
    funext y j; unfold refl; split_ifs <;> rfl
  rw [he, volume_pi]; exact h

/-- **Half by symmetry.** A measurable set symmetric in the coordinate `i` has half its volume where
`y i > 0`. -/
lemma vol_half (i : Fin 3) {S : Set (Fin 3 → ℝ)} (hS : MeasurableSet S)
    (hinv : ∀ y, refl i y ∈ S ↔ y ∈ S) :
    2 * volume (S ∩ {y | 0 < y i}) = volume S := by
  have hm : MeasurableSet {y : Fin 3 → ℝ | 0 < y i} :=
    measurableSet_lt measurable_const (measurable_pi_apply i)
  have h1 := measure_inter_add_sdiff (μ := volume) S hm
  have hneg : refl i ⁻¹' (S ∩ {y | 0 < y i}) = S ∩ {y | y i < 0} := by
    ext y; simp [refl, hinv]
  have h2 : volume (S ∩ {y | y i < 0}) = volume (S ∩ {y | 0 < y i}) := by
    rw [← hneg]; exact (mp_refl i).measure_preimage (hS.inter hm).nullMeasurableSet
  have h3 : volume (S ∩ {y | y i < 0}) = volume (S \ {y | 0 < y i}) := by
    apply vol_eq_of_sub_null (z := {y | y i = 0})
    · intro y hy
      simp only [mem_inter_iff, mem_sdiff, mem_ofPred_eq] at hy ⊢
      exact ⟨hy.1, fun h => lt_asymm hy.2 h⟩
    · intro y hy
      simp only [mem_sdiff, mem_ofPred_eq, not_lt] at hy
      rcases lt_or_eq_of_le hy.2 with h | h
      · exact Or.inl ⟨hy.1, h⟩
      · exact Or.inr h
    · exact plane_null i 0
  rw [← h1, ← h3, h2, two_mul]

lemma l1_refl (i : Fin 3) (y : Fin 3 → ℝ) : l1 (refl i y) = l1 y := by
  fin_cases i <;> simp [l1, refl]

lemma refl_apply_ne {i j : Fin 3} (h : j ≠ i) (y : Fin 3 → ℝ) : refl i y j = y j := by
  simp [refl, h]

lemma refl_apply_self (i : Fin 3) (y : Fin 3 → ℝ) : refl i y i = -y i := by
  simp [refl]

lemma ennreal_half {x : ENNReal} {c : ℝ} (h : 2 * x = ENNReal.ofReal (2 * c)) :
    x = ENNReal.ofReal c := by
  rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat] at h
  exact (ENNReal.mul_right_inj (by norm_num) (by norm_num)).1 h

end DehnCanon.Library
