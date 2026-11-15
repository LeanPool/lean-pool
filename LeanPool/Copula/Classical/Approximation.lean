/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
module

import LeanPool.Copula.Classical.Regularity
public import LeanPool.Copula.Classical.Basic

/-! # Finite probability measures approximating classical copula data

Successive binary cuts produce finite atomic measures. Rectangle additivity
normalizes their weights, and clipping rectangles proves a uniform CDF error
bound in terms of the mesh width.
-/

public section

open MeasureTheory Set
open scoped unitInterval ENNReal BigOperators

namespace ProbabilityTheory.Copula

variable {d : ℕ} {F : (Fin d → I) → ℝ}

theorem IsClassical.rectangleIncrement_clip_le (hF : IsClassical F)
    (a b u : Fin d → I) (hab : a ≤ b) :
    rectangleIncrement F (a ⊓ u) (b ⊓ u) ≤ rectangleIncrement F a b := by
  by_cases ha : a ≤ u
  · rw [inf_eq_left.mpr ha]
    exact hF.rectangleIncrement_mono_upper a (b ⊓ u) b (le_inf hab ha) inf_le_left
  · obtain ⟨i, hi⟩ := not_forall.mp ha
    have hua : u i ≤ a i := (not_le.mp hi).le
    rw [rectangleIncrement_eq_zero_of_eq (a ⊓ u) (b ⊓ u) i (by
      change min (a i) (u i) = min (b i) (u i)
      rw [min_eq_right hua, min_eq_right (hua.trans (hab i))])]
    exact hF.increasing a b hab

namespace ClassicalConstruction

/-- A finite division built by cuts along coordinate hyperplanes. -/
inductive Division : (Fin d → I) → (Fin d → I) → Type
  | leaf {a b} (hab : a ≤ b) : Division a b
  | cut {a b} (i : Fin d) (t : I) (hat : a i ≤ t) (htb : t ≤ b i)
      (left : Division a (Function.update b i t))
      (right : Division (Function.update a i t) b) : Division a b

namespace Division

variable {a b : Fin d → I}

theorem ordered (D : Division a b) : a ≤ b := by
  induction D with
  | leaf hab => exact hab
  | @cut a b i t hat htb left right ihl ihr =>
    intro j
    by_cases hj : j = i
    · subst j; exact hat.trans htb
    · simpa only [Function.update_of_ne hj] using ihl j

/-- A property holding on every leaf of a division. -/
@[expose]
def All (P : (Fin d → I) → (Fin d → I) → Prop) :
    ∀ {a b : Fin d → I}, Division a b → Prop
  | a, b, .leaf _ => P a b
  | _, _, .cut _ _ _ _ left right => left.All P ∧ right.All P

theorem All.mono {P Q : (Fin d → I) → (Fin d → I) → Prop} {D : Division a b}
    (h : D.All P) (hPQ : ∀ a b, P a b → Q a b) : D.All Q := by
  induction D with
  | leaf hab => exact hPQ _ _ h
  | cut i t hat htb left right ihl ihr => exact ⟨ihl h.1, ihr h.2⟩

/-- Put each rectangle's weight at its upper corner. -/
@[expose]
noncomputable def measure (F : (Fin d → I) → ℝ) :
    ∀ {a b : Fin d → I}, Division a b → Measure (Fin d → I)
  | a, b, .leaf _ => ENNReal.ofReal (rectangleIncrement F a b) • Measure.dirac b
  | _, _, .cut _ _ _ _ left right => left.measure F + right.measure F

theorem measure_univ (hF : IsClassical F) (D : Division a b) :
    D.measure F univ = ENNReal.ofReal (rectangleIncrement F a b) := by
  induction D with
  | leaf hab => simp only [measure, Measure.smul_apply, MeasureTheory.measure_univ,
    smul_eq_mul, mul_one]
  | @cut a b i t hat htb left right ihl ihr =>
    rw [measure, Measure.add_apply, ihl, ihr,
      ← ENNReal.ofReal_add (hF.increasing _ _ left.ordered) (hF.increasing _ _ right.ordered),
      ← rectangleIncrement_split]

private theorem clip_cut (a b u : Fin d → I) (i : Fin d) (t : I) :
    rectangleIncrement F (a ⊓ u) (b ⊓ u) =
      rectangleIncrement F (a ⊓ u) (Function.update b i t ⊓ u) +
        rectangleIncrement F (Function.update a i t ⊓ u) (b ⊓ u) := by
  have he (x : Fin d → I) : Function.update x i t ⊓ u =
      Function.update (x ⊓ u) i (min t (u i)) := by
    funext j
    by_cases hj : j = i
    · subst j; simp only [Pi.inf_apply, Function.update_self]
    · simp only [Pi.inf_apply, Function.update_of_ne hj]
  rw [he, he]
  exact rectangleIncrement_split _ _ _ _

theorem measure_Iic_le (hF : IsClassical F) (D : Division a b) (u : Fin d → I) :
    D.measure F (Iic u) ≤ ENNReal.ofReal (rectangleIncrement F (a ⊓ u) (b ⊓ u)) := by
  induction D with
  | @leaf a b hab =>
    by_cases hb : b ≤ u
    · simp only [measure, Measure.smul_apply, measurableSet_Iic, Measure.dirac_apply', mem_Iic, hb,
      indicator_of_mem, Pi.one_apply, smul_eq_mul, mul_one, inf_eq_left.mpr (hab.trans hb),
      inf_of_le_left, Std.le_refl]
    · simp only [measure, Measure.smul_apply, measurableSet_Iic, Measure.dirac_apply', mem_Iic, hb,
      not_false_eq_true, indicator_of_notMem, smul_eq_mul, mul_zero, zero_le]
  | @cut a b i t hat htb left right ihl ihr =>
    rw [measure, Measure.add_apply, clip_cut a b u i t,
      ENNReal.ofReal_add (hF.increasing _ _ (inf_le_inf left.ordered le_rfl))
        (hF.increasing _ _ (inf_le_inf right.ordered le_rfl))]
    exact add_le_add ihl ihr

theorem le_measure_Iic (hF : IsClassical F) (D : Division a b) {ε : ℝ}
    (hmesh : D.All (fun a b => ∀ i, (b i : ℝ) - (a i : ℝ) ≤ ε))
    (u w : Fin d → I) (hw : ∀ i, w i = 0 ∨ (w i : ℝ) + ε ≤ (u i : ℝ)) :
    ENNReal.ofReal (rectangleIncrement F (a ⊓ w) (b ⊓ w)) ≤ D.measure F (Iic u) := by
  induction D with
  | @leaf a b hab =>
    by_cases hb : b ≤ u
    · simpa only [measure, Measure.smul_apply, measurableSet_Iic, Measure.dirac_apply', mem_Iic, hb,
      indicator_of_mem, Pi.one_apply, smul_eq_mul,
      mul_one] using ENNReal.ofReal_le_ofReal (hF.rectangleIncrement_clip_le a b w hab)
    · obtain ⟨i, hi⟩ := not_forall.mp hb
      have hib : (u i : ℝ) < (b i : ℝ) := not_le.mp hi
      have he : (a ⊓ w) i = (b ⊓ w) i := by
        change min (a i) (w i) = min (b i) (w i)
        rcases hw i with hz | hw
        · simp only [hz, zero_le, inf_of_le_right]
        · have hwa : w i ≤ a i := by
            change (w i : ℝ) ≤ (a i : ℝ)
            have := hmesh i
            linarith
          rw [min_eq_right hwa, min_eq_right (hwa.trans (hab i))]
      rw [rectangleIncrement_eq_zero_of_eq _ _ i he, ENNReal.ofReal_zero]
      exact bot_le
  | @cut a b i t hat htb left right ihl ihr =>
    rw [measure, Measure.add_apply, clip_cut a b w i t,
      ENNReal.ofReal_add (hF.increasing _ _ (inf_le_inf left.ordered le_rfl))
        (hF.increasing _ _ (inf_le_inf right.ordered le_rfl))]
    exact add_le_add (ihl hmesh.1) (ihr hmesh.2)

/-- Repeated bisection in the coordinates listed in `l`. -/
@[expose]
noncomputable def grid (l : List (Fin d)) (a b : Fin d → I) (hab : a ≤ b) : Division a b :=
  match l with
  | [] => .leaf hab
  | i :: l =>
    let t : I := ⟨((a i : ℝ) + (b i : ℝ)) / 2, by
      constructor
      · linarith [(a i).property.1, (b i).property.1]
      · linarith [(a i).property.2, (b i).property.2]⟩
    have hat : a i ≤ t := by
      change (a i : ℝ) ≤ _
      dsimp [t]
      have := hab i
      change (a i : ℝ) ≤ (b i : ℝ) at this
      linarith
    have htb : t ≤ b i := by
      change _ ≤ (b i : ℝ)
      dsimp [t]
      have := hab i
      change (a i : ℝ) ≤ (b i : ℝ) at this
      linarith
    .cut i t hat htb
      (grid l a (Function.update b i t) (by
        intro j; by_cases hj : j = i
        · subst j; simpa only [Function.update_self] using hat
        · simpa only [Function.update_of_ne hj] using hab j))
      (grid l (Function.update a i t) b (by
        intro j; by_cases hj : j = i
        · subst j; simpa only [Function.update_self] using htb
        · simpa only [Function.update_of_ne hj] using hab j))

theorem grid_mesh (l : List (Fin d)) (a b : Fin d → I) (hab : a ≤ b) :
    (grid l a b hab).All (fun x y => ∀ i,
      (y i : ℝ) - (x i : ℝ) ≤ ((b i : ℝ) - (a i : ℝ)) * (1 / 2 : ℝ) ^ l.count i) := by
  induction l generalizing a b with
  | nil => simp only [one_div, List.count_nil, pow_zero, mul_one, tsub_le_iff_right, grid, All,
    sub_add_cancel, Std.le_refl, implies_true]
  | cons j l ih =>
    dsimp only [grid, All]
    constructor
    all_goals
      apply (ih _ _ _).mono
      intro x y hxy i
      apply (hxy i).trans_eq
      by_cases hij : i = j
      · subst i; simp only [Function.update_self, List.count_cons_self, pow_succ]; ring
      · simp only [Function.update_of_ne hij, List.count_cons_of_ne (Ne.symm hij)]

end Division

/-- A finite probability measure attached to a division of the whole cube. -/
@[expose]
noncomputable def probability (hF : IsClassical F)
    (D : Division (fun _ : Fin d => 0) (fun _ => 1)) : ProbabilityMeasure (Fin d → I) :=
  ⟨D.measure F, ⟨by rw [D.measure_univ hF, hF.rectangleIncrement_zero_lower,
    hF.normalized, ENNReal.ofReal_one]⟩⟩

theorem cdf_probability_bounds (hF : IsClassical F)
    (D : Division (fun _ : Fin d => 0) (fun _ => 1)) {ε : ℝ} (hε : 0 ≤ ε)
    (hmesh : D.All (fun a b => ∀ i, (b i : ℝ) - (a i : ℝ) ≤ ε)) (u : Fin d → I) :
    F u - (d : ℝ) * ε ≤ (probability hF D).toMeasure.real (Iic u) ∧
      (probability hF D).toMeasure.real (Iic u) ≤ F u := by
  have hnonneg (v : Fin d → I) : 0 ≤ F v := by
    rw [← hF.rectangleIncrement_zero_lower]
    exact hF.increasing _ _ (fun i => (v i).property.1)
  have hzero (v : Fin d → I) : (fun _ => (0 : I)) ⊓ v = fun _ => 0 := by
    funext i; exact min_eq_left (v i).property.1
  have hone (v : Fin d → I) : (fun _ => (1 : I)) ⊓ v = v := by
    funext i; exact min_eq_right (v i).property.2
  have hupper : (probability hF D).toMeasure (Iic u) ≤ ENNReal.ofReal (F u) := by
    change D.measure F (Iic u) ≤ _
    simpa only [hzero, hone, hF.rectangleIncrement_zero_lower] using
      D.measure_Iic_le hF u
  have hu := ENNReal.toReal_mono ENNReal.ofReal_ne_top hupper
  rw [ENNReal.toReal_ofReal (hnonneg u)] at hu
  refine ⟨?_, hu⟩
  let w : Fin d → I := fun i => ⟨max ((u i : ℝ) - ε) 0, le_max_right _ _,
    max_le (by linarith [(u i).property.2]) zero_le_one⟩
  have hw (i : Fin d) : w i = 0 ∨ (w i : ℝ) + ε ≤ (u i : ℝ) := by
    by_cases hi : (u i : ℝ) ≤ ε
    · left; apply Subtype.ext; exact max_eq_right (sub_nonpos.mpr hi)
    · right; dsimp [w]; rw [max_eq_left (sub_nonneg.mpr (not_le.mp hi).le)]; linarith
  have hwle : w ≤ u := by
    intro i
    change max ((u i : ℝ) - ε) 0 ≤ (u i : ℝ)
    exact max_le (sub_le_self _ hε) (u i).property.1
  have hlower : ENNReal.ofReal (F w) ≤ (probability hF D).toMeasure (Iic u) := by
    change _ ≤ D.measure F (Iic u)
    simpa only [hzero, hone, hF.rectangleIncrement_zero_lower] using
      D.le_measure_Iic hF hmesh u w hw
  have hl := ENNReal.toReal_mono (measure_ne_top (probability hF D).toMeasure _) hlower
  rw [ENNReal.toReal_ofReal (hnonneg w)] at hl
  have hs := hF.sub_le_sum_of_le w u hwle
  have he : ∑ i, ((u i : ℝ) - (w i : ℝ)) ≤ (d : ℝ) * ε := by
    calc
      _ ≤ ∑ _ : Fin d, ε := Finset.sum_le_sum (fun i _ => by
        dsimp [w]
        have := le_max_left ((u i : ℝ) - ε) 0
        linarith)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  change F w ≤ (probability hF D).toMeasure.real (Iic u) at hl
  linarith

/-- The dyadic atomic approximation of classical CDF data. -/
@[expose]
noncomputable def approximation (hF : IsClassical F) (n : ℕ) : ProbabilityMeasure (Fin d → I) :=
  probability hF (Division.grid ((List.replicate n (List.finRange d)).flatten)
    (fun _ => 0) (fun _ => 1) (by intro i; exact zero_le_one))

theorem approximation_bounds (hF : IsClassical F) (n : ℕ) (u : Fin d → I) :
    F u - (d : ℝ) * (1 / 2 : ℝ) ^ n ≤ (approximation hF n).toMeasure.real (Iic u) ∧
      (approximation hF n).toMeasure.real (Iic u) ≤ F u := by
  apply cdf_probability_bounds hF _ (by positivity)
  apply (Division.grid_mesh _ _ _ _).mono
  intro a b hab i
  simpa only [one_div, inv_pow, tsub_le_iff_right, Icc.coe_one, Icc.coe_zero, sub_zero,
    List.count_flatten,
    List.map_replicate, List.count_finRange, List.sum_replicate, smul_eq_mul, mul_one,
      one_mul] using hab i

/-- CDFs of the finite atomic approximations converge to the classical function. -/
theorem approximation_cdf_tendsto (hF : IsClassical F) (u : Fin d → I) :
    Filter.Tendsto (fun n => (approximation hF n).toMeasure.real (Iic u)) Filter.atTop
      (nhds (F u)) := by
  have ht : Filter.Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    (by simpa only [mul_zero, sub_zero] using Filter.Tendsto.const_sub (F u) (ht.const_mul (d : ℝ)))
    tendsto_const_nhds
  · exact fun n => (approximation_bounds hF n u).1
  · exact fun n => (approximation_bounds hF n u).2

end ClassicalConstruction

end ProbabilityTheory.Copula
