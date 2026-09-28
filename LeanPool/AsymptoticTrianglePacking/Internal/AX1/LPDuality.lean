/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

public import Mathlib.Analysis.Convex.Cone.InnerDual
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.ContinuousFunctionalCalculus

/-! # Finite packing-cover LP duality -/

@[expose] public section

open Finset

namespace LPDuality

/- **Abstract finite packing/cover LP (0/1 incidence).** `O` = objects (e.g. triangles),
`C` = constraints (e.g. edges); `inc o` = the constraints incident to object `o`. -/
variable {O C : Type*} [Fintype O] [Fintype C] [DecidableEq C]

/-- A fractional PACKING: nonneg object weights, total ≤ 1 across each constraint. -/
def IsPacking (inc : O → Finset C) (w : O → ℝ) : Prop :=
  (∀ o, 0 ≤ w o) ∧ ∀ c : C, ∑ o ∈ Finset.univ.filter (fun o => c ∈ inc o), w o ≤ 1

/-- A fractional COVER: nonneg constraint weights, total ≥ 1 inside each object. -/
def IsCover (inc : O → Finset C) (y : C → ℝ) : Prop :=
  (∀ c, 0 ≤ y c) ∧ ∀ o : O, 1 ≤ ∑ c ∈ inc o, y c

/-- Packing optimum (LP value). -/
noncomputable def packOpt (inc : O → Finset C) : ℝ :=
  sSup {x | ∃ w, IsPacking inc w ∧ x = ∑ o, w o}

/-- Cover optimum (LP value). -/
noncomputable def coverOpt (inc : O → Finset C) : ℝ :=
  sInf {x | ∃ y, IsCover inc y ∧ x = ∑ c, y c}

omit [Fintype C] in
private lemma zero_isPacking (inc : O → Finset C) : IsPacking inc (0 : O → ℝ) := by
  constructor <;> simp

omit [Fintype C] in
private lemma packValues_nonempty (inc : O → Finset C) :
    {x : ℝ | ∃ w, IsPacking inc w ∧ x = ∑ o, w o}.Nonempty := by
  refine ⟨0, 0, zero_isPacking inc, ?_⟩
  simp

omit [Fintype C] in
private lemma packValues_bddAbove [Finite C] (inc : O → Finset C)
    (hinc : ∀ o, (inc o).Nonempty) :
    BddAbove {x : ℝ | ∃ w, IsPacking inc w ∧ x = ∑ o, w o} := by
  have : Fintype C := Fintype.ofFinite C
  refine ⟨Fintype.card C, ?_⟩
  intro x hx
  obtain ⟨w, hw, rfl⟩ := hx
  -- Double counting: ∑ c, ∑ o ∈ {o | c ∈ inc o}, w o = ∑ o, (inc o).card * w o
  have h1 : ∑ c, ∑ o ∈ Finset.univ.filter (fun o => c ∈ inc o), w o ≤ (Fintype.card C : ℝ) := by
    have := Finset.sum_le_card_nsmul (Finset.univ : Finset C)
      (fun c => ∑ o ∈ Finset.univ.filter (fun o => c ∈ inc o), w o) 1
    simp only [mem_univ, forall_const, card_univ, nsmul_eq_mul, mul_one] at this
    exact this (fun c => hw.2 c)
  -- Rewrite double sum: ∑ c, ∑ o ∈ {o | c ∈ inc o}, w o = ∑ o, (inc o).card * w o
  have h2 : ∑ c, ∑ o ∈ Finset.univ.filter (fun o => c ∈ inc o), w o = ∑ o, (inc o).card * w o := by
    simp only [Finset.sum_filter]
    rw [Finset.sum_comm]
    simp [mul_comm]
  -- Since (inc o).card ≥ 1 and w o ≥ 0, we have w o ≤ (inc o).card * w o
  have h3 : ∑ o, w o ≤ ∑ o, (inc o).card * w o := by
    apply Finset.sum_le_sum
    intro o _
    have hcard : (1 : ℝ) ≤ (inc o).card := by exact_mod_cast Finset.card_pos.mpr (hinc o)
    have hwo : 0 ≤ w o := hw.1 o
    nlinarith only [hcard, hwo]
  linarith only [h1, h2, h3]

omit [Fintype C] in
private lemma packing_value_le_packOpt [Finite C] (inc : O → Finset C)
    (hinc : ∀ o, (inc o).Nonempty) {w : O → ℝ} (hw : IsPacking inc w) :
    ∑ o, w o ≤ packOpt inc := by
  apply le_csSup (packValues_bddAbove inc hinc)
  exact ⟨w, hw, rfl⟩

omit [Fintype O] [DecidableEq C] in
private lemma coverOpt_le_value (inc : O → Finset C) {y : C → ℝ}
    (hy : IsCover inc y) : coverOpt inc ≤ ∑ c, y c := by
  unfold coverOpt
  apply csInf_le
  · refine ⟨0, fun x hx => ?_⟩
    obtain ⟨z, hz, rfl⟩ := hx
    exact Finset.sum_nonneg fun c _ => hz.1 c
  · exact ⟨y, hy, rfl⟩

private abbrev PrimalIndex (O C : Type*) := C ⊕ O ⊕ Unit
private abbrev ConstraintIndex (O : Type*) := O ⊕ Unit
private abbrev PrimalSpace (O C : Type*) := EuclideanSpace ℝ (PrimalIndex O C)
private abbrev ConstraintSpace (O : Type*) := EuclideanSpace ℝ (ConstraintIndex O)

/-- The homogeneous map used to encode cover feasibility.  Its three nonnegative coordinate
blocks are cover weights, row slacks, and objective slack. -/
private noncomputable def coverMap (inc : O → Finset C) :
    PrimalSpace O C →L[ℝ] ConstraintSpace O :=
  LinearMap.toContinuousLinearMap {
    toFun := fun x => WithLp.toLp 2 (fun i => match i with
      | Sum.inl o => (∑ c ∈ inc o, x.ofLp (Sum.inl c)) - x.ofLp (Sum.inr (Sum.inl o))
      | Sum.inr _ => (∑ c, x.ofLp (Sum.inl c)) + x.ofLp (Sum.inr (Sum.inr ())))
    map_add' := by
      intros x y
      apply WithLp.ofLp_injective
      ext i
      cases i with
      | inl o => simp [Finset.sum_add_distrib]; ring
      | inr u => simp [Finset.sum_add_distrib]; ring
    map_smul' := by
      intros m x
      apply WithLp.ofLp_injective
      ext i
      cases i with
      | inl o => simp [← Finset.mul_sum]; ring
      | inr u => simp [← Finset.mul_sum]; ring }

omit [DecidableEq C] in
private lemma coverMap_apply_row (inc : O → Finset C) (x : PrimalSpace O C) (o : O) :
    (coverMap inc x).ofLp (Sum.inl o) =
      (∑ c ∈ inc o, x.ofLp (Sum.inl c)) - x.ofLp (Sum.inr (Sum.inl o)) := rfl

omit [DecidableEq C] in
private lemma coverMap_apply_value (inc : O → Finset C) (x : PrimalSpace O C) :
    (coverMap inc x).ofLp (Sum.inr ()) =
      (∑ c, x.ofLp (Sum.inl c)) + x.ofLp (Sum.inr (Sum.inr ())) := rfl

private def coverRhs (a : ℝ) : ConstraintSpace O := WithLp.toLp 2 (fun i =>
  match i with
  | Sum.inl _ => 1
  | Sum.inr _ => a)

private def nonnegativePointed (I : Type*) :
    PointedCone ℝ (EuclideanSpace ℝ I) := PointedCone.ofConeComb
  {x | ∀ i, 0 ≤ x.ofLp i} ⟨0, by simp⟩ (by
    intro x hx y hy a ha b hb i
    simpa only [WithLp.ofLp_add, Pi.add_apply, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
      using add_nonneg (mul_nonneg ha (hx i)) (mul_nonneg hb (hy i)))

private lemma nonnegative_isClosed (I : Type*) :
    IsClosed ({x : EuclideanSpace ℝ I | ∀ i, 0 ≤ x.ofLp i}) := by
  simp only [Set.ofPred_forall]
  apply isClosed_iInter
  intro i
  apply isClosed_le continuous_const
  fun_prop

private noncomputable def nonnegativeCone (I : Type*) :
    ProperCone ℝ (EuclideanSpace ℝ I) where
  toSubmodule := nonnegativePointed I
  isClosed' := nonnegative_isClosed I

private lemma mem_nonnegativeCone {I : Type*}
    {x : EuclideanSpace ℝ I} : x ∈ nonnegativeCone I ↔ ∀ i, 0 ≤ x.ofLp i := Iff.rfl

private def IsCoverCertificate (inc : O → Finset C) (q : ConstraintSpace O) : Prop :=
  (∀ o, q.ofLp (Sum.inl o) ≤ 0) ∧
  0 ≤ q.ofLp (Sum.inr ()) ∧
  ∀ c, 0 ≤ q.ofLp (Sum.inr ()) +
    ∑ o ∈ Finset.univ.filter (fun o => c ∈ inc o), q.ofLp (Sum.inl o)

/-- Testing the adjoint-dual condition on coordinate vectors gives the familiar sign and
transpose inequalities for a Farkas certificate. -/
private lemma adjoint_mem_innerDual_implies_certificate (inc : O → Finset C)
    (q : ConstraintSpace O)
    (hq : (ContinuousLinearMap.adjoint (coverMap inc)) q ∈
      ProperCone.innerDual (nonnegativeCone (PrimalIndex O C) : Set (PrimalSpace O C))) :
    IsCoverCertificate inc q := by
  classical
  unfold IsCoverCertificate
  rw [ProperCone.mem_innerDual] at hq
  constructor
  · -- ∀ o, q.ofLp (Sum.inl o) ≤ 0
    intro o
    -- Test with unit vector at position Sum.inr (Sum.inl o)
    let x : PrimalSpace O C := EuclideanSpace.single (Sum.inr (Sum.inl o)) 1
    have hx : x ∈ nonnegativeCone (PrimalIndex O C) := by
      rw [mem_nonnegativeCone]
      intro i
      simp only [x, EuclideanSpace.single]
      simp
      split_ifs <;> norm_num
    have h := hq hx
    -- Use adjointness: inner x ((coverMap).adjoint q) = inner (coverMap x) q
    rw [ContinuousLinearMap.adjoint_inner_right] at h
    -- Compute coverMap inc x for x = single (inr (inl o)) 1
    -- Compute (coverMap inc x).ofLp for our test vector
    have hx_inl : ∀ c : C, x.ofLp (Sum.inl c) = 0 := by
      intro c
      simp [x]
    have hx_inr_inl : ∀ o' : O, x.ofLp (Sum.inr (Sum.inl o')) = if o' = o then 1 else 0 := by
      intro o'
      classical
      simp [x]
    have hx_inr_inr : x.ofLp (Sum.inr (Sum.inr ())) = 0 := by simp [x]
    have hcm_inl : ∀ o' : O, (coverMap inc x).ofLp (Sum.inl o') = -if o' = o then 1 else 0 := by
      intro o'
      rw [coverMap_apply_row]
      simp [hx_inl, hx_inr_inl]
    have hcm_inr : (coverMap inc x).ofLp (Sum.inr ()) = 0 := by
      rw [coverMap_apply_value]
      simp [hx_inl, hx_inr_inr]
    -- Compute inner (coverMap inc x) q = -q.ofLp (Sum.inl o)
    have hinner : inner ℝ (coverMap inc x) q = -q.ofLp (Sum.inl o) := by
      simp [inner, hcm_inl, hcm_inr]
    linarith only [h, hinner]
  constructor
  · -- 0 ≤ q.ofLp (Sum.inr ())
    -- Test with unit vector at position Sum.inr (Sum.inr ())
    let y : PrimalSpace O C := EuclideanSpace.single (Sum.inr (Sum.inr ())) 1
    have hy : y ∈ nonnegativeCone (PrimalIndex O C) := by
      rw [mem_nonnegativeCone]
      intro i
      simp only [y, EuclideanSpace.single]
      simp
      split_ifs <;> norm_num
    have hyq := hq hy
    rw [ContinuousLinearMap.adjoint_inner_right] at hyq
    -- coverMap inc y has value 1 at Sum.inr () and 0 elsewhere
    have hyv_inl : ∀ c : C, y.ofLp (Sum.inl c) = 0 := by
      intro c
      simp [y]
    have hyv_inr_inl : ∀ o' : O, y.ofLp (Sum.inr (Sum.inl o')) = 0 := by
      intro o'
      simp [y]
    have hyv_inr_inr : y.ofLp (Sum.inr (Sum.inr ())) = 1 := by simp [y]
    have hymv : (coverMap inc y).ofLp (Sum.inr ()) = 1 := by
      rw [coverMap_apply_value]
      simp [hyv_inl, hyv_inr_inr]
    have hymv' : ∀ o' : O, (coverMap inc y).ofLp (Sum.inl o') = 0 := by
      intro o'
      rw [coverMap_apply_row]
      simp [hyv_inl, hyv_inr_inl]
    simp only [inner, star_trivial, RCLike.mul_re, RCLike.re_to_real,
      RCLike.im_to_real, mul_zero, sub_zero, Fintype.sum_sum_type, hymv',
      sum_const_zero, univ_unique, PUnit.default_eq_unit, hymv, mul_one,
      sum_singleton, zero_add] at hyq
    exact hyq
  · -- ∀ c, 0 ≤ q.ofLp (Sum.inr ()) + ∑ o with c ∈ inc o, q.ofLp (Sum.inl o)
    intro c₀
    -- Test with unit vector at position Sum.inl c₀
    let z : PrimalSpace O C := EuclideanSpace.single (Sum.inl c₀) 1
    have hz : z ∈ nonnegativeCone (PrimalIndex O C) := by
      rw [mem_nonnegativeCone]
      intro i
      simp only [z, EuclideanSpace.single]
      simp
      split_ifs <;> norm_num
    have hzq := hq hz
    rw [ContinuousLinearMap.adjoint_inner_right] at hzq
    -- Compute coverMap inc z
    have hz_inl : ∀ c : C, z.ofLp (Sum.inl c) = if c = c₀ then 1 else 0 := by
      intro c
      simp [z]
    have hz_inr_inl : ∀ o' : O, z.ofLp (Sum.inr (Sum.inl o')) = 0 := by
      intro o'
      simp [z]
    have hz_inr_inr : z.ofLp (Sum.inr (Sum.inr ())) = 0 := by simp [z]
    have hzv : (coverMap inc z).ofLp (Sum.inr ()) = 1 := by
      rw [coverMap_apply_value]
      simp [hz_inl, hz_inr_inr]
    have hzm : ∀ o' : O, (coverMap inc z).ofLp (Sum.inl o') = if c₀ ∈ inc o' then 1 else 0 := by
      intro o'
      rw [coverMap_apply_row]
      simp [hz_inl, hz_inr_inl]
    simp only [inner, star_trivial, RCLike.mul_re, RCLike.re_to_real,
      RCLike.im_to_real, mul_zero, sub_zero, Fintype.sum_sum_type, hzm,
      mul_ite, mul_one, univ_unique, PUnit.default_eq_unit, hzv,
      sum_singleton] at hzq
    convert hzq using 1
    simp [Finset.sum_filter]
    ring

omit [Fintype C] in
/-- The elementary normalization step: a certificate with positive last coordinate gives a
packing by `w o = -q o / q_last`; if that coordinate vanishes, nonempty rows force `q = 0`. -/
private lemma certificate_nonneg [Finite C] (inc : O → Finset C)
    (hinc : ∀ o, (inc o).Nonempty) {a : ℝ} (ha : packOpt inc < a)
    (q : ConstraintSpace O) (hq : IsCoverCertificate inc q) :
    0 ≤ inner ℝ (coverRhs a) q := by
  have : Fintype C := Fintype.ofFinite C
  -- Extract certificate properties
  obtain ⟨hq_neg, hq_last, hq_constraint⟩ := hq
  -- Set up abbreviations
  set q_last := q.ofLp (Sum.inr ()) with hq_last_def
  set q_o := fun o => q.ofLp (Sum.inl o) with hq_o_def
  -- Rewrite inner product
  simp only [inner]
  -- inner ℝ on ℝ is multiplication
  have h_inner : ∀ (r s : ℝ), inner ℝ r s = r * s := fun r s => mul_comm s r
  simp only [star_trivial, RCLike.mul_re, RCLike.re_to_real, RCLike.im_to_real,
    mul_zero, sub_zero, Fintype.sum_sum_type, univ_unique, PUnit.default_eq_unit,
    sum_singleton, ge_iff_le]
  -- Simplify coverRhs values
  have h_coverRhs_inl : ∀ o : O, (coverRhs a).ofLp (Sum.inl o) = 1 := by
    intro o; rfl
  have h_coverRhs_inr : (coverRhs a).ofLp (Sum.inr (α := O) ()) = a := by rfl
  simp only [h_coverRhs_inl, mul_one, h_coverRhs_inr, ge_iff_le]
    at hq_constraint hq_neg hq_last ⊢
  -- Goal: 0 ≤ ∑ o, q_o o + q_last * a
  -- Note: Sum.inr PUnit.unit = Sum.inr () in ConstraintIndex = O ⊕ Unit
  have inr_eq : (Sum.inr PUnit.unit : O ⊕ Unit) = Sum.inr () := rfl
  rw [inr_eq]
  -- Case split on whether q_last = 0
  by_cases hq_last_zero : q_last = 0
  · -- Case q_last = 0: constraint sums must all be 0, so each q_o = 0
    -- First establish a ≥ 0
    have ha_nonneg : 0 ≤ a := by
      have h_packOpt_nonneg : 0 ≤ packOpt inc := by
        apply le_csSup (packValues_bddAbove inc hinc)
        exact ⟨0, zero_isPacking inc, by simp⟩
      linarith only [ha, h_packOpt_nonneg]
    rw [← hq_last_def, hq_last_zero, zero_mul]
    -- From hq_constraint and hq_neg: all q_o must be 0
    have h_q_o_zero : ∀ o, q.ofLp (Sum.inl o) = 0 := by
      intro o
      obtain ⟨c, hc⟩ := hinc o
      have hsum := hq_constraint c
      simp only [hq_last_zero, hq_o_def, zero_add] at hsum
      -- hsum : 0 ≤ ∑ o ∈ {o | c ∈ inc o}, q.ofLp (Sum.inl o)
      -- Each term is ≤ 0, so sum ≤ 0. Thus sum = 0.
      have hsum_neg : ∑ o ∈ Finset.univ.filter (fun o => c ∈ inc o), q.ofLp (Sum.inl o) ≤ 0 := by
        apply Finset.sum_nonpos
        intro o _
        exact hq_neg o
      have hsum_eq : ∑ o ∈ Finset.univ.filter (fun o => c ∈ inc o),
          q.ofLp (Sum.inl o) = 0 := by
        linarith only [hsum, hsum_neg]
      -- Since o is in the filter and sum = 0 with all terms ≤ 0, q.ofLp (Sum.inl o) = 0
      have ho_in_filter : o ∈ Finset.univ.filter (fun o => c ∈ inc o) := by simp [hc]
      have h_eq_zero := Finset.sum_eq_zero_iff_of_nonpos (fun o _ => hq_neg o) |>.mp hsum_eq
      exact h_eq_zero o ho_in_filter
    simp [h_q_o_zero]
  · -- Case q_last > 0: use sum of constraints
    have hq_last_pos : 0 < q_last := lt_of_le_of_ne hq_last (Ne.symm hq_last_zero)
    have ha_nonneg : 0 ≤ a := by
      have h_packOpt_nonneg : 0 ≤ packOpt inc := by
        apply le_csSup (packValues_bddAbove inc hinc)
        exact ⟨0, zero_isPacking inc, by simp⟩
      linarith only [ha, h_packOpt_nonneg]
    -- Rewrite goal using q_last
    rw [← hq_last_def]
    -- Goal: 0 ≤ ∑ o, q_o o + q_last * a
    -- Sum constraint inequalities
    have h_sum_cons : ∑ c : C,
        (q_last + ∑ o ∈ Finset.univ.filter (fun o => c ∈ inc o), q_o o) ≥ 0 := by
      apply Finset.sum_nonneg
      intro c _
      exact hq_constraint c
    -- Expand sum: C * q_last + ∑ c, ∑ o with c ∈ inc o, q_o o
    have h_expand : ∑ c : C, (q_last + ∑ o ∈ Finset.univ.filter (fun o => c ∈ inc o), q_o o) =
        Fintype.card C * q_last +
          ∑ c : C, ∑ o ∈ Finset.univ.filter (fun o => c ∈ inc o), q_o o := by
      simp [Finset.sum_add_distrib]
    -- Double sum: ∑ c, ∑ o with c ∈ inc o, q_o o = ∑ o, (inc o).card * q_o o
    have h_double_sum : ∑ c : C, ∑ o ∈ Finset.univ.filter (fun o => c ∈ inc o), q_o o =
        ∑ o : O, (inc o).card * q_o o := by
      simp only [Finset.sum_filter]
      rw [Finset.sum_comm]
      simp
    -- Since (inc o).card ≥ 1 and q_o o ≤ 0: (inc o).card * q_o o ≤ q_o o
    have h_card_mul_le : ∑ o : O, (inc o).card * q_o o ≤ ∑ o : O, q_o o := by
      apply Finset.sum_le_sum
      intro o _
      have hcard : (1 : ℝ) ≤ (inc o).card := by exact_mod_cast Finset.card_pos.mpr (hinc o)
      nlinarith [hq_neg o]
    -- Therefore: C * q_last + ∑ o, q_o o ≥ C * q_last + ∑ o, (inc o).card * q_o o ≥ 0
    have h_bound : Fintype.card C * q_last + ∑ o : O, q_o o ≥ 0 := by
      linarith only [h_sum_cons, h_expand, h_double_sum, h_card_mul_le]
    -- packOpt inc ≤ Fintype.card C
    have h_packOpt_le_C : packOpt inc ≤ Fintype.card C := by
      rw [packOpt]
      apply csSup_le (packValues_nonempty inc)
      intro x hx
      obtain ⟨w, hw, rfl⟩ := hx
      -- Each constraint: ∑ o with c ∈ inc o, w o ≤ 1
      -- Summing: ∑ c, ∑ o with c ∈ inc o, w o ≤ C
      -- Double sum = ∑ o, (inc o).card * w o ≥ ∑ o, w o (since card ≥ 1 and w ≥ 0)
      have h_sum_cons : ∑ c : C,
          ∑ o ∈ Finset.univ.filter (fun o => c ∈ inc o), w o ≤ Fintype.card C := by
        have := Finset.sum_le_card_nsmul Finset.univ
          (fun c => ∑ o ∈ Finset.univ.filter (fun o => c ∈ inc o), w o) 1
        simp only [mem_univ, forall_const, card_univ, nsmul_eq_mul, mul_one] at this
        exact this fun c => hw.2 c
      have h_double_sum : ∑ c : C, ∑ o ∈ Finset.univ.filter (fun o => c ∈ inc o), w o =
          ∑ o : O, (inc o).card * w o := by
        simp only [Finset.sum_filter]
        rw [Finset.sum_comm]
        simp [mul_comm]
      have h_le : ∑ o : O, w o ≤ ∑ o : O, (inc o).card * w o := by
        apply Finset.sum_le_sum
        intro o _
        have hcard : (1 : ℝ) ≤ (inc o).card := by exact_mod_cast Finset.card_pos.mpr (hinc o)
        nlinarith [hw.1 o]
      linarith only [h_sum_cons, h_double_sum, h_le]
    -- Now use that normalized certificate gives a packing with value ≤ packOpt inc < a
    -- Define normalized packing: w o = -q_o o / q_last
    let w : O → ℝ := fun o => -q_o o / q_last
    have hw_nonneg : ∀ o, 0 ≤ w o := by
      intro o
      simp only [w]
      apply div_nonneg
      · linarith only [hq_neg o]
      · exact hq_last
    have hw_constraint : ∀ c, ∑ o ∈ Finset.univ.filter (fun o => c ∈ inc o), w o ≤ 1 := by
      intro c
      simp only [w]
      have hc := hq_constraint c
      -- hc : 0 ≤ q_last + ∑ o with c ∈ inc o, q_o o
      have : ∑ o ∈ Finset.univ.filter (fun o => c ∈ inc o), -q_o o / q_last =
          (-1 / q_last) * ∑ o ∈ Finset.univ.filter (fun o => c ∈ inc o), q_o o := by
        rw [Finset.mul_sum]
        congr 1
        ext o
        ring
      rw [this]
      -- Need: (-1 / q_last) * S ≤ 1 where S = ∑ o with c ∈ inc o, q_o o
      -- From hc: q_last + S ≥ 0, so S ≥ -q_last
      -- So (-1/q_last) * S ≤ (-1/q_last) * (-q_last) = 1 (since q_last > 0)
      have hc' : q_last + ∑ o ∈ Finset.univ.filter (fun o => c ∈ inc o), q_o o ≥ 0 := hc
      have hS_ge : ∑ o ∈ Finset.univ.filter (fun o => c ∈ inc o), q_o o ≥ -q_last := by
        linarith only [hc']
      have hq_last_ne : q_last ≠ 0 := ne_of_gt hq_last_pos
      field_simp
      nlinarith only [hS_ge]
    have hw : IsPacking inc w := ⟨hw_nonneg, hw_constraint⟩
    have h_w_value : ∑ o : O, w o ≤ packOpt inc := packing_value_le_packOpt inc hinc hw
    -- h_w_value : ∑ o, -q_o o / q_last ≤ packOpt inc
    -- i.e., -∑ o, q_o o / q_last ≤ packOpt inc
    -- i.e., ∑ o, q_o o ≥ -packOpt inc * q_last
    have h_sum_rewrite : ∑ o : O, w o = (-1 / q_last) * ∑ o : O, q_o o := by
      rw [Finset.mul_sum]
      congr 1
      ext o
      ring
    rw [h_sum_rewrite] at h_w_value
    -- h_w_value : (-1 / q_last) * ∑ o, q_o o ≤ packOpt inc
    -- Multiply by q_last: -∑ o, q_o o ≤ packOpt inc * q_last
    have hq_last_ne : q_last ≠ 0 := ne_of_gt hq_last_pos
    field_simp at h_w_value
    -- h_w_value : -∑ o, q_o o ≤ packOpt inc * q_last
    have h_lower_bound : ∑ o : O, q_o o ≥ -packOpt inc * q_last := by linarith only [h_w_value]
    -- Goal: 0 ≤ ∑ o, q_o o + q_last * a
    -- We have ∑ o, q_o o ≥ -packOpt inc * q_last
    -- So ∑ o, q_o o + q_last * a ≥ -packOpt inc * q_last + q_last * a,
    -- which is q_last * (a - packOpt inc) > 0.
    nlinarith only [ha, hq_last_pos, h_lower_bound]

/-- The Farkas certificate inequality.  This is the algebraic heart of duality: a certificate
against cover feasibility, after normalization by its last coordinate, is a packing. -/
private lemma cover_certificate_nonneg (inc : O → Finset C)
    (hinc : ∀ o, (inc o).Nonempty) {a : ℝ} (ha : packOpt inc < a)
    (q : ConstraintSpace O)
    (hq : (ContinuousLinearMap.adjoint (coverMap inc)) q ∈
      ProperCone.innerDual (nonnegativeCone (PrimalIndex O C) : Set (PrimalSpace O C))) :
    0 ≤ inner ℝ (coverRhs a) q := by
  exact certificate_nonneg inc hinc ha q (adjoint_mem_innerDual_implies_certificate inc q hq)

/-- Farkas' lemma puts the desired right-hand side in the closure of the image of the
nonnegative orthant. -/
private lemma coverRhs_mem_conic_closure (inc : O → Finset C)
    (hinc : ∀ o, (inc o).Nonempty) {a : ℝ} (ha : packOpt inc < a) :
    coverRhs a ∈ (nonnegativeCone (PrimalIndex O C)).map (coverMap inc) := by
  simp only [ProperCone.map]
  refine ProperCone.relative_hyperplane_separation.mpr ?_
  intro y hy
  exact cover_certificate_nonneg inc hinc ha y hy

omit [DecidableEq C] in
/-- A point of the conic image closure gives covers whose values approach the encoded objective.
The row error is repaired by scaling by `1 / (1 - ε)`. -/
private lemma coverOpt_le_ratio_of_mem_closure (inc : O → Finset C) {a ε : ℝ}
    (hmem : coverRhs a ∈ (nonnegativeCone (PrimalIndex O C)).map (coverMap inc))
    (hε : 0 < ε) (hε1 : ε < 1) :
    coverOpt inc ≤ (a + ε) / (1 - ε) := by
  rw [ProperCone.mem_map] at hmem
  -- hmem : coverRhs a ∈ closure of the image
  -- Use that closure is the topological closure
  let S := PointedCone.map (coverMap inc).toLinearMap
    (nonnegativeCone (PrimalIndex O C)).toPointedCone
  have hmem' : coverRhs a ∈ closure (S : Set (ConstraintSpace O)) := hmem
  rw [Metric.mem_closure_iff] at hmem'
  -- Choose δ small enough so that the error can be repaired by scaling
  set δ := min (ε / 2) (1 / 4) with hδ_def
  have hδ_pos : 0 < δ := by positivity
  obtain ⟨b, hb_S, hb_dist⟩ := hmem' δ hδ_pos
  -- b ∈ S means there exists x in nonnegativeCone with coverMap inc x = b
  obtain ⟨x, hx_cone, hx_eq⟩ := hb_S
  -- Define y c = x.ofLp (Sum.inl c), which is nonnegative
  let y : C → ℝ := fun c => x.ofLp (Sum.inl c)
  have hy_nonneg : ∀ c, 0 ≤ y c := by
    intro c
    have : x ∈ nonnegativeCone (PrimalIndex O C) := hx_cone
    rw [mem_nonnegativeCone] at this
    exact this _
  -- From coverMap inc x = b and dist (coverRhs a) b < δ
  -- The row sums and value are close to those of coverRhs a
  have h_coord_bound : ∀ i, |(coverRhs a).ofLp i - b.ofLp i| < δ := by
    intro i
    have h1 : dist (coverRhs a) b < δ := hb_dist
    have h2 : |(coverRhs a).ofLp i - b.ofLp i| ≤ ‖(coverRhs a : ConstraintSpace O) - b‖ := by
      have hnn : ((coverRhs a).ofLp i - b.ofLp i) ^ 2 ≤
          ‖(coverRhs a : ConstraintSpace O) - b‖ ^ 2 := by
        rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
        have heq : ∀ j, ‖(coverRhs a - b).ofLp j‖ ^ 2 = ((coverRhs a).ofLp j - b.ofLp j) ^ 2 := by
          intro j
          simp [Real.norm_eq_abs]
        simp_rw [heq]
        apply Finset.single_le_sum (f := fun j => ((coverRhs a).ofLp j - b.ofLp j) ^ 2)
        · intros; positivity
        · simp
      have := Real.abs_le_sqrt hnn
      rwa [Real.sqrt_sq (norm_nonneg _)] at this
    rw [dist_eq_norm] at h1
    exact lt_of_le_of_lt h2 h1
  -- From coverMap inc x = b, derive bounds on row sums
  -- For each object o: row_sum o = 1 + x.ofLp (Sum.inr (Sum.inl o)) ≥ 1
  -- But b is close to coverRhs a, so row_sum o is close to 1
  have h_row_sum_bound : ∀ o, 1 - δ < ∑ c ∈ inc o, y c := by
    intro o
    have h1 : |(coverRhs a).ofLp (Sum.inl o) - b.ofLp (Sum.inl o)| < δ := h_coord_bound (Sum.inl o)
    have h2 : b.ofLp (Sum.inl o) = (∑ c ∈ inc o, y c) - x.ofLp (Sum.inr (Sum.inl o)) := by
      rw [← hx_eq]
      rfl
    rw [h2] at h1
    have hx_nonneg : 0 ≤ x.ofLp (Sum.inr (Sum.inl o)) := by
      have hx' : x ∈ nonnegativeCone (PrimalIndex O C) := hx_cone
      rw [mem_nonnegativeCone] at hx'
      exact hx' _
    have h1' := abs_lt.mp h1
    simp at h1'
    have hca : (coverRhs a).ofLp (Sum.inl o) = 1 := rfl
    linarith only [hx_nonneg, h1', hca]
  -- Bound on the total sum
  have h_total_sum_bound : ∑ c, y c < a + δ := by
    have h1 : |(coverRhs a).ofLp (Sum.inr PUnit.unit) -
        b.ofLp (Sum.inr PUnit.unit)| < δ := h_coord_bound (Sum.inr PUnit.unit)
    have h2 : b.ofLp (Sum.inr PUnit.unit) = (∑ c, y c) + x.ofLp (Sum.inr (Sum.inr ())) := by
      rw [← hx_eq]
      rfl
    rw [h2] at h1
    have hx_nonneg : 0 ≤ x.ofLp (Sum.inr (Sum.inr ())) := by
      have hx' : x ∈ nonnegativeCone (PrimalIndex O C) := hx_cone
      rw [mem_nonnegativeCone] at hx'
      exact hx' _
    have h1' := abs_lt.mp h1
    simp at h1'
    have hca : (coverRhs a : ConstraintSpace O).ofLp (Sum.inr PUnit.unit) = a := by simp [coverRhs]
    linarith only [hx_nonneg, h1', hca]
  -- δ ≤ ε/2 < ε and δ ≤ 1/4 < 1
  have hδ_le : δ ≤ ε / 2 := min_le_left _ _
  have hδ_lt1 : δ < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num : (1 : ℝ) / 4 < 1)
  -- Since ∑ c, y c ≥ 0 and ∑ c, y c < a + δ, we have a > -δ ≥ -1/4 > -1
  have ha_gt : a > -δ := by
    have hy_sum_nonneg : 0 ≤ ∑ c, y c := Finset.sum_nonneg fun c _ => hy_nonneg c
    linarith [h_total_sum_bound]
  have ha_ge_neg1 : a ≥ -1 := by linarith only [hδ_lt1, ha_gt]
  -- Define scaled cover z = y / (1 - δ)
  set z : C → ℝ := fun c => y c / (1 - δ) with hz_def
  -- z is nonnegative
  have hz_nonneg : ∀ c, 0 ≤ z c := by
    intro c
    exact div_nonneg (hy_nonneg c) (by linarith)
  -- z is a valid cover: ∑ c ∈ inc o, z c > 1
  have hz_cover : ∀ o, 1 ≤ ∑ c ∈ inc o, z c := by
    intro o
    have := h_row_sum_bound o
    have h1mδ_pos : 0 < 1 - δ := by linarith only [hδ_lt1]
    calc 1 = (1 - δ) / (1 - δ) := by field_simp
      _ ≤ (∑ c ∈ inc o, y c) / (1 - δ) := by
        apply div_le_div_of_nonneg_right this.le (le_of_lt h1mδ_pos)
      _ = ∑ c ∈ inc o, y c / (1 - δ) := by rw [← Finset.sum_div]
      _ = ∑ c ∈ inc o, z c := by rfl
  -- z is a cover
  have hz_isCover : IsCover inc z := ⟨hz_nonneg, hz_cover⟩
  -- coverOpt inc ≤ ∑ c, z c
  have h_coverOpt_le : coverOpt inc ≤ ∑ c, z c := coverOpt_le_value inc hz_isCover
  -- ∑ c, z c = (∑ c, y c) / (1 - δ) < (a + δ) / (1 - δ)
  have h_sum_z_bound : ∑ c, z c < (a + δ) / (1 - δ) := by
    have h1mδ_pos : 0 < 1 - δ := by linarith only [hδ_lt1]
    calc ∑ c, z c = ∑ c, y c / (1 - δ) := by rfl
      _ = (∑ c, y c) / (1 - δ) := by rw [← Finset.sum_div]
      _ < (a + δ) / (1 - δ) := by apply div_lt_div_of_pos_right h_total_sum_bound h1mδ_pos
  -- (a + δ) / (1 - δ) ≤ (a + ε) / (1 - ε) since δ ≤ ε/2 < ε
  have h_ratio_bound : (a + δ) / (1 - δ) ≤ (a + ε) / (1 - ε) := by
    have h1mε_pos : 0 < 1 - ε := by linarith only [hε1]
    have h1mδ_pos : 0 < 1 - δ := by linarith only [hδ_lt1]
    field_simp
    nlinarith [hδ_le, ha_ge_neg1]
  linarith only [h_coverOpt_le, h_sum_z_bound, h_ratio_bound]

/-- Approximate conic feasibility can be repaired (by a uniform scaling) to an actual cover.
Consequently every strict upper bound on the packing optimum bounds the cover infimum. -/
private lemma coverOpt_le_of_packOpt_lt (inc : O → Finset C)
    (hinc : ∀ o, (inc o).Nonempty) {a : ℝ} (ha : packOpt inc < a) :
    coverOpt inc ≤ a := by
  by_contra h
  push Not at h
  -- coverRhs a is in the conic image
  have hmem := coverRhs_mem_conic_closure inc hinc ha
  -- For any ε ∈ (0,1), coverOpt inc ≤ (a + ε) / (1 - ε)
  have hbound : ∀ ε, 0 < ε → ε < 1 → coverOpt inc ≤ (a + ε) / (1 - ε) := by
    intros ε hε hε1
    exact coverOpt_le_ratio_of_mem_closure inc hmem hε hε1
  -- Choose ε small enough so that (a + ε) / (1 - ε) < coverOpt inc
  -- Since coverOpt inc ≥ 0 (covers are nonnegative), 1 + coverOpt inc > 0
  set c := coverOpt inc with hc_def
  have hc_nonneg : 0 ≤ c := by
    unfold coverOpt at hc_def
    apply Real.sInf_nonneg
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact Finset.sum_nonneg fun _ _ => hy.1 _
  have h_one_plus_c : 0 < 1 + c := by linarith only [hc_nonneg]
  set δ := c - a with hδ_def
  have hδ : 0 < δ := by linarith only [h]
  -- Choose ε = min(1/2, (c - a) / (2 * (1 + c)))
  set ε := min (1/2) ((c - a) / (2 * (1 + c))) with hε_def
  have hε_pos : 0 < ε := by
    apply lt_min
    · norm_num
    · exact div_pos hδ (by linarith)
  have hε_lt_1 : ε < 1 := by
    have := min_le_left (1/2) ((c - a) / (2 * (1 + c)))
    linarith only [this]
  have hε_bound : ε * (1 + c) < δ := by
    have h1 : ε ≤ (c - a) / (2 * (1 + c)) := min_le_right _ _
    have h2 : ε * (1 + c) ≤ (c - a) / 2 := by
      have := mul_le_mul_of_nonneg_right h1 (by linarith : 0 ≤ 1 + c)
      field_simp at this ⊢
      linarith only [this]
    linarith only [hδ, h2]
  -- Now derive contradiction
  have hc_le := hbound ε hε_pos hε_lt_1
  -- From hε_bound: ε * (1 + c) < c - a, we get (a + ε) / (1 - ε) < c
  have hcontra : (a + ε) / (1 - ε) < c := by
    rw [div_lt_iff₀ (by linarith : 0 < 1 - ε)]
    ring_nf
    linarith only [hε_bound]
  linarith only [hc_le, hcontra]

omit [Fintype O] [DecidableEq C] in
private lemma coverOpt_eq_zero_of_empty_row (inc : O → Finset C) {o : O}
    (ho : inc o = ∅) : coverOpt inc = 0 := by
  unfold coverOpt
  have h_empty : {x | ∃ y, IsCover inc y ∧ x = ∑ c, y c} = ∅ := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    intro ⟨y, hy, _⟩
    have := hy.2 o
    rw [ho] at this
    simp at this
    linarith only [this]
  rw [h_empty]
  simp

/-- **THE ATOM — finite LP strong duality (packing = cover).** Machinery-free: pure finite LP.
This is the only genuinely hard step; everything downstream is instantiation. -/
theorem lp_strong_duality (inc : O → Finset C) :
    coverOpt inc ≤ packOpt inc := by
  by_cases hempty : ∃ o, inc o = ∅
  · obtain ⟨o, ho⟩ := hempty
    have hzero : coverOpt inc = 0 := @coverOpt_eq_zero_of_empty_row O C _ inc o ho
    rw [hzero]
    apply Real.sSup_nonneg
    rintro x ⟨w, hw, rfl⟩
    exact Finset.sum_nonneg fun o _ => hw.1 o
  · have hinc : ∀ o, (inc o).Nonempty := fun o => by simp_all [Finset.nonempty_iff_ne_empty]
    by_contra h
    push Not at h
    -- h : packOpt inc < coverOpt inc
    set a := (packOpt inc + coverOpt inc) / 2 with ha_def
    have ha : packOpt inc < a := by linarith only [h, ha_def]
    have hcover := @coverOpt_le_of_packOpt_lt O C _ _ _ inc hinc a ha
    linarith only [ha_def, ha, hcover]

/-- Every feasible packing value is at most every feasible cover value. -/
theorem weak_duality (inc : O → Finset C) {w : O → ℝ} {y : C → ℝ}
    (hw : IsPacking inc w) (hy : IsCover inc y) :
    ∑ o, w o ≤ ∑ c, y c := by
  classical
  calc
    ∑ o, w o ≤ ∑ o, w o * ∑ c ∈ inc o, y c := by
      refine Finset.sum_le_sum fun o _ => ?_
      calc w o = w o * 1 := by ring
        _ ≤ w o * ∑ c ∈ inc o, y c :=
          mul_le_mul_of_nonneg_left (hy.2 o) (hw.1 o)
    _ = ∑ o : O, ∑ c : C, if c ∈ inc o then w o * y c else 0 := by
      refine Finset.sum_congr rfl fun o _ => ?_
      rw [Finset.mul_sum]
      simp
    _ = ∑ c : C, ∑ o : O, if c ∈ inc o then w o * y c else 0 := Finset.sum_comm
    _ = ∑ c, (∑ o ∈ Finset.univ.filter (fun o => c ∈ inc o), w o) * y c := by
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Finset.sum_mul, Finset.sum_filter]
    _ ≤ ∑ c, 1 * y c := by
      refine Finset.sum_le_sum fun c _ => ?_
      exact mul_le_mul_of_nonneg_right (hw.2 c) (hy.1 c)
    _ = ∑ c, y c := by simp

/-- Finite packing/cover weak duality at the optimum, when every object meets a constraint. -/
theorem packOpt_le_coverOpt (inc : O → Finset C) (hinc : ∀ o, (inc o).Nonempty) :
    packOpt inc ≤ coverOpt inc := by
  classical
  have hcover : {x : ℝ | ∃ y, IsCover inc y ∧ x = ∑ c, y c}.Nonempty := by
    refine ⟨Fintype.card C, (fun _ => 1), ?_, ?_⟩
    · constructor
      · intro c; norm_num
      · intro o
        simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
        exact_mod_cast Finset.card_pos.mpr (hinc o)
    · simp
  unfold packOpt coverOpt
  refine csSup_le (packValues_nonempty inc) ?_
  rintro x ⟨w, hw, rfl⟩
  refine le_csInf hcover ?_
  rintro yval ⟨y, hy, rfl⟩
  exact weak_duality inc hw hy

end LPDuality
