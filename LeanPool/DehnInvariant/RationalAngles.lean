/-
Copyright (c) 2026 DICTO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DICTO
-/

/- Modified for Lean Pool. -/

module

public import LeanPool.DehnInvariant.ConeAngles
public import LeanPool.DehnInvariant.PlaneCut
public import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring

/-!
# Dehn invariants with rational dihedral angles

A finite intersection of half-spaces has zero Dehn invariant when every pair of its normal
vectors makes a rational multiple of π. At an edge, a cone with an interior direction reduces
to the two extreme half-spaces. Cones without such a direction give a null wedge.
-/

@[expose] public section

open scoped RealInnerProductSpace
open Set MeasureTheory Measure Module TensorProduct

namespace DehnCanon.Library

/-! ### Angles whose squared cosine is 0, 1/4, 1/2, 3/4 or 1 -/

lemma mem_ratPi_of_sin_nat_mul {x : ℝ} (N : ℕ) (hN : N ≠ 0) (h : Real.sin (N * x) = 0) :
    x ∈ ratPi := by
  obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.1 h
  rw [mem_ratPi_iff]
  refine ⟨(n : ℚ) / N, ?_⟩
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hN
  have hx : x = n * Real.pi / N := by rw [eq_div_iff hN']; linarith
  rw [hx]; push_cast; ring

lemma pi_mem_ratPi : Real.pi ∈ ratPi := (mem_ratPi_iff _).2 ⟨1, by simp⟩

/-- If 4 cos² θ is 0, 1, 2, 3 or 4, then θ is a rational multiple of π. -/
lemma mem_ratPi_of_four_cos_sq {θ : ℝ} {k : ℕ} (hk : k ≤ 4) (h : 4 * Real.cos θ ^ 2 = k) :
    θ ∈ ratPi := by
  have sq0 : ∀ y : ℝ, y ^ 2 = 0 → y = 0 := fun y hy => (pow_eq_zero_iff two_ne_zero).1 hy
  have h2 := Real.cos_two_mul θ
  have hs := Real.sin_sq_add_cos_sq θ
  have key : ∀ c : ℝ, Real.cos (2 * θ) = c → 4 * c ^ 3 - 3 * c = 1 ∨ 4 * c ^ 3 - 3 * c = -1 →
      θ ∈ ratPi := by
    intro c hc h3
    have h6 : Real.cos (3 * (2 * θ)) = 4 * c ^ 3 - 3 * c := by rw [Real.cos_three_mul, hc]
    have hs6 := Real.sin_sq_add_cos_sq (3 * (2 * θ))
    have h0 : Real.sin (3 * (2 * θ)) = 0 := by
      apply sq0
      rcases h3 with e | e <;> rw [h6, e] at hs6 <;> linarith
    apply mem_ratPi_of_sin_nat_mul 6 (by norm_num)
    rw [show ((6 : ℕ) : ℝ) * θ = 3 * (2 * θ) by push_cast; ring]; exact h0
  interval_cases k
  · have hc : Real.cos θ = 0 := sq0 _ (by push_cast at h; linarith)
    apply mem_ratPi_of_sin_nat_mul 2 (by norm_num)
    rw [show ((2 : ℕ) : ℝ) * θ = 2 * θ by push_cast; ring, Real.sin_two_mul, hc, mul_zero]
  · exact key (-1 / 2) (by rw [h2]; push_cast at h; linarith) (Or.inl (by norm_num))
  · have hc : Real.cos (2 * θ) = 0 := by rw [h2]; push_cast at h; linarith
    apply mem_ratPi_of_sin_nat_mul 4 (by norm_num)
    rw [show ((4 : ℕ) : ℝ) * θ = 2 * (2 * θ) by push_cast; ring, Real.sin_two_mul, hc, mul_zero]
  · exact key (1 / 2) (by rw [h2]; push_cast at h; linarith) (Or.inr (by norm_num))
  · have hc : Real.sin θ = 0 := sq0 _ (by push_cast at h; linarith)
    apply mem_ratPi_of_sin_nat_mul 1 (by norm_num)
    rw [show ((1 : ℕ) : ℝ) * θ = θ by push_cast; ring]; exact hc

section general

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {ι : Type}

/-- Two vectors with 4⟪x, y⟫² = k ⟪x, x⟫ ⟪y, y⟫, k = 0, 1, 2, 3 or 4, make an angle that is a
rational
multiple of π (90°; 60° or 120°; 45° or 135°; 30° or 150°; 0° or 180°). -/
lemma angle_mem_ratPi_of_gram {x y : E} (hx : x ≠ 0) (hy : y ≠ 0) {k : ℕ} (hk : k ≤ 4)
    (h : 4 * ⟪x, y⟫ ^ 2 = k * (⟪x, x⟫ * ⟪y, y⟫)) : InnerProductGeometry.angle x y ∈ ratPi := by
  apply mem_ratPi_of_four_cos_sq hk
  have h1 := InnerProductGeometry.cos_angle_mul_norm_mul_norm x y
  have hxx : ⟪x, x⟫ = ‖x‖ ^ 2 := real_inner_self_eq_norm_sq x
  have hyy : ⟪y, y⟫ = ‖y‖ ^ 2 := real_inner_self_eq_norm_sq y
  have hpos : 0 < ‖x‖ ^ 2 * ‖y‖ ^ 2 := by
    have := norm_pos_iff.2 hx; have := norm_pos_iff.2 hy; positivity
  rw [← h1, hxx, hyy] at h
  have h0 : (4 * Real.cos (InnerProductGeometry.angle x y) ^ 2 - k) * (‖x‖ ^ 2 * ‖y‖ ^ 2) = 0 := by
    linear_combination h
  rcases mul_eq_zero.1 h0 with e | e
  · linarith
  · exact absurd e hpos.ne'

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fact (finrank ℝ E = 3)]

/-- **The angle class of a cone of constraints whose normals make rational angles is zero**, for any
number of constraints. -/
theorem theta_cone_eq_zero_of_rational [Finite ι] (a : ι → E) (A : Set ι) (hne : ∀ i, a i ≠ 0)
    (hang : ∀ i j, InnerProductGeometry.angle (a i) (a j) ∈ ratPi) : theta (cone a A) = 0 := by
  classical
  by_cases hfin : finrank ℝ (linCone a A) = 1
  swap
  · unfold theta; rw [linSpace_cone, ite_eq_right hfin]
  by_cases hv0 : ∃ v0, ∀ i ∈ A, ⟪a i, v0⟫ < 0
  · obtain ⟨v0, hv0⟩ := hv0
    obtain ⟨p, _, q, _, independent, cone_eq⟩ :=
      cone_eq_pair_of_strict a hfin (fun i hi _ => hv0 i hi)
    rw [cone_eq, theta_pair a rfl independent, Submodule.Quotient.mk_eq_zero]
    exact ratPi.sub_mem pi_mem_ratPi (hang p q)
  · push Not at hv0
    unfold theta
    rw [linSpace_cone, ite_eq_left hfin, Submodule.Quotient.mk_eq_zero]
    have hnull : volume (wedgeSet (cone a A) (linCone a A)) = 0 := by
      have hsub : wedgeSet (cone a A) (linCone a A) ⊆
          ⋃ i ∈ A, {w : (linCone a A)ᗮ | ⟪a i, (w : E)⟫ = 0} := by
        intro w hw
        obtain ⟨i, hi, h0⟩ := hv0 (w : E)
        exact mem_iUnion₂.2 ⟨i, hi, le_antisymm (hw.1 i hi) h0⟩
      apply measure_mono_null hsub
      rw [measure_biUnion_null_iff (Set.to_countable A)]
      intro i hi
      let normal : (linCone a A)ᗮ := ⟨a i, by
        rw [Submodule.mem_orthogonal']
        intro v hv
        exact hv i hi⟩
      let N : Submodule ℝ (linCone a A)ᗮ := (ℝ ∙ normal)ᗮ
      have hN : N ≠ ⊤ := by
        intro h
        have perpendicular : normal ∈ N := by rw [h]; trivial
        have zero : ⟪normal, normal⟫ = 0 :=
          Submodule.mem_orthogonal_singleton_iff_inner_right.1 perpendicular
        exact hne i (congrArg Subtype.val (inner_self_eq_zero.1 zero : normal = 0))
      have hset : {w : (linCone a A)ᗮ | ⟪a i, (w : E)⟫ = 0} = (N : Set (linCone a A)ᗮ) := by
        ext w
        exact (Submodule.mem_orthogonal_singleton_iff_inner_right (u := normal) (v := w)).symm
      rw [hset]
      exact Measure.addHaar_submodule volume N hN
    simp only [wedgeAngle_formula]
    rw [hnull]
    simp

/-- **Rational normals, zero invariant.** A solid cut out by finitely many half-spaces whose
normals make,
two by two, angles that are rational multiples of π has Dehn invariant zero, for all offsets `b`. -/
theorem dehnSet_sol_eq_zero_of_rational [Finite ι] (a : ι → E) (b : ι → ℝ) (hne : ∀ i, a i ≠ 0)
    (hang : ∀ i j, InnerProductGeometry.angle (a i) (a j) ∈ ratPi) : dehnSet (sol a b) = 0 := by
  have h0 : ∀ x, edgeAngle (sol a b) x = 0 := by
    intro x
    by_cases hx : x ∈ sol a b
    · rw [edgeAngle_sol a b hx]; exact theta_cone_eq_zero_of_rational a _ hne hang
    · exact edgeAngle_of_notMem hx
  rw [dehnSet_eq_single (sol a b) 0 (fun x => Or.inl (h0 x)), TensorProduct.tmul_zero]

end general

end DehnCanon.Library
