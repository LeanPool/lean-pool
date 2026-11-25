/-
Copyright (c) 2026 DICTO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DICTO
-/

/- Modified for Lean Pool. -/

module

public import LeanPool.DehnInvariant.Dissection
public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.Tactic.FunProp

/-!
Lean study 2 of the shape-language canon (DICTO, 19 Nov 2026), part F: the link to study 1.

`dehnSet_eq_dehn_edgeList`: for a bounded polytope given by finitely many half-spaces, the Dehn
invariant of
the set (`dehnSet`, defined from the set alone) equals study 1's `dehn` of an explicit edge list
read off from
the half-spaces: one entry for every set `A` of constraints whose common direction space is a
line, with
length = the 1-dimensional Hausdorff measure of the points where exactly the constraints in `A`
hold with
equality, and angle = the angle of the cone of those constraints around that line.
No `sorry`.
-/

@[expose] public section

open scoped RealInnerProductSpace
open Set MeasureTheory Measure Module TensorProduct

namespace DehnCanon.Library

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ι : Type}

/-- The points of the polytope where exactly the constraints in `A` hold with equality
(a vertex, an open edge, an open face or the interior). -/
def faceSet (a : ι → E) (b : ι → ℝ) (A : Set ι) : Set E := {x | x ∈ sol a b ∧ act a b x = A}

/-- The edge list (length, angle) of a polytope read off from its half-spaces. -/
noncomputable def edgeList [Fintype ι] (a : ι → E) (b : ι → ℝ) : List (ℝ × ℝ) :=
  ((Finset.univ : Finset (Set ι)).filter fun A => finrank ℝ (linCone a A) = 1).toList.map
    fun A => ((μH[1] (faceSet a b A)).toReal, wedgeAngle (cone a A) (linCone a A))

/-- **The set invariant is study 1's edge-list invariant.** -/
theorem dehnSet_eq_dehn_edgeList [Fintype ι] (a : ι → E) (b : ι → ℝ)
    (hb : Bornology.IsBounded (sol a b)) : dehnSet (sol a b) = dehn (edgeList a b) := by
  classical
  let c' : E → Option (Set ι) := fun x => if x ∈ sol a b then some (act a b x) else none
  let φ : Option (Set ι) → Angle := fun o => o.elim 0 (fun A => theta (cone a A))
  have hc'1 : ∀ x, x ∈ sol a b → c' x = some (act a b x) := fun x hx => ite_eq_left hx
  have hc'2 : ∀ x, x ∉ sol a b → c' x = none := fun x hx => ite_eq_right hx
  have hφ : edgeAngle (sol a b) = φ ∘ c' := by
    funext x
    change _ = φ (c' x)
    by_cases hx : x ∈ sol a b
    · rw [hc'1 x hx]; exact edgeAngle_sol a b hx
    · rw [hc'2 x hx]; exact edgeAngle_of_notMem hx
  have hsolm : MeasurableSet (sol a b) := (isClosed_sol a b).measurableSet
  have hactm : ∀ A : Set ι, MeasurableSet {x : E | act a b x = A} := by
    intro A
    have h : {x : E | act a b x = A} = ⋂ i, {x : E | ⟪a i, x⟫ = b i ↔ i ∈ A} := by
      ext x
      simp only [mem_ofPred_eq, mem_iInter]
      constructor
      · intro h i; rw [← h]; rfl
      · intro h; ext i; exact h i
    rw [h]
    refine MeasurableSet.iInter fun i => ?_
    have hcl : MeasurableSet {x : E | ⟪a i, x⟫ = b i} :=
      (isClosed_eq (by fun_prop) continuous_const).measurableSet
    by_cases hi : i ∈ A
    · have h2 : {x : E | ⟪a i, x⟫ = b i ↔ i ∈ A} = {x : E | ⟪a i, x⟫ = b i} := by
        ext x; simp [hi]
      rw [h2]; exact hcl
    · have h2 : {x : E | ⟪a i, x⟫ = b i ↔ i ∈ A} = {x : E | ⟪a i, x⟫ = b i}ᶜ := by
        ext x; simp [hi]
      rw [h2]; exact hcl.compl
  have hfib : ∀ A : Set ι, c' ⁻¹' {some A} = faceSet a b A := by
    intro A; ext x
    change c' x = some A ↔ x ∈ sol a b ∧ act a b x = A
    by_cases hx : x ∈ sol a b
    · rw [hc'1 x hx]; simp [hx]
    · rw [hc'2 x hx]; simp [hx]
  have hfibn : c' ⁻¹' {none} = (sol a b)ᶜ := by
    ext x
    change c' x = none ↔ x ∉ sol a b
    by_cases hx : x ∈ sol a b
    · rw [hc'1 x hx]; simp [hx]
    · rw [hc'2 x hx]; simp [hx]
  have hc : ∀ k, MeasurableSet (c' ⁻¹' {k}) := by
    intro k
    cases k with
    | none => rw [hfibn]; exact hsolm.compl
    | some A =>
      rw [hfib]
      change MeasurableSet (sol a b ∩ {x | act a b x = A})
      exact hsolm.inter (hactm A)
  have hfin : ∀ k, φ k ≠ 0 → μH[1] (c' ⁻¹' {k}) ≠ ⊤ := by
    intro k hk
    refine ((measure_mono ?_).trans_lt (support_finite a b hb).lt_top).ne
    intro x hx
    have hx' : c' x = k := hx
    change edgeAngle (sol a b) x ≠ 0
    rw [hφ]
    change φ (c' x) ≠ 0
    rw [hx']; exact hk
  have h1 : dehnSet (sol a b) = ∑ k, (μH[1] (c' ⁻¹' {k})).toReal ⊗ₜ[ℚ] φ k := by
    change tsum1 μH[1] (edgeAngle (sol a b)) = _
    rw [hφ]; exact tsum1_eq_sum μH[1] c' hc φ hfin
  rw [h1, Fintype.sum_option]
  have hnone : (μH[1] (c' ⁻¹' {none})).toReal ⊗ₜ[ℚ] φ none = 0 := TensorProduct.tmul_zero _ _
  rw [hnone, zero_add]
  unfold dehn edgeList
  rw [List.map_map, Finset.sum_map_toList, Finset.sum_filter]
  apply Finset.sum_congr rfl; intro A _
  change (μH[1] (c' ⁻¹' {some A})).toReal ⊗ₜ[ℚ] theta (cone a A) = _
  rw [hfib]
  unfold theta
  rw [linSpace_cone]
  by_cases h : finrank ℝ (linCone a A) = 1
  · rw [ite_eq_left h, ite_eq_left h]; rfl
  · rw [ite_eq_right h, ite_eq_right h, TensorProduct.tmul_zero]

end DehnCanon.Library
