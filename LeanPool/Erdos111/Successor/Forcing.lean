/-
Copyright (c) 2026 Jacob Parish. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jacob Parish
-/

module

public import LeanPool.Erdos111.DerivedSign

/-!
# Forced signs

Over the previous set `M`, every vertex `y` of the set `X` of new vertices with infinite
trace carries derived-sign data from Lemma D. The forcing map replaces the sign of each
`y ∈ X` by the opposite of its derived sign and keeps every other sign. Under the law
`ν.map (forced X s)` the coordinates of `X` take exactly the forced values, the marginals
on `M` are those of `ν`, and every `y ∈ X` has trace energy at most `C`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal

namespace Erdos111

variable {V : Type*}

open Classical in
/-- Derived-sign data over `M` for the vertices of `X`, as given by Lemma D. -/
structure ForcingData (G : SimpleGraph V) (C : ℝ≥0) (M X : Set V)
    (ν : Measure (V → Bool)) where
  /-- The derived sign of each vertex. -/
  s : V → (V → Bool) → Bool
  /-- The enumerated neighbours in `M` that determine the derived sign. -/
  a : V → ℕ → V
  injective : ∀ y ∈ X, Function.Injective (a y)
  adj_mem : ∀ y ∈ X, ∀ n, G.Adj y (a y n) ∧ a y n ∈ M
  measurable : ∀ y ∈ X, Measurable (s y)
  ae_finite : ∀ y ∈ X, ∀ᵐ ω ∂ν, {n | ω (a y n) ≠ s y ω}.Finite
  sum_le : ∀ y ∈ X, ∀ B : Finset V, ↑B ⊆ {u | G.Adj y u ∧ u ∈ M} →
    ∑ u ∈ B, ν {ω | ω u ≠ s y ω} ≤ C

open Classical in
/-- Lemma D supplies forcing data for every set of vertices outside `M` with infinite
traces. -/
theorem exists_forcingData {G : SimpleGraph V} {C : ℝ≥0} {M X : Set V}
    {ν : Measure (V → Bool)} (hν : Rooted G C M ν)
    (hX : ∀ y ∈ X, y ∉ M ∧ {u | G.Adj y u ∧ u ∈ M}.Infinite) :
    Nonempty (ForcingData G C M X ν) := by
  have hD : ∀ y ∈ X, ∃ (s : (V → Bool) → Bool) (a : ℕ → V),
      Function.Injective a ∧ (∀ n, G.Adj y (a n) ∧ a n ∈ M) ∧
      DependsOn s (Set.range a) ∧ Measurable s ∧
      (∀ᵐ ω ∂ν, {n | ω (a n) ≠ s ω}.Finite) ∧
      ∀ B : Finset V, ↑B ⊆ {u | G.Adj y u ∧ u ∈ M} →
        ∑ u ∈ B, ν {ω | ω u ≠ s ω} ≤ C :=
    fun y hy => exists_derivedSign hν (hX y hy).1 (hX y hy).2
  refine ⟨{
    s := fun y => if h : y ∈ X then (hD y h).choose else fun _ => false
    a := fun y => if h : y ∈ X then (hD y h).choose_spec.choose else fun _ => y
    injective := fun y hy => ?_
    adj_mem := fun y hy => ?_
    measurable := fun y hy => ?_
    ae_finite := fun y hy => ?_
    sum_le := fun y hy => ?_ }⟩ <;>
  simp only [dite_eq_left hy]
  exacts [(hD y hy).choose_spec.choose_spec.1, (hD y hy).choose_spec.choose_spec.2.1,
    (hD y hy).choose_spec.choose_spec.2.2.2.1, (hD y hy).choose_spec.choose_spec.2.2.2.2.1,
    (hD y hy).choose_spec.choose_spec.2.2.2.2.2]

open Classical in
/-- The forcing map: each `y ∈ X` takes the opposite of its derived sign. -/
noncomputable def forced (X : Set V) (s : V → (V → Bool) → Bool) (ω : V → Bool) :
    V → Bool :=
  fun v => if v ∈ X then !s v ω else ω v

open Classical in
/-- The forcing map is measurable. -/
theorem measurable_forced {G : SimpleGraph V} {C : ℝ≥0} {M X : Set V}
    {ν : Measure (V → Bool)} (d : ForcingData G C M X ν) : Measurable (forced X d.s) := by
  refine Measurable.of_eval fun v => ?_
  by_cases hv : v ∈ X
  · simp only [forced, hv, ite_true]
    exact measurable_from_top.comp (d.measurable v hv)
  · simp only [forced, hv, ite_false]
    exact measurable_pi_apply v

open Classical in
/-- The forced law has the marginals of `ν` on `M`. -/
theorem sameOn_map_forced {G : SimpleGraph V} {C : ℝ≥0} {M X : Set V}
    {ν : Measure (V → Bool)} (d : ForcingData G C M X ν) (hXM : Disjoint X M) :
    SameOn M ν (ν.map (forced X d.s)) := by
  intro J hJ
  rw [Measure.map_map (Finset.measurable_restrict J) (measurable_forced d)]
  congr 1
  funext ω j
  have hj : (j : V) ∉ X := hXM.notMem_of_mem_right (hJ j.2)
  simp [Finset.restrict, forced, hj]

open Classical in
/-- Under the forced law every `y ∈ X` has trace energy at most `C` over its
neighbours in `M`. -/
theorem traceBound_map_forced {G : SimpleGraph V} {C : ℝ≥0} {M X : Set V}
    {ν : Measure (V → Bool)} (d : ForcingData G C M X ν) (hXM : Disjoint X M)
    {y : V} (hy : y ∈ X) :
    TraceBound C (ν.map (forced X d.s)) y {u | G.Adj y u ∧ u ∈ M} := by
  intro B hB
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun u hu => ?_)) (d.sum_le y hy B hB)
  have hu : u ∉ X := hXM.notMem_of_mem_right (hB hu).2
  rw [Measure.map_apply (measurable_forced d)
    (measurableSet_eq_fun (measurable_pi_apply u) (measurable_pi_apply y))]
  congr 1
  ext ω
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, forced, hu, hy, ite_true, ite_false,
    Bool.eq_not_iff]

end Erdos111
