/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson
-/

module

public import LeanPool.ScottMeasurement.Probability.Atoms
public import LeanPool.ScottMeasurement.LinearInequalities.ScottTheorems

/-!
# Finite qualitative probability

This file isolates the last step of Scott's proof: a separating functional on
atom vectors is normalized to a finitely additive probability.
-/

@[expose] public section

namespace Scott1964.MeasurementStructures

open scoped BigOperators

noncomputable section

open LinearInequalities

/-- Linear-functional representation of a qualitative relation on event
characteristic vectors. -/
def AtomLinearRepresentation {B : Type u} [BooleanAlgebra B]
    (R : B → B → Prop) : Prop :=
  ∃ φ : ({a : B // IsAtom a} → ℝ) →ₗ[ℝ] ℝ,
    ∀ x y, R x y ↔ φ (atomVector x) ≥ φ (atomVector y)

open Classical in
/-- Integration of atom vectors against the atom masses of a finite
probability. -/
def atomWeightFunctional {B : Type u} [BooleanAlgebra B] [Fintype B]
    (μ : B → ℝ) : ({a : B // IsAtom a} → ℝ) →ₗ[ℝ] ℝ where
  toFun v := ∑ a, v a * μ a
  map_add' u v := by
    classical
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c v := by
    classical
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    symm
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    ring

open Classical in
@[simp]
theorem atomWeightFunctional_apply
    {B : Type u} [BooleanAlgebra B] [Fintype B] (μ : B → ℝ)
    (v : {a : B // IsAtom a} → ℝ) :
    atomWeightFunctional μ v = ∑ a, v a * μ a :=
  rfl

theorem atomWeightFunctional_atomVector
    {B : Type u} [BooleanAlgebra B] [Fintype B]
    {μ : B → ℝ} (hμ : IsProbability μ) (x : B) :
    atomWeightFunctional μ (atomVector x) = μ x := by
  classical
  rw [hμ.eq_sum_atoms x]
  simp only [atomWeightFunctional_apply, atomVector_apply, atomsBelow]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases hax : (a : B) ≤ x <;> simp [hax]

/-- Atom-weight integration also recovers an arbitrary signed charge. -/
theorem atomWeightFunctional_atomVector_signed
    {B : Type u} [BooleanAlgebra B] [Fintype B]
    {μ : B → ℝ} (hμ : IsSignedCharge μ) (x : B) :
    atomWeightFunctional μ (atomVector x) = μ x := by
  classical
  rw [hμ.eq_sum_atoms x]
  simp only [atomWeightFunctional_apply, atomVector_apply, atomsBelow]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases hax : (a : B) ≤ x <;> simp [hax]

theorem RealizableProbability.atomLinearRepresentation
    {B : Type u} [BooleanAlgebra B] [Finite B]
    {R : B → B → Prop} (hR : RealizableProbability R) :
    AtomLinearRepresentation R := by
  classical
  let := Fintype.ofFinite B
  rcases hR with ⟨μ, hμ, hrep⟩
  refine ⟨atomWeightFunctional μ, ?_⟩
  intro x y
  rw [atomWeightFunctional_atomVector hμ,
    atomWeightFunctional_atomVector hμ]
  exact hrep x y

theorem RealizableSignedCharge.atomLinearRepresentation
    {B : Type u} [BooleanAlgebra B] [Finite B]
    {R : B → B → Prop} (hR : RealizableSignedCharge R) :
    AtomLinearRepresentation R := by
  classical
  let := Fintype.ofFinite B
  rcases hR with ⟨μ, hμ, hrep⟩
  refine ⟨atomWeightFunctional μ, ?_⟩
  intro x y
  rw [atomWeightFunctional_atomVector_signed hμ,
    atomWeightFunctional_atomVector_signed hμ]
  exact hrep x y

/-- A linear representation on atom vectors induces a signed charge directly.
No division by the charge of `⊤` is needed. -/
theorem signedCharge_of_atomLinearRepresentation
    {B : Type u} [BooleanAlgebra B] {R : B → B → Prop}
    (hR : AtomLinearRepresentation R) :
    RealizableSignedCharge R := by
  classical
  rcases hR with ⟨φ, hrep⟩
  let μ : B → ℝ := fun x ↦ φ (atomVector x)
  refine ⟨μ, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · simp [μ, atomVector_bot]
    · intro x y hxy
      simp only [μ, atomVector_sup_of_disjoint hxy, map_add]
  · exact hrep

/-- A nondegenerate atom-functional representation normalizes to a finitely
additive probability without changing any comparisons. -/
theorem probability_of_atomLinearRepresentation {B : Type u} [BooleanAlgebra B]
    {R : B → B → Prop}
    (hR : AtomLinearRepresentation R)
    (hnt : ProbNontrivial R) (hn : ProbNonneg R) :
    RealizableProbability R := by
  classical
  rcases hR with ⟨φ, hrep⟩
  have hbot : φ (atomVector (⊥ : B)) = 0 := by rw [atomVector_bot, map_zero]
  have htop : φ (atomVector (⊤ : B)) > 0 := by
    classical
    have hge := (hrep ⊤ ⊥).1 hnt.1
    have hnle := fun h ↦ hnt.2 ((hrep ⊥ ⊤).2 h)
    rw [hbot] at hge hnle
    exact lt_of_not_ge hnle
  let μ : B → ℝ := fun x ↦ φ (atomVector x) / φ (atomVector (⊤ : B))
  refine ⟨μ, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · simp [μ, atomVector_bot]
    · simp [μ, ne_of_gt htop]
    · intro x y hxy
      change φ (atomVector (x ⊔ y)) / φ (atomVector (⊤ : B)) =
        φ (atomVector x) / φ (atomVector (⊤ : B)) +
          φ (atomVector y) / φ (atomVector (⊤ : B))
      rw [atomVector_sup_of_disjoint hxy, map_add, add_div]
    · intro x
      have hx := (hrep x ⊥).1 (hn x)
      rw [hbot] at hx
      exact div_nonneg hx htop.le
  · intro x y
    rw [hrep]
    change φ (atomVector y) ≤ φ (atomVector x) ↔
      φ (atomVector y) / φ (atomVector (⊤ : B)) ≤
        φ (atomVector x) / φ (atomVector (⊤ : B))
    exact (div_le_div_iff_of_pos_right htop).symm

/-- Condition `(2_B)` makes the normalized signed measure nonnegative. -/
theorem nonnegative_probability_of_atomLinearRepresentation
    {B : Type u} [BooleanAlgebra B] {R : B → B → Prop}
    (hR : AtomLinearRepresentation R) (hnt : ProbNontrivial R)
    (hn : ProbNonneg R) :
    ∃ μ : B → ℝ, IsFinitelyAdditiveProbability μ ∧
      ∀ x y, R x y ↔ μ x ≥ μ y :=
  probability_of_atomLinearRepresentation hR hnt hn

open Classical in
/-- Every atom-functional representation satisfies Scott's cancellation
scheme.  This is the easy direction of the finite separation theorem. -/
theorem AtomLinearRepresentation.cancellation
    {B : Type u} [BooleanAlgebra B]
    {R : B → B → Prop} (hR : AtomLinearRepresentation R) :
    ∀ (n : ℕ) (x y : Fin (n + 1) → B),
      (∀ a : B, IsAtom a →
        (∑ i, if a ≤ x i then 1 else 0) =
          (∑ i, if a ≤ y i then 1 else 0 : ℕ)) →
      (∀ i, i ≠ finHead n → R (x i) (y i)) →
        R (y (finHead n)) (x (finHead n)) := by
  classical
  rcases hR with ⟨φ, hrep⟩
  intro n x y hcount hweak
  have hvectors :
      (∑ i, atomVector (x i)) = ∑ i, atomVector (y i) :=
    (sum_atomVector_eq_iff (n + 1) x y).2 hcount
  have hsums :
      ∑ i, φ (atomVector (x i)) = ∑ i, φ (atomVector (y i)) := by
    classical
    simpa only [map_sum] using congrArg φ hvectors
  have hrest :
      ∑ i ∈ (Finset.univ.erase (finHead n)),
          φ (atomVector (y i)) ≤
        ∑ i ∈ (Finset.univ.erase (finHead n)),
          φ (atomVector (x i)) := by
    classical
    apply Finset.sum_le_sum
    intro i hi
    have hi0 : i ≠ finHead n := by simpa using (Finset.mem_erase.mp hi).1
    exact (hrep (x i) (y i)).1 (hweak i hi0)
  apply (hrep (y (finHead n)) (x (finHead n))).2
  have hzero : finHead n ∈ Finset.univ := Finset.mem_univ _
  have hx := Finset.sum_erase_add _ (fun i ↦ φ (atomVector (x i))) hzero
  have hy := Finset.sum_erase_add _ (fun i ↦ φ (atomVector (y i))) hzero
  linarith

theorem AtomLinearRepresentation.probCancellation
    {B : Type u} [BooleanAlgebra B]
    {R : B → B → Prop} (hR : AtomLinearRepresentation R) :
    ProbCancellation R :=
  hR.cancellation

/-- The atom-count formulation can equivalently be supplied as an equality
of sums of characteristic vectors. -/
theorem ProbCancellation.of_atomVector_sum
    {B : Type u} [BooleanAlgebra B]
    {R : B → B → Prop} (hR : ProbCancellation R)
    (n : ℕ) (x y : Fin (n + 1) → B)
    (hsum : (∑ i, atomVector (x i)) = ∑ i, atomVector (y i))
    (hweak : ∀ i, i ≠ finHead n → R (x i) (y i)) :
    R (y (finHead n)) (x (finHead n)) :=
  hR n x y ((sum_atomVector_eq_iff (n + 1) x y).1 hsum) hweak

/-- Scott cancellation alone implies reflexivity. -/
theorem ProbCancellation.refl
    {B : Type u} [BooleanAlgebra B]
    {R : B → B → Prop} (hR : ProbCancellation R) (x : B) :
    R x x := by
  classical
  apply hR.of_atomVector_sum 0 (fun _ ↦ x) (fun _ ↦ x)
  · rfl
  · intro i hi
    exact False.elim (hi (by simpa [finHead_eq_zero] using Fin.eq_zero i))

/-- Scott cancellation implies de Finetti transitivity. -/
theorem ProbCancellation.transitive
    {B : Type u} [BooleanAlgebra B]
    {R : B → B → Prop} (hR : ProbCancellation R) :
    ProbTransitive R := by
  classical
  intro x y z hxy hyz
  let xs : Fin 3 → B := ![z, x, y]
  let ys : Fin 3 → B := ![x, y, z]
  apply hR.of_atomVector_sum 2 xs ys
  · simp [xs, ys, Fin.sum_univ_succ]
    abel
  · intro i hi
    fin_cases i
    · exact False.elim (hi (finHead_eq_zero _).symm)
    · exact hxy
    · exact hyz

/-- Scott cancellation gives both directions of de Finetti's invariance
under adjoining a common disjoint event. -/
theorem ProbCancellation.disjointUnionInvariant
    {B : Type u} [BooleanAlgebra B]
    {R : B → B → Prop} (hR : ProbCancellation R) :
    ProbDisjointUnionInvariant R := by
  classical
  intro x y z hzx hzy
  have hxz : atomVector (x ⊔ z) = atomVector x + atomVector z :=
    atomVector_sup_of_disjoint hzx.symm
  have hyz : atomVector (y ⊔ z) = atomVector y + atomVector z :=
    atomVector_sup_of_disjoint hzy.symm
  constructor
  · intro hxy
    let xs : Fin 2 → B := ![y ⊔ z, x]
    let ys : Fin 2 → B := ![x ⊔ z, y]
    apply hR.of_atomVector_sum 1 xs ys
    · simp [xs, ys, Fin.sum_univ_succ, hxz, hyz]
      abel
    · intro i hi
      fin_cases i
      · exact False.elim (hi (finHead_eq_zero _).symm)
      · exact hxy
  · intro hxy
    let xs : Fin 2 → B := ![y, x ⊔ z]
    let ys : Fin 2 → B := ![x, y ⊔ z]
    apply hR.of_atomVector_sum 1 xs ys
    · simp [xs, ys, Fin.sum_univ_succ, hxz, hyz]
      abel
    · intro i hi
      fin_cases i
      · exact False.elim (hi (finHead_eq_zero _).symm)
      · exact hxy

/-! ## Reduction to Scott's explicit §1 relation theorem -/

open Classical in
/-- The event represented by an atom vector in the range of `atomVector`.
Outside that range its value is immaterial. -/
def eventOfAtomVector {B : Type u} [BooleanAlgebra B]
    (v : {a : B // IsAtom a} → ℝ) : B :=
  if h : ∃ x, atomVector x = v then Classical.choose h else ⊥

@[simp]
theorem eventOfAtomVector_atomVector
    {B : Type u} [BooleanAlgebra B] [Finite B] (x : B) :
    eventOfAtomVector (atomVector x) = x := by
  classical
  let := Fintype.ofFinite B
  unfold eventOfAtomVector
  split
  · rename_i h
    exact atomVector_injective (Classical.choose_spec h)
  · rename_i h
    exact False.elim (h ⟨x, rfl⟩)

/-- The relation transported from events to their characteristic vectors. -/
def AtomVectorRelation {B : Type u} [BooleanAlgebra B]
    (R : B → B → Prop)
    (u v : {a : B // IsAtom a} → ℝ) : Prop :=
  R (eventOfAtomVector u) (eventOfAtomVector v)

@[simp]
theorem atomVectorRelation_atomVectors
    {B : Type u} [BooleanAlgebra B] [Finite B]
    (R : B → B → Prop) (x y : B) :
    AtomVectorRelation R (atomVector x) (atomVector y) ↔ R x y := by
  classical
  let := Fintype.ofFinite B
  simp [AtomVectorRelation]

theorem atomVector_range_finite
    {B : Type u} [BooleanAlgebra B] [Finite B] :
    (Set.range (atomVector :
      B → ({a : B // IsAtom a} → ℝ))).Finite := by
  classical
  let := Fintype.ofFinite B
  exact Set.finite_range _

theorem atomVector_range_rational
    {B : Type u} [BooleanAlgebra B] :
    IsRationalSet (Set.range (atomVector :
      B → ({a : B // IsAtom a} → ℝ))) := by
  classical
  rintro v ⟨x, rfl⟩ a
  by_cases h : (a : B) ≤ x
  · exact ⟨1, by simp [atomVector, h]⟩
  · exact ⟨0, by simp [atomVector, h]⟩

theorem atomVectorRelation_complete
    {B : Type u} [BooleanAlgebra B] [Finite B]
    {R : B → B → Prop} (hR : ProbTotal R) :
    RelationComplete
      (Set.range (atomVector :
        B → ({a : B // IsAtom a} → ℝ)))
      (AtomVectorRelation R) := by
  classical
  let := Fintype.ofFinite B
  rintro u ⟨x, rfl⟩ v ⟨y, rfl⟩
  simpa only [atomVectorRelation_atomVectors] using hR x y

theorem atomVectorRelation_sequenceCancellation
    {B : Type u} [BooleanAlgebra B] [Finite B]
    {R : B → B → Prop} (hR : ProbCancellation R) :
    RelationSequenceCancellation
      (Set.range (atomVector :
        B → ({a : B // IsAtom a} → ℝ)))
      (AtomVectorRelation R) := by
  classical
  intro n u v hu hv huv hsum j
  let e : Equiv.Perm (Fin (n + 1)) := Equiv.swap (finHead n) j
  let x : Fin (n + 1) → B := fun i ↦ eventOfAtomVector (u (e i))
  let y : Fin (n + 1) → B := fun i ↦ eventOfAtomVector (v (e i))
  have hxu : ∀ i, atomVector (x i) = u (e i) := by
    classical
    intro i
    rcases hu (e i) with ⟨xi, hxi⟩
    change atomVector (eventOfAtomVector (u (e i))) = u (e i)
    rw [← hxi]
    simp
  have hyv : ∀ i, atomVector (y i) = v (e i) := by
    classical
    intro i
    rcases hv (e i) with ⟨yi, hyi⟩
    change atomVector (eventOfAtomVector (v (e i))) = v (e i)
    rw [← hyi]
    simp
  change R (eventOfAtomVector (v j)) (eventOfAtomVector (u j))
  apply hR.of_atomVector_sum n x y
  · simp only [hxu, hyv]
    rw [Equiv.sum_comp e, Equiv.sum_comp e, hsum]
  · intro i hi
    change R (eventOfAtomVector (u (e i))) (eventOfAtomVector (v (e i)))
    exact huv (e i)

theorem atomLinearRepresentation_of_relationRealizable
    {B : Type u} [BooleanAlgebra B] [Finite B]
    {R : B → B → Prop}
    (hreal : RelationRealizable
      (Set.range (atomVector :
        B → ({a : B // IsAtom a} → ℝ)))
      (AtomVectorRelation R)) :
    AtomLinearRepresentation R := by
  classical
  let := Fintype.ofFinite B
  rcases hreal with ⟨φ, hφ⟩
  refine ⟨φ, ?_⟩
  intro x y
  simpa only [atomVectorRelation_atomVectors] using
    hφ (atomVector x) (Set.mem_range_self x)
      (atomVector y) (Set.mem_range_self y)

/-- Scott's `(3_B)` and `(4_B)` produce a linear representation on atom
vectors, without any positivity or nondegeneracy assumptions. -/
theorem atomLinearRepresentation_of_total_cancellation
    {B : Type u} [BooleanAlgebra B] [Finite B]
    {R : B → B → Prop}
    (htotal : ProbTotal R) (hcancel : ProbCancellation R) :
    AtomLinearRepresentation R := by
  classical
  have hreal : RelationRealizable
      (Set.range (atomVector :
        B → ({a : B // IsAtom a} → ℝ)))
      (AtomVectorRelation R) :=
    (scott_theorem_1_3 atomVector_range_finite atomVector_range_rational).2
      ⟨atomVectorRelation_complete htotal,
        atomVectorRelation_sequenceCancellation hcancel⟩
  exact atomLinearRepresentation_of_relationRealizable hreal

theorem RealizableProbability.probCancellation
    {B : Type u} [BooleanAlgebra B] [Finite B]
    {R : B → B → Prop} (hR : RealizableProbability R) :
    ProbCancellation R :=
  hR.atomLinearRepresentation.probCancellation

theorem RealizableProbability.finiteNecessary
    {B : Type u} [BooleanAlgebra B] [Finite B]
    {R : B → B → Prop} (hR : RealizableProbability R) :
    ProbNontrivial R ∧ ProbNonneg R ∧ ProbTotal R ∧ ProbCancellation R :=
  ⟨hR.probNontrivial, hR.probNonneg, hR.probTotal, hR.probCancellation⟩

theorem RealizableSignedCharge.finiteNecessary
    {B : Type u} [BooleanAlgebra B] [Finite B]
    {R : B → B → Prop} (hR : RealizableSignedCharge R) :
    ProbTotal R ∧ ProbCancellation R := by
  classical
  have hlin := hR.atomLinearRepresentation
  constructor
  · rcases hlin with ⟨φ, hrep⟩
    intro x y
    exact (le_total (φ (atomVector y)) (φ (atomVector x))).imp
      ((hrep x y).2) ((hrep y x).2)
  · exact hlin.probCancellation

/-- Scott's p.15 signed-measure claim: `(3_B)` and `(4_B)` are exactly the
conditions for representation by a finitely additive signed charge. -/
theorem scott_p15_signed_charge
    {B : Type u} [BooleanAlgebra B] [Finite B]
    (R : B → B → Prop) :
    RealizableSignedCharge R ↔ ProbTotal R ∧ ProbCancellation R := by
  classical
  constructor
  · exact RealizableSignedCharge.finiteNecessary
  · rintro ⟨htotal, hcancel⟩
    exact signedCharge_of_atomLinearRepresentation
      (atomLinearRepresentation_of_total_cancellation htotal hcancel)

/-- Scott's p.15 claim with literal vector-sum cancellation `(4_B)`. -/
theorem scott_p15_signed_charge_vector
    {B : Type u} [BooleanAlgebra B] [Finite B]
    (R : B → B → Prop) :
    RealizableSignedCharge R ↔ ProbTotal R ∧ ProbVectorCancellation R := by
  classical
  let := Fintype.ofFinite B
  rw [scott_p15_signed_charge,
    probVectorCancellation_iff_probCancellation]

theorem probability_of_finite_axioms
    {B : Type u} [BooleanAlgebra B] [Finite B]
    {R : B → B → Prop}
    (hnt : ProbNontrivial R) (hn : ProbNonneg R)
    (htotal : ProbTotal R) (hcancel : ProbCancellation R) :
    RealizableProbability R := by
  classical
  have hreal : RelationRealizable
      (Set.range (atomVector :
        B → ({a : B // IsAtom a} → ℝ)))
      (AtomVectorRelation R) :=
    (scott_theorem_1_3 atomVector_range_finite atomVector_range_rational).2
      ⟨atomVectorRelation_complete htotal,
        atomVectorRelation_sequenceCancellation hcancel⟩
  exact probability_of_atomLinearRepresentation
    (atomLinearRepresentation_of_relationRealizable hreal) hnt hn

/-- **Scott 1964, Theorem 4.1 (subjective probability).** -/
theorem theorem_4_1 {B : Type u} [BooleanAlgebra B] [Finite B]
    (R : B → B → Prop) :
    RealizableProbability R ↔
      ProbNontrivial R ∧ ProbNonneg R ∧ ProbTotal R ∧ ProbCancellation R := by
  classical
  constructor
  · exact RealizableProbability.finiteNecessary
  · rintro ⟨hnt, hn, htotal, hcancel⟩
    exact probability_of_finite_axioms hnt hn htotal hcancel

/-- **Scott 1964, Theorem 4.1**, with `(4_B)` stated literally as equality
of sums of atom vectors. -/
theorem theorem_4_1_vector {B : Type u} [BooleanAlgebra B] [Finite B]
    (R : B → B → Prop) :
    RealizableProbability R ↔
      ProbNontrivial R ∧ ProbNonneg R ∧ ProbTotal R ∧
        ProbVectorCancellation R := by
  classical
  let := Fintype.ofFinite B
  rw [theorem_4_1, probVectorCancellation_iff_probCancellation]

end

end Scott1964.MeasurementStructures
