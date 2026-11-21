/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import LeanPool.LeanQuantumAlg.Primitives.QKernel.DiscreteLogConcept
public import Mathlib.Algebra.Group.TypeTags.Finite
/-!
# Quantum-kernel learning advantage (Liu, Arunachalam, Temme 2021)

A *conditional separation* over the discrete-log concept class, stated over a bundle of assumed
hypotheses. DLP hardness is modelled by an opaque proposition `ClassicalSolvesDLP` together with
its negation `dlpHard`; neither is a statement about the discrete-logarithm problem itself, and a
bundle may take `ClassicalSolvesDLP := False`. The reduction (an above-chance classical learner
for `f_1` yields `ClassicalSolvesDLP`) and the 99% SVM-QKE accuracy floor are likewise assumed
fields citing Liu, not axioms. Given these, the classical accuracy ceiling follows by a
contrapositive whose only proved ingredient is the secret-homogeneity `acc_shift` (in
`LeanPool.LeanQuantumAlg.Primitives.QKernel.DiscreteLogConcept`).

The expressivity (density-matrix EQK realization) half lives in
`LeanPool.LeanQuantumAlg.Primitives.QKernel.Expressivity`; the fidelity-kernel PSD foundation is in
`LeanPool.LeanQuantumAlg.Primitives.QKernel.Fidelity`.

Source: Liu, Arunachalam, Temme (2021), *A rigorous and robust quantum speed-up in supervised
machine learning*.
-/

@[expose] public section

namespace QuantumAlg

/-- Hypothesis bundle for the quantum-kernel learning advantage (Liu, Arunachalam, Temme
2021) over the discrete-log concept class on a finite cyclic group `G`. Given the bundle, the
classical ceiling follows by a contrapositive that consumes the proved secret-homogeneity
`acc_shift`: a learner beating `1/2 + ε`, transported to the fixed concept `f_1`, would
satisfy the reduction's premise.

The crypto/learning facts are assumed fields citing Liu (not axioms): `ClassicalSolvesDLP` is
an arbitrary proposition with `dlpHard : ¬ ClassicalSolvesDLP` (it is not tied to the
discrete-log problem; `False` is an admissible choice), `singleConceptReduction` (the
efficient reduction; its algebraic step is the proved `dlogConcept_reduction`), and
`quantumFloor` (the SVM-QKE margin generalization). -/
structure QuantumKernelAdvantage (G : Type*) [Group G] [Fintype G] [IsCyclic G] where
  /-- A generator of the cyclic group. -/
  g : G
  /-- `g` generates `G`. -/
  hg : ∀ x, x ∈ Subgroup.zpowers g
  /-- The classical advantage gap above chance that is provably unreachable. -/
  ε : ℝ
  /-- The gap is positive. -/
  hε : 0 < ε
  /-- The chance ceiling stays strictly below the quantum floor. -/
  hε_lt : 1 / 2 + ε < 99 / 100
  /-- An opaque proposition standing for "the discrete-log problem is classically easy". -/
  ClassicalSolvesDLP : Prop
  /-- **DLP hardness** (Liu Thm 1 assumption): no efficient classical DLP solver. -/
  dlpHard : ¬ ClassicalSolvesDLP
  /-- The classical learner under scrutiny. -/
  classicalPredictor : G → Bool
  /-- The secret labelling the learner targets. -/
  classicalSecret : ZMod (Nat.card G)
  /-- The learner's (uniform) test accuracy. -/
  classicalAcc : ℝ
  /-- The accuracy is the uniform agreement with the concept `f_{classicalSecret}`. -/
  classicalAcc_def : classicalAcc = acc g hg classicalPredictor classicalSecret
  /-- **The reduction** (Liu Thm 1): an above-chance learner for the fixed concept `f_1`
  yields an efficient DLP solver. Its algebraic step is `dlogConcept_reduction`. -/
  singleConceptReduction :
    (1 / 2 + ε <
      acc g hg (fun y => classicalPredictor (y * gpow g hg (classicalSecret - 1))) 1)
      → ClassicalSolvesDLP
  /-- The quantum-kernel SVM's accuracy. -/
  quantumAcc : ℝ
  /-- **Quantum floor** (Liu Thm 2): the SVM with quantum-kernel estimation is highly
  accurate (margin generalization). -/
  quantumFloor : (99 : ℝ) / 100 ≤ quantumAcc

/-- **Classical accuracy ceiling** from the bundle: given the assumed `dlpHard` and reduction,
the classical learner cannot beat `1/2 + ε`. The proof transports the learner to the fixed
concept via `acc_shift` and applies the reduction, contradicting `dlpHard`. -/
theorem QuantumKernelAdvantage.classical_ceiling {G : Type*} [Group G] [Fintype G] [IsCyclic G]
    (M : QuantumKernelAdvantage G) : M.classicalAcc ≤ 1 / 2 + M.ε := by
  by_contra h
  push Not at h
  refine M.dlpHard (M.singleConceptReduction ?_)
  rw [acc_shift, ← M.classicalAcc_def]
  exact h

/-- Under the bundle's assumed hypotheses, the quantum-kernel learner's accuracy strictly
exceeds that of the bundled classical learner. -/
theorem QuantumKernelAdvantage.separation {G : Type*} [Group G] [Fintype G] [IsCyclic G]
    (M : QuantumKernelAdvantage G) : M.classicalAcc < M.quantumAcc :=
  lt_of_le_of_lt M.classical_ceiling (lt_of_lt_of_le M.hε_lt M.quantumFloor)

/-- The conditional-separation hypotheses are jointly satisfiable: a concrete
`QuantumKernelAdvantage` on the order-2 cyclic group, with an always-wrong classical predictor
(`acc = 0`), so the reduction's premise is false and the bundle is consistent with `dlpHard`. -/
theorem qka_nonempty : Nonempty (QuantumKernelAdvantage (Multiplicative (ZMod 2))) := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Multiplicative (ZMod 2))
  refine ⟨{
    g := g, hg := hg, ε := 1 / 100, hε := by norm_num, hε_lt := by norm_num
    ClassicalSolvesDLP := False, dlpHard := not_false
    classicalPredictor := fun x => !(dlogConcept g hg 1 x)
    classicalSecret := 1
    classicalAcc := acc g hg (fun x => !(dlogConcept g hg 1 x)) 1
    classicalAcc_def := rfl
    singleConceptReduction := ?_
    quantumAcc := 1, quantumFloor := by norm_num }⟩
  intro h
  -- the shift `1 - 1 = 0` makes `gpow … = 1`, so the shifted predictor is the original
  simp only [sub_self, gpow_zero, mul_one] at h
  have hfilt : (Finset.univ.filter
      (fun x => (!(dlogConcept g hg 1 x)) = dlogConcept g hg 1 x)) = ∅ :=
    Finset.filter_eq_empty_iff.mpr (fun x _ => by cases dlogConcept g hg 1 x <;> simp)
  have hz : acc g hg (fun x => !(dlogConcept g hg 1 x)) 1 = 0 := by
    simp only [acc, hfilt, Finset.card_empty, Nat.cast_zero, zero_div]
  rw [hz] at h
  norm_num at h

end QuantumAlg
