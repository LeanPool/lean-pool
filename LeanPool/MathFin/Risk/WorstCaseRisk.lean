/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Risk.AcceptanceSet

/-!
# Worst-case loss: a concrete coherent risk measure

The most conservative coherent risk measure of losses, `worstCase L = maxᵢ Lᵢ`, is a concrete
instance of `IsCoherentRiskMeasure` on a finite state space under any measure that charges every
state (so almost-sure order is the pointwise order); counting measure is the model case. Its
Artzner–Delbaen–Eber–Heath representation (from `coherentRisk_isLUB`) specialises to the supremum of
expected loss over the *entire* probability simplex — making the abstract representation tangible:
the worst case over states equals the worst case over all mixtures of states.

## Main definitions

* `worstCase`: the worst-case loss `maxᵢ Lᵢ` over a finite nonempty state space.

## Main results

* `MathFin.worstCase_isCoherent` — under a measure charging every state, worst-case loss
  satisfies the four ADEH axioms
* `MathFin.worstCase_isLUB` — its representation is the sup over the probability simplex

## References

* [P. Artzner et al., *Coherent measures of risk*][ArtznerDelbaenEberHeath1999]

## Tags

worst-case loss, maximum loss, coherent risk measure, scenario-based risk,
representation over simplex, MSC 91G70, JEL G32
-/

@[expose] public section

namespace MathFin

open MeasureTheory

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- Worst-case loss: the most conservative coherent risk measure. -/
noncomputable def worstCase (L : ι → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty L

/-- Each `Lᵢ` lower-bounds the worst-case loss `worstCase L`. -/
lemma le_worstCase (L : ι → ℝ) (i : ι) : L i ≤ worstCase L :=
  Finset.le_sup' L (Finset.mem_univ i)

/-- Any uniform upper bound on the `Lᵢ` bounds `worstCase L` above. -/
lemma worstCase_le {L : ι → ℝ} {a : ℝ} (h : ∀ i, L i ≤ a) : worstCase L ≤ a :=
  Finset.sup'_le Finset.univ_nonempty L fun i _ ↦ h i

/-- Worst-case loss satisfies the four ADEH coherent-risk axioms for any measure on the states
that charges every state: the maximum does not see the weights, only which states are possible. -/
lemma worstCase_isCoherent [MeasurableSpace ι] {P : Measure ι}
    (hP : ∀ i, P {i} ≠ 0) : IsCoherentRiskMeasure P worstCase where
  mono X Y _ _ hXY :=
    worstCase_le fun i ↦ ((ae_iff_forall_of_singleton_ne_zero hP).1 hXY i).trans
      (le_worstCase Y i)
  add_const X _ m := by
    refine le_antisymm (worstCase_le fun i ↦ ?_) ?_
    · have := le_worstCase X i
      change X i + m ≤ worstCase X + m
      linarith
    obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty X
    have hwx : worstCase X = X i := hi
    rw [hwx]
    exact le_worstCase (fun i ↦ X i + m) i
  const_mul X _ c hc := by
    refine le_antisymm (worstCase_le fun i ↦ mul_le_mul_of_nonneg_left (le_worstCase X i) hc) ?_
    obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty X
    have hwx : worstCase X = X i := hi
    rw [hwx]
    exact le_worstCase (fun i ↦ c * X i) i
  add_le X Y _ _ :=
    worstCase_le fun i ↦ add_le_add (le_worstCase X i) (le_worstCase Y i)

/-- The representing set of worst-case loss is the entire probability simplex: the weight vectors
of the points of `Convexity.StdSimplex ℝ ι`. -/
lemma representingSet_worstCase :
    representingSet (worstCase (ι := ι))
      = Set.range fun w : Convexity.StdSimplex ℝ ι ↦ ⇑w.weights := by
  rw [Convexity.StdSimplex.range_toFun_comp_weights]
  ext q
  refine ⟨fun ⟨hnn, hsum, _⟩ ↦ ⟨Set.mem_iInter.2 hnn, hsum⟩,
    fun ⟨hnn, hsum⟩ ↦ ⟨Set.mem_iInter.1 hnn, hsum, fun Z hZ ↦ ?_⟩⟩
  exact Finset.sum_nonpos fun i _ ↦
    mul_nonpos_of_nonneg_of_nonpos (Set.mem_iInter.1 hnn i) ((le_worstCase Z i).trans hZ)

/-- **Worst-case loss is the supremum of expected loss over the entire probability simplex** —
the concrete instance of the ADEH representation. -/
theorem worstCase_isLUB (L : ι → ℝ) :
    IsLUB (Set.range fun w : Convexity.StdSimplex ℝ ι ↦ ∑ i, w.weights i * L i) (worstCase L) := by
  let : MeasurableSpace ι := ⊤
  have : MeasurableSingletonClass ι := ⟨fun _ ↦ trivial⟩
  have h := coherentRisk_isLUB (worstCase_isCoherent (P := Measure.count) fun i ↦ by simp) L
  rwa [representingSet_worstCase, ← Set.range_comp] at h

end MathFin
