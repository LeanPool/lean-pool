/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson
-/

module

public import LeanPool.ScottMeasurement.Probability.Infinite.EventSpace
public import LeanPool.ScottMeasurement.Probability.Infinite.Kelley

/-!
# A modern reconstruction of the infinite probability theorem

Scott's published 1964 paper states and proves the finite theorem, then only
announces an unstated infinite extension. The result below adapts Kelley's
method and is not presented as Scott's unpublished theorem.

Weak comparisons generate a closed cone in the universal event span, expressed
here by its continuous dual polar.  The additional generalized Kelley condition
gives a countable cover of the strict comparisons by closed convex upper sets.
This adapts the countable-cover/separation method of J. L. Kelley, *Measures on
Boolean Algebras* (1959), but the event-span formulation, condition, and theorem
statement are not attributed to Kelley. The real Hahn--Banach theorem in
`HahnBanach.lean`, through
`KelleyCover.exists_combined_separator`, then supplies one functional which is
nonnegative on every weak comparison and positive on every strict comparison.
-/

@[expose] public section

namespace Scott1964.MeasurementStructures.Probability.Infinite

open Set

noncomputable section

universe u

variable {B : Type u} [BooleanAlgebra B]

/-- The signed event-span vector associated with the comparison of `x` to `y`. -/
def comparisonVector (B : Type u) [BooleanAlgebra B] (x y : B) : EventSpan B :=
  event B x - event B y

/-- The closed weak-comparison cone, defined as the intersection of all closed
dual half-spaces which contain the declared weak comparisons. -/
def weakComparisonCone (R : B → B → Prop) : ProperCone ℝ (EventSpan B) :=
  ⨅ (L : StrongDual ℝ (EventSpan B))
    (_hL : ∀ x y, R x y → 0 ≤ L (comparisonVector B x y)),
      (ProperCone.positive ℝ ℝ).comap L

theorem mem_weakComparisonCone_iff {R : B → B → Prop} {v : EventSpan B} :
    v ∈ weakComparisonCone R ↔
      ∀ L : StrongDual ℝ (EventSpan B),
        (∀ x y, R x y → 0 ≤ L (comparisonVector B x y)) →
          0 ≤ L v := by
  simp [weakComparisonCone]

theorem comparisonVector_mem_weakComparisonCone {R : B → B → Prop}
    {x y : B} (hxy : R x y) :
    comparisonVector B x y ∈ weakComparisonCone R := by
  rw [mem_weakComparisonCone_iff]
  intro L hL
  exact hL x y hxy

/-- The set of vectors corresponding to source-strict comparisons
`x ≻ y`, namely `¬ R y x`. -/
def strictComparisonSet (R : B → B → Prop) : Set (EventSpan B) :=
  {v | ∃ x y, StrictlyPreferred R x y ∧ v = comparisonVector B x y}

theorem comparisonVector_mem_strictComparisonSet {R : B → B → Prop}
    {x y : B} (hxy : StrictlyPreferred R x y) :
    comparisonVector B x y ∈ strictComparisonSet R :=
  ⟨x, y, hxy, rfl⟩

/-- Concrete generalized Kelley condition used by this reconstruction: strict
comparison vectors admit a countable Kelley cover above the closed weak cone. -/
def GeneralizedKelleyCondition (R : B → B → Prop) : Prop :=
  Nonempty (KelleyCover (weakComparisonCone R) (strictComparisonSet R))

private theorem exists_reciprocal_le {r : ℝ} (hr : 0 < r) :
    ∃ n : ℕ, (1 : ℝ) / (n + 1) ≤ r := by
  obtain ⟨n : ℕ, hn⟩ := exists_nat_gt (1 / r)
  refine ⟨n, ?_⟩
  have hnpos : (0 : ℝ) < n + 1 := by positivity
  rw [div_le_iff₀ hnpos]
  have hr' : (1 : ℝ) < (n + 1) * r := by
    have := (div_lt_iff₀ hr).mp hn
    nlinarith
  nlinarith

private theorem realizable_generalizedKelley
    {R : B → B → Prop} (hR : RealizableProbability R) :
    GeneralizedKelleyCondition R := by
  rcases hR with ⟨μ, hμ, hrep⟩
  let p : ProbabilityPoint B := ⟨μ, hμ⟩
  let L : StrongDual ℝ (EventSpan B) :=
    (BoundedContinuousFunction.evalCLM ℝ p).comp (EventSpan B).subtypeL
  let K : ℕ → Set (EventSpan B) :=
    fun n => {v | (1 : ℝ) / (n + 1) ≤ L v}
  refine ⟨{
    layer := K
    strictInCone := ?_
    covers := ?_
    convex := ?_
    closed := ?_
    avoidsZero := ?_
    upper := ?_
  }⟩
  · rintro v ⟨x, y, hstrict, rfl⟩
    apply comparisonVector_mem_weakComparisonCone
    apply (hrep x y).2
    exact le_of_not_gt (fun h => hstrict ((hrep y x).2 h.le))
  · rintro v ⟨x, y, hstrict, rfl⟩
    have hpos : 0 < L (comparisonVector B x y) := by
      change 0 < μ x - μ y
      apply sub_pos.mpr
      exact lt_of_not_ge (fun h => hstrict ((hrep y x).2 h))
    obtain ⟨n, hn⟩ := exists_reciprocal_le hpos
    apply Set.mem_iUnion.mpr
    exact ⟨n, hn⟩
  · intro n
    exact convex_halfSpace_ge L.toLinearMap.isLinear _
  · intro n
    exact isClosed_le continuous_const L.continuous
  · intro n hz
    change (1 : ℝ) / (n + 1) ≤ L 0 at hz
    rw [map_zero] at hz
    have : (0 : ℝ) < 1 / (n + 1) := by positivity
    linarith
  · intro n v c hv hc
    dsimp [K] at hv ⊢
    rw [map_add]
    apply hv.trans
    apply le_add_of_nonneg_right
    rw [mem_weakComparisonCone_iff] at hc
    apply hc L
    intro x y hxy
    change 0 ≤ μ x - μ y
    exact sub_nonneg.mpr ((hrep x y).1 hxy)

private theorem generalizedKelley_realizable
    {R : B → B → Prop}
    (hnt : ProbNontrivial R) (hnn : ProbNonneg R) (htot : ProbTotal R)
    (hK : GeneralizedKelleyCondition R) :
    RealizableProbability R := by
  rcases hK with ⟨cover⟩
  obtain ⟨F, hFweak, hFstrict⟩ := cover.exists_combined_separator
  have htopStrict : StrictlyPreferred R (⊤ : B) ⊥ := hnt.2
  have htopSet :
      comparisonVector B (⊤ : B) ⊥ ∈ strictComparisonSet R :=
    comparisonVector_mem_strictComparisonSet htopStrict
  have htopPos : 0 < F (event B (⊤ : B)) := by
    have := hFstrict _ htopSet
    have hvec :
        event B (⊤ : B) - event B (⊥ : B) = event B (⊤ : B) := by
      rw [event_bot]
      exact sub_zero (event B (⊤ : B))
    rwa [comparisonVector, hvec] at this
  let μ : B → ℝ := fun a => F (event B a) / F (event B (⊤ : B))
  have hμ : IsProbability μ := by
    refine {
      bot := ?_
      top := ?_
      additive := ?_
      nonnegative := ?_
    }
    · simp [μ]
    · exact div_self htopPos.ne'
    · intro x y hxy
      simp only [μ]
      rw [event_sup_of_disjoint B hxy, map_add, add_div]
    · intro x
      have hxcone :
          comparisonVector B x ⊥ ∈ weakComparisonCone R :=
        comparisonVector_mem_weakComparisonCone (hnn x)
      have hxnonneg := hFweak _ hxcone
      have : 0 ≤ F (event B x) := by
        have hvec : event B x - event B (⊥ : B) = event B x := by
          rw [event_bot]
          exact sub_zero (event B x)
        rwa [comparisonVector, hvec] at hxnonneg
      exact div_nonneg this htopPos.le
  refine ⟨μ, hμ, ?_⟩
  intro x y
  constructor
  · intro hxy
    have hcone :
        comparisonVector B x y ∈ weakComparisonCone R :=
      comparisonVector_mem_weakComparisonCone hxy
    have hnonneg := hFweak _ hcone
    change F (event B x) / F (event B ⊤) ≥
      F (event B y) / F (event B ⊤)
    exact (div_le_div_iff_of_pos_right htopPos).2 (by
      have hmap := map_sub F (event B x) (event B y)
      change 0 ≤ F (event B x - event B y) at hnonneg
      linarith)
  · intro hμxy
    rcases htot x y with hxy | hyx
    · exact hxy
    · by_contra hnxy
      have hstrict : StrictlyPreferred R y x := hnxy
      have hset :
          comparisonVector B y x ∈ strictComparisonSet R :=
        comparisonVector_mem_strictComparisonSet hstrict
      have hpos := hFstrict _ hset
      have hlt : μ x < μ y := by
        change F (event B x) / F (event B ⊤) <
          F (event B y) / F (event B ⊤)
        rw [div_lt_div_iff_of_pos_right htopPos]
        have hmap := map_sub F (event B y) (event B x)
        change 0 < F (event B y - event B x) at hpos
        linarith
      exact (not_lt_of_ge hμxy) hlt

/-- If-and-only-if characterization of an infinite analogue of Scott's Theorem 4.1,
adapting Kelley's 1959 separation method. It is not an attribution of an
unpublished theorem to Scott. -/
theorem reconstructed_infinite_theorem_4_1 (R : B → B → Prop) :
    RealizableProbability R ↔
      ProbNontrivial R ∧ ProbNonneg R ∧ ProbTotal R ∧
        GeneralizedKelleyCondition R := by
  constructor
  · intro hR
    exact ⟨hR.probNontrivial, hR.probNonneg, hR.probTotal,
      realizable_generalizedKelley hR⟩
  · rintro ⟨hnt, hnn, htot, hK⟩
    exact generalizedKelley_realizable hnt hnn htot hK

end

end Scott1964.MeasurementStructures.Probability.Infinite
