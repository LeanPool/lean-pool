/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Palomar.Velocity
public import LeanPool.FastDynamo.Palomar.Flow
public import LeanPool.FastDynamo.Palomar.SemigroupEigenmode
public import LeanPool.FastDynamo.Palomar.InductionSemigroup
public import LeanPool.FastDynamo.Palomar.Eigenmode
public import LeanPool.FastDynamo.Palomar.IdealUniqueness

/-!
# Theorem 1.2 in the form of the Challenge statement

This module assembles the clauses of the Challenge statement `fast_dynamo_zero_entropy` (the
form of Theorem 1.2 that uses only mathlib notions and the definitions of
`FastDynamo.Palomar.Statement`) at the witnesses of the library: the velocity
`mainLiteralVelocity`, the diffusivity threshold `mainEps0` and the growth floor
`mainGrowthFloor`.

* `challenge_clauses_mainLiteralVelocity` — every clause except the last one (the ideal solution
  group), for these witnesses: the velocity is Lipschitz
  (`exists_lipschitzWith_mainLiteralVelocity`) and divergence free
  (`isDivergenceFree_mainLiteralVelocity`); the constants are positive (`mainEps0_pos`,
  `mainGrowthFloor_pos`); for every `0 < ε ≤ mainEps0` an induction semigroup
  exists (`exists_isInductionSemigroup_mainLiteralVelocity`), there is an eigenmode
  (`exists_eigenmode_mainLiteralVelocity`), and the eigenmode gives the growth clause for every
  induction semigroup and the growing real solution (`eigenmode_clauses`); the particle flow
  exists (`exists_isFlow_mainLiteralVelocity`), and every time map of every flow is continuous
  with zero cover entropy (`forall_isFlow_mainLiteralVelocity_continuous_coverEntropy`).
* `challenge_statement_of_isIdealGroup` — the Challenge statement, with the clause on the ideal
  solution group of `mainLiteralVelocity` as hypothesis.
* `challenge_statement` — the Challenge statement itself, the ideal clause being
  `exists_unique_isIdealGroup_mainLiteralVelocity`.  `Solution.lean` proves
  `FastDynamoChallenge.fast_dynamo_zero_entropy` by this theorem.

The statements of `challenge_statement_of_isIdealGroup` and `challenge_statement` are elaborated
in the namespace `FastDynamoChallenge` with the `open` commands of the Challenge statement, so
that their conclusions are the text of the Challenge theorem, read with the same names.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory FastDynamoChallenge UnitAddTorus Filter Topology
open scoped NNReal

/-- **Every clause of the Challenge statement except the ideal one**, at the witnesses
`mainLiteralVelocity`, `mainEps0`, `mainGrowthFloor`: the velocity is Lipschitz and divergence
free, `0 < mainEps0` and `0 < mainGrowthFloor`; for every `0 < ε ≤ mainEps0` the induction
semigroup exists, every induction semigroup satisfies `e^{γ₀ t} ≤ ‖S t‖`, and there are an
eigenmode `(K, λ, V)` and the growing real solution with datum `Re V`; the particle flow exists,
and every time map of every flow is continuous with zero topological entropy. -/
theorem challenge_clauses_mainLiteralVelocity :
    (∃ L, LipschitzWith L
      (mainLiteralVelocity : FastDynamoChallenge.T3 → FastDynamoChallenge.R3)) ∧
    IsDivergenceFree mainLiteralVelocity ∧ 0 < mainEps0 ∧ 0 < mainGrowthFloor ∧
    (∀ ε, 0 < ε → ε ≤ mainEps0 →
      (∃ S, IsInductionSemigroup mainLiteralVelocity ε S) ∧
      (∀ S, IsInductionSemigroup mainLiteralVelocity ε S → ∀ t : ℝ≥0,
        Real.exp (mainGrowthFloor * t) ≤ ‖S t‖) ∧
      ∃ (K : ℤ) (lam : ℂ) (V : L2σ),
        K ≠ 0 ∧ mainGrowthFloor ≤ lam.re ∧ V ≠ 0 ∧ MemH2 ⇑(V : L2) ∧
        (∀ m i, m 2 ≠ K → mFourierCoeff (fun x => (V : L2) x i) m = 0) ∧
        (∀ m i, inductionRHS mainLiteralVelocity ε ⇑(V : L2) m i =
          lam * mFourierCoeff (fun x => (V : L2) x i) m) ∧
        ∃ Bin : L2σ, Bin ≠ 0 ∧ MemH2 ⇑(Bin : L2) ∧
          ⇑(Bin : L2) =ᵐ[volume] (fun x => re3 ((V : L2) x)) ∧
          ∀ S, IsInductionSemigroup mainLiteralVelocity ε S → ∀ t : ℝ≥0,
            ⇑(S t Bin : L2) =ᵐ[volume] (fun x => re3 (Complex.exp (t * lam) • (V : L2) x)) ∧
            ‖S t Bin‖ = Real.exp (t * lam.re) * ‖Bin‖) ∧
    (∃ Φ, IsFlow mainLiteralVelocity Φ) ∧
    (∀ Φ, IsFlow mainLiteralVelocity Φ → ∀ t,
      Continuous (Φ t) ∧ Dynamics.coverEntropy (Φ t) Set.univ = 0) := by
  refine ⟨exists_lipschitzWith_mainLiteralVelocity, isDivergenceFree_mainLiteralVelocity,
    mainEps0_pos, mainGrowthFloor_pos, fun ε hε hε₀ => ?_, exists_isFlow_mainLiteralVelocity,
    forall_isFlow_mainLiteralVelocity_continuous_coverEntropy⟩
  obtain ⟨K, lam, V, hK, hlam, hV, hH2, hsupp, heig⟩ :=
    exists_eigenmode_mainLiteralVelocity hε hε₀
  obtain ⟨hgrowth, hBin⟩ := eigenmode_clauses hK hlam hV hH2 hsupp heig
  exact ⟨exists_isInductionSemigroup_mainLiteralVelocity hε, hgrowth,
    K, lam, V, hK, hlam, hV, hH2, hsupp, heig, hBin⟩

end

end FastDynamo

namespace FastDynamoChallenge

open MeasureTheory UnitAddTorus Filter Topology
open scoped NNReal

/-- **The Challenge statement from its ideal clause.**  If the ideal induction equation of
`mainLiteralVelocity` has exactly one solution group `T` on `L²_σ` and
`t⁻¹ log ‖T t‖ → 0`, then the Challenge statement `fast_dynamo_zero_entropy` holds, with the
witnesses `mainLiteralVelocity`, `mainEps0`, `mainGrowthFloor`
(`challenge_clauses_mainLiteralVelocity`). -/
theorem _root_.FastDynamo.challenge_statement_of_isIdealGroup
    (hT : ∃ T, IsIdealGroup FastDynamo.mainLiteralVelocity T ∧
      (∀ T', IsIdealGroup FastDynamo.mainLiteralVelocity T' → T' = T) ∧
      Tendsto (fun t : ℝ => t⁻¹ * Real.log ‖T t‖) atTop (𝓝 0)) :
    ∃ u : T3 → R3, (∃ L, LipschitzWith L u) ∧ IsDivergenceFree u ∧
    ∃ ε₀ γ₀ : ℝ, 0 < ε₀ ∧ 0 < γ₀ ∧
    (∀ ε, 0 < ε → ε ≤ ε₀ →
      (∃ S, IsInductionSemigroup u ε S) ∧
      (∀ S, IsInductionSemigroup u ε S → ∀ t : ℝ≥0, Real.exp (γ₀ * t) ≤ ‖S t‖) ∧
      ∃ (K : ℤ) (lam : ℂ) (V : L2σ),
        K ≠ 0 ∧ γ₀ ≤ lam.re ∧ V ≠ 0 ∧ MemH2 ⇑(V : L2) ∧
        (∀ m i, m 2 ≠ K → mFourierCoeff (fun x => (V : L2) x i) m = 0) ∧
        (∀ m i, inductionRHS u ε ⇑(V : L2) m i =
          lam * mFourierCoeff (fun x => (V : L2) x i) m) ∧
        ∃ Bin : L2σ, Bin ≠ 0 ∧ MemH2 ⇑(Bin : L2) ∧
          ⇑(Bin : L2) =ᵐ[volume] (fun x => re3 ((V : L2) x)) ∧
          ∀ S, IsInductionSemigroup u ε S → ∀ t : ℝ≥0,
            ⇑(S t Bin : L2) =ᵐ[volume] (fun x => re3 (Complex.exp (t * lam) • (V : L2) x)) ∧
            ‖S t Bin‖ = Real.exp (t * lam.re) * ‖Bin‖) ∧
    (∃ Φ, IsFlow u Φ) ∧
    (∀ Φ, IsFlow u Φ → ∀ t, Continuous (Φ t) ∧ Dynamics.coverEntropy (Φ t) Set.univ = 0) ∧
    ∃ T, IsIdealGroup u T ∧ (∀ T', IsIdealGroup u T' → T' = T) ∧
      Tendsto (fun t : ℝ => t⁻¹ * Real.log ‖T t‖) atTop (𝓝 0) := by
  obtain ⟨hL, hdiv, hε₀, hγ₀, hε, hΦ, hent⟩ :=
    FastDynamo.challenge_clauses_mainLiteralVelocity
  exact ⟨_, hL, hdiv, _, _, hε₀, hγ₀, hε, hΦ, hent, hT⟩

/-- **Theorem 1.2 in the form of the Challenge statement.**  The statement is, character for
character, that of `FastDynamoChallenge.fast_dynamo_zero_entropy` in `Challenge.lean`; it is proved
at the witnesses `mainLiteralVelocity`, `mainEps0`, `mainGrowthFloor`, the ideal clause being
`exists_unique_isIdealGroup_mainLiteralVelocity`. -/
theorem _root_.FastDynamo.challenge_statement :
    ∃ u : T3 → R3, (∃ L, LipschitzWith L u) ∧ IsDivergenceFree u ∧
    ∃ ε₀ γ₀ : ℝ, 0 < ε₀ ∧ 0 < γ₀ ∧
    (∀ ε, 0 < ε → ε ≤ ε₀ →
      (∃ S, IsInductionSemigroup u ε S) ∧
      (∀ S, IsInductionSemigroup u ε S → ∀ t : ℝ≥0, Real.exp (γ₀ * t) ≤ ‖S t‖) ∧
      ∃ (K : ℤ) (lam : ℂ) (V : L2σ),
        K ≠ 0 ∧ γ₀ ≤ lam.re ∧ V ≠ 0 ∧ MemH2 ⇑(V : L2) ∧
        (∀ m i, m 2 ≠ K → mFourierCoeff (fun x => (V : L2) x i) m = 0) ∧
        (∀ m i, inductionRHS u ε ⇑(V : L2) m i =
          lam * mFourierCoeff (fun x => (V : L2) x i) m) ∧
        ∃ Bin : L2σ, Bin ≠ 0 ∧ MemH2 ⇑(Bin : L2) ∧
          ⇑(Bin : L2) =ᵐ[volume] (fun x => re3 ((V : L2) x)) ∧
          ∀ S, IsInductionSemigroup u ε S → ∀ t : ℝ≥0,
            ⇑(S t Bin : L2) =ᵐ[volume] (fun x => re3 (Complex.exp (t * lam) • (V : L2) x)) ∧
            ‖S t Bin‖ = Real.exp (t * lam.re) * ‖Bin‖) ∧
    (∃ Φ, IsFlow u Φ) ∧
    (∀ Φ, IsFlow u Φ → ∀ t, Continuous (Φ t) ∧ Dynamics.coverEntropy (Φ t) Set.univ = 0) ∧
    ∃ T, IsIdealGroup u T ∧ (∀ T', IsIdealGroup u T' → T' = T) ∧
      Tendsto (fun t : ℝ => t⁻¹ * Real.log ‖T t‖) atTop (𝓝 0) :=
  FastDynamo.challenge_statement_of_isIdealGroup
    FastDynamo.exists_unique_isIdealGroup_mainLiteralVelocity

end FastDynamoChallenge
