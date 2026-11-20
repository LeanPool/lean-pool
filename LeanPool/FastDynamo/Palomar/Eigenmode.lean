/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Palomar.InductionSymbol
public import LeanPool.FastDynamo.Palomar.H2Dictionary

/-!
# The eigenmode clause of the Challenge statement

For every diffusivity `0 < ε ≤ mainEps0` the Challenge statement asks for an axial frequency
`K ≠ 0`, an eigenvalue `λ` with `mainGrowthFloor ≤ Re λ` and a non-zero field `V ∈ H² ∩ L²_σ`
whose Fourier coefficients vanish off `m₃ = K` and which solves `L_{ε,u} V = λ V` in the Fourier
form `inductionRHS u ε V = λ V̂`.

The library's eigenmode is `V = e^{2πiKx₃} b`, the axial lift `axialLiftH2 K b` of an amplitude
`b` of the transverse `H²` graph, transported to `T3`.  `mainLiteralEigenmode_clauses` gives all
clauses except `MemH2`, which is `memH2_toLiteralC3L2_productH2Embedding`; this module packages
the field as an element of `L2σ` (`exists_eigenmode_mainLiteralVelocity`).

The positivity of the constants of the main theorem is the library's `mainEps0_pos` and
`mainGrowthFloor_pos`.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory FastDynamoChallenge UnitAddTorus

/-- **E.**  For every `0 < ε ≤ mainEps0` there are an axial frequency `K ≠ 0`, an eigenvalue
`λ` with `mainGrowthFloor ≤ Re λ` and a non-zero `V ∈ L2σ` with `MemH2`, whose Fourier
coefficients vanish off `m 2 = K`, solving the Challenge's eigen-equation
`inductionRHS mainLiteralVelocity ε V = λ V̂`. -/
theorem exists_eigenmode_mainLiteralVelocity {ε : ℝ} (hε : 0 < ε) (hε₀ : ε ≤ mainEps0) :
    ∃ (K : ℤ) (lam : ℂ) (V : L2σ),
      K ≠ 0 ∧ mainGrowthFloor ≤ lam.re ∧ V ≠ 0 ∧ MemH2 ⇑(V : L2) ∧
      (∀ m i, m 2 ≠ K → mFourierCoeff (fun x => (V : L2) x i) m = 0) ∧
      (∀ m i, inductionRHS mainLiteralVelocity ε ⇑(V : L2) m i =
        lam * mFourierCoeff (fun x => (V : L2) x i) m) := by
  obtain ⟨K, lam, b, -, hK, hlam, hmem, hne, hsupp, heig⟩ :=
    mainLiteralEigenmode_clauses hε hε₀
  refine ⟨K, lam, ⟨_, hmem⟩, hK, hlam, ?_,
    memH2_toLiteralC3L2_productH2Embedding _, hsupp, heig⟩
  intro h0
  exact hne (congrArg Subtype.val h0)

end

end FastDynamo
