/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Global.MainTheoremWitnesses

/-!
# Growing eigenpairs at *every* matching cell

`MainReducedClauses` (`Main.lean`) asserts a growing eigenpair of the reduced induction operator
only in the sector of the cell canonically chosen by the parameter chain,
`mainParameterChoice.matchingCell hpos hle`.  That is all the reduction to Theorem 1.2 needs,
but it understates what the construction proves: the theorem
(`HorizontalMode.exists_growing_reducedInduction_eigenpair_matchingCell`,
`Global/GlobalSpectralTransferConcrete.lean`) is established for **every**
`c : ScaleFamily.MatchingCell mainParameterChoice.scaleFamily epsilon`, since none of its
hypotheses mentions the cell.

This module states and proves the stronger statement.

## Main results

* `exists_growing_eigenpair_of_matchingCell` — a growing eigenpair of the reduced induction
  operator at `mainVelocity` in the axial sector of *every* matching cell of the parameter chain,
  together with the axial lift as an eigenmode of the auxiliary product operator;
* `exists_growing_eigenpair_of_admissible_index` — the same statement indexed by the scale index
  `n`, i.e. at *every* admissible scale index rather than only at the selected one.

## Relation to `prop:global-spectral-transfer`

A conclusion that picked one sector per diffusivity would be narrower than
`prop:global-spectral-transfer`, which is stated for every `n` with `ε / ℓ_n² ∈ I`.
`exists_growing_eigenpair_of_admissible_index` is that uniform statement: for a fixed `0 < ε`,
*every* scale index `n` whose rescaled diffusivity `ε / ℓ_n²` lies in the seed's admissible
interval carries a growing eigenpair in the sector `K_n`.  (No upper bound on `ε` is needed: on
this route the threshold `ε₀` only enters through the *existence* of a matching cell.)
-/

@[expose] public section

namespace FastDynamo

noncomputable section

/-! ## Growing eigenpairs in every admissible sector of the parameter chain -/

/-- **A growing eigenpair in the sector of an arbitrary matching cell.**

For every `0 < ε` and every matching cell `c` of the parameter chain's scale
family, the reduced induction operator at `mainVelocity` in the axial sector
`K_{c.index}` has an eigenpair whose eigenvalue has real part at least
`mainGrowthFloor`, and the corresponding axial lift is an eigenmode of the
auxiliary product operator.  The sector index is nonzero, as the reduced
operator requires.

`mainReducedClauses_holds` is the special case `c = matchingCell hpos hle`,
with the cell hidden. -/
theorem exists_growing_eigenpair_of_matchingCell {epsilon : ℝ} (hpos : 0 < epsilon)
    (c : ScaleFamily.MatchingCell HorizontalMode.mainParameterChoice.scaleFamily epsilon) :
    HorizontalMode.mainParameterChoice.fourierIndex c ≠ 0 ∧
      ∃ (lambda : ℂ) (b : TransverseC3H2),
        mainGrowthFloor ≤ lambda.re ∧
          (reducedInductionOperator mainVelocity epsilon
            (HorizontalMode.mainParameterChoice.fourierIndex c)).IsEigenpair lambda b ∧
          (productInductionOperator mainVelocity epsilon).IsEigenpair lambda
            (axialLiftH2 (HorizontalMode.mainParameterChoice.fourierIndex c) b) := by
  obtain ⟨lambda, b, hfloor, hreduced, hproduct, -, -⟩ :=
    HorizontalMode.exists_growing_reducedInduction_eigenpair_matchingCell hpos c
  exact ⟨HorizontalMode.mainParameterChoice.fourierIndex_ne_zero c,
    lambda, b, hfloor, hreduced, hproduct⟩

/-- **The paper-shaped corollary: every admissible scale index.**

Fix `0 < ε`.  For *every* index `n` whose rescaled diffusivity
`ε / ℓ_n²` lies in the seed's admissible interval `[δ₋, δ₊]`, the axial sector
`K_n` of the parameter chain carries a growing eigenpair of the reduced induction
operator at `mainVelocity`, with growth floor `mainGrowthFloor`.

This is the every-cell form of the conclusion, as in
`prop:global-spectral-transfer`: the formalised statement does not select one
sector per diffusivity, it covers the whole admissible window. -/
theorem exists_growing_eigenpair_of_admissible_index {epsilon : ℝ} (hpos : 0 < epsilon) (n : ℕ)
    (hn : HorizontalMode.mainParameterChoice.scaleFamily.rescaledDiffusivity epsilon n ∈
      HorizontalMode.globalSeedInterface.parameters.interval) :
    ((HorizontalMode.mainParameterChoice.scaleFamily.fourierIndex n : ℤ) ≠ 0) ∧
      ∃ (lambda : ℂ) (b : TransverseC3H2),
        mainGrowthFloor ≤ lambda.re ∧
          (reducedInductionOperator mainVelocity epsilon
            (HorizontalMode.mainParameterChoice.scaleFamily.fourierIndex n :
              ℤ)).IsEigenpair lambda b ∧
          (productInductionOperator mainVelocity epsilon).IsEigenpair lambda
            (axialLiftH2
              (HorizontalMode.mainParameterChoice.scaleFamily.fourierIndex n : ℤ) b) :=
  exists_growing_eigenpair_of_matchingCell hpos ⟨n, hn⟩

end

end FastDynamo
