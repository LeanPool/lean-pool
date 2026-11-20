/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Global.TorusBackgroundResolvent
public import LeanPool.FastDynamo.Global.TorusTwoSummandParametrix

/-!
# The Section 6 background resolvent as Section 7 parametrix data

`FastDynamo/Global/TorusBackgroundResolvent.lean` produces `prop:background-resolvent` in the record
`TorusBackgroundResolventData A S ε C`: a resolvent family on the parameter set together with
the two halves of `eq:bg-resolvent`, `‖R(z)f‖₂ ≤ C‖f‖₂` and `√ε‖∇_⊥R(z)f‖₂ ≤ C‖f‖₂`.

`FastDynamo/Global/TorusTwoSummandParametrix.lean` consumes the same content through
`BackgroundParametrixData ubg ε K S`, whose gradient field is written `√(ε·E) ≤ C‖f‖` rather
than `√ε·√E ≤ C‖f‖`.  The two differ by `Real.sqrt_mul`, and that single rewrite is the whole
bridge; this module records it once, so that the parameter chain never has to repeat it.

The record `TorusBackgroundResolventData` is stated for an arbitrary `DomainOperator`; the
background instance is `B.operator ε n = horizontalInductionOperator (B.velocity n)
ε (B.fourierIndex n)` definitionally, which is exactly the shape
`BackgroundParametrixData` asks for.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

namespace TorusTwoSummandParametrix

/-- **The Section 6 to Section 7 bridge for the background summand.**  A
`TorusBackgroundResolventData` for the background operator is a `BackgroundParametrixData`; the
only mismatch is `√ε·√E` against `√(ε·E)`. -/
def BackgroundParametrixData.ofTorusBackgroundResolventData
    {ubg : TransverseRealW1Inf} {epsilon : ℝ} {K : ℤ} {S : Set ℂ} {C : ℝ}
    (hepsilon : 0 ≤ epsilon) (hC : 0 ≤ C)
    (D : TorusBackgroundResolventData (horizontalInductionOperator ubg epsilon K) S
      epsilon C) :
    BackgroundParametrixData ubg epsilon K S :=
  BackgroundParametrixData.ofHasResolventOn D.resolvent C hC D.norm_le
    (fun z hz f ↦ by
      rw [Real.sqrt_mul hepsilon]
      exact D.sqrt_eps_gradient_le z hz f)

/-- The bridged data stores the resolvent family of the Section 6 record. -/
@[simp] theorem BackgroundParametrixData.ofTorusBackgroundResolventData_resolvent
    {ubg : TransverseRealW1Inf} {epsilon : ℝ} {K : ℤ} {S : Set ℂ} {C : ℝ}
    (hepsilon : 0 ≤ epsilon) (hC : 0 ≤ C)
    (D : TorusBackgroundResolventData (horizontalInductionOperator ubg epsilon K) S
      epsilon C) :
    (BackgroundParametrixData.ofTorusBackgroundResolventData hepsilon hC D).resolvent =
      D.resolvent.inv :=
  rfl

/-- The bridged data keeps the Section 6 constant of `eq:bg-resolvent`. -/
@[simp] theorem BackgroundParametrixData.ofTorusBackgroundResolventData_bound
    {ubg : TransverseRealW1Inf} {epsilon : ℝ} {K : ℤ} {S : Set ℂ} {C : ℝ}
    (hepsilon : 0 ≤ epsilon) (hC : 0 ≤ C)
    (D : TorusBackgroundResolventData (horizontalInductionOperator ubg epsilon K) S
      epsilon C) :
    (BackgroundParametrixData.ofTorusBackgroundResolventData hepsilon hC D).bound = C :=
  rfl

end TorusTwoSummandParametrix

end

end FastDynamo
