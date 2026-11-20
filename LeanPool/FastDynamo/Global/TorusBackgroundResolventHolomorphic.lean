/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Global.TorusBackgroundResolvent
public import LeanPool.FastDynamo.Operator.ResolventSetHolomorphy

/-!
# The background resolvent is holomorphic near `cG_tau`

A clause in addition to `prop:background-resolvent`, which asserts `𝒢_τ ⊂ ρ(A^bg_{ε,n})` and
the bound `eq:bg-resolvent` but nothing about the dependence of the resolvent on `z`: the
background resolvent is holomorphic on a neighbourhood of `𝒢_τ`.  Nothing in the paper or in
the proofs of §7 uses it.

`BackgroundParameters.exists_isOpen_hasResolventOn_analyticOnNhd` proves it for every cell `n`
and every diffusivity `ε` with `δ_- ℓ_n² ≤ ε ≤ δ_+ ℓ_n²`, under the hypotheses of
`BackgroundParameters.resolvent`: the neighbourhood is the intrinsic resolvent set of
`A^bg_{ε,n}`, which is open and contains `cG_tau`; on it the domain-valued resolvent
`z ↦ (z - A^bg_{ε,n})⁻¹ : L² → H²` is a two-sided inverse of the pencil and is analytic in
operator norm (`DomainOperator.analyticOnNhd_resolventSetResolvent_inv`), and on `cG_tau` it is
the resolvent `BackgroundParameters.resolvent` used in §7.  Compactness of `cG_tau` is not
needed: the whole resolvent set is the neighbourhood.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

namespace ScaleFamily.TorusCellPlacement

namespace BackgroundParameters

variable {p : LocalSeedParameters} {r : ScaleRatios p}
  {hw : PonomarenkoSmoothingWidth} {P : TorusCellPlacement (r := r) (1 + (hw : ℝ))}
  {angularSpeed axialSpeed : ℝ}

/-- **Holomorphy of the resolvent of `prop:background-resolvent`** (a clause the paper does not
state).  There is an open set `U ⊇ cG_tau`
carrying a two-sided resolvent `R(z) = (z - A^bg_{ε,n})⁻¹ : L² → H²` of the background operator
which is analytic on `U` in operator norm and agrees on `cG_tau` with the background resolvent
`BackgroundParameters.resolvent`. -/
theorem exists_isOpen_hasResolventOn_analyticOnNhd
    (B : BackgroundParameters hw P angularSpeed axialSpeed) (n : ℕ) {ε : ℝ}
    (heps : 0 < ε) (hlow : B.diffusivityLower * P.scaleFamily.ell n ^ 2 ≤ ε)
    (hupp : ε ≤ B.diffusivityUpper * P.scaleFamily.ell n ^ 2) :
    ∃ U : Set ℂ, IsOpen U ∧ B.shiftedRegion ⊆ U ∧
      ∃ R : HasResolventOn (B.operator ε n) U, AnalyticOnNhd ℂ R.inv U ∧
        Set.EqOn R.inv (B.resolvent n heps hlow hupp).inv B.shiftedRegion := by
  let R₀ := B.resolvent n heps hlow hupp
  have hsub : B.shiftedRegion ⊆ (B.operator ε n).resolventSet := fun z hz =>
    ContinuousLinearMap.IsInvertible.of_inverse (R₀.right_inv z hz) (R₀.left_inv z hz)
  refine ⟨_, (B.operator ε n).isOpen_resolventSet, hsub,
    (B.operator ε n).resolventSetResolvent,
    (B.operator ε n).analyticOnNhd_resolventSetResolvent_inv, fun z hz => ?_⟩
  have h : ((B.operator ε n).pencil z).IsInvertible := hsub hz
  change ((B.operator ε n).pencil z).inverse = R₀.inv z
  calc ((B.operator ε n).pencil z).inverse
      = (R₀.inv z).comp (((B.operator ε n).pencil z).comp
          ((B.operator ε n).pencil z).inverse) := by
        rw [← ContinuousLinearMap.comp_assoc, R₀.left_inv z hz, ContinuousLinearMap.id_comp]
    _ = R₀.inv z := by rw [h.self_comp_inverse, ContinuousLinearMap.comp_id]

end BackgroundParameters

end ScaleFamily.TorusCellPlacement

end

end FastDynamo
