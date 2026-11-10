/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Curve.TraceMatrix
public import LeanPool.HyperellipticCurves.Log.Fold.FoldAssemble
public import LeanPool.HyperellipticCurves.Log.Trace.TraceDisk
public import LeanPool.HyperellipticCurves.Log.Trace.TraceFtau

import LeanPool.HyperellipticCurves.Log.Fold.FoldTrace

/-!
# The differential matrix under substitution and folding

Two compatibility statements feed the per-disk assembly of `thm:omega-prime-global`
clause (c), which is carried out in `LeanPool.HyperellipticCurves.Log.Trace.TraceKz` (and its
Weierstrass and
infinity mirrors).

## Main statements

* `ChabautyColeman.map_substRingHom_diffMatrix`: substituting the chart coordinates
  `X_j ↦ ζ_j(z)` into the differential matrix `M(X)` and then reducing the coefficients is
  the same as substituting the reduced coordinates into the reduced `M(X)`. The substitution
  is a ring homomorphism (`MvPowerSeries.substRingHom`), which is what makes the composite a
  homomorphism at all — the map `X_j ↦ ζ_j` is not one on power series over a function field —
  and `M` commutes with base change
  (`ChabautyColeman.FormalGroupLaw.diffMatrix_map`). This puts the formal identity and the
  curve identity on one and the same object.
* `ChabautyColeman.ftauFoldFGL_diffMatrix_eq`: the differential matrix of the fold `F_τ` is
  the `Y = 0` specialization of `∂F/∂Y`, which is the form in which the trace-form invariance
  identity produces it.

Blueprint node: `thm:omega-prime-global`, clause (c).
-/

@[expose] public section

open Polynomial IsLocalRing
open scoped PowerSeries

namespace ChabautyColeman

section Compat

variable {O : Type*} [CommRing O] {n : ℕ}

/-- **The chart substitution commutes with base change on the differential matrix.**
Substituting the chart coordinates into `M(X)` and then reducing the coefficients is the same
as substituting the reduced coordinates into the reduced `M(X)`: the substitution
`X_j ↦ ζ_j(z)` is a ring homomorphism (`MvPowerSeries.substRingHom`) commuting with
`MvPowerSeries.map`, and `M` commutes with base change
(`ChabautyColeman.FormalGroupLaw.diffMatrix_map`). This is what puts the formal identity and
the curve identity on one and the same object. -/
theorem map_substRingHom_diffMatrix {O' : Type*} [CommRing O'] (Φ : FormalGroupLaw O (Fin n))
    (φ : O →+* O') {ζ : Fin n → O⟦X⟧} (hζ : MvPowerSeries.HasSubst ζ)
    (hζφ : MvPowerSeries.HasSubst fun j ↦ PowerSeries.map φ (ζ j)) (j k : Fin n) :
    PowerSeries.map φ (MvPowerSeries.substRingHom hζ (Φ.diffMatrix j k))
      = MvPowerSeries.subst (fun j ↦ PowerSeries.map φ (ζ j)) ((Φ.map φ).diffMatrix j k) := by
  have hζφ' : MvPowerSeries.HasSubst fun s ↦ MvPowerSeries.map φ (ζ s) := hζφ
  rw [show PowerSeries.map φ (MvPowerSeries.substRingHom hζ (Φ.diffMatrix j k))
      = MvPowerSeries.map φ (MvPowerSeries.substRingHom hζ (Φ.diffMatrix j k)) from rfl,
    MvPowerSeries.map_substRingHom φ hζ hζφ', Φ.diffMatrix_map φ, Matrix.map_apply,
    MvPowerSeries.substRingHom_apply]
  rfl

end Compat

section Assemble

variable {O : Type*} [CommRing O] [IsDomain O] [IsLocalRing O] [UniformSpace O]
  [Fact (IsAdic (maximalIdeal O))] [IsUniformAddGroup O] [CompleteSpace O] [T2Space O]
  [IsTopologicalRing O]
  {n : ℕ} {f uτ vτ w c₁ c₂ : O[X]}
  [NeZero (2 : FractionRing O)]
  [Fact (Odd (f.map (algebraMap O (FractionRing O))).natDegree)]
  [Fact (Squarefree (f.map (algebraMap O (FractionRing O))))]

/-- The differential matrix of the fold `F_τ` is the `Y = 0` specialization of `∂F/∂Y`,
which is the form in which the trace-form invariance identity produces it. -/
theorem ftauFoldFGL_diffMatrix_eq
    {Aτ : Fin n → MvPowerSeries (Fin n ⊕ Fin n) O} {aτ bτ : Fin n → O}
    {dτ : FoldCertData (MvPowerSeries (Fin n ⊕ Fin n) O) n}
    {hu : uτ.Monic} {hne : uτ.natDegree = n} {hv : vτ.degree < uτ.degree}
    {hw : vτ ^ 2 - f = uτ * w} {hbez : c₁ * uτ + c₂ * (2 * vτ) = 1}
    (hfm : f.Monic) (hfdegn : f.natDegree = 2 * n + 1)
    (hroot : ∀ i, (ftauUY uτ n).eval (Aτ i) = 0)
    (hcc : ∀ i, MvPowerSeries.constantCoeff (Aτ i) = aτ i)
    (haτ : ∀ i, uτ.eval (aτ i) = 0) (hbτ : ∀ i, vτ.eval (aτ i) = bτ i)
    (hdτ : IsFtauFoldCerts Aτ aτ bτ hu hne hv hw hbez dτ)
    {π : O} (hπ : maximalIdeal O = Ideal.span {π}) (hπ0 : π ≠ 0)
    (hsplit : uτ = ∏ m' : Fin n, (X - C (aτ m')))
    (hunit : ∀ i j : Fin n, i ≠ j → IsUnit (aτ i - aτ j)) (j k : Fin n) :
    (ftauFoldFGL hu hne hv hw hbez hfm hfdegn hroot hcc haτ hbτ hdτ hπ hπ0 hsplit
        hunit).diffMatrix j k
      = setYZero (MvPowerSeries.pderiv (Sum.inr k)
          (FtauFold Aτ aτ bτ hu hne hv hw hbez dτ j)) :=
  (setYZero_apply _).symm

end Assemble

end ChabautyColeman

end
