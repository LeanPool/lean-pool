/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.BoundaryCaccioppoliDatum
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.HarmonicReplacement

/-!
# BoundaryAssemblyDirichlet

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The rough-field Dirichlet solution with boundary datum `h`

This module removes that input: it constructs `v`, at the rough coefficient
family `a` itself (not a constant background), from CoarseGraining's zero-trace
Dirichlet well-posedness.

```text
  ρ ∈ H¹₀(□_m)  solves  −∇·a∇ρ = ∇·(g − a∇h) ,      v := h + ρ .
```

Then `−∇·a∇v = ∇·g` weakly and `v − h = ρ ∈ H¹₀(□_m)` on the nose, which is
exactly CoarseGraining's `DirichletForcedCubeSolution` with `boundaryData = h`.

## The coefficient bridge

CoarseGraining's public weak formulation `IsForcedEquation` tests against
`(a.coeffOn Q).toCoeffField`, while its Dirichlet existence theorem needs the
everywhere-elliptic representative `publicCoeffField Q a`.  The two agree a.e.
on the cube (`publicCoeffField_ae_eq`), and `integral_flux_eq_publicCoeffField`
below is the only place that fact is used.

## Main results

* `memVectorL2_roughDirichletCorrectorForce` — the shifted force is `L²`.
* `exists_zeroTraceDirichletCorrector_rough` — CoarseGraining's existence at
  the rough field on the open cube.
* `memH10_sub_of_exact_zeroTrace` — two solutions with the same datum and exact
  witnesses have a difference in `H¹₀`, which discharges the zero-trace
  hypothesis of the boundary Caccioppoli display.

## What is not done here

No estimate of any kind: the energy of the solution constructed here is bounded
by CoarseGraining's `energyConsequencesRHSTheory`, consumed in `BoundaryAssemblyEnergy`.
Uniqueness of `v` is not claimed (it is not needed: every statement downstream
is existential in `v`).

## References

* ABK26, `l.coarse.grained.Caccioppoli.
* CoarseGraining/Dirichlet.lean`, `Book/Ch03/Definitions.lean`
  (`DirichletForcedCubeSolution`),
  `Book/Ch03/Theorems/PublicInternalBridges/CoeffField.lean`.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch03 MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## 1. The coefficient bridge -/

/-- The tested flux pairing may be computed with CoarseGraining's
everywhere-elliptic representative `publicCoeffField Q a` instead of the public
`CoeffOn` field: the two agree almost everywhere on the cube. -/
theorem integral_flux_eq_publicCoeffField (Q : TriadicCube d) (a : CoeffFamily d)
    (u : H1Function (Ch02.cubeDomain Q : Set (Vec d)))
    (φ : H10Function (Ch02.cubeDomain Q : Set (Vec d))) :
    ∫ x in (Ch02.cubeDomain Q : Set (Vec d)),
        vecDot (matVecMul ((a.coeffOn Q).toCoeffField x) (u.grad x))
          (φ.toH1Function.grad x) ∂volume =
      ∫ x in (Ch02.cubeDomain Q : Set (Vec d)),
        vecDot (matVecMul (publicCoeffField Q a x) (u.grad x))
          (φ.toH1Function.grad x) ∂volume := by
  refine integral_congr_ae ?_
  filter_upwards [publicCoeffField_ae_eq Q a] with x hx
  rw [hx]

/-! ## 2. The shifted force -/

/-- **The force of the zero-trace problem solved by `v − h`.**  The printed
force `g` minus the datum's own flux `a∇h`. -/
def roughDirichletCorrectorForce (Q : TriadicCube d) (a : CoeffFamily d)
    (h : H1Function (openCubeSet Q)) (g : Vec d → Vec d) : Vec d → Vec d :=
  fun x => g x - matVecMul (publicCoeffField Q a x) (h.grad x)

theorem memVectorL2_roughDirichletCorrectorForce (Q : TriadicCube d)
    (a : CoeffFamily d) (h : H1Function (openCubeSet Q)) {g : Vec d → Vec d}
    (hg : MemVectorL2 (openCubeSet Q) g) :
    MemVectorL2 (openCubeSet Q) (roughDirichletCorrectorForce Q a h g) :=
  hg.sub (memVectorL2_matVecMul_of_isEllipticFieldOn
    (publicCoeffField_isEllipticFieldOn_openCubeSet Q a) h.grad_memVectorL2)

/-! ## 3. The zero-trace corrector at the rough field -/

variable [NeZero d]

/-- **CoarseGraining's Dirichlet existence theorem at the rough field.**  Nothing
in it is special to a constant background: it asks only for an elliptic field,
and `publicCoeffField Q a` is one on the open cube. -/
theorem exists_zeroTraceDirichletCorrector_rough (Q : TriadicCube d)
    (a : CoeffFamily d) (h : H1Function (openCubeSet Q)) {g : Vec d → Vec d}
    (hg : MemVectorL2 (openCubeSet Q) g) :
    ∃ rho : H10Function (openCubeSet Q),
      IsZeroTraceDirichletRhsWeakSolution (publicCoeffField Q a) (openCubeSet Q)
        rho (roughDirichletCorrectorForce Q a h g) :=
  exists_isZeroTraceDirichletRhsWeakSolution_of_potentialZeroTraceClosureRealization
    (a := publicCoeffField Q a) (U := openCubeSet Q)
    (g := roughDirichletCorrectorForce Q a h g)
    (lam := (a.coeffOn Q).lam) (Lam := (a.coeffOn Q).Lam)
    (memVectorL2_roughDirichletCorrectorForce Q a h hg)
    (hasPotentialZeroTraceClosureRealization_openCubeSet Q)
    (Ch02.openCubeSet_nonempty Q)
    (publicCoeffField_isEllipticFieldOn_openCubeSet Q a)

/-! ## 4. The Dirichlet solution with boundary datum `h` -/

/-- **The comparison solution of the printed boundary reduction.**

For every boundary datum `h ∈ H¹(□_m)` and every square-integrable force `g`
there is a Dirichlet forced solution on the cube whose boundary datum is
exactly `h`. -/
theorem exists_dirichletForcedCubeSolution_boundaryData (Q : TriadicCube d)
    (a : CoeffFamily d) (h : H1Function (openCubeSet Q))
    {g : Vec d → Vec d} (hg : MemVectorL2 (openCubeSet Q) g) :
    ∃ v : DirichletForcedCubeSolution Q a g, v.boundaryData = h ∧
      ∃ rho : H10Function (openCubeSet Q),
        ∀ y, rho.toH1Function.toFun y = v.toH1.toFun y - h.toFun y := by
  obtain ⟨rho, hrho⟩ := exists_zeroTraceDirichletCorrector_rough Q a h hg
  have hflux : MemVectorL2 (openCubeSet Q)
      fun x => matVecMul (publicCoeffField Q a x) (h.grad x) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn
      (publicCoeffField_isEllipticFieldOn_openCubeSet Q a) h.grad_memVectorL2
  have hrhoflux : MemVectorL2 (openCubeSet Q)
      fun x => matVecMul (publicCoeffField Q a x) (rho.toH1Function.grad x) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn
      (publicCoeffField_isEllipticFieldOn_openCubeSet Q a)
      rho.toH1Function.grad_memVectorL2
  have hweak : IsForcedEquation Q a (h + rho.toH1Function) g := by
    intro φ
    have hsplit := integral_vecDot_add_left_split (U := openCubeSet Q) hflux hrhoflux
      (H := fun x => matVecMul (publicCoeffField Q a x)
        ((h + rho.toH1Function).grad x))
      (fun x => by
        show matVecMul (publicCoeffField Q a x) ((h + rho.toH1Function).grad x) = _
        rw [H1Function.add_grad, matVecMul_add]) φ
    have hforce := integral_vecDot_sub_left_split (U := openCubeSet Q) hg hflux
      (H := roughDirichletCorrectorForce Q a h g) (fun x => rfl) φ
    rw [integral_flux_eq_publicCoeffField Q a (h + rho.toH1Function) φ]
    simp only [Ch02.cubeDomain_coe]
    rw [hsplit, hrho φ, hforce]
    ring
  have hexact : ∀ x, rho.toH1Function.toFun x =
      (h + rho.toH1Function).toFun x - h.toFun x := by
    intro x
    rw [H1Function.add_toFun]
    change rho.toH1Function.toFun x = h.toFun x + rho.toH1Function.toFun x - h.toFun x
    ring
  exact ⟨⟨h + rho.toH1Function, h, hweak, ⟨rho, Filter.Eventually.of_forall hexact⟩⟩,
    rfl, rho, hexact⟩

omit [NeZero d] in
end

end Algsuperdiff.Section4.Provider.ExcessDecay
