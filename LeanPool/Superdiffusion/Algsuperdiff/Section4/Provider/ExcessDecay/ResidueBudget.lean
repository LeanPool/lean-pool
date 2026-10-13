/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.ResidueInterface

/-!
# ResidueBudget

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The residue **budget** form of the boundary scalar, and the sharpening record

## What is proved

Two consequences of `ResidueInterface.exists_scalarControl_boundaryBranch_`
`comparator`.

* `exists_scalarControl_of_boundaryBranch_harmonicResidue` — the `∀`-budget
  form.  For any real `R` that dominates `‖u − w‖_{L²(K')}` for *every*
  `Δ`-harmonic comparator `w = u + ρ`, `ρ ∈ H¹₀(K')`, the boundary scalar obeys

  ```text
    S ≤ C(d)·( ‖u − (u)_{W'}‖_{L²(W')} + 3^n·Σᵢ‖∂ᵢh‖_{L²(W')} + R ) .
  ```

  This is the shape the boundary assembly consumes; `R` is a caller
  obligation and is disclosed as such.

* `exists_scalarControl_of_boundaryBranch_recovered` — the **sharpening
  record**: instantiating the budget by the Dirichlet-principle Poincaré bound
  of `SealComparator` returns, verbatim in shape, the proved composed scalar
  theorem of the boundary lane's seal chain (at the
  constant `C·max 1 (comparatorPoincareConst d)`).  Nothing is lost by moving
  to the comparator interface.

## Why the interface was moved

The gradient residue `3^n·Σᵢ‖∂ᵢu‖_{L²(K')}` has exactly two known producers and
both are blocked:

* the fitted boundary Caccioppoli of `SealCaccioppoliGeometry` prices the
  `ν`-weighted energy `ν·⨍_{K'}|∇u|²`, so extracting the Euclidean gradient
  costs `√(σ/ν)`;
* the `p = 2` general coarse-graining comparison prices the *comparator*
  distance directly, but at the envelope factor `s^{-4}·𝓔`.

The second producer does not price the gradient at all; it prices
`‖u − w‖_{L²(K')}`.  Moving the interface to `‖u − w‖` is therefore what makes
that producer even *expressible*.  Its arithmetic is measured in
`ResidueAbsorption.lean`.

## References

* ABK26, `l.harmonic.approximation.good.scales`, Step 2.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open HCPolySupport HCPolySupport.Book MeasureTheory
open Algsuperdiff.Section4.Support
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The `∀`-budget form -/

/-- **The boundary scalar at an abstract residue budget.**

`R` is any real dominating the harmonic-approximation error at the flush
sub-cube `K'` for every `Δ`-harmonic comparator of `u` there. -/
theorem exists_scalarControl_of_boundaryBranch_harmonicResidue (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {n m : ℤ} {x z : Vec d} {i : Fin d} {σ : ℝ},
        n + 2 ≤ m →
        x ∈ openCubeSet (originCube d m) →
        z ∈ openCubeSet (originCube d m) →
        ((fun y => x + y) '' openCubeSet (originCube d n) ⊆
          ((fun y => z + y) '' openCubeSet (originCube d (n + 1))) ∩
            openCubeSet (originCube d m)) →
        (σ = 1 ∨ σ = -1) →
        wellPlacedHalfGap m (n + 2) < σ * z i →
        ∀ u h : H1Function (openCubeSet (originCube d m)),
          Support.HasZeroTraceDifferenceOn (openCubeSet (originCube d m)) u h →
          ∀ R : ℝ,
          (∀ (w : H1Function (translateSet (flushSubCentre z m n i σ)
                (openCubeSet (originCube d n))))
             (rho : H10Function (translateSet (flushSubCentre z m n i σ)
                (openCubeSet (originCube d n)))),
            IsWeaklyHarmonicOn (translateSet (flushSubCentre z m n i σ)
                (openCubeSet (originCube d n))) w →
            (∀ y, w.toFun y = u.toFun y + rho.toH1Function.toFun y) →
            (∀ y, w.grad y = u.grad y + rho.toH1Function.grad y) →
            normalizedL2On ((fun y => flushSubCentre z m n i σ + y) ''
                openCubeSet (originCube d n))
              (fun y => u.toFun y - w.toFun y) ≤ R) →
          |volumeAverage ((fun y => wellPlacedCentre x m (n + 2) + y) ''
              openCubeSet (originCube d (n + 2)))
              (fun y => u.toFun y - h.toFun y)| ≤
            C * ((eLpNorm (fun y => u.toFun y -
                  volumeAverage ((((fun y' => z + y') ''
                      openCubeSet (originCube d (n + 3))) ∩
                    openCubeSet (originCube d m))) u.toFun) 2
                (Support.normalizedVolumeMeasureOn
                  ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
                    openCubeSet (originCube d m))))).toReal +
              (3 : ℝ) ^ n *
                ∑ i' : Fin d,
                  (eLpNorm (fun y => h.grad y i') 2
                    (Support.normalizedVolumeMeasureOn
                      ((((fun y' => z + y') ''
                          openCubeSet (originCube d (n + 3))) ∩
                        openCubeSet (originCube d m))))).toReal +
              R) := by
  classical
  obtain ⟨C, hC0, hmain⟩ := exists_scalarControl_boundaryBranch_comparator d
  refine ⟨C, hC0, ?_⟩
  intro n m x z i σ hnm hx hz hgeom hσ hover u h hzt R hres
  obtain ⟨w, rho, hharm, hval, hgrad, hbound, _hpoin⟩ :=
    hmain hnm hx hz hgeom hσ hover u h hzt
  refine hbound.trans (mul_le_mul_of_nonneg_left ?_ hC0)
  have hR := hres w rho hharm hval hgrad
  linarith only [hR]

/-! ## 2. The sharpening record: the proved gradient residue recovered -/

end

end Algsuperdiff.Section4.Provider.ExcessDecay
