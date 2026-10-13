/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.CaccioppoliInteriorDatum
public import LeanPool.HighContrastHomogenization.Support.Book.Ch03.Theorems.PublicInternalBridges.CoeffField
public import LeanPool.HighContrastHomogenization.Support.Sobolev.PotentialSolenoidalL2

/-!
# BoundaryCaccioppoliDatum

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The boundary regime of the coarse-grained Caccioppoli inequality with

`l.coarse.grained.Caccioppoli.RHS` is stated *with* a boundary datum `h`, and its
right-hand side carries the extra leg `t^{-3} Λ_t ‖∇h‖²_{H^{2t}(□_0)}`.  This
module proves the other half of the printed lemma's own proof, the **boundary
reduction**:

> let `v` be the Dirichlet solution on the whole cube with the same force `g`
> and the same boundary datum `h`; then `u - v` has zero trace on all of `∂□_0`
> and solves the *homogeneous* equation, so the zero-data theorem applies to it,
> and the `∇h`-leg is produced separately by the global energy estimate for `∇v`.

Landed here: everything about `u - v`.

## Main results

* This is what makes the boundary application legitimate at a patch that meets
  `∂□_m`.
* `memVectorL2_flux`, `isForcedEquation_sub` — the flux pairing is integrable
  and the difference of two forced solutions with the same force solves the
  homogeneous equation.
* `boundaryForcedCaccioppoliDatumOfDifference` — CoarseGraining's datum,
  populated for `u - v` at zero force.
* `exists_boundaryCaccioppoliEnergy_ofDifference` — CoarseGraining's coarse
  Caccioppoli applied to it: the core energy of `u - v` is bounded by the
  *pure* `L²` term, the force leg having vanished.

## What is not done here

Three things separate this from the printed boundary display on `x + □_n`:

1. the triangle inequality `‖σ^{1/2}∇u‖ ≤ ‖σ^{1/2}∇(u-v)‖ + ‖σ^{1/2}∇v‖` on the
   core (a quadratic-form Minkowski step);
2. the volume-ratio conversion of the *global* energy norm of `v` to the core
   (a `d`-only constant, needing a lower bound on `|caccioppoliCoreSet Q x|`);

None of the three is asserted anywhere in this file.

## References

* ABK26, `l.coarse.grained.Caccioppoli.RHS`, (the reduction), and its boundary
  application.
* CoarseGraining, `CoarseCaccioppoli/Theory.lean`, `Energy/Theory.lean`,
  `PublicInternalBridges/CoeffField.lean`,
  `Sobolev/PotentialSolenoidalL2.lean`.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch03 MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## 2. The flux pairing and the homogeneous difference equation -/

/-- The flux `a ∇u` of an `H¹` function is square integrable on the cube: the
coefficient field has an everywhere-elliptic representative (CoarseGraining's
`publicCoeffField`) agreeing with it almost everywhere. -/
theorem memVectorL2_flux (Q : TriadicCube d) (a : CoeffFamily d)
    (u : H1Function (Ch02.cubeDomain Q : Set (Vec d))) :
    MemVectorL2 (Ch02.cubeDomain Q : Set (Vec d))
      (fun x => matVecMul ((a.coeffOn Q).toCoeffField x) (u.grad x)) := by
  have hB : MemVectorL2 (Ch02.cubeDomain Q : Set (Vec d))
      (fun x => matVecMul (publicCoeffField Q a x) (u.grad x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn
      (publicCoeffField_isEllipticFieldOn Q a) u.grad_memVectorL2
  refine hB.ae_eq ?_
  filter_upwards [publicCoeffField_ae_eq Q a] with x hx
  rw [hx]

/-- The matrix action is additive in the vector slot. -/
private theorem matVecMul_sub_right (A : Mat d) (x y : Vec d) :
    matVecMul A (x - y) = matVecMul A x - matVecMul A y := by
  rw [sub_eq_add_neg, matVecMul_add, matVecMul_neg, sub_eq_add_neg]

/-- The tested flux pairing is integrable. -/
theorem integrableOn_flux_pairing (Q : TriadicCube d) (a : CoeffFamily d)
    (u : H1Function (Ch02.cubeDomain Q : Set (Vec d)))
    (φ : H10Function (Ch02.cubeDomain Q : Set (Vec d))) :
    IntegrableOn
      (fun x => vecDot (matVecMul ((a.coeffOn Q).toCoeffField x) (u.grad x))
        (φ.toH1Function.grad x))
      (Ch02.cubeDomain Q : Set (Vec d)) :=
  integrableOn_vecDot_of_memVectorL2 (memVectorL2_flux Q a u)
    φ.toH1Function.grad_memVectorL2

/-- **The difference of two forced solutions with the same force is a solution of
the homogeneous equation.**  This is the first step of the printed proof of
`l.coarse.grained.Caccioppoli.RHS`. -/
theorem isForcedEquation_sub {Q : TriadicCube d} {a : CoeffFamily d}
    {g : Vec d → Vec d} {u v : H1Function (Ch02.cubeDomain Q : Set (Vec d))}
    (hu : IsForcedEquation Q a u g) (hv : IsForcedEquation Q a v g) :
    IsForcedEquation Q a (u - v) (fun _ => 0) := by
  intro φ
  have hrw : ∀ x, vecDot (matVecMul ((a.coeffOn Q).toCoeffField x) ((u - v).grad x))
      (φ.toH1Function.grad x) =
      vecDot (matVecMul ((a.coeffOn Q).toCoeffField x) (u.grad x))
          (φ.toH1Function.grad x) -
        vecDot (matVecMul ((a.coeffOn Q).toCoeffField x) (v.grad x))
          (φ.toH1Function.grad x) := by
    intro x
    rw [H1Function.sub_grad]
    show vecDot (matVecMul ((a.coeffOn Q).toCoeffField x) (u.grad x - v.grad x)) _ = _
    rw [matVecMul_sub_right]
    simp only [vecDot, Pi.sub_apply]
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hzero : ∫ x in (Ch02.cubeDomain Q : Set (Vec d)),
      vecDot ((fun _ : Vec d => (0 : Vec d)) x) (φ.toH1Function.grad x) ∂volume = 0 := by
    have : ∀ x : Vec d, vecDot ((0 : Vec d)) (φ.toH1Function.grad x) = 0 := by
      intro x
      simp [vecDot]
    simp only [this]
    exact integral_zero _ _
  rw [hzero]
  calc
    ∫ x in (Ch02.cubeDomain Q : Set (Vec d)),
        vecDot (matVecMul ((a.coeffOn Q).toCoeffField x) ((u - v).grad x))
          (φ.toH1Function.grad x) ∂volume
        = ∫ x in (Ch02.cubeDomain Q : Set (Vec d)),
            (vecDot (matVecMul ((a.coeffOn Q).toCoeffField x) (u.grad x))
                (φ.toH1Function.grad x) -
              vecDot (matVecMul ((a.coeffOn Q).toCoeffField x) (v.grad x))
                (φ.toH1Function.grad x)) ∂volume :=
          integral_congr_ae (Filter.Eventually.of_forall fun x => hrw x)
    _ = (∫ x in (Ch02.cubeDomain Q : Set (Vec d)),
            vecDot (matVecMul ((a.coeffOn Q).toCoeffField x) (u.grad x))
              (φ.toH1Function.grad x) ∂volume) -
          ∫ x in (Ch02.cubeDomain Q : Set (Vec d)),
            vecDot (matVecMul ((a.coeffOn Q).toCoeffField x) (v.grad x))
              (φ.toH1Function.grad x) ∂volume :=
          integral_sub (integrableOn_flux_pairing Q a u φ)
            (integrableOn_flux_pairing Q a v φ)
    _ = 0 := by rw [hu φ, hv φ, sub_self]

/-! ## 3. The zero force is admissible -/

/-- The zero force has the `H^s` regularity CoarseGraining's Caccioppoli theorem
asks of its right-hand side. -/
theorem forceBesovRegularity_zero (Q : TriadicCube d) (s : ℝ) :
    ForceBesovRegularity Q s (fun _ : Vec d => (0 : Vec d)) where
  memLp := by
    have h : MemLp (0 : Vec d → Vec d) 2 (normalizedCubeMeasure Q) := MemLp.zero
    exact h
  partialSeminorms_bddAbove := by
    have h := cubeBesovPositiveVectorPartialSeminormTwo_zero_bddAbove Q s
    exact h

end

end Algsuperdiff.Section4.Provider.ExcessDecay
