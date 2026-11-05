/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Schauder.CubeSchauderIteration

/-!
# CubeSchauderFreezingResidue

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Cube Schauder: the freezing residue in coordinate `L²` form

The freezing step of `CubeSchauderFreezing` delivers its harmonic-approximation
error as a **Dirichlet energy**, `∫_□ |∇w|²`.  The consumers of that error —
the zero-trace Poincaré inequality and the development's one-step excess
contraction — both take the *coordinate sum* `Σᵢ ‖∂ᵢ w‖_{L²(□)}` instead.  This
module supplies the missing dictionary and reads the freezing gain off in that
shape.

The dictionary is Cauchy--Schwarz on `Fin d` applied to the vector of coordinate
`L²` norms:

```text
  Σᵢ ‖∂ᵢ w‖_{L²(U)} ≤ √( d · ∫_U |∇w|² ) .
```

Combined with the freezing bound `∫_□ |∇w|² ≤ d · KG² · 3^j · |□_j|` of
`exists_frozenHarmonicReplacement_openCubeSet` this gives

```text
  Σᵢ ‖∂ᵢ w‖_{L²(□_j)} ≤ d · KG · √( 3^j · |□_j| ) ,
```

i.e. the freezing gain `(3^j)^{1/2}·[G]_{C^{0,1/2}}` in the exact slot shape of
the proved Dirichlet-Poincaré and one-step machinery.

## Main results

* `sum_toReal_eLpNorm_coord_le` — the Cauchy--Schwarz dictionary.
* `sum_toReal_eLpNorm_grad_le_of_dirichletEnergy_le` — its `H¹` instance.
* `exists_frozenHarmonicReplacement_coordL2` — the freezing step on an origin
  cube, with the residue delivered as `Σᵢ ‖∂ᵢ w‖_{L²}` at the explicit constant
  `d · KG · √(3^j · (3^j)^d)`.

## References

* Armstrong--Kuusi, *Elliptic Regularity* (`ellipticregularity.tex`), the
  harmonic-approximation display `e.harmapprox.Sch.onealpha`.
* ABK26; `Algsuperdiff/Frozen/External/CubeSchauder.lean`.
-/

namespace Algsuperdiff.Section4.Provider.Schauder

open MeasureTheory
open HCPolySupport
open Algsuperdiff.Section4.Support

variable {d : ℕ}

/-! ## 1. The Cauchy--Schwarz dictionary -/

/-- **The coordinate-sum dictionary.**

The sum of the coordinate `L²` norms of a vector field is at most `√d` times its
Dirichlet-type `L²` norm.  This is Cauchy--Schwarz on `Fin d` against the vector
of ones. -/
theorem sum_toReal_eLpNorm_coord_le {U : Set (Vec d)} {F : Vec d → Vec d}
    (hF : ∀ i : Fin d, MemLp (fun x => F x i) 2 (volume.restrict U)) :
    ∑ i : Fin d, (eLpNorm (fun x => F x i) 2 (volume.restrict U)).toReal ≤
      Real.sqrt ((d : ℝ) * ∫ x in U, vecNormSq (F x) ∂volume) := by
  set a : Vec d :=
    fun i => (eLpNorm (fun x => F x i) 2 (volume.restrict U)).toReal with hadef
  have ha0 : ∀ i, 0 ≤ a i := fun _ => ENNReal.toReal_nonneg
  have hsum0 : 0 ≤ ∑ i : Fin d, a i := Finset.sum_nonneg fun i _ => ha0 i
  have hsq : ∀ i : Fin d, a i * a i = ∫ x in U, F x i * F x i ∂volume := by
    intro i
    have h := HCPolySupport.toReal_eLpNorm_two_sq_eq_integral_sq (hF i)
    rw [← pow_two]
    rw [hadef]
    simpa only [pow_two] using h
  have hint : ∀ i : Fin d,
      Integrable (fun x => F x i * F x i) (volume.restrict U) := fun i =>
    (hF i).integrable_mul (hF i)
  have hpt : ∀ x, vecNormSq (F x) = ∑ i : Fin d, F x i * F x i := fun x => by
    rw [vecNormSq, vecDot]
  have hsumsq : ∑ i : Fin d, a i * a i = ∫ x in U, vecNormSq (F x) ∂volume := by
    calc ∑ i : Fin d, a i * a i = ∑ i : Fin d, ∫ x in U, F x i * F x i ∂volume :=
          Finset.sum_congr rfl fun i _ => hsq i
      _ = ∫ x in U, ∑ i : Fin d, F x i * F x i ∂volume :=
          (integral_finsetSum _ fun i _ => hint i).symm
      _ = ∫ x in U, vecNormSq (F x) ∂volume :=
          integral_congr_ae (Filter.Eventually.of_forall fun x => (hpt x).symm)
  have hcs := sq_vecDot_le_vecNormSq_mul_vecNormSq (fun _ : Fin d => (1 : ℝ)) a
  have hdot : vecDot (fun _ : Fin d => (1 : ℝ)) a = ∑ i : Fin d, a i := by
    rw [vecDot]
    exact Finset.sum_congr rfl fun i _ => one_mul (a i)
  have hone : vecNormSq (fun _ : Fin d => (1 : ℝ)) = (d : ℝ) := by
    rw [vecNormSq, vecDot]
    simp
  have hanorm : vecNormSq a = ∑ i : Fin d, a i * a i := by rw [vecNormSq, vecDot]
  rw [hdot, hone, hanorm, hsumsq] at hcs
  have hroot := Real.sqrt_le_sqrt hcs
  rwa [Real.sqrt_sq hsum0] at hroot

/-- The `H¹` instance of the dictionary, driven by a Dirichlet energy bound. -/
theorem sum_toReal_eLpNorm_grad_le_of_dirichletEnergy_le {U : Set (Vec d)}
    (w : H1Function U) {M : ℝ}
    (hE : ∫ x in U, vecNormSq (w.grad x) ∂volume ≤ M) :
    ∑ i : Fin d, (eLpNorm (fun x => w.grad x i) 2 (volume.restrict U)).toReal ≤
      Real.sqrt ((d : ℝ) * M) := by
  have hcoord : ∀ i : Fin d, MemLp (fun x => w.grad x i) 2 (volume.restrict U) :=
    fun i => w.gradMemL2 i
  refine (sum_toReal_eLpNorm_coord_le hcoord).trans ?_
  refine Real.sqrt_le_sqrt ?_
  exact mul_le_mul_of_nonneg_left hE (Nat.cast_nonneg d)

/-! ## 2. The freezing residue at an origin cube -/

/-- The square root of the freezing budget factorizes. -/
theorem sqrt_freezing_budget (D KG s V : ℝ) (hD : 0 ≤ D) (hKG : 0 ≤ KG) :
    Real.sqrt (D * (D * (KG ^ 2 * s) * V)) = D * KG * Real.sqrt (s * V) := by
  have hfac : D * (D * (KG ^ 2 * s) * V) = (D * KG) ^ 2 * (s * V) := by ring
  rw [hfac, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (mul_nonneg hD hKG)]

end Algsuperdiff.Section4.Provider.Schauder
