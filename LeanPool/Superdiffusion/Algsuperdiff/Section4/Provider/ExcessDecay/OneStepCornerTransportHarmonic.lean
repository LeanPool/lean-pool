/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepSchauderBridge
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Foundations.CubeReflection.Reflections

/-!
# OneStepCornerTransportHarmonic

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Classical harmonicity under a coordinate negation

The analytic half of the lower/mixed-face transport of the §4.3 boundary
branch.  The proved odd-class apparatus is stated at **upper** met faces; the
domain cube `□_m` is origin-symmetric, so negating one coordinate carries a
lower-face-met window to an upper-face-met one.  For that transport to be
usable the classical harmonicity of the competitor has to travel with it, which
is what this module supplies.

## The mechanism

Precomposition with a linear isometry equivalence `L` of the Euclidean carrier
commutes with the Laplacian:

```text
  Δ (f ∘ L) = (Δ f) ∘ L ,
```

with **no** differentiability hypothesis.  Indeed the iterated derivative of a
right-composition with a continuous linear equivalence is unconditional
(`ContinuousLinearEquiv.iterated at `s = univ`), and `Δ` may be read in *any*
orthonormal basis (`laplacian_eq_iterated), in particular in the image `L ∘ b`
of a fixed one.  Harmonicity then transports because `ContDiffAt` composes and
the vanishing germ of `Δ f` pulls back along the continuous `L`.

Coordinate negation is such an `L`: it is `LinearIsometryEquiv.piLpCongrRight
2` of the per-coordinate negations, and it matches CoarseGraining's
`coordFaceReflection (0 : ℝ) i` across the carrier identification `toEuc`.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

open InnerProductSpace
open scoped Laplacian
open HCPolySupport (Vec coordFaceReflection)

noncomputable section

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-! ## 1. The Laplacian under a linear isometry of the domain -/

/-- **The Laplacian commutes with precomposition by a linear isometry
equivalence.**  Unconditional: no differentiability of `f` is needed. -/
theorem laplacian_comp_linearIsometryEquiv (f : 𝔼 → ℝ) (L : 𝔼 ≃ₗᵢ[ℝ] 𝔼) (z : 𝔼) :
    Δ (f ∘ (L : 𝔼 → 𝔼)) z = Δ f (L z) := by
  classical
  have hb := congrFun
    (laplacian_eq_iteratedFDeriv_orthonormalBasis (f ∘ (L : 𝔼 → 𝔼))
      (EuclideanSpace.basisFun (Fin d) ℝ)) z
  have hb2 := congrFun
    (laplacian_eq_iteratedFDeriv_orthonormalBasis f
      ((EuclideanSpace.basisFun (Fin d) ℝ).map L)) (L z)
  rw [hb, hb2]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hcomp : iteratedFDeriv ℝ 2 (f ∘ (L : 𝔼 → 𝔼)) z
      = (iteratedFDeriv ℝ 2 f (L z)).compContinuousLinearMap
          (fun _ => (L.toContinuousLinearEquiv : 𝔼 →L[ℝ] 𝔼)) := by
    have h := (L.toContinuousLinearEquiv).iteratedFDerivWithin_comp_right f
      (s := (Set.univ : Set 𝔼)) uniqueDiffOn_univ (x := z) (Set.mem_univ _) 2
    simpa [iteratedFDerivWithin_univ] using h
  simp only [OrthonormalBasis.map_apply]
  rw [hcomp]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  congr 1
  funext j
  fin_cases j <;> rfl

/-- **Harmonicity travels with a linear isometry of the domain.** -/
theorem harmonicAt_comp_linearIsometryEquiv {f : 𝔼 → ℝ} (L : 𝔼 ≃ₗᵢ[ℝ] 𝔼) {z : 𝔼}
    (h : HarmonicAt f (L z)) : HarmonicAt (f ∘ (L : 𝔼 → 𝔼)) z := by
  refine ⟨h.1.comp z L.toContinuousLinearEquiv.contDiff.contDiffAt, ?_⟩
  have hcomp : Δ (f ∘ (L : 𝔼 → 𝔼)) = fun w => Δ f (L w) := by
    funext w
    exact laplacian_comp_linearIsometryEquiv f L w
  rw [hcomp]
  have htend : Filter.Tendsto (L : 𝔼 → 𝔼) (nhds z) (nhds (L z)) :=
    L.continuous.continuousAt
  exact h.2.comp_tendsto htend

/-! ## 2. Coordinate negation as a linear isometry -/

/-- Negation of the `i`-th coordinate of the Euclidean carrier, as a linear
isometry equivalence. -/
def negCoordLIE (i : Fin d) : 𝔼 ≃ₗᵢ[ℝ] 𝔼 :=
  LinearIsometryEquiv.piLpCongrRight 2
    (fun l => if l = i then LinearIsometryEquiv.neg ℝ else LinearIsometryEquiv.refl ℝ ℝ)

@[simp] theorem negCoordLIE_apply (i : Fin d) (z : 𝔼) (l : Fin d) :
    negCoordLIE i z l = if l = i then -(z l) else z l := by
  rw [negCoordLIE]
  by_cases h : l = i
  · simp [LinearIsometryEquiv.piLpCongrRight_apply, h]
  · simp [LinearIsometryEquiv.piLpCongrRight_apply, h]

/-- The Euclidean coordinate negation is CoarseGraining's `coordFaceReflection (0:
ℝ) i` read across the carrier identification. -/
theorem toEuc_symm_negCoordLIE (i : Fin d) (z : 𝔼) :
    (toEuc.symm : 𝔼 → Vec d) (negCoordLIE i z)
      = coordFaceReflection (0 : ℝ) i ((toEuc.symm : 𝔼 → Vec d) z) := by
  funext l
  rw [toEuc_symm_apply, negCoordLIE_apply, HCPolySupport.coordFaceReflection_apply,
    toEuc_symm_apply]
  by_cases h : l = i
  · rw [ite_eq_left h, ite_eq_left h]
    ring
  · rw [ite_eq_right h, ite_eq_right h]

theorem toEuc_negCoordLIE (i : Fin d) (y : Vec d) :
    negCoordLIE i ((toEuc : Vec d → 𝔼) y)
      = (toEuc : Vec d → 𝔼) (coordFaceReflection (0 : ℝ) i y) := by
  have h := toEuc_symm_negCoordLIE i ((toEuc : Vec d → 𝔼) y)
  rw [ContinuousLinearEquiv.symm_apply_apply] at h
  have h2 := congrArg (toEuc : Vec d → 𝔼) h
  rwa [ContinuousLinearEquiv.apply_symm_apply] at h2

/-! ## 3. The transport of `HarmonicOnNhd` -/

/-- **Classical harmonicity under a coordinate negation.**  If `V` is harmonic on
(the Euclidean image of) `S`, then `V ∘ σ_i` is harmonic on the Euclidean image
of `σ_i ⁻¹' S`. -/
theorem harmonicOnNhd_comp_coordFaceReflection_zero {S : Set (Vec d)} {V : Vec d → ℝ}
    (i : Fin d)
    (hV : HarmonicOnNhd (V ∘ (toEuc.symm : 𝔼 → Vec d)) ((toEuc : Vec d → 𝔼) '' S)) :
    HarmonicOnNhd
      ((fun y => V (coordFaceReflection (0 : ℝ) i y)) ∘ (toEuc.symm : 𝔼 → Vec d))
      ((toEuc : Vec d → 𝔼) '' (coordFaceReflection (0 : ℝ) i ⁻¹' S)) := by
  have hfun : (fun y => V (coordFaceReflection (0 : ℝ) i y)) ∘ (toEuc.symm : 𝔼 → Vec d)
      = (V ∘ (toEuc.symm : 𝔼 → Vec d)) ∘ (negCoordLIE i : 𝔼 → 𝔼) := by
    funext z
    change V (coordFaceReflection (0 : ℝ) i ((toEuc.symm : 𝔼 → Vec d) z))
      = V ((toEuc.symm : 𝔼 → Vec d) (negCoordLIE i z))
    rw [toEuc_symm_negCoordLIE]
  rw [hfun]
  rintro e ⟨y, hy, rfl⟩
  refine harmonicAt_comp_linearIsometryEquiv (negCoordLIE i) ?_
  refine hV _ ⟨coordFaceReflection (0 : ℝ) i y, hy, ?_⟩
  exact (toEuc_negCoordLIE i y).symm

end

end Algsuperdiff.Section4.Provider.ExcessDecay.Schauder
