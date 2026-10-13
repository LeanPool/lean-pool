/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Schauder.CubeSchauderData
public import LeanPool.HighContrastHomogenization.Support.Ambient.ScalarMatrix
public import LeanPool.HighContrastHomogenization.Support.Deterministic.HomogenizationBlackBoxes.Duality
public import LeanPool.HighContrastHomogenization.Support.Sobolev.PotentialSolenoidalL2Realization

/-!
# CubeSchauderExistence

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Cube Schauder, existence leg

```text
  -sigma Δ v = ∇ · g   in □_m ,      v = h   on ∂□_m
```

has a solution in the development's `IsDirichletSolutionOn` carrier.  This is
CoarseGraining's Lax--Milgram Dirichlet existence theorem
(`exists_isZeroTraceDirichletRhsWeakSolution_of_potentialZeroTraceClosureRealization`)
at the constant scalar background `sigma • I`, composed with the affine shift
by the datum `h`.

No estimate is proved here: the produced solution carries **no** regularity of
its gradient representative.  Every declaration is a proved local helper; no
source node is claimed, realized, or closed by this module.

## Main results

* `exists_isDirichletSolutionOn_smul_one` — existence with an arbitrary `H¹`
  datum.
* `exists_isDirichletSolutionOn_smul_one_of_holder` — the specialization whose
  forcing hypothesis is the frozen statement's Hölder bound.
-/

namespace Algsuperdiff.Section4.Provider.Schauder

open MeasureTheory
open HCPolySupport
open Algsuperdiff.Section4.Support
open HCPolySupport.PotentialSolenoidalL2Data

variable {d : ℕ}

/-! ## 1. The constant scalar background -/

/-- `(c • I) x = c • x`, at the exact spelling `c • (1 : Mat d)` of the frozen
statement. -/
theorem matVecMul_smul_one (c : ℝ) (x : Vec d) :
    matVecMul (c • (1 : Mat d)) x = c • x :=
  matVecMul_scalarMatrix c x

/-- `(1 : Mat d) x = x`. -/
theorem matVecMul_one (x : Vec d) : matVecMul (1 : Mat d) x = x := by
  have h := matVecMul_smul_one (1 : ℝ) x
  simpa using h

/-- The constant scalar background `sigma • I` is a `(sigma, sigma)`-elliptic
field on any measurable set. -/
theorem isEllipticFieldOn_smul_one {sigma : ℝ} (hsigma : 0 < sigma) {U : Set (Vec d)}
    (hU : MeasurableSet U) :
    IsEllipticFieldOn sigma sigma U (fun _ => sigma • (1 : Mat d)) :=
  isEllipticFieldOn_constantCoeffField hU (isEllipticMatrix_scalarMatrix hsigma)

/-! ## 2. Splitting the forcing pairing -/

section Pairing

variable {U : Set (Vec d)}

/-- The forcing pairing is odd in the force. -/
theorem integral_vecDot_neg_split (F : Vec d → Vec d) (φ : H10Function U) :
    ∫ x in U, vecDot (-F x) (φ.toH1Function.grad x) ∂volume =
      -∫ x in U, vecDot (F x) (φ.toH1Function.grad x) ∂volume := by
  have hfun : (fun x => vecDot (-F x) (φ.toH1Function.grad x)) =
      fun x => -vecDot (F x) (φ.toH1Function.grad x) := by
    funext x
    rw [vecDot_neg_left]
  rw [hfun, integral_neg]

/-- The forcing pairing is additive in the force. -/
theorem integral_vecDot_add_split {F G H : Vec d → Vec d}
    (hF : MemVectorL2 U F) (hG : MemVectorL2 U G) (hH : ∀ x, H x = F x + G x)
    (φ : H10Function U) :
    ∫ x in U, vecDot (H x) (φ.toH1Function.grad x) ∂volume =
      (∫ x in U, vecDot (F x) (φ.toH1Function.grad x) ∂volume) +
        ∫ x in U, vecDot (G x) (φ.toH1Function.grad x) ∂volume := by
  have hFint : IntegrableOn (fun x => vecDot (F x) (φ.toH1Function.grad x)) U :=
    integrableOn_vecDot_of_memVectorL2 hF φ.toH1Function.grad_memVectorL2
  have hGint : IntegrableOn (fun x => vecDot (G x) (φ.toH1Function.grad x)) U :=
    integrableOn_vecDot_of_memVectorL2 hG φ.toH1Function.grad_memVectorL2
  have hfun : (fun x => vecDot (H x) (φ.toH1Function.grad x)) =
      fun x => vecDot (F x) (φ.toH1Function.grad x) +
        vecDot (G x) (φ.toH1Function.grad x) := by
    funext x
    rw [hH x, vecDot_add_left]
  rw [hfun, integral_add hFint hGint]

/-- The forcing pairing is subtractive in the force. -/
theorem integral_vecDot_sub_split {F G H : Vec d → Vec d}
    (hF : MemVectorL2 U F) (hG : MemVectorL2 U G) (hH : ∀ x, H x = F x - G x)
    (φ : H10Function U) :
    ∫ x in U, vecDot (H x) (φ.toH1Function.grad x) ∂volume =
      (∫ x in U, vecDot (F x) (φ.toH1Function.grad x) ∂volume) -
        ∫ x in U, vecDot (G x) (φ.toH1Function.grad x) ∂volume := by
  have hFint : IntegrableOn (fun x => vecDot (F x) (φ.toH1Function.grad x)) U :=
    integrableOn_vecDot_of_memVectorL2 hF φ.toH1Function.grad_memVectorL2
  have hGint : IntegrableOn (fun x => vecDot (G x) (φ.toH1Function.grad x)) U :=
    integrableOn_vecDot_of_memVectorL2 hG φ.toH1Function.grad_memVectorL2
  have hfun : (fun x => vecDot (H x) (φ.toH1Function.grad x)) =
      fun x => vecDot (F x) (φ.toH1Function.grad x) -
        vecDot (G x) (φ.toH1Function.grad x) := by
    funext x
    rw [hH x, sub_eq_add_neg, vecDot_add_left, vecDot_neg_left, ← sub_eq_add_neg]
  rw [hfun, integral_sub hFint hGint]

/-- The forcing pairing is homogeneous in the force. -/
theorem integral_vecDot_smul_split (c : ℝ) (F : Vec d → Vec d) (φ : H10Function U) :
    ∫ x in U, vecDot (c • F x) (φ.toH1Function.grad x) ∂volume =
      c * ∫ x in U, vecDot (F x) (φ.toH1Function.grad x) ∂volume := by
  have hfun : (fun x => vecDot (c • F x) (φ.toH1Function.grad x)) =
      fun x => c * vecDot (F x) (φ.toH1Function.grad x) := by
    funext x
    rw [vecDot_smul_left]
  rw [hfun, integral_const_mul]

end Pairing

/-! ## 3. Existence -/

/-- **The comparator exists.**  For every scale, diffusivity, `H¹` datum and `L²`
forcing the constant-coefficient cube Dirichlet problem has a solution in the
development's carrier.  No regularity of `v.grad` is asserted. -/
theorem exists_isDirichletSolutionOn_smul_one [NeZero d] {m : ℤ} {sigma : ℝ}
    (hsigma : 0 < sigma) (h : H1Function (openCubeSet (originCube d m)))
    {g : Vec d → Vec d} (hg : MemVectorL2 (openCubeSet (originCube d m)) g) :
    ∃ v : H1Function (openCubeSet (originCube d m)),
      IsDirichletSolutionOn (fun _ => sigma • (1 : Mat d)) (originCube d m) v h g := by
  have hdom := isOpenBoundedConvexDomain_openCubeSet (originCube d m)
  have : IsFiniteMeasure (volumeMeasureOn (openCubeSet (originCube d m))) :=
    hdom.isFiniteMeasure_restrict_volume
  have hUmeas : MeasurableSet (openCubeSet (originCube d m)) :=
    measurableSet_openCubeSet (originCube d m)
  have hUne : Set.Nonempty (openCubeSet (originCube d m)) :=
    ⟨0, zero_mem_openCubeSet_originCube m⟩
  have hsh : MemVectorL2 (openCubeSet (originCube d m)) (fun x => sigma • h.grad x) :=
    h.grad_memVectorL2.const_smul sigma
  have hnsh : MemVectorL2 (openCubeSet (originCube d m)) (fun x => -(sigma • h.grad x)) :=
    hsh.neg
  have hforce : MemVectorL2 (openCubeSet (originCube d m))
      (fun x => -(sigma • h.grad x) - g x) := hnsh.sub hg
  have hreal :=
    hasPotentialZeroTraceClosureRealization_of_convexDomain hdom
  obtain ⟨w, hw⟩ :=
    exists_isZeroTraceDirichletRhsWeakSolution_of_potentialZeroTraceClosureRealization
      (a := fun _ => sigma • (1 : Mat d)) (U := openCubeSet (originCube d m))
      (g := fun x => -(sigma • h.grad x) - g x) (lam := sigma) (Lam := sigma)
      hforce hreal hUne (isEllipticFieldOn_smul_one hsigma hUmeas)
  refine ⟨h + w.toH1Function,
    ⟨w, fun x => by rw [H1Function.add_toFun], fun x => by rw [H1Function.add_grad]⟩, ?_⟩
  intro φ
  have hsw : MemVectorL2 (openCubeSet (originCube d m))
      (fun x => sigma • w.toH1Function.grad x) :=
    w.toH1Function.grad_memVectorL2.const_smul sigma
  have hflux : ∀ x, matVecMul ((fun _ => sigma • (1 : Mat d)) x)
      ((h + w.toH1Function).grad x)
      = (fun x => sigma • h.grad x) x + (fun x => sigma • w.toH1Function.grad x) x := by
    intro x
    change matVecMul (sigma • (1 : Mat d)) ((h + w.toH1Function).grad x)
      = sigma • h.grad x + sigma • w.toH1Function.grad x
    rw [H1Function.add_grad, matVecMul_smul_one, smul_add]
  rw [integral_vecDot_add_split hsh hsw hflux φ]
  have hwid := hw φ
  have hcongr : ∫ x in openCubeSet (originCube d m),
      vecDot (matVecMul ((fun _ => sigma • (1 : Mat d)) x) (w.toH1Function.grad x))
        (φ.toH1Function.grad x) ∂volume
      = ∫ x in openCubeSet (originCube d m),
        vecDot ((fun x => sigma • w.toH1Function.grad x) x)
          (φ.toH1Function.grad x) ∂volume :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => by
      change vecDot (matVecMul (sigma • (1 : Mat d)) (w.toH1Function.grad x))
          (φ.toH1Function.grad x)
        = vecDot (sigma • w.toH1Function.grad x) (φ.toH1Function.grad x)
      rw [matVecMul_smul_one])
  rw [hcongr] at hwid
  rw [hwid, integral_vecDot_sub_split hnsh hg (fun _ => rfl) φ,
    integral_vecDot_neg_split (fun x => sigma • h.grad x) φ]
  ring

/-- The existence leg with the frozen statement's Hölder hypothesis in place of
`L²` membership. -/
theorem exists_isDirichletSolutionOn_smul_one_of_holder [NeZero d] {m : ℤ}
    {sigma : ℝ} (hsigma : 0 < sigma) (h : H1Function (openCubeSet (originCube d m)))
    {g : Vec d → Vec d} {Kg : ℝ}
    (hKg : HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) Kg g) :
    ∃ v : H1Function (openCubeSet (originCube d m)),
      IsDirichletSolutionOn (fun _ => sigma • (1 : Mat d)) (originCube d m) v h g := by
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hKg0 : 0 ≤ Kg := holderSeminormBoundOn_nonneg_openCubeSet hd hKg
  exact exists_isDirichletSolutionOn_smul_one hsigma h
    (memVectorL2_of_holderSeminormBoundOn hKg0 (by norm_num) hKg)

end Algsuperdiff.Section4.Provider.Schauder
