/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.CaccioppoliInteriorGeometry
public import LeanPool.Superdiffusion.Support.Book.Ch03.Theorems.CoarseCaccioppoliRHS.Theory

/-!
# CaccioppoliInteriorDatum

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The interior regime of the coarse-grained Caccioppoli inequality with

CoarseGraining proves ABK26's `l.coarse.grained.Caccioppoli.RHS` in its
**boundary** form: the datum `BoundaryForcedCaccioppoliDatum Q a x g` bundles a
forced `H¹(Q)` solution together with the localized zero-trace condition

```text
  LocalizedZeroTraceFunctionOn (□_Q) (x + □_{Q.scale-1}) u ,
```

i.e. "`u` vanishes on the part of `∂Q` seen through the Dirichlet patch".  This
module observes that in the **interior** regime — the regime the frozen
theorem's frontier-empty clause selects, where the patch is a compact subset of
`Q` and the Dirichlet locus `∂Q ∩ (x + □_{Q.scale-1})` is empty — that
condition is *automatic*: multiplying by a smooth cutoff supported inside `Q`
proves in `H¹₀(Q)` for **every** `H¹(Q)` function.  So the boundary theorem's
interior specialization is unconditional in the boundary data, which is exactly
the statement needs ("the `h`-term vanishes").

Two further steps are performed here:

* **the geometric hypothesis is reduced to one inclusion.**  CoarseGraining
  asks for both `x ∈ □_Q` and the patch condition; the patch inclusion implies
  the former (the patch contains its own centre).

## What is not done here

Nothing in this module identifies the coefficient field of the frozen theorem's
Dirichlet problem on `□_m` with a `CoeffFamily` at the parent cube, and nothing
restricts an equation from `□_m` to the parent: both are inputs, supplied by
the caller.  The module is purely the interior specialization of
CoarseGraining's theorem plus the constant shift.

## References

* ABK26, `l.coarse.grained.Caccioppoli.RHS`.
* ABK26, `e.energy.bound.interior`.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch03

noncomputable section

variable {d : ℕ}

/-! ## 1. The interior regime makes the localized zero trace automatic -/

/-- **The interior localization.**  If the localization window sits inside a
bounded open convex domain, then *every* `H¹` function of that domain satisfies
the localized zero-trace condition: a smooth cutoff supported in the window has
compact support inside the domain, so the product is an admissible `H¹₀` test
function.  This is the Lean content of "in the interior regime the Dirichlet
locus is empty". -/
theorem localizedZeroTraceFunctionOn_of_memH1 {U V : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) (hVU : V ⊆ U) {u : Vec d → ℝ}
    (hu : MemH1 U u) : LocalizedZeroTraceFunctionOn U V u := by
  intro eta heta heta_compact heta_sub
  exact memH10_mul_of_contDiff_hasCompactSupport hU heta heta_compact
    (heta_sub.trans hVU) hu

/-- A cube window contains its own centre. -/
theorem mem_openCubeAtScale_self (x : Vec d) (m : ℤ) :
    x ∈ openCubeAtScale x m := by
  intro i
  have h3 : (0 : ℝ) < Real.rpow (3 : ℝ) ((m : ℤ) : ℝ) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hzero : |x i - x i| = 0 := by
    rw [sub_self, abs_zero]
  rw [hzero]
  linarith only [h3]

/-! ## 2. The interior forced datum, with a constant subtracted -/

/-- The constant function as an `H¹` function of a cube. -/
def constH1 (Q : TriadicCube d) (c : ℝ) :
    H1Function (Ch02.cubeDomain Q : Set (Vec d)) :=
  H1Function.ofContDiffOnIsOpenBoundedConvexDomain
    (by
      rw [Ch02.cubeDomain_coe]
      exact isOpenBoundedConvexDomain_openCubeSet Q)
    (contDiff_const : ContDiff ℝ 1 fun _ : Vec d => c)

private theorem constH1_toFun (Q : TriadicCube d) (c : ℝ) :
    (constH1 Q c).toFun = fun _ => c := rfl

private theorem constH1_grad (Q : TriadicCube d) (c : ℝ) :
    (constH1 Q c).grad = fun _ => (0 : Vec d) := by
  funext y
  funext i
  change (fderiv ℝ (fun _ : Vec d => c) y) (basisVec i) = 0
  rw [fderiv_fun_const]
  rfl

/-- The gradient of a constant-shifted `H¹` function. -/
theorem sub_constH1_grad (Q : TriadicCube d)
    (u : H1Function (Ch02.cubeDomain Q : Set (Vec d))) (c : ℝ) :
    (u - constH1 Q c).grad = u.grad := by
  rw [H1Function.sub_grad, constH1_grad]
  funext y
  exact sub_zero (u.grad y)

/-- The values of a constant-shifted `H¹` function. -/
private theorem sub_constH1_toFun (Q : TriadicCube d)
    (u : H1Function (Ch02.cubeDomain Q : Set (Vec d))) (c : ℝ) :
    (u - constH1 Q c).toFun = fun y => u.toFun y - c := by
  funext y
  rw [H1Function.sub_toFun, constH1_toFun]

/-- **The interior forced Caccioppoli datum with a constant subtracted.**

The equation is unchanged (it only sees `∇u`), and the localized zero-trace
condition is discharged by the interior localization.  This is the object the
interior regime feeds to CoarseGraining's boundary theorem. -/
def interiorForcedCaccioppoliDatumSubConst {Q : TriadicCube d} {a : CoeffFamily d}
    (x : Vec d) {g : Vec d → Vec d}
    (u : H1Function (Ch02.cubeDomain Q : Set (Vec d))) (c : ℝ)
    (hu : IsForcedEquation Q a u g)
    (hpatch : openCubeAtScale x (Q.scale - 1) ⊆ openCubeSet Q) :
    BoundaryForcedCaccioppoliDatum Q a x g where
  toH1 := u - constH1 Q c
  weakSolution := by
    intro phi
    rw [sub_constH1_grad]
    exact hu phi
  zeroTraceOnBoundaryPatch := by
    refine localizedZeroTraceFunctionOn_of_memH1
      (by
        rw [Ch02.cubeDomain_coe]
        exact isOpenBoundedConvexDomain_openCubeSet Q)
      (by
        rw [Ch02.cubeDomain_coe]
        exact hpatch)
      ⟨u - constH1 Q c, rfl⟩

private theorem datum_toH1_grad {Q : TriadicCube d} {a : CoeffFamily d}
    (x : Vec d) {g : Vec d → Vec d}
    (u : H1Function (Ch02.cubeDomain Q : Set (Vec d))) (c : ℝ)
    (hu : IsForcedEquation Q a u g)
    (hpatch : openCubeAtScale x (Q.scale - 1) ⊆ openCubeSet Q) :
    (interiorForcedCaccioppoliDatumSubConst x u c hu hpatch).toH1.grad = u.grad :=
  sub_constH1_grad Q u c

private theorem datum_toH1_toFun {Q : TriadicCube d} {a : CoeffFamily d}
    (x : Vec d) {g : Vec d → Vec d}
    (u : H1Function (Ch02.cubeDomain Q : Set (Vec d))) (c : ℝ)
    (hu : IsForcedEquation Q a u g)
    (hpatch : openCubeAtScale x (Q.scale - 1) ⊆ openCubeSet Q) :
    (interiorForcedCaccioppoliDatumSubConst x u c hu hpatch).toH1.toFun =
      fun y => u.toFun y - c :=
  sub_constH1_toFun Q u c

/-! ## 3. The interior energy estimate -/

/-- The local coefficient energy sees only the gradient. -/
theorem localizedCoeffEnergyValue_congr_grad {U : Ch02.Domain d} (V : Set (Vec d))
    (a : Ch02.CoeffOn U) {u v : H1Function (U : Set (Vec d))}
    (hgrad : v.grad = u.grad) :
    localizedCoeffEnergyValue V a v = localizedCoeffEnergyValue V a u := by
  rw [localizedCoeffEnergyValue, localizedCoeffEnergyValue, hgrad]

/-- **The interior coarse-grained Caccioppoli inequality with right-hand side,
mean-subtracted.**

For every forced `H¹(Q)` solution whose Dirichlet patch `x + □_{Q.scale-1}` sits
inside `Q` (the interior regime) and every real `c`,

```text
  ⨍_{□_Q ∩ (x+□_{Q.scale-2})} ∇u · ã ∇u
      ≤  prefactor(C,Q,a,s,t)
         ( λ_{t,1} 3^{-2·scale} ‖u - c‖²_{L²(Q)}
           + t^{-8}(1-2t)^{-1} λ_{t,1}^{-1} [g]²_{B^{2t}(Q)} ) ,
```

with `prefactor` CoarseGraining's `caccioppoliWithRHSPrefactor`, i.e. the printed
`(C/σ)^{2+4s/σ} s^{-2s/σ} Θ_{s,t}^{(1-t)/σ}` at `σ = 1-s-t`.

Only the boundary data has been specialized (to the interior regime); the
`∇h`-term of the printed lemma is absent because CoarseGraining's datum carries
the homogeneous localized trace. -/
theorem exists_interiorCaccioppoliEnergy_subConst (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Q : TriadicCube d} {a : CoeffFamily d} {s t : ℝ} {x : Vec d}
        {g : Vec d → Vec d}
        (u : H1Function (Ch02.cubeDomain Q : Set (Vec d))) (c : ℝ),
        IsForcedEquation Q a u g →
        0 < s → s < 1 → 0 < t → t < 1 / 2 → s + t < 1 →
        openCubeAtScale x (Q.scale - 1) ⊆ openCubeSet Q →
        ForceBesovRegularity Q (2 * t) g →
          localizedCoeffEnergyValue (caccioppoliCoreSet Q x) (a.coeffOn Q) u ≤
            caccioppoliWithRHSPrefactor C Q a s t *
              (Ch02.lambdaS Q t a *
                  Real.rpow (3 : ℝ) (-2 * (((Q.scale : ℤ) : ℝ))) *
                  normalizedL2SqOnSet (openCubeSet Q) (fun y => u.toFun y - c) +
                (Real.rpow t (-8 : ℝ) / (1 - 2 * t)) *
                  Real.rpow (Ch02.lambdaS Q t a) (-1 : ℝ) *
                  scaleNormalizedPositiveBesovVectorSeminormTwo Q (2 * t) g ^ 2) := by
  obtain ⟨C, hCpos, hC⟩ := (coarseCaccioppoliRHSTheory (d := d)).exists_constant
  refine ⟨C, hCpos, ?_⟩
  intro Q a s t x g u c hu hs hs1 ht ht2 hst hpatch hg
  have hx : x ∈ openCubeSet Q := hpatch (mem_openCubeAtScale_self x (Q.scale - 1))
  have hbound := hC (interiorForcedCaccioppoliDatumSubConst x u c hu hpatch)
    hs hs1 ht ht2 hst hx hg
  rw [boundaryForcedCaccioppoliCoreEnergy,
    localizedCoeffEnergyValue_congr_grad (caccioppoliCoreSet Q x) (a.coeffOn Q)
      (datum_toH1_grad x u c hu hpatch)] at hbound
  rw [boundaryCaccioppoliWithRHSRHS, boundaryForcedCaccioppoliParentL2Sq,
    datum_toH1_toFun] at hbound
  exact hbound

end

end Algsuperdiff.Section4.Provider.ExcessDecay
