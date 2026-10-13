/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.HighContrastHomogenization.Support.Book.Ch03.Theorems.PublicInternalBridges.WeakSolutionConstructors

/-!
# HarmonicReplacement

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Harmonic-replacement well-posedness: the constant-coefficient Dirichlet replacement

Nothing here imports that file, and nothing here claims the anchor or any
source node.

## What is built

ABK26's Step 1 introduces two constant-coefficient comparison functions on the
child window `W = x+□_n`:

```text
  -Δ v = 0            in W ,   v   = u  on ∂W;
  -σ Δ v_g = ∇·g      in W ,   v_g = u  on ∂W .
```

This module produces both, and their uniqueness, from CoarseGraining.

```text
  exists_isZeroTraceDirichletRhsWeakSolution_of_potentialZeroTraceClosureRealization
      (a := a) (U := U) (g := G) …
    :  ∃ v : H10Function U, IsZeroTraceDirichletRhsWeakSolution a U v G
```

(`PDE.exists_isZeroTraceDirichletRhsWeakSolution_of_potentialZeroTraceClosureRealization`),
an `H¹₀(U)` weak solution of `−∇·a∇ρ = ∇·G` for any `G ∈ L²(U)` and any
elliptic field `a`, together with its defining identity and the uniqueness
statements
`IsZeroTraceDirichletRhsWeakSolution.gradToVectorL2_eq_of_isEllipticFieldOn`
and `.toScalarL2_eq_of_isOpenBoundedConvexDomain`.  The closure-realization
hypothesis is discharged on an open cube by
`hasPotentialZeroTraceClosureRealization_of_isOpenBoundedConvexDomain`.
Nothing had to be reinvented: the whole content of this module is the affine
shift `v = u − ρ` that converts the *zero*-trace problem into the *`u`-trace*
problem, by moving the datum's own flux `a₀∇u` into the forcing.

## The construction

For `u ∈ H¹(W)` and `g ∈ L²(W;ℝ^d)` put

```text
  correctorForce a₀ u g  :=  a₀∇u − g  ∈ L²(W;ℝ^d) ,
```

let `ρ` be the `H¹₀(W)` solution of `−∇·a₀∇ρ = ∇·(a₀∇u − g)`, and set
`v := u − ρ`.  Then `−∇·a₀∇v = ∇·g` weakly and `u − v = ρ ∈ H¹₀(W)` *on the
nose* (not merely a.e.), which is what the downstream coarse-graining datum and
the `H¹₀` test function of the negative-norm-to-`L²` step both need.

`harmonicReplacement` is the same object at `g = 0`; since `a₀ = σ Id` is
scalar, `−∇·a₀∇v = 0` is `−Δv = 0`, the printed equation.

## References

* ABK26, `l.harmonic.approximation.good.scales`.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open HCPolySupport HCPolySupport.Book

noncomputable section

variable {d : ℕ}

/-! ## 1. Domain facts for the open triadic cube -/

section Window

variable [NeZero d] (Q : TriadicCube d)

/-- The open triadic cube carries the abstract zero-trace potential closure
realization CoarseGraining's Dirichlet existence theorem asks for. -/
theorem hasPotentialZeroTraceClosureRealization_openCubeSet :
    PotentialSolenoidalL2Data.HasPotentialZeroTraceClosureRealization (openCubeSet Q) :=
  PotentialSolenoidalL2Data.hasPotentialZeroTraceClosureRealization_of_convexDomain
    (isOpenBoundedConvexDomain_openCubeSet Q)

instance instIsFiniteMeasureVolumeMeasureOnOpenCubeSet :
    MeasureTheory.IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
  (Ch02.cubeDomain Q).instIsFiniteMeasureVolumeMeasureOn

omit [NeZero d] in
/-- A constant coefficient matrix is an elliptic field on the open cube. -/
theorem isEllipticFieldOn_openCubeSet (a0 : Ch03.ConstantCoeffMatrix d) :
    IsEllipticFieldOn a0.lam a0.Lam (openCubeSet Q) (constantCoeffField a0.matrix) :=
  Ch03.constantCoeffMatrix_isEllipticFieldOn_constantCoeffField a0
    (measurableSet_openCubeSet Q)

end Window

/-! ## 2. Splitting a forcing pairing -/

section Pairing

variable {U : Set (Vec d)}

/-- The forcing pairing is additive in the force, in the form the affine shift
produces it (the combined field is given pointwise). -/
theorem integral_vecDot_add_left_split {F G H : Vec d → Vec d}
    (hF : MemVectorL2 U F) (hG : MemVectorL2 U G) (hH : ∀ x, H x = F x + G x)
    (φ : H10Function U) :
    ∫ x in U, vecDot (H x) (φ.toH1Function.grad x) ∂MeasureTheory.volume =
      (∫ x in U, vecDot (F x) (φ.toH1Function.grad x) ∂MeasureTheory.volume) +
        ∫ x in U, vecDot (G x) (φ.toH1Function.grad x) ∂MeasureTheory.volume := by
  have hFint : MeasureTheory.IntegrableOn
      (fun x => vecDot (F x) (φ.toH1Function.grad x)) U :=
    integrableOn_vecDot_of_memVectorL2 hF φ.toH1Function.grad_memVectorL2
  have hGint : MeasureTheory.IntegrableOn
      (fun x => vecDot (G x) (φ.toH1Function.grad x)) U :=
    integrableOn_vecDot_of_memVectorL2 hG φ.toH1Function.grad_memVectorL2
  have hfun : (fun x => vecDot (H x) (φ.toH1Function.grad x)) =
      fun x => vecDot (F x) (φ.toH1Function.grad x) +
        vecDot (G x) (φ.toH1Function.grad x) := by
    funext x
    rw [hH x, vecDot_add_left]
  rw [hfun, MeasureTheory.integral_add hFint hGint]

/-- The forcing pairing is subtractive in the force. -/
theorem integral_vecDot_sub_left_split {F G H : Vec d → Vec d}
    (hF : MemVectorL2 U F) (hG : MemVectorL2 U G) (hH : ∀ x, H x = F x - G x)
    (φ : H10Function U) :
    ∫ x in U, vecDot (H x) (φ.toH1Function.grad x) ∂MeasureTheory.volume =
      (∫ x in U, vecDot (F x) (φ.toH1Function.grad x) ∂MeasureTheory.volume) -
        ∫ x in U, vecDot (G x) (φ.toH1Function.grad x) ∂MeasureTheory.volume := by
  have hFint : MeasureTheory.IntegrableOn
      (fun x => vecDot (F x) (φ.toH1Function.grad x)) U :=
    integrableOn_vecDot_of_memVectorL2 hF φ.toH1Function.grad_memVectorL2
  have hGint : MeasureTheory.IntegrableOn
      (fun x => vecDot (G x) (φ.toH1Function.grad x)) U :=
    integrableOn_vecDot_of_memVectorL2 hG φ.toH1Function.grad_memVectorL2
  have hfun : (fun x => vecDot (H x) (φ.toH1Function.grad x)) =
      fun x => vecDot (F x) (φ.toH1Function.grad x) -
        vecDot (G x) (φ.toH1Function.grad x) := by
    funext x
    rw [hH x, sub_eq_add_neg, vecDot_add_left, vecDot_neg_left, ← sub_eq_add_neg]
  rw [hfun, MeasureTheory.integral_sub hFint hGint]

end Pairing

/-! ## 3. The corrector force -/

variable [NeZero d] {Q : TriadicCube d}

/-- The force of the *zero*-trace problem solved by the correction `u − v`: the
datum's own constant-coefficient flux `a₀∇u` minus the printed force `g`. -/
def correctorForce (a0 : Ch03.ConstantCoeffMatrix d)
    (u : H1Function (openCubeSet Q)) (g : Vec d → Vec d) : Vec d → Vec d :=
  fun x => matVecMul a0.matrix (u.grad x) - g x

omit [NeZero d] in
theorem correctorForce_apply (a0 : Ch03.ConstantCoeffMatrix d)
    (u : H1Function (openCubeSet Q)) (g : Vec d → Vec d) (x : Vec d) :
    correctorForce a0 u g x = matVecMul a0.matrix (u.grad x) - g x :=
  rfl

omit [NeZero d] in
/-- The constant-coefficient flux of an `H¹` function is square integrable. -/
theorem memVectorL2_constantFlux (a0 : Ch03.ConstantCoeffMatrix d)
    (u : H1Function (openCubeSet Q)) :
    MemVectorL2 (openCubeSet Q) fun x => matVecMul a0.matrix (u.grad x) :=
  memVectorL2_matVecMul_of_isEllipticFieldOn (isEllipticFieldOn_openCubeSet Q a0)
    u.grad_memVectorL2

omit [NeZero d] in
/-- The corrector force is square integrable whenever the printed force is. -/
theorem memVectorL2_correctorForce (a0 : Ch03.ConstantCoeffMatrix d)
    (u : H1Function (openCubeSet Q)) {g : Vec d → Vec d}
    (hg : MemVectorL2 (openCubeSet Q) g) :
    MemVectorL2 (openCubeSet Q) (correctorForce a0 u g) :=
  (memVectorL2_constantFlux a0 u).sub hg

/-! ## 4. The chosen `H¹₀` corrector -/

/-- **Existence of the zero-trace corrector.**  This is CoarseGraining's Dirichlet
existence theorem, specialized to the constant background on the open cube. -/
theorem exists_dirichletCorrector (a0 : Ch03.ConstantCoeffMatrix d)
    (u : H1Function (openCubeSet Q)) {g : Vec d → Vec d}
    (hg : MemVectorL2 (openCubeSet Q) g) :
    ∃ rho : H10Function (openCubeSet Q),
      IsZeroTraceDirichletRhsWeakSolution (constantCoeffField a0.matrix)
        (openCubeSet Q) rho (correctorForce a0 u g) :=
  exists_isZeroTraceDirichletRhsWeakSolution_of_potentialZeroTraceClosureRealization
    (a := constantCoeffField a0.matrix) (U := openCubeSet Q)
    (g := correctorForce a0 u g) (lam := a0.lam) (Lam := a0.Lam)
    (memVectorL2_correctorForce a0 u hg)
    (hasPotentialZeroTraceClosureRealization_openCubeSet Q)
    (Ch02.openCubeSet_nonempty Q) (isEllipticFieldOn_openCubeSet Q a0)

/-- **The chosen zero-trace corrector.**  The `H¹₀(W)` weak solution of
`−∇·a₀∇ρ = ∇·(a₀∇u − g)`. -/
def dirichletCorrector (a0 : Ch03.ConstantCoeffMatrix d)
    (u : H1Function (openCubeSet Q)) {g : Vec d → Vec d}
    (hg : MemVectorL2 (openCubeSet Q) g) : H10Function (openCubeSet Q) :=
  Classical.choose (exists_dirichletCorrector a0 u hg)

theorem dirichletCorrector_weakSolution (a0 : Ch03.ConstantCoeffMatrix d)
    (u : H1Function (openCubeSet Q)) {g : Vec d → Vec d}
    (hg : MemVectorL2 (openCubeSet Q) g) :
    IsZeroTraceDirichletRhsWeakSolution (constantCoeffField a0.matrix)
      (openCubeSet Q) (dirichletCorrector a0 u hg) (correctorForce a0 u g) :=
  Classical.choose_spec (exists_dirichletCorrector a0 u hg)

/-! ## 5. The forced replacement `v_g` and the harmonic replacement `v` -/

/-- **The auxiliary forced solution `v_g`** of tex `e.harmonic.approx.v.def.with.g`:
the element `u − ρ` of `u + H¹₀(W)` solving `−∇·a₀∇v_g = ∇·g` weakly. -/
def forcedReplacement (a0 : Ch03.ConstantCoeffMatrix d)
    (u : H1Function (openCubeSet Q)) {g : Vec d → Vec d}
    (hg : MemVectorL2 (openCubeSet Q) g) : H1Function (openCubeSet Q) :=
  u - (dirichletCorrector a0 u hg).toH1Function

theorem forcedReplacement_toFun (a0 : Ch03.ConstantCoeffMatrix d)
    (u : H1Function (openCubeSet Q)) {g : Vec d → Vec d}
    (hg : MemVectorL2 (openCubeSet Q) g) (x : Vec d) :
    (forcedReplacement a0 u hg).toFun x =
      u.toFun x - (dirichletCorrector a0 u hg).toH1Function.toFun x := by
  rw [forcedReplacement, H1Function.sub_toFun]

theorem forcedReplacement_grad (a0 : Ch03.ConstantCoeffMatrix d)
    (u : H1Function (openCubeSet Q)) {g : Vec d → Vec d}
    (hg : MemVectorL2 (openCubeSet Q) g) (x : Vec d) :
    (forcedReplacement a0 u hg).grad x =
      u.grad x - (dirichletCorrector a0 u hg).toH1Function.grad x := by
  rw [forcedReplacement, H1Function.sub_grad]

/-- **The zero-trace difference is exact.**  `u − v_g = ρ` pointwise, with `ρ`
the chosen `H¹₀` corrector; in particular `v_g ∈ u + H¹₀(W)`. -/
theorem dirichletCorrector_toFun_eq_sub (a0 : Ch03.ConstantCoeffMatrix d)
    (u : H1Function (openCubeSet Q)) {g : Vec d → Vec d}
    (hg : MemVectorL2 (openCubeSet Q) g) (x : Vec d) :
    (dirichletCorrector a0 u hg).toH1Function.toFun x =
      u.toFun x - (forcedReplacement a0 u hg).toFun x := by
  rw [forcedReplacement_toFun]
  ring

/-- The gradient of the exact zero-trace difference. -/
theorem dirichletCorrector_grad_eq_sub (a0 : Ch03.ConstantCoeffMatrix d)
    (u : H1Function (openCubeSet Q)) {g : Vec d → Vec d}
    (hg : MemVectorL2 (openCubeSet Q) g) (x : Vec d) :
    (dirichletCorrector a0 u hg).toH1Function.grad x =
      u.grad x - (forcedReplacement a0 u hg).grad x := by
  rw [forcedReplacement_grad]
  funext i
  simp

/-- **`v_g` solves the printed constant-coefficient forced problem.** -/
theorem isConstantCoeffForcedEquation_forcedReplacement
    (a0 : Ch03.ConstantCoeffMatrix d) (u : H1Function (openCubeSet Q))
    {g : Vec d → Vec d} (hg : MemVectorL2 (openCubeSet Q) g) :
    Ch03.IsConstantCoeffForcedEquation Q a0 (forcedReplacement a0 u hg) g := by
  intro φ
  simp only [Ch02.cubeDomain_coe]
  have hflux : MemVectorL2 (openCubeSet Q)
      fun x => matVecMul a0.matrix (u.grad x) := memVectorL2_constantFlux a0 u
  have hrhoflux : MemVectorL2 (openCubeSet Q)
      fun x => matVecMul a0.matrix ((dirichletCorrector a0 u hg).toH1Function.grad x) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn (isEllipticFieldOn_openCubeSet Q a0)
      (dirichletCorrector a0 u hg).toH1Function.grad_memVectorL2
  have hsplit := integral_vecDot_sub_left_split (U := openCubeSet Q) hflux hrhoflux
    (H := fun x => matVecMul a0.matrix ((forcedReplacement a0 u hg).grad x))
    (fun x => by
      show matVecMul a0.matrix ((forcedReplacement a0 u hg).grad x) = _
      rw [forcedReplacement_grad, sub_eq_add_neg, matVecMul_add, matVecMul_neg,
        ← sub_eq_add_neg]) φ
  have hcorr := dirichletCorrector_weakSolution a0 u hg φ
  have hforce := integral_vecDot_sub_left_split (U := openCubeSet Q) hflux hg
    (H := correctorForce a0 u g) (fun x => rfl) φ
  rw [hsplit, hcorr, hforce]
  ring

omit [NeZero d] in
/-- The affine shift, read backwards: if `u − w` solves the forced problem for
an `H¹₀` function `w`, then `w` solves the zero-trace problem for the corrector
force. -/
theorem isZeroTraceDirichletRhsWeakSolution_of_isConstantCoeffForcedEquation
    (a0 : Ch03.ConstantCoeffMatrix d) (u : H1Function (openCubeSet Q))
    {g : Vec d → Vec d} (hg : MemVectorL2 (openCubeSet Q) g)
    (w : H10Function (openCubeSet Q))
    (hw : Ch03.IsConstantCoeffForcedEquation Q a0 (u - w.toH1Function) g) :
    IsZeroTraceDirichletRhsWeakSolution (constantCoeffField a0.matrix)
      (openCubeSet Q) w (correctorForce a0 u g) := by
  intro φ
  have hflux : MemVectorL2 (openCubeSet Q)
      fun x => matVecMul a0.matrix (u.grad x) := memVectorL2_constantFlux a0 u
  have hwflux : MemVectorL2 (openCubeSet Q)
      fun x => matVecMul a0.matrix (w.toH1Function.grad x) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn (isEllipticFieldOn_openCubeSet Q a0)
      w.toH1Function.grad_memVectorL2
  have hsplit := integral_vecDot_sub_left_split (U := openCubeSet Q) hflux hwflux
    (H := fun x => matVecMul a0.matrix ((u - w.toH1Function).grad x))
    (fun x => by
      show matVecMul a0.matrix ((u - w.toH1Function).grad x) = _
      simp only [H1Function.sub_grad]
      rw [sub_eq_add_neg, matVecMul_add, matVecMul_neg, ← sub_eq_add_neg]) φ
  have hforce := integral_vecDot_sub_left_split (U := openCubeSet Q) hflux hg
    (H := correctorForce a0 u g) (fun x => rfl) φ
  have hbase := hw φ
  simp only [Ch02.cubeDomain_coe] at hbase
  rw [hsplit] at hbase
  rw [hforce]
  show (∫ x in openCubeSet Q, vecDot (matVecMul a0.matrix (w.toH1Function.grad x))
      (φ.toH1Function.grad x) ∂MeasureTheory.volume) = _
  linarith only [hbase]

/-- **Uniqueness of the replacement, value form.**  This is the exact sense in
which the printed "the unique solution of the Dirichlet problem" is realized. -/
theorem toScalarL2_eq_of_isConstantCoeffForcedEquation
    (a0 : Ch03.ConstantCoeffMatrix d) (u : H1Function (openCubeSet Q))
    {g : Vec d → Vec d} (hg : MemVectorL2 (openCubeSet Q) g)
    (w : H10Function (openCubeSet Q))
    (hw : Ch03.IsConstantCoeffForcedEquation Q a0 (u - w.toH1Function) g) :
    w.toH1Function.toScalarL2 =
      (dirichletCorrector a0 u hg).toH1Function.toScalarL2 :=
  IsZeroTraceDirichletRhsWeakSolution.toScalarL2_eq_of_isOpenBoundedConvexDomain
    (U := openCubeSet Q) (a := constantCoeffField a0.matrix) (u := w)
    (v := dirichletCorrector a0 u hg) (g := correctorForce a0 u g)
    (isOpenBoundedConvexDomain_openCubeSet Q) (Ch02.openCubeSet_nonempty Q)
    (isZeroTraceDirichletRhsWeakSolution_of_isConstantCoeffForcedEquation a0 u hg w hw)
    (dirichletCorrector_weakSolution a0 u hg) (isEllipticFieldOn_openCubeSet Q a0)

end

end Algsuperdiff.Section4.Provider.ExcessDecay
