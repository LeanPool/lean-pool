/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.InteriorGlue
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.TranslationTransportAssembly

/-!
# InteriorAssemblyLhs

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The interior clause's left-hand side, identified with the constructed
# harmonic replacement

Steps `(v)` and `(vi)` of the interior-clause assembly: the frozen theorem
**quantifies** over the harmonic function `v` and the `H¹₀` witness `w` with `v
= u − w`; every proved estimate is proved for the *constructed* replacement.
This module closes the gap, in the anchor's own carriers:

```text
  ‖u − v‖_{L²(x+□_n)}  =  ‖u − v⋆‖_{L²(□_n)}   at   v⋆ = harmonicReplacement σ u_tilde,
```

`u_tilde = u(· + x)` being the solution read in the child's own frame.

## The three transported facts

* `isWeaklyHarmonicOn_untranslate` — weak harmonicity is translation covariant
  (the `H¹₀` test functions correspond bijectively; the change of variables is
  measure preserving).
* `isConstantCoeffForcedEquation_zero_of_isWeaklyHarmonicOn` — `−Δv = 0` and
  `−∇·(σ Id)∇v = 0` are the same condition: the comparator is a positive
  scalar, and it factors out of the weak identity.  This is where the frozen
  statement's *Laplacian* harmonicity (`Support.IsWeaklyHarmonicOn`) meets the
  development's *comparator* harmonicity
  (`Ch03.IsConstantCoeffForcedEquation`).
* `H10Function.untranslate` / `H1Function.untranslate` (CoarseGraining) — the
  carriers.

## References

* ABK26, `l.harmonic.approximation.good.scales`; `e.harmonic.approx.v.def`.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open HCPolySupport HCPolySupport.Book MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## 1. Weak harmonicity untranslates -/

/-- **Weak harmonicity in the back-translated frame.**

If `∫_{U+z} ∇v · ∇φ = 0` for every `φ ∈ H¹₀(U+z)`, then the same holds on `U`
for `v(· + z)`.  Exact: no constant, no hypothesis beyond the statement. -/
theorem isWeaklyHarmonicOn_untranslate {U : Set (Vec d)} (z : Vec d)
    {v : H1Function (translateSet z U)}
    (h : Support.IsWeaklyHarmonicOn (translateSet z U) v) :
    Support.IsWeaklyHarmonicOn U (H1Function.untranslate z v) := by
  intro phi
  have hkey := h (H10Function.translate phi z)
  have hL := setIntegral_comp_addRight_translateSet z U
    (fun y => vecDot (v.grad y) (phi.toH1Function.grad (y - z)))
  have hLform : (fun y : Vec d =>
        vecDot (v.grad (y + z)) (phi.toH1Function.grad (y + z - z))) =
      fun y : Vec d =>
        vecDot ((H1Function.untranslate z v).grad y) (phi.toH1Function.grad y) := by
    funext y
    rw [add_sub_cancel_right]
    rfl
  rw [hLform] at hL
  rw [hL]
  exact hkey

/-! ## 2. Laplace harmonicity is comparator harmonicity -/

/-- **The frozen statement's harmonicity is the development's.**

`Support.IsWeaklyHarmonicOn` is `−Δv = 0` weakly; the coarse-graining chain uses
`Ch03.IsConstantCoeffForcedEquation` at the scalar comparator `σ Id` with zero
force.  For a *positive scalar* comparator the two are the same condition: the
scalar factors out of the weak identity. -/
theorem isConstantCoeffForcedEquation_zero_of_isWeaklyHarmonicOn {Q : TriadicCube d}
    {sigma0 : ℝ} (hsigma0 : 0 < sigma0) (f : H1Function (openCubeSet Q))
    (h : Support.IsWeaklyHarmonicOn (openCubeSet Q) f) :
    Ch03.IsConstantCoeffForcedEquation Q (scalarComparator hsigma0) f
      (fun _ => (0 : Vec d)) := by
  intro phi
  simp only [Ch02.cubeDomain_coe]
  have hL : (fun y => vecDot (matVecMul (scalarComparator (d := d) hsigma0).matrix
        (f.grad y)) (phi.toH1Function.grad y)) =
      fun y => sigma0 * vecDot (f.grad y) (phi.toH1Function.grad y) := by
    funext y
    rw [scalarComparator_matrix, matVecMul_scalarMatrix, vecDot_smul_left]
  have hR : (fun y : Vec d =>
        vecDot ((fun _ : Vec d => (0 : Vec d)) y) (phi.toH1Function.grad y)) =
      fun _ : Vec d => (0 : ℝ) := by
    funext y
    simp [vecDot]
  rw [hL, hR, MeasureTheory.integral_const_mul, h phi, mul_zero,
    MeasureTheory.integral_zero]

/-! ## 3. The identification -/

variable [NeZero d]

/-- **The interior clause's left-hand side, in the child's own frame.**

For every pair `(v, w)` the frozen theorem quantifies over — `v` weakly
harmonic on the child window `W = x + □_n`, `v = u − w` with `w ∈ H¹₀(W)` — the
anchor's own left-hand norm equals the normalized `L²` norm of the
**constructed** harmonic corrector of the transported solution `u_tilde = u(· + x)`:

```text
  ‖u − v‖_{L²(W)}  =  ‖u(·+x) − v⋆‖_{L²(□_n)} ,
      v⋆ = harmonicReplacement (σ Id) u_tilde .
```

This is an exact identity.  The comparator scale `σ > 0` is free: harmonicity
does not see it (§2), so the same `v⋆` serves every positive scalar
background. -/
theorem eLpNorm_sub_weaklyHarmonic_eq_harmonicCorrector {sigma0 : ℝ}
    (hsigma0 : 0 < sigma0) {n m : ℤ} {x : Vec d} {W : Set (Vec d)}
    (hW : W = translateSet x (openCubeSet (originCube d n)))
    (hsub : translateSet x (openCubeSet (originCube d n)) ⊆
      openCubeSet (originCube d m))
    (u : H1Function (openCubeSet (originCube d m)))
    (v : H1Function W) (w : H10Function W)
    (hharm : Support.IsWeaklyHarmonicOn W v)
    (hval : ∀ y, v.toFun y = u.toFun y - w.toH1Function.toFun y)
    (hgrad : ∀ y, v.grad y = u.grad y - w.toH1Function.grad y) :
    eLpNorm (fun y => u.toFun y - v.toFun y) 2
        (Support.normalizedVolumeMeasureOn W) =
      eLpNorm (fun y =>
          (harmonicCorrector (scalarComparator hsigma0)
              (H1Function.untranslate x
                (u.restrict (isOpen_translateSet_openCubeSet x n) hsub))).toH1Function.toFun
            y)
        2 (normalizedCubeMeasure (originCube d n)) := by
  subst hW
  set ut : H1Function (openCubeSet (originCube d n)) :=
    H1Function.untranslate x (u.restrict (isOpen_translateSet_openCubeSet x n) hsub)
    with hut
  set wt : H10Function (openCubeSet (originCube d n)) :=
    H10Function.untranslate x w with hwt
  set a0 : Ch03.ConstantCoeffMatrix d := scalarComparator hsigma0 with ha0
  -- the left-hand integrand is the anchor's own `H¹₀` witness
  have hsub' : (fun y => u.toFun y - v.toFun y) =
      fun y => w.toH1Function.toFun y := by
    funext y
    rw [hval y]
    ring
  rw [hsub', eLpNorm_normalizedVolumeMeasureOn_translateSet x
    (openCubeSet (originCube d n)) (by norm_num) (by norm_num),
    normalizedVolumeMeasureOn_openCubeSet (originCube d n)]
  -- the transported witness
  have hwtFun : (fun y => w.toH1Function.toFun (y + x)) =
      fun y => wt.toH1Function.toFun y := by
    funext y
    rfl
  rw [hwtFun]
  -- the transported harmonic function solves the comparator problem
  have hharmt : Support.IsWeaklyHarmonicOn (openCubeSet (originCube d n))
      (H1Function.untranslate x v) :=
    isWeaklyHarmonicOn_untranslate x hharm
  have hcomp : Ch03.IsConstantCoeffForcedEquation (originCube d n) a0
      (H1Function.untranslate x v) (fun _ => (0 : Vec d)) :=
    isConstantCoeffForcedEquation_zero_of_isWeaklyHarmonicOn hsigma0 _ hharmt
  have hgradeq : ∀ y, (ut - wt.toH1Function).grad y =
      (H1Function.untranslate x v).grad y := by
    intro y
    have hy : (H1Function.untranslate x v).grad y = v.grad (y + x) := rfl
    have hu : ut.grad y = u.grad (y + x) := rfl
    have hw : wt.toH1Function.grad y = w.toH1Function.grad (y + x) := rfl
    have hsubg : (ut - wt.toH1Function).grad y =
        ut.grad y - wt.toH1Function.grad y :=
      congrArg (fun f => f y) (H1Function.sub_grad ut wt.toH1Function)
    rw [hsubg, hu, hw, hy, hgrad (y + x)]
  have hcomp' : Ch03.IsConstantCoeffForcedEquation (originCube d n) a0
      (ut - wt.toH1Function) (fun _ => (0 : Vec d)) := by
    intro phi
    have hfun : (fun y => vecDot (matVecMul a0.matrix ((ut - wt.toH1Function).grad y))
          (phi.toH1Function.grad y)) =
        fun y => vecDot (matVecMul a0.matrix ((H1Function.untranslate x v).grad y))
          (phi.toH1Function.grad y) := by
      funext y
      rw [hgradeq y]
    rw [hfun]
    exact hcomp phi
  -- the uniqueness of the zero-trace corrector
  have hg0 : MemVectorL2 (openCubeSet (originCube d n)) (fun _ => (0 : Vec d)) :=
    MeasureTheory.memLp_const (μ := volumeMeasureOn (openCubeSet (originCube d n)))
      (p := (2 : ENNReal)) (0 : Vec d)
  have huniq := toScalarL2_eq_of_isConstantCoeffForcedEquation a0 ut hg0 wt hcomp'
  have hiff : HCPolySupport.toScalarL2 wt.toH1Function.memL2 =
      HCPolySupport.toScalarL2 (harmonicCorrector a0 ut).toH1Function.memL2 := huniq
  have hae : wt.toH1Function.toFun =ᵐ[volumeMeasureOn (openCubeSet (originCube d n))]
      (harmonicCorrector a0 ut).toH1Function.toFun :=
    (HCPolySupport.toScalarL2_eq_toScalarL2_iff _ _).mp hiff
  have hae2 : (fun y => wt.toH1Function.toFun y) =ᵐ[normalizedCubeMeasure (originCube d n)]
      fun y => (harmonicCorrector a0 ut).toH1Function.toFun y := by
    rw [normalizedCubeMeasure_eq_smul_restrict_openCubeSet (originCube d n)]
    exact Measure.ae_smul_measure hae _
  exact eLpNorm_congr_ae hae2

end

end Algsuperdiff.Section4.Provider.ExcessDecay
