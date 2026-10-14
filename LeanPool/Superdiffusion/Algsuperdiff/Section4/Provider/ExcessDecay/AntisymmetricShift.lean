/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.SkewIdentities

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Support.Dirichlet
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Foundations.EuclideanL2CZ
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.SmoothLimit

/-!
# AntisymmetricShift

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The constant antisymmetric shift: the skew-divergence primitive

```text
  since ã_{L,n+2} and a_L differ by a constant anti-symmetric matrix,
    -∇·ã_{L,n+2}∇u = -∇·a_L∇u = ∇·g   in □_m .
```

The manuscript states the underlying invariance in prose only (: "the addition
of a constant antisymmetric matrix to the coefficient field has no effect on
the generator `∇·a(x)∇`") and never writes its argument; the graph records this
as the step's whole content.  This module supplies the missing argument as a
genuine theorem.

## The mathematics

For a *constant* matrix `C` and `u ∈ H¹(U)`, `φ ∈ H¹₀(U)` put

```text
  T i j := ∫_U ∂_j u · ∂_i φ .
```

`T` is **symmetric**: with `φ` smooth and compactly supported in `U`, the
coordinate derivative `∂_i φ` is again such a test function, so the weak
derivative of `u` in the direction `j` may be tested against it, giving
`T i j = -∫_U u · ∂_j ∂_i φ`; the right-hand side is symmetric in `(i, j)`
because the second derivative of a smooth function is.  A skew `C` therefore
pairs to zero against `T`, i.e.

```text
  ∫_U (C ∇u) · ∇φ = 0 ,
```

first for smooth `φ` and then, by the `H¹₀` approximation package (the pairing
is `L²`-continuous in `∇φ` because `C ∇u ∈ L²(U)`), for every `φ ∈ H¹₀(U)`.
Subtracting `C` from a coefficient field consequently changes neither side of
the divergence-form weak equation.

This is the "skew-divergence integration by parts" primitive: CoarseGraining
has no such statement (swept: `Homogenization/Sobolev/**`,
`Homogenization/Book/**` for `skew`/`antisym` — only `skewPart` algebra and
`le_antisymm`), so it is proved here at Support grade, on an **arbitrary** set
`U` (no cube, no ellipticity, no finite measure).

## No integrability hypothesis (and why none is needed)

Splitting `∫ (a − C)∇u·∇φ` into `∫ a∇u·∇φ − ∫ C∇u·∇φ` would ordinarily need
`a∇u ∈ L¹`, which the weak-equation predicate does not supply.  It is not
needed: the subtracted integral is *zero*, and Bochner integration assigns `0`
to non-integrable functions, so the two cases (`a∇u·∇φ` integrable or not) both
close — see `integral_sub_of_integrable_of_integral_eq_zero`.  Hence every
statement here is unconditional in the coefficient field.

## Main results

* `integral_vecDot_matVecMul_skew_h10` — the primitive: `∫_U (C∇u)·∇φ = 0` for
  skew constant `C`, `u ∈ H¹(U)`, `φ ∈ H¹₀(U)`.
* `integral_vecDot_matVecMul_sub_const_eq_of_skew` — the tex display's first
  equality `-∇·(a − C)∇u = -∇·a∇u`, as an identity of weak operators.
* `isDivFormWeakSolutionOn_sub_const_of_skew` (and `_iff`,
  `_add_const_of_skew`) — the weak equation is invariant under `a ↦ a − C`.
* `isDirichletSolutionOn_sub_const_of_skew` — the same for the §4.3 Dirichlet
  carrier (the boundary clause sees only `u − h`, so it is untouched).
* `IsWeaklyHarmonicOn` is *not* touched: the harmonic comparison of the lemma
  is at the constant-coefficient Laplacian, where no shift occurs.

## References

* ABK26, `l.harmonic.approximation.good.scales`.
* ABK26, (the prose statement of the invariance), (the skew stream matrix).
* CoarseGraining, `Homogenization/Sobolev/Foundations/EuclideanL2.lean`
  (`euclideanCoordSecondDeriv_comm`),
  `Homogenization/Sobolev/WeakDerivatives.lean` (`HasWeakPartialDerivOn`),
  `Homogenization/Sobolev/Foundations/CubeNeumannW22/WeakInteriorDQ/SmoothLimit.lean`
  (`tendsto_integral_mul_of_tendsto_toScalarL2`).
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open MeasureTheory Filter
open HCPolySupport
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. Two elementary reductions -/

/-- A skew matrix pairs to zero against a symmetric array. -/
private theorem sum_sum_mul_eq_zero_of_skew_of_symm {C : Mat d}
    (hC : ∀ i j : Fin d, C j i = -C i j) {T : Fin d → Fin d → ℝ}
    (hT : ∀ i j : Fin d, T i j = T j i) :
    ∑ i : Fin d, ∑ j : Fin d, C i j * T i j = 0 := by
  exact StochasticProcess.Common.DivergenceForm.sum_sum_mul_eq_zero_of_skew_of_symm hC hT

/-- Subtracting a function of vanishing integral does not change an integral,
whether or not the minuend is integrable: if it is, this is additivity; if it is
not, then neither is the difference, and both integrals are `0`. -/
private theorem integral_sub_of_integrable_of_integral_eq_zero {alpha : Type*}
    [MeasurableSpace alpha] {mu : Measure alpha} {A B : alpha → ℝ}
    (hB : Integrable B mu) (hBzero : ∫ x, B x ∂mu = 0) :
    ∫ x, (A x - B x) ∂mu = ∫ x, A x ∂mu := by
  by_cases hA : Integrable A mu
  · rw [integral_sub hA hB, hBzero, sub_zero]
  · have hAB : ¬ Integrable (fun x => A x - B x) mu := by
      intro h
      refine hA ?_
      have hsum : Integrable (fun x => A x - B x + B x) mu := h.add hB
      simpa only [sub_add_cancel] using hsum
    rw [integral_undef hAB, integral_undef hA]

/-! ## 2. The bilinear array of an `H¹` gradient against a smooth test -/

/-- The `(i, j)` entry of the pairing array `∫_U ∂_j u · ∂_i ψ`, evaluated by
one integration by parts against the smooth test function `∂_i ψ`. -/
private theorem integral_grad_mul_coordDeriv_eq {U : Set (Vec d)} (u : H1Function U)
    {psi : Vec d → ℝ} (hpsi : ContDiff ℝ (⊤ : ℕ∞) psi)
    (hpsic : HasCompactSupport psi) (hpsiU : tsupport psi ⊆ U) (i j : Fin d) :
    ∫ x in U, u.grad x j * euclideanCoordDeriv i psi x ∂volume =
      -∫ x in U, u.toFun x * euclideanCoordSecondDeriv i j psi x ∂volume := by
  have hweak := u.hasWeakGradient j (euclideanCoordDeriv i psi)
    (contDiff_euclideanCoordDeriv hpsi i)
    (hasCompactSupport_euclideanCoordDeriv hpsic i)
    ((tsupport_euclideanCoordDeriv_subset_tsupport i psi).trans hpsiU)
  have hsecond : ∀ x : Vec d,
      u.toFun x * (fderiv ℝ (euclideanCoordDeriv i psi) x) (basisVec j) =
        u.toFun x * euclideanCoordSecondDeriv i j psi x := fun _ => rfl
  rw [show (∫ x in U, u.toFun x *
        (fderiv ℝ (euclideanCoordDeriv i psi) x) (basisVec j) ∂volume) =
      ∫ x in U, u.toFun x * euclideanCoordSecondDeriv i j psi x ∂volume from
    congrArg _ (funext hsecond)] at hweak
  rw [hweak]
  ring

/-- **The pairing array is symmetric.**  This is the whole analytic content of
the antisymmetric shift: the second derivative of a smooth test function is
symmetric, and one integration by parts moves both derivatives onto it. -/
private theorem integral_grad_mul_coordDeriv_comm {U : Set (Vec d)} (u : H1Function U)
    {psi : Vec d → ℝ} (hpsi : ContDiff ℝ (⊤ : ℕ∞) psi)
    (hpsic : HasCompactSupport psi) (hpsiU : tsupport psi ⊆ U) (i j : Fin d) :
    ∫ x in U, u.grad x j * euclideanCoordDeriv i psi x ∂volume =
      ∫ x in U, u.grad x i * euclideanCoordDeriv j psi x ∂volume := by
  rw [integral_grad_mul_coordDeriv_eq u hpsi hpsic hpsiU i j,
    integral_grad_mul_coordDeriv_eq u hpsi hpsic hpsiU j i,
    euclideanCoordSecondDeriv_comm_fun hpsi i j]

/-! ## 3. The skew pairing, first at smooth tests -/

/-- Expansion of the skew pairing into the array. -/
private theorem vecDot_matVecMul_expand (C : Mat d) (v w : Vec d) :
    vecDot (matVecMul C v) w = ∑ i : Fin d, ∑ j : Fin d, C i j * (v j * w i) := by
  simp only [vecDot, matVecMul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun j _ => by ring

/-- `L²` control of the coordinates of `C ∇u` on `U`, for a constant matrix. -/
private theorem memScalarL2_matVecMul_const {U : Set (Vec d)} (C : Mat d)
    (u : H1Function U) (i : Fin d) :
    MemScalarL2 U (fun x => matVecMul C (u.grad x) i) := by
  have hEq : (fun x : Vec d => matVecMul C (u.grad x) i) =
      fun x : Vec d => ∑ j : Fin d, C i j * u.grad x j := rfl
  rw [hEq]
  exact memLp_finsetSum Finset.univ
    fun j _ => (u.gradMemL2 j).const_mul (C i j)

/-- The skew pairing against a smooth compactly supported test vanishes. -/
private theorem integral_vecDot_matVecMul_skew_smooth {U : Set (Vec d)} {C : Mat d}
    (hC : matTranspose C = -C) (u : H1Function U) {psi : Vec d → ℝ}
    (hpsi : ContDiff ℝ (⊤ : ℕ∞) psi) (hpsic : HasCompactSupport psi)
    (hpsiU : tsupport psi ⊆ U) :
    ∫ x in U, vecDot (matVecMul C (u.grad x)) (euclideanGradient psi x) ∂volume = 0 := by
  have hCentry : ∀ i j : Fin d, C j i = -C i j := by
    intro i j
    simpa only [Matrix.transpose_apply, Matrix.neg_apply]
      using! congrFun (congrFun hC i) j
  have hpsiL2 : ∀ i : Fin d, MemScalarL2 U (euclideanCoordDeriv i psi) := by
    intro i
    have hcont : Continuous (euclideanCoordDeriv i psi) :=
      (contDiff_euclideanCoordDeriv hpsi i).continuous
    have hsupp : HasCompactSupport (euclideanCoordDeriv i psi) :=
      hasCompactSupport_euclideanCoordDeriv hpsic i
    simpa only [MemScalarL2, volumeMeasureOn] using
      (hcont.memLp_of_hasCompactSupport (p := (2 : ℝ≥0∞)) hsupp).restrict U
  have hint : ∀ i j : Fin d,
      Integrable (fun x : Vec d => C i j * (u.grad x j * euclideanCoordDeriv i psi x))
        (volume.restrict U) := by
    intro i j
    have hmul : Integrable
        (fun x : Vec d => u.grad x j * euclideanCoordDeriv i psi x)
        (volume.restrict U) := by
      simpa only [Pi.mul_apply] using! (u.gradMemL2 j).integrable_mul (hpsiL2 i)
    exact hmul.const_mul (C i j)
  have hstep : ∫ x in U, vecDot (matVecMul C (u.grad x)) (euclideanGradient psi x) ∂volume =
      ∑ i : Fin d, ∑ j : Fin d,
        C i j * ∫ x in U, u.grad x j * euclideanCoordDeriv i psi x ∂volume := by
    have hpt : ∀ x : Vec d,
        vecDot (matVecMul C (u.grad x)) (euclideanGradient psi x) =
          ∑ i : Fin d, ∑ j : Fin d,
            C i j * (u.grad x j * euclideanCoordDeriv i psi x) := by
      intro x
      simpa only [euclideanGradient] using
        vecDot_matVecMul_expand C (u.grad x) (euclideanGradient psi x)
    rw [show (fun x : Vec d =>
          vecDot (matVecMul C (u.grad x)) (euclideanGradient psi x)) =
        fun x : Vec d => ∑ i : Fin d, ∑ j : Fin d,
          C i j * (u.grad x j * euclideanCoordDeriv i psi x) from funext hpt]
    rw [integral_finsetSum Finset.univ
      fun i _ => integrable_finsetSum Finset.univ fun j _ => hint i j]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum Finset.univ fun j _ => hint i j]
    exact Finset.sum_congr rfl fun j _ => integral_const_mul (C i j) _
  rw [hstep]
  exact sum_sum_mul_eq_zero_of_skew_of_symm hCentry
    fun i j => integral_grad_mul_coordDeriv_comm u hpsi hpsic hpsiU i j

/-! ## 4. The primitive: the skew pairing against every `H¹₀` test -/

/-- The set integral of a dot product of two `L²` vector fields splits into
coordinates. -/
private theorem integral_vecDot_eq_sum_coord {U : Set (Vec d)} {F G : Vec d → Vec d}
    (hF : ∀ i : Fin d, MemScalarL2 U (fun x => F x i))
    (hG : ∀ i : Fin d, MemScalarL2 U (fun x => G x i)) :
    ∫ x in U, vecDot (F x) (G x) ∂volume =
      ∑ i : Fin d, ∫ x in U, F x i * G x i ∂volume := by
  rw [show (fun x : Vec d => vecDot (F x) (G x)) =
      fun x : Vec d => ∑ i : Fin d, F x i * G x i from funext fun _ => rfl]
  refine integral_finsetSum Finset.univ fun i _ => ?_
  simpa only [Pi.mul_apply] using! (hF i).integrable_mul (hG i)

/-- **The skew-divergence integration by parts on an arbitrary set.**

For a constant *skew* matrix `C`, every `u ∈ H¹(U)` and every `φ ∈ H¹₀(U)`,

```text
  ∫_U (C ∇u) · ∇φ = 0 .
```

This is the Support-grade primitive behind and behind the prose invariance;
CoarseGraining contains no such statement. -/
theorem integral_vecDot_matVecMul_skew_h10 {U : Set (Vec d)} {C : Mat d}
    (hC : matTranspose C = -C) (u : H1Function U) (phi : H10Function U) :
    ∫ x in U, vecDot (matVecMul C (u.grad x)) (phi.toH1Function.grad x) ∂volume = 0 := by
  set F : Vec d → Vec d := fun x => matVecMul C (u.grad x) with hFdef
  have hF : ∀ i : Fin d, MemScalarL2 U (fun x => F x i) := fun i =>
    memScalarL2_matVecMul_const C u i
  set Dn : ℕ → Vec d → Vec d := fun n => euclideanGradient (phi.approx n) with hDndef
  have hDn : ∀ (n : ℕ) (i : Fin d), MemScalarL2 U (fun x => Dn n x i) := by
    intro n i
    exact memScalarL2_coord_of_memVectorL2
      (memVectorL2_euclideanGradient_of_contDiff_hasCompactSupport
        (phi.approx_smooth n) (phi.approx_hasCompactSupport n)) i
  have hDlim : ∀ i : Fin d, MemScalarL2 U (fun x => phi.toH1Function.grad x i) :=
    fun i => phi.toH1Function.gradMemL2 i
  have hconv : ∀ i : Fin d, Tendsto
      (fun n => toScalarL2 (hDn n i)) atTop (nhds (toScalarL2 (hDlim i))) := by
    intro i
    refine tendsto_toScalarL2_of_tendsto_eLpNorm (fun n => hDn n i) (hDlim i) ?_
    simpa only [hDndef, euclideanGradient, euclideanCoordDeriv, volumeMeasureOn]
      using phi.tendsto_approx_grad i
  have hpair : ∀ i : Fin d, Tendsto
      (fun n => ∫ x in U, F x i * Dn n x i ∂volume) atTop
      (nhds (∫ x in U, F x i * phi.toH1Function.grad x i ∂volume)) := fun i =>
    tendsto_integral_mul_of_tendsto_toScalarL2 (hF i) (fun n => hDn n i) (hDlim i)
      (hconv i)
  have hsum : Tendsto
      (fun n => ∑ i : Fin d, ∫ x in U, F x i * Dn n x i ∂volume) atTop
      (nhds (∑ i : Fin d, ∫ x in U, F x i * phi.toH1Function.grad x i ∂volume)) :=
    tendsto_finsetSum Finset.univ fun i _ => hpair i
  have hzero : ∀ n : ℕ, (∑ i : Fin d, ∫ x in U, F x i * Dn n x i ∂volume) = 0 := by
    intro n
    rw [← integral_vecDot_eq_sum_coord hF (fun i => hDn n i)]
    exact integral_vecDot_matVecMul_skew_smooth hC u (phi.approx_smooth n)
      (phi.approx_hasCompactSupport n) (phi.approx_support_subset n)
  have hlimzero : (∑ i : Fin d,
      ∫ x in U, F x i * phi.toH1Function.grad x i ∂volume) = 0 :=
    tendsto_nhds_unique (hsum.congr' (EventuallyEq.of_eq (funext hzero)))
      tendsto_const_nhds
  rw [integral_vecDot_eq_sum_coord hF hDlim]
  exact hlimzero

/-- The skew pairing is integrable: both factors are `L²`. -/
private theorem integrable_vecDot_matVecMul_const {U : Set (Vec d)} (C : Mat d)
    (u : H1Function U) (phi : H10Function U) :
    Integrable
      (fun x => vecDot (matVecMul C (u.grad x)) (phi.toH1Function.grad x))
      (volume.restrict U) := by
  have hEq : (fun x : Vec d =>
      vecDot (matVecMul C (u.grad x)) (phi.toH1Function.grad x)) =
      fun x : Vec d => ∑ i : Fin d,
        matVecMul C (u.grad x) i * phi.toH1Function.grad x i := funext fun _ => rfl
  rw [hEq]
  refine integrable_finsetSum Finset.univ fun i _ => ?_
  simpa only [Pi.mul_apply] using!
    (memScalarL2_matVecMul_const C u i).integrable_mul
      (phi.toH1Function.gradMemL2 i)

/-! ## 5. Invariance of the weak equation -/

/-- **`-∇·(a − C)∇u = -∇·a∇u` for constant skew `C`** — the literal first
equality of the printed display, as an identity of the two weak operators tested
against `H¹₀(U)`.  Nothing is assumed of `a`: if the unshifted pairing fails to
be integrable then so does the shifted one, and both Bochner integrals are `0`.
-/
theorem integral_vecDot_matVecMul_sub_const_eq_of_skew {U : Set (Vec d)}
    (a : CoeffField d) {C : Mat d} (hC : matTranspose C = -C)
    (u : H1Function U) (phi : H10Function U) :
    ∫ x in U, vecDot (matVecMul (a x - C) (u.grad x))
        (phi.toH1Function.grad x) ∂volume =
      ∫ x in U, vecDot (matVecMul (a x) (u.grad x))
        (phi.toH1Function.grad x) ∂volume := by
  have hpt : ∀ x : Vec d,
      vecDot (matVecMul (a x - C) (u.grad x)) (phi.toH1Function.grad x) =
        vecDot (matVecMul (a x) (u.grad x)) (phi.toH1Function.grad x) -
          vecDot (matVecMul C (u.grad x)) (phi.toH1Function.grad x) := by
    intro x
    rw [sub_matVecMul]
    simp only [vecDot, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
  rw [show (fun x : Vec d =>
        vecDot (matVecMul (a x - C) (u.grad x)) (phi.toH1Function.grad x)) =
      fun x : Vec d =>
        vecDot (matVecMul (a x) (u.grad x)) (phi.toH1Function.grad x) -
          vecDot (matVecMul C (u.grad x)) (phi.toH1Function.grad x) from funext hpt]
  exact integral_sub_of_integrable_of_integral_eq_zero
    (integrable_vecDot_matVecMul_const C u phi)
    (integral_vecDot_matVecMul_skew_h10 hC u phi)

/-- **The antisymmetric shift leaves the divergence-form weak equation invariant.**

If `-∇·a∇u = ∇·g` weakly on `U` and `C` is a constant skew matrix, then
`-∇·(a − C)∇u = ∇·g` weakly on `U`.  Nothing is assumed of `a`. -/
theorem isDivFormWeakSolutionOn_sub_const_of_skew {U : Set (Vec d)}
    {a : CoeffField d} {C : Mat d} (hC : matTranspose C = -C)
    {u : H1Function U} {g : Vec d → Vec d}
    (h : Support.IsDivFormWeakSolutionOn a U u g) :
    Support.IsDivFormWeakSolutionOn (fun x => a x - C) U u g := by
  intro phi
  rw [show (∫ x in U, vecDot (matVecMul ((fun y : Vec d => a y - C) x) (u.grad x))
        (phi.toH1Function.grad x) ∂volume) =
      ∫ x in U, vecDot (matVecMul (a x) (u.grad x))
        (phi.toH1Function.grad x) ∂volume from
    integral_vecDot_matVecMul_sub_const_eq_of_skew a hC u phi]
  exact h phi

/-- The shift by `+C` (`C` skew) is likewise invisible. -/
theorem isDivFormWeakSolutionOn_add_const_of_skew {U : Set (Vec d)}
    {a : CoeffField d} {C : Mat d} (hC : matTranspose C = -C)
    {u : H1Function U} {g : Vec d → Vec d}
    (h : Support.IsDivFormWeakSolutionOn a U u g) :
    Support.IsDivFormWeakSolutionOn (fun x => a x + C) U u g := by
  have hCneg : matTranspose (-C) = -(-C) := by
    rw [show matTranspose (-C) = -matTranspose C from Matrix.transpose_neg C, hC]
  have h' := isDivFormWeakSolutionOn_sub_const_of_skew (a := a) hCneg h
  simpa only [sub_neg_eq_add] using h'

/-- The invariance as an equivalence: the shifted and unshifted equations have
exactly the same solutions. -/
theorem isDivFormWeakSolutionOn_sub_const_of_skew_iff {U : Set (Vec d)}
    {a : CoeffField d} {C : Mat d} (hC : matTranspose C = -C)
    {u : H1Function U} {g : Vec d → Vec d} :
    Support.IsDivFormWeakSolutionOn (fun x => a x - C) U u g ↔
      Support.IsDivFormWeakSolutionOn a U u g := by
  refine ⟨fun h => ?_, fun h => isDivFormWeakSolutionOn_sub_const_of_skew hC h⟩
  have h' := isDivFormWeakSolutionOn_add_const_of_skew
    (a := fun x : Vec d => a x - C) hC h
  simpa only [sub_add_cancel] using h'

/-- **The antisymmetric shift on the §4.3 Dirichlet carrier.**  The boundary clause
of `IsDirichletSolutionOn` constrains only `u - h`, so it is untouched by a
change of coefficient field; only the equation moves, by the theorem above.
This is exactly the display. -/
theorem isDirichletSolutionOn_sub_const_of_skew {Q : TriadicCube d}
    {a : CoeffField d} {C : Mat d} (hC : matTranspose C = -C)
    {u h : H1Function (openCubeSet Q)} {g : Vec d → Vec d}
    (hsol : Support.IsDirichletSolutionOn a Q u h g) :
    Support.IsDirichletSolutionOn (fun x => a x - C) Q u h g :=
  ⟨hsol.1, isDivFormWeakSolutionOn_sub_const_of_skew hC hsol.2⟩

/-! ## 6. The energy identity of the shifted field -/

/-- A skew matrix contributes nothing to the quadratic form. -/
theorem vecDot_matVecMul_self_eq_zero_of_skew {C : Mat d}
    (hC : matTranspose C = -C) (v : Vec d) :
    vecDot (matVecMul C v) v = 0 := by
  have hCentry : ∀ i j : Fin d, C j i = -C i j := by
    intro i j
    simpa only [Matrix.transpose_apply, Matrix.neg_apply]
      using! congrFun (congrFun hC i) j
  rw [vecDot_matVecMul_expand C v v]
  exact sum_sum_mul_eq_zero_of_skew_of_symm hCentry fun i j => by ring

/-- The symmetric part is untouched by a skew shift. -/
theorem symmPart_sub_const_of_skew {C : Mat d} (hC : matTranspose C = -C)
    (A : Mat d) : symmPart (A - C) = symmPart A := by
  have hCentry : ∀ i j : Fin d, C j i = -C i j := by
    intro i j
    simpa only [Matrix.transpose_apply, Matrix.neg_apply]
      using! congrFun (congrFun hC i) j
  ext i j
  have hC' := hCentry i j
  simp only [symmPart, Matrix.sub_apply]
  linarith only [hC']

end

end Algsuperdiff.Section4.Provider.ExcessDecay
