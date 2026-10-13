/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomCGDischargeBridge

/-!
# HomCGDischargeAssembly

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# the general coarse-graining proposition at finite `p`: PROVED, at the smooth-dual reading

## What is proved here

The printed finite-`p` coarse-graining proposition,

```text
  3^{-ms} σ₀ ‖∇u - ∇v‖_{W_hat^{-s,p}(□_m)} + 3^{-ms} ‖𝐚∇u - σ₀∇v‖_{W_hat^{-s,p}(□_m)}
    ≤ C s^{-1} σ₀^{1/2} 𝓔_{s₁,∞,1}(□_m,n;𝐚,σ₀)
        ( Σ_{k ≤ n} 3^{-(s-s₁)p(n-k)} avsum_z ‖σ^{1/2}∇u‖_{L²(z+□_k)}^p )^{1/p}
      + C s^{-9/2} (s₂-s)^{-1} (1 + 𝓔²_{s₁/2,∞,2}(□_m,n;𝐚,σ₀))
          3^{s₂ n} [𝐠]_{W^{s₂,p}(□_m)}
```

is a **theorem** (`exists_printedCoarseGrainingFiniteP_smoothDual`) when the
undefined left-hand symbol `‖·‖_{W_hat^{-s,p}(□_m)}` is read as `CoarseGraining`'s
smooth fractional dual `cubeEuclideanNegativeWspSmoothDualENorm`, under exactly
the printed hypotheses:

* `𝐚` uniformly elliptic on `□_m` (`CoarseGraining`'s `Book.Ch02.CoeffOn`), `σ₀ > 0`;
* `p ∈ [2,∞)`, `s₁ < s < s₂` fractional orders, `n < m`;
* `𝐠 ∈ W^{s₂,p}(□_m)` (`MemCubeEuclideanFullWsp`);
* `-∇·𝐚∇u = ∇·𝐠` and `-∇·σ₀∇v = ∇·𝐠` in `□_m` (`IsForcedEquation`,
  `IsScalarForcedEquation`) and `u - v ∈ H¹₀(□_m)` (`HasH10Difference`).

The right-hand side is `CoarseGraining`'s `localCoarseGrainingLpRHS`, which is
the printed right-hand side symbol for symbol.  The constant is `C(p,d) < ∞`,
fixed before the cube, the orders, the coefficient field, the forcing and the
solutions.

## The three links, and where each comes from

```text
  LHS  ≤  C_cz · 3^{s(m-n)} · (smooth-dual descendant average)   -- link 1
       ≤  C_cz · C_d · 3^{s(m-n)} · 3^{sn} · (neg-Besov average) -- link 2
       ≤  C_cz · C_d · C_lcg-RHS at 3^{sm}                       -- link 3
```

* link 1 is `CoarseGraining`'s `exists_centeredCubeFluxComparison_cz` (the fractional
  Calderón--Zygmund duality argument), used as a black box;
* link 2 is `localFluxDefect_smoothDualAverage_le` of `HomCGDischargeBridge`,
  i.e. the smooth-dual/negative-Besov comparison aggregated over the
  descendant grid;
* link 3 is `CoarseGraining`'s `exists_localCoarseGrainingLp`, used as a black box.

Nothing else enters.  The three `3`-powers multiply to `1`
(`ofReal_three_rpow_scale_triple`), which is the exact statement that the
printed `3^{-ms}` prefactor is the correct normalization of this composition.

## The hypothesis bridge (`§1`)

`CoarseGraining`'s flux-comparison statement takes the *consequence* of the
printed pair — the flux difference is weakly solenoidal against `H¹₀` tests, in
the normalized cube measure — rather than the pair itself.
`isCenteredCubeFluxBalanced_of_forced` derives it from the printed pair, so no
hypothesis is smuggled: the two forced equations are subtracted, the common
forcing cancels, and the volume normalization is a nonzero scalar.  Similarly
`HasCenteredCubeH10Difference` is `HasH10Difference` on the origin cube,
definitionally.

## What this does NOT give (the honest scope)

The transcribed finite-`p` coarse-graining hypothesis of `HomFinitePSource`
carries **three** clauses.  This file's display is the *duality* content;
converting it to this repository's `WeakNegDualBoundOn` (clauses 2 and 3) needs a
test-class change, and the *multiscale* clause 1 is a different object
altogether.  See `HomCGDischargeTestClass` for both measurements.
-/

open HCPolySupport HCPolySupport.Book.Ch03 HCPolySupport.Book.Ch03.ABK26
open MeasureTheory
open scoped BigOperators ENNReal

namespace Algsuperdiff.Section4.Provider.Homogenization

noncomputable section

variable {d : ℕ}

/-! ## 1. The printed hypothesis pair produces `CoarseGraining`'s flux balance -/

/-- The `L²` membership of `𝐚∇u` on a cube, for a bundled elliptic coefficient.

Adapted from the `private` `memVectorL2_matVecMul_pointwiseCoeffOn` of
`Homogenization/Book/Ch03/ABK26/LocalCoarseGrainingDefinitions.lean`, which is
not exported. -/
theorem memVectorL2_matVecMul_coeffOn {Q : TriadicCube d}
    (a : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain Q))
    (u : H1Function (openCubeSet Q)) :
    MemVectorL2 (openCubeSet Q)
      (fun x => matVecMul (a.toCoeffField x) (u.grad x)) := by
  let b : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain Q) :=
    Internal.Ch02.BookCh02.pointwiseCoeffOn (Book.Ch02.cubeDomain Q) a
  have hEll : IsEllipticFieldOn b.lam b.Lam (openCubeSet Q) b.toCoeffField := by
    simpa only [b, Book.Ch02.cubeDomain_coe] using
      Internal.Ch02.BookCh02.pointwiseCoeffOn_isEllipticFieldOn
        (Book.Ch02.cubeDomain Q) a
  have hB : MemVectorL2 (openCubeSet Q)
      (fun x => matVecMul (b.toCoeffField x) (u.grad x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll u.grad_memVectorL2
  have hba : b.toCoeffField =ᵐ[volumeMeasureOn (openCubeSet Q)] a.toCoeffField := by
    simpa only [b, Book.Ch02.cubeDomain_coe] using!
      Internal.Ch02.BookCh02.pointwiseCoeffOn_ae_eq (Book.Ch02.cubeDomain Q) a
  apply (memLp_congr_ae ?_).mp hB
  filter_upwards [hba] with x hx
  simp only [hx]

/-- Left additivity of the Euclidean dot product under subtraction. -/
theorem vecDot_sub_left (x y z : Vec d) :
    vecDot (x - y) z = vecDot x z - vecDot y z := by
  simp only [vecDot, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

/-- The centered-cube normalized volume is a positive multiple of the raw
volume restricted to the open cube.

Adapted from the `private`
`centeredCube_normalizedVolume_eq_smul_openCubeVolume` of
`Homogenization/Book/Ch03/ABK26/FluxComparisonBridges.lean`. -/
theorem centeredCube_normalizedVolume_eq {m : ℤ} :
    (centeredCubeDomain d m).normalizedVolume =
      ENNReal.ofReal ((cubeVolume (originCube d m))⁻¹) •
        volume.restrict (openCubeSet (originCube d m)) := by
  change (cubeBoundedMeasurableDomain (originCube d m)).normalizedVolume = _
  rw [cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure,
    normalizedCubeMeasure, cubeMeasure,
    volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]

/-- **The printed hypothesis pair gives `CoarseGraining`'s flux balance.**

`-∇·𝐚∇u = ∇·𝐠` and `-∇·σ₀∇v = ∇·𝐠` in `□_m` imply that `𝐚∇u - σ₀∇v` is weakly
divergence free against `H¹₀(□_m)`, which is the hypothesis `CoarseGraining`'s
flux-comparison theorem actually consumes.  No hypothesis is smuggled: the
common forcing cancels and the volume normalization is a nonzero scalar. -/
theorem isCenteredCubeFluxBalanced_of_forced {m : ℤ}
    (a : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain (originCube d m)))
    {sigma0 : ℝ} {u v : H1Function (openCubeSet (originCube d m))}
    {g : Vec d → Vec d}
    (hu : IsForcedEquation (originCube d m) a u g)
    (hv : IsScalarForcedEquation (originCube d m) sigma0 v g) :
    IsCenteredCubeFluxBalanced m a sigma0 u v := by
  intro phi
  have hI1 : IntegrableOn (fun x =>
      vecDot (matVecMul (a.toCoeffField x) (u.grad x))
        (phi.toH1Function.grad x)) (openCubeSet (originCube d m)) :=
    integrableOn_vecDot_of_memVectorL2 (memVectorL2_matVecMul_coeffOn a u)
      phi.toH1Function.grad_memVectorL2
  have hI2 : IntegrableOn (fun x =>
      vecDot (sigma0 • v.grad x) (phi.toH1Function.grad x))
      (openCubeSet (originCube d m)) :=
    integrableOn_vecDot_of_memVectorL2 (v.grad_memVectorL2.const_smul sigma0)
      phi.toH1Function.grad_memVectorL2
  have hzero : ∫ x in openCubeSet (originCube d m),
      vecDot (matVecMul (a.toCoeffField x) (u.grad x) - sigma0 • v.grad x)
        (phi.toH1Function.grad x) ∂volume = 0 := by
    have hpt : (fun x => vecDot
        (matVecMul (a.toCoeffField x) (u.grad x) - sigma0 • v.grad x)
        (phi.toH1Function.grad x)) =
        fun x => vecDot (matVecMul (a.toCoeffField x) (u.grad x))
            (phi.toH1Function.grad x) -
          vecDot (sigma0 • v.grad x) (phi.toH1Function.grad x) := by
      funext x
      exact vecDot_sub_left _ _ _
    have hv' := hv phi
    simp only [matVecMul_scalarMatrix] at hv'
    rw [hpt, MeasureTheory.integral_sub hI1 hI2, hu phi, hv']
    ring
  rw [centeredCube_normalizedVolume_eq, MeasureTheory.integral_smul_measure,
    smul_eq_mul, hzero, mul_zero]

/-- The printed zero-trace hypothesis on the origin cube IS `CoarseGraining`'s
`HasCenteredCubeH10Difference`. -/
theorem hasCenteredCubeH10Difference_iff {m : ℤ}
    {u v : H1Function (openCubeSet (originCube d m))} :
    HasCenteredCubeH10Difference m u v ↔ HasH10Difference (originCube d m) u v :=
  Iff.rfl

/-! ## 2. Scaling bookkeeping -/

/-- The printed right-hand side is homogeneous of degree one in its constant. -/
theorem localCoarseGrainingLpRHS_const_mul [NeZero d] (K C : ℝ≥0∞)
    (Q : TriadicCube d) (n : ℤ) (hn : n ≤ Q.scale)
    (a : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain Q)) (sigma0 : ℝ)
    (hsigma0 : 0 < sigma0) (g : Vec d → Vec d)
    (u : H1Function (openCubeSet Q)) (s1 s s2 : FractionalOrder)
    (p : FiniteLpExponent) :
    K * localCoarseGrainingLpRHS C Q n hn a sigma0 hsigma0 g u s1 s s2 p =
      localCoarseGrainingLpRHS (K * C) Q n hn a sigma0 hsigma0 g u s1 s s2 p := by
  unfold localCoarseGrainingLpRHS
  ring

/-- **The three scale powers of the composition multiply to one.**

`3^{-sm} · 3^{s(m-n)} · 3^{sn} = 1`: the printed `3^{-ms}` prefactor is exactly
the normalization that the flux-comparison factor and the negative-Besov
normalization leave over. -/
theorem ofReal_three_rpow_scale_triple (s : ℝ) (m n : ℤ) :
    ENNReal.ofReal (Real.rpow 3 (-s * (m : ℝ))) *
        ENNReal.ofReal (Real.rpow 3 (s * (((m - n : ℤ) : ℝ)))) *
      ENNReal.ofReal (Real.rpow 3 (s * (n : ℝ))) = 1 := by
  have h3 : (0 : ℝ) < 3 := by norm_num
  have hnn : ∀ x : ℝ, (0 : ℝ) ≤ Real.rpow 3 x := fun x =>
    Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) x
  have hreal : Real.rpow 3 (-s * (m : ℝ)) * Real.rpow 3 (s * (((m - n : ℤ) : ℝ))) *
      Real.rpow 3 (s * (n : ℝ)) = 1 := by
    change (3 : ℝ) ^ (-s * (m : ℝ)) * (3 : ℝ) ^ (s * (((m - n : ℤ) : ℝ))) *
      (3 : ℝ) ^ (s * (n : ℝ)) = 1
    rw [← Real.rpow_add h3, ← Real.rpow_add h3]
    have hexp : -s * (m : ℝ) + s * (((m - n : ℤ) : ℝ)) + s * (n : ℝ) = 0 := by
      push_cast
      ring
    rw [hexp, Real.rpow_zero]
  rw [← ENNReal.ofReal_mul (hnn _), ← ENNReal.ofReal_mul (mul_nonneg (hnn _) (hnn _)),
    hreal, ENNReal.ofReal_one]

/-! ## 3. The printed display, PROVED at the smooth-dual reading -/

/-- **the general coarse-graining proposition at finite `p`, at the smooth-dual reading.**

For every `p ∈ [2,∞)` and every dimension `d ≥ 2` there is `C(p,d) < ∞` such
that, for every `n < m`, every `s₁ < s < s₂`, every uniformly elliptic `𝐚` on
`□_m`, every `σ₀ > 0`, every `𝐠 ∈ W^{s₂,p}(□_m)` and every pair `u, v` solving
the printed pair of equations with `u - v ∈ H¹₀(□_m)`,

```text
  3^{-ms} ( σ₀ ‖∇u - ∇v‖_{W_hat^{-s,p}} + ‖𝐚∇u - σ₀∇v‖_{W_hat^{-s,p}} )
    ≤  (the printed right-hand side, at C).
```

This is the printed display, at the printed hypotheses, with the printed
right-hand side, and with `‖·‖_{W_hat^{-s,p}(□_m)}` read as the smooth fractional
dual.  Nothing in the proof is assumed: links 1 and 3 are `CoarseGraining`
theorems, link 2 is `HomCGDischargeBridge`. -/
theorem exists_printedCoarseGrainingFiniteP_smoothDual (d : ℕ) (hd : 2 ≤ d)
    (p : FiniteLpExponent) (hp : (2 : ℝ≥0∞) ≤ p.exponent) :
    letI : NeZero d := ⟨by omega⟩
    ∃ C : ℝ≥0∞, C < ∞ ∧
      ∀ (m n : ℤ) (hnm : n < m) (s1 s s2 : FractionalOrder),
        s1.1 < s.1 → s.1 < s2.1 →
      ∀ (a : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain (originCube d m)))
        (sigma0 : ℝ) (hsigma0 : 0 < sigma0) (g : Vec d → Vec d),
        MemCubeEuclideanFullWsp (originCube d m) s2 p g →
      ∀ u v : H1Function (openCubeSet (originCube d m)),
        IsForcedEquation (originCube d m) a u g →
        IsScalarForcedEquation (originCube d m) sigma0 v g →
        HasH10Difference (originCube d m) u v →
        ENNReal.ofReal (Real.rpow 3 (-s.1 * (m : ℝ))) *
            centeredCubeFluxComparisonSmoothDualLHS m a sigma0 u v s p ≤
          localCoarseGrainingLpRHS C (originCube d m) n
            (by simpa [originCube] using hnm.le) a sigma0 hsigma0 g u s1 s s2 p := by
  let : NeZero d := ⟨by omega⟩
  obtain ⟨Ccz, hCczTop, hCcz⟩ := exists_centeredCubeFluxComparison_cz d hd p
  obtain ⟨Clc, hClcTop, hClc⟩ := exists_localCoarseGrainingLp d hd
  refine ⟨Ccz * cubeEuclideanNegativeWspSmoothDualBesovConstant d * Clc, ?_, ?_⟩
  · exact ENNReal.mul_lt_top
      (ENNReal.mul_lt_top hCczTop (cubeEuclideanNegativeWspSmoothDualBesovConstant_lt_top d))
      hClcTop
  intro m n hnm s1 s s2 hs1s hss2 a sigma0 hsigma0 g hg u v hu hv hzero
  have hn : n ≤ (originCube d m).scale := by simpa [originCube] using hnm.le
  have hbal : IsCenteredCubeFluxBalanced m a sigma0 u v :=
    isCenteredCubeFluxBalanced_of_forced a hu hv
  have hzero' : HasCenteredCubeH10Difference m u v :=
    hasCenteredCubeH10Difference_iff.mpr hzero
  have h1 := hCcz m n hnm a sigma0 hsigma0 s u v hbal hzero'
  have h2 := localFluxDefect_smoothDualAverage_le hnm hn a sigma0 u s p
  have h3 := hClc p hp m n hnm s1 s s2 hs1s hss2 a sigma0 hsigma0 g hg u hu
  set Cd : ℝ≥0∞ := cubeEuclideanNegativeWspSmoothDualBesovConstant d with hCd
  set W : ℝ≥0∞ := ENNReal.ofReal (Real.rpow 3 (-s.1 * (m : ℝ))) with hW
  set Wmn : ℝ≥0∞ := ENNReal.ofReal (Real.rpow 3 (s.1 * (((m - n : ℤ) : ℝ)))) with hWmn
  set Wn : ℝ≥0∞ := ENNReal.ofReal (Real.rpow 3 (s.1 * (n : ℝ))) with hWn
  set A : ℝ≥0∞ := centeredCubeLocalFluxDefectSmoothDualLpAverage m n hnm a sigma0 u s p
    with hA
  set B : ℝ≥0∞ := localFluxDefectNegativeBesovLpAverage (originCube d m) n hn a sigma0 u s p
    with hB
  set R : ℝ≥0∞ := localCoarseGrainingLpRHS Clc (originCube d m) n hn a sigma0 hsigma0
    g u s1 s s2 p with hR
  have htriple : W * Wmn * Wn = 1 := ofReal_three_rpow_scale_triple s.1 m n
  calc W * centeredCubeFluxComparisonSmoothDualLHS m a sigma0 u v s p
      ≤ W * (Ccz * Wmn * A) := by gcongr
    _ ≤ W * (Ccz * Wmn * (Cd * Wn * B)) := by gcongr
    _ = (W * Wmn * Wn) * (Ccz * Cd * B) := by ring
    _ = Ccz * Cd * B := by rw [htriple, one_mul]
    _ ≤ Ccz * Cd * R := by gcongr
    _ = localCoarseGrainingLpRHS (Ccz * Cd * Clc) (originCube d m) n hn a sigma0
          hsigma0 g u s1 s s2 p := by
        rw [hR, localCoarseGrainingLpRHS_const_mul]

end

end Algsuperdiff.Section4.Provider.Homogenization
