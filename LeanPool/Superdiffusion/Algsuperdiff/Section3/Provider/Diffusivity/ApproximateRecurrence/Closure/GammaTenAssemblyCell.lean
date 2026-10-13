/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.GammaTenAssemblySide
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.LocalizationFluctuationAncestor
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.LocalizationFluctuationSelectEndpoint

/-!
# GammaTenAssemblyCell

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The Step-2 cell integrand, bounded at one sample point

ABK26, Step 2 of `l.approximate.recurrence.formula`, target
`e.lower.bound.localization.terms`.

## The gap this module fills

`LocalizationFluctuationSelectEndpoint.fluctuationEnergyAverage` --- the quantity
Step 2 must put below `cgamma^{10}` --- is the grid average of the sample
integral of

```
  meshFluctuationCellIntegrand M n h Kc e e' wD wN R omega
    =  fluct( z + cu_n , a_omega; P_z , bfF_z ) ,
```

the *canonical* fluctuation number of `LocalizationFluctuationSelectValue`, which
mentions no minimizer.  The per-cube estimate that Step 2 rests on,
`LocalizationFluctuationPerCube.perCube_localizationFluctuation_le`, is instead
stated about a **realization** `tilde S_z` of the split's second `argmin`: its
left-hand side is `2 P_z . fint bfA tilde S_z + 2 mu(tilde S_z)`.

The two are reconciled exactly as
`blockVecDot_recurrenceP_le_descendantsAverage_switch_add_fluctuation`
reconciles them: at each sample point the proved split
`LocalizationRecurrenceMesh.exists_localizationRecurrenceMeshSplit_le_descendantsAverage_expanded`
produces a triple `(S, T, response)` on the whole grid, and
`LocalizationFluctuationSelectValue.localizationFluctuationValue_eq_of_isDoubledMuMinimizerField`
turns the canonical number into the realized pair.  The existential is opened
*inside* the sample-pointwise statement, so no measurable selection is made and
nothing about `S` or `T` survives in the conclusion.

## What is proved

* `meshFluctuationCellIntegrand_le_of_besovEnvelope` --- **the per-cell,
  per-sample Step-2 bound**:
  ```
    fluct_R(omega)
      <=  2 kappa Theta^2 | bfAhom^{1/2} P_z(omega) | Bg
            +  ( kappa Theta Bg )^2 ,
  ```
  with `kappa = besovDualityConst R s`, `Theta = doubledPoincareEllipticityFactor`
  at the sample's own coefficient family, and `Bg` any pathwise envelope of the
  finite-depth positive `q = 2` Besov seminorms of the gauged `bfF_z` on `R`.
  All eight analytic side conditions of the per-cube bound are discharged from
  `Closure.GammaTenAssemblySide`; none of them appears as a binder.
* `meshFluctuationCellIntegrand_le_ancestor_fold_shape` --- the same with
  `Theta^2` replaced by `32 c_{s,2}^{-2}` times
  `LocalizationFluctuationEllipticity.gaugedEllipticitySum`, the latter read at
  the cell's **own scale-`(n+h)` ancestor** and at exponent `cgamma`, via
  `LocalizationFluctuationAncestor.doubledPoincareEllipticityFactor_sq_le_recurrenceAncestor`
  (the ancestor bridge, cost `3^{22}`).  This is the shape in which the annealed
  Hoelder fold of `Closure.GammaTenGridFold` reads the ellipticity leg --- both
  summands are then **linear** in that sum --- and its `F`-leg is *literally*
  the quantity
  `LocalizationFluctuationSplitFoldArithmetic.exists_regime_gaugedEllipticitySum_pow_four_le`
  bounds, so it forces `cgamma < s`, hence a fixed Besov exponent `s`.
* `besovDualityConst_eq` --- the pinned constant is **cube-independent**: the
  two Besov scale weights are reciprocal, so `besovDualityConst R s = 2 d
  3^{d+s}` for every cell `R`.  This is what makes the two coefficients of the
  fold absolute rather than grid-dependent.

## Binders

The split's own binders (the large-cube gate, the depth-naming identity, and
the two weak formulations of `e.def.w` read along the sample), the
exponent/gauge windows `0 < s < 1`, `0 < sigma_0`, the cell membership `hR`,
and the pathwise envelope `Bg` with its two positive-seminorm bounds.  No
measurability, no integrability, no moment and no smallness proposition occurs:
everything below is a pointwise inequality at one fixed sample point.

## Scope

There is no `sorry`, no `admit`, no custom axiom and no `set_option
maxHeartbeats`.

## References

* ABK26, `l.approximate.recurrence.formula` Step 2,
  `e.lower.bound.basic.split`, `e.Pz.def`, `e.Fz.def`.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02 MeasureTheory
open Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Observable
open Algsuperdiff.Section3.Provider.CoarseEllipticity
open Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The duality constant is cube-independent -/

/-- **The pinned constant does not depend on the cell.**  `besovDualityConst Q s`
carries the product of the two Besov scale weights at exponents `-s` and `s`,
which is `(3^{Q.scale})^{s} (3^{Q.scale})^{-s} = 1`.  Hence `besovDualityConst
Q s = 2 d 3^{d+s}` on every triadic cube; this is why the two coefficients of
the Step-2 Hoelder fold are absolute constants and not grid-dependent weights. -/
theorem besovDualityConst_eq (Q : TriadicCube d) (s : ℝ) :
    besovDualityConst Q s = 2 * (d : ℝ) * (3 : ℝ) ^ ((d : ℝ) + s) := by
  have hf : (0 : ℝ) < cubeScaleFactor Q := cubeScaleFactor_pos' Q
  have hw : cubeBesovScaleWeight (-s) Q * cubeBesovScaleWeight s Q = 1 := by
    unfold cubeBesovScaleWeight
    rw [← Real.rpow_add hf, show -(-s) + -s = (0 : ℝ) by ring, Real.rpow_zero]
  rw [besovDualityConst, hw, mul_one]

/-! ## The per-cell, per-sample Step-2 bound -/

/-- **The Step-2 cell integrand at one sample point** (at one mesoscopic cell).

```
  fluct_R(omega)  <=  2 kappa Theta^2 | bfAhom^{1/2} P_z | Bg  +  (kappa Theta Bg)^2 ,
```

`kappa = besovDualityConst R s` (cube-independent, `besovDualityConst_eq`),
`Theta = doubledPoincareEllipticityFactor sig0 R a_omega s`, and `Bg` any real
dominating every finite-depth positive `q = 2` Besov seminorm of the two gauged
legs of `bfF_z` on `R`.

The left-hand side is *verbatim*
`LocalizationFluctuationSelectEndpoint.meshFluctuationCellIntegrand`, i.e. the
integrand of `fluctuationEnergyAverage`.

exactly on the binders listed in the module docstring: the split's own gates
and weak formulations, the exponent/gauge windows, the cell membership, and the
envelope.  All eight analytic side conditions of
`perCube_localizationFluctuation_le` are **discharged**, not assumed. -/
theorem meshFluctuationCellIntegrand_le_of_besovEnvelope [NeZero d]
    (M : ABKModel d) (n Kc : ℤ) (h : ℕ)
    (hK : (10 : ℝ) ^ (10 : ℕ) * M.gamma⁻¹ ≤ (Kc : ℝ) - ((n + (h : ℤ) : ℤ) : ℝ))
    (e e' : Vec d) (j : ℕ)
    (hscale : ((originCube d Kc).scale : ℤ) - (j : ℤ) =
      recurrenceMesoScale recurrenceGapMultiplier M.gamma (n + (h : ℤ)) (h : ℤ))
    (wD : ShellSeq d → H10Function (openCubeSet (originCube d Kc)))
    (wN : ShellSeq d → H1MeanZeroFunction (openCubeSet (originCube d Kc)))
    (omega : CutoffSample d)
    (hwD : IsZeroTraceDirichletRhsWeakSolution
      (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ))
      (openCubeSet (originCube d Kc)) (wD omega.val)
      (fun x => -Corrector.streamForcing
        ((Annealed.sigmaBar M n : ℝ))⁻¹ omega.val n (n + (h : ℤ)) e x))
    (hwN : IsMeanZeroNeumannRhsWeakSolution
      (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ))
      (openCubeSet (originCube d Kc)) (wN omega.val)
      (fun x => -Corrector.streamForcing
        ((Annealed.sigmaBar M n : ℝ))⁻¹ omega.val n (n + (h : ℤ)) e' x))
    {R : TriadicCube d} (hR : R ∈ descendantsAtDepth (originCube d Kc) j)
    {s sig0 Bg : ℝ} (hs : 0 < s) (hs1 : s < 1) (hsig0 : 0 < sig0) (hBg : 0 ≤ Bg)
    (hpos1 : ∀ N : ℕ, cubeBesovPositiveVectorPartialSeminormTwo R s N
      (fun x => (blockGaugeUp sig0
        ((localizationFz (Annealed.sigmaBar M n) omega.val n (n + (h : ℤ)) e' R
          (wD omega.val) (wN omega.val)).eval x)).1) ≤ Bg)
    (hpos2 : ∀ N : ℕ, cubeBesovPositiveVectorPartialSeminormTwo R s N
      (fun x => (blockGaugeUp sig0
        ((localizationFz (Annealed.sigmaBar M n) omega.val n (n + (h : ℤ)) e' R
          (wD omega.val) (wN omega.val)).eval x)).2) ≤ Bg) :
    meshFluctuationCellIntegrand M n h Kc e e' wD wN R omega ≤
      2 * (besovDualityConst R s *
            doubledPoincareEllipticityFactor sig0 R
              (coefficientCutoffTriadicCoeffFamily M (n + (h : ℤ)) omega) s *
            doubledPoincareEllipticityFactor sig0 R
              (coefficientCutoffTriadicCoeffFamily M (n + (h : ℤ)) omega) s) *
          blockVecNormSum (blockGaugeUp sig0
            (principalPz (Annealed.sigmaBar M n) omega.val n (n + (h : ℤ)) e e' R
              (wD omega.val) (wN omega.val))) * Bg +
        (besovDualityConst R s *
            doubledPoincareEllipticityFactor sig0 R
              (coefficientCutoffTriadicCoeffFamily M (n + (h : ℤ)) omega) s * Bg) *
          (besovDualityConst R s *
            doubledPoincareEllipticityFactor sig0 R
              (coefficientCutoffTriadicCoeffFamily M (n + (h : ℤ)) omega) s * Bg) := by
  classical
  have hm : n + (h : ℤ) - (h : ℤ) = n := by omega
  obtain ⟨S, T, hS, hT, hresp, _hle⟩ :=
    exists_localizationRecurrenceMeshSplit_le_descendantsAverage_expanded M omega
      (n + (h : ℤ)) Kc h hK e e' j hscale (wD omega.val) (wN omega.val)
      (by rw [hm]; exact hwD) (by rw [hm]; exact hwN)
  rw [hm] at hS hT
  -- the geometry of the cell inside the localization cube
  have hsub : openCubeSet R ⊆ openCubeSet (originCube d Kc) :=
    openCubeSet_subset_of_mem_descendantsAtDepth hR
  -- the two `L^2` legs of the realized response field
  have hTpot : MemVectorL2 (openCubeSet R) (T R).potential :=
    memVectorL2_potential_of_isDoubledResponseField (hresp R hR)
  have hTflux : MemVectorL2 (openCubeSet R) (T R).flux :=
    memVectorL2_flux_of_isDoubledResponseField (hresp R hR)
  -- the two `L^2` legs of `bfF_z` on the cell
  have hFpot : MemVectorL2 (openCubeSet R)
      (localizationFz (Annealed.sigmaBar M n) omega.val n (n + (h : ℤ)) e' R
        (wD omega.val) (wN omega.val)).potential :=
    memVectorL2_localizationFz_potential (Annealed.sigmaBar M n) omega.val n
      (n + (h : ℤ)) e' R R hsub (wD omega.val) (wN omega.val)
  have hFflux : MemVectorL2 (openCubeSet R)
      (localizationFz (Annealed.sigmaBar M n) omega.val n (n + (h : ℤ)) e' R
        (wD omega.val) (wN omega.val)).flux :=
    memVectorL2_localizationFz_flux (Annealed.sigmaBar M n) omega.val n
      (n + (h : ℤ)) e' R R hsub (wD omega.val) (wN omega.val)
  -- the canonical number equals the realized pair
  have hval := localizationFluctuationValue_eq_of_isDoubledMuMinimizerField
    (hS R hR) (hT R hR) (hresp R hR)
  change localizationFluctuationValue (cubeDomain R)
      ((coefficientCutoffTriadicCoeffFamily M (n + (h : ℤ)) omega).coeffOn R)
      (principalPz (Annealed.sigmaBar M n) omega.val n (n + (h : ℤ)) e e' R
        (wD omega.val) (wN omega.val))
      (localizationFz (Annealed.sigmaBar M n) omega.val n (n + (h : ℤ)) e' R
        (wD omega.val) (wN omega.val)) ≤ _
  rw [hval]
  simp only [cubeDomain_coe]
  exact perCube_localizationFluctuation_le (Annealed.sigmaBar M n) omega.val n
    (n + (h : ℤ)) e' R hsub (wD omega.val) hwN
    (coefficientCutoffTriadicCoeffFamily M (n + (h : ℤ)) omega)
    (principalPz (Annealed.sigmaBar M n) omega.val n (n + (h : ℤ)) e e' R
      (wD omega.val) (wN omega.val))
    (hT R hR) (hresp R hR) hs hs1 hsig0 hBg
    (memLp_two_gradH10_normalizedCubeMeasure_of_subset R hsub (wD omega.val))
    (memLp_two_neumannFluxField_normalizedCubeMeasure (Annealed.sigmaBar M n) omega.val n
      (n + (h : ℤ)) e' R hsub (wN omega.val))
    (memLp_two_blockMatVecMul_blockMatrixField_fst R _ hTpot hTflux)
    (memLp_two_blockMatVecMul_blockMatrixField_snd R _ hTpot hTflux)
    (memLp_two_localizationFz_fst (Annealed.sigmaBar M n) omega.val n (n + (h : ℤ)) e' R
      hsub (wD omega.val) (wN omega.val))
    (memLp_two_localizationFz_snd (Annealed.sigmaBar M n) omega.val n (n + (h : ℤ)) e' R
      hsub (wD omega.val) (wN omega.val))
    (integrableOn_gaugedPairing_fst R sig0 _ hTpot hTflux hFpot)
    (integrableOn_gaugedPairing_snd R sig0 _ hTpot hTflux hFflux)
    hpos1 hpos2

/-- The algebra of the fold shape: replacing `Theta^2` by `cst * Gv` in both
summands, the two nonnegative weights being carried through. -/
private theorem gammaTenCell_fold_arith {kap Th V Bg cst Gv : ℝ}
    (hkap0 : 0 ≤ kap) (hV0 : 0 ≤ V) (hBg : 0 ≤ Bg) (hsq : Th * Th ≤ cst * Gv) :
    2 * (kap * Th * Th) * V * Bg + (kap * Th * Bg) * (kap * Th * Bg) ≤
      2 * kap * cst * (Gv * V * Bg) + kap * kap * cst * (Gv * Bg * Bg) := by
  have hcross : 2 * (kap * Th * Th) * V * Bg ≤ 2 * kap * cst * (Gv * V * Bg) := by
    have hfac : (0 : ℝ) ≤ 2 * kap * (V * Bg) := by
      have := mul_nonneg hV0 hBg
      positivity
    calc 2 * (kap * Th * Th) * V * Bg = 2 * kap * (V * Bg) * (Th * Th) := by ring
      _ ≤ 2 * kap * (V * Bg) * (cst * Gv) := mul_le_mul_of_nonneg_left hsq hfac
      _ = 2 * kap * cst * (Gv * V * Bg) := by ring
  have hquad : (kap * Th * Bg) * (kap * Th * Bg) ≤ kap * kap * cst * (Gv * Bg * Bg) := by
    have hfac : (0 : ℝ) ≤ kap * kap * (Bg * Bg) := by positivity
    calc (kap * Th * Bg) * (kap * Th * Bg) = kap * kap * (Bg * Bg) * (Th * Th) := by ring
      _ ≤ kap * kap * (Bg * Bg) * (cst * Gv) := mul_le_mul_of_nonneg_left hsq hfac
      _ = kap * kap * cst * (Gv * Bg * Bg) := by ring
  exact add_le_add hcross hquad

/-- **The fold shape at the cell's own scale-`(n+h)` ancestor** (after the ancestor
bridge).

This is the variant whose ellipticity leg is *exactly* the one the proved
moment producer bounds:
`LocalizationFluctuationSplitFoldArithmetic.exists_regime_gaugedEllipticitySum_pow_four_le`
delivers `E[ (gaugedEllipticitySum sigmabar (ancestorAtScale R m) cgamma a)^4 ]
<= cgamma^{-8}` at the **ancestor** `ancestorAtScale R (n+h)`, at exponent
`cgamma`, whereas the per-cube bound is read at the cell `R` and at the Besov
exponent `s`.
`LocalizationFluctuationAncestor.doubledPoincareEllipticityFactor_sq_le_recurrenceAncestor`
is the bridge, at the price of the absolute factor `3^{22}`; it needs `cgamma <
s`, so this route is read at a **fixed** `s` (any `s` with `cgamma < s <= 1/2`
works, e.g. `s = 1/2`), which is also what makes `c_{s,2}^{-2}` and hence `c1`,
`c2` absolute constants.

The conclusion is again
```
  fluct_R(omega)  <=  c1 * ( F_R G_R H_R )  +  c2 * ( F_R H_R H_R )
```
with `F_R = gaugedEllipticitySum sigma_0 (ancestorAtScale R (n+h)) cgamma a_omega`. -/
theorem meshFluctuationCellIntegrand_le_ancestor_fold_shape [NeZero d]
    (M : ABKModel d) (n Kc : ℤ) (h : ℕ)
    (hK : (10 : ℝ) ^ (10 : ℕ) * M.gamma⁻¹ ≤ (Kc : ℝ) - ((n + (h : ℤ) : ℤ) : ℝ))
    (e e' : Vec d) (j : ℕ)
    (hscale : ((originCube d Kc).scale : ℤ) - (j : ℤ) =
      recurrenceMesoScale recurrenceGapMultiplier M.gamma (n + (h : ℤ)) (h : ℤ))
    (wD : ShellSeq d → H10Function (openCubeSet (originCube d Kc)))
    (wN : ShellSeq d → H1MeanZeroFunction (openCubeSet (originCube d Kc)))
    (omega : CutoffSample d)
    (hwD : IsZeroTraceDirichletRhsWeakSolution
      (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ))
      (openCubeSet (originCube d Kc)) (wD omega.val)
      (fun x => -Corrector.streamForcing
        ((Annealed.sigmaBar M n : ℝ))⁻¹ omega.val n (n + (h : ℤ)) e x))
    (hwN : IsMeanZeroNeumannRhsWeakSolution
      (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ))
      (openCubeSet (originCube d Kc)) (wN omega.val)
      (fun x => -Corrector.streamForcing
        ((Annealed.sigmaBar M n : ℝ))⁻¹ omega.val n (n + (h : ℤ)) e' x))
    {R : TriadicCube d} (hR : R ∈ descendantsAtDepth (originCube d Kc) j)
    (hsc : R.scale =
      recurrenceMesoScale recurrenceGapMultiplier M.gamma (n + (h : ℤ)) (h : ℤ))
    (hcover : (((recurrenceGapMultiplier : ℕ) : ℝ) + 1) ^ 2 ≤ M.gamma⁻¹)
    (hshell : (h : ℝ) ≤ 6 * Disorder.cstar M * M.gamma⁻¹)
    {s sig0 Bg : ℝ} (hgs : M.gamma < s) (hs1 : s < 1) (hsig0 : 0 < sig0) (hBg : 0 ≤ Bg)
    (hpos1 : ∀ N : ℕ, cubeBesovPositiveVectorPartialSeminormTwo R s N
      (fun x => (blockGaugeUp sig0
        ((localizationFz (Annealed.sigmaBar M n) omega.val n (n + (h : ℤ)) e' R
          (wD omega.val) (wN omega.val)).eval x)).1) ≤ Bg)
    (hpos2 : ∀ N : ℕ, cubeBesovPositiveVectorPartialSeminormTwo R s N
      (fun x => (blockGaugeUp sig0
        ((localizationFz (Annealed.sigmaBar M n) omega.val n (n + (h : ℤ)) e' R
          (wD omega.val) (wN omega.val)).eval x)).2) ≤ Bg) :
    meshFluctuationCellIntegrand M n h Kc e e' wD wN R omega ≤
      2 * besovDualityConst R s *
            (32 * (Ch03.poincareDiscountFactor s (.finite 2) *
              Ch03.poincareDiscountFactor s (.finite 2)) * Real.rpow (3 : ℝ) 22) *
          (gaugedEllipticitySum sig0 (ancestorAtScale R (n + (h : ℤ))) M.gamma
              (coefficientCutoffTriadicCoeffFamily M (n + (h : ℤ)) omega) *
            blockVecNormSum (blockGaugeUp sig0
              (principalPz (Annealed.sigmaBar M n) omega.val n (n + (h : ℤ)) e e' R
                (wD omega.val) (wN omega.val))) * Bg) +
        besovDualityConst R s * besovDualityConst R s *
            (32 * (Ch03.poincareDiscountFactor s (.finite 2) *
              Ch03.poincareDiscountFactor s (.finite 2)) * Real.rpow (3 : ℝ) 22) *
          (gaugedEllipticitySum sig0 (ancestorAtScale R (n + (h : ℤ))) M.gamma
              (coefficientCutoffTriadicCoeffFamily M (n + (h : ℤ)) omega) * Bg * Bg) := by
  have hgamma : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hs : (0 : ℝ) < s := lt_trans hgamma hgs
  refine (meshFluctuationCellIntegrand_le_of_besovEnvelope M n Kc h hK e e' j hscale wD wN
    omega hwD hwN hR hs hs1 hsig0 hBg hpos1 hpos2).trans ?_
  set af : Ch02.TriadicCoeffFamily d :=
    coefficientCutoffTriadicCoeffFamily M (n + (h : ℤ)) omega with haf
  set kap : ℝ := besovDualityConst R s with hkap
  set Th : ℝ := doubledPoincareEllipticityFactor sig0 R af s with hTh
  set V : ℝ := blockVecNormSum (blockGaugeUp sig0
    (principalPz (Annealed.sigmaBar M n) omega.val n (n + (h : ℤ)) e e' R
      (wD omega.val) (wN omega.val))) with hV
  set G : ℝ := gaugedEllipticitySum sig0 (ancestorAtScale R (n + (h : ℤ))) M.gamma af
    with hG
  have hkap0 : (0 : ℝ) ≤ kap := besovDualityConst_nonneg R s
  have hV0 : (0 : ℝ) ≤ V := blockVecNormSum_nonneg _
  have hsq : Th * Th ≤
      32 * (Ch03.poincareDiscountFactor s (.finite 2) *
        Ch03.poincareDiscountFactor s (.finite 2)) * Real.rpow (3 : ℝ) 22 * G := by
    have hbase := doubledPoincareEllipticityFactor_sq_le_recurrenceAncestor M R
      (n + (h : ℤ)) h af hsc hgs hsig0 hcover hshell
    calc Th * Th ≤ 32 * (Ch03.poincareDiscountFactor s (.finite 2) *
          Ch03.poincareDiscountFactor s (.finite 2)) *
          (Real.rpow (3 : ℝ) 22 * G) := hbase
      _ = 32 * (Ch03.poincareDiscountFactor s (.finite 2) *
          Ch03.poincareDiscountFactor s (.finite 2)) * Real.rpow (3 : ℝ) 22 * G := by ring
  exact gammaTenCell_fold_arith hkap0 hV0 hBg hsq

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure
