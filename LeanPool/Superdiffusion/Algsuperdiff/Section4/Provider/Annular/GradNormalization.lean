/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.PrincipalResponseSwitchActualShell
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Annular.UglyChain
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Support.GaugeBridge

/-!
# GradNormalization

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The gradient-slot cube-scale normalization of `e.ugly.estimate.for.J.pre`

ABK26, Section 4.1.

```
3^{2n} || grad (k_L - k_{n-2}) ||_{W^{1,infinity}(z + cu_n)}
```

, whereas the cited lemma carries the unit-cube gauge `|| grad h
||_{W^{1,infinity}(cu_0)}`/4182.  The replacement is made with no comment; it is
the gradient half of the same silent rescaling whose error half is
`ErrorTransport.lean` and whose response half is `ResponseTransport.lean`.

This module proves that half.

## What was already there, and what is added

* `ApproximateRecurrence.centeredShellUnitCube_gradientW1Infinity` is `rfl` onto
  `(incrementUnitCube₂ ⟨n,v⟩ lowScale L omega).gradientW1Infinity`: the
  manuscript's centering constant `(k_L - k_m)_{cu_m}` is invisible to the
  gradient slot, for free.
* `BadEvents.gradientW1Infinity_incrementUnitCube₂_le` bounds that by
  `incrementOscGauge₂`, i.e. by `cubeOscGauge` of the literal increment.
* `Support.cubeOscGauge_mk_eq_zpow_mul_shellW1InfGradNorm` is the *identity*
  `cubeOscGauge ⟨n,v⟩ h = 3^{2n} · shellW1InfGradNorm n (translate (3^n v) h)`.

What is added here is (i) the composition of the three at the Section 4 lattice
enumerations, in the `Real.rpow` spelling the ugly chain reads, and (ii) the
slot monotonicity of `IsUglyJEstimate`, which is what lets the chain be fed an
*inequality* where `UglyChain.exists_responseJ_ugly_estimate` demands an
equality.  Without (ii) the normalization is unusable: the gauge comparison is
one-sided in the direction of the estimate, never an identity.

## The re-gauged chain

`exists_responseJ_ugly_estimate_of_grad_le` is
`UglyChain.exists_responseJ_ugly_estimate` with the binder
`h.gradientW1Infinity = 3^{2n} Gn` weakened to `h.gradientW1Infinity ≤ 3^{2n} Gn`
and with the same conclusion.  The proof runs the original chain at the exact
witness `Gn' := 3^{-2n} · h.gradientW1Infinity` and then enlarges the fourth
slot.  The nonnegativity of the output constant `C` is *derived*, not assumed:
`Cl ≥ 0` follows from the good-event budget `hlam` and `Cr ≥ 0` from the
`sigmaBar` ratio, and the remaining factors are squares.

## The `s ≤ 1/4` residual

Unchanged and carried honestly: the Section 2.4 sensitivity anchor needs both
exponent slots in `(0, 1/4]` while the enclosing proposition admits `s ∈ [8γ,
1/2]`.  Nothing here narrows or hides that; see `UglyPre.lean`.
-/

namespace Algsuperdiff.Section4.Provider.Annular

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Frozen.Section24
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Provider.BadEvents
open Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

noncomputable section

variable {d : ℕ}

/-! ## The `zpow`/`rpow` bridge at the cube-scale factor -/

/-- The cube-scale factor `3^{2n}` of the manuscript's gradient slot, in the
`Real.rpow` spelling the ugly chain uses and in the `zpow` spelling the shell
gauges use. -/
theorem three_rpow_two_mul_intCast (n : ℤ) :
    (3 : ℝ) ^ (2 * (n : ℝ)) = (3 : ℝ) ^ (2 * n) := by
  rw [show (2 : ℝ) * (n : ℝ) = ((2 * n : ℤ) : ℝ) from by push_cast; ring,
    Real.rpow_intCast]

/-! ## The normalization itself -/

/-- The frozen unit-cube gradient gate of the manuscript's own perturbation
`h = k_L - (k_L - k_m)_{cu_m} - k_{n-2}`, rescaled onto the unit cube at the
lattice cube `⟨n, v⟩ = 3^n v + cu_n`, is bounded by the manuscript's printed
slot

```
3^{2n} || grad (k_L - k_{lowScale}) ||_{W^{1,infinity}(3^n v + cu_n)} .
```

The centering constant has already disappeared (it is invisible to a gradient
gauge), so this is exactly the cube-scale normalization and nothing else. -/
theorem gradientW1Infinity_centeredShellUnitCube_le (M : ABKModel d) (n : ℤ)
    (v : Fin d → ℤ) {lowScale L : ℤ} (hle : lowScale ≤ L)
    (omega : Cutoff.CutoffSample d) (C : Mat d) (hC : matTranspose C = -C) :
    (centeredShellUnitCube M (⟨n, v⟩ : TriadicCube d) hle omega C
        hC).gradientW1Infinity ≤
      (3 : ℝ) ^ (2 * (n : ℝ)) *
        Support.shellW1InfGradNorm n
          (ShellField.translate (Support.triadicLatticePoint n v)
            (Provider.Stream.shellIncrement omega.1 lowScale L)) := by
  rw [centeredShellUnitCube_gradientW1Infinity, three_rpow_two_mul_intCast,
    ← Support.cubeOscGauge_mk_eq_zpow_mul_shellW1InfGradNorm n v]
  exact gradientW1Infinity_incrementUnitCube₂_le (⟨n, v⟩ : TriadicCube d) lowScale L
    omega

/-- The same at the `𝒢₂` cutoff level `n − 2`, i.e. in the exact spelling in
which `e.ugly.estimate.for.J.pre` reads the slot. -/
theorem gradientW1Infinity_centeredShellUnitCube_le_lowScale_sub_two
    (M : ABKModel d) (n : ℤ) (v : Fin d → ℤ) {L : ℤ} (hle : n - 2 ≤ L)
    (omega : Cutoff.CutoffSample d) (C : Mat d) (hC : matTranspose C = -C) :
    (centeredShellUnitCube M (⟨n, v⟩ : TriadicCube d) hle omega C
        hC).gradientW1Infinity ≤
      (3 : ℝ) ^ (2 * (n : ℝ)) *
        Support.shellW1InfGradNorm n
          (ShellField.translate (Support.triadicLatticePoint n v)
            (Provider.Stream.shellIncrement omega.1 (n - 2) L)) :=
  gradientW1Infinity_centeredShellUnitCube_le M n v hle omega C hC

/-! ## Slot monotonicity of `IsUglyJEstimate` -/

/-- **The `gradN`-slot monotonicity of the five-term display.**  Enlarging the
fourth slot preserves the estimate; the three sign conditions are the ones the
weight `C c_*^{-1} γ w` needs. -/
theorem isUglyJEstimate_mono_gradN
    {Jval E2 sigDiff L2 gradN gradN' gradM cstar gam w wgam C : ℝ}
    (hC0 : 0 ≤ C) (hcstar0 : 0 ≤ cstar⁻¹) (hgam0 : 0 ≤ gam) (hw0 : 0 ≤ w)
    (hgrad : gradN ≤ gradN')
    (h : IsUglyJEstimate Jval E2 sigDiff L2 gradN gradM cstar gam w wgam C) :
    IsUglyJEstimate Jval E2 sigDiff L2 gradN' gradM cstar gam w wgam C := by
  unfold IsUglyJEstimate at h ⊢
  have hbase : (0 : ℝ) ≤ C * cstar⁻¹ * gam * w :=
    mul_nonneg (mul_nonneg (mul_nonneg hC0 hcstar0) hgam0) hw0
  have hstep := mul_le_mul_of_nonneg_left hgrad hbase
  linarith only [h, hstep]

/-- **The `L2`-slot monotonicity of the five-term display.**  Its twin at the
third slot; the conservative `L^infinity`-for-`L^2` reading of the clause-(i)
third term is consumed through this lemma. -/
theorem isUglyJEstimate_mono_L2
    {Jval E2 sigDiff L2 L2' gradN gradM cstar gam w wgam C : ℝ}
    (hC0 : 0 ≤ C) (hcstar0 : 0 ≤ cstar⁻¹) (hgam0 : 0 ≤ gam) (hw0 : 0 ≤ w)
    (hL2 : L2 ≤ L2')
    (h : IsUglyJEstimate Jval E2 sigDiff L2 gradN gradM cstar gam w wgam C) :
    IsUglyJEstimate Jval E2 sigDiff L2' gradN gradM cstar gam w wgam C := by
  unfold IsUglyJEstimate at h ⊢
  have hbase : (0 : ℝ) ≤ C * cstar⁻¹ * gam * w :=
    mul_nonneg (mul_nonneg (mul_nonneg hC0 hcstar0) hgam0) hw0
  have hstep := mul_le_mul_of_nonneg_left hL2 hbase
  linarith only [h, hstep]

/-- **The-slot monotonicity of the five-term display**, at the first slot's weight
`C w`. -/
theorem isUglyJEstimate_mono_E2
    {Jval E2 E2' sigDiff L2 gradN gradM cstar gam w wgam C : ℝ}
    (hC0 : 0 ≤ C) (hw0 : 0 ≤ w) (hE2 : E2 ≤ E2')
    (h : IsUglyJEstimate Jval E2 sigDiff L2 gradN gradM cstar gam w wgam C) :
    IsUglyJEstimate Jval E2' sigDiff L2 gradN gradM cstar gam w wgam C := by
  unfold IsUglyJEstimate at h ⊢
  have hstep := mul_le_mul_of_nonneg_left hE2 (mul_nonneg hC0 hw0)
  linarith only [h, hstep]

/-! ## The re-gauged chain -/

/-- **The composed per-cube estimate, at an inequality in the gradient slot.**

`UglyChain.exists_responseJ_ugly_estimate` demands
`h.gradientW1Infinity = 3^{2n} Gn`.  The cube-scale normalization above is a
one-sided comparison -- the gauge of the rescaled increment is *bounded by* the
manuscript's slot, never equal to it -- so the chain has to be read at an
inequality.  This is that reading, with the same conclusion and the same
constants. -/
theorem exists_responseJ_ugly_estimate_of_grad_le (d : ℕ) (dimension : 2 ≤ d) :
    letI : NeZero d := ⟨by omega⟩
    ∃ Cs : ℝ, 0 < Cs ∧
      ∀ (M : ABKModel d) (m n : ℤ)
        (a : CoeffOn (cubeDomain (originCube d 0)))
        (h : UnitCubeSkewW2Infinity d) (e : Vec d)
        (s kap Cl Cr Cp Ash C Gn Gm Lnrm : ℝ),
        0 < s → s ≤ 1 / 4 → 8 * M.gamma ≤ s → vecNorm e = 1 →
        ((n : ℝ) ≤ (m : ℝ)) → 0 ≤ Ash → 0 ≤ Gn →
        0 < kap → M.gamma * kap ^ 2 = Disorder.cstar M →
        1 / 2 * (kap * (3 : ℝ) ^ (M.gamma * (m : ℝ))) ≤ (Annealed.sigmaBar M m : ℝ) →
        1 / 4 * (kap * (3 : ℝ) ^ (M.gamma * (n : ℝ))) ≤
          (Annealed.sigmaBar M (n - 2) : ℝ) →
        (Annealed.sigmaBar M (n - 2) : ℝ) *
            (unitCubeLambda (2 * M.gamma) (.finite 2) a)⁻¹ ≤
          Cl * (3 : ℝ) ^ (M.gamma * ((m : ℝ) - (n : ℝ))) →
        (Annealed.sigmaBar M (n - 2) : ℝ)⁻¹ *
            ((3 : ℝ) ^ (2 * (n : ℝ)) * Gn) ≤
          Ash * (3 : ℝ) ^ (s / 4 * ((m : ℝ) - (n : ℝ))) →
        (Annealed.sigmaBar M m : ℝ)⁻¹ * (Annealed.sigmaBar M (n - 2) : ℝ) ≤ Cr →
        h.gradientW1Infinity ≤ (3 : ℝ) ^ (2 * (n : ℝ)) * Gn →
        h.valueL2 ^ 2 ≤
          2 * Lnrm ^ 2 + 2 * (Cp * ((3 : ℝ) ^ (2 * (m : ℝ)) * Gm)) ^ 2 →
        Cs * (1 + Ash * Cl) ^ 2 * Cr * (1 + Cl)
            + 16 * Cs * (1 + Ash * Cl) ^ 2 * Cl * (1 + Cp ^ 2)
            + 4 * Cs * (1 + 4 * Cl ^ 2) ≤ C →
        IsUglyJEstimate
          (responseJ (cubeDomain (originCube d 0))
            (perturbCoeffOn (cubeDomain (originCube d 0)) a
              h.toLInfSkewMatrixFieldOn 1)
            (Observable.inverseSqrtLoad (Annealed.sigmaBar M m) e)
            (Observable.sqrtLoad (Annealed.sigmaBar M m) e))
          (unitCubeHomogenizationError s (.finite 2) (.finite 2) a
            (Observable.isotropicComparatorMatrix
              (Annealed.sigmaBar M (n - 2))) ^ 2)
          (((Annealed.sigmaBar M m : ℝ) *
            (Annealed.sigmaBar M (n - 2) : ℝ)⁻¹ - 1) ^ 2)
          (((3 : ℝ) ^ (-(M.gamma * (n : ℝ))) * Lnrm) ^ 2)
          (((3 : ℝ) ^ ((2 - M.gamma) * (n : ℝ)) * Gn) ^ 2)
          (((3 : ℝ) ^ ((2 - M.gamma) * (m : ℝ)) * Gm) ^ 2)
          (Disorder.cstar M) M.gamma
          ((3 : ℝ) ^ (s * ((m : ℝ) - (n : ℝ))))
          ((3 : ℝ) ^ ((s + M.gamma) * ((m : ℝ) - (n : ℝ)))) C := by
  have : NeZero d := ⟨by omega⟩
  obtain ⟨Cs, hCs, hbase⟩ := exists_responseJ_ugly_estimate d dimension
  refine ⟨Cs, hCs, ?_⟩
  intro M m n a h e s kap Cl Cr Cp Ash C Gn Gm Lnrm hs0 hs14 hsgam he hnm hAsh
    hGn hkap0 hkap hsigmlow hsignlow hlam hshell hratio hgrad hH hC
  have hg0 : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hcs0 : 0 < Disorder.cstar M := (Disorder.cstar_characterization M).1
  have hsn0 : (0 : ℝ) < (Annealed.sigmaBar M (n - 2) : ℝ) :=
    (Annealed.sigmaBar M (n - 2)).2
  have hsm0 : (0 : ℝ) < (Annealed.sigmaBar M m : ℝ) := (Annealed.sigmaBar M m).2
  have hGnn : (0 : ℝ) ≤ h.gradientW1Infinity := gradientW1Infinity_nonneg h
  have h3n : (0 : ℝ) < (3 : ℝ) ^ (2 * (n : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  -- the exact witness
  have heq : h.gradientW1Infinity =
      (3 : ℝ) ^ (2 * (n : ℝ)) *
        (((3 : ℝ) ^ (2 * (n : ℝ)))⁻¹ * h.gradientW1Infinity) := by
    rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt h3n), one_mul]
  have hGn'0 : (0 : ℝ) ≤ ((3 : ℝ) ^ (2 * (n : ℝ)))⁻¹ * h.gradientW1Infinity :=
    mul_nonneg (inv_nonneg.2 h3n.le) hGnn
  have hGn'le : ((3 : ℝ) ^ (2 * (n : ℝ)))⁻¹ * h.gradientW1Infinity ≤ Gn := by
    rw [inv_mul_le_iff₀ h3n]
    exact hgrad
  -- the shell budget at the exact witness
  have hshell' : (Annealed.sigmaBar M (n - 2) : ℝ)⁻¹ *
      ((3 : ℝ) ^ (2 * (n : ℝ)) *
        (((3 : ℝ) ^ (2 * (n : ℝ)))⁻¹ * h.gradientW1Infinity)) ≤
      Ash * (3 : ℝ) ^ (s / 4 * ((m : ℝ) - (n : ℝ))) := by
    refine le_trans (mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hsn0.le)) hshell
    exact mul_le_mul_of_nonneg_left hGn'le h3n.le
  -- nonnegativity of the output constant, derived
  have hlamInv : (0 : ℝ) ≤ (unitCubeLambda (2 * M.gamma) (.finite 2) a)⁻¹ :=
    Algsuperdiff.Section24.Sensitivity.Provider.LambdaUnconditional.unitCubeLambda_inv_nonneg
      a (by linarith only [hg0])
      Algsuperdiff.Section24.Sensitivity.Provider.LambdaUnconditional.isAdmissible_finite_two
  have hCl : (0 : ℝ) ≤ Cl := by
    have hq : (0 : ℝ) < (3 : ℝ) ^ (M.gamma * ((m : ℝ) - (n : ℝ))) :=
      Real.rpow_pos_of_pos (by norm_num) _
    have hleft : (0 : ℝ) ≤ (Annealed.sigmaBar M (n - 2) : ℝ) *
        (unitCubeLambda (2 * M.gamma) (.finite 2) a)⁻¹ := mul_nonneg hsn0.le hlamInv
    have hprod : (0 : ℝ) ≤ Cl * (3 : ℝ) ^ (M.gamma * ((m : ℝ) - (n : ℝ))) :=
      le_trans hleft hlam
    by_contra hneg
    push Not at hneg
    have hlt : Cl * (3 : ℝ) ^ (M.gamma * ((m : ℝ) - (n : ℝ))) < 0 :=
      mul_neg_of_neg_of_pos hneg hq
    linarith only [hprod, hlt]
  have hCr : (0 : ℝ) ≤ Cr := by
    have hleft : (0 : ℝ) ≤ (Annealed.sigmaBar M m : ℝ)⁻¹ *
        (Annealed.sigmaBar M (n - 2) : ℝ) :=
      mul_nonneg (inv_nonneg.2 hsm0.le) hsn0.le
    linarith only [hratio, hleft]
  have hC0 : (0 : ℝ) ≤ C := by
    have t1 : (0 : ℝ) ≤ Cs * (1 + Ash * Cl) ^ 2 * Cr * (1 + Cl) :=
      mul_nonneg (mul_nonneg (mul_nonneg hCs.le (sq_nonneg _)) hCr)
        (by linarith only [hCl])
    have t2 : (0 : ℝ) ≤ 16 * Cs * (1 + Ash * Cl) ^ 2 * Cl * (1 + Cp ^ 2) :=
      mul_nonneg (mul_nonneg (mul_nonneg (by linarith only [hCs] : (0 : ℝ) ≤ 16 * Cs)
        (sq_nonneg _)) hCl) (by positivity)
    have t3 : (0 : ℝ) ≤ 4 * Cs * (1 + 4 * Cl ^ 2) :=
      mul_nonneg (by linarith only [hCs]) (by positivity)
    linarith only [hC, t1, t2, t3]
  -- the chain at the exact witness, then the fourth slot enlarged
  have key := hbase M m n a h e s kap Cl Cr Cp Ash C
    (((3 : ℝ) ^ (2 * (n : ℝ)))⁻¹ * h.gradientW1Infinity) Gm Lnrm hs0 hs14 hsgam he
    hnm hAsh hGn'0 hkap0 hkap hsigmlow hsignlow hlam hshell' hratio heq hH hC
  refine isUglyJEstimate_mono_gradN hC0 (inv_nonneg.2 hcs0.le) hg0.le
    (Real.rpow_nonneg (by norm_num) _) ?_ key
  refine pow_le_pow_left₀ (by positivity) ?_ 2
  exact mul_le_mul_of_nonneg_left hGn'le (Real.rpow_nonneg (by norm_num) _)

end

end Algsuperdiff.Section4.Provider.Annular
