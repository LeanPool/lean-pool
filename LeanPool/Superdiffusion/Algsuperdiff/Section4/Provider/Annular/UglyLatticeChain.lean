/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Annular.ErrorTransport
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Annular.EventBudgets
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Annular.ValueBridge

/-!
# UglyLatticeChain

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# `e.ugly.estimate.for.J` read at a lattice cube `z + cu_n`

ABK26, Section 4.1.  Step 2 of `p.mathcalE.annular.decomp` states the ugly
estimate "on each cube `z + cu_n`", while the Section 2.4 sensitivity anchor it
cites lives on the unit cube `cu_0`.  Four slot transports close the gap, and
this module runs all four at once:

* the gradient leg -- `GradNormalization.gradientW1Infinity_centeredShellUnitCube_le`;
* the value leg -- `ValueBridge.valueL2_sq_centeredShellUnitCube_le`.

The output is `Ugly.IsUglyJEstimate` with **every** slot at a manuscript object
on the lattice cube `⟨n, v⟩ = 3^n v + cu_n`: the response of `tilde a_{L,m}`,
the annular `(2,2)` error atom at the translated sample, the `sigma-bar` ratio,
the `L^infinity` content of `k_m - k_{n-2}` on `z + cu_n`, the
`W^{1,infinity}` gauge of `grad (k_L - k_{n-2})` on `z + cu_n` and the same
gauge of `grad (k_L - k_m)` on `cu_m`.

## The `s <= 1/4` residual, carried honestly

The anchor needs both of its exponent slots in `(0, 1/4]`; the enclosing
proposition admits `s in [8 gamma, 1/2]`.  `hs14` below is that restriction,
stated and never hidden.

## The conservative `L^infinity` reading

The third slot is produced at the `L^infinity` norm of `k_m - k_{n-2}` on
`z + cu_n` where the manuscript prints the volume-normalized `L^2` norm of the
same increment on the same cube.  This is the dominating direction and it is
exactly the reading A2b's `annularL2Block` consumes; see `ValueBridge.lean` for
the carrier discussion.
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

/-! ## Part A -- splitting the gradient gauge at an intermediate scale -/

/-- The literal increment `k_c - k_a` is the two-term shell sum
`(k_b - k_a) + (k_c - k_b)`. -/
private theorem shellIncrement_eq_sum_two (omega : Cutoff.ShellSeq d) {a b c : ℤ}
    (hab : a ≤ b) (hbc : b ≤ c) :
    Provider.Stream.shellIncrement omega a c =
      ShellField.sum (Finset.univ : Finset (Fin 2))
        ![Provider.Stream.shellIncrement omega a b,
          Provider.Stream.shellIncrement omega b c] := by
  classical
  have hdisj : Disjoint (Finset.Ioc a b) (Finset.Ioc b c) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    rw [Finset.mem_Ioc] at hx hx'
    omega
  have hunion : Finset.Ioc a b ∪ Finset.Ioc b c = Finset.Ioc a c :=
    Finset.Ioc_union_Ioc_eq_Ioc hab hbc
  refine ShellField.ext fun x => ?_
  show (∑ l ∈ Finset.Ioc a c, omega l x) =
    ∑ i : Fin 2,
      (![Provider.Stream.shellIncrement omega a b,
        Provider.Stream.shellIncrement omega b c] i) x
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  show (∑ l ∈ Finset.Ioc a c, omega l x) =
    (∑ l ∈ Finset.Ioc a b, omega l x) + ∑ l ∈ Finset.Ioc b c, omega l x
  rw [← Finset.sum_union hdisj, hunion]

/-- **The gradient gauge splits at an intermediate scale.**

`|| grad (k_c - k_a) ||_{W^{1,infinity}(z+cu_k)}` is at most the sum of the
two partial gauges.  This is the Lean form of the manuscript's `m`-versus-`L`
bookkeeping: the head block `(a, b]` feeds
`e.mathcalE.annular.decomp.pre.zero`'s fourth term and the tail block `(b, c]`
its fifth. -/
theorem shellW1InfGradNorm_translate_shellIncrement_add_le (k : ℤ) (v : Fin d → ℤ)
    (omega : Cutoff.ShellSeq d) {a b c : ℤ} (hab : a ≤ b) (hbc : b ≤ c) :
    Support.shellW1InfGradNorm k
        (ShellField.translate (Support.triadicLatticePoint k v)
          (Provider.Stream.shellIncrement omega a c)) ≤
      Support.shellW1InfGradNorm k
          (ShellField.translate (Support.triadicLatticePoint k v)
            (Provider.Stream.shellIncrement omega a b))
        + Support.shellW1InfGradNorm k
            (ShellField.translate (Support.triadicLatticePoint k v)
              (Provider.Stream.shellIncrement omega b c)) := by
  classical
  rw [shellIncrement_eq_sum_two omega hab hbc]
  refine le_trans
    (Support.shellW1InfGradNorm_translate_sum_le k v (Finset.univ : Finset (Fin 2))
      _) (le_of_eq ?_)
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]

/-- **The cross-scale comparison of the gradient gauge, at a lattice centre.**

For a scale-`n` lattice point `z` of `cu_m` the annulus cube `z + cu_n` sits
inside `cu_m`, so the volume-normalized `W^{1,infinity}` gauge on `z + cu_n`
is at most `3^{m-n}` times the one on `cu_m`.  This is the manuscript's
auxiliary step (`|| grad j_k ||_{W^{1,infinity}(z+cu_n)}` replaced by `3^{m-n}
|| grad j_k ||_{W^{1,infinity}(cu_m)}`), which
`Support.shellW1InfGradNorm_le_zpow_mul_of_le` supplies only at a common
centre. -/
theorem shellW1InfGradNorm_translate_le_zpow_mul {n m : ℤ} (hnm : n ≤ m)
    {v : Fin d → ℤ} (hv : v ∈ Support.latticeCubeSet d n m) (j : ShellField d) :
    Support.shellW1InfGradNorm n
        (ShellField.translate (Support.triadicLatticePoint n v) j) ≤
      (3 : ℝ) ^ (m - n) * Support.shellW1InfGradNorm m j := by
  have hW0 : (0 : ℝ) ≤ Support.shellW1InfGradNorm m j :=
    Support.shellW1InfGradNorm_nonneg m j
  have hone : (1 : ℝ) ≤ (3 : ℝ) ^ (m - n) :=
    one_le_zpow₀ (by norm_num : (1 : ℝ) ≤ 3) (by omega)
  have hS : Provider.Stream.localCubeSecondDerivNorm n
      (ShellField.translate (Support.triadicLatticePoint n v) j) ≤
      Provider.Stream.localCubeSecondDerivNorm m j := by
    refine Provider.Stream.localCubeSecondDerivNorm_le_of_forall n _
      (Provider.Stream.localCubeSecondDerivNorm_nonneg m j) ?_
    intro x hx
    have hmem := translate_openCubeSet_originCube_subset hnm hv hx
    have hshift : ShellField.matrixSecondDerivativeNorm
        (ShellField.secondDeriv
          (ShellField.translate (Support.triadicLatticePoint n v) j) x)
        = ShellField.matrixSecondDerivativeNorm
          (ShellField.secondDeriv j (x + Support.triadicLatticePoint n v)) := by
      rw [ShellField.translate_secondDeriv]
    rw [hshift]
    exact Provider.Stream.matrixSecondDerivativeNorm_secondDeriv_le_localCubeSecondDerivNorm
      m j hmem
  have hD : Provider.Stream.localCubeDerivNorm n
      (ShellField.translate (Support.triadicLatticePoint n v) j) ≤
      Provider.Stream.localCubeDerivNorm m j := by
    refine Provider.Stream.localCubeDerivNorm_le_of_forall n _
      (Provider.Stream.localCubeDerivNorm_nonneg m j) ?_
    intro x hx
    have hmem := translate_openCubeSet_originCube_subset hnm hv hx
    have hshift : ShellField.matrixDerivativeNorm
        (ShellField.deriv
          (ShellField.translate (Support.triadicLatticePoint n v) j) x)
        = ShellField.matrixDerivativeNorm
          (ShellField.deriv j (x + Support.triadicLatticePoint n v)) := by
      rw [ShellField.translate_deriv]
    rw [hshift]
    exact Provider.Stream.matrixDerivativeNorm_deriv_le_localCubeDerivNorm m j hmem
  rw [Support.shellW1InfGradNorm_def]
  refine max_le ?_ ?_
  · refine hS.trans ((Support.localCubeSecondDerivNorm_le_shellW1InfGradNorm m j).trans ?_)
    calc Support.shellW1InfGradNorm m j = 1 * Support.shellW1InfGradNorm m j :=
          (one_mul _).symm
      _ ≤ (3 : ℝ) ^ (m - n) * Support.shellW1InfGradNorm m j :=
          mul_le_mul_of_nonneg_right hone hW0
  · have hpn : (0 : ℝ) < (3 : ℝ) ^ (-n) := by positivity
    have hstep := mul_le_mul_of_nonneg_left hD hpn.le
    have hrw : (3 : ℝ) ^ (-n) * Provider.Stream.localCubeDerivNorm m j
        = (3 : ℝ) ^ (m - n) *
          ((3 : ℝ) ^ (-m) * Provider.Stream.localCubeDerivNorm m j) := by
      rw [← mul_assoc, ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
      congr 2
      ring
    refine hstep.trans ?_
    rw [hrw]
    exact mul_le_mul_of_nonneg_left
      (Support.three_zpow_mul_localCubeDerivNorm_le_shellW1InfGradNorm m j)
      (by positivity)

/-- **The `gradM`-slot monotonicity of the five-term display**, at the fifth
slot's weight `C c_*^{-1} gamma w_gamma`. -/
theorem isUglyJEstimate_mono_gradM
    {Jval E2 sigDiff L2 gradN gradM gradM' cstar gam w wgam C : ℝ}
    (hC0 : 0 ≤ C) (hcstar0 : 0 ≤ cstar⁻¹) (hgam0 : 0 ≤ gam) (hwgam0 : 0 ≤ wgam)
    (hgrad : gradM ≤ gradM')
    (h : IsUglyJEstimate Jval E2 sigDiff L2 gradN gradM cstar gam w wgam C) :
    IsUglyJEstimate Jval E2 sigDiff L2 gradN gradM' cstar gam w wgam C := by
  unfold IsUglyJEstimate at h ⊢
  have hbase : (0 : ℝ) ≤ C * cstar⁻¹ * gam * wgam :=
    mul_nonneg (mul_nonneg (mul_nonneg hC0 hcstar0) hgam0) hwgam0
  have hstep := mul_le_mul_of_nonneg_left hgrad hbase
  linarith only [h, hstep]

/-! ## Part B -- the composed per-cube estimate at a lattice cube -/

/-- **`e.ugly.estimate.for.J` at the lattice cube `⟨n, v⟩`**.

The Section 2.4 sensitivity anchor, collapsed by `UglyChain` and read through
the four slot transports, at the manuscript's own perturbation `h = k_L - (k_L
- k_m)_{cu_m} - k_{n-2}` and its own coefficient `tilde a_{L,m} = a_L - (k_L -
k_m)_{cu_m}`.

Every quantity on both sides is a manuscript object on `3^n v + cu_n`; nothing
unit-cube remains. -/
theorem exists_uglyJEstimate_lattice_cube (d : ℕ) (dimension : 2 ≤ d) :
    letI : NeZero d := ⟨by omega⟩
    ∃ Cs : ℝ, 0 < Cs ∧
      ∀ (M : ABKModel d) (m n L : ℤ) (v : Fin d → ℤ) (e : Vec d)
        (omega : Cutoff.CutoffSample d) (s kap Cl Cr Ash C : ℝ),
        n ≤ m → m ≤ L → v ∈ Support.latticeCubeSet d n m →
        0 < s → s ≤ 1 / 4 → 8 * M.gamma ≤ s → vecNorm e = 1 → 0 ≤ Ash →
        0 < kap → M.gamma * kap ^ 2 = Disorder.cstar M →
        1 / 2 * (kap * (3 : ℝ) ^ (M.gamma * (m : ℝ))) ≤ (Annealed.sigmaBar M m : ℝ) →
        1 / 4 * (kap * (3 : ℝ) ^ (M.gamma * (n : ℝ))) ≤
          (Annealed.sigmaBar M (n - 2) : ℝ) →
        (Annealed.sigmaBar M (n - 2) : ℝ) *
            (unitCubeLambda (2 * M.gamma) (.finite 2)
              (unitRescaledCutoffCoeff M (⟨n, v⟩ : TriadicCube d) (n - 2) omega))⁻¹ ≤
          Cl * (3 : ℝ) ^ (M.gamma * ((m : ℝ) - (n : ℝ))) →
        (Annealed.sigmaBar M (n - 2) : ℝ)⁻¹ *
            ((3 : ℝ) ^ (2 * (n : ℝ)) *
              Support.shellW1InfGradNorm n
                (ShellField.translate (Support.triadicLatticePoint n v)
                  (Provider.Stream.shellIncrement omega.1 (n - 2) L))) ≤
          Ash * (3 : ℝ) ^ (s / 4 * ((m : ℝ) - (n : ℝ))) →
        (Annealed.sigmaBar M m : ℝ)⁻¹ * (Annealed.sigmaBar M (n - 2) : ℝ) ≤ Cr →
        Cs * (1 + Ash * Cl) ^ 2 * Cr * (1 + Cl)
            + 16 * Cs * (1 + Ash * Cl) ^ 2 * Cl * (1 + centeringConst d ^ 2)
            + 4 * Cs * (1 + 4 * Cl ^ 2) ≤ C →
        IsUglyJEstimate
          (responseJ (cubeDomain (⟨n, v⟩ : TriadicCube d))
            ((subConstCutoffTriadicCoeffFamily M L
              (Support.fluxIncrementAverage M L m (originCube d m) omega)
              (matTranspose_fluxIncrementAverage M L m (originCube d m) omega)
              omega).coeffOn (⟨n, v⟩ : TriadicCube d))
            (Observable.inverseSqrtLoad (Annealed.sigmaBar M m) e)
            (Observable.sqrtLoad (Annealed.sigmaBar M m) e))
          (Support.annularErrorAtom M n s
            (Cutoff.translateCutoffSample (Support.triadicLatticePoint n v) omega) ^ 2)
          (((Annealed.sigmaBar M m : ℝ) *
            (Annealed.sigmaBar M (n - 2) : ℝ)⁻¹ - 1) ^ 2)
          (((3 : ℝ) ^ (-(M.gamma * (n : ℝ))) *
            Cutoff.localCubeControl n
              (ShellField.translate (Support.triadicLatticePoint n v)
                (Provider.Stream.shellIncrement omega.1 (n - 2) m))) ^ 2)
          (((3 : ℝ) ^ ((2 - M.gamma) * (n : ℝ)) *
            Support.shellW1InfGradNorm n
              (ShellField.translate (Support.triadicLatticePoint n v)
                (Provider.Stream.shellIncrement omega.1 (n - 2) L))) ^ 2)
          (((3 : ℝ) ^ ((2 - M.gamma) * (m : ℝ)) *
            Support.shellW1InfGradNorm m
              (Provider.Stream.shellIncrement omega.1 m L)) ^ 2)
          (Disorder.cstar M) M.gamma
          ((3 : ℝ) ^ (s * ((m : ℝ) - (n : ℝ))))
          ((3 : ℝ) ^ ((s + M.gamma) * ((m : ℝ) - (n : ℝ)))) C := by
  have : NeZero d := ⟨by omega⟩
  obtain ⟨Cs, hCs, hchain⟩ := exists_responseJ_ugly_estimate_of_grad_le d dimension
  refine ⟨Cs, hCs, ?_⟩
  intro M m n L v e omega s kap Cl Cr Ash C hnm hml hv hs0 hs14 hsgam he hAsh
    hkap0 hkap hsigmlow hsignlow hlam hshell hratio hC
  have hle : n - 2 ≤ L := by omega
  have hnmR : ((n : ℝ) ≤ (m : ℝ)) := by exact_mod_cast hnm
  have hGn0 : (0 : ℝ) ≤ Support.shellW1InfGradNorm n
      (ShellField.translate (Support.triadicLatticePoint n v)
        (Provider.Stream.shellIncrement omega.1 (n - 2) L)) :=
    Support.shellW1InfGradNorm_nonneg n _
  have key := hchain M m n
    (unitRescaledCutoffCoeff M (⟨n, v⟩ : TriadicCube d) (n - 2) omega)
    (centeredShellUnitCube M (⟨n, v⟩ : TriadicCube d) hle omega
      (Support.fluxIncrementAverage M L m (originCube d m) omega)
      (matTranspose_fluxIncrementAverage M L m (originCube d m) omega))
    e s kap Cl Cr (centeringConst d) Ash C
    (Support.shellW1InfGradNorm n
      (ShellField.translate (Support.triadicLatticePoint n v)
        (Provider.Stream.shellIncrement omega.1 (n - 2) L)))
    (Support.shellW1InfGradNorm m (Provider.Stream.shellIncrement omega.1 m L))
    (Cutoff.localCubeControl n
      (ShellField.translate (Support.triadicLatticePoint n v)
        (Provider.Stream.shellIncrement omega.1 (n - 2) m)))
    hs0 hs14 hsgam he hnmR hAsh hGn0 hkap0 hkap hsigmlow hsignlow hlam hshell
    hratio
    (gradientW1Infinity_centeredShellUnitCube_le_lowScale_sub_two M n v hle omega _ _)
    ?_ hC
  · rw [responseJ_fluxCorrectedConst_lattice_eq_perturbCoeffOn M n v hle m _ _ omega,
      ← unitCubeHomogenizationError22_unitRescaledCutoffCoeff_eq_annularErrorAtom
        M n v s omega]
    exact key
  · have hval := valueL2_sq_centeredShellUnitCube_le M hnm hml hle hv omega
    have hcast : ((3 : ℝ) ^ (2 * m) : ℝ) = (3 : ℝ) ^ (2 * (m : ℝ)) := by
      rw [show 2 * ((m : ℤ) : ℝ) = (((2 * m : ℤ)) : ℝ) from by push_cast; ring,
        Real.rpow_intCast]
    rw [hcast] at hval
    exact hval

end

end Algsuperdiff.Section4.Provider.Annular
