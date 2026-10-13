/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Annular.SigmaBarBudget

/-!
# FinalStitch

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The `huglyf` slot of clause (i), at the honest frozen event

ABK26, Section 4.1, `p.mathcalE.annular.decomp` Step 2.
`UglyLatticeChain.exists_uglyJEstimate_lattice_cube` delivers
`e.ugly.estimate.for.J` at one lattice cube `3^n v + □_n` and one unit loading
`e`, under seventeen caller obligations.  This module composes it into the
`huglyf` binder of `ClauseOne.clauseOne_bound` — at the annulus maximum over
`v`, at the *supremum* over `e` (so that the family matches
`AssemblyFeed.jLegField`, which is the carrier the `hpref` slot compares
against), and with fifteen of the seventeen obligations discharged from proved
material and from membership in the honest clause-(i) event

```
𝒢₁(m; s, √c⋆ γ^{−1/2}) .
```

## What remains, and why

Two obligations are **not** discharged, and are carried as explicitly named
hypotheses.  Neither is a proof step migrated into a hypothesis: both are
displays the manuscript itself asserts.

* It is carried as a hypothesis *here* only to keep this module's dependencies
  at the lattice chain: `LambdaBudget` it from `𝒢₀(m)` and the induction state,
  at the explicit constant `8(1+9^d)(1+C_cg)`, and `LambdaDischarge` discharges
  the endpoint's slot outright.  The binder is stated at the annulus index
  family `Support.latticeAnnulusSet d n m n` — the manuscript's own indexing,
  and a strictly weaker hypothesis than the whole `Support.latticeCubeSet d n
  m`.  See `LambdaBudget`'s module docstring for the exact uncovered class.
* `hsignlow` — `¼ κ 3^{γn} ≤ σ_{n−2}` (at the relaxed constant).  See the
  discussion in `SigmaBarBudget`: the induction state gives the printed `½`
  only with `3^{γ(n−2)}`, i.e. short by the factor `3^{2γ}`, so `¼` is what the
  material supports.  It is carried as a hypothesis *here* only to keep this
  module's dependencies at the lattice chain; `SignLowDischarge` discharges it
  outright from the induction state.

Everything else — the two `𝒢₁` budgets, the `σ` ratio, the `σ_m` lower bound,
the `κ` normalization, the tail summability, the typing data and the constant
inequality — is discharged here, at the explicit constants
`A_sh = 196`, `C_r = 4`.
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

/-! ## Part A -- the two annulus families -/

/-- **The `Jannf` family of the clause-(i) composite at the manuscript's own
objects**: the annulus maximum, over the scale-`n` lattice cubes of
`□_j ∖ □_{j−1}`, of the scalar response maximum of `ã_{L,m}`.

This is the same carrier shape as `AssemblyFeed.jLegField` (a lattice maximum of
`scalarResponseMax`), which is what makes the `hpref` slot
`IsAnnularDecompPre s m (jLegField …) (annularResponseMax …) C₁` a comparison of
like with like. -/
def annularResponseMax (M : ABKModel d) (L m : ℤ) (omega : Cutoff.CutoffSample d)
    (j n : ℤ) : ℝ :=
  Proportion.fmax (Proportion.latticeAnnulusFinset d n j (j - 1)) fun v =>
    scalarResponseMax
      ((subConstCutoffTriadicCoeffFamily M L
        (Support.fluxIncrementAverage M L m (originCube d m) omega)
        (matTranspose_fluxIncrementAverage M L m (originCube d m) omega)
        omega).coeffOn (⟨n, v⟩ : TriadicCube d))
      (Annealed.sigmaBar M m)

/-- The family at the **literal** `(2,2)` annular error atom, i.e. the manuscript
quantity rather than the measurable representative.  The two agree almost
surely (`Support.annularErrorAtom_ae_eq_annularErrorObservable`); the literal
family is what the pointwise chain produces. -/
def annularErrorAtomMax [NeZero d] (M : ABKModel d) (s : ℝ)
    (omega : Cutoff.CutoffSample d) (j n : ℤ) : ℝ :=
  Proportion.fmax (Proportion.latticeAnnulusFinset d n j (j - 1)) fun v =>
    Support.annularErrorAtom M n s
      (Cutoff.translateCutoffSample (Support.triadicLatticePoint n v) omega) ^ 2

private abbrev annularResponse_uniformDirectionBound_statement : Prop :=
    ∀ (d : ℕ) (_ : (2 : ℕ) ≤ d) (_ : NeZero d) (Cs : ℝ)
      (_ :
        ∀ (M : ABKModel d) (m n L : ℤ) (v : Fin d → ℤ) (e : Vec d) (omega : Cutoff.CutoffSample d) (s kap Cl Cr Ash C : ℝ),
          n ≤ m →
            m ≤ L →
              v ∈ Support.latticeCubeSet d n m →
                (0 : ℝ) < s →
                  s ≤ (1 / 4 : ℝ) →
                    (8 : ℝ) * M.gamma ≤ s →
                      vecNorm e = (1 : ℝ) →
                        (0 : ℝ) ≤ Ash →
                          (0 : ℝ) < kap →
                            M.gamma * kap ^ (2 : ℕ) = Disorder.cstar M →
                              (1 / 2 : ℝ) * (kap * (3 : ℝ) ^ (M.gamma * (↑m : ℝ))) ≤ (↑(Annealed.sigmaBar M m) : ℝ) →
                                (1 / 4 : ℝ) * (kap * (3 : ℝ) ^ (M.gamma * (↑n : ℝ))) ≤
                                    (↑(Annealed.sigmaBar M (n - (2 : ℤ))) : ℝ) →
                                  (↑(Annealed.sigmaBar M (n - (2 : ℤ))) : ℝ) *
                                        (unitCubeLambda ((2 : ℝ) * M.gamma) (Ch02.MultiscaleExponent.finite (2 : ℝ))
                                            (unitRescaledCutoffCoeff M { scale := n, index := v } (n - (2 : ℤ)) omega))⁻¹ ≤
                                      Cl * (3 : ℝ) ^ (M.gamma * ((↑m : ℝ) - (↑n : ℝ))) →
                                    (↑(Annealed.sigmaBar M (n - (2 : ℤ))) : ℝ)⁻¹ *
                                          ((3 : ℝ) ^ ((2 : ℝ) * (↑n : ℝ)) *
                                            Support.shellW1InfGradNorm n
                                              (ShellField.translate (Support.triadicLatticePoint n v)
                                                (Provider.Stream.shellIncrement (↑omega : Cutoff.ShellSeq d) (n - (2 : ℤ))
                                                  L))) ≤
                                        Ash * (3 : ℝ) ^ (s / (4 : ℝ) * ((↑m : ℝ) - (↑n : ℝ))) →
                                      (↑(Annealed.sigmaBar M m) : ℝ)⁻¹ * (↑(Annealed.sigmaBar M (n - (2 : ℤ))) : ℝ) ≤ Cr →
                                        Cs * ((1 : ℝ) + Ash * Cl) ^ (2 : ℕ) * Cr * ((1 : ℝ) + Cl) +
                                                (16 : ℝ) * Cs * ((1 : ℝ) + Ash * Cl) ^ (2 : ℕ) * Cl *
                                                  ((1 : ℝ) + centeringConst d ^ (2 : ℕ)) +
                                              (4 : ℝ) * Cs * ((1 : ℝ) + (4 : ℝ) * Cl ^ (2 : ℕ)) ≤
                                            C →
                                          IsUglyJEstimate
                                            (responseJ (cubeDomain { scale := n, index := v })
                                              ((subConstCutoffTriadicCoeffFamily M L
                                                    (Support.fluxIncrementAverage M L m (originCube d m) omega) (matTranspose_fluxIncrementAverage M L m (originCube d m) omega)
                                                    omega).coeffOn
                                                { scale := n, index := v })
                                              (Observable.inverseSqrtLoad (Annealed.sigmaBar M m) e)
                                              (Observable.sqrtLoad (Annealed.sigmaBar M m) e))
                                            (Support.annularErrorAtom M n s
                                                (Cutoff.translateCutoffSample (Support.triadicLatticePoint n v) omega) ^
                                              (2 : ℕ))
                                            (((↑(Annealed.sigmaBar M m) : ℝ) *
                                                  (↑(Annealed.sigmaBar M (n - (2 : ℤ))) : ℝ)⁻¹ -
                                                (1 : ℝ)) ^
                                              (2 : ℕ))
                                            (((3 : ℝ) ^ (-(M.gamma * (↑n : ℝ))) *
                                                Cutoff.localCubeControl n
                                                  (ShellField.translate (Support.triadicLatticePoint n v)
                                                    (Provider.Stream.shellIncrement (↑omega : Cutoff.ShellSeq d)
                                                      (n - (2 : ℤ)) m))) ^
                                              (2 : ℕ))
                                            (((3 : ℝ) ^ (((2 : ℝ) - M.gamma) * (↑n : ℝ)) *
                                                Support.shellW1InfGradNorm n
                                                  (ShellField.translate (Support.triadicLatticePoint n v)
                                                    (Provider.Stream.shellIncrement (↑omega : Cutoff.ShellSeq d)
                                                      (n - (2 : ℤ)) L))) ^
                                              (2 : ℕ))
                                            (((3 : ℝ) ^ (((2 : ℝ) - M.gamma) * (↑m : ℝ)) *
                                                Support.shellW1InfGradNorm m
                                                  (Provider.Stream.shellIncrement (↑omega : Cutoff.ShellSeq d) m L)) ^
                                              (2 : ℕ))
                                            (Disorder.cstar M) M.gamma ((3 : ℝ) ^ (s * ((↑m : ℝ) - (↑n : ℝ))))
                                            ((3 : ℝ) ^ ((s + M.gamma) * ((↑m : ℝ) - (↑n : ℝ)))) C)
      (M : ABKModel d) (m L m0 : ℤ) (E : { E : ℝ // (1 : ℝ) ≤ E }) (omega : Cutoff.CutoffSample d) (s Cl C : ℝ)
      (_ : Frozen.Section3.inductionState M m0 E) (_ : m ≤ m0) (_ : m ≤ L) (_ : (0 : ℝ) < s) (_ : s ≤ (1 / 4 : ℝ))
      (_ : (8 : ℝ) * M.gamma ≤ s) (_ : omega ∈ Support.eventG1 M m s (√(Disorder.cstar M) * (√M.gamma)⁻¹))
      (_ :
        ∀ (n : ℤ) (v : Fin d → ℤ),
          n ≤ m - (1 : ℤ) →
            v ∈ Support.latticeAnnulusSet d n m n →
              (↑(Annealed.sigmaBar M (n - (2 : ℤ))) : ℝ) *
                  (unitCubeLambda ((2 : ℝ) * M.gamma) (Ch02.MultiscaleExponent.finite (2 : ℝ))
                      (unitRescaledCutoffCoeff M { scale := n, index := v } (n - (2 : ℤ)) omega))⁻¹ ≤
                Cl * (3 : ℝ) ^ (M.gamma * ((↑m : ℝ) - (↑n : ℝ))))
      (_ :
        ∀ n ≤ m - (1 : ℤ),
          (1 / 4 : ℝ) * (√(Disorder.cstar M) * (√M.gamma)⁻¹ * (3 : ℝ) ^ (M.gamma * (↑n : ℝ))) ≤
            (↑(Annealed.sigmaBar M (n - (2 : ℤ))) : ℝ))
      (_ :
        Cs * ((1 : ℝ) + (196 : ℝ) * Cl) ^ (2 : ℕ) * (4 : ℝ) * ((1 : ℝ) + Cl) +
              (16 : ℝ) * Cs * ((1 : ℝ) + (196 : ℝ) * Cl) ^ (2 : ℕ) * Cl * ((1 : ℝ) + centeringConst d ^ (2 : ℕ)) +
            (4 : ℝ) * Cs * ((1 : ℝ) + (4 : ℝ) * Cl ^ (2 : ℕ)) ≤
          C)
      (j n : ℤ) (_ : j ≤ m) (_ : n ≤ j - (1 : ℤ)) (_ : (0 : ℝ) < M.gamma) (_ : (0 : ℝ) ≤ (Disorder.cstar M)⁻¹)
      (_ : n ≤ m) (_ : n ≤ m - (1 : ℤ)) (_ : (0 : ℝ) ≤ C) (_ : (0 : ℝ) < √(Disorder.cstar M) * (√M.gamma)⁻¹)
      (_ : M.gamma * (√(Disorder.cstar M) * (√M.gamma)⁻¹) ^ (2 : ℕ) = Disorder.cstar M)
      (_ :
        (1 / 2 : ℝ) * (√(Disorder.cstar M) * (√M.gamma)⁻¹ * (3 : ℝ) ^ (M.gamma * (↑m : ℝ))) ≤
          (↑(Annealed.sigmaBar M m) : ℝ))
      (_ : (↑(Annealed.sigmaBar M m) : ℝ)⁻¹ * (↑(Annealed.sigmaBar M (n - (2 : ℤ))) : ℝ) ≤ (4 : ℝ))
      (_ : (0 : ℝ) ≤ (3 : ℝ) ^ (s * ((↑m : ℝ) - (↑n : ℝ))))
      (_ : (0 : ℝ) ≤ (3 : ℝ) ^ ((s + M.gamma) * ((↑m : ℝ) - (↑n : ℝ))))
      (_ :
        ((3 : ℝ) ^ (((2 : ℝ) - M.gamma) * (↑m : ℝ)) *
              Support.shellW1InfGradNorm m (Provider.Stream.shellIncrement (↑omega : Cutoff.ShellSeq d) m L)) ^
            (2 : ℕ) ≤
          gradTailSq M m omega),
      ∀ v ∈ Proportion.latticeAnnulusFinset d n j (j - (1 : ℤ)),
        ∀ (e : Vec d),
          vecNorm e = (1 : ℝ) →
            IsUglyJEstimate
              (responseJ (cubeDomain { scale := n, index := v })
                ((subConstCutoffTriadicCoeffFamily M L (Support.fluxIncrementAverage M L m (originCube d m) omega) (matTranspose_fluxIncrementAverage M L m (originCube d m) omega)
                      omega).coeffOn
                  { scale := n, index := v })
                (Observable.inverseSqrtLoad (Annealed.sigmaBar M m) e) (Observable.sqrtLoad (Annealed.sigmaBar M m) e))
              (annularErrorAtomMax M s omega j n)
              (((↑(Annealed.sigmaBar M m) : ℝ) * (↑(Annealed.sigmaBar M (n - (2 : ℤ))) : ℝ)⁻¹ - (1 : ℝ)) ^ (2 : ℕ))
              (annularL2Block M m omega j n) ((2 : ℝ) * annularGradBlock M m omega j n + (2 : ℝ) * gradTailSq M m omega)
              (gradTailSq M m omega) (Disorder.cstar M) M.gamma ((3 : ℝ) ^ (s * ((↑m : ℝ) - (↑n : ℝ))))
              ((3 : ℝ) ^ ((s + M.gamma) * ((↑m : ℝ) - (↑n : ℝ)))) C

/-- The lattice point of index `0` is the origin. -/
private theorem triadicLatticePoint_zero (m : ℤ) :
    Support.triadicLatticePoint m (0 : Fin d → ℤ) = (0 : Vec d) := by
  funext i
  change (3 : ℝ) ^ m * (((0 : Fin d → ℤ) i : ℤ) : ℝ) = 0
  norm_num

theorem annularResponseMax_nonneg (M : ABKModel d) (L m : ℤ)
    (omega : Cutoff.CutoffSample d) (j n : ℤ) :
    0 ≤ annularResponseMax M L m omega j n :=
  Proportion.fmax_nonneg _ _

private theorem annularTranslatedGradient_squareBound :
    ∀ (d : ℕ) (M : ABKModel d) (m L : ℤ)
      (omega : Cutoff.CutoffSample d) (j n : ℤ) (v : Fin d → ℤ)
      (_ :
        Support.shellW1InfGradNorm n
            (ShellField.translate (Support.triadicLatticePoint n v)
              (Provider.Stream.shellIncrement (↑omega : Cutoff.ShellSeq d) (n - (2 : ℤ)) L)) ≤
          Support.shellW1InfGradNorm n
              (ShellField.translate (Support.triadicLatticePoint n v)
                (Provider.Stream.shellIncrement (↑omega : Cutoff.ShellSeq d) (n - (2 : ℤ)) m)) +
            Support.shellW1InfGradNorm n
              (ShellField.translate (Support.triadicLatticePoint n v)
                (Provider.Stream.shellIncrement (↑omega : Cutoff.ShellSeq d) m L)))
      (_ :
        ((3 : ℝ) ^ (((2 : ℝ) - M.gamma) * (↑n : ℝ)) *
              Support.shellW1InfGradNorm n
                (ShellField.translate (Support.triadicLatticePoint n v)
                  (Provider.Stream.shellIncrement (↑omega : Cutoff.ShellSeq d) (n - (2 : ℤ)) m))) ^
            (2 : ℕ) ≤
          annularGradBlock M m omega j n)
      (_ :
        ((3 : ℝ) ^ (((2 : ℝ) - M.gamma) * (↑n : ℝ)) *
              Support.shellW1InfGradNorm n
                (ShellField.translate (Support.triadicLatticePoint n v)
                  (Provider.Stream.shellIncrement (↑omega : Cutoff.ShellSeq d) m L))) ^
            (2 : ℕ) ≤
          gradTailSq M m omega),
      ((3 : ℝ) ^ (((2 : ℝ) - M.gamma) * (↑n : ℝ)) *
            Support.shellW1InfGradNorm n
              (ShellField.translate (Support.triadicLatticePoint n v)
                (Provider.Stream.shellIncrement (↑omega : Cutoff.ShellSeq d) (n - (2 : ℤ)) L))) ^
          (2 : ℕ) ≤
        (2 : ℝ) * annularGradBlock M m omega j n + (2 : ℝ) * gradTailSq M m omega := by
  intro _ M m L omega _ n v hsplit hXsq hYsq
  have hstep : (3 : ℝ) ^ ((2 - M.gamma) * (n : ℝ)) *
      Support.shellW1InfGradNorm n
        (ShellField.translate (Support.triadicLatticePoint n v)
          (Provider.Stream.shellIncrement omega.1 (n - 2) L))
      ≤ (3 : ℝ) ^ ((2 - M.gamma) * (n : ℝ)) *
          Support.shellW1InfGradNorm n
            (ShellField.translate (Support.triadicLatticePoint n v)
              (Provider.Stream.shellIncrement omega.1 (n - 2) m))
        + (3 : ℝ) ^ ((2 - M.gamma) * (n : ℝ)) *
          Support.shellW1InfGradNorm n
            (ShellField.translate (Support.triadicLatticePoint n v)
              (Provider.Stream.shellIncrement omega.1 m L)) := by
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left hsplit (Real.rpow_nonneg (by norm_num) _)
  have hsq := pow_le_pow_left₀ (mul_nonneg (Real.rpow_nonneg (by norm_num) _)
    (Support.shellW1InfGradNorm_nonneg n _)) hstep 2
  have hxy : ((3 : ℝ) ^ ((2 - M.gamma) * (n : ℝ)) *
        Support.shellW1InfGradNorm n
          (ShellField.translate (Support.triadicLatticePoint n v)
            (Provider.Stream.shellIncrement omega.1 (n - 2) m))
      + (3 : ℝ) ^ ((2 - M.gamma) * (n : ℝ)) *
        Support.shellW1InfGradNorm n
          (ShellField.translate (Support.triadicLatticePoint n v)
            (Provider.Stream.shellIncrement omega.1 m L))) ^ 2
      ≤ 2 * ((3 : ℝ) ^ ((2 - M.gamma) * (n : ℝ)) *
          Support.shellW1InfGradNorm n
            (ShellField.translate (Support.triadicLatticePoint n v)
              (Provider.Stream.shellIncrement omega.1 (n - 2) m))) ^ 2
        + 2 * ((3 : ℝ) ^ ((2 - M.gamma) * (n : ℝ)) *
          Support.shellW1InfGradNorm n
            (ShellField.translate (Support.triadicLatticePoint n v)
              (Provider.Stream.shellIncrement omega.1 m L))) ^ 2 := by
    linarith only [sq_nonneg ((3 : ℝ) ^ ((2 - M.gamma) * (n : ℝ)) *
      Support.shellW1InfGradNorm n
        (ShellField.translate (Support.triadicLatticePoint n v)
          (Provider.Stream.shellIncrement omega.1 (n - 2) m))
      - (3 : ℝ) ^ ((2 - M.gamma) * (n : ℝ)) *
        Support.shellW1InfGradNorm n
          (ShellField.translate (Support.triadicLatticePoint n v)
            (Provider.Stream.shellIncrement omega.1 m L)))]
  linarith only [hsq, hxy, hXsq, hYsq]

theorem annularErrorAtomMax_nonneg [NeZero d] (M : ABKModel d) (s : ℝ)
    (omega : Cutoff.CutoffSample d) (j n : ℤ) :
    0 ≤ annularErrorAtomMax M s omega j n :=
  Proportion.fmax_nonneg _ _

/-! ## Part B -- the `huglyf` binder -/

private theorem annularResponse_uniformDirectionBound : annularResponse_uniformDirectionBound_statement := by
  intro d _ _ _ hchain M m L m0 _ omega s Cl C hS _ hmL hs0 hs14 hsgam homega hlam hsignlow hC j n hjm _ hgam0 hcsinv hnm hnm1 hC0 hkap0 hkap hsigm hratio hw0 hwg0 h5 v hv e he
  have hvset : v ∈ Support.latticeAnnulusSet d n j (j - 1) :=
    (Proportion.mem_latticeAnnulusFinset_iff (by omega)).mp hv
  have hvcube : v ∈ Support.latticeCubeSet d n m :=
    openCubeSet_originCube_subset hjm hvset.1
  have hvout : Support.triadicLatticePoint n v ∉ openCubeSet (originCube d n) :=
    fun hx => hvset.2 (openCubeSet_originCube_subset (by omega : n ≤ j - 1) hx)
  have hshell := shellBudget_of_eventG1_of_inductionState M hS m hs0.le
    (by linarith only [hs14]) homega hnm hmL (by omega : n - 2 ≤ m0) hvcube
  have hchainv := hchain M m n L v e omega s
    (Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹) Cl 4 196 C hnm hmL
    hvcube hs0 hs14 hsgam he (by norm_num) hkap0 hkap hsigm (hsignlow n hnm1)
    (hlam n v hnm1 ⟨hvcube, hvout⟩) hshell hratio hC
  -- the `(2,2)` slot
  have hE2 : Support.annularErrorAtom M n s
      (Cutoff.translateCutoffSample (Support.triadicLatticePoint n v) omega) ^ 2
      ≤ annularErrorAtomMax M s omega j n := by
    rw [annularErrorAtomMax]
    exact Proportion.le_fmax
      (f := fun w => Support.annularErrorAtom M n s
        (Cutoff.translateCutoffSample (Support.triadicLatticePoint n w) omega) ^ 2)
      hv
  -- the value slot
  have hL2 : ((3 : ℝ) ^ (-(M.gamma * (n : ℝ))) *
      Cutoff.localCubeControl n
        (ShellField.translate (Support.triadicLatticePoint n v)
          (Provider.Stream.shellIncrement omega.1 (n - 2) m))) ^ 2
      ≤ annularL2Block M m omega j n := by
    rw [annularL2Block]
    refine pow_le_pow_left₀ (mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (Cutoff.localCubeControl_nonneg n _)) ?_ 2
    exact mul_le_mul_of_nonneg_left
      (Proportion.le_fmax
        (f := fun w => Cutoff.localCubeControl n
          (ShellField.translate (Support.triadicLatticePoint n w)
            (Provider.Stream.shellIncrement omega.1 (n - 2) m))) hv)
      (Real.rpow_nonneg (by norm_num) _)
  -- the fourth (`gradN`) slot: the head/tail split
  have hsplit := shellW1InfGradNorm_translate_shellIncrement_add_le n v omega.1
    (by omega : n - 2 ≤ m) hmL
  have hX0 : (0 : ℝ) ≤ (3 : ℝ) ^ ((2 - M.gamma) * (n : ℝ)) *
      Support.shellW1InfGradNorm n
        (ShellField.translate (Support.triadicLatticePoint n v)
          (Provider.Stream.shellIncrement omega.1 (n - 2) m)) :=
    mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (Support.shellW1InfGradNorm_nonneg n _)
  have hY0 : (0 : ℝ) ≤ (3 : ℝ) ^ ((2 - M.gamma) * (n : ℝ)) *
      Support.shellW1InfGradNorm n
        (ShellField.translate (Support.triadicLatticePoint n v)
          (Provider.Stream.shellIncrement omega.1 m L)) :=
    mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (Support.shellW1InfGradNorm_nonneg n _)
  have hXsq : ((3 : ℝ) ^ ((2 - M.gamma) * (n : ℝ)) *
      Support.shellW1InfGradNorm n
        (ShellField.translate (Support.triadicLatticePoint n v)
          (Provider.Stream.shellIncrement omega.1 (n - 2) m))) ^ 2
      ≤ annularGradBlock M m omega j n := by
    rw [annularGradBlock]
    refine pow_le_pow_left₀ hX0 ?_ 2
    refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (by norm_num) _)
    exact Proportion.le_fmax
      (f := fun w => Support.shellW1InfGradNorm n
        (ShellField.translate (Support.triadicLatticePoint n w)
          (Provider.Stream.shellIncrement omega.1 (n - 2) m))) hv
  have hYsq : ((3 : ℝ) ^ ((2 - M.gamma) * (n : ℝ)) *
      Support.shellW1InfGradNorm n
        (ShellField.translate (Support.triadicLatticePoint n v)
          (Provider.Stream.shellIncrement omega.1 m L))) ^ 2
      ≤ gradTailSq M m omega := by
    have hle := shellGaugeTail_le_tsum_of_eventG1 M m homega (L := L) hnm hvcube
    exact pow_le_pow_left₀ hY0 hle 2
  have h4 : ((3 : ℝ) ^ ((2 - M.gamma) * (n : ℝ)) *
      Support.shellW1InfGradNorm n
        (ShellField.translate (Support.triadicLatticePoint n v)
          (Provider.Stream.shellIncrement omega.1 (n - 2) L))) ^ 2
      ≤ 2 * annularGradBlock M m omega j n + 2 * gradTailSq M m omega  :=
        @annularTranslatedGradient_squareBound (d) (M) (m) (L) (omega) (j) (n) (v) (hsplit) (hXsq)
          (hYsq)
  refine isUglyJEstimate_mono_E2 hC0 hw0 hE2 ?_
  refine isUglyJEstimate_mono_L2 hC0 hcsinv hgam0.le hw0 hL2 ?_
  refine isUglyJEstimate_mono_gradN hC0 hcsinv hgam0.le hw0 h4 ?_
  exact isUglyJEstimate_mono_gradM hC0 hcsinv hgam0.le hwg0 h5 hchainv

/-- **`e.ugly.estimate.for.J` at the annulus, on the honest clause-(i) event.**

Of the seventeen obligations of `exists_uglyJEstimate_lattice_cube`, fifteen
are discharged inside: `n ≤ m`, `m ≤ L`, the lattice membership, `0 < s`, `s ≤
1/4`, `8γ ≤ s`, `‖e‖ = 1`, `0 ≤ A_sh`, `0 < κ`, `γκ² = c⋆`, `hsigmlow`,
`hshell`, `hratio`, the tail summability, and the constant inequality.  The two
that remain are `hlam` and `hsignlow` (at the relaxed
constant `¼`, discharged in `SignLowDischarge`); see the module docstring. -/
theorem exists_uglyJEstimate_annulus_of_eventG1 (d : ℕ) (dimension : 2 ≤ d) :
    letI : NeZero d := ⟨by omega⟩
    ∃ Cs : ℝ, 0 < Cs ∧
      ∀ (M : ABKModel d) (m L m0 : ℤ) (E : {E : ℝ // 1 ≤ E})
        (omega : Cutoff.CutoffSample d) (s Cl C : ℝ),
        Algsuperdiff.Frozen.Section3.inductionState M m0 E → m ≤ m0 → m ≤ L →
        0 < s → s ≤ 1 / 4 → 8 * M.gamma ≤ s →
        omega ∈ Support.eventG1 M m s
          (Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹) →
        0 ≤ Cl →
        (∀ (n : ℤ) (v : Fin d → ℤ), n ≤ m - 1 →
          v ∈ Support.latticeAnnulusSet d n m n →
          (Annealed.sigmaBar M (n - 2) : ℝ) *
              (unitCubeLambda (2 * M.gamma) (.finite 2)
                (unitRescaledCutoffCoeff M (⟨n, v⟩ : TriadicCube d) (n - 2) omega))⁻¹ ≤
            Cl * (3 : ℝ) ^ (M.gamma * ((m : ℝ) - (n : ℝ)))) →
        (∀ n : ℤ, n ≤ m - 1 →
          1 / 4 * ((Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹)
              * (3 : ℝ) ^ (M.gamma * (n : ℝ)))
            ≤ (Annealed.sigmaBar M (n - 2) : ℝ)) →
        Cs * (1 + 196 * Cl) ^ 2 * 4 * (1 + Cl)
            + 16 * Cs * (1 + 196 * Cl) ^ 2 * Cl * (1 + centeringConst d ^ 2)
            + 4 * Cs * (1 + 4 * Cl ^ 2) ≤ C →
        ∀ j n : ℤ, j ≤ m → n ≤ j - 1 →
          IsUglyJEstimate (annularResponseMax M L m omega j n)
            (annularErrorAtomMax M s omega j n)
            (((Annealed.sigmaBar M m : ℝ) *
              (Annealed.sigmaBar M (n - 2) : ℝ)⁻¹ - 1) ^ 2)
            (annularL2Block M m omega j n)
            (2 * annularGradBlock M m omega j n + 2 * gradTailSq M m omega)
            (gradTailSq M m omega) (Disorder.cstar M) M.gamma
            ((3 : ℝ) ^ (s * ((m - n : ℤ) : ℝ)))
            ((3 : ℝ) ^ ((s + M.gamma) * ((m - n : ℤ) : ℝ))) C := by
  have : NeZero d := ⟨by omega⟩
  obtain ⟨Cs, hCs, hchain⟩ := exists_uglyJEstimate_lattice_cube d dimension
  refine ⟨Cs, hCs, ?_⟩
  intro M m L m0 E omega s Cl C hS hm0 hmL hs0 hs14 hsgam homega hCl hlam hsignlow
    hC j n hjm hnj
  classical
  have hgam0 : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hcs0 : (0 : ℝ) < Disorder.cstar M := (Disorder.cstar_characterization M).1
  have hcsinv : (0 : ℝ) ≤ (Disorder.cstar M)⁻¹ := inv_nonneg.2 hcs0.le
  have hnm : n ≤ m := by omega
  have hnm1 : n ≤ m - 1 := by omega
  have hcast : ((m - n : ℤ) : ℝ) = (m : ℝ) - (n : ℝ) := by push_cast; ring
  -- the output constant is nonnegative
  have hCl1 : (0 : ℝ) ≤ 1 + Cl := by linarith only [hCl]
  have ht1 : (0 : ℝ) ≤ Cs * (1 + 196 * Cl) ^ 2 * 4 * (1 + Cl) :=
    mul_nonneg (mul_nonneg (mul_nonneg hCs.le (sq_nonneg _)) (by norm_num)) hCl1
  have ht2 : (0 : ℝ) ≤ 16 * Cs * (1 + 196 * Cl) ^ 2 * Cl
      * (1 + centeringConst d ^ 2) := by
    have hc2 : (0 : ℝ) ≤ 1 + centeringConst d ^ 2 := by
      have := sq_nonneg (centeringConst d)
      linarith only [this]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by linarith only [hCs]) (sq_nonneg _))
      hCl) hc2
  have ht3 : (0 : ℝ) ≤ 4 * Cs * (1 + 4 * Cl ^ 2) := by
    have hc2 : (0 : ℝ) ≤ 1 + 4 * Cl ^ 2 := by
      have := sq_nonneg Cl
      linarith only [this]
    exact mul_nonneg (by linarith only [hCs]) hc2
  have hC0 : (0 : ℝ) ≤ C := by linarith only [ht1, ht2, ht3, hC]
  -- the `σ` slots
  have hkap0 := annularEventAmplitude_pos M
  have hkap := gamma_mul_annularEventAmplitude_sq M
  have hsigm := sigmaBar_lower_of_inductionState M hS hm0
  have hratio := sigmaBar_ratio_le_four M hS (n := n) (by omega : n - 2 ≤ m) hm0
  -- the weights
  have hw0 : (0 : ℝ) ≤ (3 : ℝ) ^ (s * ((m : ℝ) - (n : ℝ))) :=
    Real.rpow_nonneg (by norm_num) _
  have hwg0 : (0 : ℝ) ≤ (3 : ℝ) ^ ((s + M.gamma) * ((m : ℝ) - (n : ℝ))) :=
    Real.rpow_nonneg (by norm_num) _
  -- the fifth (`gradM`) slot
  have h5 : ((3 : ℝ) ^ ((2 - M.gamma) * (m : ℝ)) *
      Support.shellW1InfGradNorm m (Provider.Stream.shellIncrement omega.1 m L)) ^ 2
      ≤ gradTailSq M m omega := by
    have hbase := Support.shellW1InfGradNorm_translate_shellIncrement_le m
      (0 : Fin d → ℤ) omega.1 m L
    rw [triadicLatticePoint_zero m] at hbase
    simp only [shellField_translate_zero] at hbase
    have hstep : (3 : ℝ) ^ ((2 - M.gamma) * (m : ℝ)) *
        Support.shellW1InfGradNorm m (Provider.Stream.shellIncrement omega.1 m L)
        ≤ ∑' k : {k : ℤ // m ≤ k},
            (3 : ℝ) ^ ((2 - M.gamma) * (m : ℝ))
              * Support.shellW1InfGradNorm m (omega.1 k.1) := by
      refine le_trans (mul_le_mul_of_nonneg_left hbase
        (Real.rpow_nonneg (by norm_num) _)) ?_
      exact sum_gradTailFam_Ioc_le_tsum M m homega L
    have hnn : (0 : ℝ) ≤ (3 : ℝ) ^ ((2 - M.gamma) * (m : ℝ)) *
        Support.shellW1InfGradNorm m (Provider.Stream.shellIncrement omega.1 m L) :=
      mul_nonneg (Real.rpow_nonneg (by norm_num) _)
        (Support.shellW1InfGradNorm_nonneg m _)
    exact pow_le_pow_left₀ hnn hstep 2
  -- the per-cube, per-loading estimate
  have key := @annularResponse_uniformDirectionBound (d) (dimension) (this) (Cs) (hchain) (M) (m)
    (L) (m0) (E) (omega) (s) (Cl) (C) (hS) (hm0) (hmL) (hs0) (hs14) (hsgam) (homega) (hlam)
      (hsignlow) (hC) (j) (n) (hjm) (hnj) (hgam0) (hcsinv) (hnm) (hnm1) (hC0) (hkap0) (hkap)
        (hsigm) (hratio) (hw0) (hwg0) (h5)
  -- assemble: the annulus maximum and the loading supremum
  rw [hcast]
  have hRHS0 : (0 : ℝ) ≤
      C * (3 : ℝ) ^ (s * ((m : ℝ) - (n : ℝ))) * annularErrorAtomMax M s omega j n
      + C * (3 : ℝ) ^ (s * ((m : ℝ) - (n : ℝ)))
          * (((Annealed.sigmaBar M m : ℝ) *
            (Annealed.sigmaBar M (n - 2) : ℝ)⁻¹ - 1) ^ 2)
      + C * (Disorder.cstar M)⁻¹ * M.gamma * (3 : ℝ) ^ (s * ((m : ℝ) - (n : ℝ)))
          * annularL2Block M m omega j n
      + C * (Disorder.cstar M)⁻¹ * M.gamma * (3 : ℝ) ^ (s * ((m : ℝ) - (n : ℝ)))
          * (2 * annularGradBlock M m omega j n + 2 * gradTailSq M m omega)
      + C * (Disorder.cstar M)⁻¹ * M.gamma
          * (3 : ℝ) ^ ((s + M.gamma) * ((m : ℝ) - (n : ℝ)))
          * gradTailSq M m omega := by
    have hgN0 : (0 : ℝ) ≤ 2 * annularGradBlock M m omega j n
        + 2 * gradTailSq M m omega := by
      have h1 := annularGradBlock_nonneg M m omega j n
      have h2 := gradTailSq_nonneg M m omega
      linarith only [h1, h2]
    have t1 : (0 : ℝ) ≤ C * (3 : ℝ) ^ (s * ((m : ℝ) - (n : ℝ)))
        * annularErrorAtomMax M s omega j n :=
      mul_nonneg (mul_nonneg hC0 hw0) (annularErrorAtomMax_nonneg M s omega j n)
    have t2 : (0 : ℝ) ≤ C * (3 : ℝ) ^ (s * ((m : ℝ) - (n : ℝ)))
        * (((Annealed.sigmaBar M m : ℝ) *
          (Annealed.sigmaBar M (n - 2) : ℝ)⁻¹ - 1) ^ 2) :=
      mul_nonneg (mul_nonneg hC0 hw0) (sq_nonneg _)
    have t3 : (0 : ℝ) ≤ C * (Disorder.cstar M)⁻¹ * M.gamma
        * (3 : ℝ) ^ (s * ((m : ℝ) - (n : ℝ))) * annularL2Block M m omega j n :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC0 hcsinv) hgam0.le) hw0)
        (annularL2Block_nonneg M m omega j n)
    have t4 : (0 : ℝ) ≤ C * (Disorder.cstar M)⁻¹ * M.gamma
        * (3 : ℝ) ^ (s * ((m : ℝ) - (n : ℝ)))
        * (2 * annularGradBlock M m omega j n + 2 * gradTailSq M m omega) :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC0 hcsinv) hgam0.le) hw0) hgN0
    have t5 : (0 : ℝ) ≤ C * (Disorder.cstar M)⁻¹ * M.gamma
        * (3 : ℝ) ^ ((s + M.gamma) * ((m : ℝ) - (n : ℝ))) * gradTailSq M m omega :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC0 hcsinv) hgam0.le) hwg0)
        (gradTailSq_nonneg M m omega)
    linarith only [t1, t2, t3, t4, t5]
  unfold IsUglyJEstimate
  rw [annularResponseMax]
  refine Proportion.fmax_le hRHS0 ?_
  intro v hv
  rw [scalarResponseMax]
  refine Real.sSup_le ?_ hRHS0
  rintro x ⟨e, he, rfl⟩
  exact key v hv e he

end

end Algsuperdiff.Section4.Provider.Annular
