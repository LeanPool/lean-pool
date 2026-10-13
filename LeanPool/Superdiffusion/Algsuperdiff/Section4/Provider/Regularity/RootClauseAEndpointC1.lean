/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Support.ClassicalGradient
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.RootClauseBFinalAssembly
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.RootInterfaceMerge

/-!
# RootClauseAEndpointC1

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


namespace Algsuperdiff.Section4.Provider.Regularity

open HCPolySupport MeasureTheory
open Algsuperdiff.Section3
open Algsuperdiff.Section4.Provider.ExcessDecay
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The boundary half of clause (A) at the frozen binder block -/

/-- **Clause (A) of the a.e. lattice display at the boundary centres, frozen
binders.**

`RootClauseABoundary.RootDisplayClauseABoundaryAe`'s body, character for
character, with the root's two printed datum binders — the scale-weighted sup
bound on `∇h` and the classical `C¹` tie `Support.HasGradientOn` — inserted in
the root's own order. -/
def RootDisplayClauseABoundaryC1Ae (M : ABKModel d) (C1 Cest alpha : ℝ) : Prop :=
  ∀ m : ℤ,
    ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      ∀ n : ℤ, n ≤ m →
        RootWindowPayload M C1 alpha n m omega →
          ∀ L : ℤ, m ≤ L →
            ∀ (u h : H1Function (openCubeSet (originCube d m)))
              (g : Vec d → Vec d) (Kg Kh : ℝ),
              Support.IsDirichletSolutionOn
                  (Cutoff.coefficientCutoff M.nu L omega).toCoeffField
                  (originCube d m) u h g →
              Support.HolderSeminormBoundOn (openCubeSet (originCube d m))
                  (1 / 2) Kg g →
              Support.HolderSeminormBoundOn (openCubeSet (originCube d m))
                  (1 / 2) Kh h.grad →
              (∀ y ∈ openCubeSet (originCube d m),
                ‖h.grad y‖ ≤ Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh) →
              Support.HasGradientOn (openCubeSet (originCube d m)) h.toFun h.grad →
              ∀ x : Vec d, x ∈ openCubeSet (originCube d m) →
                (offGridCentre n x ∉ openCubeSet (originCube d (m - 1)) →
                  Real.sqrt M.nu *
                      Support.normalizedL2On
                        (truncatedWindow (offGridCentre n x) m (n + 1))
                        (fun y => Real.sqrt (vecNormSq (u.grad y)))
                    ≤ Cest * Real.rpow (3 : ℝ) ((1 - alpha) * ((m : ℝ) - (n : ℝ))) *
                      (Real.sqrt M.nu *
                          Support.normalizedL2On (openCubeSet (originCube d m))
                            (fun y => Real.sqrt (vecNormSq (u.grad y)))
                        + Real.sqrt (Annealed.sigmaBar M m : ℝ)⁻¹ *
                            Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kg
                        + Real.sqrt (Annealed.sigmaBar M m : ℝ) *
                            Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh))

/-- The printed Hölder binder on `□_m` forces its constant nonnegative: `□_m` has
two distinct points. -/
private theorem holderHalfConst_nonneg_c1 [NeZero d] {m : ℤ} {K : ℝ}
    {E : Type*} [NormedAddCommGroup E] {f : Vec d → E}
    (hK : Support.HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) K f) :
    (0 : ℝ) ≤ K := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ m := zpow_pos (by norm_num) m
  have hx0 : (0 : Vec d) ∈ openCubeSet (originCube d m) := by
    rw [mem_openCubeSet_originCube_iff]
    intro i
    show (-(1 / 2 : ℝ)) * (3 : ℝ) ^ m < (0 : ℝ) ∧ (0 : ℝ) < (1 / 2 : ℝ) * (3 : ℝ) ^ m
    exact ⟨by linarith only [h3], by linarith only [h3]⟩
  have hy0 : (fun _ => (1 / 4 : ℝ) * (3 : ℝ) ^ m : Vec d) ∈
      openCubeSet (originCube d m) := by
    rw [mem_openCubeSet_originCube_iff]
    exact fun _ => ⟨by linarith only [h3], by linarith only [h3]⟩
  refine hK.nonneg hx0 hy0 ?_
  intro hEq
  have hi := congrFun hEq (⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩ : Fin d)
  simp only [Pi.zero_apply] at hi
  linarith only [hi, h3]

theorem RootDisplayClauseABoundaryC1Ae.mono_const [NeZero d] {M : ABKModel d}
    {C1 Cest Cest' alpha : ℝ} (hle : Cest ≤ Cest')
    (h : RootDisplayClauseABoundaryC1Ae M C1 Cest alpha) :
    RootDisplayClauseABoundaryC1Ae M C1 Cest' alpha := by
  intro m
  filter_upwards [h m] with omega h'
  intro n hn hpay L hL u hdat g Kg Kh hdir hKg hKh hsup hgradh x hx hout
  have hbase := h' n hn hpay L hL u hdat g Kg Kh hdir hKg hKh hsup hgradh x hx hout
  have hB0 : (0 : ℝ) ≤ Real.sqrt M.nu *
        Support.normalizedL2On (openCubeSet (originCube d m))
          (fun y => Real.sqrt (vecNormSq (u.grad y)))
      + Real.sqrt (Annealed.sigmaBar M m : ℝ)⁻¹ *
          Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kg
      + Real.sqrt (Annealed.sigmaBar M m : ℝ) *
          Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh := by
    have hL2 : (0 : ℝ) ≤ Real.sqrt M.nu *
        Support.normalizedL2On (openCubeSet (originCube d m))
          (fun y => Real.sqrt (vecNormSq (u.grad y))) :=
      mul_nonneg (Real.sqrt_nonneg _) (Support.normalizedL2On_nonneg _ _)
    have h3 : (0 : ℝ) ≤ Real.rpow (3 : ℝ) ((m : ℝ) / 2) :=
      Real.rpow_nonneg (by norm_num) _
    have hKg0 : (0 : ℝ) ≤ Kg := holderHalfConst_nonneg_c1 hKg
    have hKh0 : (0 : ℝ) ≤ Kh := holderHalfConst_nonneg_c1 hKh
    have hGleg : (0 : ℝ) ≤ Real.sqrt (Annealed.sigmaBar M m : ℝ)⁻¹ *
        Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kg :=
      mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) h3) hKg0
    have hHleg : (0 : ℝ) ≤ Real.sqrt (Annealed.sigmaBar M m : ℝ) *
        Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh :=
      mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) h3) hKh0
    linarith only [hL2, hGleg, hHleg]
  have hrpow : (0 : ℝ) ≤ Real.rpow (3 : ℝ) ((1 - alpha) * ((m : ℝ) - (n : ℝ))) :=
    Real.rpow_nonneg (by norm_num) _
  exact le_trans hbase
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hle hrpow) hB0)

end

end Algsuperdiff.Section4.Provider.Regularity
