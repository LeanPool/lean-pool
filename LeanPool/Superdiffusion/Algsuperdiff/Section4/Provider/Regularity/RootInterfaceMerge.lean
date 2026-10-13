/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.RootAssemblyChain
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.RootAssemblyParameters

/-!
# RootInterfaceMerge

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

/-! ## 1.: the `γ₀` min-merge and the threshold merge -/

/-- The left projection of a merged threshold. -/
theorem rootGamma0_le_left {g0 g1 gamma : ℝ} (h : gamma ≤ min g0 g1) : gamma ≤ g0 :=
  le_trans h (min_le_left _ _)

/-- The right projection of a merged threshold. -/
theorem rootGamma0_le_right {g0 g1 gamma : ℝ} (h : gamma ≤ min g0 g1) : gamma ≤ g1 :=
  le_trans h (min_le_right _ _)

/-! ## 3.: the two clauses of the a.e. display -/

/-- **Clause (A) of the a.e. lattice display**: the printed three-leg estimate
printed lattice centre.  The binder prefix and the conjunct body are
`RootInterfaceAe.RootLatticeDisplayAe`'s, character for character. -/
def RootDisplayClauseAAe (M : ABKModel d) (C1 Cest alpha : ℝ) : Prop :=
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
              ∀ x : Vec d, x ∈ openCubeSet (originCube d m) →
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
                          Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh)

/-- **Clause (B) of the a.e. lattice display**: the boundary-leg-free estimate,
gated by `z ∈ □_{m-1}`.  discharged this clause. -/
def RootDisplayClauseBAe (M : ABKModel d) (C1 Cest alpha : ℝ) : Prop :=
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
              ∀ x : Vec d, x ∈ openCubeSet (originCube d m) →
                (offGridCentre n x ∈ openCubeSet (originCube d (m - 1)) →
                  Real.sqrt M.nu *
                      Support.normalizedL2On
                        (truncatedWindow (offGridCentre n x) m (n + 1))
                        (fun y => Real.sqrt (vecNormSq (u.grad y)))
                    ≤ Cest * Real.rpow (3 : ℝ) ((1 - alpha) * ((m : ℝ) - (n : ℝ))) *
                      (Real.sqrt M.nu *
                          Support.normalizedL2On (openCubeSet (originCube d m))
                            (fun y => Real.sqrt (vecNormSq (u.grad y)))
                        + Real.sqrt (Annealed.sigmaBar M m : ℝ)⁻¹ *
                            Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kg))

/-! ## 4., the `C_est` alignment -/

/-- Two distinct points of `□_m`.  Needed only to turn the display's own printed
Hölder binders into the sign facts `0 ≤ K_g`, `0 ≤ K_h` ('s bonus), which is
what makes the display's right-hand bracket nonnegative. -/
private theorem exists_ne_pair_originCube [NeZero d] (m : ℤ) :
    ∃ x y : Vec d, x ∈ openCubeSet (originCube d m) ∧
      y ∈ openCubeSet (originCube d m) ∧ x ≠ y := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ m := zpow_pos (by norm_num) m
  refine ⟨(0 : Vec d), (fun _ => (1 / 4 : ℝ) * (3 : ℝ) ^ m), ?_, ?_, ?_⟩
  · rw [mem_openCubeSet_originCube_iff]
    intro i
    change (-(1 / 2 : ℝ)) * (3 : ℝ) ^ m < (0 : ℝ) ∧ (0 : ℝ) < (1 / 2 : ℝ) * (3 : ℝ) ^ m
    exact ⟨by linarith only [h3], by linarith only [h3]⟩
  · rw [mem_openCubeSet_originCube_iff]
    exact fun _ => ⟨by linarith only [h3], by linarith only [h3]⟩
  · intro hEq
    have hi := congrFun hEq (⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩ : Fin d)
    simp only [Pi.zero_apply] at hi
    linarith only [hi, h3]

/-- The nonnegativity of clause (B)'s shorter bracket. -/
private theorem rootDisplayBracketB_nonneg [NeZero d] {M : ABKModel d} {m : ℤ}
    {u : H1Function (openCubeSet (originCube d m))} {g : Vec d → Vec d} {Kg : ℝ}
    (hKg : Support.HolderSeminormBoundOn (openCubeSet (originCube d m))
      (1 / 2) Kg g) :
    (0 : ℝ) ≤ Real.sqrt M.nu *
        Support.normalizedL2On (openCubeSet (originCube d m))
          (fun y => Real.sqrt (vecNormSq (u.grad y)))
      + Real.sqrt (Annealed.sigmaBar M m : ℝ)⁻¹ *
          Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kg := by
  obtain ⟨x0, y0, hx0, hy0, hne⟩ := exists_ne_pair_originCube (d := d) m
  have hKg0 : (0 : ℝ) ≤ Kg := hKg.nonneg hx0 hy0 hne
  have h3 : (0 : ℝ) ≤ Real.rpow (3 : ℝ) ((m : ℝ) / 2) := Real.rpow_nonneg (by norm_num) _
  have hL2 : (0 : ℝ) ≤ Real.sqrt M.nu *
      Support.normalizedL2On (openCubeSet (originCube d m))
        (fun y => Real.sqrt (vecNormSq (u.grad y))) :=
    mul_nonneg (Real.sqrt_nonneg _) (Support.normalizedL2On_nonneg _ _)
  have hGleg : (0 : ℝ) ≤ Real.sqrt (Annealed.sigmaBar M m : ℝ)⁻¹ *
      Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kg :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) h3) hKg0
  linarith only [hL2, hGleg]

theorem RootDisplayClauseBAe.mono_const [NeZero d] {M : ABKModel d}
    {C1 Cest Cest' alpha : ℝ} (hle : Cest ≤ Cest')
    (h : RootDisplayClauseBAe M C1 Cest alpha) :
    RootDisplayClauseBAe M C1 Cest' alpha := by
  intro m
  filter_upwards [h m] with omega h'
  intro n hn hpay L hL u hdat g Kg Kh hdir hKg hKh x hx hin
  have hbase := h' n hn hpay L hL u hdat g Kg Kh hdir hKg hKh x hx hin
  have hB := rootDisplayBracketB_nonneg (M := M) (u := u) (g := g) hKg
  have hrpow : (0 : ℝ) ≤ Real.rpow (3 : ℝ) ((1 - alpha) * ((m : ℝ) - (n : ℝ))) :=
    Real.rpow_nonneg (by norm_num) _
  have hstep := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hle hrpow) hB
  exact le_trans hbase hstep

end

end Algsuperdiff.Section4.Provider.Regularity
