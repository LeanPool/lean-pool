/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Support.HighContrast.Corridor.PhaseComparison.Stability
public import LeanPool.Superdiffusion.Support.HighContrast.Corridor.FixedPhase.Recombination

/-!
# Resample

Ported from scottnarmstrong/CoarseGraining at c7ddd76c08ade64fed1b8d2ca51be14dfee8deb4.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# One-core resampling stability

The deterministic sensitivity estimate `e.fixed.phase.sensitivity` behind the
Efron–Stein step of Proposition 4.3.  Resampling the coefficient field on a
single core `coreBox ℓ σ k` moves the fixed-phase observable
`F_σ(b) = P · 𝐀(U; b_σ) P` by at most a normalized energy over that core:

`|F_σ(b) − F_σ(b')| ≤ 48 Θ (vol U)⁻¹ ∫_{coreBox ℓ σ k ∩ U} Z · 𝐀_σ(b) Z`,

where `Z` is a minimizer for `corridorField ℓ σ b` and `b, b'` are two fields,
`(1, Θ)`-elliptic on `U`, agreeing off the core.

The proof specializes the corridor-independent core
`abs_coarseObservable_sub_le_of_minimizer` from `PhaseComparison.Stability`
to the two corridor-modified fields and the core intersection.  The field
agreement and ellipticity inputs express the resampling-specific geometry;
the analytic minimizer assembly has one implementation.

-/

open HCPolySupport
open MeasureTheory

namespace HCPolySupport

variable {d : ℕ}

/-! ## Measurability of a core box -/

/-- Each core box is measurable (a finite product of closed intervals). -/
theorem measurableSet_coreBox (ℓ : ℝ) (σ : Vec d) (k : Fin d → ℤ) :
    MeasurableSet (coreBox ℓ σ k) := by
  rw [coreBox]
  exact MeasurableSet.univ_pi (fun i => measurableSet_Icc)

/-! ## The one-core resampling specialization -/

/-- **Part 3 (one-core resampling stability), minimizer form.**  For a fixed grid
phase `σ` and two fields `b, b'` that are `(1, Θ)`-elliptic on
`U := cubeSet (originCube d m)` and agree off the core `coreBox ℓ σ k`, the
fixed-phase observable moves by at most a normalized core-energy of the
minimizer `Z` for `corridorField ℓ σ b`. -/
theorem abs_phaseObservable_resample_sub_le_of_minimizer [NeZero d] {Θ : ℝ} (hΘ : 1 ≤ Θ)
    {m : ℤ} {ℓ : ℝ} {σ : Vec d} {k : Fin d → ℤ} (P : BlockVec d)
    {b b' : CoeffField d}
    (hEllb : IsEllipticFieldOn 1 Θ (cubeSet (originCube d m)) b)
    (hEllb' : IsEllipticFieldOn 1 Θ (cubeSet (originCube d m)) b')
    (hbb' : Set.EqOn b b' (coreBox ℓ σ k)ᶜ)
    {Z : BlockState d}
    (hZadm : IsBlockMuAdmissible (cubeSet (originCube d m)) P Z)
    (hZresp : BlockResponseSpace (corridorField ℓ σ b) (cubeSet (originCube d m)) Z)
    (hZeng : Mu (cubeSet (originCube d m)) P (corridorField ℓ σ b)
      = blockEnergyAverage (cubeSet (originCube d m)) (corridorField ℓ σ b) Z) :
    |blockVecDot P
          (blockMatVecMul
            (coarseBlockMatrix (cubeSet (originCube d m)) (corridorField ℓ σ b')) P) -
        blockVecDot P
          (blockMatVecMul
            (coarseBlockMatrix (cubeSet (originCube d m)) (corridorField ℓ σ b)) P)| ≤
      48 * Θ * (volume (cubeSet (originCube d m))).toReal⁻¹ *
        ∫ x in coreBox ℓ σ k ∩ cubeSet (originCube d m),
          blockVecDot (Z.eval x)
            (blockMatVecMul (blockCoeffField (corridorField ℓ σ b) x) (Z.eval x)) := by
  set U := cubeSet (originCube d m) with hUdef
  have hU : MeasurableSet U := measurableSet_cubeSet (originCube d m)
  -- the two corridor-modified fields are elliptic on `U`
  have hEllc : IsEllipticFieldOn 1 Θ U (corridorField ℓ σ b) :=
    isEllipticFieldOn_corridorField hU hΘ hEllb
  have hEllc' : IsEllipticFieldOn 1 Θ U (corridorField ℓ σ b') :=
    isEllipticFieldOn_corridorField hU hΘ hEllb'
  set S : Set (Vec d) := coreBox ℓ σ k ∩ U with hSdef
  have hS : MeasurableSet S := (measurableSet_coreBox ℓ σ k).inter hU
  have hSU : S ⊆ U := Set.inter_subset_right
  -- corridor fields agree on `U ∖ S = U ∖ coreBox k`
  have hagreeOff : Set.EqOn (corridorField ℓ σ b) (corridorField ℓ σ b') (U \ S) := by
    intro x hx
    have hxnc : x ∉ coreBox ℓ σ k := by
      intro hc; exact hx.2 ⟨hc, hx.1⟩
    by_cases hxS : x ∈ corridorSet ℓ σ
    · rw [corridorField_apply_of_mem hxS, corridorField_apply_of_mem hxS]
    · rw [corridorField_apply_of_not_mem hxS, corridorField_apply_of_not_mem hxS]
      exact hbb' hxnc
  exact abs_coarseObservable_sub_le_of_minimizer hΘ P hEllc hEllc' hS hSU hagreeOff
    hZadm hZresp hZeng

/-- **Part 3 (one-core resampling stability).**  Existential-minimizer wrapper. -/
theorem abs_phaseObservable_resample_sub_le [NeZero d] {Θ : ℝ} (hΘ : 1 ≤ Θ)
    {m : ℤ} {ℓ : ℝ} {σ : Vec d} {k : Fin d → ℤ} (P : BlockVec d)
    {b b' : CoeffField d}
    (hEllb : IsEllipticFieldOn 1 Θ (cubeSet (originCube d m)) b)
    (hEllb' : IsEllipticFieldOn 1 Θ (cubeSet (originCube d m)) b')
    (hbb' : Set.EqOn b b' (coreBox ℓ σ k)ᶜ) :
    ∃ Z : BlockState d,
      IsBlockMuAdmissible (cubeSet (originCube d m)) P Z ∧
        BlockResponseSpace (corridorField ℓ σ b) (cubeSet (originCube d m)) Z ∧
        |blockVecDot P
              (blockMatVecMul
                (coarseBlockMatrix (cubeSet (originCube d m)) (corridorField ℓ σ b')) P) -
            blockVecDot P
              (blockMatVecMul
                (coarseBlockMatrix (cubeSet (originCube d m)) (corridorField ℓ σ b)) P)| ≤
          48 * Θ * (volume (cubeSet (originCube d m))).toReal⁻¹ *
            ∫ x in coreBox ℓ σ k ∩ cubeSet (originCube d m),
              blockVecDot (Z.eval x)
                (blockMatVecMul (blockCoeffField (corridorField ℓ σ b) x) (Z.eval x)) := by
  have hU : MeasurableSet (cubeSet (originCube d m)) := measurableSet_cubeSet (originCube d m)
  have hEllc : IsEllipticFieldOn 1 Θ (cubeSet (originCube d m)) (corridorField ℓ σ b) :=
    isEllipticFieldOn_corridorField hU hΘ hEllb
  obtain ⟨Z, hZadm, hZeng, hZresp⟩ := exists_cubeBlockMinimizer hEllc P
  exact ⟨Z, hZadm, hZresp,
    abs_phaseObservable_resample_sub_le_of_minimizer hΘ P hEllb hEllb' hbb' hZadm hZresp hZeng⟩

end HCPolySupport
