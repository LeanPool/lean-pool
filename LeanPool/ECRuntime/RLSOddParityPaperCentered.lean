/-
Copyright (c) 2026 Jiri Kovar, Jakub Kudela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiri Kovar, Jakub Kudela
-/
module

public import LeanPool.ECRuntime.StrictMonotoneRLSOddSharpCentered

/-!
Odd-dimensional RLS with the paper's centering convention
`H_(n/2) = (H_floor(n/2) + H_ceil(n/2)) / 2`. The exact change of center
converts the lower-half harmonic `+1/2` correction into the paper's `-1/2` correction.

Ported from ECRuntime at a0e34dce6395d48d0fb9c7b8850088973f503d8b.
The module paths and public visibility are adapted for Lean Pool.
-/

@[expose] public section

open Filter
namespace ECRuntime

/-- Sharp odd-dimension RLS runtime centered using the published
half-harmonic convention, for every strictly monotone fitness family. -/
theorem proposed_strictMonotoneRLS_oddPaperHalfHarmonicCentered
    (fitness : (n : Nat) → BitString n → Real)
    (hf : ∀ n : Nat, CandidateCoordinateStrictMonotonicity (fitness n)) :
    Tendsto
      (fun m : Nat =>
        strictMonotoneRLSUniformInitialMean
          (show 0 < 2 * m + 1 by omega) (fitness (2 * m + 1)) -
          (((2 * m + 1 : Nat) : Real) *
            ((harmonicReal m + harmonicReal (m + 1)) / 2)))
      atTop (nhds (-(1 / 2 : Real))) := by
  have hOdd := proposed_strictMonotoneRLS_uniformInitial_oddSharpCentered fitness hf
  have hshift : Tendsto (fun m : Nat => m + 1) atTop atTop := by
    apply tendsto_atTop_mono' atTop
      (Filter.Eventually.of_forall (fun m : Nat => (show m ≤ m + 1 by omega)))
      tendsto_id
  have hcast : Tendsto (fun m : Nat => (((m + 1 : Nat) : Real)))
      atTop atTop := tendsto_natCast_atTop_atTop.comp hshift
  have hinv : Tendsto (fun m : Nat => (((m + 1 : Nat) : Real)⁻¹))
      atTop (nhds (0 : Real)) := tendsto_inv_atTop_zero.comp hcast
  have hsmall : Tendsto (fun m : Nat =>
      (1 / 2 : Real) * (((m + 1 : Nat) : Real)⁻¹))
      atTop (nhds (0 : Real)) := by
    simpa only [mul_zero] using hinv.const_mul (1 / 2 : Real)
  have hone : Tendsto (fun _ : Nat => (1 : Real))
      atTop (nhds (1 : Real)) := tendsto_const_nhds
  have hcorrection := hone.sub hsmall
  have hcenter := hOdd.sub hcorrection
  have hval : (1 / 2 : Real) - (1 - 0) = -(1 / 2 : Real) := by norm_num
  rw [hval] at hcenter
  apply hcenter.congr'
  filter_upwards [] with m
  have hsucc : harmonicReal (m + 1) =
      harmonicReal m + (((m + 1 : Nat) : Real)⁻¹) := by
    simp [harmonicReal, harmonic_succ]
  have hcast : ((2 * m + 1 : Nat) : Real) =
      2 * (((m + 1 : Nat) : Real)) - 1 := by
    push_cast
    ring
  have hmne : (((m + 1 : Nat) : Real)) ≠ 0 := by positivity
  rw [hsucc, hcast]
  field_simp [hmne]
  ring

end ECRuntime
