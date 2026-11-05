/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Field.StreamField

/-!
# Continuity

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Local uniform convergence and continuity of the stream matrix

On the carrier both halves of the scale decomposition converge uniformly on
every origin cube: the descending half is exactly the lower-infinite cutoff
`k_ℓ`, already continuous, and the ascending half is dominated on `□_ℓ` by the
summable series `Σ_{n > ℓ} d ‖∇j_n‖_{L^∞(□_ℓ)} · 3^{ℓ}/2` produced by the mean
value inequality.  The normalized field is therefore continuous, and so defines
a regular coefficient field in the ambient sense.

## Main results

* `continuous_streamField` — the field is continuous.
* `streamRegField` — the field as a regular coefficient field.

## References

* ABK26, the stream matrix and the scale decomposition.
-/

namespace Algsuperdiff.Section5.Field

open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.Stream
open HCPolySupport
open scoped Matrix.Norms.Elementwise

noncomputable section

variable {d : ℕ} {gamma : ℝ}

private theorem continuous_shell_entry (j : ShellField d) (i k : Fin d) :
    Continuous fun z : Vec d => j z i k :=
  (continuous_apply k).comp ((continuous_apply i).comp j.1.1.continuous)

/-- The ascending tail converges uniformly on the origin cube of scale `ell`. -/
private theorem tendstoUniformlyOn_upperTail (omega : FullSample d gamma) (ell : ℕ)
    (i k : Fin d) :
    TendstoUniformlyOn
      (fun q z => ∑ r ∈ Finset.range q,
        (omega.1.1 ((ell : ℤ) + 1 + (r : ℤ)) z i k -
          omega.1.1 ((ell : ℤ) + 1 + (r : ℤ)) 0 i k))
      (fun z => ∑' r : ℕ,
        (omega.1.1 ((ell : ℤ) + 1 + (r : ℤ)) z i k -
          omega.1.1 ((ell : ℤ) + 1 + (r : ℤ)) 0 i k))
      Filter.atTop (openCubeSet (originCube d (ell : ℤ))) := by
  refine tendstoUniformlyOn_tsum_nat
    (u := fun r : ℕ => (d : ℝ) *
      localCubeDerivNorm (ell : ℤ) (omega.1.1 ((ell : ℤ) + 1 + (r : ℤ))) *
        ((1 / 2 : ℝ) * (3 : ℝ) ^ (ell : ℤ)))
    (((summable_localCubeDerivNorm_ascending omega ell ((ell : ℤ) + 1)).mul_left
      (d : ℝ)).mul_right _) fun r z hz => ?_
  have hbound := abs_entry_sub_le_of_mem_openOriginCube (ell : ℤ)
    (omega.1.1 ((ell : ℤ) + 1 + (r : ℤ))) hz i k
  have hcoef : (0 : ℝ) ≤ (d : ℝ) *
      localCubeDerivNorm (ell : ℤ) (omega.1.1 ((ell : ℤ) + 1 + (r : ℤ))) :=
    mul_nonneg (Nat.cast_nonneg d) (localCubeDerivNorm_nonneg _ _)
  rw [Real.norm_eq_abs]
  exact hbound.trans
    (mul_le_mul_of_nonneg_left (norm_le_of_mem_openOriginCube hz) hcoef)

private theorem continuousOn_upperTail (omega : FullSample d gamma) (ell : ℕ)
    (i k : Fin d) :
    ContinuousOn
      (fun z : Vec d => ∑' r : ℕ,
        (omega.1.1 ((ell : ℤ) + 1 + (r : ℤ)) z i k -
          omega.1.1 ((ell : ℤ) + 1 + (r : ℤ)) 0 i k))
      (openCubeSet (originCube d (ell : ℤ))) := by
  refine (tendstoUniformlyOn_upperTail omega ell i k).continuousOn ?_
  refine (Filter.Eventually.of_forall fun q => ?_).frequently
  refine Continuous.continuousOn ?_
  refine continuous_finsetSum (Finset.range q) fun r _ => ?_
  exact (continuous_shell_entry (omega.1.1 ((ell : ℤ) + 1 + (r : ℤ))) i k).sub
    continuous_const

/-- **Continuity of the normalized field, entrywise.** -/
theorem continuous_streamField_entry (omega : FullSample d gamma) (i k : Fin d) :
    Continuous fun x : Vec d => streamField omega x i k := by
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨ell, hx⟩ := exists_nat_mem_openOriginCube x
  have hsplit : (fun z : Vec d => streamField omega z i k) =
      fun z : Vec d =>
        (cutoff (ell : ℤ) omega.1 z i k - cutoff (ell : ℤ) omega.1 0 i k) +
          ∑' r : ℕ, (omega.1.1 ((ell : ℤ) + 1 + (r : ℤ)) z i k -
            omega.1.1 ((ell : ℤ) + 1 + (r : ℤ)) 0 i k) := by
    funext z
    exact streamField_eq_cutoff_add_upperTail omega (ell : ℤ) z i k
  have hcont : ContinuousOn (fun z : Vec d => streamField omega z i k)
      (openCubeSet (originCube d (ell : ℤ))) := by
    rw [hsplit]
    exact (((continuous_cutoff_entry (ell : ℤ) omega.1 i k).sub
      continuous_const).continuousOn).add (continuousOn_upperTail omega ell i k)
  exact (hcont x hx).continuousAt
    ((isOpen_openCubeSet (originCube d (ell : ℤ))).mem_nhds hx)

/-- **Continuity of the normalized field.** -/
theorem continuous_streamField (omega : FullSample d gamma) :
    Continuous (streamField omega) :=
  continuous_pi fun i => continuous_pi fun k => continuous_streamField_entry omega i k

/-- The symmetric part of `ν I + k` is exactly `ν I`, so the normalized field
contributes no symmetric part to the coefficient field. -/
theorem symmPart_nu_add_streamField (nu : ℝ) (omega : FullSample d gamma) (x : Vec d) :
    symmPart (nu • (1 : Mat d) + streamField omega x) = nu • (1 : Mat d) := by
  have hskew := streamField_skew omega x
  ext i k
  have hskew_entry : streamField omega x k i = -streamField omega x i k := by
    have := congrFun (congrFun hskew i) k
    simpa only [Matrix.transpose_apply, Matrix.neg_apply] using this
  simp only [symmPart, Matrix.add_apply, Matrix.smul_apply]
  rw [hskew_entry]
  by_cases hik : i = k
  · subst hik
    simp only [Matrix.one_apply, ite_eq_left]
    ring
  · have hki : k ≠ i := Ne.symm hik
    simp only [Matrix.one_apply, ite_eq_right hik, ite_eq_right hki]
    ring

end

end Algsuperdiff.Section5.Field
