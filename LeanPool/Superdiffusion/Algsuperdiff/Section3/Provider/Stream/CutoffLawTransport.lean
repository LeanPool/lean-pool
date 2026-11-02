/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Stream.LargeCubeLinfty
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Cutoff.Carrier

/-!
# CutoffLawTransport

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Transporting the stream `Γ_σ` estimates to the cutoff sample law

The proved stream estimates of `Algsuperdiff.Section3.Provider.Stream` are all
stated under the canonical shell-sequence law `M.P.toMeasure` on `ShellSeq d`,
while every consumer downstream of the genuine lower-infinite cutoff works
under `Cutoff.cutoffSampleLaw M` on the lower-tail-good subtype
`Cutoff.CutoffSample d`.  This module supplies the transport between the two.

The bridge is the exact push-forward identity
`Cutoff.map_cutoffSampleLaw_val`: the sample law pushes forward along the
subtype inclusion to the shell law.  Because that inclusion is a measurable
embedding, the induced identity on preimages holds for *every* subset of
`ShellSeq d`, measurable or not, so the transport of a weak-Orlicz tail bound
needs no measurability or admissibility hypothesis at all: an upper-tail event
of `fun omega => X omega.1` is by definition the inclusion preimage of the
corresponding upper-tail event of `X`.

## Main results

* `Algsuperdiff.Section3.Provider.Stream.measure_preimage_val_cutoffSampleLaw`:
  the inclusion preimage identity for arbitrary subsets.
* `Algsuperdiff.Section3.Provider.Stream.isBigOWith_cutoffSampleLaw_comp_val`:
  the generic one-sided transfer.
* `Algsuperdiff.Section3.Provider.Stream.isBigOWith_cutoffSampleLaw_of_forall_eq_comp_val`:
  the same transfer for a sample-level function that is only known to factor
  through the inclusion pointwise.
* The `_cutoffLaw` corollaries: each principal proved stream export restated
  verbatim under `Cutoff.cutoffSampleLaw M`, with `omega.1` in place of
  `omega`.

## References

* ABK26 (the transported displays; see the source citations on the proved
  exports themselves).
-/

namespace Algsuperdiff.Section3.Provider.Stream

open MeasureTheory
open HCPolySupport
open HCPolySupport.Book.Ch02
open Algsuperdiff.Section3.Cutoff

noncomputable section

variable {d : ℕ}

/-! ## The sample inclusion as a mass-preserving embedding -/

/-- The inclusion of the lower-tail-good sample carrier into the shell-sequence
carrier is a measurable embedding. -/
theorem measurableEmbedding_cutoffSample_val :
    MeasurableEmbedding (Subtype.val : CutoffSample d → ShellSeq d) :=
  MeasurableEmbedding.subtype_coe (measurableSet_lowerTailGoodSet d)

/-- Every subset of the shell-sequence carrier -- measurable or not -- pulls
back along the sample inclusion with exactly its original mass.  This is the
measurable-embedding strengthening of `Cutoff.map_cutoffSampleLaw_val`. -/
theorem measure_preimage_val_cutoffSampleLaw (M : ABKModel d) (s : Set (ShellSeq d)) :
    (cutoffSampleLaw M).toMeasure ((Subtype.val : CutoffSample d → ShellSeq d) ⁻¹' s) =
      M.P.toMeasure s := by
  rw [← measurableEmbedding_cutoffSample_val.map_apply (cutoffSampleLaw M).toMeasure s,
    map_cutoffSampleLaw_val]

/-- The real-valued form of `measure_preimage_val_cutoffSampleLaw`, which is
the shape consumed by the weak-Orlicz tail calculus. -/
theorem measureReal_preimage_val_cutoffSampleLaw (M : ABKModel d)
    (s : Set (ShellSeq d)) :
    (cutoffSampleLaw M).toMeasure.real
        ((Subtype.val : CutoffSample d → ShellSeq d) ⁻¹' s) =
      M.P.toMeasure.real s := by
  simp only [measureReal_def, measure_preimage_val_cutoffSampleLaw]

/-! ## The generic transfers -/

/-- Generic transfer of a one-sided weak-Orlicz tail bound from the canonical
shell law to the cutoff sample law.  No measurability of `X` and no
admissibility of `Ψ` is needed: the upper-tail event of `fun omega => X omega.1`
is definitionally the inclusion preimage of the upper-tail event of `X`, and
the inclusion preserves the mass of every subset. -/
theorem isBigOWith_cutoffSampleLaw_comp_val {M : ABKModel d} {Psi : ℝ → ℝ}
    {X : ShellSeq d → ℝ} {A : ℝ}
    (hX : IndependentSums.IsBigOWith M.P.toMeasure Psi X A) :
    IndependentSums.IsBigOWith (cutoffSampleLaw M).toMeasure Psi
      (fun omega : CutoffSample d => X omega.1) A := by
  intro t ht
  have hset : IndependentSums.upperTailEvent
      (fun omega : CutoffSample d => X omega.1) (A * t) =
      (Subtype.val : CutoffSample d → ShellSeq d) ⁻¹'
        IndependentSums.upperTailEvent X (A * t) := rfl
  rw [hset, measureReal_preimage_val_cutoffSampleLaw]
  exact hX ht

/-- The one-sided transfer for a function already phrased on the sample
carrier, given only that it factors pointwise through the inclusion. -/
theorem isBigOWith_cutoffSampleLaw_of_forall_eq_comp_val {M : ABKModel d}
    {Psi : ℝ → ℝ} {X : ShellSeq d → ℝ} {Y : CutoffSample d → ℝ} {A : ℝ}
    (hY : ∀ omega : CutoffSample d, Y omega = X omega.1)
    (hX : IndependentSums.IsBigOWith M.P.toMeasure Psi X A) :
    IndependentSums.IsBigOWith (cutoffSampleLaw M).toMeasure Psi Y A := by
  rw [show Y = fun omega : CutoffSample d => X omega.1 from funext hY]
  exact isBigOWith_cutoffSampleLaw_comp_val hX

/-! ## The small-cube `L^∞` increment bounds on the cutoff law -/

/-- `isBigOWith_gammaSigma_translatedIncrementSupBound` under the cutoff sample
law: the small-cube bound on a translated cube, at the same amplitude. -/
theorem isBigOWith_gammaSigma_translatedIncrementSupBound_cutoffLaw
    (M : ABKModel d) {n m : ℤ} (hnm : n < m) (z : Vec d) :
    IndependentSums.IsBigOWith (cutoffSampleLaw M).toMeasure
      (IndependentSums.gammaSigma 2)
      (fun omega : CutoffSample d => translatedIncrementSupBound z n m omega.1)
      (streamLinftyConst d *
        min (Real.sqrt M.gamma⁻¹) (Real.sqrt ((m : ℝ) - (n : ℝ))) *
        (3 : ℝ) ^ (M.gamma * (m : ℝ))) :=
  isBigOWith_cutoffSampleLaw_comp_val
    (isBigOWith_gammaSigma_translatedIncrementSupBound M hnm z)

end

end Algsuperdiff.Section3.Provider.Stream
