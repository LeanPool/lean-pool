/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Probability.RDependent
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Probability.AnnulusSeparation

/-!
# AnnulusRDependent

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# `r`-dependence of the annular per-scale atoms

ABK26 applies Proposition `p.concentration` to the per-scale annular atoms three
times, each time through the sentence "since the sequence `{X_j}` is
`2`-dependent".  The abstract hypothesis is
`Algsuperdiff.Probability.RDependent`; the geometry is
`AnnulusSeparation.separatedBy_annulusRegion_of_gap`; the probability is
`ShellActiveSigma.iIndepFun_of_local_cutoffSample`.  This module is the one
bridge that joins them, and nothing else.

## The statement

`rDependent_of_annulusLocalSigma`: if every `X n` is measurable for the single
sigma-field `cutoffSampleLocalSigma M (n − c) (annulusRegion d n)` — i.e. `X n`
reads only truncations at or below level `n − c`, and only on the annulus of its
own index — then `X` is `r`-dependent for every `r ≥ 1` with
`3 + 2·3^{1−c}·√d ≤ 3^r`.

The truncation offset `c` and the count `r` are **free**.

## Who supplies the hypothesis

`hX` is exactly the `hloc` slot the proved `𝒢₂` lane already discharges:

* `Provider.Proportion.G2Locality.measurable_Xcal_annulusRegion_local` — the
  §4.1 atom `X_j` at `c = 2`;
* `Provider.Proportion.G2Locality.measurable_errorAnnMax_annulusRegion_local` —
  its per-inner-scale summand, same offset;

## Main results

* `rDependent_of_annulusLocalSigma` — the bridge, free `c` and free `r`.

## References

* ABK26, `p.concentration`.
* ABK26, `l.minimal.scale.sep`, Step 1 (the separation claim).
-/

namespace Algsuperdiff.Section4.Probability

open MeasureTheory
open HCPolySupport
open Algsuperdiff.Section3

variable {d : ℕ}

/-! ## The bridge -/

/-- **The `r`-dependence of the annular atoms.**  A family `X : ℤ → Ω → ℝ` on the
genuine cutoff carrier, each member of which reads only truncations at or below
its own level `n − c` and only on the annulus `annulusRegion d n` of its own
index, is `r`-dependent for the cutoff law, for every `r ≥ 1` with
`3 + 2·3^{1−c}·√d ≤ 3^r`.

The proof is the composition of the two proved halves: the finite set of
pairwise `≥ r`-separated indices carried is turned into the pairwise geometric
separation `separatedBy_annulusRegion_of_gap` at the shared-shell threshold `√d
· 3^{min (n−c) (n'−c)}`, which is verbatim the `hsep` hypothesis of
`iIndepFun_of_local_cutoffSample` at `Lidx n = n − c`. -/
theorem rDependent_of_annulusLocalSigma (M : ABKModel d) (c : ℤ) {r : ℕ}
    (hr1 : 1 ≤ r)
    (hr : 3 + 2 * (3 : ℝ) ^ (1 - c) * Real.sqrt (d : ℝ) ≤ (3 : ℝ) ^ (r : ℕ))
    {X : ℤ → Cutoff.CutoffSample d → ℝ}
    (hX : ∀ n : ℤ, Measurable[Cutoff.cutoffSampleLocalSigma M (n - c)
      (annulusRegion d n)] (X n)) :
    Algsuperdiff.Probability.RDependent (Cutoff.cutoffSampleLaw M).toMeasure X r := by
  intro s hs
  exact iIndepFun_of_local_cutoffSample M (fun i : {i // i ∈ s} => i.1 - c)
    (U := fun i : {i // i ∈ s} => annulusRegion d i.1)
    (fun i => measurableSet_annulusRegion d i.1)
    (fun i j hij => separatedBy_annulusRegion_of_gap hr1 hr
      (hs i.1 i.2 j.1 j.2 fun h => hij (Subtype.ext h)))
    (fun i => hX i.1)

end Algsuperdiff.Section4.Probability
