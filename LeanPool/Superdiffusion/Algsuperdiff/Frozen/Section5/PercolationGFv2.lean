/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.PercolationScale
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Provider.PercolationAssemblyV2

/-!
# PercolationGFv2

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

open Algsuperdiff.Section3
open Algsuperdiff.Section5.Support
open HCPolySupport MeasureTheory
open scoped ENNReal

/-!
# Chains of good cubes, with the constants supplied — [ABK] Section 5.2

Source: `references/algsuperdiff.tex:13108-13123`, together with the tail clause
of the same proposition.

For a disorder model of strength `gamma` small enough there are constants `c`,
`C` and `Creg` such that, for every accuracy
`ep ∈ [C gamma^{1/2} |log gamma|^{7/2}, 1/4]` and every maximal scale `m`, there
is an `ℕ`-valued random variable `Y` with
`P[Y ≥ N] ≤ exp(-c ep^2 gamma^{-1} |log gamma|^{-6} 3^N)` for `N ≥ 1` such that,
almost surely, at every scale `n ≤ m - Y` every lattice path crossing the
annulus between the rescaled cubes of side `3^{m-n}` and `3^{m-n+1}` meets the
good event `Q(z + □_n, ep)` at at least `(3/4) 3^{m-n}` of the sites it visits.

## The constants are supplied, not assumed

The statement is unconditional: no moment hypothesis on the localized error or
on the localized regularity of a cube appears, and the constant `Creg` of the
good cube event moves into the leading existential rather than being chosen by
the reader. Those moments are the content of the Section 4 bounds
`Algsuperdiff.Frozen.Section4.s5_error_moment_bound` and
`Algsuperdiff.Frozen.Section4.s5_regularity_moment_bound_v2`, the latter at the
exponent `c gamma⁻¹ |log gamma|⁻⁶`, and they hold for the model itself. This is
the reading of the paper, where that constant is the one of the regularity
moment bound and is not free.

The two exponents recorded above are the ones those bounds force. The Section 4
error bound carries the amplitude
`C (p^{1/2} + |log gamma|^{1/2}) gamma^{1/2} |log gamma|^3`; calibrating the
Markov exponent of the error leg against it splits the target in two halves and
gives `|log gamma|^{7/2}` at the lower end of the range of `ep` and
`|log gamma|^{-6}` in the exponent of the tail, both as in the paper.

The constant `Cinj` stays a parameter. It is the constant of the injection
estimate in `L^∞`, which enters the large-scale part of the good event, and a
consumer instantiates it there.

## Reading of the statement

* **Almost-sure quantifier.** The sample space carries no upper-tail
  restriction, so `Y` is finite only almost surely: the path property is
  asserted for almost every sample, after the choice of `Y`, which is a single
  random variable serving every scale `n ≤ m - Y` and every path.
* **Annulus.** The crossing runs from the cube of index `(m - n).toNat` to the
  complement of the cube of index `(m - n).toNat + 1`. This is the printed
  annulus after dividing the lattice `3^{n-1} ℤ^d` by `3^{n-1}`, and it is the
  annulus the source's own proof uses; the narrower annulus obtained by shifting
  both indices down by one would make the threshold `(3/4) 3^{m-n}`
  unattainable by a straight path.
* **Counting.** `qSiteCount` counts the *distinct* sites visited by the path
  (`pathSites N x` is the image of `Finset.range (N + 1)`) at which the good
  event occurs, matching the printed sum over `z ∈ Γ`. It is defined so that no
  decidability instance appears in the statement; `qSiteCount_eq_card_filter`
  identifies it with the corresponding filtered cardinality.
* **Measurability of `Y`.** `Measurable Y` is asserted in addition to the
  printed conclusion; it is what the later use of `Y` as a random scale needs.
* **Constants.** `c`, `C` and `Creg` may depend on `d`, on the value `cstar` of
  the model's ellipticity parameter `c⋆`, and on `Cinj`, which is bound before
  them. The source's `Creg` depends only on `d` and `c⋆`; that it does not in
  fact depend on `Cinj` is invisible to the type. `Creg` stands for three
  constants written separately in the source (the one of the error moments, the
  one of the regularity moments, and twice the latter in the good cube event)
  and `Cinj` for three more (the constant in the range of `p`, the one in the
  exponent `p = c gamma⁻¹ |log gamma|⁻⁶`, and the constant of the injection
  estimate inside the large-scale event of `Q`). Enlarging `Cinj` weakens the
  large-scale event and shrinks `Q`, which `c` and `C` absorb.
* **Small-disorder premise.** The hypothesis `M.gamma ≤ gamma0` is *not* printed
  in Section 5.2; it is the regime of the injection estimate, which the proof of
  this statement invokes through the constant of the event `Q`, and is made
  explicit here for the same reason.

## Conventions

* The tail clause is written as `P[N ≤ Y] ≤ exp(…3^N)` for `N ≥ 1`, where the
  paper writes `P[Y > N]` for every `N ∈ ℕ`. The form here implies the paper's,
  since `P[Y > N] = P[N + 1 ≤ Y]` and `3^{N+1} ≥ 3^N`; the `N ≥ 1` gate is what
  the re-indexing needs, and the union bound of the paper's own proof starts
  at `N`.
* The scale exponent used inside the proof is `a = 5/4`, a value the percolation
  lemma's binder `1 < a ≤ d` admits; the paper runs the same lemma at
  `a = 7/4 - 2 gamma`. No statement changes.

Proved; reduces to the standard axioms.
-/

-- FROZEN-STATEMENT-BEGIN
theorem Algsuperdiff.Frozen.Section5.percolation_GF_v2
    (d : ℕ) (cstar : ℝ) (hcstar : 0 < cstar) (Cinj : ℝ) (hCinj : 0 < Cinj) :
    ∃ gamma0 c C Creg : ℝ, 0 < gamma0 ∧ 0 < c ∧ 0 < C ∧ 0 < Creg ∧
      ∀ M : ABKModel d, Disorder.cstar M = cstar → M.gamma ≤ gamma0 →
      ∀ ep : ℝ, ep ∈ Set.Icc (C * Real.sqrt M.gamma *
          Real.rpow |Real.log M.gamma| (7 / 2)) (1 / 4) →
      ∀ m : ℤ, ∃ Y : Cutoff.CutoffSample d → ℕ,
        Measurable Y ∧
        (∀ N : ℕ, 1 ≤ N →
          (Cutoff.cutoffSampleLaw M).toMeasure {omega | N ≤ Y omega} ≤
            ENNReal.ofReal (Real.exp (-(c * ep ^ (2 : ℕ) * M.gamma⁻¹ *
              |Real.log M.gamma| ^ (-6 : ℤ) * (3 : ℝ) ^ N)))) ∧
        ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure, ∀ n : ℤ,
          n ≤ m - (Y omega : ℤ) →
          ∀ (N : ℕ) (x : ℕ → Fin d → ℤ),
            Provider.Percolation.IsLatticePath x N →
            x 0 ∈ Provider.Percolation.cubeAt (m - n).toNat 0 →
            x N ∉ Provider.Percolation.cubeAt ((m - n).toNat + 1) 0 →
            (3 / 4 : ℝ) * (3 : ℝ) ^ (m - n).toNat ≤
              ((qSiteCount M Creg Cinj n ep
                (Algsuperdiff.Section5.Percolation.pathSites N x) omega : ℕ) : ℝ)
-- FROZEN-STATEMENT-END
    := by
  exact Algsuperdiff.Section5.Provider.percolation_GF_v2_provider d cstar hcstar Cinj hCinj
