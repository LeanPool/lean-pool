/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Proportion.G2Locality
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Probability.AnnulusRDependent

/-!
# KickFamily

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The Step-1 annular kick family of `l.minimal.scale.sep`

ABK26, §4.2, Step 1 of `l.minimal.scale.sep`.  The manuscript's Step 1 opens
with the inner-scale sum

```
Σ_{i ≤ j−1} 3^{−½s(j−i)} max_{z ∈ 3^i ℤ^d ∩ (□_j ∖ □_{j−1})}
    𝓔_{s,2,2}(z + □_i; 𝐚_{i−2}, σ_{i−2})
```

This module builds the sum — the **unsquared** sibling of the §4.1 `𝒢₂` object
`Proportion.errorAnnMax`, at the §4.2 weight `3^{−½s·}` rather than `3^{−¼s·}`
— together with the two legs `X_j^{(1)}, X_j^{(2)}`, their locality, and their
`r`-dependence.

## The leg construction, and why it is a clamp

`X_j^{(1)}` and `X_j^{(2)}` are the **clamp** and the **overshoot** of the sum at
a deterministic threshold `lam`:

```
X_j^{(1)} = min(annularKick_j, lam) ,   X_j^{(2)} = annularKick_j − min(annularKick_j, lam) ,
X_j^{(1)} + X_j^{(2)} = annularKick_j  exactly.
```

Both legs are therefore **measurable functions of the single variable
`annularKick_j`**, and that is the point: the manuscript's Step 1 claims that
`X_j^{(i)}` and `X_{j'}^{(i')}` are independent for `|j − j'| > 1`, *for each*
`i, i' ∈ {1,2}` — a joint statement about the pair.  Any leg decomposition
built from the two `Γ`-witnesses of the induction bound would fail it: those
witnesses are supplied by the Section 3 anchor as bare existentials and carry
no locality whatsoever.  With the clamp, the joint claim is a one-line
push-forward of the `r`-dependence of `annularKick`, which is itself a one-line
consequence of the proved bridge `Section4.Probability.rDependent_of_annulusLocalSigma`.
The threshold that makes the two clamped legs carry the manuscript's `Γ₂` and
`Γ_{1/2}` amplitudes is chosen in `KickTails.lean`; nothing in this file
depends on its value, so `lam` is a free real parameter throughout.

## Main definitions

* `kickAtom` — the per-cube atom `𝓔_{s,2,2}(z + □_i; 𝐚_{i−2}, σ_{i−2})`,
  rendered by translating the *sample* (resolution A4) at the public measurable
  `(2,2)` observable, **unsquared**.
* `kickAnnMax` — the `0`-floored lattice-annulus maximum of the atom.
* `annularKickE` / `annularKick` — the weighted inner-scale sum, formed in
  `ℝ≥0∞` and read back into `ℝ`.
* `kickLegLow` / `kickLegHigh` — the two legs `X_j^{(1)}, X_j^{(2)}`.

## Main results

* `annularKickE_eq_wsumE`, `annularKick_eq_wsum` — the bridge to the `ℕ`-indexed
  weighted-series apparatus of `Proportion.SeriesTail`, so the tail machinery is
  reused verbatim.
* `measurable_annularKick_annulusRegion_local` — locality at truncation level
  `j − 2` on `annulusRegion d j`, the `hX` slot of the `r`-dependence bridge.

## Deviations from the printed text

* (inherited from §4.1) — the summand reads the field at the inner scale `i`;
  this is the proved `Support.annularErrorObservable` at index `i`, so the
  convention is the manuscript's.
* (inherited) — the `(2,2)` observable is the measurable representative,
  choice-dependent on a null set; every statement below is a statement about that
  same representative, and the locality step absorbs the choice through
  `Proportion.measurable_cutoffSampleLocalSigma_of_ae_eq`.
* The leg split is a *construction*, not a printed definition: exhibits no
  `X_j^{(i)}`.  See the module note above for why the clamp is the reading that
  supports the printed independence claim.

## References

* ABK26, `l.minimal.scale.sep`, Step 1.
-/

namespace Algsuperdiff.Section4.Provider.MinimalScale

open Algsuperdiff.Section3
open HCPolySupport HCPolySupport.Book MeasureTheory
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Probability
open Algsuperdiff.Section4.Provider.Proportion
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The unsquared per-cube atom -/

/-- **The Step-1 per-cube atom** `𝓔_{s,2,2}(z + □_i; 𝐚_{i−2}, σ_{i−2})`,
rendered by translating the sample (resolution A4) at the public measurable
`(2,2)` observable.  This is `Proportion.errorAtomSq` *without* the square: §4.2
Step 1 never squares. -/
def kickAtom (M : ABKModel d) (i : ℤ) (s : {s : ℝ // 0 < s}) (z : Vec d)
    (omega : Cutoff.CutoffSample d) : ℝ :=
  Support.annularErrorObservable M i s (Cutoff.translateCutoffSample z omega)

theorem kickAtom_nonneg (M : ABKModel d) (i : ℤ) (s : {s : ℝ // 0 < s}) (z : Vec d)
    (omega : Cutoff.CutoffSample d) : 0 ≤ kickAtom M i s z omega :=
  Support.annularErrorObservable_nonneg M i s _

theorem measurable_kickAtom (M : ABKModel d) (i : ℤ) (s : {s : ℝ // 0 < s})
    (z : Vec d) : Measurable (kickAtom M i s z) :=
  (Support.measurable_annularErrorObservable M i s).comp
    (Cutoff.measurable_translateCutoffSample z)

/-- The atom is the square root of the §4.1 squared atom; this is the one line that
lets the proved `𝒢₂` locality export be reused unmodified. -/
theorem kickAtom_eq_sqrt_errorAtomSq (M : ABKModel d) (i : ℤ) (s : {s : ℝ // 0 < s})
    (z : Vec d) (omega : Cutoff.CutoffSample d) :
    kickAtom M i s z omega = Real.sqrt (errorAtomSq M i s z omega) := by
  have h0 : (0 : ℝ) ≤ Support.annularErrorObservable M i s
      (Cutoff.translateCutoffSample z omega) :=
    Support.annularErrorObservable_nonneg M i s _
  simp only [kickAtom, errorAtomSq]
  rw [Real.sqrt_sq h0]

/-! ## 2. The lattice-annulus maximum -/

/-- **The lattice-annulus maximum**: `max_{z ∈ 3^i ℤ^d ∩ (□_j ∖ □_{j−1})}
𝓔_{s,2,2}(z + □_i; 𝐚_{i−2}, σ_{i−2})`, `0`-floored so that it is total (the
annulus enumeration may be empty). -/
def kickAnnMax (M : ABKModel d) (s : {s : ℝ // 0 < s}) (j i : ℤ)
    (omega : Cutoff.CutoffSample d) : ℝ :=
  fmax (latticeAnnulusFinset d i j (j - 1))
    (fun v => kickAtom M i s (Support.triadicLatticePoint i v) omega)

theorem kickAnnMax_nonneg (M : ABKModel d) (s : {s : ℝ // 0 < s}) (j i : ℤ)
    (omega : Cutoff.CutoffSample d) : 0 ≤ kickAnnMax M s j i omega :=
  fmax_nonneg _ _

theorem measurable_kickAnnMax (M : ABKModel d) (s : {s : ℝ // 0 < s}) (j i : ℤ) :
    Measurable (kickAnnMax M s j i) :=
  measurable_fmax _ fun v => measurable_kickAtom M i s (Support.triadicLatticePoint i v)

/-! ## 3. The weighted inner-scale sum -/

/-- **The Step-1 inner-scale sum**, formed in `ℝ≥0∞`: `Σ_{i ≤ j−1} 3^{−½s(j−i)} ·
kickAnnMax_j(i)`.  The weight is the §4.2 weight `3^{−½s·}` — half the decay
rate of the §4.1 `𝒢₂` lane, because §4.2 Step 1 does not square. -/
def annularKickE (M : ABKModel d) (s : {s : ℝ // 0 < s}) (j : ℤ)
    (omega : Cutoff.CutoffSample d) : ℝ≥0∞ :=
  ∑' i : {i : ℤ // i ≤ j - 1},
    ENNReal.ofReal (weightThird ((s : ℝ) / 2) (j - i.1).toNat * kickAnnMax M s j i.1 omega)

/-- The real-valued inner-scale sum; at the sample points where the `ℝ≥0∞` sum is
infinite this is `0`, which only strengthens every upper-tail statement about
it. -/
def annularKick (M : ABKModel d) (s : {s : ℝ // 0 < s}) (j : ℤ)
    (omega : Cutoff.CutoffSample d) : ℝ :=
  (annularKickE M s j omega).toReal

/-- **The bridge to the `ℕ`-indexed weighted-series apparatus.**  The inner
scales `i ≤ j − 1` are enumerated by the offset `p = j − 1 − i`, at which the
weight is `weightThird (½s) (p+1)`. -/
theorem annularKickE_eq_wsumE (M : ABKModel d) (s : {s : ℝ // 0 < s}) (j : ℤ)
    (omega : Cutoff.CutoffSample d) :
    annularKickE M s j omega =
      wsumE (fun p => kickAnnMax M s j (j - 1 - (p : ℤ)))
        (fun p => weightThird ((s : ℝ) / 2) (p + 1)) omega := by
  rw [annularKickE, ← (innerScaleEquiv j).tsum_eq
      (fun i : {i : ℤ // i ≤ j - 1} =>
        ENNReal.ofReal (weightThird ((s : ℝ) / 2) (j - i.1).toNat *
          kickAnnMax M s j i.1 omega)), wsumE]
  refine tsum_congr fun p => ?_
  have htn : (j - (j - 1 - (p : ℤ))).toNat = p + 1 := by omega
  show ENNReal.ofReal (weightThird ((s : ℝ) / 2) (j - (j - 1 - (p : ℤ))).toNat *
      kickAnnMax M s j (j - 1 - (p : ℤ)) omega) = _
  rw [htn]

theorem annularKick_eq_wsum (M : ABKModel d) (s : {s : ℝ // 0 < s}) (j : ℤ) :
    annularKick M s j =
      wsum (fun p => kickAnnMax M s j (j - 1 - (p : ℤ)))
        (fun p => weightThird ((s : ℝ) / 2) (p + 1)) := by
  funext omega
  rw [annularKick, annularKickE_eq_wsumE M s j omega]
  rfl

theorem annularKick_nonneg (M : ABKModel d) (s : {s : ℝ // 0 < s}) (j : ℤ)
    (omega : Cutoff.CutoffSample d) : 0 ≤ annularKick M s j omega :=
  ENNReal.toReal_nonneg

theorem measurable_annularKick (M : ABKModel d) (s : {s : ℝ // 0 < s}) (j : ℤ) :
    Measurable (annularKick M s j) := by
  rw [annularKick_eq_wsum]
  exact measurable_wsum fun p => measurable_kickAnnMax M s j _

/-! ## 4. Locality on the annulus of the own index -/

/-- **The unsquared atom is local**, at truncation level `i − 2` and every region
containing the closed cube `z + □_i = ⟨i, v⟩`.  Obtained from the proved `𝒢₂`
export `Proportion.measurable_errorAtomSq_local` by a square root: the atom is
nonnegative, so no information is lost. -/
theorem measurable_kickAtom_local (M : ABKModel d) (i : ℤ) (s : {s : ℝ // 0 < s})
    (v : Fin d → ℤ) {m : ℤ} (hm : i - 2 ≤ m) {U : Set (Vec d)}
    (hQU : cubeSet (Localize.latticeCube i v) ⊆ U) :
    Measurable[Cutoff.cutoffSampleLocalSigma M m U]
      (kickAtom M i s (Support.triadicLatticePoint i v)) := by
  have hsq := measurable_errorAtomSq_local M i s v hm hQU
  have heq : kickAtom M i s (Support.triadicLatticePoint i v)
      = fun omega => Real.sqrt (errorAtomSq M i s (Support.triadicLatticePoint i v) omega) :=
    funext fun omega => kickAtom_eq_sqrt_errorAtomSq M i s _ omega
  rw [heq]
  exact Real.continuous_sqrt.measurable.comp hsq

/-- **The lattice-annulus maximum is local** on the annulus region of its own
index: every read cube `⟨i, v⟩` with `v` in the annulus enumeration sits inside
`annulusRegion d j`, and every truncation level `i − 2` is at or below `j − 2`. -/
theorem measurable_kickAnnMax_annulusRegion_local (M : ABKModel d)
    (s : {s : ℝ // 0 < s}) {j i : ℤ} (hi : i ≤ j - 1) :
    Measurable[Cutoff.cutoffSampleLocalSigma M (j - 2) (annulusRegion d j)]
      (kickAnnMax M s j i) := by
  refine @measurable_fmax_of_mem (Cutoff.CutoffSample d) (Fin d → ℤ)
    (Cutoff.cutoffSampleLocalSigma M (j - 2) (annulusRegion d j)) _ _ ?_
  intro v hv
  have hvset : v ∈ Support.latticeAnnulusSet d i j (j - 1) :=
    (mem_latticeAnnulusFinset_iff (d := d) (by omega)).1 hv
  exact measurable_kickAtom_local M i s v (by omega)
    (cubeSet_latticeCube_subset_annulusRegion (d := d) hi hvset)

/-- **The Step-1 inner-scale sum is local** on `annulusRegion d j` at truncation
level `j − 2` — the `hX` slot of the `r`-dependence bridge. -/
theorem measurable_annularKick_annulusRegion_local (M : ABKModel d)
    (s : {s : ℝ // 0 < s}) (j : ℤ) :
    Measurable[Cutoff.cutoffSampleLocalSigma M (j - 2) (annulusRegion d j)]
      (annularKick M s j) := by
  rw [annularKick_eq_wsum]
  refine @measurable_wsum (Cutoff.CutoffSample d)
    (Cutoff.cutoffSampleLocalSigma M (j - 2) (annulusRegion d j)) _ _ fun p => ?_
  exact measurable_kickAnnMax_annulusRegion_local M s (by omega)

/-! ## 5. `r`-dependence -/

/-- **The Step-1 family is `r`-dependent**, for every `r ≥ 1` clearing the honest
separation count `3 + 2·3^{1−2}·√d ≤ 3^r` of the proved bridge at truncation
offset `c = 2`. -/
theorem rDependent_annularKick (M : ABKModel d) (s : {s : ℝ // 0 < s}) {r : ℕ}
    (hr1 : 1 ≤ r)
    (hr : 3 + 2 * (3 : ℝ) ^ (1 - (2 : ℤ)) * Real.sqrt (d : ℝ) ≤ (3 : ℝ) ^ (r : ℕ)) :
    Algsuperdiff.Probability.RDependent (Cutoff.cutoffSampleLaw M).toMeasure
      (fun j => annularKick M s j) r :=
  rDependent_of_annulusLocalSigma M 2 hr1 hr
    fun j => measurable_annularKick_annulusRegion_local M s j

/-! ## 6. The two legs -/

/-- **The `Γ₂` leg `X_j^{(1)}`**: the inner-scale sum clamped at the deterministic
threshold `lam`. -/
def kickLegLow (M : ABKModel d) (s : {s : ℝ // 0 < s}) (lam : ℝ) (j : ℤ)
    (omega : Cutoff.CutoffSample d) : ℝ :=
  min (annularKick M s j omega) lam

/-- **The `Γ_{1/2}` leg `X_j^{(2)}`**: the overshoot of the inner-scale sum above
`lam`. -/
def kickLegHigh (M : ABKModel d) (s : {s : ℝ // 0 < s}) (lam : ℝ) (j : ℤ)
    (omega : Cutoff.CutoffSample d) : ℝ :=
  annularKick M s j omega - min (annularKick M s j omega) lam

/-- **The split is exact**: `X_j^{(1)} + X_j^{(2)}` is the inner-scale sum on the
nose, at every sample point.  Nothing is dropped and no null set enters. -/
theorem kickLegLow_add_kickLegHigh (M : ABKModel d) (s : {s : ℝ // 0 < s})
    (lam : ℝ) (j : ℤ) (omega : Cutoff.CutoffSample d) :
    kickLegLow M s lam j omega + kickLegHigh M s lam j omega = annularKick M s j omega := by
  simp only [kickLegLow, kickLegHigh]
  ring

theorem kickLegLow_le (M : ABKModel d) (s : {s : ℝ // 0 < s}) (lam : ℝ) (j : ℤ)
    (omega : Cutoff.CutoffSample d) : kickLegLow M s lam j omega ≤ lam :=
  min_le_right _ _

theorem kickLegLow_nonneg (M : ABKModel d) (s : {s : ℝ // 0 < s}) {lam : ℝ}
    (hlam : 0 ≤ lam) (j : ℤ) (omega : Cutoff.CutoffSample d) :
    0 ≤ kickLegLow M s lam j omega :=
  le_min (annularKick_nonneg M s j omega) hlam

theorem kickLegHigh_nonneg (M : ABKModel d) (s : {s : ℝ // 0 < s}) (lam : ℝ) (j : ℤ)
    (omega : Cutoff.CutoffSample d) : 0 ≤ kickLegHigh M s lam j omega := by
  have h : min (annularKick M s j omega) lam ≤ annularKick M s j omega := min_le_left _ _
  simp only [kickLegHigh]
  linarith only [h]

theorem measurable_kickLegLow (M : ABKModel d) (s : {s : ℝ // 0 < s}) (lam : ℝ)
    (j : ℤ) : Measurable (kickLegLow M s lam j) :=
  (measurable_annularKick M s j).min measurable_const

theorem measurable_kickLegHigh (M : ABKModel d) (s : {s : ℝ // 0 < s}) (lam : ℝ)
    (j : ℤ) : Measurable (kickLegHigh M s lam j) :=
  (measurable_annularKick M s j).sub
    ((measurable_annularKick M s j).min measurable_const)

end

end Algsuperdiff.Section4.Provider.MinimalScale
