/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.BadEvents.LambdaLocal
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Probability.AnnulusSeparation
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Localize.SensitivitySwitch
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Proportion.Ycal

/-!
# TranslatedLocality

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Translated-cube locality of the multiscale-ellipticity literal

ABK26, §4.1, `l.good.scales.ratio.lambda`, the two-dependence step: the per-scale
atoms `𝒴_n` are asserted to be `2`-dependent.  The independence producer
consumes that assertion as *locality*: `𝒴_n` must be measurable for the
integral-local information `Cutoff.cutoffSampleLocalSigma M (n−2)
(annulusRegion d n)` of the annulus it reads.  This module supplies that
locality, unconditionally.

## The bridge

The `𝒢₀` atom is written by translating the *sample*, never the cube:

```
λ_{γ,2}^{-1}(z+□_j; a_c)  :=  cutoffLowerEllipticityInvLiteral M j c γ 2
                                 (translateCutoffSample z ω) ,
```

while the proved locality statement
`BadEvents.measurable_cubeLowerEllipticityInvLiteral_cutoffSampleLocal` is
about the *cube* reading `cubeLowerEllipticityInvLiteral M Q c γ 2 ω` at a
genuine `TriadicCube Q`.  The two are identified by the proved pathwise swap
`BadEvents.cubeLowerEllipticityInvLiteral_translateCutoffSample`, whose
mathematical content is the Chapter 2 translation covariance
`BadEvents.lambdaSq_cutoff_translateCutoffSample` of the actual coefficient
cutoff.

The decisive point is that the centres occurring in §4.1 are **triadic lattice
points** `z = 3^j v`, so `z + □_j` *is* the triadic cube `⟨j, v⟩`
(`Localize.latticeCube`, whose `triadicCubeShift` is `Support.triadicLatticePoint`).
No σ-algebra on a translated region, and no translated-region bookkeeping, is
needed: the cube reading is available at the honest cube, and the locality
lemma applies to it verbatim.  Arbitrary real translates `z` are *not* covered
and are not needed anywhere in §4.1.

## The chain

1. `cubeSet_latticeCube_subset_annulusRegion` — the geometry: a lattice cube
   `3^j v + □_j` whose centre lies in the open annulus `□_n ∖ □_{n−1}` has its
   whole (half-open) realization inside `annulusRegion d n`, for `j ≤ n−1`.
   This is the proved no-enlargement fact
   `Probability.mem_annulusRegion_of_le_triadicLatticePoint`, read at the cube.
2. `cutoffLowerEllipticityInvLiteral_translateCutoffSample_latticeCube` — the
   core identity, in the orientation the Section 4 carriers need.
3. `measurable_cutoffLowerEllipticityInvLiteral_translate_cutoffSampleLocal` —
   the general export: the translated-sample reading of the `λ`-literal at the
   lattice cube `⟨j, v⟩`, at cutoff level `c`, is
   `cutoffSampleLocalSigma M m U`-measurable for every `U ⊇ cubeSet ⟨j, v⟩` and
   every `m ≥ c`.  The domain scale `j` and the cutoff scale `c` are
   independent parameters, so the `𝒢₂` reading `z + □_n` at `a_{n−2}` is
   covered as well.
4. `measurable_cgExcess_annulusRegion_local` and
   `measurable_Ycal_annulusRegion_local` — the `𝒢₀` instances, ending at the
   `hloc` slot of `columnsIndep_Ycal`.

## The corrected reduction (recorded)

Reducing the `𝒴`-locality to a per-cube slot quantified over **every** index
vector `v : Fin d → ℤ` gives a slot that is not dischargeable, and not because
of a missing lemma: a cube `3^{k−2}v + □_{k−2}` with `v` outside the annulus
enumeration is genuinely not read by `annulusRegion d n`.  The `0`-floored
maximum only ever evaluates the bracket on `latticeAnnulusFinset d (k−2) n
(n−1)`, so the honest reduction quantifies over the members of that `Finset`;
that is `measurable_Ycal_local_of_annulusFinset` below, on top of the restricted
`measurable_fmax_of_mem`.  The endpoint delivered is unconditional.

## Scope

Provider material: proved local helpers.  Every statement is pointwise in the
sample; nothing is `a.e.` and no hypothesis is added to any consumer.

## References

* ABK26, `l.good.scales.ratio.lambda`.
* `d.good.event.for.lambda`, (`𝒢₀`).
-/

namespace Algsuperdiff.Section4.Provider.Proportion

open Algsuperdiff.Section3
open Algsuperdiff.Section3.Provider.BadEvents
open HCPolySupport HCPolySupport.Book MeasureTheory
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Probability

noncomputable section

variable {d : ℕ}

/-! ## 1. The geometry: a lattice cube of the annulus stays in the annulus -/

/-- **The read cube sits inside the annulus region.**  If the lattice point
`3^j v` lies in the open triadic annulus `□_n ∖ □_{n−1}` and `j ≤ n − 1`, then
the entire half-open realization of the triadic cube `⟨j, v⟩ = 3^j v + □_j` is
contained in `annulusRegion d n`.

This is the cube-level reading of the proved no-enlargement fact
`Probability.mem_annulusRegion_of_le_triadicLatticePoint`: the cubes read by
the per-scale atom *tile* the annulus and do not stick out of it, so no
fattening of the observation region — and hence no degradation of the
separation count — is incurred. -/
theorem cubeSet_latticeCube_subset_annulusRegion {j n : ℤ} (hj : j ≤ n - 1)
    {v : Fin d → ℤ} (hv : v ∈ Support.latticeAnnulusSet d j n (n - 1)) :
    cubeSet (Localize.latticeCube j v) ⊆ annulusRegion d n := by
  intro x hx
  refine mem_annulusRegion_of_le_triadicLatticePoint hj hv fun i => ?_
  have hxi := hx i
  have hlow : ((v i : ℝ) - (1 / 2 : ℝ)) * (3 : ℝ) ^ j ≤ x i := hxi.1
  have hupp : x i < ((v i : ℝ) + (1 / 2 : ℝ)) * (3 : ℝ) ^ j := hxi.2
  have hpt : Support.triadicLatticePoint j v i = (3 : ℝ) ^ j * (v i : ℝ) := rfl
  rw [hpt, abs_le]
  constructor
  · linarith only [hlow]
  · linarith only [hupp]

/-! ## 2. The core identity at a triadic lattice point -/

/-- **The translated-sample reading is the translated-cube reading.**

```
λ_{s,q}^{-1}(□_j; a_c(τ_{3^j v} ω))  =  λ_{s,q}^{-1}(3^j v + □_j; a_c(ω)) ,
```

i.e. the `λ`-functional of the translated field on the centred cube equals the
functional of the field on the translated cube.  This is the proved pathwise
swap `BadEvents.cubeLowerEllipticityInvLiteral_translateCutoffSample` read at
the lattice cube `⟨j, v⟩`, whose base point is `Support.triadicLatticePoint j
v` and whose scale is `j`; its own content is the Chapter 2 translation
covariance of the actual coefficient cutoff.  It holds at every sample point,
for every cutoff level `c` and every admissible exponent, with no hypothesis. -/
theorem cutoffLowerEllipticityInvLiteral_translateCutoffSample_latticeCube
    (M : ABKModel d) (j cutoffScale : ℤ) (v : Fin d → ℤ) (s : ℝ)
    (q : CoarseEllipticityExponent) (omega : Cutoff.CutoffSample d) :
    Observable.cutoffLowerEllipticityInvLiteral M j cutoffScale s q
        (Cutoff.translateCutoffSample (Support.triadicLatticePoint j v) omega) =
      cubeLowerEllipticityInvLiteral M (Localize.latticeCube j v) cutoffScale s q omega := by
  have h := cubeLowerEllipticityInvLiteral_translateCutoffSample M
    (Localize.latticeCube j v) cutoffScale s q omega
  rw [Localize.triadicCubeShift_latticeCube, Localize.latticeCube_scale] at h
  exact h.symm

/-! ## 3. The general locality export -/

/-- **The `λ`-literal read at a translated cube is integral-local.**

For a triadic lattice centre `z = 3^j v`, an observation region `U` containing
the closed cube `z + □_j`, and any shell index `m` at or above the cutoff level
`c`, the translated-sample reading

```
ω ↦ λ_{s,q}^{-1}(z + □_j; a_c(ω))  =  (cutoffLowerEllipticityInvLiteral M j c s q)
                                          (translateCutoffSample z ω)
```

is `Cutoff.cutoffSampleLocalSigma M m U`-measurable.

Nothing is `a.e.`: the literal is the genuinely measurable observable, and the
locality is the proved
`BadEvents.measurable_cubeLowerEllipticityInvLiteral_cutoffSampleLocal`, whose
descendant tree never leaves the closed cube.  The domain scale `j` and the
cutoff level `c` are independent, so this covers the `𝒢₀` reading (`j = c`) and
the `𝒢₂`-style reading (`c = j − 2`) alike. -/
theorem measurable_cutoffLowerEllipticityInvLiteral_translate_cutoffSampleLocal
    (M : ABKModel d) (j cutoffScale m : ℤ) (v : Fin d → ℤ) {U : Set (Vec d)}
    (hU : cubeSet (Localize.latticeCube j v) ⊆ U) (hm : cutoffScale ≤ m)
    {s : ℝ} (hs : 0 < s) (q : CoarseEllipticityExponent) :
    Measurable[Cutoff.cutoffSampleLocalSigma M m U]
      (fun omega => Observable.cutoffLowerEllipticityInvLiteral M j cutoffScale s q
        (Cutoff.translateCutoffSample (Support.triadicLatticePoint j v) omega)) := by
  have hrw : (fun omega => Observable.cutoffLowerEllipticityInvLiteral M j cutoffScale s q
        (Cutoff.translateCutoffSample (Support.triadicLatticePoint j v) omega))
      = cubeLowerEllipticityInvLiteral M (Localize.latticeCube j v) cutoffScale s q :=
    funext fun omega =>
      cutoffLowerEllipticityInvLiteral_translateCutoffSample_latticeCube M j cutoffScale v
        s q omega
  rw [hrw]
  exact (measurable_cubeLowerEllipticityInvLiteral_cutoffSampleLocal M cutoffScale
    (Localize.latticeCube j v) hU hs q).mono
    (cutoffSampleLocalSigma_mono M hm (subset_refl U)) le_rfl

/-! ## 4. The `𝒢₀` bracket at an annulus centre -/

/-- **The `𝒢₀` bracket at a lattice centre of the annulus is local.**  For a
centre enumerated by `Support.latticeAnnulusSet d j n (n−1)` with `j ≤ n − 2`,
the excess `𝒳_j(3^j v)` is measurable for the integral-local information of
`annulusRegion d n` at shell index `n − 2`.

The scale hypothesis `j ≤ n − 2` is exactly what the `𝒢₀` lane supplies
(`j = k − 2` with `k ≤ n`): it gives both the geometric room `j ≤ n − 1` and the
shell-index comparison the local σ-field needs. -/
theorem measurable_cgExcess_annulusRegion_local (M : ABKModel d) (Ccg : ℝ) {n j : ℤ}
    (hj : j ≤ n - 2) {v : Fin d → ℤ}
    (hv : v ∈ Support.latticeAnnulusSet d j n (n - 1)) :
    Measurable[Cutoff.cutoffSampleLocalSigma M (n - 2) (annulusRegion d n)]
      (fun omega => Localize.cgExcess M Ccg j (Support.triadicLatticePoint j v) omega) := by
  let : MeasurableSpace (Cutoff.CutoffSample d) :=
    Cutoff.cutoffSampleLocalSigma M (n - 2) (annulusRegion d n)
  have hlit := measurable_cutoffLowerEllipticityInvLiteral_translate_cutoffSampleLocal
    M j j (n - 2) v (cubeSet_latticeCube_subset_annulusRegion (by omega) hv) hj
    M.shellPrefix.gamma_pos Support.coarseEllipticityExponentTwo
  have hrw : (fun omega => Localize.cgExcess M Ccg j (Support.triadicLatticePoint j v) omega)
      = fun omega => max ((Annealed.sigmaBar M (j - 1) : ℝ) *
          Observable.cutoffLowerEllipticityInvLiteral M j j M.gamma
              Support.coarseEllipticityExponentTwo
              (Cutoff.translateCutoffSample (Support.triadicLatticePoint j v) omega) -
            Ccg) 0 := rfl
  rw [hrw]
  exact ((hlit.const_mul _).sub_const _).max measurable_const

/-! ## 5. The annulus maximum -/

/-- **Measurability of the `0`-floored maximum from the members alone.**  The
proved `measurable_fmax` asks for measurability of *every* index; the maximum
only ever evaluates the members of `S`, and that is all the §4.1 lattice maxima
can supply (a centre outside the annulus enumeration reads a cube the annulus
does not contain). -/
theorem measurable_fmax_of_mem {Omega iota : Type*} [MeasurableSpace Omega]
    (S : Finset iota) {f : iota → Omega → ℝ} (hf : ∀ i ∈ S, Measurable (f i)) :
    Measurable fun omega => fmax S (fun i => f i omega) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simpa only [fmax_empty] using (measurable_const : Measurable fun _ : Omega => (0 : ℝ))
  | @insert i S _hi ih =>
      simp only [fmax_insert]
      exact (((hf i (Finset.mem_insert_self i S)).max measurable_const).max
        (ih fun j hj => hf j (Finset.mem_insert_of_mem hj)))

/-! ## 6. The `𝒴`-locality: the `hloc` slot of the concentration lane -/

/-- **The corrected per-cube reduction.**  `𝒴_n` is local as soon as the `𝒢₀`
bracket is local at each centre the annulus maxima actually enumerate.  The
quantifier ranges over the members of `latticeAnnulusFinset d (k−2) n (n−1)`,
which is what the `0`-floored maximum reads; quantifying over all
`v : Fin d → ℤ` asks for locality at cubes the annulus does not contain, and is
not dischargeable. -/
theorem measurable_Ycal_local_of_annulusFinset (M : ABKModel d) (Ccg sprime : ℝ) (n : ℤ)
    (hatomloc : ∀ k : ℤ, k ≤ n → ∀ v ∈ latticeAnnulusFinset d (k - 2) n (n - 1),
      Measurable[Cutoff.cutoffSampleLocalSigma M (n - 2) (annulusRegion d n)]
        (fun omega => Localize.cgExcess M Ccg (k - 2)
          (Support.triadicLatticePoint (k - 2) v) omega)) :
    Measurable[Cutoff.cutoffSampleLocalSigma M (n - 2) (annulusRegion d n)]
      (Ycal M Ccg sprime n) := by
  let : MeasurableSpace (Cutoff.CutoffSample d) :=
    Cutoff.cutoffSampleLocalSigma M (n - 2) (annulusRegion d n)
  refine measurable_wsum fun j => ?_
  exact measurable_fmax_of_mem _ fun v hv => hatomloc (n - (j : ℤ)) (by omega) v hv

/-- **`𝒴_n` is local — unconditionally.**  This is the `hloc` slot of
`columnsIndep_Ycal`: the `𝒢₀` score field at index `n`
is measurable for the integral-local information
`cutoffSampleLocalSigma M (n−2) (annulusRegion d n)` of the annulus it reads.

Together with `Probability.separatedBy_annulusRegion_of_gap` this is the honest
content's one-line `2`-dependence assertion: the atoms are measurable for
regions that are separated at the shared-shell threshold, which is exactly what
`iIndepFun_of_local_cutoffSample` consumes. -/
theorem measurable_Ycal_annulusRegion_local (M : ABKModel d) (Ccg sprime : ℝ) (n : ℤ) :
    Measurable[Cutoff.cutoffSampleLocalSigma M (n - 2) (annulusRegion d n)]
      (Ycal M Ccg sprime n) :=
  measurable_Ycal_local_of_annulusFinset M Ccg sprime n fun k hk v hv =>
    measurable_cgExcess_annulusRegion_local M Ccg (by omega)
      ((mem_latticeAnnulusFinset_iff (by omega : k - 2 ≤ n)).1 hv)

end

end Algsuperdiff.Section4.Provider.Proportion
