/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Annular.Step1
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Annular.AssemblyFeed
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Annular.ResponseTransport
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Proportion.LatticeCount

/-!
# CarrierIdentification

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The two `ã_{L,m}` carriers of Section 4.1 carry the same response functional

ABK26, Section 4.1, (`ã_{L,m} := a_L − (k_L − k_m)_{□_m}`),
(`e.mathcalE.annular.decomp.pre`).

Section 4.1 reads the response functional `J(z+□_n, …; ã_{L,m})` through **two**
different Chapter 2 triadic coefficient families:

* `subConstCutoffTriadicCoeffFamily M L C hC ω` at `C := (k_L − k_m)_{□_m}` —
  the hand-built family of `SubConstFamily`, the object the ugly chain and hence
  the annulus maximum of `FinalStitch` is built on.

Their **fields** are literally the same function of `x`
(`Support.fluxCorrectedField_apply` and `subConstCutoffField_apply` both read
`a_L(x) − C`), but the two `TriadicCoeffFamily` wrappers are constructed
differently, so no `responseJ` identification was available.  This module
supplies it.

## The route

The missing input is the `Ch02.CoeffOn.AEEq` between the two `coeffOn` values.
Both sides have a **definitional** `coeffOn`-characterization:

* `subConstCutoffTriadicCoeffFamily_coeffOn_toCoeffField` (this repository) gives
  `((… C hC ω).coeffOn Q).toCoeffField = subConstCutoffField M L C ω` by `rfl`.

So the `A is `Filter.Eventually.of_forall` applied to a pointwise field
identity, and `Ch02.responseJ_eq_ofA transports every response value; the
supremum over the unit sphere follows.  No new device and no new mathematics:
this is a definitional unfolding on both sides.

## Ownership note

`annularResponseMaxPref` is the canonical annulus response family.
`FinalStitch.annularResponseMax` reuses it through an abbreviation, so both
names reduce to the same lattice maximum.

## References

* ABK26.
-/

namespace Algsuperdiff.Section4.Provider.Annular

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02
open Algsuperdiff.Section3

noncomputable section

variable {d : ℕ}

/-! ## Part A -- the scalar response maximum respects a.e. equality -/

/-- **The scalar response maximum only sees the coefficient a.e.**  Every element
of `scalarResponseSet` is a `responseJ` value, and `Ch02.responseJ_eq_ofAEEq`
identifies those; the two value sets are therefore equal, hence so are their
suprema.

(`TransposeDischarge.scalarResponseMax_congr_aeeq` is the same statement; it is
re-derived here because that module was under concurrent edit. -/
theorem scalarResponseMax_eq_of_coeffOn_aeeq {U : Domain d} {a b : CoeffOn U}
    (h : CoeffOn.AEEq a b) (sigma : Observable.PositiveScalar) :
    scalarResponseMax a sigma = scalarResponseMax b sigma := by
  unfold scalarResponseMax scalarResponseSet
  refine congrArg sSup (Set.ext fun x => ?_)
  constructor
  · rintro ⟨e, he, rfl⟩
    exact ⟨e, he, responseJ_eq_ofAEEq h _ _⟩
  · rintro ⟨e, he, rfl⟩
    exact ⟨e, he, responseJ_eq_ofAEEq h.symm _ _⟩

/-! ## Part B -- the two `ã_{L,m}` families agree on every lattice cube -/

/-- **A6c finding (f), closed.**  The Chapter 4 dependent family of the
flux-corrected carrier field and the hand-built family of `a_L − C` at
`C = (k_L − k_m)_{□_m}` have a.e. equal coefficient objects on every scale-`n`
lattice cube.

The proof is a pointwise field identity: both `toCoeffField` values reduce definitionally,
one through
`Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField_coeffOn_toCoeffField` and
`Support.fluxCorrectedRegField_toFun`, the other through
`subConstCutoffTriadicCoeffFamily_coeffOn_toCoeffField`, to `x ↦ a_L(x) − (k_L −
k_m)_{□_m}`. -/
theorem fluxCorrectedCoeffFamily_coeffOn_aeeq_subConstCutoff (M : ABKModel d)
    (L m : ℤ) (omega : Cutoff.CutoffSample d) (n : ℤ) (v : Fin d → ℤ) :
    CoeffOn.AEEq
      ((Support.fluxCorrectedCoeffFamily M L m (originCube d m) omega).coeffOn
        (latticeCube n v))
      ((subConstCutoffTriadicCoeffFamily M L
        (Support.fluxIncrementAverage M L m (originCube d m) omega)
        (matTranspose_fluxIncrementAverage M L m (originCube d m) omega)
        omega).coeffOn (⟨n, v⟩ : TriadicCube d)) := by
  refine Filter.Eventually.of_forall fun x => ?_
  change (Support.fluxCorrectedRegField M L m (originCube d m) omega).toFun x = _
  rw [Support.fluxCorrectedRegField_toFun]
  rfl

/-- **The response-level carrier identification.**  The scalar response maximum
of the `jLegField` carrier at the lattice cube `3^n v + □_n` equals the scalar
response maximum of the annulus carrier at the same cube. -/
theorem scalarResponseMax_fluxCorrected_eq_subConstCutoff (M : ABKModel d)
    (L m : ℤ) (omega : Cutoff.CutoffSample d) (n : ℤ) (v : Fin d → ℤ)
    (sigma : Observable.PositiveScalar) :
    scalarResponseMax
        ((Support.fluxCorrectedCoeffFamily M L m (originCube d m) omega).coeffOn
          (latticeCube n v)) sigma
      = scalarResponseMax
        ((subConstCutoffTriadicCoeffFamily M L
          (Support.fluxIncrementAverage M L m (originCube d m) omega)
          (matTranspose_fluxIncrementAverage M L m (originCube d m) omega)
          omega).coeffOn (⟨n, v⟩ : TriadicCube d)) sigma :=
  scalarResponseMax_eq_of_coeffOn_aeeq
    (fluxCorrectedCoeffFamily_coeffOn_aeeq_subConstCutoff M L m omega n v) sigma

/-! ## Part C -- the annulus response family -/

/-- **The `Jann` family of `e.mathcalE.annular.decomp.pre`**: the maximum, over the
scale-`n` lattice cubes of the annulus `□_j ∖ □_{j−1}`, of the scalar response
maximum of `ã_{L,m}`.

`FinalStitch.annularResponseMax` is a compatibility name for this family. -/
def annularResponseMaxPref (M : ABKModel d) (L m : ℤ)
    (omega : Cutoff.CutoffSample d) (j n : ℤ) : ℝ :=
  Proportion.fmax (Proportion.latticeAnnulusFinset d n j (j - 1)) fun v =>
    scalarResponseMax
      ((subConstCutoffTriadicCoeffFamily M L
        (Support.fluxIncrementAverage M L m (originCube d m) omega)
        (matTranspose_fluxIncrementAverage M L m (originCube d m) omega)
        omega).coeffOn (⟨n, v⟩ : TriadicCube d))
      (Annealed.sigmaBar M m)

theorem annularResponseMaxPref_nonneg (M : ABKModel d) (L m : ℤ)
    (omega : Cutoff.CutoffSample d) (j n : ℤ) :
    0 ≤ annularResponseMaxPref M L m omega j n :=
  Proportion.fmax_nonneg _ _

/-- **The annulus family dominates each of its `jLegField`-carrier entries.**
For a lattice index in the annulus `□_j ∖ □_{j−1}`, the flux-corrected scalar
response maximum at that cube is at most the annulus maximum. -/
theorem scalarResponseMax_le_annularResponseMaxPref (M : ABKModel d) (L m : ℤ)
    (omega : Cutoff.CutoffSample d) {j n : ℤ} (hnj : n ≤ j) {v : Fin d → ℤ}
    (hv : v ∈ Support.latticeAnnulusSet d n j (j - 1)) :
    scalarResponseMax
        ((Support.fluxCorrectedCoeffFamily M L m (originCube d m) omega).coeffOn
          (latticeCube n v)) (Annealed.sigmaBar M m)
      ≤ annularResponseMaxPref M L m omega j n := by
  rw [scalarResponseMax_fluxCorrected_eq_subConstCutoff M L m omega n v]
  exact Proportion.le_fmax
    (f := fun w : Fin d → ℤ => scalarResponseMax
      ((subConstCutoffTriadicCoeffFamily M L
        (Support.fluxIncrementAverage M L m (originCube d m) omega)
        (matTranspose_fluxIncrementAverage M L m (originCube d m) omega)
        omega).coeffOn (⟨n, w⟩ : TriadicCube d))
      (Annealed.sigmaBar M m))
    ((Proportion.mem_latticeAnnulusFinset_iff (d := d) hnj).mpr hv)

/-- **The annulus family is dominated by the full-grid `J`-leg.**  Every annulus
index of `□_j ∖ □_{j−1}` with `j ≤ m` is a lattice index of `□_m`, so the
annulus maximum is at most `AssemblyFeed.jLegField` at the same scale. -/
theorem annularResponseMaxPref_le_jLegField (M : ABKModel d) (L m : ℤ)
    (omega : Cutoff.CutoffSample d) {j n : ℤ} (hjm : j ≤ m) (hnj : n ≤ j - 1) :
    annularResponseMaxPref M L m omega j n ≤ jLegField M L m omega n := by
  refine Proportion.fmax_le (jLegField_nonneg M L m omega n) ?_
  intro v hv
  have hvset : v ∈ Support.latticeAnnulusSet d n j (j - 1) :=
    (Proportion.mem_latticeAnnulusFinset_iff (d := d) (by omega : n ≤ j)).mp hv
  have hvcube : v ∈ Support.latticeCubeSet d n m :=
    openCubeSet_originCube_subset hjm hvset.1
  rw [← scalarResponseMax_fluxCorrected_eq_subConstCutoff M L m omega n v]
  exact Proportion.le_fmax
    (f := fun w : Fin d → ℤ => scalarResponseMax
      ((Support.fluxCorrectedCoeffFamily M L m (originCube d m) omega).coeffOn
        (latticeCube n w)) (Annealed.sigmaBar M m))
    ((mem_latticeCubeFinset_iff (by omega : n ≤ m) v).mpr hvcube)

/-- **The annulus family is uniformly bounded**, by the single cube-`□_m`
ellipticity constant of `AssemblyFeed.jLegField_le_uniform`.  Unconditional: no
event, no probability, no regime. -/
theorem annularResponseMaxPref_le_uniform [NeZero d] (M : ABKModel d) (L m : ℤ)
    (omega : Cutoff.CutoffSample d) {j n : ℤ} (hjm : j ≤ m) (hnj : n ≤ j - 1) :
    annularResponseMaxPref M L m omega j n
      ≤ normalizedBlockResponseUniformBound (originCube d m)
          (Support.fluxCorrectedCoeffFamily M L m (originCube d m) omega)
          (Observable.isotropicComparatorMatrix (Annealed.sigmaBar M m)) :=
  (annularResponseMaxPref_le_jLegField M L m omega hjm hnj).trans
    (jLegField_le_uniform M L m omega (by omega : n ≤ m))

end

end Algsuperdiff.Section4.Provider.Annular
