/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Annular.Step1Assembly
public import LeanPool.HighContrastHomogenization.Support.Book.Ch05.Theorems.Section53.JUpperBoundWeakNorms.Additivity.CrossTerm

/-!
# PrefDischarge

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# `e.mathcalE.annular.decomp.pre` at the development's own carriers: the `hpref` slot

ABK26, Section 4.1, `e.mathcalE.annular.decomp.pre`, Step 1.  This module
discharges the last open mathematical input of the annular clause-(i)
endpoint:

```
IsAnnularDecompPre s m (jLegField M L m ω) (annularResponseMax M L m ω) C₁
```

at the **absolute** constant `C₁ = 4`, for **every** sample `ω`, every `L`, every
`m`, and every `s ∈ (0, 1/4]`.

## The three legs

`Step1.annularDecompPre_of` reduces the target to `hgrid`, `hcov` and `hcen`.  With

* `Jcov n := Σ_{j = n+1}^{m} Jann j n` (the annular cover leg), and
* `Jcen n := J(□_n)` (the centre leg, `centreResponseMax`),

the three legs are:

* **`hgrid`** -- the manuscript's cover, `3^n ℤ^d ∩ □_m = {0} ∪ ⋃_{j=n+1}^m
  (3^n ℤ^d ∩ (□_j ∖ □_{j-1}))`.  Landed as
  `Step1.exists_mem_latticeAnnulusSet`; the carrier identification of
  `CarrierIdentification` is what lets the annulus entries be recognized as
  `jLegField` entries.
* **`hcov`** -- the interchange, which `Step1Assembly.tsum_annFam_row` and
  `Step1Assembly.annDouble_eq_tsum_rows` make an **identity**: `C_cov = 1`, no
  loss.
* **`hcen`** -- the centre resummation.  Its only structural input is the
  **one-step** subadditivity of `J` at depth one and constant one, which is
  CoarseGraining's unconditional
  `Ch05.Section53.JUpperBoundWeakNorms.responseJOnCube_le_childResponseJAverageOnFamilyAtDepth`
  read at the origin cube, plus the identification of the `3^d` children of
  `□_n` as `{□_{n-1}} ∪ (3^{n-1}ℤ^d ∩ (□_n ∖ □_{n-1}))`.
  `Step1Assembly.tsum_centre_le` then closes it at `C_cen = 3`.

`C₁ = C_cov + C_cen = 1 + 3 = 4`.

## Three things worth recording

1. **No event, no probability, no regime.**  Step 1 is deterministic: the
   target holds for every `ω`.  The finiteness the closure needs comes from
   `AssemblyFeed.jLegField_le_uniform`, which is CoarseGraining's *scale-free*
   uniform response bound -- itself unconditional.  Consequently the honest
   clause-(i) event never enters, and no `m ≤ L` side condition is needed
   either.
2. Because the theorem below is proved on the *full* sample space, that
   obligation is vacuous: the `∀ ω` statement is invariant under every map of
   the sample space, `N` included.  The slot wrapper
   `annularDecompPre_slot_of_mem_annularEvent` therefore also holds at `−ω`
   whenever it holds at `ω`, with no extra input.
3. **The subadditivity is at depth one and constant one**, exactly as printed.

## Ownership note

The annulus family used here is `CarrierIdentification.annularResponseMaxPref`,
which is `FinalStitch.annularResponseMax` verbatim; that module was under
concurrent edit and could not be imported.  The two are definitionally equal, so
the endpoint's `hpref` slot is discharged from the theorem below by `exact`.

## References

* ABK26.
-/

namespace Algsuperdiff.Section4.Provider.Annular

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02
open HCPolySupport.Book.Ch05.Section53.JUpperBoundWeakNorms
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Observable

noncomputable section

variable {d : ℕ}

/-! ## Part A -- the centre leg `J(□_n)` -/

/-- **The centre leg of the Step-1 split**: the scalar response maximum of
`ã_{L,m}` on the origin cube `□_n`, `0`-floored through the singleton lattice
maximum (the entries of every `J`-maximum in Section 4.1 are `0`-floored the same
way; see `AssemblyFeed.jLegField`). -/
def centreResponseMax (M : ABKModel d) (L m : ℤ) (omega : Cutoff.CutoffSample d)
    (n : ℤ) : ℝ :=
  Proportion.fmax ({0} : Finset (Fin d → ℤ)) fun v =>
    scalarResponseMax
      ((Support.fluxCorrectedCoeffFamily M L m (originCube d m) omega).coeffOn
        (latticeCube n v))
      (Annealed.sigmaBar M m)

theorem centreResponseMax_nonneg (M : ABKModel d) (L m : ℤ)
    (omega : Cutoff.CutoffSample d) (n : ℤ) :
    0 ≤ centreResponseMax M L m omega n :=
  Proportion.fmax_nonneg _ _

theorem scalarResponseMax_origin_le_centreResponseMax (M : ABKModel d) (L m : ℤ)
    (omega : Cutoff.CutoffSample d) (n : ℤ) :
    scalarResponseMax
        ((Support.fluxCorrectedCoeffFamily M L m (originCube d m) omega).coeffOn
          (latticeCube n (0 : Fin d → ℤ))) (Annealed.sigmaBar M m)
      ≤ centreResponseMax M L m omega n :=
  Proportion.le_fmax
    (f := fun v : Fin d → ℤ => scalarResponseMax
      ((Support.fluxCorrectedCoeffFamily M L m (originCube d m) omega).coeffOn
        (latticeCube n v)) (Annealed.sigmaBar M m))
    (Finset.mem_singleton_self _)

/-- The centre leg is dominated by the full-grid `J`-leg at the same scale. -/
theorem centreResponseMax_le_jLegField (M : ABKModel d) (L m : ℤ)
    (omega : Cutoff.CutoffSample d) {n : ℤ} (hnm : n ≤ m) :
    centreResponseMax M L m omega n ≤ jLegField M L m omega n := by
  refine Proportion.fmax_le (jLegField_nonneg M L m omega n) ?_
  intro v hv
  rw [Finset.mem_singleton] at hv
  subst hv
  exact Proportion.le_fmax
    (f := fun w : Fin d → ℤ => scalarResponseMax
      ((Support.fluxCorrectedCoeffFamily M L m (originCube d m) omega).coeffOn
        (latticeCube n w)) (Annealed.sigmaBar M m))
    ((mem_latticeCubeFinset_iff hnm 0).mpr (zero_mem_latticeCubeSet n m))

/-! ## Part B -- the `3^d` children of `□_n` in the lattice enumeration -/

private theorem descendantsAtDepth_one_originCube (n : ℤ) :
    descendantsAtDepth (originCube d n) 1
      = (latticeCubeFinset d (n - 1) n).image (latticeCube (n - 1)) := by
  have hk : n - 1 ≤ (originCube d n).scale := by
    change n - 1 ≤ n
    omega
  have h1 := descendantsAtScale_eq_descendantsAtDepth (originCube d n) hk
  have h2 : Int.toNat ((originCube d n).scale - (n - 1)) = 1 := by
    have h : (originCube d n).scale - (n - 1) = (1 : ℤ) := by
      change n - (n - 1) = (1 : ℤ)
      ring
    rw [h]
    rfl
  rw [h2] at h1
  rw [← h1]
  exact descendantsAtScale_originCube_eq_image (by omega : n - 1 ≤ n)

private theorem card_latticeCubeFinset_pred (n : ℤ) :
    ((latticeCubeFinset d (n - 1) n).card : ℝ) = (3 : ℝ) ^ d := by
  rw [latticeCubeFinset_card (by omega : n - 1 ≤ n)]
  have h : (n - (n - 1)).toNat = 1 := by
    have h' : n - (n - 1) = (1 : ℤ) := by ring
    rw [h']
    rfl
  rw [h]
  push_cast
  ring

/-! ## Part C -- the one-step subadditivity of the centre leg -/

/-- **The Step-1 centre step**:

```
J(□_n) ≤ ⨍_{z' ∈ 3^{n-1}ℤ^d ∩ □_n} J(z' + □_{n-1})
       ≤ max_{z' ∈ 3^{n-1}ℤ^d ∩ (□_n ∖ □_{n-1})} J(z' + □_{n-1}) + 3^{-d} J(□_{n-1}) .
```

The first inequality is CoarseGraining's **unconditional** response
subadditivity at depth one
(`responseJOnCube_le_childResponseJAverageOnFamilyAtDepth`, zero side
hypotheses); the second splits the `3^d` children of `□_n` into the central one
`□_{n-1}` and the `3^d − 1` others, which are precisely the scale-`(n−1)`
lattice cubes of the annulus `□_n ∖ □_{n-1}` -- the manuscript's own indexing,
and the family `annularResponseMaxPref … n (n−1)` maximizes over exactly them.
The printed coefficient `1` on the maximum is what `3^{-d}·(3^d − 1) ≤ 1`
gives. -/
theorem centreResponseMax_le_annulus_add (M : ABKModel d) (L m : ℤ)
    (omega : Cutoff.CutoffSample d) (n : ℤ) :
    centreResponseMax M L m omega n
      ≤ annularResponseMaxPref M L m omega n (n - 1)
        + ((3 : ℝ) ^ d)⁻¹ * centreResponseMax M L m omega (n - 1)  := by
  classical
  have hJann0 : (0 : ℝ) ≤ annularResponseMaxPref M L m omega n (n - 1) :=
    annularResponseMaxPref_nonneg M L m omega n (n - 1)
  have hJc0 : (0 : ℝ) ≤ centreResponseMax M L m omega (n - 1) :=
    centreResponseMax_nonneg M L m omega (n - 1)
  have hrho0 : (0 : ℝ) < (3 : ℝ) ^ d := by positivity
  have hb0 : (0 : ℝ) ≤ annularResponseMaxPref M L m omega n (n - 1)
      + ((3 : ℝ) ^ d)⁻¹ * centreResponseMax M L m omega (n - 1) := by positivity
  refine Proportion.fmax_le hb0 ?_
  intro v hv
  rw [Finset.mem_singleton] at hv
  subst hv
  refine Real.sSup_le ?_ hb0
  rintro x ⟨e, he, rfl⟩
  have hsub := responseJOnCube_le_childResponseJAverageOnFamilyAtDepth
    (Support.fluxCorrectedCoeffFamily M L m (originCube d m) omega)
    (latticeCube n (0 : Fin d → ℤ)) 1
    (inverseSqrtLoad (Annealed.sigmaBar M m) e) (sqrtLoad (Annealed.sigmaBar M m) e)
  have havg : childResponseJAverageOnFamilyAtDepth
      (Support.fluxCorrectedCoeffFamily M L m (originCube d m) omega)
      (latticeCube n (0 : Fin d → ℤ)) 1
      (inverseSqrtLoad (Annealed.sigmaBar M m) e) (sqrtLoad (Annealed.sigmaBar M m) e)
      = ((descendantsAtDepth (latticeCube n (0 : Fin d → ℤ)) 1).card : ℝ)⁻¹ *
        ∑ R ∈ descendantsAtDepth (latticeCube n (0 : Fin d → ℤ)) 1,
          responseJ (cubeDomain R)
            ((Support.fluxCorrectedCoeffFamily M L m (originCube d m) omega).coeffOn R)
            (inverseSqrtLoad (Annealed.sigmaBar M m) e)
            (sqrtLoad (Annealed.sigmaBar M m) e) := rfl
  rw [havg] at hsub
  have hset : descendantsAtDepth (latticeCube n (0 : Fin d → ℤ)) 1
      = (latticeCubeFinset d (n - 1) n).image (latticeCube (n - 1)) := by
    rw [show latticeCube n (0 : Fin d → ℤ) = originCube d n from rfl]
    exact descendantsAtDepth_one_originCube n
  have hcard : ((descendantsAtDepth (latticeCube n (0 : Fin d → ℤ)) 1).card : ℝ)
      = (3 : ℝ) ^ d := by
    rw [hset, Finset.card_image_of_injective _ (latticeCube_injective (n - 1))]
    exact card_latticeCubeFinset_pred n
  have hsumImage : ∑ R ∈ descendantsAtDepth (latticeCube n (0 : Fin d → ℤ)) 1,
      responseJ (cubeDomain R)
        ((Support.fluxCorrectedCoeffFamily M L m (originCube d m) omega).coeffOn R)
        (inverseSqrtLoad (Annealed.sigmaBar M m) e)
        (sqrtLoad (Annealed.sigmaBar M m) e)
      = ∑ w ∈ latticeCubeFinset d (n - 1) n,
        responseJ (cubeDomain (latticeCube (n - 1) w))
          ((Support.fluxCorrectedCoeffFamily M L m (originCube d m) omega).coeffOn
            (latticeCube (n - 1) w))
          (inverseSqrtLoad (Annealed.sigmaBar M m) e)
          (sqrtLoad (Annealed.sigmaBar M m) e) := by
    rw [hset]
    exact Finset.sum_image fun a _ b _ hab => latticeCube_injective (n - 1) hab
  rw [hcard, hsumImage] at hsub
  refine hsub.trans ?_
  have h0mem : (0 : Fin d → ℤ) ∈ latticeCubeFinset d (n - 1) n :=
    (mem_latticeCubeFinset_iff (by omega : n - 1 ≤ n) 0).mpr
      (zero_mem_latticeCubeSet (n - 1) n)
  have hcentre : responseJ (cubeDomain (latticeCube (n - 1) (0 : Fin d → ℤ)))
      ((Support.fluxCorrectedCoeffFamily M L m (originCube d m) omega).coeffOn
        (latticeCube (n - 1) (0 : Fin d → ℤ)))
      (inverseSqrtLoad (Annealed.sigmaBar M m) e)
      (sqrtLoad (Annealed.sigmaBar M m) e)
      ≤ centreResponseMax M L m omega (n - 1) :=
    (responseJ_le_scalarResponseMax
      (Support.fluxCorrectedCoeffFamily M L m (originCube d m) omega)
      (latticeCube (n - 1) (0 : Fin d → ℤ)) (Annealed.sigmaBar M m) he).trans
      (scalarResponseMax_origin_le_centreResponseMax M L m omega (n - 1))
  have hother : ∀ w ∈ (latticeCubeFinset d (n - 1) n).erase (0 : Fin d → ℤ),
      responseJ (cubeDomain (latticeCube (n - 1) w))
        ((Support.fluxCorrectedCoeffFamily M L m (originCube d m) omega).coeffOn
          (latticeCube (n - 1) w))
        (inverseSqrtLoad (Annealed.sigmaBar M m) e)
        (sqrtLoad (Annealed.sigmaBar M m) e)
      ≤ annularResponseMaxPref M L m omega n (n - 1) := by
    intro w hw
    have hw0 : w ≠ (0 : Fin d → ℤ) := Finset.ne_of_mem_erase hw
    have hwmem : w ∈ Support.latticeCubeSet d (n - 1) n :=
      (mem_latticeCubeFinset_iff (by omega : n - 1 ≤ n) w).mp
        (Finset.mem_of_mem_erase hw)
    have hwann : w ∈ Support.latticeAnnulusSet d (n - 1) n (n - 1) :=
      ⟨hwmem, triadicLatticePoint_notMem_openCubeSet hw0⟩
    refine (responseJ_le_scalarResponseMax
      (Support.fluxCorrectedCoeffFamily M L m (originCube d m) omega)
      (latticeCube (n - 1) w) (Annealed.sigmaBar M m) he).trans ?_
    exact scalarResponseMax_le_annularResponseMaxPref M L m omega
      (by omega : n - 1 ≤ n) hwann
  have hcardErase :
      (((latticeCubeFinset d (n - 1) n).erase (0 : Fin d → ℤ)).card : ℝ)
        ≤ (3 : ℝ) ^ d := by
    rw [← card_latticeCubeFinset_pred (d := d) n]
    exact Nat.cast_le.mpr Finset.card_erase_le
  have hsumErase : ∑ w ∈ (latticeCubeFinset d (n - 1) n).erase (0 : Fin d → ℤ),
      responseJ (cubeDomain (latticeCube (n - 1) w))
        ((Support.fluxCorrectedCoeffFamily M L m (originCube d m) omega).coeffOn
          (latticeCube (n - 1) w))
        (inverseSqrtLoad (Annealed.sigmaBar M m) e)
        (sqrtLoad (Annealed.sigmaBar M m) e)
      ≤ (3 : ℝ) ^ d * annularResponseMaxPref M L m omega n (n - 1) := by
    have hcnt := Finset.sum_le_card_nsmul
      ((latticeCubeFinset d (n - 1) n).erase (0 : Fin d → ℤ))
      (fun w : Fin d → ℤ => responseJ (cubeDomain (latticeCube (n - 1) w))
        ((Support.fluxCorrectedCoeffFamily M L m (originCube d m) omega).coeffOn
          (latticeCube (n - 1) w))
        (inverseSqrtLoad (Annealed.sigmaBar M m) e)
        (sqrtLoad (Annealed.sigmaBar M m) e))
      (annularResponseMaxPref M L m omega n (n - 1)) hother
    rw [nsmul_eq_mul] at hcnt
    exact hcnt.trans (mul_le_mul_of_nonneg_right hcardErase hJann0)
  have htotal : ∑ w ∈ latticeCubeFinset d (n - 1) n,
      responseJ (cubeDomain (latticeCube (n - 1) w))
        ((Support.fluxCorrectedCoeffFamily M L m (originCube d m) omega).coeffOn
          (latticeCube (n - 1) w))
        (inverseSqrtLoad (Annealed.sigmaBar M m) e)
        (sqrtLoad (Annealed.sigmaBar M m) e)
      ≤ centreResponseMax M L m omega (n - 1)
        + (3 : ℝ) ^ d * annularResponseMaxPref M L m omega n (n - 1) := by
    rw [← Finset.add_sum_erase _ _ h0mem]
    exact add_le_add hcentre hsumErase
  have hstep := mul_le_mul_of_nonneg_left htotal (le_of_lt (inv_pos.mpr hrho0))
  have hinv : ((3 : ℝ) ^ d)⁻¹ * (3 : ℝ) ^ d = 1 := inv_mul_cancel₀ (ne_of_gt hrho0)
  have hid : ((3 : ℝ) ^ d)⁻¹ * (centreResponseMax M L m omega (n - 1)
        + (3 : ℝ) ^ d * annularResponseMaxPref M L m omega n (n - 1))
      = annularResponseMaxPref M L m omega n (n - 1)
        + ((3 : ℝ) ^ d)⁻¹ * centreResponseMax M L m omega (n - 1) := by
    have h1 : ((3 : ℝ) ^ d)⁻¹ * (centreResponseMax M L m omega (n - 1)
          + (3 : ℝ) ^ d * annularResponseMaxPref M L m omega n (n - 1))
        = ((3 : ℝ) ^ d)⁻¹ * centreResponseMax M L m omega (n - 1)
          + (((3 : ℝ) ^ d)⁻¹ * (3 : ℝ) ^ d)
            * annularResponseMaxPref M L m omega n (n - 1) := by ring
    rw [h1, hinv, one_mul]
    ring
  exact hstep.trans (le_of_eq hid)

/-! ## Part D -- the annular cover leg and the grid split -/

/-- **The annular cover leg**: the sum, over the annuli `□_j ∖ □_{j-1}` meeting
`□_m`, of the scale-`n` annulus maxima. -/
def annCoverSum (M : ABKModel d) (L m : ℤ) (omega : Cutoff.CutoffSample d)
    (n : ℤ) : ℝ :=
  ∑ j ∈ Finset.Icc (n + 1) m, annularResponseMaxPref M L m omega j n

theorem annCoverSum_nonneg (M : ABKModel d) (L m : ℤ)
    (omega : Cutoff.CutoffSample d) (n : ℤ) :
    0 ≤ annCoverSum M L m omega n :=
  Finset.sum_nonneg fun j _ => annularResponseMaxPref_nonneg M L m omega j n

/-- **The Step-1 grid split**: the full-grid `J`-maximum is at most the annular
cover leg plus the centre leg.  This is the lattice cover `3^n ℤ^d ∩ □_m = {0}
∪ ⋃_{j=n+1}^m (3^n ℤ^d ∩ (□_j ∖ □_{j-1}))` together with the carrier
identification. -/
theorem jLegField_le_annCoverSum_add_centre (M : ABKModel d) (L m : ℤ)
    (omega : Cutoff.CutoffSample d) {n : ℤ} (hnm : n ≤ m) :
    jLegField M L m omega n
      ≤ annCoverSum M L m omega n + centreResponseMax M L m omega n := by
  classical
  have hcov0 : (0 : ℝ) ≤ annCoverSum M L m omega n := annCoverSum_nonneg M L m omega n
  have hcen0 : (0 : ℝ) ≤ centreResponseMax M L m omega n :=
    centreResponseMax_nonneg M L m omega n
  refine Proportion.fmax_le (by linarith only [hcov0, hcen0]) ?_
  intro v hv
  have hvset : v ∈ Support.latticeCubeSet d n m :=
    (mem_latticeCubeFinset_iff hnm v).mp hv
  by_cases hv0 : v = (0 : Fin d → ℤ)
  · subst hv0
    refine le_trans (scalarResponseMax_origin_le_centreResponseMax M L m omega n) ?_
    linarith only [hcov0]
  · obtain ⟨j, hj1, hj2, hjann⟩ := exists_mem_latticeAnnulusSet hv0 hvset
    refine le_trans (scalarResponseMax_le_annularResponseMaxPref M L m omega
      (by omega : n ≤ j) hjann) ?_
    have hle2 : annularResponseMaxPref M L m omega j n ≤ annCoverSum M L m omega n :=
      Finset.single_le_sum
        (f := fun k : ℤ => annularResponseMaxPref M L m omega k n)
        (fun k _ => annularResponseMaxPref_nonneg M L m omega k n)
        (Finset.mem_Icc.mpr ⟨hj1, hj2⟩)
    linarith only [hle2, hcen0]

/-! ## Part E -- the summability of the annular family, and the interchange -/

/-- The annular family of `annularResponseMaxPref` against the Step-1 weight is
summable, unconditionally: it is dominated by one scale-free ellipticity constant
times a geometric weight. -/
theorem summable_annFam_annularResponseMaxPref [NeZero d] (M : ABKModel d)
    (L m : ℤ) (omega : Cutoff.CutoffSample d) {s : ℝ} (hs0 : 0 < s) :
    Summable (annFam m (fun j n =>
      (3 : ℝ) ^ (-(2 * s * ((m - n : ℤ) : ℝ)))
        * annularResponseMaxPref M L m omega j n)) := by
  refine summable_annFam_of_le
    (K := normalizedBlockResponseUniformBound (originCube d m)
      (Support.fluxCorrectedCoeffFamily M L m (originCube d m) omega)
      (isotropicComparatorMatrix (Annealed.sigmaBar M m)))
    (c := 2 * s) (by linarith only [hs0])
    (fun j n => mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (annularResponseMaxPref_nonneg M L m omega j n)) ?_
  intro j n hjm hnj
  have hB := annularResponseMaxPref_le_uniform M L m omega hjm hnj
  have hw0 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(2 * s * ((m - n : ℤ) : ℝ))) :=
    Real.rpow_nonneg (by norm_num) _
  calc (3 : ℝ) ^ (-(2 * s * ((m - n : ℤ) : ℝ)))
        * annularResponseMaxPref M L m omega j n
      ≤ (3 : ℝ) ^ (-(2 * s * ((m - n : ℤ) : ℝ)))
        * normalizedBlockResponseUniformBound (originCube d m)
          (Support.fluxCorrectedCoeffFamily M L m (originCube d m) omega)
          (isotropicComparatorMatrix (Annealed.sigmaBar M m)) :=
        mul_le_mul_of_nonneg_left hB hw0
    _ = normalizedBlockResponseUniformBound (originCube d m)
          (Support.fluxCorrectedCoeffFamily M L m (originCube d m) omega)
          (isotropicComparatorMatrix (Annealed.sigmaBar M m))
        * (3 : ℝ) ^ (-(2 * s * ((m - n : ℤ) : ℝ))) := by ring

/-- The guarded cover row **is** the `n`-row of the annular family: the
manuscript's interchange, as an identity. -/
theorem guarded_annCoverSum_eq_row (M : ABKModel d) (L m : ℤ)
    (omega : Cutoff.CutoffSample d) (s : ℝ) (n : ℤ) :
    (if n ≤ m then (3 : ℝ) ^ (-(2 * s * ((m - n : ℤ) : ℝ)))
        * annCoverSum M L m omega n else 0)
      = ∑' j : ℤ, annFam m (fun j' n' =>
          (3 : ℝ) ^ (-(2 * s * ((m - n' : ℤ) : ℝ)))
            * annularResponseMaxPref M L m omega j' n') (j, n) := by
  classical
  rw [tsum_annFam_row]
  by_cases hn : n ≤ m
  · rw [ite_eq_left hn, ite_eq_left hn]
    exact Finset.mul_sum _ _ _
  · rw [ite_eq_right hn, ite_eq_right hn]

/-! ## Part F -- the Step-1 shape at the development's carriers -/

/-- **`e.mathcalE.annular.decomp.pre` at the development's own carriers**, at the
absolute constant `C₁ = 4`.

Unconditional in the sample: no good event, no probability, no smallness regime
and no `m ≤ L` side condition.  The hypotheses are exactly the manuscript's own
typing and range data. -/
theorem annularDecompPre_jLegField [NeZero d] (dimension : 2 ≤ d) (M : ABKModel d)
    (L m : ℤ) (omega : Cutoff.CutoffSample d) {s : ℝ} (hs0 : 0 < s)
    (hs14 : s ≤ 1 / 4) :
    IsAnnularDecompPre s m (jLegField M L m omega)
      (annularResponseMaxPref M L m omega) 4 := by
  classical
  have hsum := summable_annFam_annularResponseMaxPref M L m omega hs0
  have hnine : (9 : ℝ) ≤ (3 : ℝ) ^ d := by
    have h := pow_le_pow_right₀ (show (1 : ℝ) ≤ 3 by norm_num) dimension
    have h9 : ((3 : ℝ)) ^ (2 : ℕ) = 9 := by norm_num
    rw [h9] at h
    exact h
  -- the two split legs
  have hrow := guarded_annCoverSum_eq_row M L m omega s
  have hsplit : Summable (fun n : ℤ =>
      if n ≤ m then (3 : ℝ) ^ (-(2 * s * ((m - n : ℤ) : ℝ)))
        * annCoverSum M L m omega n else 0) :=
    (summable_annFam_rows hsum).congr fun n => (hrow n).symm
  have hsplit2 : Summable (fun n : ℤ =>
      if n ≤ m then (3 : ℝ) ^ (-(2 * s * ((m - n : ℤ) : ℝ)))
        * centreResponseMax M L m omega n else 0) :=
    summable_guarded_geom hs0 (centreResponseMax_nonneg M L m omega)
      (fun n hn => (centreResponseMax_le_jLegField M L m omega hn).trans
        (jLegField_le_uniform M L m omega hn))
  -- `hcov`, an identity at `C_cov = 1`
  have hcov : ∑' n : ℤ, (if n ≤ m then (3 : ℝ) ^ (-(2 * s * ((m - n : ℤ) : ℝ)))
        * annCoverSum M L m omega n else 0)
      ≤ 1 * annDouble m (fun j n =>
          (3 : ℝ) ^ (-(2 * s * ((m - n : ℤ) : ℝ)))
            * annularResponseMaxPref M L m omega j n) := by
    rw [one_mul, annDouble_eq_tsum_rows hsum]
    exact le_of_eq (tsum_congr hrow)
  -- `hcen`, the centre closure at `C_cen = 3`
  have hcen : ∑' n : ℤ, (if n ≤ m then (3 : ℝ) ^ (-(2 * s * ((m - n : ℤ) : ℝ)))
        * centreResponseMax M L m omega n else 0)
      ≤ 3 * ∑' u : ℕ,
          (3 : ℝ) ^ (-(2 * s * ((m - (m - (u : ℤ) - 1) : ℤ) : ℝ)))
            * annularResponseMaxPref M L m omega (m - (u : ℤ)) (m - (u : ℤ) - 1) :=
    tsum_centre_le (rho := (3 : ℝ) ^ d)
      (B := normalizedBlockResponseUniformBound (originCube d m)
        (Support.fluxCorrectedCoeffFamily M L m (originCube d m) omega)
        (isotropicComparatorMatrix (Annealed.sigmaBar M m)))
      (Jcen := centreResponseMax M L m omega)
      (A := fun n => annularResponseMaxPref M L m omega n (n - 1))
      hs0 hs14 hnine
      (centreResponseMax_nonneg M L m omega)
      (fun n => annularResponseMaxPref_nonneg M L m omega n (n - 1))
      (fun n hn => (centreResponseMax_le_jLegField M L m omega hn).trans
        (jLegField_le_uniform M L m omega hn))
      (fun n hn => annularResponseMaxPref_le_uniform M L m omega hn (le_refl (n - 1)))
      (centreResponseMax_le_annulus_add M L m omega)
  exact annularDecompPre_of
    (Ccov := 1) (Ccen := 3)
    (Jcen := centreResponseMax M L m omega)
    (Jcov := annCoverSum M L m omega)
    (fun j n => annularResponseMaxPref_nonneg M L m omega j n)
    (by norm_num) hsum
    (fun n hn => jLegField_le_annCoverSum_add_centre M L m omega hn)
    hcov hcen hsplit hsplit2 (jLegField_nonneg M L m omega) (by norm_num)

/-! ## Part G -- the `hpref` slot of the clause-(i) endpoint -/

/-- **The `hpref` slot of the annular clause-(i) endpoint, discharged.**

This is the exact binder shape the endpoint carries -- the honest clause-(i) event
`𝒢₀(m; C_cg) ∩ 𝒢₁(m; s, √c⋆ γ^{−1/2})` in front, `∀ L ≥ m` inside -- at the
absolute constant `C₁ = 4`.

Both quantifiers are pure weakenings of `annularDecompPre_jLegField`: neither
the event nor `m ≤ L` is used. -/
theorem annularDecompPre_slot_of_mem_annularEvent (d : ℕ) (dimension : 2 ≤ d) :
    letI : NeZero d := ⟨by omega⟩
    ∀ (M : ABKModel d) (Ccg : ℝ) (m : ℤ) (s : {s : ℝ // 0 < s}), (s : ℝ) ≤ 1 / 4 →
      ∀ omega ∈ Support.eventG0 M Ccg m ∩
          Support.eventG1 M m (s : ℝ)
            (Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹),
        ∀ L : ℤ, m ≤ L →
          IsAnnularDecompPre (s : ℝ) m (jLegField M L m omega)
            (annularResponseMaxPref M L m omega) 4 := by
  have : NeZero d := ⟨by omega⟩
  intro M Ccg m s hs14 omega _hmem L _hL
  exact annularDecompPre_jLegField dimension M L m omega s.2 hs14

end

end Algsuperdiff.Section4.Provider.Annular
