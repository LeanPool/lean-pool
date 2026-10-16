/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.SealCaccioppoliGeometry
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.SealMeanCube
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepOddPackaging
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepSchauderComposeBoundary
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.BoundaryCoveringTrace
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepSchauderInteriorGrad

/-!
# SealOddGlue

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The flush-cube odd-harmonic comparator: the `(W)(iv)` glue

## What is proved

The boundary lane's flush scale-`n` sub-cube `K' = x' + □_n` (`x' =
flushSubCentre z m n i σ`) is a **one-met-face truncated window**: its `σeᵢ`
face lies exactly in the frontier of `□_m` and no other face of `∂□_m` is met.
For a weakly `Δ`-harmonic `v : H¹(K')` whose value decomposes as `v = w₀ + ρᵤ −
ρₕ` with `w₀ ∈ H¹₀(□_m)` (the anchor's own zero-trace witness) and `ρᵤ, ρₕ ∈
H¹₀(K')` (the two comparator correctors), this module produces — through the
proved `OneStepOddPackaging`/`OddReflectionAssembly`/Weyl chain — a **globally
pointwise-odd, classically harmonic representative** `W` on the doubled cube,
agreeing with `v` almost everywhere on `K'`
(`exists_oddHarmonic_of_flushComparator`), and composes it with the proved
flush-cube mean bound `(A)` into

```text
  |⨍_{K'} v| ≤ C(d) · ‖v − (v)_{K'}‖_{L²(K')}
```

No trace operator occurs.

## The pointwise-odd upgrade

Weyl's representative `V` agrees with the odd extension only almost everywhere.
`V` is continuous on the doubled window (harmonic functions are), the odd
extension is *pointwise* odd, and the doubled window is open and
reflection-symmetric, so `V ∘ r = −V` **everywhere** on it
(`MeasureTheory.Measure.eqOn_open_of_ae_eq`).  The symmetrization
`W := (V − V ∘ r)/2` is then globally pointwise odd, equals `V` on the doubled
window (hence is classically harmonic there and inherits the a.e.
identification), and is square-integrable.

## References

* ABK26, `l.harmonic.approximation.good.scales`, Step 2.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open HCPolySupport MeasureTheory InnerProductSpace
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

noncomputable section

variable {d : ℕ}

/-! ## 1. The flush sub-cube is a one-met-face window -/

/-- The clamp proves inside the closed centre band. -/
theorem abs_wellPlacedCentre_le {m k : ℤ} (hkm : k ≤ m) (z : Vec d) (j : Fin d) :
    |wellPlacedCentre z m k j| ≤ wellPlacedHalfGap m k := by
  have hg : 0 ≤ wellPlacedHalfGap m k := wellPlacedHalfGap_nonneg hkm
  rw [abs_le]
  constructor
  · exact le_max_left _ _
  · have h1 : min (wellPlacedHalfGap m k) (z j) ≤ wellPlacedHalfGap m k :=
      min_le_left _ _
    have h2 : max (-wellPlacedHalfGap m k) (min (wellPlacedHalfGap m k) (z j)) ≤
        max (-wellPlacedHalfGap m k) (wellPlacedHalfGap m k) := max_le_max le_rfl h1
    have h3 : max (-wellPlacedHalfGap m k) (wellPlacedHalfGap m k) =
        wellPlacedHalfGap m k := max_eq_right (by linarith only [hg])
    calc wellPlacedCentre z m k j
        ≤ max (-wellPlacedHalfGap m k) (wellPlacedHalfGap m k) := h2
      _ = wellPlacedHalfGap m k := h3

/-- Off the flush direction, the flush sub-cube meets no face of `∂□_m`. -/
theorem not_meetsFace_flushSubCentre_of_ne {n m : ℤ} (hnm : n + 2 ≤ m)
    (z : Vec d) (i : Fin d) (σ : ℝ) {j : Fin d} (hj : j ≠ i) :
    ¬ MeetsUpperFace (flushSubCentre z m n i σ) m n j ∧
      ¬ MeetsLowerFace (flushSubCentre z m n i σ) m n j := by
  have hcentre : flushSubCentre z m n i σ j = wellPlacedCentre z m (n + 2) j := by
    rw [flushSubCentre_apply, ite_eq_right hj, add_zero]
  have habs := abs_wellPlacedCentre_le (by linarith only [hnm] : n + 2 ≤ m) z j
  rw [abs_le, wellPlacedHalfGap] at habs
  have h32 : (3 : ℝ) ^ n < (3 : ℝ) ^ (n + 2) :=
    zpow_lt_zpow_right₀ (by norm_num) (by linarith only [])
  constructor
  · rw [MeetsUpperFace, hcentre]
    push Not
    linarith only [habs.2, h32]
  · rw [MeetsLowerFace, hcentre]
    push Not
    linarith only [habs.1, h32]

/-- **The met face, upper branch (`σ = 1`).** -/
theorem meetsUpperFace_flushSubCentre {n m : ℤ} (hnm : n + 2 ≤ m) {z : Vec d}
    {i : Fin d} (hover : wellPlacedHalfGap m (n + 2) < 1 * z i) :
    MeetsUpperFace (flushSubCentre z m n i 1) m n i := by
  have hlevel := flushSubCentre_faceLevel_signed (σ := 1) hnm (Or.inl rfl) hover
  rw [MeetsUpperFace]
  rw [one_mul] at hlevel
  linarith only [hlevel]

/-- **The met face, lower branch (`σ = −1`).** -/
theorem meetsLowerFace_flushSubCentre {n m : ℤ} (hnm : n + 2 ≤ m) {z : Vec d}
    {i : Fin d} (hover : wellPlacedHalfGap m (n + 2) < (-1) * z i) :
    MeetsLowerFace (flushSubCentre z m n i (-1)) m n i := by
  have hlevel := flushSubCentre_faceLevel_signed (σ := -1) hnm (Or.inr rfl) hover
  rw [MeetsLowerFace]
  have h1 : flushSubCentre z m n i (-1) i + (-1) * ((3 : ℝ) ^ n / 2) =
      (-1) * ((1 / 2 : ℝ) * (3 : ℝ) ^ m) := hlevel
  linarith only [h1]

/-! ## 2. The descent geometry: the reflected window truncates back to `K'` -/

/-- **The reflected window returns to the flush sub-cube inside `□_m`.**

`reflectedWindow x' m n ∩ □_m ⊆ (x' + □_n) ∩ □_m = K'`: the doubling happened
across the frontier face, so intersecting with the domain undoes it.  This is
what lets the anchor's global `H¹₀(□_m)` witness descend through the reflected
window as localization window. -/
theorem reflectedWindow_flush_inter_subset {n m : ℤ} (hnm : n + 2 ≤ m)
    {z : Vec d} {i : Fin d} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hover : wellPlacedHalfGap m (n + 2) < σ * z i) :
    reflectedWindow (flushSubCentre z m n i σ) m n ∩
        openCubeSet (originCube d m) ⊆
      truncatedWindow (flushSubCentre z m n i σ) m n := by
  intro y hy
  obtain ⟨hyR, hym⟩ := hy
  refine ⟨?_, hym⟩
  rw [mem_reflectedWindow_iff] at hyR
  rw [mem_image_add_openCubeSet_coord_iff]
  intro j
  have hym' := mem_openCubeSet_originCube_iff.mp hym j
  by_cases hj : j = i
  · subst hj
    have hlevel := flushSubCentre_faceLevel_signed hnm hσ hover
    rcases hσ with h1 | h1
    · subst h1
      have hup : MeetsUpperFace (flushSubCentre z m n j 1) m n j :=
        meetsUpperFace_flushSubCentre hnm hover
      have hnlow : ¬ MeetsLowerFace (flushSubCentre z m n j 1) m n j :=
        not_meetsLowerFace_of_meetsUpperFace (by linarith only [hnm]) hup
      have hlo := (hyR j).1
      rw [reflectedLo_of_not_meetsLowerFace hnlow] at hlo
      have hlo' : flushSubCentre z m n j 1 j - (1 / 2 : ℝ) * (3 : ℝ) ^ n ≤
          windowLo (flushSubCentre z m n j 1) m n j := le_max_left _ _
      rw [one_mul] at hlevel
      exact ⟨by linarith only [hlo, hlo'], by linarith only [hym'.2, hlevel]⟩
    · subst h1
      have hlow : MeetsLowerFace (flushSubCentre z m n j (-1)) m n j :=
        meetsLowerFace_flushSubCentre hnm hover
      have hhi := (hyR j).2
      have hnup : ¬ MeetsUpperFace (flushSubCentre z m n j (-1)) m n j := by
        intro hup
        exact (not_meetsLowerFace_of_meetsUpperFace
          (by linarith only [hnm]) hup) hlow
      rw [reflectedHi_of_not_meetsUpperFace hnup] at hhi
      have hhi' : windowHi (flushSubCentre z m n j (-1)) m n j ≤
          flushSubCentre z m n j (-1) j + (1 / 2 : ℝ) * (3 : ℝ) ^ n := min_le_left _ _
      have hlev : flushSubCentre z m n j (-1) j + (-1) * ((3 : ℝ) ^ n / 2) =
          (-1) * ((1 / 2 : ℝ) * (3 : ℝ) ^ m) := hlevel
      exact ⟨by linarith only [hym'.1, hlev], by linarith only [hhi, hhi']⟩
  · have hnone := not_meetsFace_flushSubCentre_of_ne hnm z i σ hj
    have hlo := (hyR j).1
    have hhi := (hyR j).2
    rw [reflectedLo_of_not_meetsLowerFace hnone.2] at hlo
    rw [reflectedHi_of_not_meetsUpperFace hnone.1] at hhi
    have hlo' : flushSubCentre z m n i σ j - (1 / 2 : ℝ) * (3 : ℝ) ^ n ≤
        windowLo (flushSubCentre z m n i σ) m n j := le_max_left _ _
    have hhi' : windowHi (flushSubCentre z m n i σ) m n j ≤
        flushSubCentre z m n i σ j + (1 / 2 : ℝ) * (3 : ℝ) ^ n := min_le_left _ _
    exact ⟨by linarith only [hlo, hlo'], by linarith only [hhi, hhi']⟩

/-- **The doubled cube sits inside the reflected window.** -/
theorem sealDouble_flush_subset_reflectedWindow {n m : ℤ} (hnm : n + 2 ≤ m)
    {z : Vec d} {i : Fin d} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hover : wellPlacedHalfGap m (n + 2) < σ * z i) :
    sealDouble (flushSubCentre z m n i σ) ((3 : ℝ) ^ n) i σ ⊆
      reflectedWindow (flushSubCentre z m n i σ) m n := by
  intro y hy
  simp only [sealDouble] at hy
  rw [mem_coordBox_iff] at hy
  rw [mem_reflectedWindow_iff]
  have h3n : (0 : ℝ) < (3 : ℝ) ^ n := zpow_pos (by norm_num) n
  have h3m : (3 : ℝ) ^ n < (3 : ℝ) ^ m :=
    zpow_lt_zpow_right₀ (by norm_num) (by linarith only [hnm])
  intro j
  have hyj := hy j
  by_cases hj : j = i
  · subst hj
    have hlevel := flushSubCentre_faceLevel_signed hnm hσ hover
    rw [ite_eq_left rfl, ite_eq_left rfl] at hyj
    rcases hσ with h1 | h1
    · subst h1
      have hup : MeetsUpperFace (flushSubCentre z m n j 1) m n j :=
        meetsUpperFace_flushSubCentre hnm hover
      have hnlow : ¬ MeetsLowerFace (flushSubCentre z m n j 1) m n j :=
        not_meetsLowerFace_of_meetsUpperFace (by linarith only [hnm]) hup
      rw [one_mul] at hlevel
      have hwlo : windowLo (flushSubCentre z m n j 1) m n j =
          flushSubCentre z m n j 1 j - (1 / 2 : ℝ) * (3 : ℝ) ^ n := by
        rw [windowLo]
        exact max_eq_left (by linarith only [hlevel, h3m])
      constructor
      · rw [reflectedLo_of_not_meetsLowerFace hnlow, hwlo]
        linarith only [hyj.1]
      · rw [reflectedHi_of_meetsUpperFace hup, hwlo]
        linarith only [hyj.2, hlevel]
    · subst h1
      have hlow : MeetsLowerFace (flushSubCentre z m n j (-1)) m n j :=
        meetsLowerFace_flushSubCentre hnm hover
      have hnup : ¬ MeetsUpperFace (flushSubCentre z m n j (-1)) m n j := by
        intro hup
        exact (not_meetsLowerFace_of_meetsUpperFace
          (by linarith only [hnm]) hup) hlow
      have hlev : flushSubCentre z m n j (-1) j + (-1) * ((3 : ℝ) ^ n / 2) =
          (-1) * ((1 / 2 : ℝ) * (3 : ℝ) ^ m) := hlevel
      have hwhi : windowHi (flushSubCentre z m n j (-1)) m n j =
          flushSubCentre z m n j (-1) j + (1 / 2 : ℝ) * (3 : ℝ) ^ n := by
        rw [windowHi]
        exact min_eq_left (by linarith only [hlev, h3m])
      constructor
      · rw [reflectedLo_of_meetsLowerFace hlow, hwhi]
        linarith only [hyj.1, hlev]
      · rw [reflectedHi_of_not_meetsUpperFace hnup, hwhi]
        linarith only [hyj.2]
  · have hnone := not_meetsFace_flushSubCentre_of_ne hnm z i σ hj
    rw [ite_eq_right hj, ite_eq_right hj] at hyj
    have hcentre : flushSubCentre z m n i σ j = wellPlacedCentre z m (n + 2) j := by
      rw [flushSubCentre_apply, ite_eq_right hj, add_zero]
    have habs := abs_wellPlacedCentre_le (by linarith only [hnm] : n + 2 ≤ m) z j
    rw [abs_le, wellPlacedHalfGap] at habs
    have h32 : (3 : ℝ) ^ n < (3 : ℝ) ^ (n + 2) :=
      zpow_lt_zpow_right₀ (by norm_num) (by linarith only [])
    have hwlo : windowLo (flushSubCentre z m n i σ) m n j =
        flushSubCentre z m n i σ j - (1 / 2 : ℝ) * (3 : ℝ) ^ n := by
      rw [windowLo]
      refine max_eq_left ?_
      rw [hcentre]
      linarith only [habs.1, h32]
    have hwhi : windowHi (flushSubCentre z m n i σ) m n j =
        flushSubCentre z m n i σ j + (1 / 2 : ℝ) * (3 : ℝ) ^ n := by
      rw [windowHi]
      refine min_eq_left ?_
      rw [hcentre]
      linarith only [habs.2, h32]
    constructor
    · rw [reflectedLo_of_not_meetsLowerFace hnone.2, hwlo]
      linarith only [hyj.1]
    · rw [reflectedHi_of_not_meetsUpperFace hnone.1, hwhi]
      linarith only [hyj.2]

/-! ## 3. The localized zero trace of the comparator difference -/

/-- **The face-only zero trace, discharged.**

The comparator difference `v = w₀ + ρᵤ − ρₕ` has localized zero trace on the
flush sub-cube through the reflected window: the anchor's `H¹₀(□_m)` witness
descends by `reflectedWindow ∩ □_m ⊆ K'`, and the two `H¹₀(K')` correctors
localize through anything. -/
theorem localizedZeroTraceFunctionOn_flushComparatorDifference {n m : ℤ}
    (hnm : n + 2 ≤ m) {z : Vec d} {i : Fin d} {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) (hover : wellPlacedHalfGap m (n + 2) < σ * z i)
    (w0 : H10Function (openCubeSet (originCube d m)))
    (rho_u rho_h : H10Function (truncatedWindow (flushSubCentre z m n i σ) m n))
    {f : Vec d → ℝ}
    (hval : ∀ y, f y = w0.toH1Function.toFun y + rho_u.toH1Function.toFun y -
      rho_h.toH1Function.toFun y) :
    LocalizedZeroTraceFunctionOn (truncatedWindow (flushSubCentre z m n i σ) m n)
      (reflectedWindow (flushSubCentre z m n i σ) m n) f := by
  have h0 : LocalizedZeroTraceFunctionOn
      (truncatedWindow (flushSubCentre z m n i σ) m n)
      (reflectedWindow (flushSubCentre z m n i σ) m n)
      w0.toH1Function.toFun :=
    localizedZeroTraceFunctionOn_of_memH10_of_inter_subset
      (isOpen_truncatedWindow _ m n)
      (truncatedWindow_subset_domain _ m n)
      (reflectedWindow_flush_inter_subset hnm hσ hover) w0
  have hu : LocalizedZeroTraceFunctionOn
      (truncatedWindow (flushSubCentre z m n i σ) m n)
      (reflectedWindow (flushSubCentre z m n i σ) m n)
      rho_u.toH1Function.toFun := localizedZeroTraceFunctionOn_of_h10_any rho_u
  have hh : LocalizedZeroTraceFunctionOn
      (truncatedWindow (flushSubCentre z m n i σ) m n)
      (reflectedWindow (flushSubCentre z m n i σ) m n)
      rho_h.toH1Function.toFun := localizedZeroTraceFunctionOn_of_h10_any rho_h
  have hsum := localizedZeroTraceFunctionOn_sub
    (localizedZeroTraceFunctionOn_add h0 hu) hh
  have hfun : f = fun y => (w0.toH1Function.toFun y + rho_u.toH1Function.toFun y) -
      rho_h.toH1Function.toFun y := by
    funext y
    exact hval y
  rw [hfun]
  exact hsum

/-! ## 4. The odd harmonic representative on the doubled window -/

/-- **The pointwise-odd classical representative, upper met face.**

From a weakly `Δ`-harmonic `v` on a one-met-face truncated window with
face-only localized zero trace, a globally pointwise-odd `W`, square-integrable
on any `D ⊆ reflectedWindow`, classically harmonic on `toEuc '' D`, agreeing
with `v` almost everywhere on the window. -/
theorem exists_oddHarmonic_of_meetsUpperFace [NeZero d] {x' : Vec d} {m k : ℤ}
    (hkm : k < m) {i : Fin d} (hup : MeetsUpperFace x' m k i)
    (hother : ∀ j, j ≠ i → ¬ MeetsUpperFace x' m k j ∧ ¬ MeetsLowerFace x' m k j)
    {D : Set (Vec d)} (hD : D ⊆ reflectedWindow x' m k)
    (v : H1Function (truncatedWindow x' m k))
    (hv : IsWeaklyHarmonicOn (truncatedWindow x' m k) v)
    (hzt : LocalizedZeroTraceFunctionOn (truncatedWindow x' m k)
      (reflectedWindow x' m k) v.toFun) :
    ∃ W : Vec d → ℝ,
      (∀ y, W (coordFaceReflection ((1 / 2 : ℝ) * (3 : ℝ) ^ m) i y) = -W y) ∧
      MemLp W 2 (volume.restrict D) ∧
      HarmonicOnNhd (W ∘ (toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d))
        ((toEuc : Vec d → EuclideanSpace ℝ (Fin d)) '' D) ∧
      W =ᵐ[volume.restrict (truncatedWindow x' m k)] v.toFun := by
  obtain ⟨w, hwval, hwgrad⟩ :=
    exists_h1_oddFaceReflection_of_meetsUpperFace hkm hup hother v hzt
  have hharm : IsWeaklyHarmonicOn (reflectedWindow x' m k) w :=
    isWeaklyHarmonicOn_reflectedWindow_of_meetsUpperFace hkm hup hother v hv w hwgrad
  obtain ⟨V, hVharm, hVmem, hVae⟩ :=
    exists_classicalCompetitor_reflectedWindow x' m k hharm
  have hwodd : ∀ y, w.toFun (coordFaceReflection ((1 / 2 : ℝ) * (3 : ℝ) ^ m) i y) =
      -w.toFun y := by
    intro y
    rw [hwval, hwval y]
    exact oddFaceExtend_comp_coordFaceReflection _ i _ y
  obtain ⟨W, hWodd, hWmem, hWharm, hWeq⟩ := exists_oddHarmonic_of_ae_eq
    (isOpen_reflectedWindow x' m k)
    (contDiff_coordFaceReflection ((1 / 2 : ℝ) * (3 : ℝ) ^ m) i).continuous
    (measurePreserving_coordFaceReflection ((1 / 2 : ℝ) * (3 : ℝ) ^ m) i)
    (fun y => coordFaceReflection_involutive ((1 / 2 : ℝ) * (3 : ℝ) ^ m) i y)
    (mem_reflectedWindow_coordFaceReflection_iff hkm hup) hVharm hVmem hVae hwodd
  refine ⟨W, hWodd, hWmem.restrict D, hWharm.mono (Set.image_mono hD), ?_⟩
  have hsub := truncatedWindow_subset_reflectedWindow x' m k
  have hVae' : V =ᵐ[volume.restrict (truncatedWindow x' m k)] w.toFun :=
    ae_restrict_of_ae_restrict_of_subset hsub hVae
  have hface : faceHalf (reflectedWindow x' m k) i ((1 / 2 : ℝ) * (3 : ℝ) ^ m) 1 =
      truncatedWindow x' m k :=
    faceHalf_reflectedWindow_of_meetsUpperFace hkm hup hother
  filter_upwards [hVae',
    self_mem_ae_restrict (isOpen_truncatedWindow x' m k).measurableSet]
    with y hy hymem
  rw [hWeq (hsub hymem), hy, hwval y]
  have hy' : y ∈ faceHalf (reflectedWindow x' m k) i ((1 / 2 : ℝ) * (3 : ℝ) ^ m) 1 := by
    rwa [hface]
  have h := oddFaceExtend_zeroExtend_faceHalf (u := v.toFun) hy'
  rwa [hface] at h

/-- **The pointwise-odd classical representative, lower met face.** -/
theorem exists_oddHarmonic_of_meetsLowerFace [NeZero d] {x' : Vec d} {m k : ℤ}
    (hkm : k < m) {i : Fin d} (hlow : MeetsLowerFace x' m k i)
    (hother : ∀ j, j ≠ i → ¬ MeetsUpperFace x' m k j ∧ ¬ MeetsLowerFace x' m k j)
    {D : Set (Vec d)} (hD : D ⊆ reflectedWindow x' m k)
    (v : H1Function (truncatedWindow x' m k))
    (hv : IsWeaklyHarmonicOn (truncatedWindow x' m k) v)
    (hzt : LocalizedZeroTraceFunctionOn (truncatedWindow x' m k)
      (reflectedWindow x' m k) v.toFun) :
    ∃ W : Vec d → ℝ,
      (∀ y, W (coordFaceReflection (-(1 / 2 : ℝ) * (3 : ℝ) ^ m) i y) = -W y) ∧
      MemLp W 2 (volume.restrict D) ∧
      HarmonicOnNhd (W ∘ (toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d))
        ((toEuc : Vec d → EuclideanSpace ℝ (Fin d)) '' D) ∧
      W =ᵐ[volume.restrict (truncatedWindow x' m k)] v.toFun := by
  obtain ⟨w, hwval, hwgrad⟩ :=
    exists_h1_oddFaceReflection_of_meetsLowerFace hkm hlow hother v hzt
  have hharm : IsWeaklyHarmonicOn (reflectedWindow x' m k) w :=
    isWeaklyHarmonicOn_reflectedWindow_of_meetsLowerFace hkm hlow hother v hv w hwgrad
  obtain ⟨V, hVharm, hVmem, hVae⟩ :=
    exists_classicalCompetitor_reflectedWindow x' m k hharm
  have hwodd : ∀ y, w.toFun (coordFaceReflection (-(1 / 2 : ℝ) * (3 : ℝ) ^ m) i y) =
      -w.toFun y := by
    intro y
    rw [hwval, hwval y]
    exact oddFaceExtend_comp_coordFaceReflection _ i _ y
  obtain ⟨W, hWodd, hWmem, hWharm, hWeq⟩ := exists_oddHarmonic_of_ae_eq
    (isOpen_reflectedWindow x' m k)
    (contDiff_coordFaceReflection (-(1 / 2 : ℝ) * (3 : ℝ) ^ m) i).continuous
    (measurePreserving_coordFaceReflection (-(1 / 2 : ℝ) * (3 : ℝ) ^ m) i)
    (fun y => coordFaceReflection_involutive (-(1 / 2 : ℝ) * (3 : ℝ) ^ m) i y)
    (mem_reflectedWindow_coordFaceReflection_iff_lower hkm hlow) hVharm hVmem hVae hwodd
  refine ⟨W, hWodd, hWmem.restrict D, hWharm.mono (Set.image_mono hD), ?_⟩
  have hsub := truncatedWindow_subset_reflectedWindow x' m k
  have hVae' : V =ᵐ[volume.restrict (truncatedWindow x' m k)] w.toFun :=
    ae_restrict_of_ae_restrict_of_subset hsub hVae
  have hface : faceHalf (reflectedWindow x' m k) i (-(1 / 2 : ℝ) * (3 : ℝ) ^ m) (-1) =
      truncatedWindow x' m k :=
    faceHalf_reflectedWindow_of_meetsLowerFace hkm hlow hother
  filter_upwards [hVae',
    self_mem_ae_restrict (isOpen_truncatedWindow x' m k).measurableSet]
    with y hy hymem
  rw [hWeq (hsub hymem), hy, hwval y]
  have hy' : y ∈ faceHalf (reflectedWindow x' m k) i (-(1 / 2 : ℝ) * (3 : ℝ) ^ m) (-1) := by
    rwa [hface]
  have h := oddFaceExtend_zeroExtend_faceHalf (u := v.toFun) hy'
  rwa [hface] at h

/-- **The `(W)(iv)` glue at the flush sub-cube.**

The two branch lemmas, entered from the flush geometry, with the localized zero
trace discharged from the three-witness decomposition. -/
theorem exists_oddHarmonic_of_flushComparator [NeZero d] {n m : ℤ}
    (hnm : n + 2 ≤ m) {z : Vec d} {i : Fin d} {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) (hover : wellPlacedHalfGap m (n + 2) < σ * z i)
    (v : H1Function (truncatedWindow (flushSubCentre z m n i σ) m n))
    (hv : IsWeaklyHarmonicOn (truncatedWindow (flushSubCentre z m n i σ) m n) v)
    (w0 : H10Function (openCubeSet (originCube d m)))
    (rho_u rho_h : H10Function (truncatedWindow (flushSubCentre z m n i σ) m n))
    (hval : ∀ y, v.toFun y = w0.toH1Function.toFun y + rho_u.toH1Function.toFun y -
      rho_h.toH1Function.toFun y) :
    ∃ W : Vec d → ℝ,
      (∀ y, W (coordFaceReflection (σ * ((1 / 2 : ℝ) * (3 : ℝ) ^ m)) i y) = -W y) ∧
      MemLp W 2 (volume.restrict
        (sealDouble (flushSubCentre z m n i σ) ((3 : ℝ) ^ n) i σ)) ∧
      HarmonicOnNhd (W ∘ (toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d))
        ((toEuc : Vec d → EuclideanSpace ℝ (Fin d)) ''
          sealDouble (flushSubCentre z m n i σ) ((3 : ℝ) ^ n) i σ) ∧
      W =ᵐ[volume.restrict (truncatedWindow (flushSubCentre z m n i σ) m n)]
        v.toFun := by
  have hzt := localizedZeroTraceFunctionOn_flushComparatorDifference hnm hσ hover
    w0 rho_u rho_h hval
  have hkm : n < m := by linarith only [hnm]
  have hD := sealDouble_flush_subset_reflectedWindow hnm hσ hover
  rcases hσ with h1 | h1
  · subst h1
    obtain ⟨W, hodd, hmem, hharm, hae⟩ := exists_oddHarmonic_of_meetsUpperFace hkm
      (meetsUpperFace_flushSubCentre hnm hover)
      (fun j hj => not_meetsFace_flushSubCentre_of_ne hnm z i 1 hj)
      hD v hv hzt
    refine ⟨W, ?_, hmem, hharm, hae⟩
    intro y
    have h1 : (1 : ℝ) * ((1 / 2 : ℝ) * (3 : ℝ) ^ m) =
        (1 / 2 : ℝ) * (3 : ℝ) ^ m := by ring
    rw [h1]
    exact hodd y
  · subst h1
    obtain ⟨W, hodd, hmem, hharm, hae⟩ := exists_oddHarmonic_of_meetsLowerFace hkm
      (meetsLowerFace_flushSubCentre hnm hover)
      (fun j hj => not_meetsFace_flushSubCentre_of_ne hnm z i (-1) hj)
      hD v hv hzt
    refine ⟨W, ?_, hmem, hharm, hae⟩
    intro y
    have h1 : (-1 : ℝ) * ((1 / 2 : ℝ) * (3 : ℝ) ^ m) =
        -(1 / 2 : ℝ) * (3 : ℝ) ^ m := by ring
    rw [h1]
    exact hodd y

/-! ## 5. The flush-cube mean bound, applied to the comparator difference -/

/-- **`(A)` discharged at the comparator difference.**

The mean of the weakly `Δ`-harmonic comparator difference over the flush
sub-cube is priced by its own oscillation, at a `d`-only constant. -/
theorem exists_abs_volumeAverage_le_normalizedL2On_flushComparator (d : ℕ)
    [NeZero d] :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {n m : ℤ} {z : Vec d} {i : Fin d} {σ : ℝ},
        n + 2 ≤ m → (σ = 1 ∨ σ = -1) →
        wellPlacedHalfGap m (n + 2) < σ * z i →
        ∀ (v : H1Function (truncatedWindow (flushSubCentre z m n i σ) m n)),
          IsWeaklyHarmonicOn (truncatedWindow (flushSubCentre z m n i σ) m n) v →
          ∀ (w0 : H10Function (openCubeSet (originCube d m)))
            (rho_u rho_h :
              H10Function (truncatedWindow (flushSubCentre z m n i σ) m n)),
            (∀ y, v.toFun y = w0.toH1Function.toFun y +
              rho_u.toH1Function.toFun y - rho_h.toH1Function.toFun y) →
            |volumeAverage ((fun y => flushSubCentre z m n i σ + y) ''
                openCubeSet (originCube d n)) v.toFun| ≤
              C * normalizedL2On ((fun y => flushSubCentre z m n i σ + y) ''
                  openCubeSet (originCube d n))
                (fun y => v.toFun y -
                  volumeAverage ((fun y => flushSubCentre z m n i σ + y) ''
                    openCubeSet (originCube d n)) v.toFun) := by
  classical
  obtain ⟨C, hC0, hC⟩ := exists_abs_le_normalizedL2On_sealFlushSubCube d
  refine ⟨C, hC0, ?_⟩
  intro n m z i σ hnm hσ hover v hv w0 rho_u rho_h hval
  obtain ⟨W, hodd, hmem, hharm, hae⟩ :=
    exists_oddHarmonic_of_flushComparator hnm hσ hover v hv w0 rho_u rho_h hval
  have hcentre : sealFlushSubCentre z m (n + 2) n i σ = flushSubCentre z m n i σ :=
    rfl
  have hharm' : HarmonicOnNhd ((fun y => W y -
      volumeAverage ((fun y => flushSubCentre z m n i σ + y) ''
        openCubeSet (originCube d n)) v.toFun) ∘
      (toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d))
      ((toEuc : Vec d → EuclideanSpace ℝ (Fin d)) ''
        sealDouble (sealFlushSubCentre z m (n + 2) n i σ) ((3 : ℝ) ^ n) i σ) := by
    rw [hcentre]
    have hsub := harmonicOnNhd_sub_const hharm
      (volumeAverage ((fun y => flushSubCentre z m n i σ + y) ''
        openCubeSet (originCube d n)) v.toFun)
    have hfun : (fun e => (W ∘ (toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d)) e -
        volumeAverage ((fun y => flushSubCentre z m n i σ + y) ''
          openCubeSet (originCube d n)) v.toFun) = (fun y => W y -
        volumeAverage ((fun y => flushSubCentre z m n i σ + y) ''
          openCubeSet (originCube d n)) v.toFun) ∘
        (toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d) := by
      funext e
      simp [Function.comp]
    rwa [hfun] at hsub
  have hmem' : MemLp W 2 (volume.restrict
      (sealDouble (sealFlushSubCentre z m (n + 2) n i σ) ((3 : ℝ) ^ n) i σ)) := by
    rw [hcentre]
    exact hmem
  have hA := hC m (n + 2) n z i σ W
    (volumeAverage ((fun y => flushSubCentre z m n i σ + y) ''
      openCubeSet (originCube d n)) v.toFun)
    hnm hσ hover hodd hmem' hharm'
  have hKtw : truncatedWindow (flushSubCentre z m n i σ) m n =
      (fun y => flushSubCentre z m n i σ + y) '' openCubeSet (originCube d n) :=
    truncatedWindow_eq_flushSubCube hnm z i hσ
  have haeK : W =ᵐ[volume.restrict ((fun y => flushSubCentre z m n i σ + y) ''
      openCubeSet (originCube d n))] v.toFun := by
    rw [← hKtw]
    exact hae
  have hnorm : normalizedL2On ((fun y => sealFlushSubCentre z m (n + 2) n i σ + y) ''
      openCubeSet (originCube d n))
      (fun y => W y - volumeAverage ((fun y => flushSubCentre z m n i σ + y) ''
        openCubeSet (originCube d n)) v.toFun) =
      normalizedL2On ((fun y => flushSubCentre z m n i σ + y) ''
        openCubeSet (originCube d n))
      (fun y => v.toFun y - volumeAverage ((fun y => flushSubCentre z m n i σ + y) ''
        openCubeSet (originCube d n)) v.toFun) := by
    rw [hcentre]
    refine normalizedL2On_congr_ae ?_
    filter_upwards [haeK] with y hy
    rw [hy]
  rw [hnorm] at hA
  exact hA

end

end Algsuperdiff.Section4.Provider.ExcessDecay
