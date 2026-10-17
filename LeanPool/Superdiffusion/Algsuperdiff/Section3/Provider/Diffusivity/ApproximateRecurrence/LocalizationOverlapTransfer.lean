/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.LocalizationOverlapCount

/-!
# LocalizationOverlapTransfer

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Provider: the bounded-overlap covering transfer for the meso windows

Source displays in ABK26:

* `e.nablaw.oscillations` (label; display), whose outer window is `z +
  cu_{m-h}`;
* `e.lower.bound.oscillations` (label; display), which averages over the mesh
  `z in 3^n Zd cap cu_K` and is deduced "by `e.nablaw.in.L.eight`" -- a
  statement about the single global normalized norm on `cu_K`;
* `e.nablaw.in.L.eight` (label; display).

The passage from the global quantity on `cu_K` to the mesh average of window
quantities is the covering step that the manuscript does not write out.  This
module supplies it.

## What is proved

With `N = m - h - n` the gap and `W_R = z + cu_{n+N}` the window based at the
site `z = triadicCubeShift R` of a scale-`n` cube `R`:

* `sum_setIntegral_openCubeAtScale_le` -- for a nonnegative `f` integrable on
  `cu_K`, and a family of scale-`n` cubes whose windows lie in `cu_K`,
  `sum_R int_{W_R} f <= 3^{dN} int_{cu_K} f`.  The multiplicity `3^{dN}` is the
  exact overlap count of `LocalizationOverlapCount`, and is attained there.
* `cubeFamilyAverage_volumeAverage_openCubeAtScale_le_of_card` -- the same
  statement after both normalizations, at a caller-supplied constant `C`
  controlled by the cardinality gate `3^{d(K-n)} <= C |I|`.  This is the general
  form: the constant is exactly the ratio of the full lattice count
  `3^{d(K-n)}` to the number of cubes actually summed, and the overlap
  multiplicity has cancelled against the window volume completely.
* `cubeFamilyAverage_volumeAverage_openCubeAtScale_interior_le` -- the instance
  the display consumes, on `interiorMesoCubeGrid d K n (n + N - 1)`, at the
  absolute constant `3^d`.

## Where the constant comes from, exactly

The multiplicity `3^{dN}` and the window volume `3^{(n+N)d}` cancel *exactly*:
the volume-normalized transfer constant produced by the covering alone is `1`.
The entire constant `3^d` of the interior instance is the **interior-grid
deficit**: the interior grid is only guaranteed to contain the scale-`n`
descendants of the concentric child `cu_{K-1}`, i.e. at least `3^{-d}` of the
full grid (`card_mesoCubeGrid_le_three_pow_mul_card_interior`, module
`LocalizationGrid`), and the grid average divides by the number of cubes
summed.  On the full grid `mesoCubeGrid d K n` the same argument gives the
constant `1`, but the full grid's boundary windows are not contained in `cu_K`
and the hypothesis `hsub` fails there; that is the content.

## Divergences from the printed statement

* The manuscript's unrestricted mesh is not such a family, and no bound at the
  boundary sites is claimed here.
* **The count is not clipped.**  `sum_setIntegral_openCubeAtScale_le` uses the
  full lattice multiplicity `3^{dN}`; clipping the family to `cu_K` could only
  improve it, and no such improvement is claimed.
* **Nonnegativity is required everywhere, not almost everywhere.**  The
  applications supply a pointwise nonnegative integrand (a squared or fourth
  power), so the cheaper hypothesis is used.  Nothing below is false for the
  a.e. version; it is simply not proved here.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

open HCPolySupport HCPolySupport.Book.Ch03 MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## The covering bound on the sum of window integrals -/

/-- **The bounded-overlap covering bound.**  For a nonnegative integrable `f` and
a family of scale-`n` cubes whose windows `z + cu_{n+N}` lie in `cu_K`, the sum
of the window integrals exceeds the integral over `cu_K` by at most the overlap
multiplicity `3^{dN}` of `card_filter_mem_openCubeAtScale_le`.

: the caller supplies `hI`, `hsub`, `hf`, `hf0`. -/
theorem sum_setIntegral_openCubeAtScale_le {K n : ℤ} {N : ℕ}
    {I : Finset (TriadicCube d)} {f : Vec d → ℝ}
    (hI : ∀ R ∈ I, R.scale = n)
    (hsub : ∀ R ∈ I, openCubeAtScale (triadicCubeShift R) (n + (N : ℤ)) ⊆
      openCubeSet (originCube d K))
    (hf : IntegrableOn f (openCubeSet (originCube d K)) volume)
    (hf0 : ∀ x, 0 ≤ f x) :
    ∑ R ∈ I, ∫ x in openCubeAtScale (triadicCubeShift R) (n + (N : ℤ)), f x ∂volume ≤
      ((3 : ℝ) ^ N) ^ d * ∫ x in openCubeSet (originCube d K), f x ∂volume := by
  classical
  set U : Set (Vec d) := openCubeSet (originCube d K) with hU
  set W : TriadicCube d → Set (Vec d) :=
    fun R => openCubeAtScale (triadicCubeShift R) (n + (N : ℤ)) with hW
  have hWmeas : ∀ R : TriadicCube d, MeasurableSet (W R) := fun R =>
    measurableSet_openCubeAtScale _ _
  have hstep : ∀ R ∈ I, (∫ x in W R, f x ∂volume) =
      ∫ x in U, Set.indicator (W R) f x ∂volume := by
    intro R hR
    rw [setIntegral_indicator (hWmeas R), Set.inter_eq_self_of_subset_right (hsub R hR)]
  have hint : ∀ R ∈ I, Integrable (Set.indicator (W R) f) (volume.restrict U) :=
    fun R _ => hf.indicator (hWmeas R)
  have hsumint : Integrable (fun x => ∑ R ∈ I, Set.indicator (W R) f x)
      (volume.restrict U) := integrable_finsetSum I hint
  have hconstint : Integrable (fun x => ((3 : ℝ) ^ N) ^ d * f x) (volume.restrict U) :=
    hf.const_mul _
  have hptw : ∀ x : Vec d, ∑ R ∈ I, Set.indicator (W R) f x ≤ ((3 : ℝ) ^ N) ^ d * f x := by
    intro x
    have hfac : ∀ R : TriadicCube d,
        Set.indicator (W R) f x = Set.indicator (W R) (fun _ => (1 : ℝ)) x * f x := by
      intro R
      by_cases hx : x ∈ W R
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, one_mul]
      · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, zero_mul]
    rw [Finset.sum_congr rfl fun R _ => hfac R, ← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (sum_indicator_openCubeAtScale_le x n N hI) (hf0 x)
  calc ∑ R ∈ I, ∫ x in W R, f x ∂volume
      = ∑ R ∈ I, ∫ x in U, Set.indicator (W R) f x ∂volume := Finset.sum_congr rfl hstep
    _ = ∫ x in U, ∑ R ∈ I, Set.indicator (W R) f x ∂volume :=
        (integral_finsetSum I hint).symm
    _ ≤ ∫ x in U, ((3 : ℝ) ^ N) ^ d * f x ∂volume := integral_mono hsumint hconstint hptw
    _ = ((3 : ℝ) ^ N) ^ d * ∫ x in U, f x ∂volume := integral_const_mul _ _

/-! ## The normalized transfer -/

private theorem volume_openCubeSet_originCube_toReal (K : ℤ) :
    (volume (openCubeSet (originCube d K))).toReal = ((3 : ℝ) ^ K) ^ d := by
  rw [volume_openCubeSet_toReal, cubeVolume, cubeScaleFactor_originCube]

/-- **The normalized bounded-overlap transfer.**  After dividing by the window
volume and by the number of cubes summed, the overlap multiplicity has cancelled
against the window volume exactly, and the whole constant is the cardinality
ratio supplied by `hcard`.

: the caller supplies `hInon`, `hI`, `hsub`, `hcard`, `hf`, `hf0`. -/
theorem cubeFamilyAverage_volumeAverage_openCubeAtScale_le_of_card {K n : ℤ} {N : ℕ}
    {I : Finset (TriadicCube d)} {f : Vec d → ℝ} {C : ℝ}
    (hInon : I.Nonempty)
    (hI : ∀ R ∈ I, R.scale = n)
    (hsub : ∀ R ∈ I, openCubeAtScale (triadicCubeShift R) (n + (N : ℤ)) ⊆
      openCubeSet (originCube d K))
    (hcard : ((3 : ℝ) ^ (K - n)) ^ d ≤ C * (I.card : ℝ))
    (hf : IntegrableOn f (openCubeSet (originCube d K)) volume)
    (hf0 : ∀ x, 0 ≤ f x) :
    cubeFamilyAverage I (fun R =>
        volumeAverage (openCubeAtScale (triadicCubeShift R) (n + (N : ℤ))) f) ≤
      C * volumeAverage (openCubeSet (originCube d K)) f := by
  have h3ne : (3 : ℝ) ≠ 0 := by norm_num
  set A : ℝ := ∫ x in openCubeSet (originCube d K), f x ∂volume with hAdef
  have hA : 0 ≤ A :=
    setIntegral_nonneg (measurableSet_openCubeSet _) fun x _ => hf0 x
  have hc : (0 : ℝ) < (I.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hInon
  set V : ℝ := ((3 : ℝ) ^ (n + (N : ℤ))) ^ d with hVdef
  have hVpos : (0 : ℝ) < V := pow_pos (Corrector.zpow_three_pos _) d
  set VK : ℝ := ((3 : ℝ) ^ K) ^ d with hVKdef
  have hVKpos : (0 : ℝ) < VK := pow_pos (Corrector.zpow_three_pos _) d
  set M : ℝ := ((3 : ℝ) ^ N) ^ d with hMdef
  have hMnn : (0 : ℝ) ≤ M := pow_nonneg (pow_nonneg (by norm_num) N) d
  have hFR : ∀ R ∈ I,
      volumeAverage (openCubeAtScale (triadicCubeShift R) (n + (N : ℤ))) f =
        V⁻¹ * ∫ x in openCubeAtScale (triadicCubeShift R) (n + (N : ℤ)), f x ∂volume := by
    intro R _
    rw [volumeAverage, Corrector.volume_openCubeAtScale_toReal]
  have hsum := sum_setIntegral_openCubeAtScale_le hI hsub hf hf0
  have hprod : ((3 : ℝ) ^ (K - n)) ^ d * V = M * VK := by
    rw [hVdef, hMdef, hVKdef, ← mul_pow, ← mul_pow, ← zpow_add₀ h3ne,
      ← zpow_natCast (3 : ℝ) N, ← zpow_add₀ h3ne]
    congr 2
    ring
  have hkey : M * VK ≤ C * (I.card : ℝ) * V := by
    have h1 : ((3 : ℝ) ^ (K - n)) ^ d * V ≤ C * (I.card : ℝ) * V :=
      mul_le_mul_of_nonneg_right hcard hVpos.le
    rw [hprod] at h1
    exact h1
  have hcoef : ((I.card : ℝ))⁻¹ * (V⁻¹ * M) ≤ C * VK⁻¹ := by
    have hL : ((I.card : ℝ))⁻¹ * (V⁻¹ * M) =
        (M * VK) * ((I.card : ℝ) * V * VK)⁻¹ := by
      field_simp
    have hR : C * VK⁻¹ = (C * (I.card : ℝ) * V) * ((I.card : ℝ) * V * VK)⁻¹ := by
      field_simp
    rw [hL, hR]
    exact mul_le_mul_of_nonneg_right hkey (by positivity)
  rw [cubeFamilyAverage, Finset.sum_congr rfl hFR, ← Finset.mul_sum, volumeAverage,
    volume_openCubeSet_originCube_toReal, ← hAdef, ← hVKdef]
  calc ((I.card : ℝ))⁻¹ * (V⁻¹ *
        ∑ R ∈ I, ∫ x in openCubeAtScale (triadicCubeShift R) (n + (N : ℤ)), f x ∂volume)
      ≤ ((I.card : ℝ))⁻¹ * (V⁻¹ * (M * A)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (((I.card : ℝ))⁻¹ * (V⁻¹ * M)) * A := by ring
    _ ≤ (C * VK⁻¹) * A := mul_le_mul_of_nonneg_right hcoef hA
    _ = C * (VK⁻¹ * A) := by ring

/-- **The transfer on the interior meso grid, at the absolute constant `3^d`.**

This is the form `e.lower.bound.oscillations` consumes.  The constant is *not*
the overlap multiplicity -- that has cancelled exactly -- but the interior-grid
deficit of `LocalizationGrid`.

: the caller supplies `hn : n <= K - 1`, `hN : n + N <= K - 1`, `hf`, `hf0`. -/
theorem cubeFamilyAverage_volumeAverage_openCubeAtScale_interior_le {K n : ℤ} {N : ℕ}
    {f : Vec d → ℝ} (hn : n ≤ K - 1) (hN : n + (N : ℤ) ≤ K - 1)
    (hf : IntegrableOn f (openCubeSet (originCube d K)) volume)
    (hf0 : ∀ x, 0 ≤ f x) :
    cubeFamilyAverage (interiorMesoCubeGrid d K n (n + (N : ℤ) - 1)) (fun R =>
        volumeAverage (openCubeAtScale (triadicCubeShift R) (n + (N : ℤ))) f) ≤
      (3 : ℝ) ^ d * volumeAverage (openCubeSet (originCube d K)) f := by
  have houter : (n + (N : ℤ) - 1) + 1 ≤ K - 1 := by omega
  have hnK : n ≤ K := by omega
  refine cubeFamilyAverage_volumeAverage_openCubeAtScale_le_of_card
    (interiorMesoCubeGrid_nonempty hn houter)
    (fun _ hR => scale_eq_of_mem_mesoCubeGrid (interiorMesoCubeGrid_subset hR))
    (fun _ hR => ?_) ?_ hf hf0
  · have h := window_subset_of_mem_interiorMesoCubeGrid hR
    rw [show (n + (N : ℤ) - 1) + 1 = n + (N : ℤ) by ring] at h
    rwa [openCubeAtScale_eq_translateSet, openCubeAtScale_zero_eq_openCubeSet_originCube]
  · have hcard := card_mesoCubeGrid_le_three_pow_mul_card_interior
      (d := d) (K := K) (n := n) (outer := n + (N : ℤ) - 1) hn houter
    rw [card_mesoCubeGrid hnK] at hcard
    have hcastR : (((3 ^ d : ℕ) ^ (K - n).toNat : ℕ) : ℝ) ≤
        (3 : ℝ) ^ d * ((interiorMesoCubeGrid d K n (n + (N : ℤ) - 1)).card : ℝ) := by
      exact_mod_cast hcard
    have hz : (3 : ℝ) ^ (K - n) = (3 : ℝ) ^ ((K - n).toNat) := by
      rw [← zpow_natCast (3 : ℝ) ((K - n).toNat),
        Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ K - n)]
    have hrw : ((3 : ℝ) ^ (K - n)) ^ d = (((3 ^ d : ℕ) ^ (K - n).toNat : ℕ) : ℝ) := by
      push_cast
      rw [hz, ← pow_mul, ← pow_mul]
      ring
    rw [hrw]
    exact hcastR

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
