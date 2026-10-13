/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.HighContrastHomogenization.Support.Besov.Localization
public import LeanPool.HighContrastHomogenization.Support.Geometry.CubeColoring
public import LeanPool.HighContrastHomogenization.Support.Geometry.TriadicCubeTranslation

/-!
# LocalizationGrid

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Provider: the meso grid of the localization display, full and interior filtered

Source displays in ABK26:

* `e.lower.bound.localization.terms` (label) averages its bracketed integrand
  over the site set `z in 3^n Z^d cap cu_K`;
* `e.recurrence.params` (label) fixes the meso scale `n`;
* the `A_4` leg of Step 2 averages `|bfAhom^{1/2} P_z|^4` over the *same* site
  set.

This module supplies the two grid renderings of that site set and the exact
bookkeeping that relates them.

## What is proved

* `cubeAverage_originCube_eq_descendantsAverage` -- the tiling identity
  `fint_{cu_K} f = descendantsAverage (originCube d K) j (fun R => fint_R f)`
  for `f` integrable on `cu_K`, at the origin cube.  This is a *specialization*
  of CoarseGraining's
  `cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn`, which
  already holds at an arbitrary triadic cube and arbitrary depth; nothing new
  is proved here, the named form is recorded because it is the display's
  carrier.
* `mesoCubeGrid` -- the full scale-`n` grid of `cu_K`, i.e.
  `descendantsAtScale (originCube d K) n`, and
  `cubeAverage_originCube_eq_mesoGridAverage`, the tiling identity in the
  scale-indexed grid form, at tiling constant `1`.
* `interiorMesoCubeGrid` -- the subfamily of `mesoCubeGrid` whose *enlarged*
  outer window `z + cu_{outer+1}` still lies inside `cu_K`, together with
  `window_subset_of_mem_interiorMesoCubeGrid`, the containment that the
  per-cube estimates consume.
* `card_mesoCubeGrid_le_three_pow_mul_card_interior` -- the boundary-layer
  count: the removed layer costs at most the pure model constant `3^d`.
* `cubeFamilyAverage_interior_le_of_full` -- the resulting transfer of a
  nonnegative grid average from the full family to the interior family.

## Divergences from the printed statement

* The tiling identity holds at constant `1`; this is `mesoCubeGrid` and
  `cubeAverage_originCube_eq_mesoGridAverage`.
* **The display leg is interior-filtered.**  It runs on the *interior-filtered*
  subfamily, on which the tiling identity is false: a boundary layer of width
  `~3^{outer+1}` is removed.  This is `interiorMesoCubeGrid`, and the two legs
  meet only through the one-directional cardinality bookkeeping below.
* **The two legs are different objects.**  The two previous items describe
  different legs.  `mesoCubeGrid` carries the `A_4` / principal leg,
  `interiorMesoCubeGrid` the display leg.
* **The count constant is crude and `gamma`-free.**  The boundary-layer count
  below is `3^d`, obtained from the concentric child `cu_{K-1}`; the true ratio
  is `1 + O(3^{-(K-outer)})`.  No sharper count is claimed.

## What is not proved here

* **The full-grid boundary transfer is open.**  Only `interior <= 3^d * full`
  is proved.  The opposite direction `full <= C * interior` -- what a lift of
  the display leg back to the manuscript's full grid would need -- is NOT
  proved here and is not attainable by this route: the display's integrand has
  no sign, and no per-cube bound of any kind is available at boundary cubes.  A
  consumer that wants the full grid must supply that transfer itself; this
  module does not.
* **The grid mismatch is untouched.**  The manuscript states its per-cube
  inputs on the `cu_m` grid while the display averages the `cu_K` grid; the
  stationarity argument reconciling them is not supplied below.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

open HCPolySupport MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## The average over a finite family of cubes -/

/-- The unweighted average of a real function over a finite family of cubes.
On a family of equal-volume cubes -- which is the only case used below -- this
is also the volume-weighted average. -/
def cubeFamilyAverage (I : Finset (TriadicCube d)) (F : TriadicCube d → ℝ) : ℝ :=
  ((I.card : ℝ))⁻¹ * ∑ R ∈ I, F R

theorem descendantsAverage_eq_cubeFamilyAverage (Q : TriadicCube d) (j : ℕ)
    (F : TriadicCube d → ℝ) :
    descendantsAverage Q j F = cubeFamilyAverage (descendantsAtDepth Q j) F :=
  rfl

theorem cubeFamilyAverage_nonneg {I : Finset (TriadicCube d)} {F : TriadicCube d → ℝ}
    (hF : ∀ R ∈ I, 0 ≤ F R) : 0 ≤ cubeFamilyAverage I F := by
  refine mul_nonneg (by positivity) (Finset.sum_nonneg hF)

/-! ## The two grids -/

/-- The manuscript's meso site set `3^n Z^d cap cu_K`, rendered as the finite
family of scale-`n` triadic descendants of `cu_K`. -/
def mesoCubeGrid (d : ℕ) (K n : ℤ) : Finset (TriadicCube d) :=
  descendantsAtScale (originCube d K) n

/-- The interior-filtered meso grid: those scale-`n` descendants of `cu_K` whose
*enlarged* outer window `z + cu_{outer+1}`, based at the cube's own site `z =
triadicCubeShift R`, is still contained in `cu_K`.  This is the exact carrier
of the per-cube estimates. -/
def interiorMesoCubeGrid (d : ℕ) (K n outer : ℤ) : Finset (TriadicCube d) := by
  classical
  exact (mesoCubeGrid d K n).filter fun R =>
    translateSet (triadicCubeShift R) (openCubeSet (originCube d (outer + 1))) ⊆
      openCubeSet (originCube d K)

theorem mem_interiorMesoCubeGrid_iff {K n outer : ℤ} {R : TriadicCube d} :
    R ∈ interiorMesoCubeGrid d K n outer ↔
      R ∈ mesoCubeGrid d K n ∧
        translateSet (triadicCubeShift R) (openCubeSet (originCube d (outer + 1))) ⊆
          openCubeSet (originCube d K) := by
  classical
  simp [interiorMesoCubeGrid]

theorem interiorMesoCubeGrid_subset {K n outer : ℤ} :
    interiorMesoCubeGrid d K n outer ⊆ mesoCubeGrid d K n := fun _ hR =>
  (mem_interiorMesoCubeGrid_iff.mp hR).1

/-- **The containment that the per-cube estimates consume.**  A member of the
interior grid has its enlarged outer window inside `cu_K`; this is the
`hparent` input of the nested Campanato tower. -/
theorem window_subset_of_mem_interiorMesoCubeGrid {K n outer : ℤ} {R : TriadicCube d}
    (hR : R ∈ interiorMesoCubeGrid d K n outer) :
    translateSet (triadicCubeShift R) (openCubeSet (originCube d (outer + 1))) ⊆
      openCubeSet (originCube d K) :=
  (mem_interiorMesoCubeGrid_iff.mp hR).2

theorem mesoCubeGrid_eq_descendantsAtDepth {K n : ℤ} (hn : n ≤ K) :
    mesoCubeGrid d K n = descendantsAtDepth (originCube d K) (K - n).toNat :=
  descendantsAtScale_eq_descendantsAtDepth (originCube d K) hn

theorem card_mesoCubeGrid {K n : ℤ} (hn : n ≤ K) :
    (mesoCubeGrid d K n).card = (3 ^ d) ^ (K - n).toNat := by
  rw [mesoCubeGrid_eq_descendantsAtDepth hn, descendantsAtDepth_card]

theorem mesoCubeGrid_nonempty {K n : ℤ} (hn : n ≤ K) :
    (mesoCubeGrid d K n).Nonempty := by
  rw [mesoCubeGrid_eq_descendantsAtDepth hn]
  exact descendantsAtDepth_nonempty _ _

theorem scale_eq_of_mem_mesoCubeGrid {K n : ℤ} {R : TriadicCube d}
    (hR : R ∈ mesoCubeGrid d K n) : R.scale = n :=
  scale_eq_of_mem_descendantsAtScale hR

/-! ## The tiling identity -/

/-- **The mesh tiling identity at the origin cube.** For `f` integrable on `cu_K`,
`fint_{cu_K} f = descendantsAverage (originCube d K) j (fun R => fint_R f)`.

This is CoarseGraining's
`cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn` specialized to
the origin cube; the general identity was already available at an arbitrary
triadic cube and an arbitrary depth. -/
theorem cubeAverage_originCube_eq_descendantsAverage (K : ℤ) (j : ℕ) (f : Vec d → ℝ)
    (hf : IntegrableOn f (cubeSet (originCube d K)) volume) :
    cubeAverage (originCube d K) f =
      descendantsAverage (originCube d K) j (fun R => cubeAverage R f) :=
  cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn (originCube d K) j f hf

/-- **The tiling identity in the scale-indexed grid form.**  The manuscript's
`avsum_{z in 3^n Z^d cap cu_K} fint_{z + cu_n} f` is `fint_{cu_K} f` exactly:
the tiling constant is `1`. -/
theorem cubeAverage_originCube_eq_mesoGridAverage {K n : ℤ} (hn : n ≤ K) (f : Vec d → ℝ)
    (hf : IntegrableOn f (cubeSet (originCube d K)) volume) :
    cubeAverage (originCube d K) f =
      cubeFamilyAverage (mesoCubeGrid d K n) (fun R => cubeAverage R f) := by
  rw [mesoCubeGrid_eq_descendantsAtDepth hn, ← descendantsAverage_eq_cubeFamilyAverage]
  exact cubeAverage_originCube_eq_descendantsAverage K _ f hf

/-! ## The concentric child, and the boundary-layer count -/

private theorem originCube_pred_mem_childCubes (d : ℕ) (K : ℤ) :
    originCube d (K - 1) ∈ childCubes (originCube d K) := by
  refine Finset.mem_image.mpr ⟨fun _ => (1 : Fin 3), Finset.mem_univ _, ?_⟩
  have hindex : (fun i : Fin d => 3 * (originCube d K).index i + ((1 : Fin 3) : ℤ) - 1) =
      (originCube d (K - 1)).index := by
    funext i
    show 3 * (0 : ℤ) + ((1 : Fin 3) : ℤ) - 1 = 0
    norm_num
  exact congrArg (fun idx => (⟨K - 1, idx⟩ : TriadicCube d)) hindex

private theorem descendantsAtDepth_subset_of_mem_childCubes {Q R : TriadicCube d}
    (hR : R ∈ childCubes Q) :
    ∀ j : ℕ, descendantsAtDepth R j ⊆ descendantsAtDepth Q (j + 1)
  | 0 => by
      intro S hS
      rw [descendantsAtDepth_zero, Finset.mem_singleton] at hS
      rw [zero_add, descendantsAtDepth_one]
      exact hS ▸ hR
  | j + 1 => by
      intro S hS
      rw [descendantsAtDepth_succ] at hS
      rw [descendantsAtDepth_succ]
      obtain ⟨T, hT, hST⟩ := Finset.mem_biUnion.mp hS
      exact Finset.mem_biUnion.mpr
        ⟨T, descendantsAtDepth_subset_of_mem_childCubes hR j hT, hST⟩

private theorem mesoCubeGrid_pred_subset {K n : ℤ} (hn : n ≤ K - 1) :
    mesoCubeGrid d (K - 1) n ⊆ mesoCubeGrid d K n := by
  have hnK : n ≤ K := by omega
  rw [mesoCubeGrid_eq_descendantsAtDepth hn, mesoCubeGrid_eq_descendantsAtDepth hnK]
  have hdepth : (K - n).toNat = (K - 1 - n).toNat + 1 := by omega
  rw [hdepth]
  exact descendantsAtDepth_subset_of_mem_childCubes (originCube_pred_mem_childCubes d K) _

/-- The site of a cube lies in the cube. -/
private theorem triadicCubeShift_mem_cubeSet (R : TriadicCube d) :
    triadicCubeShift R ∈ cubeSet R := by
  intro i
  have hs : 0 < cubeScaleFactor R := zpow_pos (by norm_num) _
  constructor
  · show ((R.index i : ℝ) - 1 / 2) * cubeScaleFactor R ≤
      (R.index i : ℝ) * cubeScaleFactor R
    nlinarith [hs]
  · show (R.index i : ℝ) * cubeScaleFactor R <
      ((R.index i : ℝ) + 1 / 2) * cubeScaleFactor R
    nlinarith [hs]

/-- **The concentric child fills the interior grid.**  Every scale-`n`
descendant of the concentric child `cu_{K-1}` already satisfies the enlarged
window condition, provided the window scale does not exceed `K - 1`. -/
private theorem mesoCubeGrid_pred_subset_interior {K n outer : ℤ}
    (hn : n ≤ K - 1) (houter : outer + 1 ≤ K - 1) :
    mesoCubeGrid d (K - 1) n ⊆ interiorMesoCubeGrid d K n outer := by
  intro R hR
  refine mem_interiorMesoCubeGrid_iff.mpr ⟨mesoCubeGrid_pred_subset hn hR, ?_⟩
  have hApos : (0 : ℝ) < (3 : ℝ) ^ (K - 1) := zpow_pos (by norm_num) _
  have hBpos : (0 : ℝ) < (3 : ℝ) ^ (outer + 1) := zpow_pos (by norm_num) _
  have hBA : (3 : ℝ) ^ (outer + 1) ≤ (3 : ℝ) ^ (K - 1) :=
    zpow_le_zpow_right₀ (by norm_num) houter
  have hK : (3 : ℝ) ^ K = 3 * (3 : ℝ) ^ (K - 1) := by
    have hKeq : K - 1 + 1 = K := by omega
    have h1 : (3 : ℝ) ^ (K - 1 + 1) = (3 : ℝ) ^ (K - 1) * 3 :=
      zpow_add_one₀ (by norm_num) (K - 1)
    rw [hKeq] at h1
    rw [h1]
    ring
  have hcenter : triadicCubeShift R ∈ cubeSet (originCube d (K - 1)) :=
    cubeSet_subset_of_mem_descendantsAtScale hn hR (triadicCubeShift_mem_cubeSet R)
  rw [mem_cubeSet_originCube_iff] at hcenter
  intro x hx
  rw [mem_translateSet_iff_sub_mem, mem_openCubeSet_originCube_iff] at hx
  rw [mem_openCubeSet_originCube_iff]
  intro i
  obtain ⟨hzlo, hzhi⟩ := hcenter i
  obtain ⟨hxlo, hxhi⟩ := hx i
  have hpi : (x - triadicCubeShift R) i = x i - triadicCubeShift R i := rfl
  rw [hpi] at hxlo hxhi
  rw [hK]
  constructor
  · linarith
  · linarith

/-- **The boundary-layer count.**  The full meso grid exceeds the interior grid by
at most the pure model constant `3^d`, free of `gamma`, of `m`, of `h` and of
`K`. -/
theorem card_mesoCubeGrid_le_three_pow_mul_card_interior {K n outer : ℤ}
    (hn : n ≤ K - 1) (houter : outer + 1 ≤ K - 1) :
    (mesoCubeGrid d K n).card ≤ 3 ^ d * (interiorMesoCubeGrid d K n outer).card := by
  have hnK : n ≤ K := by omega
  have hcardsub : (mesoCubeGrid d (K - 1) n).card ≤
      (interiorMesoCubeGrid d K n outer).card :=
    Finset.card_le_card (mesoCubeGrid_pred_subset_interior hn houter)
  have hfull : (mesoCubeGrid d K n).card = 3 ^ d * (mesoCubeGrid d (K - 1) n).card := by
    rw [card_mesoCubeGrid hnK, card_mesoCubeGrid hn]
    have hdepth : (K - n).toNat = (K - 1 - n).toNat + 1 := by omega
    rw [hdepth, pow_succ]
    ring
  rw [hfull]
  exact Nat.mul_le_mul_left _ hcardsub

theorem interiorMesoCubeGrid_nonempty {K n outer : ℤ}
    (hn : n ≤ K - 1) (houter : outer + 1 ≤ K - 1) :
    (interiorMesoCubeGrid d K n outer).Nonempty :=
  (mesoCubeGrid_nonempty (d := d) (K := K - 1) (n := n) hn).mono
    (mesoCubeGrid_pred_subset_interior hn houter)

/-! ## The transfer of a nonnegative average -/

private theorem cubeFamilyAverage_le_of_subset {I J : Finset (TriadicCube d)}
    {F : TriadicCube d → ℝ} {c : ℝ} (hIJ : I ⊆ J) (hI : I.Nonempty)
    (hcard : (J.card : ℝ) ≤ c * (I.card : ℝ)) (hF : ∀ R ∈ J, 0 ≤ F R) :
    cubeFamilyAverage I F ≤ c * cubeFamilyAverage J F := by
  have hIcard : 0 < (I.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hI
  have hJcard : 0 < (J.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr (hI.mono hIJ)
  have hsum : ∑ R ∈ I, F R ≤ ∑ R ∈ J, F R :=
    Finset.sum_le_sum_of_subset_of_nonneg hIJ fun R hRJ _ => hF R hRJ
  have hsum0 : 0 ≤ ∑ R ∈ J, F R := Finset.sum_nonneg hF
  have hinv : ((I.card : ℝ))⁻¹ ≤ c * ((J.card : ℝ))⁻¹ := by
    rw [inv_le_iff_one_le_mul₀ hIcard]
    have hrw : c * ((J.card : ℝ))⁻¹ * (I.card : ℝ) = c * (I.card : ℝ) / (J.card : ℝ) := by
      field_simp
    rw [hrw, le_div_iff₀ hJcard]
    linarith
  calc cubeFamilyAverage I F
      = ((I.card : ℝ))⁻¹ * ∑ R ∈ I, F R := rfl
    _ ≤ ((I.card : ℝ))⁻¹ * ∑ R ∈ J, F R :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ (c * ((J.card : ℝ))⁻¹) * ∑ R ∈ J, F R :=
        mul_le_mul_of_nonneg_right hinv hsum0
    _ = c * cubeFamilyAverage J F := by
        rw [cubeFamilyAverage, mul_assoc]

/-- **Transfer of a nonnegative grid average from the full family to the interior
family**, at the boundary-layer cost `3^d`. -/
theorem cubeFamilyAverage_interior_le_of_full {K n outer : ℤ} {F : TriadicCube d → ℝ}
    (hn : n ≤ K - 1) (houter : outer + 1 ≤ K - 1)
    (hF : ∀ R ∈ mesoCubeGrid d K n, 0 ≤ F R) :
    cubeFamilyAverage (interiorMesoCubeGrid d K n outer) F ≤
      (3 : ℝ) ^ d * cubeFamilyAverage (mesoCubeGrid d K n) F := by
  refine cubeFamilyAverage_le_of_subset interiorMesoCubeGrid_subset
    (interiorMesoCubeGrid_nonempty hn houter) ?_ hF
  have h := card_mesoCubeGrid_le_three_pow_mul_card_interior (d := d) hn houter
  exact_mod_cast h

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
