/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Data.Pi.Interval
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.LocalizationOscillationGridMoment
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Fractional.PairCapture

/-!
# LocalizationFluctuationMeshTransfer

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The interior-to-full mesh passage

```
  z in 3^n Zd cap cu_K   with   z + cu_{m-h} subseteq cu_K ,
```

whereas the display that consumes it, `e.lower.bound.oscillations`, averages
over the *full* mesh `3^n Zd cap cu_K`.

**This module takes the second route**, which is the one the formalization
needs: the downstream carrier is the full `descendantsAtDepth` family of
`LocalizationRecurrenceMesh`, so the interior restriction cannot be pushed
forward.  The transfer has two halves, both proved here and both unconditional.

The signed transfer is also proved here in the `Closure` namespace, with the
interior average replaced by its maximum with zero. The nonnegative estimate
is a corollary of that common calculation.

* A **Cauchy--Schwarz split**: for a nonnegative family `F` on a finite grid `I`
  and any sub-grid `J`,
  ```
  avsum_{R in I} F R
    <= avsum_{R in J} F R
       + sqrt(1 - |J| / |I|) * sqrt(avsum_{R in I} (F R)^2) .
  ```
  Nothing is assumed about `F` beyond nonnegativity; the boundary contribution
  is paid by the square root of the *missing fraction* against the square
  function of the same average.

* A **boundary count**: the interior mesh of `LocalizationGrid` contains the
  index box of radius `halfRange p - halfRange g`, where `p = K - n` is the
  depth of the mesh and `g = (m-h) - n` the window gap, so
  ```
  1 - |interiorMesoCubeGrid d K n (m-h-1)| / |mesoCubeGrid d K n|
    <= d * 3^{g - p} = d * 3^{(m-h) - K} .
  ```
  Under the recurrence's own large-cube gate `10^10 gamma^{-1} <= K - m` the
  right-hand side is below `3^{-10^10 gamma^{-1}}` up to the dimensional
  factor, i.e. smaller than every power of `gamma`.

Combining the two gives `gridFourthMoment_mesoCubeGrid_le_interior_add`: the
full-mesh fourth-moment average of `e.lower.bound.oscillations` is the interior
one plus `sqrt(d 3^{(m-h)-K})` times the square root of the *squared* grid
average.  The remaining input a consumer owes is exactly that squared average,
i.e. an eighth-moment envelope of the same per-cell quantity; no boundary
geometry, no artificial cutoff and no stationarity argument is introduced.

## Binders

Every statement below is finite combinatorics or cube-index arithmetic.  The
only hypotheses are the scale bookkeeping `K = n + p`, `outer + 1 = n + g`,
`g <= p` -- which merely *name* the depth and the window gap of the recurrence
mesh -- and the nonnegativity of the averaged family.  No smallness, moment,
measurability or integrability proposition occurs, and nothing about the
corrector or the sample space is assumed.

## Scope

There is no `sorry`.

## References

* ABK26, `e.nablaw.oscillations`, `e.lower.bound.oscillations`,
  `e.recurrence.params`.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

open HCPolySupport MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## The Cauchy--Schwarz split of a grid average -/

/-- Cauchy--Schwarz for a nonnegative family on a finite grid. -/
theorem sum_le_sqrt_card_mul_sqrt_sum_sq (s : Finset (TriadicCube d))
    (F : TriadicCube d → ℝ) (hF : ∀ R ∈ s, 0 ≤ F R) :
    ∑ R ∈ s, F R ≤ Real.sqrt (s.card : ℝ) * Real.sqrt (∑ R ∈ s, F R ^ 2) := by
  have h := sq_sum_le_card_mul_sum_sq (s := s) (f := F)
  have hnn : 0 ≤ ∑ R ∈ s, F R := Finset.sum_nonneg hF
  have h2 : Real.sqrt ((∑ R ∈ s, F R) ^ 2) ≤
      Real.sqrt ((s.card : ℝ) * ∑ R ∈ s, F R ^ 2) := Real.sqrt_le_sqrt h
  rwa [Real.sqrt_sq hnn, Real.sqrt_mul (by positivity)] at h2

namespace Closure

/-- **The boundary transfer without a sign hypothesis.**

For any sub-family `J` of `I` and any real family `F`,

```
  avsum_I F  <=  max (avsum_J F) 0  +  sqrt (1 - |J|/|I|) . sqrt (avsum_I F^2) .
```

The interior half uses only `|J| <= |I|` and `0 <= max (avsum_J F) 0`; the strip
half is Cauchy--Schwarz at `|F|`.  Unconditional. -/
theorem cubeFamilyAverage_le_max_add_sqrt_boundaryFraction {I J : Finset (TriadicCube d)}
    (hJI : J ⊆ I) (F : TriadicCube d → ℝ) :
    cubeFamilyAverage I F ≤
      max (cubeFamilyAverage J F) 0 +
        Real.sqrt (1 - (J.card : ℝ) / (I.card : ℝ)) *
          Real.sqrt (cubeFamilyAverage I (fun R => F R ^ 2)) := by
  classical
  rcases Nat.eq_zero_or_pos I.card with hI0 | hIpos
  · have hIempty : I = ∅ := Finset.card_eq_zero.mp hI0
    subst hIempty
    have hJempty : J = ∅ := Finset.subset_empty.mp hJI
    subst hJempty
    simp [cubeFamilyAverage]
  have hN : (0 : ℝ) < (I.card : ℝ) := by exact_mod_cast hIpos
  have hMN : J.card ≤ I.card := Finset.card_le_card hJI
  have hMNR : (J.card : ℝ) ≤ (I.card : ℝ) := by exact_mod_cast hMN
  have hsplit : ∑ R ∈ I, F R = ∑ R ∈ J, F R + ∑ R ∈ I \ J, F R := by
    rw [← Finset.sum_union Finset.disjoint_sdiff]
    congr 1
    exact (Finset.union_sdiff_of_subset hJI).symm
  have hpart1 : ((I.card : ℝ))⁻¹ * ∑ R ∈ J, F R ≤ max (cubeFamilyAverage J F) 0 := by
    rcases Nat.eq_zero_or_pos J.card with hJ0 | hJpos
    · have hJempty : J = ∅ := Finset.card_eq_zero.mp hJ0
      subst hJempty
      simp [cubeFamilyAverage]
    · have hM : (0 : ℝ) < (J.card : ℝ) := by exact_mod_cast hJpos
      have hsumJ : ∑ R ∈ J, F R = (J.card : ℝ) * cubeFamilyAverage J F := by
        change _ = (J.card : ℝ) * (((J.card : ℝ))⁻¹ * ∑ R ∈ J, F R)
        field_simp
      rw [hsumJ]
      have hle1 : (J.card : ℝ) / (I.card : ℝ) ≤ 1 := (div_le_one hN).2 hMNR
      have hmax : cubeFamilyAverage J F ≤ max (cubeFamilyAverage J F) 0 := le_max_left _ _
      have hmax0 : (0 : ℝ) ≤ max (cubeFamilyAverage J F) 0 := le_max_right _ _
      calc ((I.card : ℝ))⁻¹ * ((J.card : ℝ) * cubeFamilyAverage J F)
          = ((J.card : ℝ) / (I.card : ℝ)) * cubeFamilyAverage J F := by
            field_simp
        _ ≤ ((J.card : ℝ) / (I.card : ℝ)) * max (cubeFamilyAverage J F) 0 :=
            mul_le_mul_of_nonneg_left hmax (by positivity)
        _ ≤ 1 * max (cubeFamilyAverage J F) 0 :=
            mul_le_mul_of_nonneg_right hle1 hmax0
        _ = max (cubeFamilyAverage J F) 0 := one_mul _
  have hcard : ((I \ J).card : ℝ) = (I.card : ℝ) - (J.card : ℝ) := by
    rw [Finset.card_sdiff_of_subset hJI]
    push_cast [hMN]
    ring
  have hCS : ∑ R ∈ I \ J, |F R| ≤
      Real.sqrt (((I \ J).card : ℝ)) * Real.sqrt (∑ R ∈ I \ J, |F R| ^ 2) :=
    sum_le_sqrt_card_mul_sqrt_sum_sq _ (fun R => |F R|) fun R _ => abs_nonneg _
  have habs2 : ∑ R ∈ I \ J, |F R| ^ 2 = ∑ R ∈ I \ J, F R ^ 2 :=
    Finset.sum_congr rfl fun R _ => sq_abs _
  have hsq_le : ∑ R ∈ I \ J, F R ^ 2 ≤ ∑ R ∈ I, F R ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset fun R _ _ => sq_nonneg _
  have hsumle : ∑ R ∈ I \ J, F R ≤ ∑ R ∈ I \ J, |F R| :=
    Finset.sum_le_sum fun R _ => le_abs_self _
  have hpart2 : ((I.card : ℝ))⁻¹ * ∑ R ∈ I \ J, F R ≤
      Real.sqrt (1 - (J.card : ℝ) / (I.card : ℝ)) *
        Real.sqrt (cubeFamilyAverage I (fun R => F R ^ 2)) := by
    have hstep : ((I.card : ℝ))⁻¹ * ∑ R ∈ I \ J, F R ≤
        ((I.card : ℝ))⁻¹ *
          (Real.sqrt (((I \ J).card : ℝ)) * Real.sqrt (∑ R ∈ I, F R ^ 2)) := by
      refine mul_le_mul_of_nonneg_left (hsumle.trans (hCS.trans ?_)) (by positivity)
      rw [habs2]
      exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hsq_le) (Real.sqrt_nonneg _)
    refine hstep.trans (le_of_eq ?_)
    unfold cubeFamilyAverage
    rw [hcard, Real.sqrt_mul (by positivity),
      show (1 : ℝ) - (J.card : ℝ) / (I.card : ℝ) =
        ((I.card : ℝ))⁻¹ * ((I.card : ℝ) - (J.card : ℝ)) by field_simp,
      Real.sqrt_mul (by positivity)]
    have hinv : Real.sqrt (((I.card : ℝ))⁻¹) * Real.sqrt (((I.card : ℝ))⁻¹) =
        ((I.card : ℝ))⁻¹ := Real.mul_self_sqrt (by positivity)
    have hrhs : Real.sqrt (((I.card : ℝ))⁻¹) * Real.sqrt ((I.card : ℝ) - (J.card : ℝ)) *
        (Real.sqrt (((I.card : ℝ))⁻¹) * Real.sqrt (∑ R ∈ I, F R ^ 2)) =
        (Real.sqrt (((I.card : ℝ))⁻¹) * Real.sqrt (((I.card : ℝ))⁻¹)) *
          (Real.sqrt ((I.card : ℝ) - (J.card : ℝ)) * Real.sqrt (∑ R ∈ I, F R ^ 2)) := by
      ring
    simp only []
    rw [hrhs, hinv]
  unfold cubeFamilyAverage
  rw [hsplit, mul_add]
  exact add_le_add hpart1 hpart2

end Closure

/-- **The boundary transfer.**  For a nonnegative family, the average over the
full grid is the average over any sub-grid plus a Cauchy--Schwarz remainder
carrying the square root of the missing fraction.  Unconditional. -/
theorem cubeFamilyAverage_le_add_sqrt_boundaryFraction {I J : Finset (TriadicCube d)}
    (hJI : J ⊆ I) (F : TriadicCube d → ℝ) (hF : ∀ R ∈ I, 0 ≤ F R) :
    cubeFamilyAverage I F ≤
      cubeFamilyAverage J F +
        Real.sqrt (1 - (J.card : ℝ) / (I.card : ℝ)) *
          Real.sqrt (cubeFamilyAverage I (fun R => F R ^ 2)) := by
  have hJ : 0 ≤ cubeFamilyAverage J F :=
    cubeFamilyAverage_nonneg fun R hR => hF R (hJI hR)
  simpa only [max_eq_left hJ] using
    Closure.cubeFamilyAverage_le_max_add_sqrt_boundaryFraction hJI F

/-! ## The index box inside the interior mesh -/

/-- The window of a cube whose site is far enough from the boundary stays inside
the big cube.  Unconditional cube-index arithmetic. -/
theorem translateSet_subset_openCubeSet_originCube {K L n : ℤ} {R : TriadicCube d}
    (hsc : R.scale = n)
    (hidx : ∀ i, |(R.index i : ℝ)| * (3 : ℝ) ^ n + (3 : ℝ) ^ L / 2 ≤ (3 : ℝ) ^ K / 2) :
    translateSet (triadicCubeShift R) (openCubeSet (originCube d L)) ⊆
      openCubeSet (originCube d K) := by
  intro x hx
  rw [mem_translateSet_iff_sub_mem] at hx
  intro i
  have h := hx i
  have hz : triadicCubeShift R i = (R.index i : ℝ) * (3 : ℝ) ^ n := by
    simp [triadicCubeShift, cubeScaleFactor, hsc]
  have hL : ((originCube d L).index i : ℝ) = 0 := by simp [originCube]
  have hLf : cubeScaleFactor (originCube d L) = (3 : ℝ) ^ L := rfl
  have hKf : cubeScaleFactor (originCube d K) = (3 : ℝ) ^ K := rfl
  have hKi : ((originCube d K).index i : ℝ) = 0 := by simp [originCube]
  rw [hL, hLf] at h
  simp only [Pi.sub_apply, hz] at h
  have hb := hidx i
  have habs : |(R.index i : ℝ) * (3 : ℝ) ^ n| = |(R.index i : ℝ)| * (3 : ℝ) ^ n := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (3 : ℝ) ^ n)]
  have hzabs : |(R.index i : ℝ) * (3 : ℝ) ^ n| + (3 : ℝ) ^ L / 2 ≤ (3 : ℝ) ^ K / 2 := by
    rw [habs]; exact hb
  have h1 : -|(R.index i : ℝ) * (3 : ℝ) ^ n| ≤ (R.index i : ℝ) * (3 : ℝ) ^ n :=
    neg_abs_le _
  have h2 : (R.index i : ℝ) * (3 : ℝ) ^ n ≤ |(R.index i : ℝ) * (3 : ℝ) ^ n| :=
    le_abs_self _
  rw [hKi, hKf]
  constructor <;> [linarith [h.1, h.2]; linarith [h.1, h.2]]

/-- The family of scale-`n` triadic cubes whose index lies in the centred box of
radius `r`.  This is the interior sub-mesh of the boundary count. -/
def indexBoxGrid (d : ℕ) (n r : ℤ) : Finset (TriadicCube d) := by
  classical
  exact (Finset.Icc (fun _ : Fin d => -r) (fun _ : Fin d => r)).image
    (fun idx => ({ scale := n, index := idx } : TriadicCube d))

theorem mem_indexBoxGrid_iff {n r : ℤ} {R : TriadicCube d} :
    R ∈ indexBoxGrid d n r ↔ R.scale = n ∧ ∀ i, -r ≤ R.index i ∧ R.index i ≤ r := by
  classical
  constructor
  · intro hR
    rw [indexBoxGrid, Finset.mem_image] at hR
    obtain ⟨idx, hidx, rfl⟩ := hR
    rw [Finset.mem_Icc] at hidx
    exact ⟨rfl, fun i => ⟨hidx.1 i, hidx.2 i⟩⟩
  · rintro ⟨hsc, hidx⟩
    rw [indexBoxGrid, Finset.mem_image]
    refine ⟨R.index, ?_, ?_⟩
    · rw [Finset.mem_Icc]
      exact ⟨fun i => (hidx i).1, fun i => (hidx i).2⟩
    · cases R; simp_all

theorem card_indexBoxGrid (d : ℕ) (n r : ℤ) :
    (indexBoxGrid d n r).card = ((2 * r + 1).toNat) ^ d := by
  classical
  have hinj : Function.Injective
      (fun idx : Fin d → ℤ => ({ scale := n, index := idx } : TriadicCube d)) := by
    intro a b hab
    simpa using congrArg TriadicCube.index hab
  rw [indexBoxGrid, Finset.card_image_of_injective _ hinj, Pi.card_Icc]
  have hcard : (Finset.Icc (-r) r).card = (2 * r + 1).toNat := by
    rw [Int.card_Icc]
    congr 1
    omega
  simp [hcard]

theorem indexBoxGrid_subset_mesoCubeGrid (d : ℕ) {K n r : ℤ} (hnK : n ≤ K)
    (hr : r ≤ Gagliardo.halfRange (K - n).toNat) :
    indexBoxGrid d n r ⊆ mesoCubeGrid d K n := by
  intro R hR
  obtain ⟨hsc, hidx⟩ := mem_indexBoxGrid_iff.mp hR
  have hos : (originCube d K).scale = K := rfl
  have hsK : n ≤ (originCube d K).scale := by rw [hos]; exact hnK
  rw [mesoCubeGrid, descendantsAtScale, dite_eq_left hsK, hos]
  refine Gagliardo.mem_descendantsAtDepth_of_index_range ?_ ?_
  · rw [hsc, hos]
    omega
  · intro i
    have h0 : (originCube d K).index i = 0 := rfl
    have hb := hidx i
    have hhr : (0 : ℤ) ≤ Gagliardo.halfRange (K - n).toNat := Gagliardo.halfRange_nonneg _
    rw [h0, mul_zero]
    constructor <;> omega

theorem indexBoxGrid_subset_interiorMesoCubeGrid (d : ℕ) {K n outer r : ℤ}
    (hnK : n ≤ K) (hr : r ≤ Gagliardo.halfRange (K - n).toNat)
    (hgeom : (r : ℝ) * (3 : ℝ) ^ n + (3 : ℝ) ^ (outer + 1) / 2 ≤ (3 : ℝ) ^ K / 2) :
    indexBoxGrid d n r ⊆ interiorMesoCubeGrid d K n outer := by
  intro R hR
  obtain ⟨hsc, hidx⟩ := mem_indexBoxGrid_iff.mp hR
  refine mem_interiorMesoCubeGrid_iff.mpr
    ⟨indexBoxGrid_subset_mesoCubeGrid d hnK hr hR, ?_⟩
  refine translateSet_subset_openCubeSet_originCube hsc ?_
  intro i
  have hb := hidx i
  have habs : |(R.index i : ℝ)| ≤ (r : ℝ) := by
    rw [abs_le]
    constructor
    · exact_mod_cast neg_le_of_neg_le (by exact_mod_cast neg_le.mp (by exact_mod_cast hb.1))
    · exact_mod_cast hb.2
  have h3 : (0 : ℝ) < (3 : ℝ) ^ n := by positivity
  nlinarith [habs, h3, hgeom]

/-! ## The boundary fraction -/

theorem two_mul_halfRange_real (m : ℕ) :
    2 * ((Gagliardo.halfRange m : ℤ) : ℝ) = (3 : ℝ) ^ m - 1 := by
  have h := Gagliardo.two_mul_halfRange m
  have hcast : ((2 * Gagliardo.halfRange m : ℤ) : ℝ) = (((3 : ℤ) ^ m - 1 : ℤ) : ℝ) := by
    exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) h
  push_cast at hcast
  linarith

/-- **The interior mesh is large.**  At mesh depth `p = K - n` and window gap
`g = (outer + 1) - n`, the interior grid contains the index box of radius
`halfRange p - halfRange g`, whose cardinality is `(3^p - 3^g + 1)^d`. -/
theorem card_interiorMesoCubeGrid_ge (d : ℕ) {K n outer : ℤ} {p g : ℕ}
    (hK : K = n + (p : ℤ)) (houter : outer + 1 = n + (g : ℤ)) (hgp : g ≤ p) :
    (((3 : ℝ) ^ p - (3 : ℝ) ^ g + 1) ^ d : ℝ) ≤
      ((interiorMesoCubeGrid d K n outer).card : ℝ) := by
  have hnK : n ≤ K := by omega
  have hpn : (K - n).toNat = p := by omega
  set r : ℤ := Gagliardo.halfRange p - Gagliardo.halfRange g with hrdef
  have h2p := Gagliardo.two_mul_halfRange p
  have h2g := Gagliardo.two_mul_halfRange g
  have hpow : (3 : ℤ) ^ g ≤ (3 : ℤ) ^ p := pow_le_pow_right₀ (by norm_num) hgp
  have hr0 : 0 ≤ r := by omega
  have hrle : r ≤ Gagliardo.halfRange (K - n).toNat := by
    rw [hpn]
    have := Gagliardo.halfRange_nonneg g
    omega
  have h3n : (0 : ℝ) < (3 : ℝ) ^ n := by positivity
  have hKpow : (3 : ℝ) ^ K = (3 : ℝ) ^ n * (3 : ℝ) ^ p := by
    rw [hK, zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_natCast]
  have hOpow : (3 : ℝ) ^ (outer + 1) = (3 : ℝ) ^ n * (3 : ℝ) ^ g := by
    rw [houter, zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_natCast]
  have hrR : 2 * ((r : ℤ) : ℝ) = (3 : ℝ) ^ p - (3 : ℝ) ^ g := by
    have hp := two_mul_halfRange_real p
    have hg := two_mul_halfRange_real g
    rw [hrdef]
    push_cast
    linarith
  have hgeom : (r : ℝ) * (3 : ℝ) ^ n + (3 : ℝ) ^ (outer + 1) / 2 ≤ (3 : ℝ) ^ K / 2 := by
    rw [hKpow, hOpow]
    nlinarith [hrR, h3n]
  have hcardle : (indexBoxGrid d n r).card ≤ (interiorMesoCubeGrid d K n outer).card :=
    Finset.card_le_card (indexBoxGrid_subset_interiorMesoCubeGrid d hnK hrle hgeom)
  have hbox : (indexBoxGrid d n r).card = ((2 * r + 1).toNat) ^ d :=
    card_indexBoxGrid d n r
  have hnat : ((2 * r + 1).toNat : ℤ) = (3 : ℤ) ^ p - (3 : ℤ) ^ g + 1 := by omega
  have hcastR : (((2 * r + 1).toNat : ℕ) : ℝ) = (3 : ℝ) ^ p - (3 : ℝ) ^ g + 1 := by
    have hz : (((2 * r + 1).toNat : ℕ) : ℝ) = (((2 * r + 1).toNat : ℤ) : ℝ) := by
      push_cast; ring
    rw [hz, hnat]
    push_cast
    ring
  calc (((3 : ℝ) ^ p - (3 : ℝ) ^ g + 1) ^ d : ℝ)
      = (((2 * r + 1).toNat : ℕ) : ℝ) ^ d := by rw [hcastR]
    _ = ((indexBoxGrid d n r).card : ℝ) := by rw [hbox]; push_cast; ring
    _ ≤ ((interiorMesoCubeGrid d K n outer).card : ℝ) := by exact_mod_cast hcardle

/-- **The boundary fraction.**  The fraction of the full mesh that the interior
mesh misses is at most `d 3^{g - p}`, i.e. `d 3^{L - K}` where `L = outer + 1`
is the window scale and `K` the big-cube scale. -/
theorem one_sub_interior_card_ratio_le (d : ℕ) {K n outer : ℤ} {p g : ℕ}
    (hK : K = n + (p : ℤ)) (houter : outer + 1 = n + (g : ℤ)) (hgp : g ≤ p) :
    1 - ((interiorMesoCubeGrid d K n outer).card : ℝ) /
        ((mesoCubeGrid d K n).card : ℝ) ≤
      (d : ℝ) * ((3 : ℝ) ^ g / (3 : ℝ) ^ p) := by
  have hnK : n ≤ K := by omega
  have hpn : (K - n).toNat = p := by omega
  have hCM : ((mesoCubeGrid d K n).card : ℝ) = ((3 : ℝ) ^ p) ^ d := by
    rw [card_mesoCubeGrid hnK, hpn]
    push_cast
    rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  have hCI := card_interiorMesoCubeGrid_ge d hK houter hgp
  have h3p : (0 : ℝ) < (3 : ℝ) ^ p := by positivity
  have h3g : (1 : ℝ) ≤ (3 : ℝ) ^ g := one_le_pow₀ (by norm_num)
  have hgple : (3 : ℝ) ^ g ≤ (3 : ℝ) ^ p := pow_le_pow_right₀ (by norm_num) hgp
  set X : ℝ := ((3 : ℝ) ^ p - (3 : ℝ) ^ g + 1) / (3 : ℝ) ^ p with hX
  have hX0 : 0 ≤ X := by
    rw [hX]
    exact div_nonneg (by linarith) h3p.le
  have hX1 : X ≤ 1 := by
    rw [hX, div_le_one h3p]
    linarith
  have hbern : 1 + (d : ℝ) * (X - 1) ≤ X ^ d := by
    have h := one_add_mul_le_pow (a := X - 1) (by linarith) d
    simpa using h
  have hCMpos : (0 : ℝ) < ((mesoCubeGrid d K n).card : ℝ) := by
    rw [hCM]; positivity
  have hratio : X ^ d ≤ ((interiorMesoCubeGrid d K n outer).card : ℝ) /
      ((mesoCubeGrid d K n).card : ℝ) := by
    rw [le_div_iff₀ hCMpos, hCM, hX, div_pow, div_mul_eq_mul_div,
      div_le_iff₀ (by positivity)]
    have hpos : (0 : ℝ) < ((3 : ℝ) ^ p) ^ d := by positivity
    nlinarith [hCI, hpos]
  have hone : (1 : ℝ) - X = ((3 : ℝ) ^ g - 1) / (3 : ℝ) ^ p := by
    rw [hX]
    field_simp
    ring
  have hlast : (d : ℝ) * (1 - X) ≤ (d : ℝ) * ((3 : ℝ) ^ g / (3 : ℝ) ^ p) := by
    rw [hone]
    have hdiv : ((3 : ℝ) ^ g - 1) / (3 : ℝ) ^ p ≤ (3 : ℝ) ^ g / (3 : ℝ) ^ p := by
      rw [sub_div]
      have hpos : (0 : ℝ) ≤ 1 / (3 : ℝ) ^ p := by positivity
      linarith
    exact mul_le_mul_of_nonneg_left hdiv (Nat.cast_nonneg d)
  linarith [hbern, hratio, hlast]

/-! ## The transfer of the fourth-moment grid average -/

/-- **The transfer at the display's own functional.**  The full-mesh
fourth-moment average of `e.lower.bound.oscillations` is the interior one plus
`sqrt(d 3^{g-p})` times the square root of the squared grid average.

only on the scale bookkeeping; nothing about `F`, the corrector or the sample
space is assumed. -/
theorem gridFourthMoment_mesoCubeGrid_le_interior_add {Omega : Type*}
    [MeasurableSpace Omega] (mu : Measure Omega) (d : ℕ) {K n outer : ℤ} {p g : ℕ}
    (hK : K = n + (p : ℤ)) (houter : outer + 1 = n + (g : ℤ)) (hgp : g ≤ p)
    (F : TriadicCube d → Omega → ℝ) :
    gridFourthMoment mu (mesoCubeGrid d K n) F ≤
      gridFourthMoment mu (interiorMesoCubeGrid d K n outer) F +
        Real.sqrt ((d : ℝ) * ((3 : ℝ) ^ g / (3 : ℝ) ^ p)) *
          Real.sqrt (cubeFamilyAverage (mesoCubeGrid d K n)
            (fun R => (∫ omega, F R omega ^ (4 : ℝ) ∂mu) ^ 2)) := by
  have hnn : ∀ R ∈ mesoCubeGrid d K n, 0 ≤ ∫ omega, F R omega ^ (4 : ℝ) ∂mu :=
    fun R _ => integral_nonneg fun omega => rpow_four_nonneg (F R omega)
  have hmain := cubeFamilyAverage_le_add_sqrt_boundaryFraction
    (I := mesoCubeGrid d K n) (J := interiorMesoCubeGrid d K n outer)
    interiorMesoCubeGrid_subset (fun R => ∫ omega, F R omega ^ (4 : ℝ) ∂mu) hnn
  have hfrac : Real.sqrt (1 - ((interiorMesoCubeGrid d K n outer).card : ℝ) /
        ((mesoCubeGrid d K n).card : ℝ)) ≤
      Real.sqrt ((d : ℝ) * ((3 : ℝ) ^ g / (3 : ℝ) ^ p)) :=
    Real.sqrt_le_sqrt (one_sub_interior_card_ratio_le d hK houter hgp)
  have hsq : (0 : ℝ) ≤ Real.sqrt (cubeFamilyAverage (mesoCubeGrid d K n)
      (fun R => (∫ omega, F R omega ^ (4 : ℝ) ∂mu) ^ 2)) := Real.sqrt_nonneg _
  have hmul := mul_le_mul_of_nonneg_right hfrac hsq
  unfold gridFourthMoment
  linarith [hmain, hmul]

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
