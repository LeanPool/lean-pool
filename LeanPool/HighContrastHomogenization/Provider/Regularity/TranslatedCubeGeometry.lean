/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Support.Geometry.CubeMeasure
public import LeanPool.HighContrastHomogenization.Support.Geometry.Translation

/-!
# High-contrast homogenization: Provider.Regularity.TranslatedCubeGeometry

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Triadic cubes displaced by a fixed vector

A triadic cube displaced by a fixed vector is again a half-open box of the same
side length.  Two facts about such a displacement are recorded here.

* The set where the displaced cube and the undisplaced cube disagree has volume
  at most twice the dimension times the relative displacement times the cube
  volume: a fixed displacement is asymptotically invisible on a growing cube.
* A displaced cube is compatible with the triadic grid at every scale whose side
  length divides each coordinate of the displacement, so a triadic cube of that
  scale is either contained in the displaced cube or disjoint from it.

Both statements are elementary interval arithmetic, and both are used to bound
the positive Besov norm of the difference of two cube indicator functions.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory Set

variable {d : ℕ}

/-- The half-open realization of a triadic cube displaced by a fixed vector. -/
@[expose]
def translatedCubeSet (Q : TriadicCube d) (t : Vec d) : Set (Vec d) :=
  translateSet t (cubeSet Q)

/-- The set on which two displacements of a triadic cube disagree. -/
@[expose]
def cubeTranslationGap (Q : TriadicCube d) (u v : Vec d) : Set (Vec d) :=
  (translatedCubeSet Q u \ translatedCubeSet Q v) ∪
    (translatedCubeSet Q v \ translatedCubeSet Q u)

/-! ## Coordinate description -/

theorem mem_translatedCubeSet_iff {Q : TriadicCube d} {t x : Vec d} :
    x ∈ translatedCubeSet Q t ↔
      ∀ i, ((Q.index i : ℝ) - (1 / 2 : ℝ)) * cubeScaleFactor Q + t i ≤ x i ∧
        x i < ((Q.index i : ℝ) + (1 / 2 : ℝ)) * cubeScaleFactor Q + t i := by
  rw [translatedCubeSet, mem_translateSet_iff_sub_mem]
  constructor
  · intro hx i
    have hxi : ((Q.index i : ℝ) - (1 / 2 : ℝ)) * cubeScaleFactor Q ≤ x i - t i ∧
        x i - t i < ((Q.index i : ℝ) + (1 / 2 : ℝ)) * cubeScaleFactor Q := hx i
    exact ⟨by linarith only [hxi.1], by linarith only [hxi.2]⟩
  · intro hx i
    have hxi := hx i
    simp only [Pi.sub_apply]
    exact ⟨by linarith only [hxi.1], by linarith only [hxi.2]⟩

theorem translatedCubeSet_eq_pi_Ico (Q : TriadicCube d) (t : Vec d) :
    translatedCubeSet Q t =
      Set.pi Set.univ fun i : Fin d =>
        Set.Ico
          (((Q.index i : ℝ) - (1 / 2 : ℝ)) * cubeScaleFactor Q + t i)
          (((Q.index i : ℝ) + (1 / 2 : ℝ)) * cubeScaleFactor Q + t i) := by
  ext x
  rw [mem_translatedCubeSet_iff]
  constructor
  · intro hx i _hi
    exact ⟨(hx i).1, (hx i).2⟩
  · intro hx i
    exact ⟨(hx i (Set.mem_univ i)).1, (hx i (Set.mem_univ i)).2⟩

@[simp] theorem translatedCubeSet_zero (Q : TriadicCube d) :
    translatedCubeSet Q (0 : Vec d) = cubeSet Q :=
  translateSet_zero (cubeSet Q)

theorem measurableSet_translatedCubeSet (Q : TriadicCube d) (t : Vec d) :
    MeasurableSet (translatedCubeSet Q t) := by
  rw [translatedCubeSet_eq_pi_Ico]
  exact MeasurableSet.univ_pi fun _ => measurableSet_Ico

theorem measurableSet_cubeTranslationGap (Q : TriadicCube d) (u v : Vec d) :
    MeasurableSet (cubeTranslationGap Q u v) :=
  ((measurableSet_translatedCubeSet Q u).diff
      (measurableSet_translatedCubeSet Q v)).union
    ((measurableSet_translatedCubeSet Q v).diff (measurableSet_translatedCubeSet Q u))

/-! ## Volumes -/

private theorem cubeScaleFactor_pos' (Q : TriadicCube d) :
    0 < cubeScaleFactor Q :=
  zpow_pos (by norm_num : (0 : ℝ) < 3) _

theorem volume_translatedCubeSet (Q : TriadicCube d) (t : Vec d) :
    volume (translatedCubeSet Q t) = volume (cubeSet Q) :=
  volume_translateSet_eq t (cubeSet Q)

theorem volume_translatedCubeSet_ne_top (Q : TriadicCube d) (t : Vec d) :
    volume (translatedCubeSet Q t) ≠ ⊤ := by
  rw [volume_translatedCubeSet]
  exact (volume_cubeSet_lt_top Q).ne

theorem volume_translatedCubeSet_toReal (Q : TriadicCube d) (t : Vec d) :
    (volume (translatedCubeSet Q t)).toReal = cubeVolume Q := by
  rw [volume_translatedCubeSet, volume_cubeSet_toReal]

/-! ## The part common to two displacements -/

private theorem inter_translatedCubeSet_eq_pi (Q : TriadicCube d) (u v : Vec d) :
    translatedCubeSet Q u ∩ translatedCubeSet Q v =
      Set.pi Set.univ fun i : Fin d =>
        Set.Ico
          (max (((Q.index i : ℝ) - (1 / 2 : ℝ)) * cubeScaleFactor Q + u i)
            (((Q.index i : ℝ) - (1 / 2 : ℝ)) * cubeScaleFactor Q + v i))
          (min (((Q.index i : ℝ) + (1 / 2 : ℝ)) * cubeScaleFactor Q + u i)
            (((Q.index i : ℝ) + (1 / 2 : ℝ)) * cubeScaleFactor Q + v i)) := by
  rw [translatedCubeSet_eq_pi_Ico, translatedCubeSet_eq_pi_Ico,
    ← Set.pi_inter_distrib]
  exact Set.pi_congr rfl fun i _ => Set.Ico_inter_Ico

/-- The volume common to two displacements of a triadic cube is the product of
the shortened side lengths. -/
theorem volume_inter_translatedCubeSet_toReal (Q : TriadicCube d) (u v : Vec d)
    (huv : ∀ i, |u i - v i| ≤ cubeScaleFactor Q) :
    (volume (translatedCubeSet Q u ∩ translatedCubeSet Q v)).toReal =
      ∏ i : Fin d, (cubeScaleFactor Q - |u i - v i|) := by
  have hkey : ∀ i : Fin d,
      min (((Q.index i : ℝ) + (1 / 2 : ℝ)) * cubeScaleFactor Q + u i)
          (((Q.index i : ℝ) + (1 / 2 : ℝ)) * cubeScaleFactor Q + v i) -
        max (((Q.index i : ℝ) - (1 / 2 : ℝ)) * cubeScaleFactor Q + u i)
          (((Q.index i : ℝ) - (1 / 2 : ℝ)) * cubeScaleFactor Q + v i) =
      cubeScaleFactor Q - |u i - v i| := by
    intro i
    rcases le_total (v i) (u i) with hti | hti
    · rw [max_eq_left (by linarith only [hti]),
        min_eq_right (by linarith only [hti]),
        abs_of_nonneg (by linarith only [hti] : (0 : ℝ) ≤ u i - v i)]
      ring
    · rw [max_eq_right (by linarith only [hti]),
        min_eq_left (by linarith only [hti]),
        abs_of_nonpos (by linarith only [hti] : u i - v i ≤ 0)]
      ring
  have hab : (fun i : Fin d =>
        max (((Q.index i : ℝ) - (1 / 2 : ℝ)) * cubeScaleFactor Q + u i)
          (((Q.index i : ℝ) - (1 / 2 : ℝ)) * cubeScaleFactor Q + v i)) ≤
      fun i : Fin d =>
        min (((Q.index i : ℝ) + (1 / 2 : ℝ)) * cubeScaleFactor Q + u i)
          (((Q.index i : ℝ) + (1 / 2 : ℝ)) * cubeScaleFactor Q + v i) := by
    intro i
    have h := hkey i
    have habs := huv i
    have habs0 : 0 ≤ |u i - v i| := abs_nonneg _
    linarith only [h, habs, habs0]
  rw [inter_translatedCubeSet_eq_pi, Real.volume_pi_Ico_toReal (ι := Fin d) hab]
  exact Finset.prod_congr rfl fun i _ => hkey i

/-! ## The relative volume of the disagreement set -/

private theorem one_sub_pow_le_mul_one_sub {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (n : ℕ) : 1 - r ^ n ≤ (n : ℝ) * (1 - r) := by
  induction n with
  | zero => simp
  | succ m ih =>
      have hpow : r ^ m ≤ 1 := pow_le_one₀ hr0 hr1
      have hle : r ^ m * (1 - r) ≤ 1 - r :=
        mul_le_of_le_one_left (by linarith only [hr1]) hpow
      have hstep : 1 - r ^ (m + 1) = (1 - r ^ m) + r ^ m * (1 - r) := by ring
      rw [hstep]
      push_cast
      linarith only [ih, hle]

/-- Two displacements differing by at most `V` in every coordinate disagree only
on a set whose relative volume is at most twice the dimension times the relative
difference. -/
theorem volume_cubeTranslationGap_toReal_le (Q : TriadicCube d) (u v : Vec d)
    {V : ℝ} (hV : 0 ≤ V) (hVle : V ≤ cubeScaleFactor Q)
    (huv : ∀ i, |u i - v i| ≤ V) :
    (volume (cubeTranslationGap Q u v)).toReal ≤
      2 * (d : ℝ) * (V / cubeScaleFactor Q) * cubeVolume Q := by
  set L : ℝ := cubeScaleFactor Q with hLdef
  have hLpos : 0 < L := cubeScaleFactor_pos' Q
  have htL : ∀ i, |u i - v i| ≤ L := fun i => (huv i).trans hVle
  have hvolQ : cubeVolume Q = L ^ d := rfl
  have hinterTop : volume (translatedCubeSet Q u ∩ translatedCubeSet Q v) ≠ ⊤ :=
    measure_ne_top_of_subset Set.inter_subset_left
      (volume_translatedCubeSet_ne_top Q u)
  have hmeasInter : MeasurableSet (translatedCubeSet Q u ∩ translatedCubeSet Q v) :=
    (measurableSet_translatedCubeSet Q u).inter (measurableSet_translatedCubeSet Q v)
  have hinterReal := volume_inter_translatedCubeSet_toReal Q u v htL
  have hconst : (L - V) ^ d = ∏ _i : Fin d, (L - V) := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hinterLower : (L - V) ^ d ≤
      (volume (translatedCubeSet Q u ∩ translatedCubeSet Q v)).toReal := by
    rw [hinterReal, hconst]
    exact Finset.prod_le_prod₀ (fun i _ => by linarith only [hV, hVle])
      (fun i _ => by linarith only [huv i])
  have hdiffU :
      (volume (translatedCubeSet Q u \ translatedCubeSet Q v)).toReal ≤
        L ^ d - (L - V) ^ d := by
    have hset : translatedCubeSet Q u \ translatedCubeSet Q v =
        translatedCubeSet Q u \ (translatedCubeSet Q u ∩ translatedCubeSet Q v) :=
      Set.sdiff_self_inter.symm
    have hmeas :
        volume (translatedCubeSet Q u \
            (translatedCubeSet Q u ∩ translatedCubeSet Q v)) =
          volume (translatedCubeSet Q u) -
            volume (translatedCubeSet Q u ∩ translatedCubeSet Q v) :=
      measure_sdiff Set.inter_subset_left hmeasInter.nullMeasurableSet hinterTop
    rw [hset, hmeas, ENNReal.toReal_sub_of_le
      (measure_mono Set.inter_subset_left) (volume_translatedCubeSet_ne_top Q u),
      volume_translatedCubeSet_toReal, hvolQ]
    linarith only [hinterLower]
  have hdiffV :
      (volume (translatedCubeSet Q v \ translatedCubeSet Q u)).toReal ≤
        L ^ d - (L - V) ^ d := by
    have hset : translatedCubeSet Q v \ translatedCubeSet Q u =
        translatedCubeSet Q v \ (translatedCubeSet Q v ∩ translatedCubeSet Q u) :=
      Set.sdiff_self_inter.symm
    have hmeasInter' : MeasurableSet (translatedCubeSet Q v ∩ translatedCubeSet Q u) :=
      (measurableSet_translatedCubeSet Q v).inter (measurableSet_translatedCubeSet Q u)
    have hinterTop' : volume (translatedCubeSet Q v ∩ translatedCubeSet Q u) ≠ ⊤ := by
      rw [Set.inter_comm]; exact hinterTop
    have hmeas :
        volume (translatedCubeSet Q v \
            (translatedCubeSet Q v ∩ translatedCubeSet Q u)) =
          volume (translatedCubeSet Q v) -
            volume (translatedCubeSet Q v ∩ translatedCubeSet Q u) :=
      measure_sdiff Set.inter_subset_left hmeasInter'.nullMeasurableSet hinterTop'
    have hleV : volume (translatedCubeSet Q v ∩ translatedCubeSet Q u) ≤
        volume (translatedCubeSet Q v) := measure_mono Set.inter_subset_left
    have hswap : (volume (translatedCubeSet Q v ∩ translatedCubeSet Q u)).toReal =
        (volume (translatedCubeSet Q u ∩ translatedCubeSet Q v)).toReal := by
      rw [Set.inter_comm]
    rw [hset, hmeas, ENNReal.toReal_sub_of_le hleV
      (volume_translatedCubeSet_ne_top Q v),
      volume_translatedCubeSet_toReal, hswap, hvolQ]
    linarith only [hinterLower]
  have hgap : L ^ d - (L - V) ^ d ≤ (d : ℝ) * (V / L) * L ^ d := by
    have hr0 : (0 : ℝ) ≤ (L - V) / L :=
      div_nonneg (by linarith only [hVle]) hLpos.le
    have hr1 : (L - V) / L ≤ 1 := by
      rw [div_le_one hLpos]; linarith only [hV]
    have hkey := one_sub_pow_le_mul_one_sub hr0 hr1 d
    have hone : 1 - (L - V) / L = V / L := by
      field_simp
      ring
    rw [hone, div_pow] at hkey
    have hLd : (0 : ℝ) < L ^ d := by positivity
    have hmul := mul_le_mul_of_nonneg_right hkey hLd.le
    calc
      L ^ d - (L - V) ^ d = (1 - (L - V) ^ d / L ^ d) * L ^ d := by field_simp
      _ ≤ (d : ℝ) * (V / L) * L ^ d := hmul
  have hUtop : volume (translatedCubeSet Q u \ translatedCubeSet Q v) ≠ ⊤ :=
    measure_ne_top_of_subset Set.sdiff_subset (volume_translatedCubeSet_ne_top Q u)
  have hVtop : volume (translatedCubeSet Q v \ translatedCubeSet Q u) ≠ ⊤ :=
    measure_ne_top_of_subset Set.sdiff_subset (volume_translatedCubeSet_ne_top Q v)
  have hunion :
      volume (cubeTranslationGap Q u v) ≤
        volume (translatedCubeSet Q u \ translatedCubeSet Q v) +
          volume (translatedCubeSet Q v \ translatedCubeSet Q u) :=
    measure_union_le _ _
  have hsumTop :
      volume (translatedCubeSet Q u \ translatedCubeSet Q v) +
        volume (translatedCubeSet Q v \ translatedCubeSet Q u) ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨hUtop, hVtop⟩
  have hreal := ENNReal.toReal_mono hsumTop hunion
  rw [ENNReal.toReal_add hUtop hVtop] at hreal
  rw [hvolQ]
  linarith only [hreal, hdiffU, hdiffV, hgap]

/-! ## Compatibility with the triadic grid -/

private theorem Ico_subset_or_disjoint_of_int_offset {r : ℝ} (hr : 0 < r) {M : ℕ}
    {b a : ℝ} {p : ℤ} (ha : a = b + (p : ℝ) * r) :
    Set.Ico b (b + r) ⊆ Set.Ico a (a + (M : ℝ) * r) ∨
      Disjoint (Set.Ico b (b + r)) (Set.Ico a (a + (M : ℝ) * r)) := by
  by_cases hcase : p ≤ 0 ∧ 1 ≤ p + (M : ℤ)
  · refine Or.inl ?_
    obtain ⟨hp0, hpM⟩ := hcase
    have hpr : (p : ℝ) ≤ 0 := by exact_mod_cast hp0
    have hlow : a ≤ b := by
      have hnp : (p : ℝ) * r ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hpr hr.le
      rw [ha]; linarith only [hnp]
    have hcast : (1 : ℝ) ≤ (p : ℝ) + (M : ℝ) := by exact_mod_cast hpM
    have hhigh : b + r ≤ a + (M : ℝ) * r := by
      have hmul : r ≤ ((p : ℝ) + (M : ℝ)) * r := by nlinarith only [hcast, hr]
      rw [ha]; nlinarith only [hmul]
    exact Set.Ico_subset_Ico hlow hhigh
  · refine Or.inr ?_
    rw [Set.disjoint_left]
    intro x hx hx'
    rcases le_or_gt p 0 with hp | hp
    · have hpM : p + (M : ℤ) ≤ 0 := by
        by_contra hcon
        exact hcase ⟨hp, by omega⟩
      have hcast : (p : ℝ) + (M : ℝ) ≤ 0 := by exact_mod_cast hpM
      have hhigh : a + (M : ℝ) * r ≤ b := by
        rw [ha]; nlinarith only [hcast, hr]
      exact absurd hx'.2 (not_lt.2 (le_trans hhigh hx.1))
    · have hcast : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
      have hlow : b + r ≤ a := by
        rw [ha]; nlinarith only [hcast, hr]
      exact absurd hx.2 (not_lt.2 (le_trans hlow hx'.1))

/-- A triadic cube whose side length divides every coordinate of the
displacement is either contained in the displaced cube or disjoint from it. -/
theorem cubeSet_subset_or_disjoint_translatedCubeSet
    {R A : TriadicCube d} {t : Vec d} (hscale : R.scale ≤ A.scale)
    (hlat : ∀ i, ∃ p : ℤ, t i = (p : ℝ) * cubeScaleFactor R) :
    cubeSet R ⊆ translatedCubeSet A t ∨
      Disjoint (cubeSet R) (translatedCubeSet A t) := by
  classical
  set r : ℝ := cubeScaleFactor R with hrdef
  have hrpos : 0 < r := cubeScaleFactor_pos' R
  set k : ℕ := (A.scale - R.scale).toNat with hkdef
  have hkcast : ((k : ℤ)) = A.scale - R.scale := Int.toNat_of_nonneg (by omega)
  set M : ℕ := 3 ^ k with hMdef
  have hMr : (M : ℝ) * r = cubeScaleFactor A := by
    have hMreal : (M : ℝ) = (3 : ℝ) ^ ((k : ℤ)) := by
      rw [hMdef]; push_cast; rw [zpow_natCast]
    rw [hMreal, hrdef, cubeScaleFactor, cubeScaleFactor,
      ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), hkcast]
    congr 1
    omega
  obtain ⟨h, hh⟩ : ∃ h : ℕ, M = 2 * h + 1 := by
    have hodd : Odd M := by
      rw [hMdef]
      exact Odd.pow (by decide)
    obtain ⟨h, hh⟩ := hodd
    exact ⟨h, by omega⟩
  have hoffset : ∀ i : Fin d, ∃ p : ℤ,
      ((A.index i : ℝ) - (1 / 2 : ℝ)) * cubeScaleFactor A + t i =
        ((R.index i : ℝ) - (1 / 2 : ℝ)) * r + (p : ℝ) * r := by
    intro i
    obtain ⟨pi, hpi⟩ := hlat i
    refine ⟨A.index i * (M : ℤ) - (h : ℤ) + pi - R.index i, ?_⟩
    have hMval : (M : ℝ) = 2 * (h : ℝ) + 1 := by
      rw [hh]; push_cast; ring
    rw [← hMr, hpi]
    push_cast
    rw [hMval]
    ring
  by_cases hall : ∀ i : Fin d,
      Set.Ico (((R.index i : ℝ) - (1 / 2 : ℝ)) * r)
          (((R.index i : ℝ) - (1 / 2 : ℝ)) * r + r) ⊆
        Set.Ico (((A.index i : ℝ) - (1 / 2 : ℝ)) * cubeScaleFactor A + t i)
          (((A.index i : ℝ) - (1 / 2 : ℝ)) * cubeScaleFactor A + t i + (M : ℝ) * r)
  · refine Or.inl ?_
    intro x hx
    rw [mem_translatedCubeSet_iff]
    intro i
    have hxi : ((R.index i : ℝ) - (1 / 2 : ℝ)) * cubeScaleFactor R ≤ x i ∧
        x i < ((R.index i : ℝ) + (1 / 2 : ℝ)) * cubeScaleFactor R := hx i
    have hxi' : x i ∈ Set.Ico (((R.index i : ℝ) - (1 / 2 : ℝ)) * r)
        (((R.index i : ℝ) - (1 / 2 : ℝ)) * r + r) := by
      refine ⟨hxi.1, ?_⟩
      have h2 := hxi.2
      rw [hrdef]
      linarith only [h2]
    have hmem := hall i hxi'
    refine ⟨hmem.1, ?_⟩
    have h3 := hmem.2
    rw [hMr] at h3
    linarith only [h3]
  · refine Or.inr ?_
    push Not at hall
    obtain ⟨i, hi⟩ := hall
    obtain ⟨p, hp⟩ := hoffset i
    have hdisj := Ico_subset_or_disjoint_of_int_offset (r := r) hrpos (M := M)
      (b := ((R.index i : ℝ) - (1 / 2 : ℝ)) * r)
      (a := ((A.index i : ℝ) - (1 / 2 : ℝ)) * cubeScaleFactor A + t i) (p := p) hp
    rcases hdisj with hsub | hdis
    · exact absurd hsub hi
    rw [Set.disjoint_left]
    intro x hx hx'
    have hxi : ((R.index i : ℝ) - (1 / 2 : ℝ)) * cubeScaleFactor R ≤ x i ∧
        x i < ((R.index i : ℝ) + (1 / 2 : ℝ)) * cubeScaleFactor R := hx i
    have hxi' := (mem_translatedCubeSet_iff.mp hx') i
    rw [Set.disjoint_left] at hdis
    refine hdis (a := x i) ?_ ?_
    · refine ⟨hxi.1, ?_⟩
      have h2 := hxi.2
      rw [hrdef]
      linarith only [h2]
    · refine ⟨hxi'.1, ?_⟩
      have h3 := hxi'.2
      rw [hMr]
      linarith only [h3]

end HighContrast
end HCPolySupport
