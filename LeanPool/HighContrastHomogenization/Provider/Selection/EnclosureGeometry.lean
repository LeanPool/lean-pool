/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Selection.RoundedHops
public import LeanPool.HighContrastHomogenization.Provider.Recurrence.AdaptedCell
public import LeanPool.HighContrastHomogenization.Provider.Transport.WhitneyLayer
public import LeanPool.HighContrastHomogenization.Setup.SelectionObjects

/-!
# High-contrast homogenization: Provider.Selection.EnclosureGeometry

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Geometry of the selection enclosure

The grids retained by the selector have exponentially controlled eccentricity.
After rounding, this gives a uniform operator-norm bound and hence a fixed
enlargement that places every adapted cell inside a centered triadic cube.
The same enclosure contains all aligned cells whose centers lie in either
terminal cell.
-/

namespace HCPolySupport.HighContrast.Selection

open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-! ## The grid enlargement -/

/-- The integer enlargement needed to contain every grid used by a capped
selection run. -/
@[expose]
def gridEnlargement (d : ℕ) (chop : ℝ) (Ncap : ℕ) : ℕ :=
  ⌈Real.logb 3 (Real.sqrt d * (100 / 99 : ℝ)) +
      chop * ((Ncap + 1 : ℕ) : ℝ) / Real.log 3⌉₊

/-! ## Linear images of centered cubes -/

/-- An operator-norm bound turns an adapted cell into a centered cube after a
fixed integer enlargement. -/
theorem adaptedCell_subset_centeredCube_add (hd : 1 ≤ d) {q : Mat d} {T : ℤ}
    {G : ℕ} (hq : ‖q‖ * Real.sqrt d ≤ (3 : ℝ) ^ G) :
    adaptedCell q T ⊆ centeredCube d (T + (G : ℤ)) := by
  rintro x ⟨y, hy, rfl⟩
  rw [Recurrence.mem_centeredCube_iff] at hy ⊢
  let c : ℝ := (1 / 2 : ℝ) * (3 : ℝ) ^ T
  have hc : 0 < c := by dsimp [c]; positivity
  have hynorm : ‖y‖ < c := by
    rw [pi_norm_lt_iff hc]
    intro i
    rw [Real.norm_eq_abs, abs_lt]
    simpa only [c, neg_mul] using hy i
  have hycoord : ∀ i : Fin d, |y i| ≤ ‖y‖ := by
    intro i
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm y i
  have hpow : (3 : ℝ) ^ (T + (G : ℤ)) = (3 : ℝ) ^ T * (3 : ℝ) ^ G := by
    rw [zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_natCast]
  intro i
  have habs := Transport.abs_matVecMul_le_of_abs_le q hycoord i
  have hstrict : |matVecMul q y i| < (1 / 2 : ℝ) * (3 : ℝ) ^ (T + (G : ℤ)) := by
    by_cases hqzero : ‖q‖ = 0
    · calc
        |matVecMul q y i| ≤ ‖q‖ * (Real.sqrt d * ‖y‖) := habs
        _ = 0 := by rw [hqzero, zero_mul]
        _ < (1 / 2 : ℝ) * (3 : ℝ) ^ (T + (G : ℤ)) := by positivity
    · have hcoef : 0 < ‖q‖ * Real.sqrt d := by
        exact mul_pos (lt_of_le_of_ne (norm_nonneg q) (Ne.symm hqzero))
          (Real.sqrt_pos.2 (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)))
      calc
        |matVecMul q y i| ≤ ‖q‖ * (Real.sqrt d * ‖y‖) := habs
        _ = (‖q‖ * Real.sqrt d) * ‖y‖ := by ring
        _ < (‖q‖ * Real.sqrt d) * c := mul_lt_mul_of_pos_left hynorm hcoef
        _ ≤ (3 : ℝ) ^ G * c := mul_le_mul_of_nonneg_right hq hc.le
        _ = (1 / 2 : ℝ) * (3 : ℝ) ^ (T + (G : ℤ)) := by
          rw [hpow]
          dsimp [c]
          ring
  simpa only [neg_mul] using (abs_lt.mp hstrict)

/-- A rounded grid whose witness has the capped eccentricity bound fits in the
displayed enlarged centered cube. -/
theorem roundedGrid_adaptedCell_subset_gridEnlargement (hd : 2 ≤ d)
    {jdag T : ℤ} (hjdag : (kZero d : ℤ) ≤ jdag) {m : Mat d} (hm : m.PosDef)
    {chop : ℝ} {Ncap : ℕ}
    (hecc : witnessEccentricity m ≤
      Real.exp (chop * ((Ncap + 1 : ℕ) : ℝ))) :
    adaptedCell (roundedGrid jdag m) T ⊆
      centeredCube d (T + (gridEnlargement d chop Ncap : ℤ)) := by
  let : NeZero d := ⟨by omega⟩
  let a : ℝ := Real.sqrt d * (100 / 99 : ℝ)
  let e : ℝ := chop * ((Ncap + 1 : ℕ) : ℝ)
  have ha : 0 < a := by dsimp [a]; positivity
  have hlog3 : Real.log 3 ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one (by norm_num) (by norm_num)
  have hpow : (3 : ℝ) ^
      (Real.logb 3 a + e / Real.log 3) = a * Real.exp e := by
    rw [Real.rpow_add (by norm_num),
      Real.rpow_logb (by norm_num) (by norm_num) ha,
      Real.rpow_def_of_pos (by norm_num)]
    congr 1
    congr 1
    field_simp
  have hceil : Real.logb 3 a + e / Real.log 3 ≤
      (gridEnlargement d chop Ncap : ℝ) := by
    dsimp [gridEnlargement, a, e]
    exact Nat.le_ceil _
  have hlarge : a * Real.exp e ≤ (3 : ℝ) ^ gridEnlargement d chop Ncap := by
    have hmono := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) hceil
    rw [hpow, Real.rpow_natCast] at hmono
    exact hmono
  have hnorm := norm_roundedGrid_le hjdag hm
  apply adaptedCell_subset_centeredCube_add (Nat.one_le_iff_ne_zero.mpr (by omega))
  calc
    ‖roundedGrid jdag m‖ * Real.sqrt d
        ≤ ((100 / 99 : ℝ) * witnessEccentricity m) * Real.sqrt d :=
      mul_le_mul_of_nonneg_right hnorm (Real.sqrt_nonneg d)
    _ ≤ ((100 / 99 : ℝ) * Real.exp e) * Real.sqrt d :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hecc (by norm_num)) (Real.sqrt_nonneg d)
    _ = a * Real.exp e := by dsimp [a, e]; ring
    _ ≤ (3 : ℝ) ^ gridEnlargement d chop Ncap := hlarge

/-! ## The enlargement budget -/

/-- The capped enlargement is bounded by the sharp coefficient used in the
execution-window budget. -/
theorem gridEnlargement_le (hd : 2 ≤ d) {chop CN Lam : ℝ}
    (hchop : 0 ≤ chop) (hLam : 1 ≤ Lam) (Ncap : ℕ)
    (hcap : ((Ncap + 1 : ℕ) : ℝ) ≤ (CN + 3) * Lam) :
    (gridEnlargement d chop Ncap : ℝ) ≤
      (2 + (1 / 2 : ℝ) * Real.logb 3 d +
        chop / Real.log 3 * (CN + 3)) * Lam := by
  have hd0 : (0 : ℝ) ≤ d := by positivity
  have hd1 : (1 : ℝ) < d := by exact_mod_cast lt_of_lt_of_le (by omega : 1 < 2) hd
  have hsqrt0 : 0 < Real.sqrt d := Real.sqrt_pos.2 (lt_trans zero_lt_one hd1)
  have hsqrt1 : (1 : ℝ) ≤ Real.sqrt d := Real.one_le_sqrt.mpr hd1.le
  have hbase1 : (1 : ℝ) < Real.sqrt d * (100 / 99 : ℝ) := by
    calc
      (1 : ℝ) < 100 / 99 := by norm_num
      _ ≤ Real.sqrt d * (100 / 99 : ℝ) := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hsqrt1 (by norm_num : (0 : ℝ) ≤
          100 / 99)
  have hlogbase :
      Real.logb 3 (Real.sqrt d * (100 / 99 : ℝ)) =
        (1 / 2 : ℝ) * Real.logb 3 d + Real.logb 3 (100 / 99 : ℝ) := by
    rw [Real.logb_mul hsqrt0.ne' (by norm_num : (100 / 99 : ℝ) ≠ 0)]
    simp only [Real.logb]
    rw [Real.log_sqrt hd0]
    ring
  have hratio : Real.logb 3 (100 / 99 : ℝ) < 1 := by
    rw [← Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 3)]
    exact Real.logb_lt_logb (by norm_num : (1 : ℝ) < 3)
      (by norm_num : (0 : ℝ) < 100 / 99) (by norm_num : (100 / 99 : ℝ) < 3)
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hterm0 : 0 ≤ chop * ((Ncap + 1 : ℕ) : ℝ) / Real.log 3 := by positivity
  have hx0 : 0 ≤ Real.logb 3 (Real.sqrt d * (100 / 99 : ℝ)) +
      chop * ((Ncap + 1 : ℕ) : ℝ) / Real.log 3 := by
    exact add_nonneg (Real.logb_pos (by norm_num : (1 : ℝ) < 3) hbase1).le hterm0
  have hceil := Nat.ceil_lt_add_one hx0
  have hfirst : (gridEnlargement d chop Ncap : ℝ) ≤
      2 + (1 / 2 : ℝ) * Real.logb 3 d +
        chop / Real.log 3 * ((Ncap + 1 : ℕ) : ℝ) := by
    change (gridEnlargement d chop Ncap : ℝ) <
      Real.logb 3 (Real.sqrt d * (100 / 99 : ℝ)) +
        chop * ((Ncap + 1 : ℕ) : ℝ) / Real.log 3 + 1 at hceil
    calc
      (gridEnlargement d chop Ncap : ℝ) ≤
          Real.logb 3 (Real.sqrt d * (100 / 99 : ℝ)) +
            chop * ((Ncap + 1 : ℕ) : ℝ) / Real.log 3 + 1 := hceil.le
      _ ≤ (1 / 2 : ℝ) * Real.logb 3 d + 1 +
          chop * ((Ncap + 1 : ℕ) : ℝ) / Real.log 3 + 1 := by
        rw [hlogbase]
        have := hratio.le
        gcongr
      _ = 2 + (1 / 2 : ℝ) * Real.logb 3 d +
          chop / Real.log 3 * ((Ncap + 1 : ℕ) : ℝ) := by ring
  have hcoef : 0 ≤ chop / Real.log 3 := div_nonneg hchop hlog3.le
  have hcap' := mul_le_mul_of_nonneg_left hcap hcoef
  have hlogd : 0 ≤ Real.logb 3 d :=
    (Real.logb_pos (by norm_num : (1 : ℝ) < 3) hd1).le
  have hconst : 0 ≤ 2 + (1 / 2 : ℝ) * Real.logb 3 d := by positivity
  have habsorb : 2 + (1 / 2 : ℝ) * Real.logb 3 d ≤
      (2 + (1 / 2 : ℝ) * Real.logb 3 d) * Lam := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hLam hconst
  calc
    (gridEnlargement d chop Ncap : ℝ) ≤
        2 + (1 / 2 : ℝ) * Real.logb 3 d +
          chop / Real.log 3 * ((Ncap + 1 : ℕ) : ℝ) := hfirst
    _ ≤ (2 + (1 / 2 : ℝ) * Real.logb 3 d) * Lam +
        chop / Real.log 3 * ((CN + 3) * Lam) := add_le_add habsorb hcap'
    _ = (2 + (1 / 2 : ℝ) * Real.logb 3 d +
        chop / Real.log 3 * (CN + 3)) * Lam := by ring

/-! ## The terminal cell family -/

/-- An aligned cell whose center belongs to a larger adapted cell is contained
in that cell. -/
theorem adaptedCellTranslate_subset_of_mem_containedCenters {q : Mat d}
    (hq : q.PosDef) {k v : ℤ} (hkv : k ≤ v) {z : Vec d}
    (hz : z ∈ containedCenters q k v) :
    adaptedCellTranslate q k z ⊆ adaptedCell q v := by
  rcases hz with ⟨⟨w, rfl⟩, hw⟩
  change adaptedCellAt q k w ⊆ adaptedCell q v
  exact Recurrence.adaptedCellAt_subset_adaptedCell hq hkv hw

/-- Enclosure of the terminal adapted-cell tower implies both terminal
enclosure clauses, including every aligned cell below the starting scale. -/
theorem terminal_enclosure_of_adaptedCell_enclosure {q : Mat d} (hq : q.PosDef)
    {jdag s t Mexec : ℤ} (hjs : jdag ≤ s) (hst : s ≤ t)
    (hwhole : ∀ k : ℤ, jdag ≤ k → k ≤ t →
      adaptedCell q k ⊆ centeredCube d Mexec) :
    (∀ k : ℤ, jdag ≤ k → k ≤ t →
      adaptedCell q k ⊆ centeredCube d Mexec) ∧
    (∀ k : ℤ, k < jdag → ∀ v : ℤ, v = s ∨ v = t →
      ∀ z ∈ containedCenters q k v,
        adaptedCellTranslate q k z ⊆ centeredCube d Mexec) := by
  refine ⟨hwhole, ?_⟩
  intro k hk v hv z hz
  rcases hv with hvs | hvt
  · have hjv : jdag ≤ v := by simpa only [hvs] using hjs
    have hvt' : v ≤ t := by simpa only [hvs] using hst
    exact (adaptedCellTranslate_subset_of_mem_containedCenters hq
      (hk.le.trans hjv) hz).trans (hwhole v hjv hvt')
  · have hjv : jdag ≤ v := by simpa only [hvt] using hjs.trans hst
    have hvt' : v ≤ t := hvt.le
    exact (adaptedCellTranslate_subset_of_mem_containedCenters hq
      (hk.le.trans hjv) hz).trans (hwhole v hjv hvt')

end

end HCPolySupport.HighContrast.Selection
