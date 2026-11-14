/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P4984T1ClosedGap
public import LeanPool.ApollonianSuperharmonic.P4828T1Gap
public import LeanPool.ApollonianSuperharmonic.P4828T1LineSupport
public import LeanPool.ApollonianSuperharmonic.P5023T1ContactHull
public import LeanPool.ApollonianSuperharmonic.P5023T1CircularSide
public import LeanPool.ApollonianSuperharmonic.P5023T1CircularEstimate
public import LeanPool.ApollonianSuperharmonic.P5023T1LineSideGeometry
public import LeanPool.ApollonianSuperharmonic.P5023T1LineEstimate
public import LeanPool.ApollonianSuperharmonic.P5023T1ConvexDiameter

-- [TABLET NODE: P4984T1ContactDiameter]

/-!
# P4984T1ContactDiameter

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4984T1ContactDiameter (L : Real)
    (q : Fin 4 → CircleCoordinates) (hq : ProperBandQuadruple q)
    (hs : P4828T1LineSupport L q)
    (hi : P4828T1Disk (q 0) ⊆ P4828T1Gap L q) :
    Metric.diam (P4984T1ClosedGap L q) ≤
      6 * Real.sqrt (1 / ((q 0).1 : Real)) := by
-- BODY
  let p (k : Fin 4) : ℂ := (q k).2 / ((q k).1 : ℝ)
  let r (k : Fin 4) : ℝ := 1 / ((q k).1 : ℝ)
  let v := P5023T1ContactVertices L q
  have curv := ProperBandCurvatureStructure q hq
  have hR : 0 < r 0 := one_div_pos.mpr (by exact_mod_cast curv.1)
  have radii (i : Fin 3) (hp : 0 < (q i.succ).1) :
      0 < r i.succ ∧ r 0 < r i.succ ∧ r i.succ ≤ 1 := by
    have hpR : (0 : ℝ) < (q i.succ).1 := by exact_mod_cast hp
    have hp1 : (1 : ℝ) ≤ (q i.succ).1 := by
      exact_mod_cast (show (1 : ℤ) ≤ (q i.succ).1 by omega)
    refine ⟨one_div_pos.mpr hpR, ?_, ?_⟩
    · exact one_div_lt_one_div_of_lt hpR (by exact_mod_cast hq.2 i)
    · simpa only [one_div_one] using one_div_le_one_div_of_le (by norm_num) hp1
  have sides (i : Fin 3) : dist (v (i + 1)) (v (i + 2)) ≤ 4 * Real.sqrt (r 0) := by
    by_cases hp : 0 < (q i.succ).1
    · exact (P5023T1CircularSide L q hq hs hi i hp).trans
        (P5023T1CircularEstimate (r i.succ) (r 0) hR
          (radii i hp).2.1 (radii i hp).2.2)
    · have hz : (q i.succ).1 = 0 := by have hn := curv.2.1 i; omega
      have other_pos (k : Fin 3) (hk : k ≠ i) : 0 < (q k.succ).1 := by
        have hn := curv.2.1 k
        by_contra hnp
        have hkz : (q k.succ).1 = 0 := by omega
        exact hk (curv.2.2 i k hz hkz).symm
      have hj : 0 < (q (i + 1).succ).1 :=
        other_pos (i + 1) (by fin_cases i <;> decide)
      have hk : 0 < (q (i + 2).succ).1 :=
        other_pos (i + 2) (by fin_cases i <;> decide)
      rcases P5023T1LineSideGeometry L q hq hs hi i hz with ⟨ht, hu, hv, hd⟩
      calc
        dist (v (i + 1)) (v (i + 2)) =
            |(p (i + 1).succ).im - (p (i + 2).succ).im| := hd
        _ ≤ 4 * Real.sqrt (r 0) :=
          (P5023T1LineEstimate (r 0) (r (i + 1).succ) (r (i + 2).succ)
            (p 0).im (p (i + 1).succ).im (p (i + 2).succ).im hR.le
            (radii (i + 1) hj).1.le (radii (i + 2) hk).1.le
            (radii (i + 1) hj).2.2 (radii (i + 2) hk).2.2 ht hu hv).2
  have hD : 0 ≤ 4 * Real.sqrt (r 0) := by positivity
  have pairs : ∀ i j : Fin 3, dist (v i) (v j) ≤ 4 * Real.sqrt (r 0) := by
    have h01 : dist (v 0) (v 1) ≤ 4 * Real.sqrt (r 0) := by simpa using sides 2
    have h12 : dist (v 1) (v 2) ≤ 4 * Real.sqrt (r 0) := by simpa using sides 0
    have h20 : dist (v 2) (v 0) ≤ 4 * Real.sqrt (r 0) := by simpa using sides 1
    intro i j
    fin_cases i <;> fin_cases j
    · simpa only [dist_self] using hD
    · exact h01
    · rw [dist_comm]; exact h20
    · rw [dist_comm]; exact h01
    · simpa only [dist_self] using hD
    · exact h12
    · exact h20
    · rw [dist_comm]; exact h12
    · simpa only [dist_self] using hD
  have hdiam := P5023T1ConvexDiameter v (P4984T1ClosedGap L q)
    (4 * Real.sqrt (r 0)) hD (P5023T1ContactHull L q hq hs) pairs
  calc
    Metric.diam (P4984T1ClosedGap L q) ≤ 4 * Real.sqrt (r 0) := hdiam
    _ ≤ 6 * Real.sqrt (1 / ((q 0).1 : ℝ)) := by
      dsimp [r]
      nlinarith [Real.sqrt_nonneg (1 / ((q 0).1 : ℝ))]

end ApollonianSuperharmonic

end
