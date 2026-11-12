/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P4828T1Gap
public import LeanPool.ApollonianSuperharmonic.P4828T1LineSupport
public import LeanPool.ApollonianSuperharmonic.P4828T1Rotate
public import LeanPool.ApollonianSuperharmonic.P4828T1Step
public import LeanPool.ApollonianSuperharmonic.P4909T1TriangleFan
public import LeanPool.ApollonianSuperharmonic.P4909T1LineFan
public import LeanPool.ApollonianSuperharmonic.P4909T1OmittedDiskBarrier
public import LeanPool.ApollonianSuperharmonic.P4909T1TangentSegments
public import LeanPool.ApollonianSuperharmonic.P4828T1Disk
public import LeanPool.ApollonianSuperharmonic.ProperBandCurvatureStructure
public import LeanPool.ApollonianSuperharmonic.TangencyCoordinateIdentity

-- [TABLET NODE: P4828T1ResidualPatches]

/-!
# P4828T1ResidualPatches

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace ResidualGapConstruction

private noncomputable abbrev p (q : Fin 4 → CircleCoordinates) (i : Fin 4) : ℂ := by
  classical
  exact (q i).2 / ((q i).1 : ℝ)

private noncomputable abbrev r (q : Fin 4 → CircleCoordinates) (i : Fin 4) : ℝ := by
  classical
  exact 1 / ((q i).1 : ℝ)

private noncomputable abbrev s (q : Fin 4 → CircleCoordinates) (b : Fin 3) := by
  classical
  exact P4828T1Step (P4828T1Rotate q b)

private noncomputable abbrev P (L : Real) (q : Fin 4 → CircleCoordinates) := by
  classical
  exact P4909T1ParentPolygon L q

private noncomputable abbrev F (L : Real) (q : Fin 4 → CircleCoordinates) (b : Fin 3) := by
  classical
  let s (b : Fin 3) := P4828T1Step (P4828T1Rotate q b)
  exact P4909T1ParentPolygon L (s b)

private noncomputable abbrev idx (b j : Fin 3) : Fin 4 := by
  classical
  exact ![0, (b + 1).succ, (b + 2).succ] j

private theorem parent (q : Fin 4 → CircleCoordinates) (b j : Fin 3) : (s q) b j.succ = q (idx b
    j) := by
  classical
  let s (b : Fin 3) := P4828T1Step (P4828T1Rotate q b)
  let idx (b j : Fin 3) : Fin 4 := ![0, (b + 1).succ, (b + 2).succ] j
  change (s b j.succ = q (idx b j))
  fin_cases b <;> fin_cases j <;> rfl

private theorem idx_inj (b : Fin 3) : Function.Injective (idx b) := by
  classical
  let idx (b j : Fin 3) : Fin 4 := ![0, (b + 1).succ, (b + 2).succ] j
  change (Function.Injective (idx b))
  fin_cases b <;> decide

private theorem idx_ne (b j : Fin 3) : idx b j ≠ b.succ := by
  classical
  let idx (b j : Fin 3) : Fin 4 := ![0, (b + 1).succ, (b + 2).succ] j
  change (idx b j ≠ b.succ)
  fin_cases b <;> fin_cases j <;> decide

private theorem old_retained (b j : Fin 3) (hne : j ≠ b) :
      ∃ k : Fin 3, idx b k = j.succ := by
  classical
  let idx (b j : Fin 3) : Fin 4 := ![0, (b + 1).succ, (b + 2).succ] j
  change (∃ k : Fin 3, idx b k = j.succ)
  fin_cases b <;> fin_cases j <;>
    first | exact (hne rfl).elim | exact ⟨1, rfl⟩ | exact ⟨2, rfl⟩

private theorem gap_iff (L : Real) (t : Fin 4 → CircleCoordinates) (z : ℂ) :
      z ∈ P4828T1Gap L t ↔
        z ∈ interior (P4909T1ParentPolygon L t) ∧
        ∀ j : Fin 3, 0 < (t j.succ).1 →
          1 / ((t j.succ).1 : ℝ) < dist z ((t j.succ).2 / ((t j.succ).1 : ℝ)) := by
  classical
  exact Iff.rfl

private theorem rpos (q : Fin 4 → CircleCoordinates) (i : Fin 4) (hi : 0 < (q i).1) : 0 < (r q) i
    := by
  classical
  let r (i : Fin 4) : ℝ := 1 / ((q i).1 : ℝ)
  change (0 < r i)
  dsimp [r]
  positivity

private theorem hcenter (L : Real) (q : Fin 4 → CircleCoordinates) (hq : ProperBandQuadruple q)
    (hinside : P4828T1Disk (q 0) ⊆ P4828T1Gap L q) : (p q) 0 ∈ interior (P L q) := by
  classical
  let p (i : Fin 4) : ℂ := (q i).2 / ((q i).1 : ℝ)
  let r (i : Fin 4) : ℝ := 1 / ((q i).1 : ℝ)
  let P := P4909T1ParentPolygon L q
  have gap_iff (t : Fin 4 → CircleCoordinates) (z : ℂ) :
      z ∈ P4828T1Gap L t ↔
        z ∈ interior (P4909T1ParentPolygon L t) ∧
        ∀ j : Fin 3, 0 < (t j.succ).1 →
          1 / ((t j.succ).1 : ℝ) < dist z ((t j.succ).2 / ((t j.succ).1 : ℝ)) := gap_iff L t z
  have hc := ProperBandCurvatureStructure q hq
  have rpos (i : Fin 4) (hi : 0 < (q i).1) : 0 < r i := rpos q i hi
  change (p 0 ∈ interior P)
  have hz : p 0 ∈ P4828T1Disk (q 0) := by
    change dist (p 0) (p 0) < r 0
    simpa using rpos 0 hc.1
  exact ((gap_iff q (p 0)).mp (hinside hz)).1

private theorem support (L : Real) (q : Fin 4 → CircleCoordinates) (hs : P4828T1LineSupport L
    q) (k i : Fin 4) (hk : (q k).1 = 0) (hi : 0 < (q i).1) :
      if (q k).2 = -1 then ((p q) i).re = L + (r q) i
      else ((p q) i).re = L + 2 - (r q) i := by
  classical
  let p (i : Fin 4) : ℂ := (q i).2 / ((q i).1 : ℝ)
  let r (i : Fin 4) : ℝ := 1 / ((q i).1 : ℝ)
  change (if (q k).2 = -1 then (p i).re = L + r i
      else (p i).re = L + 2 - r i)
  have hh := hs.signed k i hk hi
  have hnum : ((q i).2 : ℂ).re = (q i).2.re := by norm_num
  have hci : ((q i).1 : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hi
  have hre : (p i).re = (q i).2.re / ((q i).1 : ℝ) := by
    simp [p]
  rcases hs.normals k hk with hn | hn
  · simp only [hn]
    rw [hn] at hh
    norm_num at hh
    rw [hnum] at hh
    rw [hre]
    dsimp [r]
    field_simp [hci]
    linarith
  · have hne : (q k).2 ≠ -1 := by rw [hn]; norm_num
    simp only [ite_eq_right hne]
    rw [hn] at hh
    norm_num at hh
    rw [hnum] at hh
    rw [hre]
    dsimp [r]
    field_simp [hci]
    linarith

private theorem foot_dist (L : Real) (q : Fin 4 → CircleCoordinates) (hs : P4828T1LineSupport L
    q) (k i : Fin 4) (hk : (q k).1 = 0) (hi : 0 < (q i).1) :
      dist ((p q) i) ⟨if (q k).2 = -1 then L else L + 2, ((p q) i).im⟩ = (r q) i := by
  classical
  let p (i : Fin 4) : ℂ := (q i).2 / ((q i).1 : ℝ)
  let r (i : Fin 4) : ℝ := 1 / ((q i).1 : ℝ)
  have rpos (i : Fin 4) (hi : 0 < (q i).1) : 0 < r i := rpos q i hi
  have support (k i : Fin 4) (hk : (q k).1 = 0) (hi : 0 < (q i).1) :
      if (q k).2 = -1 then (p i).re = L + r i
      else (p i).re = L + 2 - r i := support L q hs k i hk hi
  change (dist (p i) ⟨if (q k).2 = -1 then L else L + 2, (p i).im⟩ = r i)
  have hr := (rpos i hi).le
  have hh := support k i hk hi
  rw [Complex.dist_eq]
  by_cases hn : (q k).2 = -1
  · simp only [ite_eq_left hn] at hh ⊢
    have hv : p i - (⟨L, (p i).im⟩ : ℂ) = (r i : ℂ) := by
      apply Complex.ext <;> simp [hh]
    rw [hv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]
  · simp only [ite_eq_right hn] at hh ⊢
    have hv : p i - (⟨L + 2, (p i).im⟩ : ℂ) = (-r i : ℂ) := by
      apply Complex.ext <;> simp [hh]
    rw [hv, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]

private theorem foot_cover (L : Real) (q : Fin 4 → CircleCoordinates) (hs : P4828T1LineSupport
    L q) (k i : Fin 4) (hk : (q k).1 = 0) (hi : 0 < (q i).1) :
      segment ℝ ((p q) i)
        ⟨if (q k).2 = -1 then L else L + 2, ((p q) i).im⟩ ⊆
        Metric.closedBall ((p q) i) ((r q) i) := by
  classical
  let p (i : Fin 4) : ℂ := (q i).2 / ((q i).1 : ℝ)
  let r (i : Fin 4) : ℝ := 1 / ((q i).1 : ℝ)
  have rpos (i : Fin 4) (hi : 0 < (q i).1) : 0 < r i := rpos q i hi
  have support (k i : Fin 4) (hk : (q k).1 = 0) (hi : 0 < (q i).1) :
      if (q k).2 = -1 then (p i).re = L + r i
      else (p i).re = L + 2 - r i := support L q hs k i hk hi
  have foot_dist (k i : Fin 4) (hk : (q k).1 = 0) (hi : 0 < (q i).1) :
      dist (p i) ⟨if (q k).2 = -1 then L else L + 2, (p i).im⟩ = r i := foot_dist L q hs k i hk hi
  change (segment ℝ (p i)
        ⟨if (q k).2 = -1 then L else L + 2, (p i).im⟩ ⊆
        Metric.closedBall (p i) (r i))
  intro z hz
  have hd := foot_dist k i hk hi
  rcases (P4909T1TangentSegments _ _ (r i) 0
    (by simpa only [add_zero] using hd)).1 hz with h | h
  · exact h
  · have heq : z = ⟨if (q k).2 = -1 then L else L + 2, (p i).im⟩ := by
      simpa only [Metric.mem_closedBall, dist_le_zero] using h
    rw [Metric.mem_closedBall, heq, dist_comm, hd]

private theorem line_dist (L : Real) (q : Fin 4 → CircleCoordinates) (hs : P4828T1LineSupport L
    q) (k i : Fin 4) (hk : (q k).1 = 0) (hi : 0 < (q i).1)
      (z : ℂ) (hz : z.re = if (q k).2 = -1 then L else L + 2) :
      (r q) i ≤ dist z ((p q) i) := by
  classical
  let p (i : Fin 4) : ℂ := (q i).2 / ((q i).1 : ℝ)
  let r (i : Fin 4) : ℝ := 1 / ((q i).1 : ℝ)
  have rpos (i : Fin 4) (hi : 0 < (q i).1) : 0 < r i := rpos q i hi
  have support (k i : Fin 4) (hk : (q k).1 = 0) (hi : 0 < (q i).1) :
      if (q k).2 = -1 then (p i).re = L + r i
      else (p i).re = L + 2 - r i := support L q hs k i hk hi
  change (r i ≤ dist z (p i))
  have hh := support k i hk hi
  have hab := Complex.abs_re_le_norm (z - p i)
  rw [Complex.sub_re, hz] at hab
  rw [Complex.dist_eq]
  by_cases hn : (q k).2 = -1
  · simp only [ite_eq_left hn] at hh hab
    have heq : L - (p i).re = -r i := by linarith
    rw [heq, abs_neg, abs_of_pos (rpos i hi)] at hab
    exact hab
  · simp only [ite_eq_right hn] at hh hab
    have heq : L + 2 - (p i).re = r i := by linarith
    rw [heq, abs_of_pos (rpos i hi)] at hab
    exact hab

private theorem center_dist (q : Fin 4 → CircleCoordinates) (hq : ProperBandQuadruple q) (i j :
    Fin 4) (hij : i ≠ j)
      (hi : 0 < (q i).1) (hj : 0 < (q j).1) :
      dist ((p q) i) ((p q) j) = (r q) i + (r q) j := by
  classical
  let p (i : Fin 4) : ℂ := (q i).2 / ((q i).1 : ℝ)
  let r (i : Fin 4) : ℝ := 1 / ((q i).1 : ℝ)
  change (dist (p i) (p j) = r i + r j)
  let v : GaussianInt := (q j).1 • (q i).2 - (q i).1 • (q j).2
  have ht := TangencyCoordinateIdentity q hq.1 i j hij
  have hn : Complex.normSq (v : ℂ) = (((q i).1 + (q j).1 : ℤ)^2 : ℝ) := by
    have normCast (w : GaussianInt) :
        Complex.normSq (w : ℂ) = (Zsqrtd.norm w : ℝ) := by
      simp [Complex.normSq, Zsqrtd.norm_def]
    rw [normCast]
    exact_mod_cast ht
  have hnsq : ‖(v : ℂ)‖ ^ 2 = (((q i).1 + (q j).1 : ℤ) : ℝ) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, hn]
  have hnorm : ‖(v : ℂ)‖ = (((q i).1 + (q j).1 : ℤ) : ℝ) := by
    have hnonneg := norm_nonneg (v : ℂ)
    have hsum : 0 ≤ (((q i).1 + (q j).1 : ℤ) : ℝ) := by positivity
    nlinarith
  have hdiff : p i - p j =
      (v : ℂ) / (((q i).1 * (q j).1 : ℤ) : ℂ) := by
    dsimp [p, v]
    push_cast
    simp only [map_sub, map_zsmul]
    field_simp [ne_of_gt hi, ne_of_gt hj]
    ring
  rw [Complex.dist_eq, hdiff, Complex.norm_div, Complex.norm_intCast, hnorm]
  have ha : 0 < ((q i).1 : ℝ) := by exact_mod_cast hi
  have hb : 0 < ((q j).1 : ℝ) := by exact_mod_cast hj
  have hab : 0 < (((q i).1 * (q j).1 : ℤ) : ℝ) := by
    exact_mod_cast mul_pos hi hj
  rw [abs_of_pos hab]
  dsimp [r]
  push_cast
  field_simp [ne_of_gt ha, ne_of_gt hb]
  ring

private theorem geometry (L : Real) (q : Fin 4 → CircleCoordinates) (hq : ProperBandQuadruple q)
    (hs : P4828T1LineSupport L q) (hinside : P4828T1Disk (q 0) ⊆ P4828T1Gap L q) :
      (∀ b, (F L q) b ⊆ (P L q) ∧ (0 < (q b.succ).1 → (p q) b.succ ∉ (F L q) b) ∧
        frontier ((F L q) b) ⊆ P4909T1ParentEdges L ((s q) b)) ∧
      (∀ b c, b ≠ c → Disjoint (interior ((F L q) b)) (interior ((F L q) c))) ∧
      (P L q) = ⋃ b, (F L q) b ∧
      (∀ z ∈ interior (P L q),
        (∀ i : Fin 4, 0 < (q i).1 → z ∉ segment ℝ ((p q) 0) ((p q) i)) →
        (∀ k : Fin 3, (q k.succ).1 = 0 →
          z ∉ segment ℝ ((p q) 0)
            ⟨if (q k.succ).2 = -1 then L else L + 2, ((p q) 0).im⟩) →
        ∃ b, z ∈ interior ((F L q) b)) := by
  classical
  let p (i : Fin 4) : ℂ := (q i).2 / ((q i).1 : ℝ)
  let r (i : Fin 4) : ℝ := 1 / ((q i).1 : ℝ)
  let s (b : Fin 3) := P4828T1Step (P4828T1Rotate q b)
  let P := P4909T1ParentPolygon L q
  let F (b : Fin 3) := P4909T1ParentPolygon L (s b)
  have gap_iff (t : Fin 4 → CircleCoordinates) (z : ℂ) :
      z ∈ P4828T1Gap L t ↔
        z ∈ interior (P4909T1ParentPolygon L t) ∧
        ∀ j : Fin 3, 0 < (t j.succ).1 →
          1 / ((t j.succ).1 : ℝ) < dist z ((t j.succ).2 / ((t j.succ).1 : ℝ)) := gap_iff L t z
  have hc := ProperBandCurvatureStructure q hq
  have rpos (i : Fin 4) (hi : 0 < (q i).1) : 0 < r i := rpos q i hi
  have hcenter : p 0 ∈ interior P := hcenter L q hq hinside
  have support (k i : Fin 4) (hk : (q k).1 = 0) (hi : 0 < (q i).1) :
      if (q k).2 = -1 then (p i).re = L + r i
      else (p i).re = L + 2 - r i := support L q hs k i hk hi
  change ((∀ b, F b ⊆ P ∧ (0 < (q b.succ).1 → p b.succ ∉ F b) ∧
        frontier (F b) ⊆ P4909T1ParentEdges L (s b)) ∧
      (∀ b c, b ≠ c → Disjoint (interior (F b)) (interior (F c))) ∧
      P = ⋃ b, F b ∧
      (∀ z ∈ interior P,
        (∀ i : Fin 4, 0 < (q i).1 → z ∉ segment ℝ (p 0) (p i)) →
        (∀ k : Fin 3, (q k.succ).1 = 0 →
          z ∉ segment ℝ (p 0)
            ⟨if (q k.succ).2 = -1 then L else L + 2, (p 0).im⟩) →
        ∃ b, z ∈ interior (F b)))
  by_cases hp : ∀ j : Fin 3, 0 < (q j.succ).1
  · have hall : ∀ i : Fin 4, 0 < (q i).1 := Fin.cases hc.1 hp
    have g := P4909T1TriangleFan L q hall hcenter
    exact ⟨fun b => ⟨(g.1 b).1, fun _ => (g.1 b).2.1, (g.1 b).2.2⟩, g.2⟩
  · obtain ⟨l, hl⟩ := not_forall.mp hp
    have hl0 : (q l.succ).1 = 0 := by have := hc.2.1 l; omega
    have hother (i : Fin 3) (hne : i ≠ l) : 0 < (q i.succ).1 := by
      have hn := hc.2.1 i
      have hnonzero : (q i.succ).1 ≠ 0 := fun h => hne (hc.2.2 i l h hl0)
      omega
    apply P4909T1LineFan L q l hl0 hother hc.1 (hs.normals l.succ hl0)
    · intro i hi
      have hh := support l.succ i hl0 hi
      have hr := rpos i hi
      split_ifs at hh ⊢ <;> linarith
    · exact hcenter

private theorem omitted (L : Real) (q : Fin 4 → CircleCoordinates) (hq : ProperBandQuadruple q)
    (hs : P4828T1LineSupport L q) (hinside : P4828T1Disk (q 0) ⊆ P4828T1Gap L q) (b : Fin
    3) (hb : 0 < (q b.succ).1) :
      ∀ z ∈ interior ((F L q) b), (r q) b.succ < dist z ((p q) b.succ) := by
  classical
  let p (i : Fin 4) : ℂ := (q i).2 / ((q i).1 : ℝ)
  let r (i : Fin 4) : ℝ := 1 / ((q i).1 : ℝ)
  let s (b : Fin 3) := P4828T1Step (P4828T1Rotate q b)
  let P := P4909T1ParentPolygon L q
  let F (b : Fin 3) := P4909T1ParentPolygon L (s b)
  let idx (b j : Fin 3) : Fin 4 := ![0, (b + 1).succ, (b + 2).succ] j
  have parent (b j : Fin 3) : s b j.succ = q (idx b j) := parent q b j
  have idx_inj (b : Fin 3) : Function.Injective (idx b) := idx_inj b
  have idx_ne (b j : Fin 3) : idx b j ≠ b.succ := idx_ne b j
  have gap_iff (t : Fin 4 → CircleCoordinates) (z : ℂ) :
      z ∈ P4828T1Gap L t ↔
        z ∈ interior (P4909T1ParentPolygon L t) ∧
        ∀ j : Fin 3, 0 < (t j.succ).1 →
          1 / ((t j.succ).1 : ℝ) < dist z ((t j.succ).2 / ((t j.succ).1 : ℝ)) := gap_iff L t z
  have hc := ProperBandCurvatureStructure q hq
  have rpos (i : Fin 4) (hi : 0 < (q i).1) : 0 < r i := rpos q i hi
  have hcenter : p 0 ∈ interior P := hcenter L q hq hinside
  have support (k i : Fin 4) (hk : (q k).1 = 0) (hi : 0 < (q i).1) :
      if (q k).2 = -1 then (p i).re = L + r i
      else (p i).re = L + 2 - r i := support L q hs k i hk hi
  have foot_dist (k i : Fin 4) (hk : (q k).1 = 0) (hi : 0 < (q i).1) :
      dist (p i) ⟨if (q k).2 = -1 then L else L + 2, (p i).im⟩ = r i := foot_dist L q hs k i hk hi
  have foot_cover (k i : Fin 4) (hk : (q k).1 = 0) (hi : 0 < (q i).1) :
      segment ℝ (p i)
        ⟨if (q k).2 = -1 then L else L + 2, (p i).im⟩ ⊆
        Metric.closedBall (p i) (r i) := foot_cover L q hs k i hk hi
  have line_dist (k i : Fin 4) (hk : (q k).1 = 0) (hi : 0 < (q i).1)
      (z : ℂ) (hz : z.re = if (q k).2 = -1 then L else L + 2) :
      r i ≤ dist z (p i) := line_dist L q hs k i hk hi z hz
  have center_dist (i j : Fin 4) (hij : i ≠ j)
      (hi : 0 < (q i).1) (hj : 0 < (q j).1) :
      dist (p i) (p j) = r i + r j := center_dist q hq i j hij hi hj
  have geometry :
      (∀ b, F b ⊆ P ∧ (0 < (q b.succ).1 → p b.succ ∉ F b) ∧
        frontier (F b) ⊆ P4909T1ParentEdges L (s b)) ∧
      (∀ b c, b ≠ c → Disjoint (interior (F b)) (interior (F c))) ∧
      P = ⋃ b, F b ∧
      (∀ z ∈ interior P,
        (∀ i : Fin 4, 0 < (q i).1 → z ∉ segment ℝ (p 0) (p i)) →
        (∀ k : Fin 3, (q k.succ).1 = 0 →
          z ∉ segment ℝ (p 0)
            ⟨if (q k.succ).2 = -1 then L else L + 2, (p 0).im⟩) →
        ∃ b, z ∈ interior (F b)) := geometry L q hq hs hinside
  change (∀ z ∈ interior (F b), r b.succ < dist z (p b.succ))
  apply P4909T1OmittedDiskBarrier (F b) (p b.succ) (r b.succ)
    (rpos _ hb) ((geometry.1 b).2.1 hb)
  rw [Set.disjoint_left]
  intro z hz hball
  have hedge := (geometry.1 b).2.2 hz
  change (∃ i j : Fin 3, i ≠ j ∧ 0 < (s b i.succ).1 ∧
      0 < (s b j.succ).1 ∧ z ∈ segment ℝ
        (((s b i.succ).2 : ℂ) / ((s b i.succ).1 : ℝ))
        (((s b j.succ).2 : ℂ) / ((s b j.succ).1 : ℝ))) ∨
    (∃ i k : Fin 3, 0 < (s b i.succ).1 ∧ (s b k.succ).1 = 0 ∧
      z ∈ segment ℝ (((s b i.succ).2 : ℂ) / ((s b i.succ).1 : ℝ))
        ⟨if (s b k.succ).2 = -1 then L else L + 2,
          (((s b i.succ).2 : ℂ) / ((s b i.succ).1 : ℝ)).im⟩) ∨
    (∃ k : Fin 3, (s b k.succ).1 = 0 ∧
      z.re = if (s b k.succ).2 = -1 then L else L + 2) at hedge
  simp only [parent] at hedge
  have avoid (i : Fin 3) (hi : 0 < (q (idx b i)).1) :
      z ∉ Metric.closedBall (p (idx b i)) (r (idx b i)) := by
    have hd := center_dist b.succ (idx b i) (idx_ne b i).symm hb hi
    exact Set.disjoint_left.mp
      (P4909T1TangentSegments _ _ _ _ hd).2 hball
  rcases hedge with ⟨i, j, hij, hi, hj, hz⟩ | ⟨i, k, hi, hk, hz⟩ | ⟨k, hk, hz⟩
  · have hd := center_dist (idx b i) (idx b j) ((idx_inj b).ne hij) hi hj
    rcases (P4909T1TangentSegments _ _ _ _ hd).1 hz with h | h
    · exact avoid i hi h
    · exact avoid j hj h
  · have hd := foot_dist (idx b k) (idx b i) hk hi
    have hclosed := foot_cover (idx b k) (idx b i) hk hi hz
    exact avoid i hi hclosed
  · have hd := line_dist (idx b k) b.succ hk hb z hz
    have hzlt := Metric.mem_ball.mp hball
    exact (not_lt_of_ge hd) hzlt

private theorem inserted_exterior (L : Real) (q : Fin 4 → CircleCoordinates) (hq :
    ProperBandQuadruple q) (b : Fin 3) (z : ℂ)
      (hz : z ∈ P4828T1Gap L ((s q) b)) : (r q) 0 < dist z ((p q) 0) := by
  classical
  let p (i : Fin 4) : ℂ := (q i).2 / ((q i).1 : ℝ)
  let r (i : Fin 4) : ℝ := 1 / ((q i).1 : ℝ)
  let s (b : Fin 3) := P4828T1Step (P4828T1Rotate q b)
  let idx (b j : Fin 3) : Fin 4 := ![0, (b + 1).succ, (b + 2).succ] j
  have parent (b j : Fin 3) : s b j.succ = q (idx b j) := parent q b j
  have gap_iff (t : Fin 4 → CircleCoordinates) (z : ℂ) :
      z ∈ P4828T1Gap L t ↔
        z ∈ interior (P4909T1ParentPolygon L t) ∧
        ∀ j : Fin 3, 0 < (t j.succ).1 →
          1 / ((t j.succ).1 : ℝ) < dist z ((t j.succ).2 / ((t j.succ).1 : ℝ)) := gap_iff L t z
  have hc := ProperBandCurvatureStructure q hq
  change (r 0 < dist z (p 0))
  have hp : s b (Fin.succ 0) = q 0 := parent b 0
  have he := ((gap_iff (s b) z).mp hz).2 0 (by rw [hp]; exact hc.1)
  simpa only [hp] using he

private theorem gap_subset (L : Real) (q : Fin 4 → CircleCoordinates) (hq : ProperBandQuadruple
    q) (hs : P4828T1LineSupport L q) (hinside : P4828T1Disk (q 0) ⊆ P4828T1Gap L q) (b :
    Fin 3) : P4828T1Gap L ((s q) b) ⊆ P4828T1Gap L q := by
  classical
  let p (i : Fin 4) : ℂ := (q i).2 / ((q i).1 : ℝ)
  let r (i : Fin 4) : ℝ := 1 / ((q i).1 : ℝ)
  let s (b : Fin 3) := P4828T1Step (P4828T1Rotate q b)
  let P := P4909T1ParentPolygon L q
  let F (b : Fin 3) := P4909T1ParentPolygon L (s b)
  let idx (b j : Fin 3) : Fin 4 := ![0, (b + 1).succ, (b + 2).succ] j
  have parent (b j : Fin 3) : s b j.succ = q (idx b j) := parent q b j
  have idx_inj (b : Fin 3) : Function.Injective (idx b) := idx_inj b
  have idx_ne (b j : Fin 3) : idx b j ≠ b.succ := idx_ne b j
  have old_retained (b j : Fin 3) (hne : j ≠ b) :
      ∃ k : Fin 3, idx b k = j.succ := old_retained b j hne
  have gap_iff (t : Fin 4 → CircleCoordinates) (z : ℂ) :
      z ∈ P4828T1Gap L t ↔
        z ∈ interior (P4909T1ParentPolygon L t) ∧
        ∀ j : Fin 3, 0 < (t j.succ).1 →
          1 / ((t j.succ).1 : ℝ) < dist z ((t j.succ).2 / ((t j.succ).1 : ℝ)) := gap_iff L t z
  have hc := ProperBandCurvatureStructure q hq
  have rpos (i : Fin 4) (hi : 0 < (q i).1) : 0 < r i := rpos q i hi
  have hcenter : p 0 ∈ interior P := hcenter L q hq hinside
  have support (k i : Fin 4) (hk : (q k).1 = 0) (hi : 0 < (q i).1) :
      if (q k).2 = -1 then (p i).re = L + r i
      else (p i).re = L + 2 - r i := support L q hs k i hk hi
  have foot_dist (k i : Fin 4) (hk : (q k).1 = 0) (hi : 0 < (q i).1) :
      dist (p i) ⟨if (q k).2 = -1 then L else L + 2, (p i).im⟩ = r i := foot_dist L q hs k i hk hi
  have foot_cover (k i : Fin 4) (hk : (q k).1 = 0) (hi : 0 < (q i).1) :
      segment ℝ (p i)
        ⟨if (q k).2 = -1 then L else L + 2, (p i).im⟩ ⊆
        Metric.closedBall (p i) (r i) := foot_cover L q hs k i hk hi
  have line_dist (k i : Fin 4) (hk : (q k).1 = 0) (hi : 0 < (q i).1)
      (z : ℂ) (hz : z.re = if (q k).2 = -1 then L else L + 2) :
      r i ≤ dist z (p i) := line_dist L q hs k i hk hi z hz
  have center_dist (i j : Fin 4) (hij : i ≠ j)
      (hi : 0 < (q i).1) (hj : 0 < (q j).1) :
      dist (p i) (p j) = r i + r j := center_dist q hq i j hij hi hj
  have geometry :
      (∀ b, F b ⊆ P ∧ (0 < (q b.succ).1 → p b.succ ∉ F b) ∧
        frontier (F b) ⊆ P4909T1ParentEdges L (s b)) ∧
      (∀ b c, b ≠ c → Disjoint (interior (F b)) (interior (F c))) ∧
      P = ⋃ b, F b ∧
      (∀ z ∈ interior P,
        (∀ i : Fin 4, 0 < (q i).1 → z ∉ segment ℝ (p 0) (p i)) →
        (∀ k : Fin 3, (q k.succ).1 = 0 →
          z ∉ segment ℝ (p 0)
            ⟨if (q k.succ).2 = -1 then L else L + 2, (p 0).im⟩) →
        ∃ b, z ∈ interior (F b)) := geometry L q hq hs hinside
  have omitted (b : Fin 3) (hb : 0 < (q b.succ).1) :
      ∀ z ∈ interior (F b), r b.succ < dist z (p b.succ) := omitted L q hq hs hinside b hb
  change (P4828T1Gap L (s b) ⊆ P4828T1Gap L q)
  intro z hz
  have hg := (gap_iff (s b) z).mp hz
  apply (gap_iff q z).mpr
  refine ⟨interior_mono (geometry.1 b).1 hg.1, ?_⟩
  intro j hj
  by_cases hjeq : j = b
  · subst j
    exact omitted b hj z hg.1
  · obtain ⟨k, hk⟩ := old_retained b j hjeq
    have hp : s b k.succ = q j.succ := by rw [parent, hk]
    have he := hg.2 k (by simpa only [hp] using hj)
    simpa only [hp] using he

end ResidualGapConstruction

theorem P4828T1ResidualPatches (L : Real)
    (q : Fin 4 → CircleCoordinates) (hq : ProperBandQuadruple q)
    (hs : P4828T1LineSupport L q)
    (hinside : P4828T1Disk (q 0) ⊆ P4828T1Gap L q) :
    let residual (b : Fin 3) :=
      P4828T1Gap L (P4828T1Step (P4828T1Rotate q b))
    (∀ b, residual b ⊆ P4828T1Gap L q ∧
      Disjoint (residual b) (P4828T1Disk (q 0))) ∧
    (∀ b c, b ≠ c → Disjoint (residual b) (residual c)) ∧
    P4828T1Gap L q \ Metric.closedBall
      ((q 0).2 / ((q 0).1 : Real)) (1 / ((q 0).1 : Real)) =
      ⋃ b : Fin 3, residual b := by
-- BODY
  classical
  let p (i : Fin 4) : ℂ := (q i).2 / ((q i).1 : ℝ)
  let r (i : Fin 4) : ℝ := 1 / ((q i).1 : ℝ)
  let s (b : Fin 3) := P4828T1Step (P4828T1Rotate q b)
  let P := P4909T1ParentPolygon L q
  let F (b : Fin 3) := P4909T1ParentPolygon L (s b)
  let idx (b j : Fin 3) : Fin 4 := ![0, (b + 1).succ, (b + 2).succ] j
  have parent (b j : Fin 3) : s b j.succ = q (idx b j) := ResidualGapConstruction.parent q b j
  have idx_inj (b : Fin 3) : Function.Injective (idx b) := ResidualGapConstruction.idx_inj b
  have idx_ne (b j : Fin 3) : idx b j ≠ b.succ := ResidualGapConstruction.idx_ne b j
  have old_retained (b j : Fin 3) (hne : j ≠ b) :
      ∃ k : Fin 3, idx b k = j.succ := ResidualGapConstruction.old_retained b j hne
  have gap_iff (t : Fin 4 → CircleCoordinates) (z : ℂ) :
      z ∈ P4828T1Gap L t ↔
        z ∈ interior (P4909T1ParentPolygon L t) ∧
        ∀ j : Fin 3, 0 < (t j.succ).1 →
          1 / ((t j.succ).1 : ℝ) < dist z ((t j.succ).2 / ((t j.succ).1 : ℝ)) :=
              ResidualGapConstruction.gap_iff L t z
  have hc := ProperBandCurvatureStructure q hq
  have rpos (i : Fin 4) (hi : 0 < (q i).1) : 0 < r i := ResidualGapConstruction.rpos q i hi
  have hcenter : p 0 ∈ interior P := ResidualGapConstruction.hcenter L q hq hinside
  -- Divide the signed supporting-line equation, preserving its actual offset.
  have support (k i : Fin 4) (hk : (q k).1 = 0) (hi : 0 < (q i).1) :
      if (q k).2 = -1 then (p i).re = L + r i
      else (p i).re = L + 2 - r i := ResidualGapConstruction.support L q hs k i hk hi
  have foot_dist (k i : Fin 4) (hk : (q k).1 = 0) (hi : 0 < (q i).1) :
      dist (p i) ⟨if (q k).2 = -1 then L else L + 2, (p i).im⟩ = r i :=
          ResidualGapConstruction.foot_dist L q hs k i hk hi
  have foot_cover (k i : Fin 4) (hk : (q k).1 = 0) (hi : 0 < (q i).1) :
      segment ℝ (p i)
        ⟨if (q k).2 = -1 then L else L + 2, (p i).im⟩ ⊆
        Metric.closedBall (p i) (r i) := ResidualGapConstruction.foot_cover L q hs k i hk hi
  have line_dist (k i : Fin 4) (hk : (q k).1 = 0) (hi : 0 < (q i).1)
      (z : ℂ) (hz : z.re = if (q k).2 = -1 then L else L + 2) :
      r i ≤ dist z (p i) := ResidualGapConstruction.line_dist L q hs k i hk hi z hz
  -- External tangency is obtained directly from the registered norm identity.
  have center_dist (i j : Fin 4) (hij : i ≠ j)
      (hi : 0 < (q i).1) (hj : 0 < (q j).1) :
      dist (p i) (p j) = r i + r j := ResidualGapConstruction.center_dist q hq i j hij hi hj
  have geometry :
      (∀ b, F b ⊆ P ∧ (0 < (q b.succ).1 → p b.succ ∉ F b) ∧
        frontier (F b) ⊆ P4909T1ParentEdges L (s b)) ∧
      (∀ b c, b ≠ c → Disjoint (interior (F b)) (interior (F c))) ∧
      P = ⋃ b, F b ∧
      (∀ z ∈ interior P,
        (∀ i : Fin 4, 0 < (q i).1 → z ∉ segment ℝ (p 0) (p i)) →
        (∀ k : Fin 3, (q k.succ).1 = 0 →
          z ∉ segment ℝ (p 0)
            ⟨if (q k.succ).2 = -1 then L else L + 2, (p 0).im⟩) →
        ∃ b, z ∈ interior (F b)) := ResidualGapConstruction.geometry L q hq hs hinside
  -- No point of an omitted open disk can cross the concrete boundary carrier.
  have omitted (b : Fin 3) (hb : 0 < (q b.succ).1) :
      ∀ z ∈ interior (F b), r b.succ < dist z (p b.succ) := ResidualGapConstruction.omitted L q
          hq hs hinside b hb
  have inserted_exterior (b : Fin 3) (z : ℂ)
      (hz : z ∈ P4828T1Gap L (s b)) : r 0 < dist z (p 0) :=
          ResidualGapConstruction.inserted_exterior L q hq b z hz
  have gap_subset (b : Fin 3) : P4828T1Gap L (s b) ⊆ P4828T1Gap L q :=
      ResidualGapConstruction.gap_subset L q hq hs hinside b
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · intro b
    refine ⟨gap_subset b, ?_⟩
    rw [Set.disjoint_left]
    intro z hz hd
    have he := inserted_exterior b z hz
    have hlt : dist z (p 0) < r 0 := Metric.mem_ball.mp hd
    exact (not_lt_of_ge he.le) hlt
  · intro b c hbc
    rw [Set.disjoint_left]
    intro z hb hz
    exact Set.disjoint_left.mp (geometry.2.1 b c hbc)
      ((gap_iff (s b) z).mp hb).1 ((gap_iff (s c) z).mp hz).1
  · apply Set.Subset.antisymm
    · intro z hz
      have hg := (gap_iff q z).mp hz.1
      have hex : r 0 < dist z (p 0) := by
        exact lt_of_not_ge (fun h => hz.2 (Metric.mem_closedBall.mpr h))
      have radial (i : Fin 4) (hi : 0 < (q i).1) : z ∉ segment ℝ (p 0) (p i) := by
        intro hseg
        by_cases hi0 : i = 0
        · subst i
          have heq : z = p 0 := by simpa using hseg
          rw [heq, dist_self] at hex
          exact (not_lt_of_ge (rpos 0 hc.1).le) hex
        · have hd := center_dist 0 i (Ne.symm hi0) hc.1 hi
          have hseg' := (P4909T1TangentSegments _ _ _ _ hd).1 hseg
          rcases hseg' with h | h
          · exact (not_le_of_gt hex) (Metric.mem_closedBall.mp h)
          · obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.mpr hi0
            exact (not_le_of_gt (hg.2 j hi)) (Metric.mem_closedBall.mp h)
      have foot (k : Fin 3) (hk : (q k.succ).1 = 0) :
          z ∉ segment ℝ (p 0)
            ⟨if (q k.succ).2 = -1 then L else L + 2, (p 0).im⟩ := by
        intro hseg
        have hd := foot_dist k.succ 0 hk hc.1
        have hclosed := foot_cover k.succ 0 hk hc.1 hseg
        exact (not_le_of_gt hex) (Metric.mem_closedBall.mp hclosed)
      obtain ⟨b, hb⟩ := geometry.2.2.2 z hg.1 radial foot
      apply Set.mem_iUnion.mpr
      refine ⟨b, (gap_iff (s b) z).mpr ⟨hb, ?_⟩⟩
      intro j hj
      rw [parent] at hj ⊢
      by_cases hi0 : idx b j = 0
      · simpa only [hi0] using hex
      · obtain ⟨k, hk⟩ := Fin.exists_succ_eq.mpr hi0
        simpa only [hk] using hg.2 k (by simpa only [hk] using hj)
    · intro z hz
      obtain ⟨b, hb⟩ := Set.mem_iUnion.mp hz
      refine ⟨gap_subset b hb, ?_⟩
      intro hcball
      exact (not_le_of_gt (inserted_exterior b z hb)) (Metric.mem_closedBall.mp hcball)

end ApollonianSuperharmonic

end
