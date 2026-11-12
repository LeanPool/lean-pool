/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P4984T1ClosedGap
public import LeanPool.ApollonianSuperharmonic.P4828T1Gap
public import LeanPool.ApollonianSuperharmonic.P4828T1LineSupport
public import LeanPool.ApollonianSuperharmonic.ProperBandCurvatureStructure
public import LeanPool.ApollonianSuperharmonic.TangencyCoordinateIdentity
public import LeanPool.ApollonianSuperharmonic.P4909T1TriangleFan
public import LeanPool.ApollonianSuperharmonic.P4909T1LineFan
public import LeanPool.ApollonianSuperharmonic.P4909T1OmittedDiskBarrier
public import LeanPool.ApollonianSuperharmonic.P4909T1TangentSegments
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Module.RCLike.Real
public import Mathlib.Analysis.RCLike.Basic

-- [TABLET NODE: P4984T1ClosedSubdivision]

/-!
# P4984T1ClosedSubdivision

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace ClosedSubdivisionProof

private theorem fan :
    ∀ (L : Real), ∀ (q : Fin 4 → CircleCoordinates), (P4828T1LineSupport L q) → (
    let p (i : Fin 4) : ℂ := (q i).2 / ((q i).1 : ℝ)
    let s (b : Fin 3) := P4828T1Step (P4828T1Rotate q b)
    let P := P4909T1ParentPolygon L q
    let F (b : Fin 3) := P4909T1ParentPolygon L (s b)
    (0 < (q 0).1) → ((∀ i : Fin 3, 0 ≤ (q i.succ).1) → ((p 0 ∈ interior P) → ((∀ (i : Fin (3 :
        ℕ)), ∀ (j : Fin (3 : ℕ)), (q i.succ).1 = (0 : ℤ) → (q j.succ).1 = (0 : ℤ) → i = j) → ((∀
        b : Fin 3, F b ⊆ P ∧
        (0 < (q b.succ).1 → p b.succ ∉ F b) ∧
        frontier (F b) ⊆ P4909T1ParentEdges L (s b)) ∧
      (∀ b c : Fin 3, b ≠ c → Disjoint (interior (F b)) (interior (F c))) ∧
      P = ⋃ b : Fin 3, F b))))) := by
  classical
  intro L q hs p s P F hchildpos hparentsNonneg hinside hzunique
  by_cases hline : ∃ l : Fin 3, (q l.succ).1 = 0
  · obtain ⟨l, hl⟩ := hline
    have hpos : ∀ i : Fin 3, i ≠ l → 0 < (q i.succ).1 := by
      intro i hil
      have hnonneg := hparentsNonneg i
      by_contra hn
      have hi0 : (q i.succ).1 = 0 := by omega
      have heq := hzunique i l hi0 hl
      exact hil heq
    have hnormal := hs.normals l.succ hl
    have hside : ∀ i : Fin 4, 0 < (q i).1 →
        if (q l.succ).2 = -1 then L < (p i).re
        else (p i).re < L + 2 := by
      intro i hi
      have hi0 : (q i).1 ≠ 0 := ne_of_gt hi
      have hre : (p i).re = (q i).2.re / (q i).1 := by
        dsimp [p]
        rw [Complex.div_re]
        simp []
        field_simp [hi0]
      have hh := hs.signed l.succ i hl hi
      have hcurvReal : (0 : ℝ) < (q i).1 := by exact_mod_cast hi
      have hrealI : ((q i).2 : ℂ).re = (q i).2.re := by norm_num
      rcases hnormal with hneg | hposLine
      · rw [hneg] at hh
        norm_num at hh
        rw [hrealI] at hh
        rw [hre]
        rw [hneg]
        apply (lt_div_iff₀ hcurvReal).2
        nlinarith [hh]
      · rw [hposLine] at hh
        norm_num at hh
        rw [hrealI] at hh
        rw [hre]
        have hcond : (q l.succ).2 ≠ -1 := by rw [hposLine]; norm_num
        rw [ite_eq_right hcond]
        apply (div_lt_iff₀ hcurvReal).2
        nlinarith [hh]
    have hfan := P4909T1LineFan L q l hl hpos hchildpos hnormal hside hinside
    simpa only [p, s, P, F] using
      (show (∀ b : Fin 3, P4909T1ParentPolygon L (s b) ⊆
        P4909T1ParentPolygon L q ∧
        (0 < (q b.succ).1 → p b.succ ∉ P4909T1ParentPolygon L (s b)) ∧
        frontier (P4909T1ParentPolygon L (s b)) ⊆
          P4909T1ParentEdges L (s b)) ∧
        (∀ b c : Fin 3, b ≠ c → Disjoint
          (interior (P4909T1ParentPolygon L (s b)))
          (interior (P4909T1ParentPolygon L (s c)))) ∧
        P4909T1ParentPolygon L q = ⋃ b : Fin 3,
          P4909T1ParentPolygon L (s b) from ⟨
        (fun b => ⟨(hfan.1 b).1, fun hb => (hfan.1 b).2.1 hb, (hfan.1 b).2.2⟩),
        hfan.2.1, hfan.2.2.1⟩)
  · have hpos : ∀ i : Fin 4, 0 < (q i).1 := by
      intro i
      fin_cases i
      · exact hchildpos
      · have hnonneg : 0 ≤ (q (Fin.succ 0)).1 := hparentsNonneg 0
        by_contra hnot
        have hz : (q (Fin.succ 0)).1 = 0 :=
          le_antisymm (le_of_not_gt hnot) hnonneg
        exact hline ⟨0, hz⟩
      · have hnonneg : 0 ≤ (q (Fin.succ 1)).1 := hparentsNonneg 1
        by_contra hnot
        have hz : (q (Fin.succ 1)).1 = 0 :=
          le_antisymm (le_of_not_gt hnot) hnonneg
        exact hline ⟨1, hz⟩
      · have hnonneg : 0 ≤ (q (Fin.succ 2)).1 := hparentsNonneg 2
        by_contra hnot
        have hz : (q (Fin.succ 2)).1 = 0 :=
          le_antisymm (le_of_not_gt hnot) hnonneg
        exact hline ⟨2, hz⟩
    have hfan := P4909T1TriangleFan L q hpos hinside
    exact ⟨(fun b => ⟨(hfan.1 b).1, fun _ => (hfan.1 b).2.1,
      (hfan.1 b).2.2⟩), hfan.2.1, hfan.2.2.1⟩

private theorem polygonClosed :
    ∀ (L : Real),
    ∀ (t : Fin 4 → CircleCoordinates), IsClosed (P4909T1ParentPolygon L t) := by
  classical
  intro L t
  let complexNormedSpace : NormedSpace ℝ ℂ := by
    refine ⟨fun a z => ?_⟩
    change ‖(a : ℂ) * z‖ ≤ ‖a‖ * ‖z‖
    have ha : ‖(a : ℂ)‖ = ‖a‖ := by norm_cast
    rw [Complex.norm_mul, ha]
  let center (i : Fin 3) : ℂ := (t i.succ).2 / ((t i.succ).1 : ℝ)
  let foot (i k : Fin 3) : ℂ :=
    ⟨if (t k.succ).2 = -1 then L else L + 2, (center i).im⟩
  have hfinite : {z : ℂ | ∃ i : Fin 3, 0 < (t i.succ).1 ∧
      (z = center i ∨ ∃ k : Fin 3, (t k.succ).1 = 0 ∧ z = foot i k)}.Finite := by
    apply (Set.finite_range center).union (Set.finite_range (fun ij : Fin 3 × Fin 3 => foot ij.1
        ij.2)) |>.subset
    rintro z ⟨i, hi, rfl | ⟨k, hk, rfl⟩⟩
    · exact Set.mem_union_left _ ⟨i, rfl⟩
    · exact Set.mem_union_right _ ⟨(i, k), rfl⟩
  change IsClosed (convexHull ℝ {z : ℂ | ∃ i : Fin 3, 0 < (t i.succ).1 ∧
    (z = center i ∨ ∃ k : Fin 3, (t k.succ).1 = 0 ∧ z = foot i k)})
  exact hfinite.isClosed_convexHull ℝ

private theorem gapClosed :
    ∀ (L : Real),  ∀ (t : Fin 4 → CircleCoordinates), IsClosed
        (P4984T1ClosedGap L t) := by
  classical
  intro L t
  have polygonClosed := ClosedSubdivisionProof.polygonClosed L
  have hp := polygonClosed t
  have hineq : IsClosed {z : ℂ | ∀ j : Fin 3, 0 < (t j.succ).1 →
      (1 / ((t j.succ).1 : ℝ)) ≤ dist z ((t j.succ).2 / ((t j.succ).1 : ℝ))} := by
    rw [Set.ofPred_forall]
    apply isClosed_iInter
    intro j
    by_cases hj : 0 < (t j.succ).1
    · have heq : {z : ℂ | 0 < (t j.succ).1 →
          (1 / ((t j.succ).1 : ℝ)) ≤ dist z ((t j.succ).2 / ((t j.succ).1 : ℝ))} =
        {z : ℂ | (1 / ((t j.succ).1 : ℝ)) ≤
          dist z ((t j.succ).2 / ((t j.succ).1 : ℝ))} := by
        ext z
        simp [hj]
      rw [heq]
      exact isClosed_le continuous_const (continuous_id.dist continuous_const)
    · have heq : {z : ℂ | 0 < (t j.succ).1 →
          (1 / ((t j.succ).1 : ℝ)) ≤ dist z ((t j.succ).2 / ((t j.succ).1 : ℝ))} =
        Set.univ := by
        ext z
        simp [hj]
      rw [heq]
      exact isClosed_univ
  change IsClosed (P4909T1ParentPolygon L t ∩ {z : ℂ | ∀ j : Fin 3,
    0 < (t j.succ).1 → (1 / ((t j.succ).1 : ℝ)) ≤
      dist z ((t j.succ).2 / ((t j.succ).1 : ℝ))})
  exact hp.inter hineq

private theorem support :
    ∀ (L : Real), ∀ (q : Fin 4 → CircleCoordinates), (P4828T1LineSupport L q) → (
    let p (i : Fin 4) : ℂ := (q i).2 / ((q i).1 : ℝ)
    let r (i : Fin 4) : ℝ := 1 / ((q i).1 : ℝ)
    ∀ (k : Fin 4), ∀ (i : Fin 4), ((q k).1 = 0) → ((0 < (q i).1) → (if (q k).2 = -1 then (p i).re
        = L + r i
      else (p i).re = L + 2 - r i))) := by
  classical
  intro L q hs p r k i hk hi
  have hh := hs.signed k i hk hi
  have hnum : ((q i).2 : ℂ).re = (q i).2.re := by norm_num
  have hci : ((q i).1 : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hi
  have hre : (p i).re = (q i).2.re / (q i).1 := by simp [p]
  rcases hs.normals k hk with hn | hn
  · simp? [hn]
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

private theorem footDist :
    ∀ (L : Real), ∀ (q : Fin 4 → CircleCoordinates),
    let p (i : Fin 4) : ℂ := (q i).2 / ((q i).1 : ℝ)
    let r (i : Fin 4) : ℝ := 1 / ((q i).1 : ℝ)
    (∀ (i : Fin 4), (0 < (q i).1) → (0 < r i)) → ((∀ (k : Fin 4), ∀ (i : Fin 4), ((q k).1 = 0) →
        ((0 < (q i).1) → (if (q k).2 = -1 then (p i).re = L + r i else (p i).re = L + 2 - r i)))
        → (∀ (k : Fin 4), ∀ (i : Fin 4), ((q k).1 = 0) → ((0 < (q i).1) → (dist (p i) ⟨if (q k).2
        = -1 then L else L + 2, (p i).im⟩ = r i)))) := by
  classical
  intro L q p r rpos support k i hk hi
  have hr := (rpos i hi).le
  have hh := support k i hk hi
  rw [Complex.dist_eq]
  by_cases hn : (q k).2 = -1
  · simp? [hn] at hh ⊢
    have hv : p i - (⟨L, (p i).im⟩ : ℂ) = (r i : ℂ) := by
      apply Complex.ext <;> simp [hh]
    rw [hv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]
  · simp? [hn] at hh ⊢
    have hv : p i - (⟨L + 2, (p i).im⟩ : ℂ) = (-r i : ℂ) := by
      apply Complex.ext <;> simp [hh]
    rw [hv, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]

private theorem footCover :
    ∀ (L : Real), ∀ (q : Fin 4 → CircleCoordinates),
    let p (i : Fin 4) : ℂ := (q i).2 / ((q i).1 : ℝ)
    let r (i : Fin 4) : ℝ := 1 / ((q i).1 : ℝ)
    (∀ (k : Fin 4), ∀ (i : Fin 4), ((q k).1 = 0) → ((0 < (q i).1) → (dist (p i) ⟨if (q k).2 = -1
        then L else L + 2, (p i).im⟩ = r i))) → (∀ (k : Fin 4), ∀ (i : Fin 4), ((q k).1 = 0) →
        ((0 < (q i).1) → (segment ℝ (p i) ⟨if (q k).2 = -1 then L else L + 2, (p i).im⟩ ⊆
        Metric.closedBall (p i) (r i)))) := by
  classical
  intro L q p r footDist k i hk hi z hz
  have hd := footDist k i hk hi
  rcases (P4909T1TangentSegments _ _ (r i) 0
    (by simpa only [add_zero] using hd)).1 hz with h | h
  · exact h
  · have heq : z = ⟨if (q k).2 = -1 then L else L + 2, (p i).im⟩ := by
      simpa only [Metric.mem_closedBall, dist_le_zero] using h
    rw [Metric.mem_closedBall, heq, dist_comm, hd]

private theorem lineDist :
    ∀ (L : Real), ∀ (q : Fin 4 → CircleCoordinates),
    let p (i : Fin 4) : ℂ := (q i).2 / ((q i).1 : ℝ)
    let r (i : Fin 4) : ℝ := 1 / ((q i).1 : ℝ)
    (∀ (i : Fin 4), (0 < (q i).1) → (0 < r i)) → ((∀ (k : Fin 4), ∀ (i : Fin 4), ((q k).1 = 0) →
        ((0 < (q i).1) → (if (q k).2 = -1 then (p i).re = L + r i else (p i).re = L + 2 - r i)))
        → (∀ (k : Fin 4), ∀ (i : Fin 4), ((q k).1 = 0) → ((0 < (q i).1) → (∀ (z : ℂ), (z.re = if
        (q k).2 = -1 then L else L + 2) → (r i ≤ dist z (p i)))))) := by
  classical
  intro L q p r rpos support k i hk hi z hz
  have hh := support k i hk hi
  have hab := Complex.abs_re_le_norm (z - p i)
  rw [Complex.sub_re, hz] at hab
  rw [Complex.dist_eq]
  by_cases hn : (q k).2 = -1
  · simp? [hn] at hh hab
    have heq : L - (p i).re = -r i := by linarith
    rw [heq, abs_neg, abs_of_pos (rpos i hi)] at hab
    exact hab
  · simp? [hn] at hh hab
    have heq : L + 2 - (p i).re = r i := by linarith
    rw [heq, abs_of_pos (rpos i hi)] at hab
    exact hab

private theorem hdist :
    ∀ (t : Fin 4 → CircleCoordinates), (SemiProperQuadruple t) → (∀ (i : Fin 4), ∀ (j : Fin 4),
        (i ≠ j) → ((0 < (t i).1) → ((0 < (t j).1) → (dist (((t i).2 : ℂ) / ((t i).1 : ℝ)) (((t
        j).2 : ℂ) / ((t j).1 : ℝ)) =
        1 / ((t i).1 : ℝ) + 1 / ((t j).1 : ℝ))))) := by
  classical
  intro t ht i j hij hi hj
  let a : ℝ := (t i).1
  let b : ℝ := (t j).1
  let x : ℂ := (t i).2
  let y : ℂ := (t j).2
  change dist (((t i).2 : ℂ) / ((t i).1 : ℝ))
    (((t j).2 : ℂ) / ((t j).1 : ℝ)) =
      1 / ((t i).1 : ℝ) + 1 / ((t j).1 : ℝ)
  change dist (x / a) (y / b) = 1 / a + 1 / b
  have hh := TangencyCoordinateIdentity t ht i j hij
  have hn : (Zsqrtd.norm ((t j).1 • (t i).2 - (t i).1 • (t j).2) : ℝ) =
      ((t i).1 + (t j).1 : ℤ) ^ 2 := by exact_mod_cast hh
  have hns : Complex.normSq ((b : ℝ) * x - a * y) = (a + b)^2 := by
    dsimp [a, b, x, y]
    norm_num [Complex.normSq_apply, Zsqrtd.norm] at hn ⊢
    nlinarith
  have haPos : 0 < a := by simpa [a] using hi
  have hbPos : 0 < b := by simpa [b] using hj
  have ha : a ≠ 0 := ne_of_gt haPos
  have hb : b ≠ 0 := ne_of_gt hbPos
  have hdiv : (x / a - y / b) * (a * b) = (b : ℂ) * x - a * y := by
    field_simp [ha, hb]
  have hratio : x / a - y / b = ((b : ℂ) * x - a * y) / (a * b) := by
    rw [← hdiv]
    field_simp [ha, hb]
  have hnumNorm : ‖(b : ℝ) * x - a * y‖ = a + b := by
    rw [← sq_eq_sq₀ (norm_nonneg _) (add_pos haPos hbPos).le]
    rw [← Complex.normSq_eq_norm_sq]
    exact hns
  have hA : ‖(a : ℂ)‖ = a := by simp [Complex.norm_real, abs_of_pos haPos]
  have hB : ‖(b : ℂ)‖ = b := by simp [Complex.norm_real, abs_of_pos hbPos]
  rw [dist_eq_norm, hratio, Complex.norm_div, hnumNorm,
    Complex.norm_mul, hA, hB]
  field_simp [ha, hb]; ring

private theorem boundaryAvoid :
    ∀ (L : Real), ∀ (q : Fin 4 → CircleCoordinates), (ProperBandQuadruple q) → (
    let p (i : Fin 4) : ℂ := (q i).2 / ((q i).1 : ℝ)
    let r (i : Fin 4) : ℝ := 1 / ((q i).1 : ℝ)
    let s (b : Fin 3) := P4828T1Step (P4828T1Rotate q b)
    let P := P4909T1ParentPolygon L q
    let F (b : Fin 3) := P4909T1ParentPolygon L (s b)
    ((∀ b : Fin 3, F b ⊆ P ∧ (0 < (q b.succ).1 → p b.succ ∉ F b) ∧ frontier (F b) ⊆
        P4909T1ParentEdges L (s b)) ∧ (∀ b c : Fin 3, b ≠ c → Disjoint (interior (F b))
        (interior (F c))) ∧ P = ⋃ b : Fin 3, F b) → (
    let idx (b j : Fin 3) : Fin 4 := ![0, (b + 1).succ, (b + 2).succ] j
    (∀ (b : Fin 3), ∀ (j : Fin 3), s b j.succ = q (idx b j)) → ((∀ (b : Fin 3),
        Function.Injective (idx b)) → ((∀ (b : Fin 3), ∀ (j : Fin 3), idx b j ≠ b.succ) → ((∀ (k
        : Fin 4), ∀ (i : Fin 4), ((q k).1 = 0) → ((0 < (q i).1) → (segment ℝ (p i) ⟨if (q k).2 =
        -1 then L else L + 2, (p i).im⟩ ⊆ Metric.closedBall (p i) (r i)))) → ((∀ (k : Fin 4), ∀
        (i : Fin 4), ((q k).1 = 0) → ((0 < (q i).1) → (∀ (z : ℂ), (z.re = if (q k).2 = -1 then L
        else L + 2) → (r i ≤ dist z (p i))))) → ((∀ (t : Fin 4 → CircleCoordinates),
        (SemiProperQuadruple t) → (∀ (i : Fin 4), ∀ (j : Fin 4), (i ≠ j) → ((0 < (t i).1) → ((0 <
        (t j).1) → (dist (((t i).2 : ℂ) / ((t i).1 : ℝ)) (((t j).2 : ℂ) / ((t j).1 : ℝ)) = 1 /
        ((t i).1 : ℝ) + 1 / ((t j).1 : ℝ)))))) → (∀ (b : Fin 3), (0 < (q b.succ).1) → (∀ z ∈
        frontier (F b), z ∉ Metric.ball (p b.succ) (r b.succ)))))))))) := by
  classical
  intro L q hq p r s P F fan idx parent idx_inj idx_ne footCover lineDist hdist b hb z hz hball
  have hedge := (fan.1 b).2.2 hz
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
  have avoid (i : Fin 3) (hi : 0 < (s b i.succ).1) :
      z ∉ Metric.closedBall (p (idx b i)) (r (idx b i)) := by
    have hroot : 0 < (q (idx b i)).1 := by simpa only [parent] using hi
    have hd := hdist q hq.1 b.succ (idx b i) (idx_ne b i).symm hb hroot
    exact Set.disjoint_left.mp
      (P4909T1TangentSegments _ _ _ _ hd).2 hball
  simp only [parent] at hedge
  rcases hedge with ⟨i, j, hij, hi, hj, hzseg⟩ |
      ⟨i, k, hi, hk, hzseg⟩ | ⟨k, hk, hzline⟩
  · have hrooti : 0 < (q (idx b i)).1 := by simpa only [parent] using hi
    have hrootj : 0 < (q (idx b j)).1 := by simpa only [parent] using hj
    have hij' : idx b i ≠ idx b j := fun he => hij (idx_inj b he)
    have hd := hdist q hq.1 (idx b i) (idx b j) hij' hrooti hrootj
    rcases (P4909T1TangentSegments _ _ _ _ hd).1 hzseg with h | h
    · exact avoid i (by simpa only [parent] using hrooti) h
    · exact avoid j (by simpa only [parent] using hrootj) h
  · have hkroot : (q (idx b k)).1 = 0 := by simpa only [parent] using hk
    have hrooti : 0 < (q (idx b i)).1 := by simpa only [parent] using hi
    have hclosed := footCover (idx b k) (idx b i) hkroot hrooti hzseg
    exact avoid i (by simpa only [parent] using hrooti) hclosed
  · have hkroot : (q (idx b k)).1 = 0 := by simpa only [parent] using hk
    have hdistLine := lineDist (idx b k) b.succ hkroot hb z hzline
    have hball' : dist z (p b.succ) < r b.succ := by
      simpa only [Metric.mem_ball, dist_comm] using hball
    exact (not_lt_of_ge hdistLine) hball'

private theorem omittedClosed :
    ∀ (L : Real), ∀ (q : Fin 4 → CircleCoordinates),
    let p (i : Fin 4) : ℂ := (q i).2 / ((q i).1 : ℝ)
    let r (i : Fin 4) : ℝ := 1 / ((q i).1 : ℝ)
    let s (b : Fin 3) := P4828T1Step (P4828T1Rotate q b)
    let F (b : Fin 3) := P4909T1ParentPolygon L (s b)
    (∀ (b : Fin 3), (0 < (q b.succ).1) → (∀ z ∈ frontier (F b), z ∉ Metric.ball (p b.succ) (r
        b.succ))) → ((∀ (b : Fin 3), (0 < (q b.succ).1) → (∀ z ∈ interior (F b), r b.succ < dist
        z (p b.succ))) → (∀ (b : Fin 3), (0 < (q b.succ).1) → (∀ z ∈ F b, r b.succ ≤ dist z (p
        b.succ)))) := by
  classical
  intro L q p r s F boundaryAvoid omittedInterior b hb
  have polygonClosed := ClosedSubdivisionProof.polygonClosed L
  intro z hz
  by_cases hi : z ∈ interior (F b)
  · exact (omittedInterior b hb z hi).le
  · have hf : z ∈ frontier (F b) := by
      rw [(polygonClosed (s b)).frontier_eq]
      exact ⟨hz, hi⟩
    have hnot := boundaryAvoid b hb z hf
    exact le_of_not_gt (fun hlt => hnot (Metric.mem_ball.mpr (by
      simpa only [Metric.mem_ball, dist_comm] using hlt)))

private theorem childSubset :
    ∀ (L : Real), ∀ (q : Fin 4 → CircleCoordinates),
    let p (i : Fin 4) : ℂ := (q i).2 / ((q i).1 : ℝ)
    let r (i : Fin 4) : ℝ := 1 / ((q i).1 : ℝ)
    let s (b : Fin 3) := P4828T1Step (P4828T1Rotate q b)
    let H := P4984T1ClosedGap L q
    let child (b : Fin 3) := P4984T1ClosedGap L (s b)
    let P := P4909T1ParentPolygon L q
    let F (b : Fin 3) := P4909T1ParentPolygon L (s b)
    ((∀ b : Fin 3, F b ⊆ P ∧ (0 < (q b.succ).1 → p b.succ ∉ F b) ∧ frontier (F b) ⊆
        P4909T1ParentEdges L (s b)) ∧ (∀ b c : Fin 3, b ≠ c → Disjoint (interior (F b))
        (interior (F c))) ∧ P = ⋃ b : Fin 3, F b) → (
    let idx (b j : Fin 3) : Fin 4 := ![0, (b + 1).succ, (b + 2).succ] j
    (∀ (b : Fin 3), ∀ (j : Fin 3), s b j.succ = q (idx b j)) → ((∀ (b : Fin 3), ∀ (j : Fin 3), (j
        ≠ b) → (∃ k : Fin 3, idx b k = j.succ)) → ((∀ (b : Fin 3), (0 < (q b.succ).1) → (∀ z ∈ F
        b, r b.succ ≤ dist z (p b.succ))) → (∀ (b : Fin 3), child b ⊆ H)))) := by
  classical
  intro L q p r s H child P F fan idx parent oldRetained omittedClosed b z hz
  change z ∈ F b ∧ ∀ j : Fin 3, 0 < (s b j.succ).1 →
    1 / ((s b j.succ).1 : ℝ) ≤
      dist z (((s b j.succ).2 : ℂ) / ((s b j.succ).1 : ℝ)) at hz
  change z ∈ P ∧ ∀ j : Fin 3, 0 < (q j.succ).1 →
    1 / ((q j.succ).1 : ℝ) ≤ dist z (p j.succ)
  refine ⟨(fan.1 b).1 hz.1, ?_⟩
  intro j hj
  by_cases hjeq : j = b
  · subst j
    exact omittedClosed b hj z hz.1
  · obtain ⟨k, hk⟩ := oldRetained b j hjeq
    have hp : s b k.succ = q j.succ := by rw [parent, hk]
    have hh := hz.2 k (by simpa only [hp] using hj)
    simpa only [hp, p, r] using hh

private theorem openBallSubset :
    ∀ (L : Real), ∀ (q : Fin 4 → CircleCoordinates), (P4828T1Disk (q (0 : Fin (4 : ℕ))) ⊆
        P4828T1Gap L q) → (
    let p (i : Fin 4) : ℂ := (q i).2 / ((q i).1 : ℝ)
    let r (i : Fin 4) : ℝ := 1 / ((q i).1 : ℝ)
    let H := P4984T1ClosedGap L q
    ∀ (z : ℂ), (z ∈ Metric.ball (p 0) (r 0)) → (z ∈ H)) := by
  classical
  intro L q hi p r H z hz
  let P := P4909T1ParentPolygon L q
  have hg : z ∈ P4828T1Gap L q := by
    apply hi
    simpa only [P4828T1Disk, Metric.mem_ball, p, r] using hz
  change z ∈ P ∧ ∀ j : Fin 3, 0 < (q j.succ).1 →
    1 / ((q j.succ).1 : ℝ) ≤ dist z (p j.succ)
  refine ⟨interior_subset hg.1, ?_⟩
  intro j hj
  exact (hg.2 j hj).le

private theorem makeChild :
    ∀ (L : Real), ∀ (q : Fin 4 → CircleCoordinates),
    let p (i : Fin 4) : ℂ := (q i).2 / ((q i).1 : ℝ)
    let r (i : Fin 4) : ℝ := 1 / ((q i).1 : ℝ)
    let s (b : Fin 3) := P4828T1Step (P4828T1Rotate q b)
    let child (b : Fin 3) := P4984T1ClosedGap L (s b)
    let F (b : Fin 3) := P4909T1ParentPolygon L (s b)
    let idx (b j : Fin 3) : Fin 4 := ![0, (b + 1).succ, (b + 2).succ] j
    (∀ (b : Fin 3), ∀ (j : Fin 3), s b j.succ = q (idx b j)) → ((∀ (b : Fin 3), ∀ (j : Fin 3),
        idx b j ≠ b.succ) → (∀ (b : Fin 3), ∀ (z : ℂ), (z ∈ F b) → ((r 0 ≤ dist z (p 0)) → ((∀ j
        : Fin 3, 0 < (q j.succ).1 →
        r j.succ ≤ dist z (p j.succ)) → (z ∈ child b))))) := by
  classical
  intro L q p r s child F idx parent idx_ne b z hzF hinsert hold
  change z ∈ F b ∧ ∀ k : Fin 3, 0 < (s b k.succ).1 →
    1 / ((s b k.succ).1 : ℝ) ≤
      dist z (((s b k.succ).2 : ℂ) / ((s b k.succ).1 : ℝ))
  refine ⟨hzF, ?_⟩
  intro k hk
  by_cases hzero : idx b k = 0
  · have hp : s b k.succ = q 0 := by rw [parent, hzero]
    simpa only [hp, p, r] using hinsert
  · obtain ⟨j, hj⟩ := Fin.exists_succ_eq.mpr hzero
    have hjb : j ≠ b := by
      intro he
      subst j
      exact idx_ne b k (by simp only [hj])
    have hp : s b k.succ = q j.succ := by rw [parent, hj]
    have hjpos : 0 < (q j.succ).1 := by simpa only [hp] using hk
    have hh := hold j hjpos
    simpa only [hp, p, r] using hh

private theorem hUnion :
    ∀ (L : Real), ∀ (q : Fin 4 → CircleCoordinates),
    let p (i : Fin 4) : ℂ := (q i).2 / ((q i).1 : ℝ)
    let r (i : Fin 4) : ℝ := 1 / ((q i).1 : ℝ)
    let s (b : Fin 3) := P4828T1Step (P4828T1Rotate q b)
    let H := P4984T1ClosedGap L q
    let child (b : Fin 3) := P4984T1ClosedGap L (s b)
    let P := P4909T1ParentPolygon L q
    let F (b : Fin 3) := P4909T1ParentPolygon L (s b)
    ((∀ b : Fin 3, F b ⊆ P ∧ (0 < (q b.succ).1 → p b.succ ∉ F b) ∧ frontier (F b) ⊆
        P4909T1ParentEdges L (s b)) ∧ (∀ b c : Fin 3, b ≠ c → Disjoint (interior (F b))
        (interior (F c))) ∧ P = ⋃ b : Fin 3, F b) → ((∀ (b : Fin 3), child b ⊆ H) →
        ((Metric.closedBall (p 0) (r 0) ⊆ H) → ((∀ (b : Fin 3), ∀ (z : ℂ), (z ∈ F b) → ((r 0 ≤
        dist z (p 0)) → ((∀ j : Fin 3, 0 < (q j.succ).1 → r j.succ ≤ dist z (p j.succ)) → (z ∈
        child b)))) → ((∀ (z : ℂ), (z ∈ H) → (∀ j : Fin 3, 0 < (q j.succ).1 → r j.succ ≤ dist z
        (p j.succ))) → (H = Metric.closedBall (p 0) (r 0) ∪ ⋃ b : Fin 3, child b))))) := by
  classical
  intro L q p r s H child P F fan childSubset closedBallSubset makeChild rootConstraints
  apply Set.Subset.antisymm
  · intro z hz
    by_cases hball : z ∈ Metric.closedBall (p 0) (r 0)
    · exact Set.mem_union_left _ hball
    · have hzP : z ∈ P := by
        change z ∈ P ∧ _ at hz
        exact hz.1
      have hcover : z ∈ ⋃ b : Fin 3, F b := by rw [← fan.2.2]; exact hzP
      obtain ⟨b, hb⟩ := Set.mem_iUnion.mp hcover
      have hnot : r 0 < dist z (p 0) := by
        apply lt_of_not_ge
        intro hle
        exact hball (Metric.mem_closedBall.mpr (by simpa only [dist_comm] using hle))
      exact Set.mem_union_right _ (Set.mem_iUnion.mpr ⟨b,
        makeChild b z hb hnot.le (rootConstraints z hz)⟩)
  · intro z hz
    have hz' : z ∈ Metric.closedBall (p 0) (r 0) ∨ z ∈ ⋃ b : Fin 3, child b := by
      simpa only [Set.mem_union] using hz
    rcases hz' with hball | hchildren
    · exact closedBallSubset hball
    · obtain ⟨b, hb⟩ := Set.mem_iUnion.mp hchildren
      exact childSubset b hb

private theorem sphereSubset :
    ∀ (L : Real), ∀ (q : Fin 4 → CircleCoordinates),
    let p (i : Fin 4) : ℂ := (q i).2 / ((q i).1 : ℝ)
    let r (i : Fin 4) : ℝ := 1 / ((q i).1 : ℝ)
    let s (b : Fin 3) := P4828T1Step (P4828T1Rotate q b)
    let H := P4984T1ClosedGap L q
    let child (b : Fin 3) := P4984T1ClosedGap L (s b)
    let P := P4909T1ParentPolygon L q
    let F (b : Fin 3) := P4909T1ParentPolygon L (s b)
    ((∀ b : Fin 3, F b ⊆ P ∧ (0 < (q b.succ).1 → p b.succ ∉ F b) ∧ frontier (F b) ⊆
        P4909T1ParentEdges L (s b)) ∧ (∀ b c : Fin 3, b ≠ c → Disjoint (interior (F b))
        (interior (F c))) ∧ P = ⋃ b : Fin 3, F b) → ((Metric.closedBall (p 0) (r 0) ⊆ H) → ((∀ (b
        : Fin 3), ∀ (z : ℂ), (z ∈ F b) → ((r 0 ≤ dist z (p 0)) → ((∀ j : Fin 3, 0 < (q j.succ).1
        → r j.succ ≤ dist z (p j.succ)) → (z ∈ child b)))) → ((∀ (z : ℂ), (z ∈ H) → (∀ j : Fin 3,
        0 < (q j.succ).1 → r j.succ ≤ dist z (p j.succ))) → (Metric.sphere (p 0) (r 0) ⊆ ⋃ b :
        Fin 3, child b)))) := by
  classical
  intro L q p r s H child P F fan closedBallSubset makeChild rootConstraints z hz
  have hdistSphere := Metric.mem_sphere.mp hz
  have hzH : z ∈ H := closedBallSubset (Metric.mem_closedBall.mpr (by
    simpa only [dist_comm] using hdistSphere.le))
  have hzP : z ∈ P := by
    change z ∈ P ∧ _ at hzH
    exact hzH.1
  have hcover : z ∈ ⋃ b : Fin 3, F b := by rw [← fan.2.2]; exact hzP
  obtain ⟨b, hb⟩ := Set.mem_iUnion.mp hcover
  have hinsert : r 0 ≤ dist z (p 0) := by
    simpa only [dist_comm] using hdistSphere.ge
  exact Set.mem_iUnion.mpr ⟨b, makeChild b z hb hinsert (rootConstraints z hzH)⟩

end ClosedSubdivisionProof

theorem P4984T1ClosedSubdivision (L : Real)
    (q : Fin 4 → CircleCoordinates) (hq : ProperBandQuadruple q)
    (hs : P4828T1LineSupport L q)
    (hi : P4828T1Disk (q 0) ⊆ P4828T1Gap L q) :
    let H := P4984T1ClosedGap L q
    let child (b : Fin 3) :=
      P4984T1ClosedGap L (P4828T1Step (P4828T1Rotate q b))
    let p : Complex := (q 0).2 / ((q 0).1 : Real)
    let r : Real := 1 / ((q 0).1 : Real)
    IsClosed H ∧
    (∀ b, child b ⊆ H) ∧
    H = Metric.closedBall p r ∪ ⋃ b, child b ∧
    Metric.sphere p r ⊆ ⋃ b, child b ∧
    (∀ b c, b ≠ c → interior (child b) ∩ interior (child c) = ∅) := by
-- BODY
  classical
  let complexNormedSpace : NormedSpace ℝ ℂ := by
    refine ⟨fun a z => ?_⟩
    change ‖(a : ℂ) * z‖ ≤ ‖a‖ * ‖z‖
    have ha : ‖(a : ℂ)‖ = ‖a‖ := by norm_cast
    rw [Complex.norm_mul, ha]
  dsimp only
  let p (i : Fin 4) : ℂ := (q i).2 / ((q i).1 : ℝ)
  let r (i : Fin 4) : ℝ := 1 / ((q i).1 : ℝ)
  let s (b : Fin 3) := P4828T1Step (P4828T1Rotate q b)
  let H := P4984T1ClosedGap L q
  let child (b : Fin 3) := P4984T1ClosedGap L (s b)
  let P := P4909T1ParentPolygon L q
  let F (b : Fin 3) := P4909T1ParentPolygon L (s b)
  have hcurv := ProperBandCurvatureStructure q hq
  have hchildpos : 0 < (q 0).1 := hcurv.1
  have hparentsNonneg : ∀ i : Fin 3, 0 ≤ (q i.succ).1 := hcurv.2.1
  have hcenterIn : p 0 ∈ P4828T1Gap L q := by
    have hball : p 0 ∈ P4828T1Disk (q 0) := by
      change dist (((q 0).2 : ℂ) / ((q 0).1 : ℝ))
        (((q 0).2 : ℂ) / ((q 0).1 : ℝ)) < 1 / ((q 0).1 : ℝ)
      rw [dist_self]
      exact div_pos one_pos (by exact_mod_cast hchildpos)
    exact hi hball
  have hinside : p 0 ∈ interior P := hcenterIn.1
  have hzunique := hcurv.2.2
  have fan := ClosedSubdivisionProof.fan L q hs hchildpos hparentsNonneg hinside
          hzunique
  have polygonClosed (t : Fin 4 → CircleCoordinates) := ClosedSubdivisionProof.polygonClosed L t
  have gapClosed (t : Fin 4 → CircleCoordinates) := ClosedSubdivisionProof.gapClosed L  t
  have hHclosed : IsClosed H := by
    change IsClosed (P4984T1ClosedGap L q)
    exact gapClosed q
  have hchildClosed (b : Fin 3) : IsClosed (child b) := by
    exact gapClosed (s b)
  let idx (b j : Fin 3) : Fin 4 := ![0, (b + 1).succ, (b + 2).succ] j
  have parent (b j : Fin 3) : s b j.succ = q (idx b j) := by
    fin_cases b <;> fin_cases j <;> rfl
  have idx_inj (b : Fin 3) : Function.Injective (idx b) := by
    fin_cases b <;> decide
  have idx_ne (b j : Fin 3) : idx b j ≠ b.succ := by
    fin_cases b <;> fin_cases j <;> decide
  have oldRetained (b j : Fin 3) (hjb : j ≠ b) :
      ∃ k : Fin 3, idx b k = j.succ := by
    clear * - b j hjb idx
    fin_cases b <;> fin_cases j <;> simp_all? [idx]
    all_goals first | exact ⟨1, rfl⟩ | exact ⟨2, rfl⟩
  have rpos (i : Fin 4) (hi : 0 < (q i).1) : 0 < r i := by
    dsimp [r]
    positivity
  have support (k i : Fin 4) (hk : (q k).1 = 0) (hi : 0 < (q i).1) :=
      ClosedSubdivisionProof.support L q hs k i hk hi
  have footDist (k i : Fin 4) (hk : (q k).1 = 0) (hi : 0 < (q i).1) :=
      ClosedSubdivisionProof.footDist L q rpos support k i hk hi
  have footCover (k i : Fin 4) (hk : (q k).1 = 0) (hi : 0 < (q i).1) :=
      ClosedSubdivisionProof.footCover L q footDist k i hk hi
  have lineDist (k i : Fin 4) (hk : (q k).1 = 0) (hi : 0 < (q i).1)
      (z : ℂ) (hz : z.re = if (q k).2 = -1 then L else L + 2) := ClosedSubdivisionProof.lineDist
          L q rpos support k i hk hi z hz
  have hdist (t : Fin 4 → CircleCoordinates) (ht : SemiProperQuadruple t)
      (i j : Fin 4) (hij : i ≠ j) (hi : 0 < (t i).1) (hj : 0 < (t j).1) :=
          ClosedSubdivisionProof.hdist t ht i j hij hi hj
  have boundaryAvoid (b : Fin 3) (hb : 0 < (q b.succ).1) := ClosedSubdivisionProof.boundaryAvoid
      L q hq fan parent idx_inj idx_ne footCover
          lineDist hdist b hb
  have omittedInterior (b : Fin 3) (hb : 0 < (q b.succ).1) :
      ∀ z ∈ interior (F b), r b.succ < dist z (p b.succ) := by
    apply P4909T1OmittedDiskBarrier (F b) (p b.succ) (r b.succ)
      (rpos b.succ hb) ((fan.1 b).2.1 hb)
    rw [Set.disjoint_left]
    intro z hz hball
    exact boundaryAvoid b hb z hz hball
  have omittedClosed (b : Fin 3) (hb : 0 < (q b.succ).1) := ClosedSubdivisionProof.omittedClosed L q
           boundaryAvoid omittedInterior b hb
  have childSubset (b : Fin 3) := ClosedSubdivisionProof.childSubset L q fan parent
      oldRetained omittedClosed b
  have openBallSubset (z : ℂ) (hz : z ∈ Metric.ball (p 0) (r 0)) :=
      ClosedSubdivisionProof.openBallSubset L q hi z hz
  have closedBallSubset : Metric.closedBall (p 0) (r 0) ⊆ H := by
    intro z hz
    have hopen : Metric.ball (p 0) (r 0) ⊆ H := fun w hw => openBallSubset w hw
    have hzball : z ∈ closure (Metric.ball (p 0) (r 0)) := by
      rw [closure_ball (p 0) (ne_of_gt (rpos 0 hchildpos))]
      exact hz
    have hzH : z ∈ closure H := closure_mono hopen hzball
    rw [hHclosed.closure_eq] at hzH
    exact hzH
  have makeChild (b : Fin 3) (z : ℂ) (hzF : z ∈ F b)
      (hinsert : r 0 ≤ dist z (p 0))
      (hold : ∀ j : Fin 3, 0 < (q j.succ).1 →
        r j.succ ≤ dist z (p j.succ)) := ClosedSubdivisionProof.makeChild L q
            parent idx_ne b z hzF hinsert hold
  have rootConstraints (z : ℂ) (hz : z ∈ H) :
      ∀ j : Fin 3, 0 < (q j.succ).1 → r j.succ ≤ dist z (p j.succ) := by
    change z ∈ P ∧ ∀ j : Fin 3, 0 < (q j.succ).1 →
      1 / ((q j.succ).1 : ℝ) ≤ dist z (p j.succ) at hz
    intro j hj
    simpa only [r] using hz.2 j hj
  have hUnion := ClosedSubdivisionProof.hUnion L q fan childSubset closedBallSubset makeChild
      rootConstraints
  have sphereSubset := ClosedSubdivisionProof.sphereSubset L q fan closedBallSubset makeChild
      rootConstraints
  have childPoly (b : Fin 3) : child b ⊆ F b := by
    intro z hz
    change z ∈ F b ∧ _ at hz
    exact hz.1
  have disjointChildInterior (b c : Fin 3) (hbc : b ≠ c) :
      interior (child b) ∩ interior (child c) = ∅ := by
    exact Set.disjoint_iff_inter_eq_empty.mp
      ((fan.2.1 b c hbc).mono (interior_mono (childPoly b))
        (interior_mono (childPoly c)))
  exact ⟨hHclosed, childSubset, hUnion, sphereSubset, disjointChildInterior⟩

end ApollonianSuperharmonic

end
