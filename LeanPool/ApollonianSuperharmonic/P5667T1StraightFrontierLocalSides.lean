/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import LeanPool.ApollonianSuperharmonic.LocalSideScaling

public import LeanPool.ApollonianSuperharmonic.P3934T1SectorSelection
public import LeanPool.ApollonianSuperharmonic.P3889T1TwoRaySectors

-- [TABLET NODE: P5667T1StraightFrontierLocalSides]

/-!
# P5667T1StraightFrontierLocalSides

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace StraightFrontierProof

private theorem hcol :
    (by
      classical
      exact
        ∀ (B : Real × Real),
        let n : Real := ‖B‖
        let d : Real × Real := n⁻¹ • B
        (d ≠ (0, 0)) → (∀ (y : ℝ × ℝ), d.1 * y.2 - d.2 * y.1 = (0 : ℝ) → ∃ (c : ℝ), y = c • d)
    ) := by
  classical
  intro B n d hdnz y hy
  have hcoord : d.1 ≠ 0 ∨ d.2 ≠ 0 := by
    by_contra h
    push Not at h
    apply hdnz
    ext <;> simp [h.1, h.2]
  rcases hcoord with h1 | h2
  · refine ⟨y.1 / d.1, ?_⟩
    ext
    · simp [h1]
    · dsimp
      field_simp
      nlinarith [hy]
  · refine ⟨y.2 / d.2, ?_⟩
    ext
    · dsimp
      field_simp [h2]
      nlinarith [hy]
    · simp [h2]

private theorem hDleft :
    (by
      classical
      exact
        ∀ (x : Real × Real), ∀ (B : Real × Real), ∀ (r : Real),
        let n : Real := ‖B‖
        let d : Real × Real := n⁻¹ • B
        let D : (Real × Real) → Real := fun q =>
          d.1 * (q.2 - x.2) - d.2 * (q.1 - x.1)
        let ray : Set (Real × Real) :=
          {q | ∃ a : Real, 0 ≤ a ∧ q = x + a • (-d)} ∪
            {q | ∃ a : Real, 0 ≤ a ∧ q = x + a • d}
        ∀ (E : P3889T1TwoRaySectorDecomposition x r (-d) d), (∀ (y : Real × Real), (d.1 * y.2 -
            d.2 * y.1 = 0) → (∃ c : Real, y = c • d)) → ((∀ (q : Real × Real), (q ∈ E.left) → (q
            ∈ Metric.ball x r)) → ((∀ (q : Real × Real), (q ∈ E.left) → (q ∉ ray)) → (∀ q ∈
            E.left, D q ≠ (0 : ℝ))))
    ) := by
  classical
  intro x B r n d D ray E hcol hleftball hleftnotray q hq hzero
  have hqball := hleftball q hq
  have hy : d.1 * (q.2 - x.2) - d.2 * (q.1 - x.1) = 0 := by
    simpa [D] using hzero
  obtain ⟨c, hc⟩ := hcol (q - x) (by simpa using hy)
  have hqline : q = x + c • d := by
    calc q = x + (q - x) := by simp
      _ = x + c • d := by rw [hc]
  by_cases h : 0 ≤ c
  · have : q ∈ ray := Or.inr ⟨c, h, hqline⟩
    exact hleftnotray q hq this
  · have hqline' : q = x + (-c) • (-d) := by
      have hvec : (-c) • (-d) = c • d := by simp [neg_smul]
      calc
        q = x + c • d := hqline
        _ = x + (-c) • (-d) := by rw [← hvec]
    have : q ∈ ray := Or.inl ⟨-c, neg_nonneg.mpr (le_of_lt (lt_of_not_ge h)), hqline'⟩
    exact hleftnotray q hq this

private theorem hDright :
    (by
      classical
      exact
        ∀ (x : Real × Real), ∀ (B : Real × Real), ∀ (r : Real),
        let n : Real := ‖B‖
        let d : Real × Real := n⁻¹ • B
        let D : (Real × Real) → Real := fun q =>
          d.1 * (q.2 - x.2) - d.2 * (q.1 - x.1)
        let ray : Set (Real × Real) :=
          {q | ∃ a : Real, 0 ≤ a ∧ q = x + a • (-d)} ∪
            {q | ∃ a : Real, 0 ≤ a ∧ q = x + a • d}
        ∀ (E : P3889T1TwoRaySectorDecomposition x r (-d) d), (∀ (y : Real × Real), (d.1 * y.2 -
            d.2 * y.1 = 0) → (∃ c : Real, y = c • d)) → ((∀ (q : Real × Real), (q ∈ E.right) → (q
            ∈ Metric.ball x r)) → ((∀ (q : Real × Real), (q ∈ E.right) → (q ∉ ray)) → (∀ q ∈
            E.right, D q ≠ (0 : ℝ))))
    ) := by
  classical
  intro x B r n d D ray E hcol hrightball hrightnotray q hq hzero
  have hqball := hrightball q hq
  have hy : d.1 * (q.2 - x.2) - d.2 * (q.1 - x.1) = 0 := by
    simpa [D] using hzero
  obtain ⟨c, hc⟩ := hcol (q - x) (by simpa using hy)
  have hqline : q = x + c • d := by
    calc q = x + (q - x) := by simp
      _ = x + c • d := by rw [hc]
  by_cases h : 0 ≤ c
  · have : q ∈ ray := Or.inr ⟨c, h, hqline⟩
    exact hrightnotray q hq this
  · have hqline' : q = x + (-c) • (-d) := by
      have hvec : (-c) • (-d) = c • d := by simp [neg_smul]
      calc
        q = x + c • d := hqline
        _ = x + (-c) • (-d) := by rw [← hvec]
    have : q ∈ ray := Or.inl ⟨-c, neg_nonneg.mpr (le_of_lt (lt_of_not_ge h)), hqline'⟩
    exact hrightnotray q hq this

private theorem hsectorSign :
    (by
      classical
      exact
        ∀ (x : Real × Real), ∀ (B : Real × Real), ∀ (r : Real),
        let n : Real := ‖B‖
        let d : Real × Real := n⁻¹ • B
        let D : (Real × Real) → Real := fun q =>
          d.1 * (q.2 - x.2) - d.2 * (q.1 - x.1)
        ∀ (E : P3889T1TwoRaySectorDecomposition x r (-d) d),
        let pos : Set (Real × Real) := {q | 0 < D q}
        let neg : Set (Real × Real) := {q | D q < 0}
        (E.left ⊆ pos ∨ E.left ⊆ neg) → ((E.right ⊆ pos ∨ E.right ⊆ neg) → (
        let j : Real × Real := (-d.2, d.1)
        let qpos : Real × Real := x + (r / 4) • j
        let qneg : Real × Real := x - (r / 4) • j
        (0 < D qpos) → ((D qneg < 0) → ((qpos ∈ E.left ∪ E.right) → ((qneg ∈ E.left ∪ E.right) →
            ((E.left ⊆ pos ∧ E.right ⊆ neg) ∨ (E.left ⊆ neg ∧ E.right ⊆ pos)))))))
    ) := by
  classical
  intro x B r n d D E pos neg hleftSign hrightSign j qpos qneg hDpos hDneg hqposCover hqnegCover
  rcases hleftSign with hleftpos | hleftneg
  · refine Or.inl ⟨hleftpos, ?_⟩
    rcases hrightSign with hrightpos | hrightneg
    · exfalso
      rcases hqnegCover with hq | hq
      · exact (not_lt_of_ge (le_of_lt (hleftpos hq))) hDneg
      · exact (not_lt_of_ge (le_of_lt (hrightpos hq))) hDneg
    · exact hrightneg
  · rcases hrightSign with hrightpos | hrightneg
    · exact Or.inr ⟨hleftneg, hrightpos⟩
    · exfalso
      rcases hqposCover with hq | hq
      · exact (not_lt_of_ge (le_of_lt (hleftneg hq))) hDpos
      · exact (not_lt_of_ge (le_of_lt (hrightneg hq))) hDpos

private theorem sectorEq :
    (by
      classical
      exact
        ∀ (x : Real × Real), ∀ (B : Real × Real), ∀ (r : Real),
        let n : Real := ‖B‖
        let d : Real × Real := n⁻¹ • B
        let D : (Real × Real) → Real := fun q =>
          d.1 * (q.2 - x.2) - d.2 * (q.1 - x.1)
        let ray : Set (Real × Real) :=
          {q | ∃ a : Real, 0 ≤ a ∧ q = x + a • (-d)} ∪
            {q | ∃ a : Real, 0 ≤ a ∧ q = x + a • d}
        (∀ (q : Real × Real), (q ∈ ray) → (D q = 0)) → (
        let pos : Set (Real × Real) := {q | 0 < D q}
        let neg : Set (Real × Real) := {q | D q < 0}
        ∀ (C : Set (ℝ × ℝ)), ∀ (D' : Set (ℝ × ℝ)), C ⊆ pos → D' ⊆ neg → C ⊆ Metric.ball x r → D'
            ⊆ Metric.ball x r → C ∪ D' = Metric.ball x r \ ray → C = Metric.ball x r ∩ pos ∧ D' =
            Metric.ball x r ∩ neg)
    ) := by
  classical
  intro x B r n d D ray hrayzero pos neg C D' hCpos hDneg hCball hDball hCD
  constructor
  · apply Set.Subset.antisymm
    · intro q hq
      exact ⟨hCball hq, hCpos hq⟩
    · intro q hq
      rcases hq with ⟨hqball, hqpos⟩
      have hc : q ∈ C ∪ D' := by
        rw [hCD]
        refine ⟨hqball, ?_⟩
        intro hqr
        have hz := hrayzero q hqr
        change 0 < D q at hqpos
        change D q = 0 at hz
        linarith
      rcases hc with hqC | hqD
      · exact hqC
      · have hqneg := hDneg hqD
        change D q < 0 at hqneg
        exact False.elim ((not_lt_of_ge (le_of_lt hqneg)) hqpos)
  · apply Set.Subset.antisymm
    · intro q hq
      exact ⟨hDball hq, hDneg hq⟩
    · intro q hq
      rcases hq with ⟨hqball, hqneg⟩
      have hc : q ∈ C ∪ D' := by
        rw [hCD]
        refine ⟨hqball, ?_⟩
        intro hqr
        have hz := hrayzero q hqr
        change D q < 0 at hqneg
        change D q = 0 at hz
        linarith
      rcases hc with hqC | hqD
      · have hqpos := hCpos hqC
        change 0 < D q at hqpos
        exact False.elim ((not_lt_of_ge (le_of_lt hqpos)) hqneg)
      · exact hqD

private theorem hsectorEq :
    (by
      classical
      exact
        ∀ (x : Real × Real), ∀ (B : Real × Real), ∀ (r : Real),
        let n : Real := ‖B‖
        let d : Real × Real := n⁻¹ • B
        let D : (Real × Real) → Real := fun q =>
          d.1 * (q.2 - x.2) - d.2 * (q.1 - x.1)
        let ray : Set (Real × Real) :=
          {q | ∃ a : Real, 0 ≤ a ∧ q = x + a • (-d)} ∪
            {q | ∃ a : Real, 0 ≤ a ∧ q = x + a • d}
        ∀ (E : P3889T1TwoRaySectorDecomposition x r (-d) d), (E.left ∪ E.right = Metric.ball x
            r \ ray) → ((∀ (q : Real × Real), (q ∈ E.left) → (q ∈ Metric.ball x r)) → ((∀ (q :
            Real × Real), (q ∈ E.right) → (q ∈ Metric.ball x r)) → (
        let pos : Set (Real × Real) := {q | 0 < D q}
        let neg : Set (Real × Real) := {q | D q < 0}
        ((E.left ⊆ pos ∧ E.right ⊆ neg) ∨ (E.left ⊆ neg ∧ E.right ⊆ pos)) → ((∀ (C : Set (Real ×
            Real)), ∀ (D' : Set (Real × Real)), (C ⊆ pos) → ((D' ⊆ neg) → ((C ⊆ Metric.ball x r)
            → ((D' ⊆ Metric.ball x r) → ((C ∪ D' = Metric.ball x r \ ray) → (C = Metric.ball x r
            ∩ pos ∧ D' = Metric.ball x r ∩ neg)))))) → ((E.left = Metric.ball x r ∩ pos ∧ E.right
            = Metric.ball x r ∩ neg) ∨ (E.left = Metric.ball x r ∩ neg ∧ E.right = Metric.ball x
            r ∩ pos))))))
    ) := by
  classical
  intro x B r n d D ray E hcover hleftball hrightball pos neg hsectorSign sectorEq
  rcases hsectorSign with h | h
  · exact Or.inl (sectorEq E.left E.right h.1 h.2 hleftball hrightball hcover)
  · have hcover' : E.right ∪ E.left = Metric.ball x r \ ray := by
      rw [Set.union_comm]
      exact hcover
    obtain ⟨hrightPos, hleftNeg⟩ :=
      sectorEq E.right E.left h.2 h.1 hrightball hleftball hcover'
    exact Or.inr ⟨hleftNeg, hrightPos⟩

private theorem sidePos :
    (by
      classical
      exact
        ∀ (x : Real × Real), ∀ (B : Real × Real), ∀ (r : Real), ((0 : ℝ) < r) → (
        let n : Real := ‖B‖
        let d : Real × Real := n⁻¹ • B
        let D : (Real × Real) → Real := fun q =>
          d.1 * (q.2 - x.2) - d.2 * (q.1 - x.1)
        let pos : Set (Real × Real) := {q | 0 < D q}
        ∀ (W : Set (ℝ × ℝ)), W ∩ Metric.ball x r = Metric.ball x r ∩ pos → P3934T1LocalSide W x
            d true)
    ) := by
  classical
  intro x B r hr n d D pos W hW
  refine ⟨r, hr, ?_⟩
  change W ∩ Metric.ball x r =
    {q | q ∈ Metric.ball x r ∧ 0 <
      d.1 * (q.2 - x.2) - d.2 * (q.1 - x.1)}
  rw [hW]
  ext q
  simp [pos, D]

private theorem sideNeg :
    (by
      classical
      exact
        ∀ (x : Real × Real), ∀ (B : Real × Real), ∀ (r : Real), ((0 : ℝ) < r) → (
        let n : Real := ‖B‖
        let d : Real × Real := n⁻¹ • B
        let D : (Real × Real) → Real := fun q =>
          d.1 * (q.2 - x.2) - d.2 * (q.1 - x.1)
        let neg : Set (Real × Real) := {q | D q < 0}
        ∀ (W : Set (ℝ × ℝ)), W ∩ Metric.ball x r = Metric.ball x r ∩ neg → P3934T1LocalSide W x
            d false)
    ) := by
  classical
  intro x B r hr n d D neg W hW
  refine ⟨r, hr, ?_⟩
  change W ∩ Metric.ball x r =
    {q | q ∈ Metric.ball x r ∧
      (d.1 * (q.2 - x.2) - d.2 * (q.1 - x.1)) < 0}
  rw [hW]
  ext q
  simp [neg, D]

private theorem hlocal :
    (by
      classical
      exact
        ∀ (U : Set (Real × Real)), ∀ (x : Real × Real), ∀ (B : Real × Real), ∀ (r : Real),
        let n : Real := ‖B‖
        let d : Real × Real := n⁻¹ • B
        let D : (Real × Real) → Real := fun q =>
          d.1 * (q.2 - x.2) - d.2 * (q.1 - x.1)
        ∀ (E : P3889T1TwoRaySectorDecomposition x r (-d) d), (U ∩ Metric.ball x r = E.left ∧
            (closure U)ᶜ ∩ Metric.ball x r = E.right ∨ U ∩ Metric.ball x r = E.right ∧ (closure
            U)ᶜ ∩ Metric.ball x r = E.left) → (
        let pos : Set (Real × Real) := {q | 0 < D q}
        let neg : Set (Real × Real) := {q | D q < 0}
        ((E.left = Metric.ball x r ∩ pos ∧ E.right = Metric.ball x r ∩ neg) ∨ (E.left =
            Metric.ball x r ∩ neg ∧ E.right = Metric.ball x r ∩ pos)) → ((∀ (W : Set (Real ×
            Real)), (W ∩ Metric.ball x r = Metric.ball x r ∩ pos) → (P3934T1LocalSide W x d
            true)) → ((∀ (W : Set (Real × Real)), (W ∩ Metric.ball x r = Metric.ball x r ∩ neg) →
            (P3934T1LocalSide W x d false)) → (∃ e : Bool, P3934T1LocalSide U x d e ∧
            P3934T1LocalSide (closure U)ᶜ x d (!e)))))
    ) := by
  classical
  intro U x B r n d D E hselect pos neg hsectorEq sidePos sideNeg
  rcases hselect with hs | hs
  · rcases hsectorEq with heq | heq
    · exact ⟨true, sidePos U (by rw [hs.1, heq.1]),
        sideNeg (closure U)ᶜ (by rw [hs.2, heq.2])⟩
    · exact ⟨false, sideNeg U (by rw [hs.1, heq.1]),
        sidePos (closure U)ᶜ (by rw [hs.2, heq.2])⟩
  · rcases hsectorEq with heq | heq
    · exact ⟨false, sideNeg U (by rw [hs.1, heq.2]),
        sidePos (closure U)ᶜ (by rw [hs.2, heq.1])⟩
    · exact ⟨true, sidePos U (by rw [hs.1, heq.2]),
        sideNeg (closure U)ᶜ (by rw [hs.2, heq.1])⟩

end StraightFrontierProof

namespace StraightFrontierDetails

private theorem hBdecomp :
    (by
      classical
      exact
        ∀ (B : Real × Real),
        let n : Real := ‖B‖
        (0 < n) → (
        let d : Real × Real := n⁻¹ • B
        B = n • d) ) := by
  classical
  intro B n hn d
  dsimp [d]
  rw [smul_smul]
  simp [n, hn.ne']

private theorem hd :
    (by
      classical
      exact
        ∀ (B : Real × Real),
        let n : Real := ‖B‖
        (0 < n) → (
        let d : Real × Real := n⁻¹ • B
        ‖d‖ = 1) ) := by
  classical
  intro B n hn d
  dsimp [d]
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn)]
  change n⁻¹ * n = 1
  exact inv_mul_cancel₀ hn.ne'

private theorem hdnz :
    (by
      classical
      exact
        ∀ (B : Real × Real),
        let n : Real := ‖B‖
        let d : Real × Real := n⁻¹ • B
        (‖d‖ = 1) → (d ≠ (0, 0)) ) := by
  classical
  intro B n d hd hz
  rw [hz] at hd
  norm_num at hd

private theorem hnotopp :
    (by
      classical
      exact
        ∀ (B : Real × Real),
        let n : Real := ‖B‖
        let d : Real × Real := n⁻¹ • B
        (d ≠ (0, 0)) → (-d ≠ d) ) := by
  classical
  intro B n d hdnz hz
  have h1 : d.1 = 0 := by have := congrArg Prod.fst hz; dsimp at this; linarith
  have h2 : d.2 = 0 := by have := congrArg Prod.snd hz; dsimp at this; linarith
  apply hdnz
  ext <;> assumption

private theorem hminus :
    (by
      classical
      exact
        ∀ (x : Real × Real), ∀ (B : Real × Real),
        let n : Real := ‖B‖
        let d : Real × Real := n⁻¹ • B
        {q | ∃ a : Real, 0 ≤ a ∧ q = x - a • d} = {q | ∃ a : Real, 0 ≤ a ∧ q = x + a • (-d)} ) := by
  classical
  intro x B n d
  ext q
  constructor
  · rintro ⟨a, ha, hq⟩
    exact ⟨a, ha, by simpa [smul_neg, sub_eq_add_neg] using hq⟩
  · rintro ⟨a, ha, hq⟩
    exact ⟨a, ha, by simpa [smul_neg, sub_eq_add_neg] using hq⟩

private theorem hchart' :
    (by
      classical
      exact
        ∀ (U : Set (Real × Real)), ∀ (x : Real × Real), ∀ (B : Real × Real), ∀ (r : Real),
            (frontier U ∩ Metric.ball x r = ({q : ℝ × ℝ | ∃ (a : ℝ), (0 : ℝ) ≤ a ∧ q = x + a •
            ‖B‖⁻¹ • B} ∪ {q : ℝ × ℝ | ∃ (a : ℝ), (0 : ℝ) ≤ a ∧ q = x - a • ‖B‖⁻¹ • B}) ∩
            Metric.ball x r) → (
        let n : Real := ‖B‖
        let d : Real × Real := n⁻¹ • B
        let ray : Set (Real × Real) :=
          {q | ∃ a : Real, 0 ≤ a ∧ q = x + a • (-d)} ∪
            {q | ∃ a : Real, 0 ≤ a ∧ q = x + a • d}
        ({q | ∃ a : Real, 0 ≤ a ∧ q = x - a • d} = {q | ∃ a : Real, 0 ≤ a ∧ q = x + a • (-d)}) →
            (frontier U ∩ Metric.ball x r = ray ∩ Metric.ball x r)) ) := by
  classical
  intro U x B r hchart n d ray hminus
  rw [hminus, Set.union_comm] at hchart
  simpa only [ray] using hchart

private theorem hx :
    (by
      classical
      exact
        ∀ (U : Set (Real × Real)), ∀ (x : Real × Real), ∀ (B : Real × Real), ∀ (r : Real), ((0 :
            ℝ) < r) → ((frontier U ∩ Metric.ball x r = ({q : ℝ × ℝ | ∃ (a : ℝ), (0 : ℝ) ≤ a ∧ q =
            x + a • ‖B‖⁻¹ • B} ∪ {q : ℝ × ℝ | ∃ (a : ℝ), (0 : ℝ) ≤ a ∧ q = x - a • ‖B‖⁻¹ • B}) ∩
            Metric.ball x r) → (x ∈ frontier U)) ) := by
  classical
  intro U x B r hr hchart
  have hm : x ∈ frontier U ∩ Metric.ball x r := by
    rw [hchart]
    exact ⟨Or.inl ⟨0, le_rfl, by simp⟩, Metric.mem_ball_self hr⟩
  exact hm.1

private theorem hrayzero :
    (by
      classical
      exact
        ∀ (x : Real × Real), ∀ (B : Real × Real),
        let n : Real := ‖B‖
        let d : Real × Real := n⁻¹ • B
        let D : (Real × Real) → Real := fun q =>
          d.1 * (q.2 - x.2) - d.2 * (q.1 - x.1)
        let ray : Set (Real × Real) :=
          {q | ∃ a : Real, 0 ≤ a ∧ q = x + a • (-d)} ∪
            {q | ∃ a : Real, 0 ≤ a ∧ q = x + a • d}
        ∀ q ∈ ray, D q = (0 : ℝ) ) := by
  classical
  intro x B n d D ray q hq
  rcases hq with ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩
  · dsimp [D]
    simp []
    ring
  · dsimp [D]
    simp []
    ring

private theorem hleftball :
    (by
      classical
      exact
        ∀ (x : Real × Real), ∀ (B : Real × Real), ∀ (r : Real),
        let n : Real := ‖B‖
        let d : Real × Real := n⁻¹ • B
        let ray : Set (Real × Real) :=
          {q | ∃ a : Real, 0 ≤ a ∧ q = x + a • (-d)} ∪
            {q | ∃ a : Real, 0 ≤ a ∧ q = x + a • d}
        ∀ (E : P3889T1TwoRaySectorDecomposition x r (-d) d), (E.left ∪ E.right = Metric.ball x
            r \ ray) → (∀ q ∈ E.left, q ∈ Metric.ball x r) ) := by
  classical
  intro x B r n d ray E hcover q hq
  have hq' : q ∈ E.left ∪ E.right := Or.inl hq
  rw [hcover] at hq'
  exact hq'.1

private theorem hrightball :
    (by
      classical
      exact
        ∀ (x : Real × Real), ∀ (B : Real × Real), ∀ (r : Real),
        let n : Real := ‖B‖
        let d : Real × Real := n⁻¹ • B
        let ray : Set (Real × Real) :=
          {q | ∃ a : Real, 0 ≤ a ∧ q = x + a • (-d)} ∪
            {q | ∃ a : Real, 0 ≤ a ∧ q = x + a • d}
        ∀ (E : P3889T1TwoRaySectorDecomposition x r (-d) d), (E.left ∪ E.right = Metric.ball x
            r \ ray) → (∀ q ∈ E.right, q ∈ Metric.ball x r) ) := by
  classical
  intro x B r n d ray E hcover q hq
  have hq' : q ∈ E.left ∪ E.right := Or.inr hq
  rw [hcover] at hq'
  exact hq'.1

private theorem hleftnotray :
    (by
      classical
      exact
        ∀ (x : Real × Real), ∀ (B : Real × Real), ∀ (r : Real),
        let n : Real := ‖B‖
        let d : Real × Real := n⁻¹ • B
        let ray : Set (Real × Real) :=
          {q | ∃ a : Real, 0 ≤ a ∧ q = x + a • (-d)} ∪
            {q | ∃ a : Real, 0 ≤ a ∧ q = x + a • d}
        ∀ (E : P3889T1TwoRaySectorDecomposition x r (-d) d), (E.left ∪ E.right = Metric.ball x
            r \ ray) → (∀ q ∈ E.left, q ∉ ray) ) := by
  classical
  intro x B r n d ray E hcover q hq
  have hq' : q ∈ E.left ∪ E.right := Or.inl hq
  rw [hcover] at hq'
  exact hq'.2

private theorem hrightnotray :
    (by
      classical
      exact
        ∀ (x : Real × Real), ∀ (B : Real × Real), ∀ (r : Real),
        let n : Real := ‖B‖
        let d : Real × Real := n⁻¹ • B
        let ray : Set (Real × Real) :=
          {q | ∃ a : Real, 0 ≤ a ∧ q = x + a • (-d)} ∪
            {q | ∃ a : Real, 0 ≤ a ∧ q = x + a • d}
        ∀ (E : P3889T1TwoRaySectorDecomposition x r (-d) d), (E.left ∪ E.right = Metric.ball x
            r \ ray) → (∀ q ∈ E.right, q ∉ ray) ) := by
  classical
  intro x B r n d ray E hcover q hq
  have hq' : q ∈ E.left ∪ E.right := Or.inr hq
  rw [hcover] at hq'
  exact hq'.2

private theorem hposnegDis :
    (by
      classical
      exact
        ∀ (x : Real × Real), ∀ (B : Real × Real),
        let n : Real := ‖B‖
        let d : Real × Real := n⁻¹ • B
        let D : (Real × Real) → Real := fun q =>
          d.1 * (q.2 - x.2) - d.2 * (q.1 - x.1)
        let pos : Set (Real × Real) := {q | 0 < D q}
        let neg : Set (Real × Real) := {q | D q < 0}
        Disjoint pos neg ) := by
  classical
  intro x B n d D pos neg
  apply Set.disjoint_left.mpr
  intro q hqpos hqneg
  change 0 < D q at hqpos
  change D q < 0 at hqneg
  exact (not_lt_of_ge (le_of_lt hqpos)) hqneg

private theorem hleftSplit :
    (by
      classical
      exact
        ∀ (x : Real × Real), ∀ (B : Real × Real), ∀ (r : Real),
        let n : Real := ‖B‖
        let d : Real × Real := n⁻¹ • B
        let D : (Real × Real) → Real := fun q =>
          d.1 * (q.2 - x.2) - d.2 * (q.1 - x.1)
        ∀ (E : P3889T1TwoRaySectorDecomposition x r (-d) d), (∀ (q : Real × Real), (q ∈ E.left)
            → (D q ≠ 0)) → (
        let pos : Set (Real × Real) := {q | 0 < D q}
        let neg : Set (Real × Real) := {q | D q < 0}
        E.left ⊆ pos ∪ neg) ) := by
  classical
  intro x B r n d D E hDleft pos neg q hq
  have hne := hDleft q hq
  by_cases hn : D q < 0
  · exact Or.inr hn
  · exact Or.inl (lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm hne))

private theorem hrightSplit :
    (by
      classical
      exact
        ∀ (x : Real × Real), ∀ (B : Real × Real), ∀ (r : Real),
        let n : Real := ‖B‖
        let d : Real × Real := n⁻¹ • B
        let D : (Real × Real) → Real := fun q =>
          d.1 * (q.2 - x.2) - d.2 * (q.1 - x.1)
        ∀ (E : P3889T1TwoRaySectorDecomposition x r (-d) d), (∀ (q : Real × Real), (q ∈
            E.right) → (D q ≠ 0)) → (
        let pos : Set (Real × Real) := {q | 0 < D q}
        let neg : Set (Real × Real) := {q | D q < 0}
        E.right ⊆ pos ∪ neg) ) := by
  classical
  intro x B r n d D E hDright pos neg q hq
  have hne := hDright q hq
  by_cases hn : D q < 0
  · exact Or.inr hn
  · exact Or.inl (lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm hne))

private theorem hleftSign :
    (by
      classical
      exact
        ∀ (x : Real × Real), ∀ (B : Real × Real), ∀ (r : Real),
        let n : Real := ‖B‖
        let d : Real × Real := n⁻¹ • B
        let D : (Real × Real) → Real := fun q =>
          d.1 * (q.2 - x.2) - d.2 * (q.1 - x.1)
        ∀ (E : P3889T1TwoRaySectorDecomposition x r (-d) d),
        let pos : Set (Real × Real) := {q | 0 < D q}
        let neg : Set (Real × Real) := {q | D q < 0}
        (IsOpen pos) → ((IsOpen neg) → ((Disjoint pos neg) → ((E.left ⊆ pos ∪ neg) → (E.left ⊆
            pos ∨ E.left ⊆ neg)))) ) := by
  classical
  intro x B r n d D E pos neg hposOpen hnegOpen hposnegDis hleftSplit
  by_cases hp : (E.left ∩ pos).Nonempty
  · exact Or.inl (E.left_connected.isPreconnected.subset_left_of_subset_union
      hposOpen hnegOpen hposnegDis hleftSplit hp)
  · right
    intro q hq
    rcases hleftSplit hq with hpq | hnq
    · exact (hp ⟨q, hq, hpq⟩).elim
    · exact hnq

private theorem hrightSign :
    (by
      classical
      exact
        ∀ (x : Real × Real), ∀ (B : Real × Real), ∀ (r : Real),
        let n : Real := ‖B‖
        let d : Real × Real := n⁻¹ • B
        let D : (Real × Real) → Real := fun q =>
          d.1 * (q.2 - x.2) - d.2 * (q.1 - x.1)
        ∀ (E : P3889T1TwoRaySectorDecomposition x r (-d) d),
        let pos : Set (Real × Real) := {q | 0 < D q}
        let neg : Set (Real × Real) := {q | D q < 0}
        (IsOpen pos) → ((IsOpen neg) → ((Disjoint pos neg) → ((E.right ⊆ pos ∪ neg) → (E.right ⊆
            pos ∨ E.right ⊆ neg)))) ) := by
  classical
  intro x B r n d D E pos neg hposOpen hnegOpen hposnegDis hrightSplit
  by_cases hp : (E.right ∩ pos).Nonempty
  · exact Or.inl (E.right_connected.isPreconnected.subset_left_of_subset_union
      hposOpen hnegOpen hposnegDis hrightSplit hp)
  · right
    intro q hq
    rcases hrightSplit hq with hpq | hnq
    · exact (hp ⟨q, hq, hpq⟩).elim
    · exact hnq

private theorem hsq :
    (by
      classical
      exact
        ∀ (B : Real × Real),
        let n : Real := ‖B‖
        let d : Real × Real := n⁻¹ • B
        (d ≠ (0, 0)) → (0 < d.1 ^ 2 + d.2 ^ 2) ) := by
  classical
  intro B n d hdnz
  rcases (show d.1 ≠ 0 ∨ d.2 ≠ 0 from by
    by_contra h
    push Not at h
    exact hdnz (by ext <;> simp [h.1, h.2])) with h1 | h2
  · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero h1) (sq_nonneg _)
  · exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero h2)

private theorem hjnorm :
    (by
      classical
      exact
        ∀ (B : Real × Real),
        let n : Real := ‖B‖
        let d : Real × Real := n⁻¹ • B
        (‖d‖ = 1) → (
        let j : Real × Real := (-d.2, d.1)
        ‖j‖ = 1) ) := by
  classical
  intro B n d hd j
  dsimp [j]
  simpa [Prod.norm_def, Real.norm_eq_abs, max_comm] using hd

private theorem hqposball :
    (by
      classical
      exact
        ∀ (x : Real × Real), ∀ (B : Real × Real), ∀ (r : Real), ((0 : ℝ) < r) → (
        let n : Real := ‖B‖
        let d : Real × Real := n⁻¹ • B
        let j : Real × Real := (-d.2, d.1)
        (‖j‖ = 1) → (
        let qpos : Real × Real := x + (r / 4) • j
        qpos ∈ Metric.ball x r)) ) := by
  classical
  intro x B r hr n d j hjnorm qpos
  change dist qpos x < r
  rw [dist_eq_norm]
  have hdiff : qpos - x = (r / 4) • j := by simp [qpos]
  rw [hdiff, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity : 0 < r / 4), hjnorm]
  linarith

private theorem hqnegball :
    (by
      classical
      exact
        ∀ (x : Real × Real), ∀ (B : Real × Real), ∀ (r : Real), ((0 : ℝ) < r) → (
        let n : Real := ‖B‖
        let d : Real × Real := n⁻¹ • B
        let j : Real × Real := (-d.2, d.1)
        (‖j‖ = 1) → (
        let qneg : Real × Real := x - (r / 4) • j
        qneg ∈ Metric.ball x r)) ) := by
  classical
  intro x B r hr n d j hjnorm qneg
  change dist qneg x < r
  rw [dist_eq_norm]
  have hdiff : qneg - x = -((r / 4) • j) := by simp [qneg, sub_eq_add_neg]
  rw [hdiff, norm_neg, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity : 0 < r / 4), hjnorm]
  linarith

private theorem hDpos :
    (by
      classical
      exact
        ∀ (x : Real × Real), ∀ (B : Real × Real), ∀ (r : Real), ((0 : ℝ) < r) → (
        let n : Real := ‖B‖
        let d : Real × Real := n⁻¹ • B
        let D : (Real × Real) → Real := fun q =>
          d.1 * (q.2 - x.2) - d.2 * (q.1 - x.1)
        (0 < d.1 ^ 2 + d.2 ^ 2) → (
        let j : Real × Real := (-d.2, d.1)
        let qpos : Real × Real := x + (r / 4) • j
        0 < D qpos)) ) := by
  classical
  intro x B r hr n d D hsq j qpos
  dsimp [D, qpos, j]
  simp []
  nlinarith [hsq, hr]

private theorem hDneg :
    (by
      classical
      exact
        ∀ (x : Real × Real), ∀ (B : Real × Real), ∀ (r : Real), ((0 : ℝ) < r) → (
        let n : Real := ‖B‖
        let d : Real × Real := n⁻¹ • B
        let D : (Real × Real) → Real := fun q =>
          d.1 * (q.2 - x.2) - d.2 * (q.1 - x.1)
        (0 < d.1 ^ 2 + d.2 ^ 2) → (
        let j : Real × Real := (-d.2, d.1)
        let qneg : Real × Real := x - (r / 4) • j
        D qneg < 0)) ) := by
  classical
  intro x B r hr n d D hsq j qneg
  dsimp [D, qneg, j]
  simp []
  nlinarith [hsq, hr]

private theorem hqposCover :
    (by
      classical
      exact
        ∀ (x : Real × Real), ∀ (B : Real × Real), ∀ (r : Real),
        let n : Real := ‖B‖
        let d : Real × Real := n⁻¹ • B
        let D : (Real × Real) → Real := fun q =>
          d.1 * (q.2 - x.2) - d.2 * (q.1 - x.1)
        let ray : Set (Real × Real) :=
          {q | ∃ a : Real, 0 ≤ a ∧ q = x + a • (-d)} ∪
            {q | ∃ a : Real, 0 ≤ a ∧ q = x + a • d}
        ∀ (E : P3889T1TwoRaySectorDecomposition x r (-d) d), (∀ (q : Real × Real), (q ∈ ray) →
            (D q = 0)) → ((E.left ∪ E.right = Metric.ball x r \ ray) → (
        let j : Real × Real := (-d.2, d.1)
        let qpos : Real × Real := x + (r / 4) • j
        (qpos ∈ Metric.ball x r) → ((0 < D qpos) → (qpos ∈ E.left ∪ E.right)))) ) := by
  classical
  intro x B r n d D ray E hrayzero hcover j qpos hqposball hDpos
  rw [hcover]
  refine ⟨hqposball, ?_⟩
  intro hqray
  have := hrayzero qpos hqray
  linarith

private theorem hqnegCover :
    (by
      classical
      exact
        ∀ (x : Real × Real), ∀ (B : Real × Real), ∀ (r : Real),
        let n : Real := ‖B‖
        let d : Real × Real := n⁻¹ • B
        let D : (Real × Real) → Real := fun q =>
          d.1 * (q.2 - x.2) - d.2 * (q.1 - x.1)
        let ray : Set (Real × Real) :=
          {q | ∃ a : Real, 0 ≤ a ∧ q = x + a • (-d)} ∪
            {q | ∃ a : Real, 0 ≤ a ∧ q = x + a • d}
        ∀ (E : P3889T1TwoRaySectorDecomposition x r (-d) d), (∀ (q : Real × Real), (q ∈ ray) →
            (D q = 0)) → ((E.left ∪ E.right = Metric.ball x r \ ray) → (
        let j : Real × Real := (-d.2, d.1)
        let qneg : Real × Real := x - (r / 4) • j
        (qneg ∈ Metric.ball x r) → ((D qneg < 0) → (qneg ∈ E.left ∪ E.right)))) ) := by
  classical
  intro x B r n d D ray E hrayzero hcover j qneg hqnegball hDneg
  rw [hcover]
  refine ⟨hqnegball, ?_⟩
  intro hqray
  have := hrayzero qneg hqray
  linarith

end StraightFrontierDetails

theorem P5667T1StraightFrontierLocalSides
    (U : Set (Real × Real)) (hU : IsOpen U)
    (he : frontier (closure U)ᶜ = frontier U)
    (x B : Real × Real) (hB : B ≠ 0) (r : Real) (hr : 0 < r)
    (hchart : frontier U ∩ Metric.ball x r =
      ({q | ∃ a : Real, 0 ≤ a ∧ q = x + a • (‖B‖⁻¹ • B)} ∪
        {q | ∃ a : Real, 0 ≤ a ∧ q = x - a • (‖B‖⁻¹ • B)}) ∩
          Metric.ball x r) :
    ∃ e : Bool, P3934T1LocalSide U x B e ∧
      P3934T1LocalSide (closure U)ᶜ x B (!e) := by
-- BODY
  have scaleLocalSide (W : Set (Real × Real)) (z w : Real × Real)
      (c : Real) (e : Bool) (hc : 0 < c)
      (hside : P3934T1LocalSide W z w e) :
      P3934T1LocalSide W z (c • w) e := LocalSideScaling.positiveScale W z w c e hc hside
  let n : Real := ‖B‖
  have hn : 0 < n := by dsimp [n]; exact norm_pos_iff.mpr hB
  let d : Real × Real := n⁻¹ • B
  have hBdecomp : B = n • d := StraightFrontierDetails.hBdecomp B hn
  have hd : ‖d‖ = 1 := StraightFrontierDetails.hd B hn
  have hdnz : d ≠ (0, 0) := StraightFrontierDetails.hdnz B hd
  have hnotopp : -d ≠ d := StraightFrontierDetails.hnotopp B hdnz
  let D : (Real × Real) → Real := fun q =>
    d.1 * (q.2 - x.2) - d.2 * (q.1 - x.1)
  have hDcont : Continuous D := by dsimp [D]; fun_prop
  let ray : Set (Real × Real) :=
    {q | ∃ a : Real, 0 ≤ a ∧ q = x + a • (-d)} ∪
      {q | ∃ a : Real, 0 ≤ a ∧ q = x + a • d}
  have hminus :
      {q | ∃ a : Real, 0 ≤ a ∧ q = x - a • d} =
        {q | ∃ a : Real, 0 ≤ a ∧ q = x + a • (-d)} := StraightFrontierDetails.hminus x B
  have hchart' : frontier U ∩ Metric.ball x r = ray ∩ Metric.ball x r :=
      StraightFrontierDetails.hchart' U x B r hchart hminus
  have hx : x ∈ frontier U := StraightFrontierDetails.hx U x B r hr hchart
  obtain ⟨E⟩ := P3889T1TwoRaySectors x r (-d) d hr (by simpa using hd)
    hd hnotopp
  have hselect := P3934T1SectorSelection U x r (-d) d E hr hU hx he hchart'
  have hcol (y : Real × Real) (hy : d.1 * y.2 - d.2 * y.1 = 0) :
      ∃ c : Real, y = c • d := StraightFrontierProof.hcol B hdnz y hy
  have hrayzero (q : Real × Real) (hq : q ∈ ray) : D q = 0 := StraightFrontierDetails.hrayzero x
      B q hq
  have hcover : E.left ∪ E.right = Metric.ball x r \ ray := by
    simpa only [ray] using E.cover
  have hleftball (q : Real × Real) (hq : q ∈ E.left) : q ∈ Metric.ball x r :=
      StraightFrontierDetails.hleftball x B r E hcover q hq
  have hrightball (q : Real × Real) (hq : q ∈ E.right) : q ∈ Metric.ball x r :=
      StraightFrontierDetails.hrightball x B r E hcover q hq
  have hleftnotray (q : Real × Real) (hq : q ∈ E.left) : q ∉ ray :=
      StraightFrontierDetails.hleftnotray x B r E hcover q hq
  have hrightnotray (q : Real × Real) (hq : q ∈ E.right) : q ∉ ray :=
      StraightFrontierDetails.hrightnotray x B r E hcover q hq
  have hDleft (q : Real × Real) (hq : q ∈ E.left) : D q ≠ 0 := StraightFrontierProof.hDleft x B r
      E hcol hleftball hleftnotray q hq
  have hDright (q : Real × Real) (hq : q ∈ E.right) : D q ≠ 0 := StraightFrontierProof.hDright x
      B r E hcol hrightball hrightnotray q hq
  let pos : Set (Real × Real) := {q | 0 < D q}
  let neg : Set (Real × Real) := {q | D q < 0}
  have hposOpen : IsOpen pos := by
    exact isOpen_Ioi.preimage hDcont
  have hnegOpen : IsOpen neg := by
    exact isOpen_Iio.preimage hDcont
  have hposnegDis : Disjoint pos neg := StraightFrontierDetails.hposnegDis x B
  have hleftSplit : E.left ⊆ pos ∪ neg := StraightFrontierDetails.hleftSplit x B r E hDleft
  have hrightSplit : E.right ⊆ pos ∪ neg := StraightFrontierDetails.hrightSplit x B r E hDright
  have hleftSign : E.left ⊆ pos ∨ E.left ⊆ neg := StraightFrontierDetails.hleftSign x B r E
      hposOpen hnegOpen hposnegDis hleftSplit
  have hrightSign : E.right ⊆ pos ∨ E.right ⊆ neg := StraightFrontierDetails.hrightSign x B r E
      hposOpen hnegOpen hposnegDis hrightSplit
  have hsq : 0 < d.1 ^ 2 + d.2 ^ 2 := StraightFrontierDetails.hsq B hdnz
  let j : Real × Real := (-d.2, d.1)
  have hjnorm : ‖j‖ = 1 := StraightFrontierDetails.hjnorm B hd
  let qpos : Real × Real := x + (r / 4) • j
  let qneg : Real × Real := x - (r / 4) • j
  have hqposball : qpos ∈ Metric.ball x r := StraightFrontierDetails.hqposball x B r hr hjnorm
  have hqnegball : qneg ∈ Metric.ball x r := StraightFrontierDetails.hqnegball x B r hr hjnorm
  have hDpos : 0 < D qpos := StraightFrontierDetails.hDpos x B r hr hsq
  have hDneg : D qneg < 0 := StraightFrontierDetails.hDneg x B r hr hsq
  have hqposCover : qpos ∈ E.left ∪ E.right := StraightFrontierDetails.hqposCover x B r E
      hrayzero hcover hqposball hDpos
  have hqnegCover : qneg ∈ E.left ∪ E.right := StraightFrontierDetails.hqnegCover x B r E
      hrayzero hcover hqnegball hDneg
  have hsectorSign :
      (E.left ⊆ pos ∧ E.right ⊆ neg) ∨
        (E.left ⊆ neg ∧ E.right ⊆ pos) := StraightFrontierProof.hsectorSign x B r E hleftSign
            hrightSign hDpos hDneg hqposCover hqnegCover
  have sectorEq (C D' : Set (Real × Real))
      (hCpos : C ⊆ pos) (hDneg : D' ⊆ neg)
      (hCball : C ⊆ Metric.ball x r)
      (hDball : D' ⊆ Metric.ball x r)
      (hCD : C ∪ D' = Metric.ball x r \ ray) :
      C = Metric.ball x r ∩ pos ∧
        D' = Metric.ball x r ∩ neg := StraightFrontierProof.sectorEq x B r hrayzero C D' hCpos
            hDneg hCball hDball hCD
  have hsectorEq :
      (E.left = Metric.ball x r ∩ pos ∧ E.right = Metric.ball x r ∩ neg) ∨
        (E.left = Metric.ball x r ∩ neg ∧ E.right = Metric.ball x r ∩ pos) :=
            StraightFrontierProof.hsectorEq x B r E hcover hleftball hrightball hsectorSign sectorEq
  have sidePos (W : Set (Real × Real))
      (hW : W ∩ Metric.ball x r = Metric.ball x r ∩ pos) :
      P3934T1LocalSide W x d true := StraightFrontierProof.sidePos x B r hr W hW
  have sideNeg (W : Set (Real × Real))
      (hW : W ∩ Metric.ball x r = Metric.ball x r ∩ neg) :
      P3934T1LocalSide W x d false := StraightFrontierProof.sideNeg x B r hr W hW
  have hlocal : ∃ e : Bool,
      P3934T1LocalSide U x d e ∧
      P3934T1LocalSide (closure U)ᶜ x d (!e) := StraightFrontierProof.hlocal U x B r E hselect
          hsectorEq sidePos sideNeg
  obtain ⟨e, hUside, hVside⟩ := hlocal
  refine ⟨e, ?_, ?_⟩
  · simpa only [hBdecomp] using scaleLocalSide U x d n e hn hUside
  · simpa only [hBdecomp] using scaleLocalSide (closure U)ᶜ x d n (!e) hn hVside

end ApollonianSuperharmonic

end
