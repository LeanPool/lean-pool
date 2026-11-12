/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.DiamondOdometer
public import LeanPool.ApollonianSuperharmonic.DiamondTileRecursiveIdentification
public import LeanPool.ApollonianSuperharmonic.TileOdometerAffineTranslation
public import LeanPool.ApollonianSuperharmonic.P4194T1DiamondVertexIncidence
public import LeanPool.ApollonianSuperharmonic.DiamondVertexDomains
public import LeanPool.ApollonianSuperharmonic.DiamondTileGeometry
public import LeanPool.ApollonianSuperharmonic.P4207T1UnitRestrictions
public import LeanPool.ApollonianSuperharmonic.P4207T1ShiftedPredecessor
public import LeanPool.ApollonianSuperharmonic.P4223T1DiamondRowNumerators

-- [TABLET NODE: DiamondTileOdometerRestriction]

/-!
# DiamondTileOdometerRestriction

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace DiamondRestrictionProof

private theorem geometry :
    (∀ (T : ProtoTile), ((P4207T1FormulaRestriction T).domain : Set GaussianInt) =
        FootprintVertices T) → (∀ K : DiamondParameter, FootprintVertices (DiamondTile K.1) =
        DiamondVertexDomains K false ∧ PartialOdometerSquares (P4207T1FormulaRestriction
        (DiamondTile K.1)) = DiamondCellDomain K.1) := by
  classical
  intro domain
  rintro ⟨k, hk⟩
  have footprint (x : GaussianInt) :
      x ∈ FootprintVertices (DiamondTile k) ↔
      0 ≤ x.im ∧ x.im ≤ 2 * (k : Int) ∧
      -(k : Int) ≤ x.re ∧ x.re ≤ (k : Int) ∧
      -x.im - 1 ≤ x.re ∧ x.re ≤ x.im + 1 ∧
      -(2 * (k : Int) - x.im + 1) ≤ x.re ∧
      x.re ≤ 2 * (k : Int) - x.im + 1 := by
    rw [(P4194T1DiamondVertexIncidence k hk x).1]
    have four : (∃ j : Fin 4, LatticeVertexIncidentCell x j ∈ DiamondCellDomain k) ↔
        x ∈ DiamondCellDomain k ∨ x - 1 ∈ DiamondCellDomain k ∨
        x - 1 - ⟨0, 1⟩ ∈ DiamondCellDomain k ∨
        x - ⟨0, 1⟩ ∈ DiamondCellDomain k := by
      simp only [Fin.exists_fin_succ, LatticeVertexIncidentCell]
      simp
    rw [four]
    simp only [(P4194T1DiamondCellRows _ _).1]
    norm_num
    omega
  have vertex : FootprintVertices (DiamondTile k) = DiamondVertexDomains ⟨k, hk⟩ false := by
    ext x
    rw [footprint]
    change _ ↔ max (Int.natAbs x.re)
      (max (Int.natAbs (x.im - (k : Int)))
        (Int.natAbs x.re + Int.natAbs (x.im - (k : Int)) - 1)) ≤ k
    simp only [max_le_iff]
    have h1 := Int.natCast_natAbs x.re
    have h2 := Int.natCast_natAbs (x.im - (k : Int))
    rcases le_total 0 x.re with ha | ha <;>
      rcases le_total 0 (x.im - (k : Int)) with hb | hb <;>
      simp only [abs_of_nonneg, abs_of_nonpos, ha, hb] at h1 h2 <;>
      omega
  refine ⟨vertex, ?_⟩
  ext x
  simp only [PartialOdometerSquares, Finset.mem_filter]
  have mem (y : GaussianInt) :
      y ∈ (P4207T1FormulaRestriction (DiamondTile k)).domain ↔
      y ∈ FootprintVertices (DiamondTile k) := by
    change y ∈ ((P4207T1FormulaRestriction (DiamondTile k)).domain : Set GaussianInt) ↔ _
    rw [domain]
  simp only [mem, footprint, (P4194T1DiamondCellRows _ _).1]
  norm_num
  omega

private theorem slope :
    (∀ (T : ProtoTile), ∀ (x : GaussianInt), (x ∈ (P4207T1FormulaRestriction T).domain) →
        ((P4207T1FormulaRestriction T).value x = P4207T1DiamondFormula x)) → ((∀ K :
        DiamondParameter, FootprintVertices (DiamondTile K.1) = DiamondVertexDomains K false ∧
        PartialOdometerSquares (P4207T1FormulaRestriction (DiamondTile K.1)) =
        DiamondCellDomain K.1) → (∀ (K : DiamondParameter), PartialOdometerSlope
        (P4207T1FormulaRestriction (DiamondTile K.1)) = some ((↑K.1 : ℝ) / (2 : ℝ), -((↑K.1 :
        ℝ) / (2 : ℝ))))) := by
  classical
  intro value geometry K
  let k := K.1
  let h := P4207T1FormulaRestriction (DiamondTile k)
  have squares : PartialOdometerSquares h = DiamondCellDomain k := (geometry K).2
  let r : Nat → Nat := fun y => min (y + 1) (2 * k - y)
  let row : Nat → Finset GaussianInt := fun y =>
    (Finset.range (2 * r y)).image fun j : Nat =>
      (⟨(j : Int) - (r y : Int), (y : Int)⟩ : GaussianInt)
  have hinj (y : Nat) : Function.Injective
      (fun j : Nat => (⟨(j : Int) - (r y : Int), (y : Int)⟩ : GaussianInt)) := by
    intro i j he
    have hre := congrArg Zsqrtd.re he
    simp only at hre
    omega
  have hdisj : (↑(Finset.range (2 * k)) : Set Nat).PairwiseDisjoint row := by
    intro y hy z hz hyz
    apply Finset.disjoint_left.mpr
    intro x hxy hxz
    obtain ⟨i, hi, hix⟩ := Finset.mem_image.mp hxy
    obtain ⟨j, hj, hjx⟩ := Finset.mem_image.mp hxz
    have him := congrArg Zsqrtd.im (hix.trans hjx.symm)
    simp only at him
    exact hyz (by omega)
  have by_rows (f : GaussianInt → Int) :
      (∑ x ∈ DiamondCellDomain k, f x) =
        ∑ y ∈ Finset.range (2 * k), ∑ j ∈ Finset.range (2 * r y),
          f ⟨(j : Int) - (r y : Int), (y : Int)⟩ := by
    change (∑ x ∈ (Finset.range (2 * k)).biUnion row, f x) = _
    rw [Finset.sum_biUnion hdisj]
    apply Finset.sum_congr rfl
    intro y hy
    exact Finset.sum_image (fun i hi j hj he => hinj y he)
  have hfirst (y : Nat) (hy : y < k) : r y = y + 1 := by
    dsimp [r]
    apply Nat.min_eq_left
    omega
  have hlast (y : Nat) (hy : y < k) : r (k + y) = k - y := by
    dsimp [r]
    rw [Nat.min_eq_right (by omega)]
    omega
  have triangle : ∀ n : Nat,
      (∑ y ∈ Finset.range n, 2 * ((y : Int) + 1)) =
        (n : Int) * ((n : Int) + 1) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring
  have height_sum :
      (∑ y ∈ Finset.range (2 * k), (r y : Int) * (2 * (y : Int) + 1)) =
        2 * (k : Int) * (k : Int) * ((k : Int) + 1) := by
    rw [show 2 * k = k + k by omega, Finset.sum_range_add]
    have first :
        (∑ y ∈ Finset.range k, (r y : Int) * (2 * (y : Int) + 1)) =
          ∑ y ∈ Finset.range k, ((y : Int) + 1) * (2 * (y : Int) + 1) := by
      apply Finset.sum_congr rfl
      intro y hy
      rw [hfirst y (Finset.mem_range.mp hy)]
      push_cast
      rfl
    have last :
        (∑ y ∈ Finset.range k, (r (k + y) : Int) * (2 * ((k + y : Nat) : Int) + 1)) =
          ∑ y ∈ Finset.range k, ((y : Int) + 1) *
            (4 * (k : Int) - 2 * (y : Int) - 1) := by
      rw [← Finset.sum_range_reflect
        (fun y => ((y : Int) + 1) * (4 * (k : Int) - 2 * (y : Int) - 1)) k]
      apply Finset.sum_congr rfl
      intro y hy
      have hyk := Finset.mem_range.mp hy
      rw [hlast y hyk]
      have he : ((k - y : Nat) : Int) = (k : Int) - y := by omega
      have he' : ((k - 1 - y : Nat) : Int) = (k : Int) - 1 - y := by omega
      simp only [Nat.cast_add, he, he']
      ring
    rw [first, last, ← Finset.sum_add_distrib]
    calc
      _ = ∑ y ∈ Finset.range k, (2 * (k : Int)) * (2 * ((y : Int) + 1)) := by
        apply Finset.sum_congr rfl
        intro y hy
        ring
      _ = _ := by rw [← Finset.mul_sum, triangle]; ring
  have count : ((DiamondCellDomain k).card : Int) =
      2 * (k : Int) * ((k : Int) + 1) := by
    have hc := (DiamondTileGeometry k K.2).2
    change (DiamondCellDomain k).card = 2 * k * (k + 1) at hc
    exact_mod_cast hc
  have nonempty : (DiamondCellDomain k).Nonempty := by
    apply Finset.card_pos.mp
    have hk := K.2
    have hc : 0 < ((DiamondCellDomain k).card : Int) := by
      rw [count]
      positivity
    exact_mod_cast hc
  have numerators (vertical : Bool) :
      (∑ x ∈ DiamondCellDomain k,
        if vertical then
          h.value (x + ⟨0, 1⟩) - h.value x +
            h.value (x + 1 + ⟨0, 1⟩) - h.value (x + 1)
        else
          h.value (x + 1) - h.value x +
            h.value (x + 1 + ⟨0, 1⟩) - h.value (x + ⟨0, 1⟩)) =
        (if vertical then -1 else 1) * (k : Int) * (DiamondCellDomain k).card := by
    have replace :
        (∑ x ∈ DiamondCellDomain k,
          if vertical then
            h.value (x + ⟨0, 1⟩) - h.value x +
              h.value (x + 1 + ⟨0, 1⟩) - h.value (x + 1)
          else
            h.value (x + 1) - h.value x +
              h.value (x + 1 + ⟨0, 1⟩) - h.value (x + ⟨0, 1⟩)) =
        ∑ x ∈ DiamondCellDomain k,
          if vertical then
            P4207T1DiamondFormula (x + ⟨0, 1⟩) - P4207T1DiamondFormula x +
              P4207T1DiamondFormula (x + 1 + ⟨0, 1⟩) -
                P4207T1DiamondFormula (x + 1)
          else
            P4207T1DiamondFormula (x + 1) - P4207T1DiamondFormula x +
              P4207T1DiamondFormula (x + 1 + ⟨0, 1⟩) -
                P4207T1DiamondFormula (x + ⟨0, 1⟩) := by
      apply Finset.sum_congr rfl
      intro x hx
      have hx' : x ∈ PartialOdometerSquares h := squares.symm ▸ hx
      obtain ⟨h0, h1, hi, h1i⟩ := Finset.mem_filter.mp hx'
      rw [value _ x h0, value _ _ h1, value _ _ hi, value _ _ h1i]
    rw [replace, by_rows]
    cases vertical
    · simp only [Bool.false_eq_true, ↓reduceIte, one_mul]
      calc
        _ = ∑ y ∈ Finset.range (2 * k), (r y : Int) * (2 * (y : Int) + 1) := by
          apply Finset.sum_congr rfl
          intro y hy
          exact (P4223T1DiamondRowNumerators (r y) (y : Int)).1
        _ = _ := by rw [height_sum, count]; ring
    · simp only [↓reduceIte]
      calc
        _ = ∑ y ∈ Finset.range (2 * k), -(r y : Int) * (2 * (y : Int) + 1) := by
          apply Finset.sum_congr rfl
          intro y hy
          exact (P4223T1DiamondRowNumerators (r y) (y : Int)).2
        _ = -(∑ y ∈ Finset.range (2 * k), (r y : Int) * (2 * (y : Int) + 1)) := by
          simp only [neg_mul, Finset.sum_neg_distrib]
        _ = _ := by rw [height_sum, count]; ring
  have horizontal := congrArg (fun z : Int => (z : Real)) (numerators false)
  have vertical := congrArg (fun z : Int => (z : Real)) (numerators true)
  norm_num only [Bool.false_eq_true, ↓reduceIte, one_mul] at horizontal vertical
  push_cast at horizontal vertical
  change PartialOdometerSlope h = _
  simp only [PartialOdometerSlope, squares, nonempty, ↓reduceIte]
  push_cast
  rw [horizontal, vertical]
  have hc : ((DiamondCellDomain k).card : Real) ≠ 0 := by
    exact_mod_cast (Finset.card_ne_zero.mpr nonempty)
  dsimp only [k] at hc
  congr 1
  ext <;> dsimp [k] <;> field_simp [hc]

private theorem certificates :
    (∀ (T : ProtoTile), ((P4207T1FormulaRestriction T).domain : Set GaussianInt) =
        FootprintVertices T) → ((∀ (T : ProtoTile), ∀ (x : GaussianInt), (x ∈
        (P4207T1FormulaRestriction T).domain) → ((P4207T1FormulaRestriction T).value x =
        P4207T1DiamondFormula x)) → ((∀ (K : DiamondParameter), PartialOdometerSlope
        (P4207T1FormulaRestriction (DiamondTile K.1)) = some (((K.1 : Real) / 2), -((K.1 :
        Real) / 2))) → ((∀ (z : GaussianInt), ∀ (x : GaussianInt), (OdometerTranslation
        (P4207T1FormulaRestriction ⟨{x}, x⟩) (CurvatureOneOdometer z)) → (TileOdometer (1, 1 +
        2 * z) ⟨{x}, x⟩ (P4207T1FormulaRestriction ⟨{x}, x⟩))) → (∀ n, ∀ (hn : 0 < n),
            TileOdometer (DiamondRecursiveQuadruple ⟨n, hn⟩ 0) (DiamondTile n)
        (P4207T1FormulaRestriction (DiamondTile n)))))) := by
  classical
  intro domain value slope unit n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    let K : DiamondParameter := ⟨n, hn⟩
    let q := DiamondRecursiveQuadruple K
    obtain ⟨_, hq, _, _, _, _, _, _, ha32, ha13, ha21⟩ :=
      DiamondCoordinateConfiguration K
    have arows (i : Fin 3) :
        BandVectors.2 (q (i + 2).succ) (q (i + 1).succ) =
          ![⟨1 - (n : Int), 0⟩, ⟨(n : Int) - 1, 1⟩, ⟨0, -1⟩] i := by
      fin_cases i
      · exact ha32
      · exact ha13
      · exact ha21
    obtain ⟨hT, S, hocc, hcells, e0t, e0f, e1t, e1f, e2f, e2t⟩ :=
      DiamondTileRecursiveIdentification K
    have units := P4207T1UnitRestrictions K
    have outerSlope := slope K
    have hprev : TileOdometer (q 3) (DiamondTile (n - 1))
        (P4207T1FormulaRestriction (DiamondTile (n - 1))) := by
      by_cases hp : 0 < n - 1
      · have hi := ih (n - 1) (by omega) hp
        have he : n - 1 + 1 = n := by omega
        have heI : ((n - 1 : Nat) : Int) + 1 = (n : Int) := by omega
        simpa [q, K, DiamondRecursiveQuadruple, he, heI] using hi
      · have he : n = 1 := by omega
        subst n
        convert TileOdometer.line (-1) 0 (Or.inr rfl)
          (P4207T1FormulaRestriction (DiamondTile 0)) (by
            simp [P4207T1FormulaRestriction, DiamondTile, DiamondCellDomain]) using 1 <;>
          simp [q, K, DiamondRecursiveQuadruple, DiamondTile, DiamondCellDomain,
            Zsqrtd.ext_iff]
    have hupper := TileOdometerAffineTranslation _ _ _ ⟨0, 2⟩ ⟨1, -1⟩ 1 hprev
    rw [← P4207T1ShiftedPredecessor] at hupper
    have hsub (i : Fin 3) (s : Bool) :
        TileOdometer (q i.succ) (S i s) (P4207T1FormulaRestriction (S i s)) := by
      fin_cases i <;> cases s
      · change TileOdometer (q 1) (S 0 false) (P4207T1FormulaRestriction (S 0 false))
        rw [e0f]
        convert unit ⟨0, 1⟩ ⟨(n : Int) - 1, (n : Int)⟩ (units 0 false).1 using 1;
          simp [q, K, DiamondRecursiveQuadruple, Zsqrtd.ext_iff]
      · change TileOdometer (q 1) (S 0 true) (P4207T1FormulaRestriction (S 0 true))
        rw [e0t]
        convert unit ⟨0, 1⟩ ⟨-(n : Int), (n : Int) - 1⟩ (units 0 true).1 using 1;
          simp [q, K, DiamondRecursiveQuadruple, Zsqrtd.ext_iff]
      · change TileOdometer (q 2) (S 1 false) (P4207T1FormulaRestriction (S 1 false))
        rw [e1f]
        simpa [q, K, DiamondRecursiveQuadruple] using
          unit 0 ⟨-(n : Int), (n : Int)⟩ (units 1 false).1
      · change TileOdometer (q 2) (S 1 true) (P4207T1FormulaRestriction (S 1 true))
        rw [e1t]
        simpa [q, K, DiamondRecursiveQuadruple] using
          unit 0 ⟨(n : Int) - 1, (n : Int) - 1⟩ (units 1 true).1
      · change TileOdometer (q 3) (S 2 false) (P4207T1FormulaRestriction (S 2 false))
        rw [e2f]
        exact hprev
      · change TileOdometer (q 3) (S 2 true) (P4207T1FormulaRestriction (S 2 true))
        rw [e2t]
        exact hupper
    have nonempty : (DiamondTile n).cells.Nonempty := by
      refine ⟨0, (P4194T1DiamondCellRows n 0).1.mpr ?_⟩
      norm_num
      omega
    have cover (x : GaussianInt) :
        x ∈ (P4207T1FormulaRestriction (DiamondTile n)).domain ↔
        ∃ i s, x ∈ (P4207T1FormulaRestriction (S i s)).domain := by
      have member (T : ProtoTile) (x : GaussianInt) :
          x ∈ (P4207T1FormulaRestriction T).domain ↔ x ∈ FootprintVertices T := by
        change x ∈ ((P4207T1FormulaRestriction T).domain : Set GaussianInt) ↔ _
        rw [domain]
      simp only [member]
      constructor
      · intro hx
        rw [FootprintVertices, ite_eq_left nonempty] at hx
        obtain ⟨a, ha, hx⟩ := hx
        obtain ⟨i, s, has⟩ := (hcells a).mp ha
        have hsne : (S i s).cells.Nonempty := ⟨a, has⟩
        refine ⟨i, s, ?_⟩
        rw [FootprintVertices, ite_eq_left hsne]
        exact ⟨a, has, hx⟩
      · rintro ⟨i, s, hx⟩
        exact (hocc i s).2.1 hx
    refine TileOdometer.decompose (q := q) (S := S)
      (hs := fun i s => P4207T1FormulaRestriction (S i s))
      (h := P4207T1FormulaRestriction (DiamondTile n)) hq hT hsub hcells
      (fun i s => (hocc i s).2.1) (fun i s => (hocc i s).2.2) cover ?_ ?_ ?_
    · intro i s x hx
      rw [value _ x ((cover x).mpr ⟨i, s, hx⟩), value _ x hx]
    · intro i s j t
      right
      refine ⟨0, ?_⟩
      intro x hx hy
      rw [value _ x hy, value _ x hx, sub_self]
    · intro i s
      rw [arows i]
      fin_cases i <;> cases s
      · refine Or.inr ⟨_, ((n : Real) - 1 / 2, -1 / 2), outerSlope, ?_, ?_, ?_⟩
        · change PartialOdometerSlope (P4207T1FormulaRestriction (S 0 false)) = _
          rw [e0f]; exact (units 0 false).2
        all_goals norm_num [K]; ring
      · refine Or.inr ⟨_, (1 / 2, 1 / 2 - (n : Real)), outerSlope, ?_, ?_, ?_⟩
        · change PartialOdometerSlope (P4207T1FormulaRestriction (S 0 true)) = _
          rw [e0t]; exact (units 0 true).2
        all_goals norm_num [K]; ring
      · refine Or.inr ⟨_, (1, -(n : Real)), outerSlope, ?_, ?_, ?_⟩
        · change PartialOdometerSlope (P4207T1FormulaRestriction (S 1 false)) = _
          rw [e1f]; exact (units 1 false).2
        all_goals norm_num [K]; ring
      · refine Or.inr ⟨_, ((n : Real) - 1, 0), outerSlope, ?_, ?_, ?_⟩
        · change PartialOdometerSlope (P4207T1FormulaRestriction (S 1 true)) = _
          rw [e1t]; exact (units 1 true).2
        all_goals norm_num [K]; ring
      · by_cases hp : 0 < n - 1
        · have hs := slope ⟨n - 1, hp⟩
          refine Or.inr ⟨_, (((n - 1 : Nat) : Real) / 2,
            -(((n - 1 : Nat) : Real) / 2)), outerSlope, ?_, ?_, ?_⟩
          · change PartialOdometerSlope (P4207T1FormulaRestriction (S 2 false)) = _
            rw [e2f]; exact hs
          all_goals
            norm_num [K]
            rw [Nat.cast_sub (by omega : 1 ≤ n)]
            push_cast
            ring
        · left
          have he : n = 1 := by omega
          simp [q, K, DiamondRecursiveQuadruple, he]
      · by_cases hp : 0 < n - 1
        · have hs := (PartialOdometerAffineTranslateFormulas
              (P4207T1FormulaRestriction (DiamondTile (n - 1)))
              ⟨0, 2⟩ ⟨1, -1⟩ 1).2.2.2.2.2
          rw [slope ⟨n - 1, hp⟩] at hs
          refine Or.inr ⟨_, ((((n - 1 : Nat) : Real) / 2 + 1),
            -(((n - 1 : Nat) : Real) / 2) - 1), outerSlope, ?_, ?_, ?_⟩
          · change PartialOdometerSlope (P4207T1FormulaRestriction (S 2 true)) = _
            rw [e2t, P4207T1ShiftedPredecessor]
            simpa [K, sub_eq_add_neg] using hs
          all_goals
            norm_num [K]
            rw [Nat.cast_sub (by omega : 1 ≤ n)]
            push_cast
            ring
        · left
          have he : n = 1 := by omega
          simp [q, K, DiamondRecursiveQuadruple, he]

end DiamondRestrictionProof

theorem DiamondTileOdometerRestriction (K : DiamondParameter) :
    ∃ h : PartialOdometer,
      TileOdometer ((DiamondRecursiveQuadruple K) 0)
          (DiamondTile K.1) h /\
      (h.domain : Set GaussianInt) = DiamondVertexDomains K false /\
      FootprintVertices (DiamondTile K.1) =
        DiamondVertexDomains K false /\
      PartialOdometerSquares h = DiamondCellDomain K.1 /\
      (∀ x, x ∈ h.domain → h.value x = DiamondOdometer K x) /\
      PartialOdometerSlope h =
        some (((K.1 : Real) / 2), -((K.1 : Real) / 2)) := by
-- BODY
  classical
  have domain (T : ProtoTile) :
      ((P4207T1FormulaRestriction T).domain : Set GaussianInt) = FootprintVertices T :=
    by
      ext x
      by_cases h : T.cells.Nonempty <;>
        simp [P4207T1FormulaRestriction, FootprintVertices, h]
  have value (T : ProtoTile) (x : GaussianInt)
      (hx : x ∈ (P4207T1FormulaRestriction T).domain) :
      (P4207T1FormulaRestriction T).value x = P4207T1DiamondFormula x :=
    by
      change (if x ∈ (P4207T1FormulaRestriction T).domain then _ else 0) = _
      exact ite_eq_left hx
  have geometry : ∀ K : DiamondParameter,
      FootprintVertices (DiamondTile K.1) = DiamondVertexDomains K false ∧
      PartialOdometerSquares (P4207T1FormulaRestriction (DiamondTile K.1)) =
        DiamondCellDomain K.1 := DiamondRestrictionProof.geometry domain
  have slope (K : DiamondParameter) :
      PartialOdometerSlope (P4207T1FormulaRestriction (DiamondTile K.1)) =
        some (((K.1 : Real) / 2), -((K.1 : Real) / 2)) := DiamondRestrictionProof.slope value
            geometry K
  have unit (z x : GaussianInt)
      (ht : OdometerTranslation (P4207T1FormulaRestriction ⟨{x}, x⟩)
        (CurvatureOneOdometer z)) :
      TileOdometer (1, 1 + 2 * z) ⟨{x}, x⟩
        (P4207T1FormulaRestriction ⟨{x}, x⟩) :=
    TileOdometer.unit z x _ _ rfl (domain _) ht
  have certificates : ∀ n (hn : 0 < n),
      TileOdometer (DiamondRecursiveQuadruple ⟨n, hn⟩ 0) (DiamondTile n)
        (P4207T1FormulaRestriction (DiamondTile n)) := DiamondRestrictionProof.certificates
            domain value slope unit
  refine ⟨P4207T1FormulaRestriction (DiamondTile K.1), certificates K.1 K.2,
    (domain _).trans (geometry K).1,
    (geometry K).1,
    (geometry K).2, ?_, slope K⟩
  intro x hx
  rw [value _ x hx]
  have hdom : x ∈ DiamondVertexDomains K false := by
    rw [← (geometry K).1, ← domain]
    exact hx
  exact ((Classical.choose_spec (DiamondOdometerExistsUnique K)).1.2.2.2 x hdom).symm

end ApollonianSuperharmonic

end
