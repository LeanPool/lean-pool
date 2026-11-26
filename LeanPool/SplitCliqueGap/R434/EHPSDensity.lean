/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
/- Modified by Lean Pool contributors for the current Lean and Mathlib toolchain. -/
module

public import LeanPool.SplitCliqueGap.R434.EHPSHostTransfer
public import Mathlib.Data.Int.Interval
public import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.WLOG
import Mathlib.Algebra.BigOperators.Fin

/-! A lattice count of the seven vertical strips of the EHPS region. -/

@[expose] public section

open Finset
open scoped BigOperators

namespace GapExtremal.R434.EHPS

/-- The width multiplier of a strip in the explicit density construction. -/
def stripWidth (i : Fin 7) : ℕ :=
  match i.val with | 0 => 2 | 1 => 4 | 2 => 3 | _ => 1

/-- The horizontal start of a strip, in units of the scaling parameter. -/
def stripStart (i : Fin 7) : ℤ :=
  match i.val with | 0 => 6 | 1 => 8 | 2 => 8 | 3 => 11 | 4 => 3 | 5 => 4 | _ => 5

/-- The inclusive lower vertical boundary at horizontal index `k`. -/
def stripBottom (q k : ℤ) (i : Fin 7) : ℤ :=
  match i.val with
  | 0 => 2 * q-k | 1 => 0 | 2 => 6 * q-k | 3 => 3 * q-k
  | 4 => 12 * q-2 * k | 5 => 10 * q-k | _ => 9 * q-k

/-- The exclusive upper vertical boundary at horizontal index `k`. -/
def stripTop (q k : ℤ) (i : Fin 7) : ℤ :=
  match i.val with
  | 0 => 8 * q-k | 1 => 6 * q-k | 2 => 6 * q | 3 => 6 * q-k
  | 4 => 12 * q | 5 => 12 * q | _ => 12 * q-k

/-- Integer grid points at one horizontal coordinate of a strip. -/
def stripRow (q d : ℕ) (i : Fin 7) (j : ℕ) : Finset (ℤ × ℤ) :=
  {stripStart i * (q : ℤ) + (j : ℤ) + d} ×ˢ
    Ico (stripBottom q ((j : ℤ) + d) i + d) (stripTop q ((j : ℤ) + d) i - d)

/-- Integer grid points in one strip of the density construction. -/
def stripSet (q d p : ℕ) (i : Fin 7) : Finset (ℤ × ℤ) :=
  (range (stripWidth i * p)).biUnion (stripRow q d i)

/-- The union of the seven strips used to bound the grid density from below. -/
def densitySet (q d p : ℕ) : Finset (ℤ × ℤ) :=
  univ.biUnion (stripSet q d p)

theorem strip_row_bounds {q d p j : ℕ} {i : Fin 7} {z : ℤ × ℤ}
    (hq : p + 2 * d ≤ q) (hj : j ∈ range (stripWidth i * p)) (hz : z ∈ stripRow q d i j) :
    let k := (j : ℤ) + d
    (d : ℤ) ≤ k ∧ k + d < (stripWidth i : ℤ) * (q : ℤ) ∧
      z.1 = stripStart i * (q : ℤ) + k ∧
      stripBottom q k i + d ≤ z.2 ∧ z.2 < stripTop q k i - d := by
  have hq' : (p : ℤ) + 2 * (d : ℤ) ≤ q := by exact_mod_cast hq
  have hj' : (j : ℤ) < (stripWidth i : ℤ) * (p : ℤ) := by exact_mod_cast (mem_range.mp hj)
  simp only [stripRow, mem_product, mem_singleton, mem_Ico] at hz
  have hd : 0 ≤ (d : ℤ) := by positivity
  have hj₀ : 0 ≤ (j : ℤ) := by positivity
  have hhi : (j : ℤ) + d + d < (stripWidth i : ℤ) * (q : ℤ) := by
    fin_cases i <;> norm_num [stripWidth] at hj' ⊢ <;> omega
  exact ⟨by omega, hhi, by linarith only [hz.1], hz.2.1, hz.2.2⟩

theorem strip_coordinates {q d p m : ℕ} (hq : p + 2 * d ≤ q)
    (hm₁ : 12 * q ≤ m) (hm₂ : m ≤ 12 * q + 11) (hd : 20 ≤ d)
    {i : Fin 7} {z : ℤ × ℤ} (hz : z ∈ stripSet q d p i) :
    0 ≤ z.1 ∧ z.1 < m ∧ 0 ≤ z.2 ∧ z.2 < m ∧
    ((i.val ≤ 1 ∧ (m : ℤ) ≤ 2 * z.1 ∧ 2 * (m : ℤ) < 3 * (z.1 + z.2) ∧
        6 * (z.1 + z.2) ≤ 7 * (m : ℤ)) ∨
     (2 ≤ i.val ∧ i.val ≤ 3 ∧ (m : ℤ) ≤ 2 * z.1 ∧ 2 * z.2 < m ∧
        7 * (12 * (q : ℤ))/6 + d ≤ z.1 + z.2 ∧ 12 * (z.1 + z.2) ≤ 17 * (m : ℤ)) ∨
     (4 ≤ i.val ∧ 2 * z.1 < m ∧ (m : ℤ) ≤ 2 * z.2 ∧
        14 * (q : ℤ) + d ≤ z.1 + z.2 ∧ 12 * (z.1 + z.2) ≤ 17 * (m : ℤ) ∧
        18 * (q : ℤ) + d ≤ 2 * z.1 + z.2)) := by
  obtain ⟨j,hj,hz⟩ := mem_biUnion.mp hz
  obtain ⟨hk₀,hk₁,hx,hy₀,hy₁⟩ := strip_row_bounds hq hj hz
  have hmL : 12 * (q : ℤ) ≤ m := by exact_mod_cast hm₁
  have hmU : (m : ℤ) ≤ 12 * (q : ℤ) + 11 := by exact_mod_cast hm₂
  have hd' : (20 : ℤ) ≤ d := by exact_mod_cast hd
  have hq' : 0 ≤ (q : ℤ) := by positivity
  fin_cases i <;>
    norm_num [stripWidth, stripStart, stripBottom, stripTop] at hk₁ hx hy₀ hy₁
  · refine ⟨by omega,by omega,by omega,by omega, .inl ⟨by decide,by omega,by omega,by omega⟩⟩
  · refine ⟨by omega,by omega,by omega,by omega, .inl ⟨by decide,by omega,by omega,by omega⟩⟩
  · refine ⟨by omega,by omega,by omega,by omega, .inr (.inl
      ⟨by decide,by decide,by omega,by omega,by omega,by omega⟩)⟩
  · refine ⟨by omega,by omega,by omega,by omega, .inr (.inl
      ⟨by decide,by decide,by omega,by omega,by omega,by omega⟩)⟩
  · refine ⟨by omega,by omega,by omega,by omega, .inr (.inr
      ⟨by decide,by omega,by omega,by omega,by omega,by omega⟩)⟩
  · refine ⟨by omega,by omega,by omega,by omega, .inr (.inr
      ⟨by decide,by omega,by omega,by omega,by omega,by omega⟩)⟩
  · refine ⟨by omega,by omega,by omega,by omega, .inr (.inr
      ⟨by decide,by omega,by omega,by omega,by omega,by omega⟩)⟩

theorem densitySet_in_region {q d p m : ℕ} [NeZero m] {ε : ℝ}
    (hq : p + 2 * d ≤ q) (hm₁ : 12 * q ≤ m) (hm₂ : m ≤ 12 * q + 11) (hd : 20 ≤ d)
    (hε : ε * (m : ℝ) + 20 ≤ d) {z : ℤ × ℤ} (hz : z ∈ densitySet q d p) :
    ((z.1 : ZMod m), (z.2 : ZMod m)) ∈ gridSupport ε m := by
  obtain ⟨i,_,hi⟩ := mem_biUnion.mp hz
  obtain ⟨hx₀,hxU,hy₀,hyU,hcases⟩ := strip_coordinates hq hm₁ hm₂ hd hi
  have hmpos : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  have hval (a : ℤ) (ha : 0 ≤ a) (hU : a < (m : ℤ)) :
      (((a : ZMod m).val : ℕ) : ℝ) = (a : ℝ) := by
    have hn : ((a.toNat : ℕ) : ℤ) = a := Int.toNat_of_nonneg ha
    have hlt : a.toNat < m := by exact_mod_cast (show (a.toNat : ℤ) < m by rw [hn]; exact hU)
    have he : (a : ZMod m) = (a.toNat : ZMod m) := by
      simpa only [Int.cast_natCast] using (congrArg (fun t : ℤ => (t : ZMod m)) hn).symm
    rw [he, ZMod.val_natCast_of_lt hlt]
    exact_mod_cast hn
  apply mem_gridSupport.mpr
  simp only [gridPoint, hval _ hx₀ hxU, hval _ hy₀ hyU]
  have hx₀' : (0 : ℝ) ≤ (z.1 : ℝ) := by exact_mod_cast hx₀
  have hxU' : (z.1 : ℝ) < (m : ℝ) := by exact_mod_cast hxU
  have hy₀' : (0 : ℝ) ≤ (z.2 : ℝ) := by exact_mod_cast hy₀
  have hyU' : (z.2 : ℝ) < (m : ℝ) := by exact_mod_cast hyU
  refine ⟨div_nonneg hx₀' hmpos.le, (div_lt_one₀ hmpos).mpr hxU',
    div_nonneg hy₀' hmpos.le, (div_lt_one₀ hmpos).mpr hyU', ?_⟩
  have hmU : (m : ℝ) ≤ 12 * (q : ℝ) + 11 := by exact_mod_cast hm₂
  simp only [total, ← add_div]
  rcases hcases with ⟨_,hx,hl,hu⟩ | ⟨_,_,hx,hy,hl,hu⟩ | ⟨_,hx,hy,hl,hu,hdbl⟩
  · have hx' : (m : ℝ) ≤ 2 * (z.1 : ℝ) := by exact_mod_cast hx
    have hl' : 2 * (m : ℝ) < 3 * ((z.1 : ℝ) + (z.2 : ℝ)) := by exact_mod_cast hl
    have hu' : 6 * ((z.1 : ℝ) + (z.2 : ℝ)) ≤ 7 * (m : ℝ) := by exact_mod_cast hu
    exact .inl ⟨(le_div_iff₀ hmpos).mpr (by linarith), (lt_div_iff₀ hmpos).mpr (by linarith),
      (div_le_iff₀ hmpos).mpr (by linarith)⟩
  · have hx' : (m : ℝ) ≤ 2 * (z.1 : ℝ) := by exact_mod_cast hx
    have hy' : 2 * (z.2 : ℝ) < (m : ℝ) := by exact_mod_cast hy
    have hlN : 14 * (q : ℤ) + d ≤ z.1 + z.2 := by omega
    have hl' : 14 * (q : ℝ) + d ≤ (z.1 : ℝ) + (z.2 : ℝ) := by exact_mod_cast hlN
    have hu' : 12 * ((z.1 : ℝ) + (z.2 : ℝ)) ≤ 17 * (m : ℝ) := by exact_mod_cast hu
    refine .inr (.inl ⟨(le_div_iff₀ hmpos).mpr (by linarith), (div_lt_iff₀ hmpos).mpr (by linarith),
      (le_div_iff₀ hmpos).mpr ?_, (div_le_iff₀ hmpos).mpr (by linarith)⟩)
    linarith only [hl',hε,hmU]
  · have hx' : 2 * (z.1 : ℝ) < (m : ℝ) := by exact_mod_cast hx
    have hy' : (m : ℝ) ≤ 2 * (z.2 : ℝ) := by exact_mod_cast hy
    have hl' : 14 * (q : ℝ) + d ≤ (z.1 : ℝ) + (z.2 : ℝ) := by exact_mod_cast hl
    have hu' : 12 * ((z.1 : ℝ) + (z.2 : ℝ)) ≤ 17 * (m : ℝ) := by exact_mod_cast hu
    have hd' : 18 * (q : ℝ) + d ≤ 2 * (z.1 : ℝ) + (z.2 : ℝ) := by exact_mod_cast hdbl
    refine .inr (.inr ⟨(div_lt_iff₀ hmpos).mpr (by linarith), (le_div_iff₀ hmpos).mpr (by linarith),
      (le_div_iff₀ hmpos).mpr (by linarith only [hl',hε,hmU]), (div_le_iff₀ hmpos).mpr (by
        linarith), ?_⟩)
    rw [← mul_div_assoc, ← add_div]
    apply (le_div_iff₀ hmpos).mpr
    linarith only [hd',hε,hmU]

theorem stripSets_disjoint {q d p : ℕ} (hq : p + 2 * d ≤ q) :
    ((univ : Finset (Fin 7)) : Set (Fin 7)).PairwiseDisjoint (stripSet q d p) := by
  intro i hi i' hi' hne
  wlog horder : i < i' generalizing i i'
  · exact (this hi' hi hne.symm (lt_of_le_of_ne (le_of_not_gt horder) hne.symm)).symm
  change Disjoint (stripSet q d p i) (stripSet q d p i')
  rw [disjoint_left]
  intro z hz hz'
  obtain ⟨j,hj,hr⟩ := mem_biUnion.mp hz
  obtain ⟨j',hj',hr'⟩ := mem_biUnion.mp hz'
  obtain ⟨h₀,h₁,hx,hy₀,hy₁⟩ := strip_row_bounds hq hj hr
  obtain ⟨h₀',h₁',hx',hy₀',hy₁'⟩ := strip_row_bounds hq hj' hr'
  have hd : 0 ≤ (d : ℤ) := by positivity
  have hq₀ : 0 ≤ (q : ℤ) := by positivity
  fin_cases i <;> fin_cases i' <;> norm_num [Fin.lt_def] at horder
  all_goals
    norm_num [stripWidth, stripStart] at h₁ h₁' hx hx'
    first
    | omega
    | norm_num [stripBottom, stripTop] at hy₀ hy₁ hy₀' hy₁'
      omega

/-- The initial height multiplier of each strip. -/
def baseHeight (i : Fin 7) : ℤ :=
  match i.val with | 0 => 6 | 1 => 6 | 2 => 0 | 3 => 3 | 4 => 0 | 5 => 2 | _ => 3

/-- The change in ideal strip height per unit horizontal displacement. -/
def heightSlope (i : Fin 7) : ℤ :=
  match i.val with | 1 => -1 | 2 => 1 | 4 => 2 | 5 => 1 | _ => 0

/-- The affine height of a strip before rounding the boundary. -/
def idealHeight (p j : ℕ) (i : Fin 7) : ℤ :=
  baseHeight i * (p : ℤ) + heightSlope i * (j : ℤ)

theorem stripRow_card_lower {q d p j : ℕ} (hq : p + 2 * d ≤ q) (i : Fin 7) :
    idealHeight p j i - 2 * (d : ℤ) ≤ ((stripRow q d i j).card : ℤ) := by
  have hq' : (p : ℤ) + 2 * (d : ℤ) ≤ q := by exact_mod_cast hq
  have hd' : 0 ≤ (d : ℤ) := by positivity
  simp only [stripRow, card_product, card_singleton, one_mul, Int.card_Ico]
  fin_cases i <;> norm_num [idealHeight, stripBottom, stripTop, baseHeight, heightSlope] <;> omega

theorem stripRows_disjoint (q d p : ℕ) (i : Fin 7) :
    ((range (stripWidth i * p) : Finset ℕ) : Set ℕ).PairwiseDisjoint (stripRow q d i) := by
  intro j _ j' _ hne
  change Disjoint (stripRow q d i j) (stripRow q d i j')
  rw [disjoint_left]
  intro z h h'
  simp only [stripRow, mem_product, mem_singleton] at h h'
  apply hne
  omega

theorem sum_range_int_twice (n : ℕ) :
    2 * ∑ j ∈ range n, (j : ℤ) = (n : ℤ) * ((n : ℤ) - 1) := by
  cases n with
  | zero => simp
  | succ n =>
    have h := sum_range_id_mul_two (n + 1)
    simp only [Nat.add_sub_cancel] at h
    have h' := congrArg (fun t : ℕ => (t : ℤ)) h
    push_cast at h'
    calc
      _ = (∑ j ∈ range (n + 1), (j : ℤ)) * 2 := by rw [mul_comm]
      _ = _ := by simpa using h'

theorem sum_idealHeight (p : ℕ) :
    ∑ i : Fin 7, ∑ j ∈ range (stripWidth i * p), idealHeight p j i =
      42 * (p : ℤ)^2 - (p : ℤ) := by
  simp only [idealHeight, sum_add_distrib, ← Finset.mul_sum, sum_const, card_range, nsmul_eq_mul]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Nat.cast_mul]
  have h₁ := sum_range_int_twice p
  have h₃ := sum_range_int_twice (3 * p)
  have h₄ := sum_range_int_twice (4 * p)
  push_cast at h₃ h₄
  norm_num [stripWidth, baseHeight, heightSlope, Fin.succ] at ⊢
  nlinarith only [h₁,h₃,h₄]

theorem densitySet_card_lower {q d p : ℕ} (hq : p + 2 * d ≤ q) :
    42 * (p : ℤ)^2 - (p : ℤ) - 26 * (d : ℤ) * (p : ℤ) ≤ ((densitySet q d p).card : ℤ) := by
  have hsum (i : Fin 7) : (∑ j ∈ range (stripWidth i * p), (idealHeight p j i - 2 * (d : ℤ))) ≤
      ((stripSet q d p i).card : ℤ) := by
    rw [stripSet, card_biUnion (stripRows_disjoint q d p i)]
    push_cast
    exact sum_le_sum fun j _ => stripRow_card_lower hq i
  have hl := sum_le_sum (s := (univ : Finset (Fin 7))) (fun i _ => hsum i)
  rw [densitySet, card_biUnion (stripSets_disjoint hq)]
  push_cast
  simp only [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul, Nat.cast_mul] at hl
  rw [sum_idealHeight] at hl
  have hconst : (∑ i : Fin 7, (stripWidth i : ℤ) * (p : ℤ) * (2 * (d : ℤ))) =
      26 * (d : ℤ) * (p : ℤ) := by
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
    (norm_num [stripWidth, Fin.succ]; ring)
  rw [hconst] at hl
  exact hl

theorem density_grid_lower {q d p m : ℕ} [NeZero m] {ε : ℝ}
    (hq : p + 2 * d ≤ q) (hm₁ : 12 * q ≤ m) (hm₂ : m ≤ 12 * q + 11) (hd : 20 ≤ d)
    (hε : ε * (m : ℝ) + 20 ≤ d) :
    42 * (p : ℤ)^2 - (p : ℤ) - 26 * (d : ℤ) * (p : ℤ) ≤ ((gridSupport ε m).card : ℤ) := by
  classical
  let f (z : ℤ × ℤ) : Grid m := ((z.1 : ZMod m), (z.2 : ZMod m))
  let S := densitySet q d p
  have hcoord {z : ℤ × ℤ} (hz : z ∈ S) : 0 ≤ z.1 ∧ z.1 < m ∧ 0 ≤ z.2 ∧ z.2 < m := by
    obtain ⟨i,_,hi⟩ := mem_biUnion.mp hz
    obtain ⟨hx,hx',hy,hy',_⟩ := strip_coordinates hq hm₁ hm₂ hd hi
    exact ⟨hx,hx',hy,hy'⟩
  have hinj : Set.InjOn f S := by
    intro a ha b hb hab
    obtain ⟨h₁,h₁',h₂,h₂'⟩ := hcoord ha
    obtain ⟨h₃,h₃',h₄,h₄'⟩ := hcoord hb
    have recInt (x : ℤ) (hx : 0 ≤ x) (hx' : x < (m : ℤ)) : ((x : ZMod m).val : ℤ) = x := by
      have h := Int.toNat_of_nonneg hx
      have hN : x.toNat < m := by exact_mod_cast (show (x.toNat : ℤ) < m by rw [h]; exact hx')
      have he : (x : ZMod m) = (x.toNat : ZMod m) := by
        simpa only [Int.cast_natCast] using (congrArg (fun t : ℤ => (t : ZMod m)) h).symm
      rw [he, ZMod.val_natCast_of_lt hN, h]
    apply Prod.ext
    · have he : (a.1 : ZMod m) = (b.1 : ZMod m) := congrArg Prod.fst hab
      rw [← recInt a.1 h₁ h₁', ← recInt b.1 h₃ h₃', he]
    · have he : (a.2 : ZMod m) = (b.2 : ZMod m) := congrArg Prod.snd hab
      rw [← recInt a.2 h₂ h₂', ← recInt b.2 h₄ h₄', he]
  have hsub : S.image f ⊆ gridSupport ε m := by
    intro z hz
    obtain ⟨a,ha,rfl⟩ := mem_image.mp hz
    exact densitySet_in_region hq hm₁ hm₂ hd hε ha
  have hcard := card_le_card hsub
  rw [card_image_of_injOn hinj] at hcard
  exact (densitySet_card_lower hq).trans (by exact_mod_cast hcard)

end GapExtremal.R434.EHPS
