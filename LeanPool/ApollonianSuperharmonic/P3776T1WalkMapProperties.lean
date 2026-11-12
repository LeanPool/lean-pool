/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P3776T1WalkMap
public import LeanPool.ApollonianSuperharmonic.FootprintEdges
public import LeanPool.ApollonianSuperharmonic.FootprintVertices
public import LeanPool.ApollonianSuperharmonic.LatticeTile
public import Mathlib.Tactic.Module
public import Mathlib.Data.List.GetD
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Topology.Algebra.Ring.Real

-- [TABLET NODE: P3776T1WalkMapProperties]

/-!
# P3776T1WalkMapProperties

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace WalkMapLemmas

private theorem hsingle :
    ∀ (a : GaussianInt), Continuous (P3776T1WalkMap [a]) := by
  classical
  intro a
  have heq : P3776T1WalkMap [a] =
      (fun _ : Set.Icc (0 : Real) 1 => GaussianRealPoint a) := by
    funext t
    simp [P3776T1WalkMap]
  rw [heq]
  exact continuous_const

private theorem hseg :
    ∀ (q : List GaussianInt), ∀ (k : Nat), (k < q.length - 1) → ∀ (t : Set.Icc (0 : Real) 1), ((k
        : Real) / (q.length - 1) ≤ (t : Real)) → ((t : Real) ≤ ((k + 1 : Nat) : Real) / (q.length
        - 1)) → P3776T1WalkMap q t =
        (1 - ((q.length - 1 : Nat) * (t : Real) - k)) •
            GaussianRealPoint (q.getD k 0) +
          ((q.length - 1 : Nat) * (t : Real) - k) •
            GaussianRealPoint (q.getD (k + 1) 0) := by
  classical
  intro q k hk t ht1 ht2
  have hn : 0 < q.length - 1 := by omega
  have hncast : ((q.length - 1 : Nat) : Real) = (q.length : Real) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ q.length)]
    simp
  have hden : (0 : Real) < (q.length : Real) - 1 := by
    rw [← hncast]
    exact_mod_cast hn
  have s1 : (k : Real) ≤ (q.length - 1 : Nat) * (t : Real) := by
    have ht := ht1
    rw [div_le_iff₀ hden] at ht
    rw [hncast]
    nlinarith [mul_comm (↑(q.length - 1 : Nat) : Real) (t : Real)]
  have s2 : (q.length - 1 : Nat) * (t : Real) ≤ (k + 1 : Nat) := by
    have ht := ht2
    rw [le_div_iff₀ hden] at ht
    rw [hncast]
    nlinarith [mul_comm (↑(q.length - 1 : Nat) : Real) (t : Real)]
  have hjlo : k ≤ ⌊(q.length - 1 : Nat) * (t : Real)⌋₊ := Nat.le_floor s1
  have hjhi : ⌊(q.length - 1 : Nat) * (t : Real)⌋₊ ≤ k + 1 :=
    Nat.floor_le_of_le s2
  unfold P3776T1WalkMap
  simp only [ite_eq_right (by omega : q.length - 1 ≠ 0)]
  by_cases hj : ⌊(↑(q.length - 1 : Nat) * (t : Real))⌋₊ = k
  · rw [hj]
    simp only [min_eq_left (by omega : k ≤ q.length - 1 - 1)]
  · have hj' : ⌊(↑(q.length - 1 : Nat) * (t : Real))⌋₊ = k + 1 := by omega
    rw [hj']
    have hsEq : (↑(q.length - 1 : Nat) * (t : Real)) = (k + 1 : Nat) := by
      have hfloor : (⌊(↑(q.length - 1 : Nat) * (t : Real))⌋₊ : Real) ≤
          ↑(q.length - 1 : Nat) * (t : Real) :=
        Nat.floor_le (by nlinarith [t.2.1])
      apply le_antisymm
      · exact s2
      · simpa [hj'] using hfloor
    by_cases hlast : k + 1 = q.length - 1
    · have hminlast : min (k + 1) (q.length - 1 - 1) = k := by omega
      rw [hminlast, hsEq]
    · have hmin : min (k + 1) (q.length - 1 - 1) = k + 1 := by
        apply min_eq_left
        omega
      rw [hmin, hsEq]; norm_num [Nat.cast_add]

private theorem hlastD :
    ∀ (p : List GaussianInt), (p ≠ []) → p.getLast?.getD 0 = p.getD (p.length - 1) 0 := by
  classical
  intro p hp
  induction p using List.reverseRecOn with
  | nil => simp
  | append_singleton q a ih => simp [List.getLast?_append]

private theorem hinterval :
    ∀ (p : List GaussianInt), (0 < p.length - 1) → ∀ (t : Set.Icc (0 : Real) 1), ∃ k, k <
        p.length - 1 ∧
        (k : Real) / (p.length - 1) ≤ (t : Real) ∧
        (t : Real) ≤ ((k + 1 : Nat) : Real) / (p.length - 1) := by
  classical
  intro p hn t
  let n := p.length - 1
  let s : Real := (n : Real) * (t : Real)
  let j := Nat.floor s
  have hnR : (0 : Real) < n := by exact_mod_cast hn
  have hncast : (n : Real) = (p.length : Real) - 1 := by
    dsimp [n]
    rw [Nat.cast_sub (by omega : 1 ≤ p.length)]
    simp
  have hden : (0 : Real) < (p.length : Real) - 1 := by rw [← hncast]; exact hnR
  have hslo : (j : Real) ≤ s := Nat.floor_le (by
    dsimp [s]
    nlinarith [t.2.1])
  have hshi : s < (j : Real) + 1 := by
    dsimp [j, s]
    exact Nat.lt_floor_add_one _
  have hsn : s ≤ n := by
    dsimp [s]
    nlinarith [t.2.2]
  have hjle : j ≤ n := by exact_mod_cast (hslo.trans hsn)
  by_cases hjn : j = n
  · let k := n - 1
    have hk : k < n := by dsimp [k]; omega
    have hklo : (k : Real) ≤ s := by
      dsimp [k]
      rw [hjn] at hslo
      have hkn : ((n - 1 : Nat) : Real) ≤ n := by exact_mod_cast (Nat.sub_le n 1)
      exact hkn.trans hslo
    have hleft : (k : Real) / ((p.length : Real) - 1) ≤ (t : Real) := by
      rw [div_le_iff₀ hden]
      dsimp [s] at hklo
      rw [← hncast]
      nlinarith [hklo, mul_comm (↑n) (t : Real)]
    have hright : (t : Real) ≤ ((k + 1 : Nat) : Real) / ((p.length : Real) - 1) := by
      rw [le_div_iff₀ hden]
      rw [← hncast]
      dsimp [k]
      rw [show n - 1 + 1 = n by omega]
      rw [mul_comm]
      dsimp [s] at hsn
      exact hsn
    refine ⟨k, hk, hleft, hright⟩
  · have hjlt : j < n := by omega
    have hleft : (j : Real) / ((p.length : Real) - 1) ≤ (t : Real) := by
      rw [div_le_iff₀ hden]
      dsimp [s] at hslo
      rw [← hncast]
      nlinarith [hslo, mul_comm (↑n) (t : Real)]
    have hright : (t : Real) ≤ ((j + 1 : Nat) : Real) / ((p.length : Real) - 1) := by
      rw [le_div_iff₀ hden]
      dsimp [s] at hshi
      rw [hncast] at hshi
      have hh := hshi
      rw [mul_comm] at hh
      norm_num [Nat.cast_add] at hh ⊢
      exact hh.le
    exact ⟨j, hjlt, hleft, hright⟩

private theorem hcombo :
    ∀ (lo : Real × Real), ∀ (hi : Real × Real), ∀ (a : Real × Real), ∀ (b : Real × Real), (a ∈
        Set.Icc lo hi) → (b ∈ Set.Icc lo hi) → ∀ (r : Real), (0 ≤ r) → (r ≤ 1) → (1 - r) • a + r
        • b ∈ Set.Icc lo hi := by
  classical
  intro lo hi a b ha hb r hr0 hr1
  simp only [Set.mem_Icc, Prod.le_def] at ha hb ⊢
  simp only [Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd, smul_eq_mul] at ⊢
  rcases ha with ⟨⟨hal, hal'⟩, ⟨hai, hai'⟩⟩
  rcases hb with ⟨⟨hbl, hbl'⟩, ⟨hbi, hbi'⟩⟩
  constructor <;> constructor
  · have h1 := mul_nonneg (sub_nonneg.mpr hr1) (sub_nonneg.mpr hal)
    have h2 := mul_nonneg hr0 (sub_nonneg.mpr hbl)
    nlinarith [h1, h2]
  · have h1 := mul_nonneg (sub_nonneg.mpr hr1) (sub_nonneg.mpr hal')
    have h2 := mul_nonneg hr0 (sub_nonneg.mpr hbl')
    nlinarith [h1, h2]
  · have h1 := mul_nonneg (sub_nonneg.mpr hr1) (sub_nonneg.mpr hai)
    have h2 := mul_nonneg hr0 (sub_nonneg.mpr hbi)
    nlinarith [h1, h2]
  · have h1 := mul_nonneg (sub_nonneg.mpr hr1) (sub_nonneg.mpr hai')
    have h2 := mul_nonneg hr0 (sub_nonneg.mpr hbi')
    nlinarith [h1, h2]

private theorem walk_continuous :
    ∀ (p : List GaussianInt), (p ≠ []) → (∀ (a : GaussianInt), Continuous (P3776T1WalkMap [a]))
        → (∀ (q : List GaussianInt), ∀ (k : Nat), (k < q.length - 1) → ∀ (t : Set.Icc (0 : Real)
        1), ((k : Real) / (q.length - 1) ≤ (t : Real)) → ((t : Real) ≤ ((k + 1 : Nat) : Real) /
        (q.length - 1)) → P3776T1WalkMap q t = (1 - ((q.length - 1 : Nat) * (t : Real) - k)) •
        GaussianRealPoint (q.getD k 0) + ((q.length - 1 : Nat) * (t : Real) - k) •
        GaussianRealPoint (q.getD (k + 1) 0)) → (p.getLast?.getD 0 = p.getD (p.length - 1) 0) →
        ((0 < p.length - 1) → ∀ (t : Set.Icc (0 : Real) 1), ∃ k, k < p.length - 1 ∧ (k : Real) /
        (p.length - 1) ≤ (t : Real) ∧ (t : Real) ≤ ((k + 1 : Nat) : Real) / (p.length - 1)) →
        Continuous (P3776T1WalkMap p) := by
  classical
  intro p hp hsingle hseg hlastD hinterval
  by_cases hp1 : p.length = 1
  · obtain ⟨a, rfl⟩ : ∃ a : GaussianInt, p = [a] := by
      cases p with
      | nil => simp at hp
      | cons a q =>
        cases q with
        | nil => exact ⟨a, rfl⟩
        | cons b q => simp at hp1
    exact hsingle a
  · have hpLen : 0 < p.length := by
      cases p with
      | nil => contradiction
      | cons a q => simp
    have hn : 0 < p.length - 1 := by omega
    let I : Fin (p.length - 1) → Set (Set.Icc (0 : Real) 1) := fun i =>
      {t | (i.val : Real) / (p.length - 1) ≤ (t : Real) ∧
        (t : Real) ≤ ((i.val + 1 : Nat) : Real) / (p.length - 1)}
    have hclosed (i : Fin (p.length - 1)) : IsClosed (I i) := by
      change IsClosed ((fun t : Set.Icc (0 : Real) 1 => (t : Real)) ⁻¹'
        Set.Icc ((i.val : Real) / (p.length - 1))
          (((i.val + 1 : Nat) : Real) / (p.length - 1)))
      exact isClosed_Icc.preimage continuous_subtype_val
    have hcont (i : Fin (p.length - 1)) :
        ContinuousOn (P3776T1WalkMap p) (I i) := by
      let A := GaussianRealPoint (p.getD i.val 0)
      let B := GaussianRealPoint (p.getD (i.val + 1) 0)
      have ha : Continuous (fun t : Set.Icc (0 : Real) 1 =>
          (1 - ((p.length - 1 : Nat) * (t : Real) - i.val)) • A +
            ((p.length - 1 : Nat) * (t : Real) - i.val) • B) := by
        have hc : Continuous (fun t : Set.Icc (0 : Real) 1 =>
            (p.length - 1 : Nat) * (t : Real) - i.val) :=
          (continuous_const.mul continuous_subtype_val).sub continuous_const
        exact ((continuous_const.sub hc).smul continuous_const).add
          (hc.smul continuous_const)
      apply ha.continuousOn.congr
      intro t ht
      simpa [A, B] using hseg p i.val i.isLt t ht.1 ht.2
    have hcover : (⋃ i : Fin (p.length - 1), I i) = Set.univ := by
      ext t
      constructor
      · intro _
        simp
      · intro _
        let n := p.length - 1
        let s : Real := (n : Real) * (t : Real)
        let j := Nat.floor s
        have hnR : (0 : Real) < n := by exact_mod_cast hn
        have hncast : (n : Real) = (p.length : Real) - 1 := by
          dsimp [n]
          rw [Nat.cast_sub (by omega : 1 ≤ p.length)]
          simp
        have hden : (0 : Real) < (p.length : Real) - 1 := by
          rw [← hncast]
          exact hnR
        have hslo : (j : Real) ≤ s := Nat.floor_le (by
          dsimp [s]
          nlinarith [t.2.1])
        have hshi : s < (j : Real) + 1 := by
          dsimp [j, s]
          exact Nat.lt_floor_add_one _
        have hsn : s ≤ n := by
          dsimp [s]
          nlinarith [t.2.2]
        have hjle : j ≤ n := by exact_mod_cast (hslo.trans hsn)
        by_cases hjn : j = n
        · let k := n - 1
          have hk : k < n := by dsimp [k]; omega
          have hklo : (k : Real) ≤ s := by
            dsimp [k]
            rw [hjn] at hslo
            have hkn : ((n - 1 : Nat) : Real) ≤ n := by exact_mod_cast (Nat.sub_le n 1)
            exact hkn.trans hslo
          have hleft : (k : Real) / ((p.length : Real) - 1) ≤ (t : Real) := by
            rw [div_le_iff₀ hden]
            dsimp [s] at hsn
            nlinarith [hklo]
          have hright : (t : Real) ≤ ((k + 1 : Nat) : Real) / ((p.length : Real) - 1) := by
            rw [le_div_iff₀ hden]
            rw [← hncast]
            dsimp [k]
            rw [show n - 1 + 1 = n by omega]
            rw [mul_comm]
            dsimp [s] at hsn
            exact hsn
          refine Set.mem_iUnion.mpr ⟨⟨k, hk⟩, ?_⟩
          exact ⟨hleft, hright⟩
        · have hjlt : j < n := by omega
          have hk : j < n := hjlt
          have hleft : (j : Real) / ((p.length : Real) - 1) ≤ (t : Real) := by
            rw [div_le_iff₀ hden]
            dsimp [s] at hslo
            nlinarith [hslo, mul_comm (↑n) (t : Real)]
          have hright : (t : Real) ≤ ((j + 1 : Nat) : Real) / ((p.length : Real) - 1) := by
            rw [le_div_iff₀ hden]
            dsimp [s] at hshi
            rw [hncast] at hshi
            have hh := hshi
            rw [mul_comm] at hh
            norm_num [Nat.cast_add] at hh ⊢
            exact hh.le
          refine Set.mem_iUnion.mpr ⟨⟨j, hk⟩, ?_⟩
          exact ⟨hleft, hright⟩
    have hlf := locallyFinite_of_finite (I)
    have hall : ContinuousOn (P3776T1WalkMap p) (⋃ i, I i) :=
      hlf.continuousOn_iUnion hclosed hcont
    rw [hcover, continuousOn_univ] at hall
    exact hall

private theorem walk_start :
    ∀ (p : List GaussianInt), (p ≠ []) → (∀ (q : List GaussianInt), ∀ (k : Nat), (k < q.length -
        1) → ∀ (t : Set.Icc (0 : Real) 1), ((k : Real) / (q.length - 1) ≤ (t : Real)) → ((t :
        Real) ≤ ((k + 1 : Nat) : Real) / (q.length - 1)) → P3776T1WalkMap q t = (1 - ((q.length
        - 1 : Nat) * (t : Real) - k)) • GaussianRealPoint (q.getD k 0) + ((q.length - 1 : Nat) *
        (t : Real) - k) • GaussianRealPoint (q.getD (k + 1) 0)) → (p.getLast?.getD 0 = p.getD
        (p.length - 1) 0) → ((0 < p.length - 1) → ∀ (t : Set.Icc (0 : Real) 1), ∃ k, k < p.length
        - 1 ∧ (k : Real) / (p.length - 1) ≤ (t : Real) ∧ (t : Real) ≤ ((k + 1 : Nat) : Real) /
        (p.length - 1)) → (Continuous (P3776T1WalkMap p)) → P3776T1WalkMap p ⟨0, by norm_num⟩
        = GaussianRealPoint (p.getD 0 0) := by
  classical
  intro p hp hseg hlastD hinterval walk_continuous
  by_cases hp1 : p.length = 1
  · obtain ⟨a, rfl⟩ : ∃ a : GaussianInt, p = [a] := by
      cases p with
      | nil => simp at hp
      | cons a q => cases q with
        | nil => exact ⟨a, rfl⟩
        | cons b q => simp at hp1
    simp [P3776T1WalkMap]
  · have hpLen : 0 < p.length := by cases p with | nil => contradiction | cons a q => simp
    have hn : 0 < p.length - 1 := by omega
    let t0 : Set.Icc (0 : Real) 1 := ⟨0, by norm_num, by norm_num⟩
    have hden : (0 : Real) < (p.length : Real) - 1 := by
      rw [← (show ((p.length - 1 : Nat) : Real) = (p.length : Real) - 1 by
        rw [Nat.cast_sub (by omega : 1 ≤ p.length)]; simp)]
      exact_mod_cast hn
    have ht1 : (0 : Real) / ((p.length : Real) - 1) ≤ (t0 : Real) := by
      simp [t0]
    have ht2 : (t0 : Real) ≤ ((0 + 1 : Nat) : Real) / ((p.length : Real) - 1) := by
      simpa [t0] using (div_nonneg (by norm_num : (0 : Real) ≤ 1) hden.le)
    have hval := hseg p 0 (by omega) t0 (by simpa using ht1) ht2
    simpa [t0] using hval

private theorem walk_end :
    ∀ (p : List GaussianInt), (p ≠ []) → (∀ (q : List GaussianInt), ∀ (k : Nat), (k < q.length -
        1) → ∀ (t : Set.Icc (0 : Real) 1), ((k : Real) / (q.length - 1) ≤ (t : Real)) → ((t :
        Real) ≤ ((k + 1 : Nat) : Real) / (q.length - 1)) → P3776T1WalkMap q t = (1 - ((q.length
        - 1 : Nat) * (t : Real) - k)) • GaussianRealPoint (q.getD k 0) + ((q.length - 1 : Nat) *
        (t : Real) - k) • GaussianRealPoint (q.getD (k + 1) 0)) → (p.getLast?.getD 0 = p.getD
        (p.length - 1) 0) → ((0 < p.length - 1) → ∀ (t : Set.Icc (0 : Real) 1), ∃ k, k < p.length
        - 1 ∧ (k : Real) / (p.length - 1) ≤ (t : Real) ∧ (t : Real) ≤ ((k + 1 : Nat) : Real) /
        (p.length - 1)) → (Continuous (P3776T1WalkMap p)) → (P3776T1WalkMap p ⟨0, by
        norm_num⟩ = GaussianRealPoint (p.getD 0 0)) → P3776T1WalkMap p ⟨1, by norm_num⟩ =
      GaussianRealPoint (p.getLast?.getD 0) := by
  classical
  intro p hp hseg hlastD hinterval walk_continuous walk_start
  by_cases hp1 : p.length = 1
  · obtain ⟨a, rfl⟩ : ∃ a : GaussianInt, p = [a] := by
      cases p with
      | nil => simp at hp
      | cons a q => cases q with
        | nil => exact ⟨a, rfl⟩
        | cons b q => simp at hp1
    simp [P3776T1WalkMap]
  · have hpLen : 0 < p.length := by cases p with | nil => contradiction | cons a q => simp
    have hn : 0 < p.length - 1 := by omega
    let n := p.length - 1
    let t1 : Set.Icc (0 : Real) 1 := ⟨1, by norm_num, by norm_num⟩
    have hnR : (0 : Real) < n := by exact_mod_cast hn
    have hncast : (n : Real) = (p.length : Real) - 1 := by
      dsimp [n]
      rw [Nat.cast_sub (by omega : 1 ≤ p.length)]
      simp
    have hden : (0 : Real) < (p.length : Real) - 1 := by rw [← hncast]; exact hnR
    have hlen : n + 1 = p.length := by dsimp [n]; omega
    have hleft : ((n - 1 : Nat) : Real) / ((p.length : Real) - 1) ≤ (t1 : Real) := by
      rw [div_le_iff₀ hden]
      simp only [one_mul, t1]
      rw [← hncast]
      exact_mod_cast (Nat.sub_le n 1)
    have hright' : (t1 : Real) ≤ ((n - 1 + 1 : Nat) : Real) / ((p.length : Real) - 1) := by
      rw [le_div_iff₀ hden]
      simp only [one_mul, Nat.sub_add_cancel (by omega : 1 ≤ n), tsub_le_iff_right, t1]
      exact_mod_cast hlen.symm.le
    have hval := hseg p (n - 1) (by dsimp [n]; omega) t1 hleft hright'
    rw [← hlen] at hval
    simpa [t1, hlastD, Nat.cast_sub (by omega : 1 ≤ n),
      Nat.sub_add_cancel (by omega : 1 ≤ n)] using hval

private theorem walk_reverse :
    ∀ (p : List GaussianInt), (p ≠ []) → (∀ (q : List GaussianInt), ∀ (k : Nat), (k < q.length -
        1) → ∀ (t : Set.Icc (0 : Real) 1), ((k : Real) / (q.length - 1) ≤ (t : Real)) → ((t :
        Real) ≤ ((k + 1 : Nat) : Real) / (q.length - 1)) → P3776T1WalkMap q t = (1 - ((q.length
        - 1 : Nat) * (t : Real) - k)) • GaussianRealPoint (q.getD k 0) + ((q.length - 1 : Nat) *
        (t : Real) - k) • GaussianRealPoint (q.getD (k + 1) 0)) → (p.getLast?.getD 0 = p.getD
        (p.length - 1) 0) → ((0 < p.length - 1) → ∀ (t : Set.Icc (0 : Real) 1), ∃ k, k < p.length
        - 1 ∧ (k : Real) / (p.length - 1) ≤ (t : Real) ∧ (t : Real) ≤ ((k + 1 : Nat) : Real) /
        (p.length - 1)) → (Continuous (P3776T1WalkMap p)) → (P3776T1WalkMap p ⟨0, by
        norm_num⟩ = GaussianRealPoint (p.getD 0 0)) → (P3776T1WalkMap p ⟨1, by norm_num⟩ =
        GaussianRealPoint (p.getLast?.getD 0)) → (∀ t : Set.Icc (0 : Real) 1,
      P3776T1WalkMap p.reverse t =
        P3776T1WalkMap p ⟨1 - (t : Real), by constructor <;> linarith [t.2.1, t.2.2]⟩) := by
  classical
  intro p hp hseg hlastD hinterval walk_continuous walk_start walk_end t
  by_cases hp1 : p.length = 1
  · obtain ⟨a, rfl⟩ : ∃ a : GaussianInt, p = [a] := by
      cases p with
      | nil => simp at hp
      | cons a q => cases q with
        | nil => exact ⟨a, rfl⟩
        | cons b q => simp at hp1
    let t' : Set.Icc (0 : Real) 1 := ⟨1 - (t : Real), by constructor <;> linarith [t.2.1, t.2.2]⟩
    simp [P3776T1WalkMap]
  · have hpLen : 0 < p.length := by cases p with | nil => contradiction | cons a q => simp
    have hn : 0 < p.length - 1 := by omega
    let n := p.length - 1
    obtain ⟨k, hk, ht1, ht2⟩ := hinterval hn t
    let j := n - 1 - k
    have hj : j + k + 1 = n := by dsimp [j]; omega
    have hjlt : j < n := by dsimp [j]; omega
    have hnR : (0 : Real) < n := by exact_mod_cast hn
    have hncast : (n : Real) = (p.length : Real) - 1 := by
      dsimp [n]
      rw [Nat.cast_sub (by omega : 1 ≤ p.length)]
      simp
    have hden : (0 : Real) < (p.length : Real) - 1 := by
      rw [← hncast]
      exact_mod_cast hn
    let t' : Set.Icc (0 : Real) 1 := ⟨1 - (t : Real), by
      constructor <;> linarith [t.2.1, t.2.2]⟩
    have hrevlo : (k : Real) / (p.reverse.length - 1) ≤ (t : Real) := by
      simpa [List.length_reverse] using ht1
    have hrevhi : (t : Real) ≤ ((k + 1 : Nat) : Real) / (p.reverse.length - 1) := by
      simpa [List.length_reverse] using ht2
    have hbaselo : (j : Real) / (p.length - 1) ≤ (t' : Real) := by
      rw [div_le_iff₀ hden]
      have htop := ht2
      rw [le_div_iff₀ hden, ← hncast] at htop
      rw [← hncast]
      have hjR : (j : Real) + k + 1 = n := by exact_mod_cast hj
      dsimp [t']
      have htop' : (t : Real) * n ≤ (k : Real) + 1 := by
        norm_num [Nat.cast_add] at htop ⊢
        exact htop
      have hsub : n - ((k : Real) + 1) = (j : Real) := by linarith
      have hmul : (1 - (t : Real)) * n = n - (t : Real) * n := by ring
      rw [hmul, ← hsub]
      linarith [htop']
    have hbasehi : (t' : Real) ≤ ((j + 1 : Nat) : Real) / (p.length - 1) := by
      rw [le_div_iff₀ hden]
      have hbot := ht1
      rw [div_le_iff₀ hden, ← hncast] at hbot
      rw [← hncast]
      have hjR : (j : Real) + k + 1 = n := by exact_mod_cast hj
      dsimp [t']
      norm_num [Nat.cast_add]
      nlinarith [hbot, mul_comm (↑n) (t : Real)]
    have hrev := by
      simpa [List.length_reverse] using
        hseg p.reverse k (by simpa [List.length_reverse] using hk) t hrevlo hrevhi
    have hbase := hseg p j hjlt t' hbaselo hbasehi
    have hidx0 : p.reverse.getD k 0 = p.getD (j + 1) 0 := by
      rw [List.getD_reverse k (by simpa [List.length_reverse] using (show k < p.length by omega))]
      congr 1
      dsimp [j, n]
      omega
    have hidx1 : p.reverse.getD (k + 1) 0 = p.getD j 0 := by
      rw [List.getD_reverse (k + 1) (by simpa [List.length_reverse] using (show k + 1 <
          p.length by omega))]
      congr 1
      dsimp [j, n]
      omega
    have hcoeff : (p.length - 1 : Nat) * (t : Real) - k =
        1 - ((p.length - 1 : Nat) * (t' : Real) - j) := by
      have hjR : (j : Real) + k + 1 = n := by exact_mod_cast hj
      have hcastN : ((p.length - 1 : Nat) : Real) = (n : Real) := rfl
      rw [hcastN]
      dsimp [t']
      nlinarith [hjR, mul_comm (↑n) (t : Real)]
    rw [hrev, hbase]
    change (1 - ((p.length - 1 : Nat) * (t : Real) - k)) •
        GaussianRealPoint (p.reverse.getD k 0) +
      ((p.length - 1 : Nat) * (t : Real) - k) •
        GaussianRealPoint (p.reverse.getD (k + 1) 0) =
      (1 - ((p.length - 1 : Nat) * (t' : Real) - j)) • GaussianRealPoint (p.getD j 0) +
        ((p.length - 1 : Nat) * (t' : Real) - j) • GaussianRealPoint (p.getD (j + 1) 0)
    rw [hidx0, hidx1, hcoeff]
    module

private theorem walk_translate :
    ∀ (p : List GaussianInt), (p ≠ []) → (∀ (q : List GaussianInt), ∀ (k : Nat), (k < q.length -
        1) → ∀ (t : Set.Icc (0 : Real) 1), ((k : Real) / (q.length - 1) ≤ (t : Real)) → ((t :
        Real) ≤ ((k + 1 : Nat) : Real) / (q.length - 1)) → P3776T1WalkMap q t = (1 - ((q.length
        - 1 : Nat) * (t : Real) - k)) • GaussianRealPoint (q.getD k 0) + ((q.length - 1 : Nat) *
        (t : Real) - k) • GaussianRealPoint (q.getD (k + 1) 0)) → (p.getLast?.getD 0 = p.getD
        (p.length - 1) 0) → ((0 < p.length - 1) → ∀ (t : Set.Icc (0 : Real) 1), ∃ k, k < p.length
        - 1 ∧ (k : Real) / (p.length - 1) ≤ (t : Real) ∧ (t : Real) ≤ ((k + 1 : Nat) : Real) /
        (p.length - 1)) → (Continuous (P3776T1WalkMap p)) → (P3776T1WalkMap p ⟨0, by
        norm_num⟩ = GaussianRealPoint (p.getD 0 0)) → (P3776T1WalkMap p ⟨1, by norm_num⟩ =
        GaussianRealPoint (p.getLast?.getD 0)) → ((∀ t : Set.Icc (0 : Real) 1, P3776T1WalkMap
        p.reverse t = P3776T1WalkMap p ⟨1 - (t : Real), by constructor <;> linarith [t.2.1,
        t.2.2]⟩)) → (∀ u : GaussianInt, ∀ t : Set.Icc (0 : Real) 1,
      P3776T1WalkMap (p.map (fun z => z + u)) t =
        P3776T1WalkMap p t + GaussianRealPoint u) := by
  classical
  intro p hp hseg hlastD hinterval walk_continuous walk_start walk_end walk_reverse u t
  have hpoint (z : GaussianInt) :
      GaussianRealPoint (z + u) = GaussianRealPoint z + GaussianRealPoint u := by
    ext <;> simp [GaussianRealPoint]
  by_cases hp1 : p.length = 1
  · obtain ⟨a, rfl⟩ : ∃ a : GaussianInt, p = [a] := by
      cases p with
      | nil => simp at hp
      | cons a q => cases q with
        | nil => exact ⟨a, rfl⟩
        | cons b q => simp at hp1
    simp [P3776T1WalkMap, hpoint]
  · have hpLen : 0 < p.length := by cases p with | nil => contradiction | cons a q => simp
    have hn : 0 < p.length - 1 := by omega
    obtain ⟨k, hk, ht1, ht2⟩ := hinterval hn t
    have hval := hseg p k hk t ht1 ht2
    have hmval := hseg (p.map fun z => z + u) k
      (by simpa [List.length_map] using hk) t
      (by simpa [List.length_map] using ht1)
      (by simpa [List.length_map] using ht2)
    have hget (i : Nat) (hi : i < p.length) :
        (p.map (fun z => z + u)).getD i 0 = (p.getD i 0) + u := by
      rw [List.getD_eq_getElem (l := p.map (fun z => z + u)) (d := 0)
        (by simpa [List.length_map] using hi)]
      rw [List.getD_eq_getElem (l := p) (d := 0) hi]
      simp
    have hi0 : k < p.length := by omega
    have hi1 : k + 1 < p.length := by omega
    simp only [List.length_map] at hmval
    rw [hmval, hval, hget k hi0, hget (k + 1) hi1, hpoint, hpoint]
    module

private theorem walk_contained :
    ∀ (p : List GaussianInt), (p ≠ []) → (∀ (q : List GaussianInt), ∀ (k : Nat), (k < q.length -
        1) → ∀ (t : Set.Icc (0 : Real) 1), ((k : Real) / (q.length - 1) ≤ (t : Real)) → ((t :
        Real) ≤ ((k + 1 : Nat) : Real) / (q.length - 1)) → P3776T1WalkMap q t = (1 - ((q.length
        - 1 : Nat) * (t : Real) - k)) • GaussianRealPoint (q.getD k 0) + ((q.length - 1 : Nat) *
        (t : Real) - k) • GaussianRealPoint (q.getD (k + 1) 0)) → (p.getLast?.getD 0 = p.getD
        (p.length - 1) 0) → ((0 < p.length - 1) → ∀ (t : Set.Icc (0 : Real) 1), ∃ k, k < p.length
        - 1 ∧ (k : Real) / (p.length - 1) ≤ (t : Real) ∧ (t : Real) ≤ ((k + 1 : Nat) : Real) /
        (p.length - 1)) → (∀ (lo : Real × Real), ∀ (hi : Real × Real), ∀ (a : Real × Real), ∀ (b
        : Real × Real), (a ∈ Set.Icc lo hi) → (b ∈ Set.Icc lo hi) → ∀ (r : Real), (0 ≤ r) → (r ≤
        1) → (1 - r) • a + r • b ∈ Set.Icc lo hi) → (Continuous (P3776T1WalkMap p)) →
        (P3776T1WalkMap p ⟨0, by norm_num⟩ = GaussianRealPoint (p.getD 0 0)) →
        (P3776T1WalkMap p ⟨1, by norm_num⟩ = GaussianRealPoint (p.getLast?.getD 0)) → ((∀ t :
        Set.Icc (0 : Real) 1, P3776T1WalkMap p.reverse t = P3776T1WalkMap p ⟨1 - (t : Real),
        by constructor <;> linarith [t.2.1, t.2.2]⟩)) → ((∀ u : GaussianInt, ∀ t : Set.Icc (0 :
        Real) 1, P3776T1WalkMap (p.map (fun z => z + u)) t = P3776T1WalkMap p t +
        GaussianRealPoint u)) → (∀ T : ProtoTile, LatticeTile T →
      (∀ z ∈ p, z ∈ FootprintVertices T) →
      (∀ a b : GaussianInt, ∀ l₁ l₂ : List GaussianInt,
        p = l₁ ++ a :: b :: l₂ → {a, b} ∈ FootprintEdges T) →
      ∀ t, P3776T1WalkMap p t ∈ TileRealization T) := by
  classical
  intro p hp hseg hlastD hinterval hcombo walk_continuous walk_start walk_end walk_reverse
      walk_translate T hT hv hed t
  have hdisc : Nonempty
      ((Metric.closedBall (0 : Real × Real) 1 : Set (Real × Real)) ≃ₜ
        TileRealization T) := by
    simpa [LatticeTile, TopologicalDisk] using hT
  rcases hdisc with ⟨e⟩
  have hreal : (TileRealization T).Nonempty := by
    let z : Real × Real := 0
    have hz : z ∈ (Metric.closedBall (0 : Real × Real) 1 : Set (Real × Real)) := by
      simp [z, Metric.mem_closedBall]
    exact ⟨e ⟨z, hz⟩, (e ⟨z, hz⟩).property⟩
  have hcells : T.cells.Nonempty := by
    by_contra hne
    have hemptyCells : T.cells = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    have hempty : TileRealization T = ∅ := by simp [TileRealization, hemptyCells]
    rw [hempty] at hreal
    simp at hreal
  have hvertex (z : GaussianInt) (hz : z ∈ FootprintVertices T) :
      ∃ x ∈ T.cells, z = x ∨ z = x + 1 ∨
        z = x + ⟨0, 1⟩ ∨ z = x + 1 + ⟨0, 1⟩ := by
    simpa [FootprintVertices, hcells] using hz
  have hcorner (x z : GaussianInt)
      (hz : z = x ∨ z = x + 1 ∨ z = x + ⟨0, 1⟩ ∨ z = x + 1 + ⟨0, 1⟩) :
      GaussianRealPoint z ∈ ClosedSquareRealization x := by
    rcases hz with hz | hz | hz | hz
    · subst z
      simp [GaussianRealPoint, ClosedSquareRealization]
    · subst z
      simp [GaussianRealPoint, ClosedSquareRealization]
    · subst z
      simp [GaussianRealPoint, ClosedSquareRealization]
    · subst z
      simp [GaussianRealPoint, ClosedSquareRealization]
  have hpair (a b c d x : GaussianInt)
      (hc : c = x ∨ c = x + 1 ∨ c = x + ⟨0, 1⟩ ∨ c = x + 1 + ⟨0, 1⟩)
      (hd : d = x ∨ d = x + 1 ∨ d = x + ⟨0, 1⟩ ∨ d = x + 1 + ⟨0, 1⟩)
      (hab : ({a, b} : Finset GaussianInt) = {c, d}) :
      GaussianRealPoint a ∈ ClosedSquareRealization x ∧
        GaussianRealPoint b ∈ ClosedSquareRealization x := by
    have hamem : a ∈ ({c, d} : Finset GaussianInt) := by
      rw [← hab]
      simp
    have hbmem : b ∈ ({c, d} : Finset GaussianInt) := by
      rw [← hab]
      simp
    have hcs := hcorner x c hc
    have hds := hcorner x d hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hamem hbmem
    rcases hamem with hac | had
    · rcases hbmem with hbc | hbd
      · exact ⟨by simpa [hac] using hcs, by simpa [hbc] using hcs⟩
      · exact ⟨by simpa [hac] using hcs, by simpa [hbd] using hds⟩
    · rcases hbmem with hbc | hbd
      · exact ⟨by simpa [had] using hds, by simpa [hbc] using hcs⟩
      · exact ⟨by simpa [had] using hds, by simpa [hbd] using hds⟩
  have hedgeSupport (a b : GaussianInt) (he : {a, b} ∈ FootprintEdges T) :
      ∃ x ∈ T.cells, GaussianRealPoint a ∈ ClosedSquareRealization x ∧
        GaussianRealPoint b ∈ ClosedSquareRealization x := by
    change ∃ x ∈ T.cells,
      ({a, b} : Finset GaussianInt) = {x, x + 1} ∨
      ({a, b} : Finset GaussianInt) = {x, x + ⟨0, 1⟩} ∨
      ({a, b} : Finset GaussianInt) = {x + 1, x + 1 + ⟨0, 1⟩} ∨
      ({a, b} : Finset GaussianInt) = {x + ⟨0, 1⟩, x + 1 + ⟨0, 1⟩} at he
    rcases he with ⟨x, hx, he | he | he | he⟩
    · have h := hpair a b x (x + 1) x (by simp) (by simp) he
      exact ⟨x, hx, h.1, h.2⟩
    · have h := hpair a b x (x + ⟨0, 1⟩) x (by simp) (by simp) he
      exact ⟨x, hx, h.1, h.2⟩
    · have h := hpair a b (x + 1) (x + 1 + ⟨0, 1⟩) x (by simp) (by simp) he
      exact ⟨x, hx, h.1, h.2⟩
    · have h := hpair a b (x + ⟨0, 1⟩) (x + 1 + ⟨0, 1⟩) x (by simp) (by simp) he
      exact ⟨x, hx, h.1, h.2⟩
  by_cases hp1 : p.length = 1
  · obtain ⟨a, rfl⟩ : ∃ a : GaussianInt, p = [a] := by
      cases p with
      | nil => simp at hp
      | cons a q => cases q with
        | nil => exact ⟨a, rfl⟩
        | cons b q => simp at hp1
    obtain ⟨x, hx, hca⟩ := hvertex a (hv a (by simp))
    change GaussianRealPoint a ∈ ⋃ x ∈ T.cells, ClosedSquareRealization x
    exact Set.mem_iUnion.mpr ⟨x, Set.mem_iUnion.mpr ⟨hx, hcorner x a hca⟩⟩
  · have hpLen : 0 < p.length := by cases p with | nil => contradiction | cons a q => simp
    have hn : 0 < p.length - 1 := by omega
    obtain ⟨k, hk, ht1, ht2⟩ := hinterval hn t
    have hk0 : k < p.length := by omega
    have hk1 : k + 1 < p.length := by omega
    let a := p.getD k 0
    let b := p.getD (k + 1) 0
    have hgetA : a = p[k] := by
      exact List.getD_eq_getElem (l := p) (d := 0) hk0
    have hgetB : b = p[k + 1] := by
      exact List.getD_eq_getElem (l := p) (d := 0) hk1
    have haV : a ∈ FootprintVertices T := by
      apply hv a
      rw [hgetA]
      exact List.getElem_mem hk0
    have hbV : b ∈ FootprintVertices T := by
      apply hv b
      rw [hgetB]
      exact List.getElem_mem hk1
    have hdrop0 : p.drop k = a :: p.drop (k + 1) := by
      calc
        p.drop k = p[k] :: p.drop (k + 1) := (List.cons_getElem_drop_succ (h := hk0)).symm
        _ = a :: p.drop (k + 1) := by
          congr 1
          exact hgetA.symm
    have hdrop1 : p.drop (k + 1) = b :: p.drop (k + 2) := by
      calc
        p.drop (k + 1) = p[k + 1] :: p.drop (k + 2) := (List.cons_getElem_drop_succ (h :=
            hk1)).symm
        _ = b :: p.drop (k + 2) := by
          congr 1
          exact hgetB.symm
    have hdecomp : p = p.take k ++ a :: b :: p.drop (k + 2) := by
      calc
        p = p.take k ++ p.drop k := (List.take_append_drop k p).symm
        _ = p.take k ++ a :: b :: p.drop (k + 2) := by rw [hdrop0, hdrop1]
    have he := hed a b (p.take k) (p.drop (k + 2)) hdecomp
    obtain ⟨x, hx, hax, hbx⟩ := hedgeSupport a b he
    have hval := hseg p k hk t ht1 ht2
    let r : Real := (p.length - 1 : Nat) * (t : Real) - k
    have hncast : ((p.length - 1 : Nat) : Real) = (p.length : Real) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ p.length)]
      simp
    have hden : (0 : Real) < (p.length : Real) - 1 := by
      rw [← hncast]
      exact_mod_cast hn
    have hmlo : (k : Real) ≤ (p.length - 1 : Nat) * (t : Real) := by
      rw [div_le_iff₀ hden] at ht1
      rw [← hncast] at ht1
      nlinarith [mul_comm (↑(p.length - 1 : Nat) : Real) (t : Real)]
    have hmhi : (p.length - 1 : Nat) * (t : Real) ≤ (k + 1 : Nat) := by
      rw [le_div_iff₀ hden] at ht2
      rw [← hncast] at ht2
      nlinarith [mul_comm (↑(p.length - 1 : Nat) : Real) (t : Real)]
    have hr0 : 0 ≤ r := by dsimp [r]; linarith [hmlo]
    have hr1 : r ≤ 1 := by
      dsimp [r]
      norm_num [Nat.cast_add] at hmhi ⊢
      linarith [hmhi]
    have hsq : P3776T1WalkMap p t ∈ ClosedSquareRealization x := by
      rw [hval]
      exact hcombo _ _ _ _ hax hbx r hr0 hr1
    change P3776T1WalkMap p t ∈ ⋃ x ∈ T.cells, ClosedSquareRealization x
    exact Set.mem_iUnion.mpr ⟨x, Set.mem_iUnion.mpr ⟨hx, hsq⟩⟩

end WalkMapLemmas

theorem P3776T1WalkMapProperties (p : List GaussianInt) (hp : p ≠ []) :
    Continuous (P3776T1WalkMap p) ∧
    P3776T1WalkMap p ⟨0, by norm_num⟩ = GaussianRealPoint (p.getD 0 0) ∧
    P3776T1WalkMap p ⟨1, by norm_num⟩ =
      GaussianRealPoint (p.getLast?.getD 0) ∧
    (∀ t : Set.Icc (0 : Real) 1,
      P3776T1WalkMap p.reverse t =
        P3776T1WalkMap p ⟨1 - (t : Real), by constructor <;> linarith [t.2.1, t.2.2]⟩) ∧
    (∀ u : GaussianInt, ∀ t : Set.Icc (0 : Real) 1,
      P3776T1WalkMap (p.map (fun z => z + u)) t =
        P3776T1WalkMap p t + GaussianRealPoint u) ∧
    (∀ T : ProtoTile, LatticeTile T →
      (∀ z ∈ p, z ∈ FootprintVertices T) →
      (∀ a b : GaussianInt, ∀ l₁ l₂ : List GaussianInt,
        p = l₁ ++ a :: b :: l₂ → {a, b} ∈ FootprintEdges T) →
      ∀ t, P3776T1WalkMap p t ∈ TileRealization T) := by
-- BODY
  classical
  have hsingle (a : GaussianInt) : Continuous (P3776T1WalkMap [a]) := WalkMapLemmas.hsingle a
  have hseg (q : List GaussianInt) (k : Nat) (hk : k < q.length - 1)
      (t : Set.Icc (0 : Real) 1)
      (ht1 : (k : Real) / (q.length - 1) ≤ (t : Real))
      (ht2 : (t : Real) ≤ ((k + 1 : Nat) : Real) / (q.length - 1)) :
      P3776T1WalkMap q t =
        (1 - ((q.length - 1 : Nat) * (t : Real) - k)) •
            GaussianRealPoint (q.getD k 0) +
          ((q.length - 1 : Nat) * (t : Real) - k) •
            GaussianRealPoint (q.getD (k + 1) 0) := WalkMapLemmas.hseg q k hk t ht1 ht2
  have hlastD : p.getLast?.getD 0 = p.getD (p.length - 1) 0 := WalkMapLemmas.hlastD p hp
  have hinterval (hn : 0 < p.length - 1) (t : Set.Icc (0 : Real) 1) :
      ∃ k, k < p.length - 1 ∧
        (k : Real) / (p.length - 1) ≤ (t : Real) ∧
        (t : Real) ≤ ((k + 1 : Nat) : Real) / (p.length - 1) := WalkMapLemmas.hinterval p hn t
  have hcombo (lo hi a b : Real × Real) (ha : a ∈ Set.Icc lo hi)
      (hb : b ∈ Set.Icc lo hi) (r : Real) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
      (1 - r) • a + r • b ∈ Set.Icc lo hi := WalkMapLemmas.hcombo lo hi a b ha hb r hr0 hr1
  have walk_continuous : Continuous (P3776T1WalkMap p) := WalkMapLemmas.walk_continuous p hp
      hsingle hseg hlastD hinterval
  have walk_start : P3776T1WalkMap p ⟨0, by norm_num⟩ = GaussianRealPoint (p.getD 0 0) :=
      WalkMapLemmas.walk_start p hp hseg hlastD hinterval walk_continuous
  have walk_end : P3776T1WalkMap p ⟨1, by norm_num⟩ =
      GaussianRealPoint (p.getLast?.getD 0) := WalkMapLemmas.walk_end p hp hseg hlastD hinterval
          walk_continuous walk_start
  have walk_reverse : (∀ t : Set.Icc (0 : Real) 1,
      P3776T1WalkMap p.reverse t =
        P3776T1WalkMap p ⟨1 - (t : Real), by constructor <;> linarith [t.2.1, t.2.2]⟩) :=
            WalkMapLemmas.walk_reverse p hp hseg hlastD hinterval walk_continuous walk_start
            walk_end
  have walk_translate : (∀ u : GaussianInt, ∀ t : Set.Icc (0 : Real) 1,
      P3776T1WalkMap (p.map (fun z => z + u)) t =
        P3776T1WalkMap p t + GaussianRealPoint u) := WalkMapLemmas.walk_translate p hp hseg
            hlastD hinterval walk_continuous walk_start walk_end walk_reverse
  have walk_contained : (∀ T : ProtoTile, LatticeTile T →
      (∀ z ∈ p, z ∈ FootprintVertices T) →
      (∀ a b : GaussianInt, ∀ l₁ l₂ : List GaussianInt,
        p = l₁ ++ a :: b :: l₂ → {a, b} ∈ FootprintEdges T) →
      ∀ t, P3776T1WalkMap p t ∈ TileRealization T) := WalkMapLemmas.walk_contained p hp hseg
          hlastD hinterval hcombo walk_continuous walk_start walk_end walk_reverse walk_translate
  exact ⟨walk_continuous, walk_start, walk_end, walk_reverse, walk_translate, walk_contained⟩

end ApollonianSuperharmonic

end
