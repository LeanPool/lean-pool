/-
Copyright (c) 2026 Stefanos Lappas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefanos Lappas
-/
module

public import LeanPool.MirekThiele.Foundations
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
public import Mathlib.MeasureTheory.Function.JacobianOneDim

/-! # Part 2 of the development: the second stopping time, the paper's sums (2.43)–(2.49),
Marcinkiewicz interpolation for outer measures, the Carleson embedding (Theorem 2.68) and
Lemmas 2.71, 2.72. Continues `MirekThiele.Foundations` inside `namespace StoppingData`. -/

@[expose] public section

open MeasureTheory

namespace MirekThiele

variable {d : ℕ}

section StoppingCollections

variable {n : ℕ}

namespace StoppingData

variable (D : StoppingData d n)



/-! #### The part `∑'` of (2.44): the numbers `φ_S` ((2.45), (2.46), p. 48)

On a cube `S` contained in a first stopping cube `P`, `𝔤 𝟙_S` is a multiple `φ_S u 𝟙_S` of `u 𝟙_S`:
the terms `g_P 𝟙_S` cancel, and all other terms of (2.12) restricted to `S` are multiples of
`u 𝟙_S` (the cubes of `𝐏 ∖ 𝐏₄`, `parents(𝐏)₄`, `𝐏₄'` inside `S` coincide with `S`, the others
containing `S`
contribute their coefficients). The coefficient satisfies `|φ_S| ≤ C_φ |Q|^{-1/q} ‖g‖_q`. -/

/-- A stopping cube contained in a subcube `S` of a stopping cube `P` equals `S`. [PROVED] -/
theorem eq_of_subset_of_mem_Pst {S P P' : DyadicCube d} (hP : P ∈ D.stoppingCubes)
    (hSP : S.toSet ⊆ P.toSet) (hP' : P' ∈ D.stoppingCubes) (h : P'.toSet ⊆ S.toSet) : P' = S := by
  have hPP' : P = P' := hP'.2 P hP.1 (h.trans hSP)
  subst hPP'
  exact DyadicCube.eq_of_subset_of_m_eq h
    (le_antisymm (DyadicCube.m_le_of_subset D.hd h) (DyadicCube.m_le_of_subset D.hd hSP))

/-- No parent of `parents(𝐏)₄` is contained in a subcube of a stopping cube. [PROVED] -/
theorem eq_of_subset_of_mem_Pbar4 {S P R' : DyadicCube d} (hP : P ∈ D.stoppingCubes)
    (hSP : S.toSet ⊆ P.toSet) (hR' : R' ∈ D.Pbar4) (h : R'.toSet ⊆ S.toSet) : R' = S := by
  exfalso
  obtain ⟨P'', hP'', rfl⟩ := D.mem_Pbar4.mp hR'
  have hP''s : P'' ∈ D.stoppingCubes := (D.mem_PstIn4.mp hP'').1
  have h1 : P'' = S := D.eq_of_subset_of_mem_Pst hP hSP hP''s (P''.subset_parent.trans h)
  subst h1
  have hm := DyadicCube.m_le_of_subset D.hd h
  rw [DyadicCube.parent_m] at hm
  omega

/-- A sibling of `𝐏₄'` contained in a subcube `S` of a stopping cube `P` equals `S`. [PROVED] -/
theorem eq_of_subset_of_mem_Psib4 {S P P' : DyadicCube d} (hP : P ∈ D.stoppingCubes)
    (hSP : S.toSet ⊆ P.toSet) (hP' : P' ∈ D.Psib4) (h : P'.toSet ⊆ S.toSet) : P' = S := by
  have hd := D.hd
  obtain ⟨⟨R', hR', hc⟩, -⟩ := D.mem_Psib4.mp hP'
  obtain ⟨P'', hP'', rfl⟩ := D.mem_Pbar4.mp hR'
  obtain ⟨ε, rfl⟩ := mem_children.mp hc
  have hP''s : P'' ∈ D.stoppingCubes := (D.mem_PstIn4.mp hP'').1
  have hP'P : (P''.parent.child ε).toSet ⊆ P.toSet := h.trans hSP
  have hP'par : (P''.parent.child ε).toSet ⊆ P''.parent.toSet := DyadicCube.child_subset _ _
  have hcm : (P''.parent.child ε).m = P''.parent.m - 1 := rfl
  have hpm := DyadicCube.parent_m P''
  -- `P` and the parent of `P''` are nested; the parent is not contained in `P`
  have hnot : ¬ P''.parent.toSet ⊆ P.toSet := by
    intro hsub
    have hPP'' : P = P'' := hP''s.2 P hP.1 (P''.subset_parent.trans hsub)
    subst hPP''
    have hm := DyadicCube.m_le_of_subset hd hsub
    omega
  have hsubP : P.toSet ⊆ P''.parent.toSet := by
    rcases le_total P.m P''.parent.m with hm | hm
    · rcases DyadicCube.subset_or_disjoint P P''.parent hm with hsub | hdis
      · exact hsub
      · exact absurd (hP'par (P''.parent.child ε).corner_mem)
          (Set.disjoint_left.mp hdis (hP'P (P''.parent.child ε).corner_mem))
    · rcases DyadicCube.subset_or_disjoint P''.parent P hm with hsub | hdis
      · exact absurd hsub hnot
      · exact absurd (hP'P (P''.parent.child ε).corner_mem)
          (Set.disjoint_left.mp hdis (hP'par (P''.parent.child ε).corner_mem))
  -- hence `P ⊊ parent`, so `m(P) ≤ m(P')`, and `P' ⊆ P` gives `P' = P`
  have hne : P ≠ P''.parent := fun e => hnot (e ▸ subset_rfl)
  have hmlt : P.m < P''.parent.m :=
    lt_of_le_of_ne (DyadicCube.m_le_of_subset hd hsubP) fun e =>
      hne (DyadicCube.eq_of_subset_of_m_eq hsubP e)
  have hm1 := DyadicCube.m_le_of_subset hd hP'P
  have hP'eq : P''.parent.child ε = P :=
    DyadicCube.eq_of_subset_of_m_eq hP'P (by omega)
  rw [hP'eq] at h ⊢
  exact DyadicCube.eq_of_subset_of_m_eq h
    (le_antisymm (DyadicCube.m_le_of_subset hd h) (DyadicCube.m_le_of_subset hd hSP))

/-- `g 𝟙_S` is cancelled by the stopping cubes: `𝟙_S ∑_{P' ∈ 𝐏} g 𝟙_{P'} = g 𝟙_S` for `S ⊆ P ∈ 𝐏`.
[PROVED] -/
theorem truncateₗ_sum_Pst_G {S P : DyadicCube d} (hP : P ∈ D.stoppingCubes)
    (hSP : S.toSet ⊆ P.toSet) :
    TestFun.truncateₗ S (∑ P' ∈ D.Pst, TestFun.truncateₗ P' D.G) = TestFun.truncateₗ S D.G := by
  have h : ∑ P' ∈ D.Pst, TestFun.truncateₗ S (TestFun.truncateₗ P' D.G) =
      TestFun.truncateₗ S (TestFun.truncateₗ P D.G) :=
    Finset.sum_eq_single_of_mem P (D.mem_Pst.mpr hP) fun P' hP' hne => by
      have hdis : Disjoint P'.toSet P.toSet :=
        maximal_pairwiseDisjoint _ (D.mem_Pst.mp hP') hP hne
      exact TestFun.truncateₗ_truncateₗ_of_disjoint (Set.disjoint_of_subset_left hSP hdis.symm) D.G
  rw [map_sum, h, TestFun.truncateₗ_truncateₗ_of_subset hSP D.G]

open Classical in
/-- A coefficient sum restricted to a subcube `S` of a stopping cube is a multiple of `u 𝟙_S`.
[PROVED] -/
theorem truncateₗ_sum_coef_eq {S : DyadicCube d} (s : Finset (DyadicCube d))
    (heq : ∀ P' ∈ s, P'.toSet ⊆ S.toSet → P' = S) :
    TestFun.truncateₗ S (∑ P' ∈ s, D.coef P' • TestFun.truncateₗ P' D.u) =
      (∑ P' ∈ s with P'.toSet ⊆ S.toSet, D.coef P' +
        ∑ P' ∈ s with ¬ P'.toSet ⊆ S.toSet ∧ S.toSet ⊆ P'.toSet, D.coef P') •
        TestFun.truncateₗ S D.u := by
  classical
  rw [TestFun.truncateₗ_sum_smul_truncateₗ, add_smul, Finset.sum_smul]
  have e : ∑ P' ∈ s with P'.toSet ⊆ S.toSet, D.coef P' • TestFun.truncateₗ P' D.u =
      ∑ P' ∈ s with P'.toSet ⊆ S.toSet, D.coef P' • TestFun.truncateₗ S D.u :=
    Finset.sum_congr rfl fun P' hP' => by
      rw [heq P' (Finset.mem_of_mem_filter P' hP') (Finset.mem_filter.mp hP').2]
  rw [e, Finset.sum_smul]

open Classical in
/-- At most one cube of `s` is contained in `S` when all such cubes equal `S`. [PROVED] -/
theorem card_filter_subset_le_one {S : DyadicCube d} (s : Finset (DyadicCube d))
    (heq : ∀ P' ∈ s, P'.toSet ⊆ S.toSet → P' = S) :
    (s.filter fun P' => P'.toSet ⊆ S.toSet).card ≤ 1 :=
  Finset.card_le_one.mpr fun x hx y hy => by
    rw [Finset.mem_filter] at hx hy
    rw [heq x hx.1 hx.2, heq y hy.1 hy.2]

/-- The constant of (2.45), (2.46): `C_φ = 1 + 8 C_G^{1/q} (4 + 2 ⌊2^d/ε⌋)`. -/
noncomputable def Cφ : ℝ := 1 + 8 * D.CG ^ (1 / D.q) * (4 + 2 * ⌊(2 : ℝ) ^ d / D.ε⌋₊)

theorem Cφ_nonneg : 0 ≤ D.Cφ := by
  have := D.CG_pos
  unfold Cφ
  positivity

/-- On a cube `S` contained in a first stopping cube `P`, `𝔤 𝟙_S` is a multiple of `u 𝟙_S` (the
identity of (2.45), (2.46), which needs no bound on `g`): the terms `g 𝟙_{P'}` of (2.12) cancel and
the remaining terms are multiples of `u 𝟙_S`. [PROVED] -/
theorem exists_truncateₗ_pruned_eq_smul {S P : DyadicCube d} (hP : P ∈ D.stoppingCubes)
    (hSP : S.toSet ⊆ P.toSet) :
    ∃ φ : ℝ, TestFun.truncateₗ S D.pruned = φ • TestFun.truncateₗ S D.u := by
  classical
  have heqOut : ∀ P' ∈ D.PstOut4, P'.toSet ⊆ S.toSet → P' = S := fun P' hP' h =>
    D.eq_of_subset_of_mem_Pst hP hSP (D.mem_PstOut4.mp hP').1 h
  have heqBar : ∀ P' ∈ D.Pbar4, P'.toSet ⊆ S.toSet → P' = S := fun P' hP' h =>
    D.eq_of_subset_of_mem_Pbar4 hP hSP hP' h
  have heqSib : ∀ P' ∈ D.Psib4, P'.toSet ⊆ S.toSet → P' = S := fun P' hP' h =>
    D.eq_of_subset_of_mem_Psib4 hP hSP hP' h
  set c₁ : Finset (DyadicCube d) → ℝ := fun s => ∑ P' ∈ s with P'.toSet ⊆ S.toSet, D.coef P'
    with hc₁
  set c₂ : Finset (DyadicCube d) → ℝ := fun s =>
    ∑ P' ∈ s with ¬ P'.toSet ⊆ S.toSet ∧ S.toSet ⊆ P'.toSet, D.coef P' with hc₂
  refine ⟨-avg D.Q D.G + (c₁ D.PstOut4 + c₂ D.PstOut4) + (c₁ D.Pbar4 + c₂ D.Pbar4) -
    (c₁ D.Psib4 + c₂ D.Psib4), ?_⟩
  have hGs : TestFun.truncateₗ S (∑ P' ∈ D.PstOut4, TestFun.truncateₗ P' D.G) +
      TestFun.truncateₗ S (∑ P' ∈ D.PstIn4, TestFun.truncateₗ P' D.G) =
      TestFun.truncateₗ S D.G := by
    rw [← map_add, ← D.sum_Pst_eq]
    exact D.truncateₗ_sum_Pst_G hP hSP
  have e2 := D.truncateₗ_sum_coef_eq D.PstOut4 heqOut
  have e4 := D.truncateₗ_sum_coef_eq D.Pbar4 heqBar
  have e5 := D.truncateₗ_sum_coef_eq D.Psib4 heqSib
  unfold pruned
  simp only [map_sub, map_add, map_smul]
  rw [e2, e4, e5]
  have hre : ∀ a b c x y z w : TestFun d, a - b - c + x - y + z - w = (a - (c + y)) - b + x + z - w
    :=
    fun a b c x y z w => by abel
  rw [hre, hGs, sub_self, zero_sub]
  simp only [hc₁, hc₂]
  module

/-- **(2.45), (2.46)**: on a cube `S` contained in a first stopping cube `P`,
`𝔤 𝟙_S = φ_S u 𝟙_S` with `|φ_S| ≤ C_φ |Q|^{-1/q} ‖g‖_q`. [PROVED] -/
theorem exists_phi (hG : D.GBound) {S P : DyadicCube d} (hP : P ∈ D.stoppingCubes)
    (hSP : S.toSet ⊆ P.toSet) :
    ∃ φ : ℝ, TestFun.truncateₗ S D.pruned = φ • TestFun.truncateₗ S D.u ∧
      |φ| ≤ D.Cφ * D.Q.vol ^ (-(1 / D.q)) * lpNorm (D.G : (Fin d → ℝ) → ℝ) D.q := by
  classical
  have hq1 : 1 ≤ D.q := D.hq.le
  have hε := D.ε_pos
  have hV := D.Q.vol_pos
  set N := lpNorm (D.G : (Fin d → ℝ) → ℝ) D.q with hN
  have hN0 : 0 ≤ N := lpNorm_nonneg _ _
  set M := ⌊(2 : ℝ) ^ d / D.ε⌋₊ with hM
  set K := D.CG ^ (1 / D.q) * D.Q.vol ^ (-(1 / D.q)) * N with hK
  have hK0 : 0 ≤ K := by have := D.CG_pos; positivity
  -- the three coefficient collections
  have heqOut : ∀ P' ∈ D.PstOut4, P'.toSet ⊆ S.toSet → P' = S := fun P' hP' h =>
    D.eq_of_subset_of_mem_Pst hP hSP (D.mem_PstOut4.mp hP').1 h
  have heqBar : ∀ P' ∈ D.Pbar4, P'.toSet ⊆ S.toSet → P' = S := fun P' hP' h =>
    D.eq_of_subset_of_mem_Pbar4 hP hSP hP' h
  have heqSib : ∀ P' ∈ D.Psib4, P'.toSet ⊆ S.toSet → P' = S := fun P' hP' h =>
    D.eq_of_subset_of_mem_Psib4 hP hSP hP' h
  have hgoodOut : ∀ P' ∈ D.PstOut4, D.Good P' := fun P' hP' =>
    D.good_of_mem_stoppingCubes (D.mem_PstOut4.mp hP').1
  have huOut : ∀ P' ∈ D.PstOut4, 1 / 8 < |avg P' D.u| := fun P' hP' =>
    D.bound_2_11 D.hd (D.stoppingCubes_subset_tree' (D.mem_PstOut4.mp hP').1)
      (D.PstOut4_not_in_P4 hP')
  have huBar : ∀ P' ∈ D.Pbar4, 1 / 8 < |avg P' D.u| := fun P' hP' =>
    D.bound_2_11 D.hd (D.Pbar4_mem_tree hP') (D.Pbar4_not_in_P4 hP')
  have huSib : ∀ P' ∈ D.Psib4, 1 / 8 < |avg P' D.u| := fun P' hP' =>
    D.bound_2_11 D.hd (D.Psib4_mem_tree hP') (D.Psib4_not_in_P4 hP')
  -- overlap bounds
  have hM4 : ∀ x, (D.Pbar4.filter fun R => x ∈ R.toSet).card ≤ M := fun x =>
    Nat.le_floor (D.card_Pbar4_filter_le x)
  have hM4' : ∀ x, (D.Psib4.filter fun R => x ∈ R.toSet).card ≤ M := fun x =>
    Nat.le_floor (D.card_Psib4_filter_le x)
  have hdisjOut : (↑D.PstOut4 : Set (DyadicCube d)).PairwiseDisjoint DyadicCube.toSet :=
    fun P hP R hR hne => maximal_pairwiseDisjoint _ (D.mem_PstOut4.mp hP).1
      (D.mem_PstOut4.mp hR).1 hne
  have hM1 : ∀ x, (D.PstOut4.filter fun P => x ∈ P.toSet).card ≤ 1 := fun x =>
    Finset.card_le_one.mpr fun P hP R hR => by
      rw [Finset.mem_filter] at hP hR
      by_contra hne
      exact Set.disjoint_left.mp (hdisjOut hP.1 hR.1 hne) hP.2 hR.2
  -- a bound for a coefficient sum over a filter of `s` with at most `t` cubes
  have hbound : ∀ (s : Finset (DyadicCube d)) (p : DyadicCube d → Prop) [DecidablePred p] (t : ℕ),
      (∀ P' ∈ s, D.Good P') → (∀ P' ∈ s, 1 / 8 < |avg P' D.u|) → (s.filter p).card ≤ t →
      |∑ P' ∈ s with p P', D.coef P'| ≤ t * (8 * K) := by
    intro s p _ t hgood hu hcard
    have h := D.abs_sum_coef_le hG (s.filter p) (fun P' hP' => hgood P' (Finset.mem_of_mem_filter P'
      hP'))
      (fun P' hP' => hu P' (Finset.mem_of_mem_filter P' hP'))
    refine h.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    exact_mod_cast hcard
  -- the expansion of `𝔤 𝟙_S`
  set c₁ : Finset (DyadicCube d) → ℝ := fun s => ∑ P' ∈ s with P'.toSet ⊆ S.toSet, D.coef P'
    with hc₁
  set c₂ : Finset (DyadicCube d) → ℝ := fun s =>
    ∑ P' ∈ s with ¬ P'.toSet ⊆ S.toSet ∧ S.toSet ⊆ P'.toSet, D.coef P' with hc₂
  refine ⟨-avg D.Q D.G + (c₁ D.PstOut4 + c₂ D.PstOut4) + (c₁ D.Pbar4 + c₂ D.Pbar4) -
    (c₁ D.Psib4 + c₂ D.Psib4), ?_, ?_⟩
  · have hGs : TestFun.truncateₗ S (∑ P' ∈ D.PstOut4, TestFun.truncateₗ P' D.G) +
        TestFun.truncateₗ S (∑ P' ∈ D.PstIn4, TestFun.truncateₗ P' D.G) =
        TestFun.truncateₗ S D.G := by
      rw [← map_add, ← D.sum_Pst_eq]
      exact D.truncateₗ_sum_Pst_G hP hSP
    have e2 := D.truncateₗ_sum_coef_eq D.PstOut4 heqOut
    have e4 := D.truncateₗ_sum_coef_eq D.Pbar4 heqBar
    have e5 := D.truncateₗ_sum_coef_eq D.Psib4 heqSib
    unfold pruned
    simp only [map_sub, map_add, map_smul]
    rw [e2, e4, e5]
    have hre : ∀ a b c x y z w : TestFun d, a - b - c + x - y + z - w = (a - (c + y)) - b + x + z -
      w :=
      fun a b c x y z w => by abel
    rw [hre, hGs, sub_self, zero_sub]
    simp only [hc₁, hc₂]
    module
  · have h1 : |avg D.Q D.G| ≤ D.Q.vol ^ (-(1 / D.q)) * N := abs_avg_le D.Q D.G hq1
    have hb1 := hbound D.PstOut4 _ 1 hgoodOut huOut (card_filter_subset_le_one _ heqOut)
    have hb2 := hbound D.PstOut4 _ 1 hgoodOut huOut (card_filter_ssup_le S hM1)
    have hb3 := hbound D.Pbar4 _ 1 (fun P' hP' => D.good_of_Pbar4 hP') huBar
      (card_filter_subset_le_one _ heqBar)
    have hb4 := hbound D.Pbar4 _ M (fun P' hP' => D.good_of_Pbar4 hP') huBar
      (card_filter_ssup_le S hM4)
    have hb5 := hbound D.Psib4 _ 1 (fun P' hP' => D.good_of_Psib4 hP') huSib
      (card_filter_subset_le_one _ heqSib)
    have hb6 := hbound D.Psib4 _ M (fun P' hP' => D.good_of_Psib4 hP') huSib
      (card_filter_ssup_le S hM4')
    simp only [Nat.cast_one, one_mul] at hb1 hb2 hb3 hb5
    have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    calc |-avg D.Q D.G + (c₁ D.PstOut4 + c₂ D.PstOut4) + (c₁ D.Pbar4 + c₂ D.Pbar4) -
          (c₁ D.Psib4 + c₂ D.Psib4)|
        ≤ |avg D.Q D.G| + |c₁ D.PstOut4| + |c₂ D.PstOut4| + |c₁ D.Pbar4| + |c₂ D.Pbar4| +
          |c₁ D.Psib4| + |c₂ D.Psib4| := by
          have t1 := abs_sub (-avg D.Q D.G + (c₁ D.PstOut4 + c₂ D.PstOut4) +
            (c₁ D.Pbar4 + c₂ D.Pbar4)) (c₁ D.Psib4 + c₂ D.Psib4)
          have t2 := abs_add_le (-avg D.Q D.G + (c₁ D.PstOut4 + c₂ D.PstOut4))
            (c₁ D.Pbar4 + c₂ D.Pbar4)
          have t3 := abs_add_le (-avg D.Q D.G) (c₁ D.PstOut4 + c₂ D.PstOut4)
          have t4 := abs_add_le (c₁ D.PstOut4) (c₂ D.PstOut4)
          have t5 := abs_add_le (c₁ D.Pbar4) (c₂ D.Pbar4)
          have t6 := abs_add_le (c₁ D.Psib4) (c₂ D.Psib4)
          rw [abs_neg] at t3
          linarith
      _ ≤ D.Q.vol ^ (-(1 / D.q)) * N + 8 * K + 8 * K + 8 * K + M * (8 * K) + 8 * K + M * (8 * K) :=
          add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add h1 hb1) hb2)
            hb3) hb4) hb5) hb6
      _ = D.Cφ * D.Q.vol ^ (-(1 / D.q)) * N := by
          unfold Cφ
          rw [hK]
          simp only [hM]
          ring

/-- Exponent bookkeeping: `(|S|/|Q|)^{1-1/r} |S|^{1/r} = |S| |Q|^{1/r-1}`. [PROVED] -/
theorem rpow_fact1 {s V r : ℝ} (hs : 0 < s) (hV : 0 < V) :
    (s / V) ^ (1 - 1 / r) * s ^ (1 / r) = s * V ^ (1 / r - 1) := by
  rw [Real.div_rpow hs.le hV.le, div_eq_mul_inv, ← Real.rpow_neg hV.le, mul_right_comm,
    ← Real.rpow_add hs, sub_add_cancel, Real.rpow_one, neg_sub]

/-- Exponent bookkeeping for (2.52):
`(|R|/|Q|)^{1-1/r-1/q} |R|^{1/r} (|S|/|R|)^{1-1/q} (|S|/|Q|)^{1/q} = |S| |Q|^{1/r-1}`. [PROVED] -/
theorem rpow_fact2 {s t V r q : ℝ} (hs : 0 < s) (ht : 0 < t) (hV : 0 < V) :
    (t / V) ^ (1 - 1 / r - 1 / q) * t ^ (1 / r) * (s / t) ^ (1 - 1 / q) * (s / V) ^ (1 / q) =
      s * V ^ (1 / r - 1) := by
  rw [Real.div_rpow ht.le hV.le, Real.div_rpow hs.le ht.le, Real.div_rpow hs.le hV.le,
    div_eq_mul_inv (t ^ _), div_eq_mul_inv (s ^ (1 - 1 / q)), div_eq_mul_inv (s ^ (1 / q)),
    ← Real.rpow_neg hV.le, ← Real.rpow_neg ht.le, ← Real.rpow_neg hV.le]
  have hT : t ^ (1 - 1 / r - 1 / q) * t ^ (1 / r) * t ^ (-(1 - 1 / q)) = 1 := by
    rw [← Real.rpow_add ht, ← Real.rpow_add ht, show 1 - 1 / r - 1 / q + 1 / r + -(1 - 1 / q) = 0
      by ring, Real.rpow_zero]
  have hS : s ^ (1 - 1 / q) * s ^ (1 / q) = s := by
    rw [← Real.rpow_add hs, sub_add_cancel, Real.rpow_one]
  have hQ : V ^ (-(1 - 1 / r - 1 / q)) * V ^ (-(1 / q)) = V ^ (1 / r - 1) := by
    rw [← Real.rpow_add hV]
    congr 1
    ring
  calc t ^ (1 - 1 / r - 1 / q) * V ^ (-(1 - 1 / r - 1 / q)) * t ^ (1 / r) *
        (s ^ (1 - 1 / q) * t ^ (-(1 - 1 / q))) * (s ^ (1 / q) * V ^ (-(1 / q)))
      = (t ^ (1 - 1 / r - 1 / q) * t ^ (1 / r) * t ^ (-(1 - 1 / q))) *
          (s ^ (1 - 1 / q) * s ^ (1 / q)) * (V ^ (-(1 - 1 / r - 1 / q)) * V ^ (-(1 / q))) := by
        ring
    _ = _ := by rw [hT, hS, hQ, one_mul]

/-! #### The part `∑'` of (2.44), the full sum (2.44), and the sum (2.42) (p. 48–50) -/

/-- A cube which is not "in no first stopping cube" lies in a first stopping cube. [PROVED] -/
theorem exists_stopping_of_not_notInStopping {S : DyadicCube d} (h : ¬ D.NotInStopping S) :
    ∃ P ∈ D.stoppingCubes, S.toSet ⊆ P.toSet := by
  by_contra h'
  exact h fun P hP hsub => h' ⟨P, hP, hsub⟩

/-- On a subcube `S ⊆ R` of a first stopping cube, `𝔤̂ 𝟙_S = (φ_S − c_R) u 𝟙_S`. [PROVED] -/
theorem truncateₗ_ghat_eq_phi {R S : DyadicCube d} (hSR : S.toSet ⊆ R.toSet) {φ : ℝ}
    (hφ : TestFun.truncateₗ S D.pruned = φ • TestFun.truncateₗ S D.u) :
    TestFun.truncateₗ S (D.ghat R) = (φ - D.cS R) • TestFun.truncateₗ S D.u := by
  rw [ghat_eq, TestFun.truncateₗ_truncateₗ_of_subset hSR, psi_eq, map_sub, map_smul, hφ]
  module

/-- The constant of the combined bound (2.37): `K₂ = 4^d B^{1+1/q} / ε²`. -/
noncomputable def K₂' : ℝ := 4 ^ d * D.B ^ (1 + 1 / D.q) / D.ε ^ 2

theorem K₂'_nonneg : 0 ≤ D.K₂' := by
  have := D.ε_pos
  have : 0 ≤ D.B := by linarith [D.hB]
  unfold K₂'
  positivity

/-- **(2.37) combined with (2.10) at `R`**: for a good cube `S` of the second stopping time and a
mean-zero `ϱ` supported on `S`, `|Λ_S(ϱ, u)| ≤ K₂ F |Q|^{1/q} (|S|/|Q|)^{1-1/r} ‖ϱ‖_r`. [PROVED] -/
theorem slotForm_le_second {R : DyadicCube d} (hR : R ∈ D.tree) (hRs : D.NotInStopping R)
    (hFR : 0 < D.FP R) {S : DyadicCube d} (hS : (D.second R hR hRs hFR).Good S) (ρ : TestFun d)
    (hρ : SupportedOn ρ S) (hρ0 : MeanZero (ρ : (Fin d → ℝ) → ℝ)) :
    |slotForm D.T D.a D.g S ρ| ≤
      D.K₂' * D.F * D.Q.vol ^ (1 / D.q) * (S.vol / D.Q.vol) ^ (1 - 1 / D.r) *
        lpNorm (ρ : (Fin d → ℝ) → ℝ) D.r := by
  have hB0 : 0 ≤ D.B := by linarith [D.hB]
  have hq0 : 0 < D.q := by linarith [D.hq]
  have hε := D.ε_pos
  have hV := D.Q.vol_pos
  have hRv := R.vol_pos
  have hSv := S.vol_pos
  have hF0 := D.Fpos'.le
  have hu0 : 0 ≤ lpNorm (D.u : (Fin d → ℝ) → ℝ) D.q := lpNorm_nonneg _ _
  have hρ0' : 0 ≤ lpNorm (ρ : (Fin d → ℝ) → ℝ) D.r := lpNorm_nonneg _ _
  have h := D.second_bound_2_37 hR hRs hFR hS ρ hρ hρ0
  have hu := D.lpNorm_u_le
  have hcomb : (R.vol / D.Q.vol) ^ (1 - 1 / D.r) * (S.vol / R.vol) ^ (1 - 1 / D.r) =
      (S.vol / D.Q.vol) ^ (1 - 1 / D.r) := by
    rw [← Real.mul_rpow (by positivity) (by positivity), div_mul_div_comm, mul_comm R.vol S.vol,
      mul_div_mul_right _ _ hRv.ne']
  refine h.trans ?_
  unfold KR
  calc 2 ^ d * (2 ^ d * (D.B * D.F * lpNorm (D.u : (Fin d → ℝ) → ℝ) D.q * D.ε⁻¹) *
        (R.vol / D.Q.vol) ^ (1 - 1 / D.r) * D.ε⁻¹) * (S.vol / R.vol) ^ (1 - 1 / D.r) *
        lpNorm (ρ : (Fin d → ℝ) → ℝ) D.r
      ≤ 2 ^ d * (2 ^ d * (D.B * D.F * (D.B * D.Q.vol) ^ (1 / D.q) * D.ε⁻¹) *
          (R.vol / D.Q.vol) ^ (1 - 1 / D.r) * D.ε⁻¹) * (S.vol / R.vol) ^ (1 - 1 / D.r) *
          lpNorm (ρ : (Fin d → ℝ) → ℝ) D.r := by gcongr
    _ = D.K₂' * D.F * D.Q.vol ^ (1 / D.q) *
          ((R.vol / D.Q.vol) ^ (1 - 1 / D.r) * (S.vol / R.vol) ^ (1 - 1 / D.r)) *
          lpNorm (ρ : (Fin d → ℝ) → ℝ) D.r := by
        unfold K₂'
        rw [Real.mul_rpow hB0 hV.le, Real.rpow_add' hB0 (by positivity), Real.rpow_one,
          show (4 : ℝ) ^ d = 2 ^ d * 2 ^ d by rw [← mul_pow]; norm_num]
        ring
    _ = _ := by rw [hcomb]

/-- The function `b_S − [v]_S^{-1} v_S` of (2.42), `v = b_{τ,𝐐_R,k}`. -/
noncomputable def yS (R S : DyadicCube d) : TestFun d :=
  D.vP S - (1 / avg S (D.vP R)) • TestFun.truncateₗ S (D.vP R)

theorem yS_supported (R : DyadicCube d) {S : DyadicCube d} (hS : S.toSet ⊆ D.Q.toSet) :
    SupportedOn (D.yS R S : (Fin d → ℝ) → ℝ) S := fun x hx => by
  unfold yS
  rw [Submodule.coe_sub, Pi.sub_apply, Submodule.coe_smul, Pi.smul_apply, D.vP_supp S hS x hx,
    TestFun.truncateₗ_supportedOn S _ x hx, smul_zero, sub_zero]

theorem yS_meanZero (R : DyadicCube d) {S : DyadicCube d} (hS : S.toSet ⊆ D.Q.toSet)
    (hv : avg S (D.vP R) ≠ 0) : MeanZero (D.yS R S : (Fin d → ℝ) → ℝ) := by
  change TestFun.integralₗ (D.yS R S) = 0
  unfold yS
  rw [map_sub, map_smul, smul_eq_mul, TestFun.integralₗ_apply, D.vP_mean S hS,
    TestFun.integralₗ_truncateₗ, one_div, ← mul_assoc, inv_mul_cancel₀ hv, one_mul, sub_self]

section Sum244'

variable {R : DyadicCube d} (hR : R ∈ D.tree) (hRs : D.NotInStopping R) (hFR : 0 < D.FP R)

open Classical in
theorem Sin_subset_R {S : DyadicCube d} (hS : S ∈ D.Sin hR hRs hFR) : S.toSet ⊆ R.toSet :=
  (D.second R hR hRs hFR).Pst_subset_Q (Finset.mem_of_mem_filter S hS)

open Classical in
theorem Sin_good {S : DyadicCube d} (hS : S ∈ D.Sin hR hRs hFR) :
    (D.second R hR hRs hFR).Good S :=
  (D.second R hR hRs hFR).good_of_mem_stoppingCubes
    ((D.second R hR hRs hFR).mem_Pst.mp (Finset.mem_of_mem_filter S hS))

open Classical in
theorem Sin_inside {S : DyadicCube d} (hS : S ∈ D.Sin hR hRs hFR) :
    ∃ P ∈ D.stoppingCubes, S.toSet ⊆ P.toSet :=
  D.exists_stopping_of_not_notInStopping (Finset.mem_filter.mp hS).2

/-- The constant of the part `∑'` of (2.44): `C₄₅ = 2 B^{1/r} (C_φ + 8 C_loc) K₂`. -/
noncomputable def C₄₅ : ℝ := 2 * D.B ^ (1 / D.r) * (D.Cφ + 8 * D.locConst) * D.K₂'

theorem C₄₅_nonneg : 0 ≤ D.C₄₅ := by
  have := D.Cφ_nonneg
  have := D.locConst_nonneg
  have := D.K₂'_nonneg
  have : 0 ≤ D.B := by linarith [D.hB]
  unfold C₄₅
  positivity

/-- A general term of the part `∑'` (p. 48): for a good cube `S` of the second stopping time
contained in a first stopping cube, with `𝔤̂ 𝟙_S = (φ_S − c_R) u 𝟙_S`, and `ρ` supported on `S` with
mean zero and `‖ρ‖_r ≤ c |S|^{1/r}`: `|Λ_S(ρ, 𝔤̂)| ≤ c (C_φ + 8 C_loc) K₂ E_S`. [PROVED] -/
theorem abs_form2_ghat_le_of_inside (hG : D.GBound) {S : DyadicCube d}
    (hS : (D.second R hR hRs hFR).Good S) (hSR : S.toSet ⊆ R.toSet)
    (hin : ∃ P ∈ D.stoppingCubes, S.toSet ⊆ P.toSet) (ρ : TestFun d) (hρ : SupportedOn ρ S)
    (hρ0 : MeanZero (ρ : (Fin d → ℝ) → ℝ)) {c : ℝ}
    (hρn : lpNorm (ρ : (Fin d → ℝ) → ℝ) D.r ≤ c * S.vol ^ (1 / D.r)) :
    |twoSlotForm D.T D.a D.b D.g S ρ (D.ghat R)| ≤
      c * (D.Cφ + 8 * D.locConst) * D.K₂' * D.E S := by
  have hV := D.Q.vol_pos
  have hSv := S.vol_pos
  have hF0 := D.Fpos'.le
  have hK := D.K₂'_nonneg
  have hN0 : 0 ≤ lpNorm (D.G : (Fin d → ℝ) → ℝ) D.q := lpNorm_nonneg _ _
  have hL := D.locConst_nonneg
  have hCφ := D.Cφ_nonneg
  obtain ⟨P, hP, hSP⟩ := hin
  obtain ⟨φ, hφ, hφb⟩ := D.exists_phi hG hP hSP
  have hcR := D.abs_cS_le hG hR hRs
  have hcoef : |φ - D.cS R| ≤
      (D.Cφ + 8 * D.locConst) * D.Q.vol ^ (-(1 / D.q)) * lpNorm (D.G : (Fin d → ℝ) → ℝ) D.q := by
    calc |φ - D.cS R| ≤ |φ| + |D.cS R| := abs_sub _ _
      _ ≤ D.Cφ * D.Q.vol ^ (-(1 / D.q)) * lpNorm (D.G : (Fin d → ℝ) → ℝ) D.q +
          8 * (D.locConst * D.Q.vol ^ (-(1 / D.q)) * lpNorm (D.G : (Fin d → ℝ) → ℝ) D.q) :=
          add_le_add hφb hcR
      _ = _ := by ring
  have hslot := D.slotForm_le_second hR hRs hFR hS ρ hρ hρ0
  have hone : D.Q.vol ^ (-(1 / D.q)) * D.Q.vol ^ (1 / D.q) = 1 := by
    rw [← Real.rpow_add hV, neg_add_cancel, Real.rpow_zero]
  rw [← twoSlotForm_truncateₗ_right, D.truncateₗ_ghat_eq_phi hSR hφ, twoSlotForm_smul_right,
    twoSlotForm_truncateₗ_right, twoSlotForm_self D.T D.hab, abs_mul]
  calc |φ - D.cS R| * |slotForm D.T D.a D.g S ρ|
      ≤ ((D.Cφ + 8 * D.locConst) * D.Q.vol ^ (-(1 / D.q)) * lpNorm (D.G : (Fin d → ℝ) → ℝ) D.q) *
          (D.K₂' * D.F * D.Q.vol ^ (1 / D.q) * (S.vol / D.Q.vol) ^ (1 - 1 / D.r) *
            (c * S.vol ^ (1 / D.r))) := by
        refine mul_le_mul hcoef (hslot.trans ?_) (abs_nonneg _) (by positivity)
        gcongr
    _ = c * (D.Cφ + 8 * D.locConst) * D.K₂' * (D.F * lpNorm (D.G : (Fin d → ℝ) → ℝ) D.q *
          ((D.Q.vol ^ (-(1 / D.q)) * D.Q.vol ^ (1 / D.q)) *
            ((S.vol / D.Q.vol) ^ (1 - 1 / D.r) * S.vol ^ (1 / D.r)))) := by ring
    _ = _ := by
        rw [hone, one_mul, rpow_fact1 hSv hV]
        unfold E
        ring

/-- **The part `∑'` of (2.44)** (p. 48): `|∑' Λ_S(h_S − b_S, 𝔤̂)| ≤ C₄₅ E_R`. [PROVED] -/
theorem abs_sum_Sin_le (hG : D.GBound) :
    |∑ S ∈ D.Sin hR hRs hFR, twoSlotForm D.T D.a D.b D.g S (TestFun.ind S - D.vP S) (D.ghat R)| ≤
      D.C₄₅ * D.E R := by
  classical
  have hE0 : ∀ S, 0 ≤ D.E S := fun S => (D.E_pos S).le
  have hsumE : ∑ S ∈ D.Sin hR hRs hFR, D.E S ≤ D.E R :=
    ((Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun S _ _ => hE0 S).trans
      (D.sum_E_second_le hR hRs hFR)).trans
      (mul_le_of_le_one_left (hE0 R) (by linarith [D.ε_pos]))
  have hB0 : 0 ≤ D.B := by linarith [D.hB]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ S ∈ D.Sin hR hRs hFR,
        |twoSlotForm D.T D.a D.b D.g S (TestFun.ind S - D.vP S) (D.ghat R)|
      ≤ ∑ S ∈ D.Sin hR hRs hFR,
          (2 * D.B ^ (1 / D.r)) * (D.Cφ + 8 * D.locConst) * D.K₂' * D.E S := by
        refine Finset.sum_le_sum fun S hS => ?_
        have hSQ : S.toSet ⊆ D.Q.toSet := (D.Sin_subset_R hR hRs hFR hS).trans hR.1
        exact D.abs_form2_ghat_le_of_inside hR hRs hFR hG (D.Sin_good hR hRs hFR hS)
          (D.Sin_subset_R hR hRs hFR hS) (D.Sin_inside hR hRs hFR hS) _
          (D.ind_sub_vP_supported hSQ) (D.ind_sub_vP_meanZero hSQ)
          (D.lpNorm_ind_sub_vP_le hSQ)
    _ = D.C₄₅ * ∑ S ∈ D.Sin hR hRs hFR, D.E S := by
        rw [Finset.mul_sum]
        unfold C₄₅
        exact Finset.sum_congr rfl fun S _ => by ring
    _ ≤ D.C₄₅ * D.E R := mul_le_mul_of_nonneg_left hsumE D.C₄₅_nonneg

/-- **The sum (2.44)** (p. 48–49): with `C₄₄ = C_α + C₄₉ + C₄₅`,
`|Λ_R(∑_{S ∈ 𝐒} (h_S − b_S), 𝔤̂)| ≤ ((1−ε) A' + C₄₄) E_R`. [PROVED] -/
theorem abs_form2_sum244_le (hG : D.GBound) :
    |twoSlotForm D.T D.a D.b D.g R (∑ S ∈ (D.second R hR hRs hFR).Pst, (TestFun.ind S - D.vP S))
        (D.ghat R)| ≤
      ((1 - D.ε) * D.A' + (D.Cα + D.C₄₉ + D.C₄₅)) * D.E R := by
  rw [D.form2_sum_ind_sub_vP_eq hR hRs hFR, D.sum_Pst_eq_Sout_add_Sin hR hRs hFR]
  refine (abs_add_le _ _).trans ?_
  have h1 := D.abs_sum_Sout_le hR hRs hFR hG
  have h2 := D.abs_sum_Sin_le hR hRs hFR hG
  linarith

/-! #### The sum (2.42) with (2.50)–(2.53) (p. 49–50) -/

/-- The constant `C_y = B^{1/r} + 8 (2^d B/ε)^{1/r}` of `‖b_S − [v]_S^{-1} v_S‖_r ≤ C_y |S|^{1/r}`.
-/
noncomputable def Cy : ℝ := D.B ^ (1 / D.r) + 8 * (2 ^ d * D.B / D.ε) ^ (1 / D.r)

theorem Cy_nonneg : 0 ≤ D.Cy := by
  have := D.ε_pos
  have : 0 ≤ D.B := by linarith [D.hB]
  unfold Cy
  positivity

/-- `‖b_S − [v]_S^{-1} v_S‖_r ≤ C_y |S|^{1/r}` for a good cube `S` of the second stopping time
with `|[v]_S| > 1/8`, by (1.7) and (2.34). [PROVED] -/
theorem lpNorm_yS_le {S : DyadicCube d} (hS : (D.second R hR hRs hFR).Good S)
    (hv8 : 1 / 8 < |avg S (D.vP R)|) :
    lpNorm (D.yS R S : (Fin d → ℝ) → ℝ) D.r ≤ D.Cy * S.vol ^ (1 / D.r) := by
  have hr1 : 1 ≤ D.r := D.hr.le
  have hr0 : 0 < D.r := by linarith
  have hB0 : 0 ≤ D.B := by linarith [D.hB]
  have hε := D.ε_pos
  have hSv := S.vol_pos
  have hSQ : S.toSet ⊆ D.Q.toSet := hS.1.1.trans hR.1
  have hv : lpNorm (TestFun.truncateₗ S (D.vP R) : (Fin d → ℝ) → ℝ) D.r ≤
      (2 ^ d * D.B / D.ε * S.vol) ^ (1 / D.r) := by
    have h := (D.second R hR hRs hFR).lpNorm_truncateₗ_u_le hS
    rw [second_u] at h
    exact h
  have hc : |1 / avg S (D.vP R)| ≤ 8 := by
    rw [abs_div, abs_one, div_le_iff₀ (by linarith)]
    linarith
  unfold yS
  refine (TestFun.lpNorm_sub_le _ _ hr1).trans ?_
  rw [TestFun.lpNorm_smul]
  calc lpNorm (D.vP S : (Fin d → ℝ) → ℝ) D.r +
        |1 / avg S (D.vP R)| * lpNorm (TestFun.truncateₗ S (D.vP R) : (Fin d → ℝ) → ℝ) D.r
      ≤ (D.B * S.vol) ^ (1 / D.r) + 8 * (2 ^ d * D.B / D.ε * S.vol) ^ (1 / D.r) :=
        add_le_add (D.lpNorm_vP_le hSQ) (mul_le_mul hc hv (lpNorm_nonneg _ _) (by norm_num))
    _ = D.Cy * S.vol ^ (1 / D.r) := by
        unfold Cy
        rw [Real.mul_rpow hB0 hSv.le, Real.mul_rpow (by positivity) hSv.le]
        ring

/-- The cubes of `𝐒 ∖ 𝐒₄` have `|[v]_S| > 1/8` and `[v]_S ≠ 0`. [PROVED] -/
theorem PstOut4_second_avg_v {S : DyadicCube d} (hS : S ∈ (D.second R hR hRs hFR).PstOut4) :
    1 / 8 < |avg S (D.vP R)| :=
  D.second_bound_2_30 hR hRs hFR
    ((D.second R hR hRs hFR).stoppingCubes_subset_tree'
      ((D.second R hR hRs hFR).mem_PstOut4.mp hS).1)
    ((D.second R hR hRs hFR).PstOut4_not_in_P4 hS)

theorem avg_v_ne_of_gt {S : DyadicCube d} (hv8 : 1 / 8 < |avg S (D.vP R)|) :
    avg S (D.vP R) ≠ 0 := by
  intro h
  rw [h, abs_zero] at hv8
  norm_num at hv8

theorem PstOut4_second_avg_v_ne {S : DyadicCube d} (hS : S ∈ (D.second R hR hRs hFR).PstOut4) :
    avg S (D.vP R) ≠ 0 :=
  D.avg_v_ne_of_gt (D.PstOut4_second_avg_v hR hRs hFR hS)

open Classical in
theorem PstOut4_second_subset_R {S : DyadicCube d} (hS : S ∈ (D.second R hR hRs hFR).PstOut4) :
    S.toSet ⊆ R.toSet :=
  (D.second R hR hRs hFR).Pst_subset_Q (Finset.mem_of_mem_filter S hS)

theorem PstOut4_second_good {S : DyadicCube d} (hS : S ∈ (D.second R hR hRs hFR).PstOut4) :
    (D.second R hR hRs hFR).Good S :=
  (D.second R hR hRs hFR).good_of_mem_stoppingCubes
    ((D.second R hR hRs hFR).mem_PstOut4.mp hS).1

/-- **The identity (2.50)**: by the smoothness condition,
`Λ_R(∑_{S ∈ 𝐒∖𝐒₄} (b_S − [v]_S^{-1} v_S), 𝔤̂) = ∑_{S ∈ 𝐒∖𝐒₄} Λ_S(b_S − [v]_S^{-1} v_S, 𝔤̂)`.
[PROVED] -/
theorem form2_sum_yS_eq :
    twoSlotForm D.T D.a D.b D.g R (∑ S ∈ (D.second R hR hRs hFR).PstOut4, D.yS R S) (D.ghat R) =
      ∑ S ∈ (D.second R hR hRs hFR).PstOut4, twoSlotForm D.T D.a D.b D.g S (D.yS R S) (D.ghat R) :=
        by
  rw [twoSlotForm_sum_left D.T D.hab]
  refine Finset.sum_congr rfl fun S hS => ?_
  have hSR := D.PstOut4_second_subset_R hR hRs hFR hS
  exact (twoSlotForm_eq_of_subset_left D.T D.hab D.g hSR (D.yS_supported R (hSR.trans hR.1))
    (D.yS_meanZero R (hSR.trans hR.1) (D.PstOut4_second_avg_v_ne hR hRs hFR hS)) _).symm

/-- The constant of (2.52): `C₅₂ = 8 · 2^d B^{1+1/r} C_G^{1-1/r-1/q} C_ψ / ε`. -/
noncomputable def C₅₂ : ℝ :=
  8 * 2 ^ d * D.B ^ (1 + 1 / D.r) * D.CG ^ (1 - 1 / D.r - 1 / D.q) * D.psiConst / D.ε

theorem C₅₂_nonneg : 0 ≤ D.C₅₂ := by
  have := D.ε_pos
  have := D.CG_pos
  have := D.psiConst_nonneg
  have : 0 ≤ D.B := by linarith [D.hB]
  unfold C₅₂
  positivity

/-- **(2.52)** for one cube: for `S ∈ 𝐒∖𝐒₄` in no first stopping cube,
`|[v]_S^{-1} Λ_S(v_S, ψ_S)| ≤ C₅₂ E_S`, by (2.36) applied to the mean-zero function `ψ_S 𝟙_S`, the
local bounds `F_R ≤ (C_G |R|/|Q|)^{1-1/r-1/q} F`, `‖ψ_S 𝟙_S‖_q ≤ C_ψ (|S|/|Q|)^{1/q} ‖g‖_q`, and
`‖v‖_r ≤ (B|R|)^{1/r}`. [PROVED] -/
theorem abs_term_2_52_le (hG : D.GBound) {S : DyadicCube d}
    (hgood' : (D.second R hR hRs hFR).Good S) (hv8 : 1 / 8 < |avg S (D.vP R)|)
    (hSs : D.NotInStopping S) :
    |(1 / avg S (D.vP R)) * twoSlotForm D.T D.a D.b D.g S (D.vP R) (D.psi S)| ≤ D.C₅₂ * D.E S := by
  have hr0 : 0 < D.r := by linarith [D.hr]
  have hq0 : 0 < D.q := by linarith [D.hq]
  have hB0 : 0 ≤ D.B := by linarith [D.hB]
  have hε := D.ε_pos
  have hV := D.Q.vol_pos
  have hRv := R.vol_pos
  have hSv := S.vol_pos
  have hF0 := D.Fpos'.le
  have hCG := D.CG_pos
  have hψ0 := D.psiConst_nonneg
  have hN0 : 0 ≤ lpNorm (D.G : (Fin d → ℝ) → ℝ) D.q := lpNorm_nonneg _ _
  have hv0 : 0 ≤ lpNorm (D.vP R : (Fin d → ℝ) → ℝ) D.r := lpNorm_nonneg _ _
  have hSt : S ∈ D.tree := D.second_tree_subset hR hRs hFR hgood'.1
  have hgoodR : D.Good R := D.good_of_notInStopping hR hRs
  have hc : |1 / avg S (D.vP R)| ≤ 8 := by
    rw [abs_div, abs_one, div_le_iff₀ (by linarith)]
    linarith
  -- (2.36) for `ψ_S 𝟙_S`
  have h36 := D.second_bound_2_36 hR hRs hFR hgood' (D.ghat S)
    (D.ghat_supported S) (D.ghat_meanZero hSt hSs)
  have hψ : lpNorm (D.ghat S : (Fin d → ℝ) → ℝ) D.q ≤
      D.psiConst * (S.vol / D.Q.vol) ^ (1 / D.q) * lpNorm (D.G : (Fin d → ℝ) → ℝ) D.q :=
    D.lpNorm_truncateₗ_psi_le hG hSt hSs
  have hFP := D.FP_le hgoodR
  have hv := D.lpNorm_vP_le hR.1
  have hg0 : 0 ≤ lpNorm (D.ghat S : (Fin d → ℝ) → ℝ) D.q := lpNorm_nonneg _ _
  have hFP0 := D.FP_nonneg R
  rw [← twoSlotForm_truncateₗ_right, ← ghat_eq, abs_mul]
  calc |1 / avg S (D.vP R)| * |twoSlotForm D.T D.a D.b D.g S (D.vP R) (D.ghat S)|
      ≤ 8 * (2 ^ d * (D.B * ((D.CG * (R.vol / D.Q.vol)) ^ (1 - 1 / D.r - 1 / D.q) * D.F) *
          (D.B * R.vol) ^ (1 / D.r) * D.ε⁻¹) * (S.vol / R.vol) ^ (1 - 1 / D.q) *
          (D.psiConst * (S.vol / D.Q.vol) ^ (1 / D.q) * lpNorm (D.G : (Fin d → ℝ) → ℝ) D.q)) := by
        refine mul_le_mul hc (h36.trans ?_) (abs_nonneg _) (by positivity)
        gcongr
    _ = D.C₅₂ * (D.F * lpNorm (D.G : (Fin d → ℝ) → ℝ) D.q *
          ((R.vol / D.Q.vol) ^ (1 - 1 / D.r - 1 / D.q) * R.vol ^ (1 / D.r) *
            (S.vol / R.vol) ^ (1 - 1 / D.q) * (S.vol / D.Q.vol) ^ (1 / D.q))) := by
        unfold C₅₂
        rw [Real.mul_rpow hCG.le (by positivity), Real.mul_rpow hB0 hRv.le,
          Real.rpow_add' hB0 (by positivity), Real.rpow_one]
        ring
    _ = D.C₅₂ * D.E S := by
        rw [rpow_fact2 hSv hRv hV]
        unfold E
        ring

/-- The constant of (2.50) (the part `∑'` of (2.42)): `C₅₀ = C_y (C_φ + 8 C_loc) K₂`. -/
noncomputable def C₅₀ : ℝ := D.Cy * (D.Cφ + 8 * D.locConst) * D.K₂'

/-- The constant of (2.53): `C₅₃ = 16 · 2^d C_loc B^{1+1/q} C_y / ε`. -/
noncomputable def C₅₃ : ℝ := 16 * 2 ^ d * D.locConst * D.B ^ (1 + 1 / D.q) * D.Cy / D.ε

theorem C₅₃_nonneg : 0 ≤ D.C₅₃ := by
  have := D.locConst_nonneg
  have := D.Cy_nonneg
  have := D.ε_pos
  have : 0 ≤ D.B := by linarith [D.hB]
  unfold C₅₃
  positivity

/-- **(2.53)** for one cube: `|c_S − c_R| |Λ_S(b_S − [v]_S^{-1} v_S, u)| ≤ C₅₃ E_S` for `S ∈ 𝐒∖𝐒₄`
in
no first stopping cube, by (2.10). [PROVED] -/
theorem abs_term_2_53_le (hG : D.GBound) {S : DyadicCube d}
    (hgood' : (D.second R hR hRs hFR).Good S) (hv8 : 1 / 8 < |avg S (D.vP R)|)
    (hSs : D.NotInStopping S) :
    |(D.cS S - D.cS R) * slotForm D.T D.a D.g S (D.yS R S)| ≤ D.C₅₃ * D.E S := by
  have hr0 : 0 < D.r := by linarith [D.hr]
  have hq0 : 0 < D.q := by linarith [D.hq]
  have hB0 : 0 ≤ D.B := by linarith [D.hB]
  have hε := D.ε_pos
  have hV := D.Q.vol_pos
  have hSv := S.vol_pos
  have hF0 := D.Fpos'.le
  have hL0 := D.locConst_nonneg
  have hCy := D.Cy_nonneg
  have hN0 : 0 ≤ lpNorm (D.G : (Fin d → ℝ) → ℝ) D.q := lpNorm_nonneg _ _
  have hu0 : 0 ≤ lpNorm (D.u : (Fin d → ℝ) → ℝ) D.q := lpNorm_nonneg _ _
  have hSt : S ∈ D.tree := D.second_tree_subset hR hRs hFR hgood'.1
  have hgood : D.Good S := D.good_of_notInStopping hSt hSs
  have hSQ : S.toSet ⊆ D.Q.toSet := hSt.1
  set K := D.locConst * D.Q.vol ^ (-(1 / D.q)) * lpNorm (D.G : (Fin d → ℝ) → ℝ) D.q with hK
  have hK0 : 0 ≤ K := by positivity
  have hc : |D.cS S - D.cS R| ≤ 16 * K := by
    calc |D.cS S - D.cS R| ≤ |D.cS S| + |D.cS R| := abs_sub _ _
      _ ≤ 8 * K + 8 * K := add_le_add (D.abs_cS_le hG hSt hSs) (D.abs_cS_le hG hR hRs)
      _ = 16 * K := by ring
  have h10 := D.bound_2_10 D.hd hgood (D.yS R S) (D.yS_supported R hSQ)
    (D.yS_meanZero R hSQ (D.avg_v_ne_of_gt hv8))
  have hy := D.lpNorm_yS_le hR hRs hFR hgood' hv8
  have hu := D.lpNorm_u_le
  have hy0 : 0 ≤ lpNorm (D.yS R S : (Fin d → ℝ) → ℝ) D.r := lpNorm_nonneg _ _
  have hX0 : 0 ≤ (S.vol / D.Q.vol) ^ (1 - 1 / D.r) := Real.rpow_nonneg (by positivity) _
  have hone : D.Q.vol ^ (-(1 / D.q)) * D.Q.vol ^ (1 / D.q) = 1 := by
    rw [← Real.rpow_add hV, neg_add_cancel, Real.rpow_zero]
  rw [abs_mul]
  calc |D.cS S - D.cS R| * |slotForm D.T D.a D.g S (D.yS R S)|
      ≤ (16 * K) * (2 ^ d * (D.B * D.F * (D.B * D.Q.vol) ^ (1 / D.q) * D.ε⁻¹) *
          (S.vol / D.Q.vol) ^ (1 - 1 / D.r) * (D.Cy * S.vol ^ (1 / D.r))) := by
        refine mul_le_mul hc (h10.trans ?_) (abs_nonneg _) (by positivity)
        gcongr
    _ = D.C₅₃ * (D.F * lpNorm (D.G : (Fin d → ℝ) → ℝ) D.q *
          ((D.Q.vol ^ (-(1 / D.q)) * D.Q.vol ^ (1 / D.q)) *
            ((S.vol / D.Q.vol) ^ (1 - 1 / D.r) * S.vol ^ (1 / D.r)))) := by
        unfold C₅₃
        rw [hK, Real.mul_rpow hB0 hV.le, Real.rpow_add' hB0 (by positivity), Real.rpow_one]
        ring
    _ = D.C₅₃ * D.E S := by
        rw [hone, one_mul, rpow_fact1 hSv hV]
        unfold E
        ring

/-- **(2.51)–(2.53)**: for `S ∈ 𝐒∖𝐒₄` in no first stopping cube,
`Λ_S(b_S − [v]_S^{-1} v_S, 𝔤̂) = Λ_S(b_S, ψ_S) − [v]_S^{-1} Λ_S(v, ψ_S) + (c_S − c_R) Λ_S(b_S −
[v]_S^{-1} v_S, u)`.
[PROVED] -/
theorem form2_yS_ghat_eq {S : DyadicCube d} (hSR : S.toSet ⊆ R.toSet) :
    twoSlotForm D.T D.a D.b D.g S (D.yS R S) (D.ghat R) =
      D.form2 S (D.vP S) (D.psi S) -
        (1 / avg S (D.vP R)) * twoSlotForm D.T D.a D.b D.g S (D.vP R) (D.psi S) +
        (D.cS S - D.cS R) * slotForm D.T D.a D.g S (D.yS R S) := by
  rw [← twoSlotForm_truncateₗ_right, D.truncateₗ_ghat_eq hSR, twoSlotForm_add_right,
    twoSlotForm_truncateₗ_right, twoSlotForm_smul_right, twoSlotForm_truncateₗ_right,
    twoSlotForm_self D.T D.hab]
  congr 1
  unfold yS
  rw [twoSlotForm_sub_left D.T D.hab, twoSlotForm_smul_left D.T D.hab, twoSlotForm_truncateₗ_left]
  rfl

/-- The constant of (2.42): `C₄₂ = C₅₀ + C_α + C₅₂ + C₅₃`. -/
noncomputable def C₄₂ : ℝ := D.C₅₀ + D.Cα + D.C₅₂ + D.C₅₃

theorem Cα_nonneg : 0 ≤ D.Cα := by
  have := D.psiConst_nonneg
  have := D.CG_pos
  have : 0 ≤ D.B := by linarith [D.hB]
  unfold Cα
  positivity

theorem C₅₀_nonneg : 0 ≤ D.C₅₀ := by
  have := D.Cy_nonneg
  have := D.Cφ_nonneg
  have := D.locConst_nonneg
  have := D.K₂'_nonneg
  unfold C₅₀
  positivity

theorem C₄₂_nonneg : 0 ≤ D.C₄₂ := by
  have := D.C₅₀_nonneg
  have := D.Cα_nonneg
  have := D.C₅₂_nonneg
  have := D.C₅₃_nonneg
  unfold C₄₂
  positivity

/-- **(2.50)–(2.53) for one cube**: for a good cube `S ⊆ R` of the second stopping time with
`|[v]_S| > 1/8`, `|Λ_S(b_S − [v]_S^{-1} v_S, 𝔤̂)| ≤ C₄₂ E_S`: by (2.50) if `S` lies in a first
stopping cube, by (2.51)–(2.53) otherwise. [PROVED] -/
theorem abs_form2_yS_ghat_le (hG : D.GBound) {S : DyadicCube d}
    (hgood' : (D.second R hR hRs hFR).Good S) (hSR : S.toSet ⊆ R.toSet)
    (hv8 : 1 / 8 < |avg S (D.vP R)|) :
    |twoSlotForm D.T D.a D.b D.g S (D.yS R S) (D.ghat R)| ≤ D.C₄₂ * D.E S := by
  have hE0 : 0 ≤ D.E S := (D.E_pos S).le
  have hSQ : S.toSet ⊆ D.Q.toSet := hSR.trans hR.1
  have hvne := D.avg_v_ne_of_gt hv8
  have hC₅₀ := D.C₅₀_nonneg
  have hCα := D.Cα_nonneg
  have hC₅₂ := D.C₅₂_nonneg
  have hC₅₃ := D.C₅₃_nonneg
  unfold C₄₂
  by_cases hSs : D.NotInStopping S
  · -- `∑''`: (2.51)–(2.53)
    have hSt : S ∈ D.tree := D.second_tree_subset hR hRs hFR hgood'.1
    have h51 : |D.form2 S (D.vP S) (D.psi S)| ≤ D.Cα * D.E S := by
      have := D.abs_form2_v_ghat_le hSt hSs hG
      rwa [ghat_eq, ← form2, D.form2_truncateₗ_right] at this
    have h52 := D.abs_term_2_52_le hR hRs hFR hG hgood' hv8 hSs
    have h53 := D.abs_term_2_53_le hR hRs hFR hG hgood' hv8 hSs
    rw [D.form2_yS_ghat_eq hSR]
    calc |D.form2 S (D.vP S) (D.psi S) -
          (1 / avg S (D.vP R)) * twoSlotForm D.T D.a D.b D.g S (D.vP R) (D.psi S) +
          (D.cS S - D.cS R) * slotForm D.T D.a D.g S (D.yS R S)|
        ≤ |D.form2 S (D.vP S) (D.psi S)| +
          |(1 / avg S (D.vP R)) * twoSlotForm D.T D.a D.b D.g S (D.vP R) (D.psi S)| +
          |(D.cS S - D.cS R) * slotForm D.T D.a D.g S (D.yS R S)| :=
          (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
      _ ≤ D.Cα * D.E S + D.C₅₂ * D.E S + D.C₅₃ * D.E S := add_le_add (add_le_add h51 h52) h53
      _ ≤ (D.C₅₀ + D.Cα + D.C₅₂ + D.C₅₃) * D.E S := by nlinarith
  · -- `∑'`: (2.50)
    have h50 := D.abs_form2_ghat_le_of_inside hR hRs hFR hG hgood' hSR
      (D.exists_stopping_of_not_notInStopping hSs) (D.yS R S) (D.yS_supported R hSQ)
      (D.yS_meanZero R hSQ hvne) (D.lpNorm_yS_le hR hRs hFR hgood' hv8)
    calc |twoSlotForm D.T D.a D.b D.g S (D.yS R S) (D.ghat R)|
        ≤ D.Cy * (D.Cφ + 8 * D.locConst) * D.K₂' * D.E S := h50
      _ = D.C₅₀ * D.E S := by unfold C₅₀; ring
      _ ≤ (D.C₅₀ + D.Cα + D.C₅₂ + D.C₅₃) * D.E S := by nlinarith

/-- **The sum (2.42)** (p. 49–50): `|Λ_R(∑_{S ∈ 𝐒∖𝐒₄} (b_S − [v]_S^{-1} v_S), 𝔤̂)| ≤ C₄₂ E_R`.
[PROVED] -/
theorem abs_form2_sum242_le (hG : D.GBound) :
    |twoSlotForm D.T D.a D.b D.g R (∑ S ∈ (D.second R hR hRs hFR).PstOut4, D.yS R S) (D.ghat R)| ≤
      D.C₄₂ * D.E R := by
  classical
  set D' := D.second R hR hRs hFR with hD'
  have hE0 : ∀ S, 0 ≤ D.E S := fun S => (D.E_pos S).le
  have hsumE : ∑ S ∈ D'.PstOut4, D.E S ≤ D.E R :=
    ((Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun S _ _ => hE0 S).trans
      (D.sum_E_second_le hR hRs hFR)).trans
      (mul_le_of_le_one_left (hE0 R) (by linarith [D.ε_pos]))
  have hC := D.C₄₂_nonneg
  rw [D.form2_sum_yS_eq hR hRs hFR]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ S ∈ D'.PstOut4, |twoSlotForm D.T D.a D.b D.g S (D.yS R S) (D.ghat R)|
      ≤ ∑ S ∈ D'.PstOut4, D.C₄₂ * D.E S := Finset.sum_le_sum fun S hS =>
        D.abs_form2_yS_ghat_le hR hRs hFR hG (D.PstOut4_second_good hR hRs hFR hS)
          (D.PstOut4_second_subset_R hR hRs hFR hS) (D.PstOut4_second_avg_v hR hRs hFR hS)
    _ = D.C₄₂ * ∑ S ∈ D'.PstOut4, D.E S := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hsumE hC

end Sum244'

/-! #### The sum (2.43): the parents `parents(𝐒)₄` and siblings `𝐒₄'` of the second stopping time
(p. 50–51)

The three sums of (2.43) regroup as `∑_{parents(S) ∈ parents(𝐒)₄} Λ_{parents(S)}(ξ^{parents(S)},
𝔤̂)` with the functions `ξ^{parents(S)}` of
(2.54) (the mirror of (2.21)). Expanding `f_j 𝟙_{parents(S)}` over the children of `parents(S)`
and using the decay
condition moves the children's terms to the children, where they are estimated as in (2.42)
and (2.44); the sums involving `[v]_S^{-1} v_S` are written as `b_S − (b_S − [v]_S^{-1} v_S)`. The
local bounds needed on good cubes `S` of the second stopping time (for `u 𝟙_S`, `F_S` and
`𝔤̂ 𝟙_S`) follow from (2.32), (2.35) and the first-stopping-time bounds at `R`. -/

/-- **Expansion over the children for the two-slot form** (p. 50): for `ρ` supported on a child
`c = R.child ε` of `R` and `ρ'` supported on `R`,
`|Λ_R(ρ, ρ') − Λ_c(ρ, ρ')| ≤ n 2^d F_R ‖ρ‖_{p_a} ‖ρ'‖_{p_b}`. [PROVED] -/
theorem abs_twoSlotForm_sub_child_le (T : PerfectCZForm d n) (p : HolderTuple n) {a b : Fin n}
    (hab : a ≠ b) (g : Fin n → TestFun d) (R : DyadicCube d) (ε : Fin d → Bool) {ρ ρ' : TestFun d}
    (hρ : SupportedOn ρ (R.child ε)) (hρ' : SupportedOn ρ' R) :
    |twoSlotForm T a b g R ρ ρ' - twoSlotForm T a b g (R.child ε) ρ ρ'| ≤
      n * 2 ^ d * ((∏ j ∈ (Finset.univ.erase a).erase b,
        lpNorm (TestFun.truncateₗ R (g j) : (Fin d → ℝ) → ℝ) (p.p j)) *
        lpNorm (ρ : (Fin d → ℝ) → ℝ) (p.p a) * lpNorm (ρ' : (Fin d → ℝ) → ℝ) (p.p b)) := by
  have hcR : (R.child ε).toSet ⊆ R.toSet := R.child_subset ε
  have hρR : SupportedOn ρ R := fun x hx => hρ x fun h => hx (hcR h)
  set e : Fin n → TestFun d :=
    Function.update (Function.update (fun j => TestFun.truncateₗ R (g j)) a ρ) b ρ' with he
  have h1 : twoSlotForm T a b g R ρ ρ' = T.form e := by
    unfold twoSlotForm
    rw [TestFun.truncateₗ_of_supportedOn hρR, TestFun.truncateₗ_of_supportedOn hρ']
  have h2 : twoSlotForm T a b g (R.child ε) ρ ρ' =
      T.form (fun j => TestFun.truncateₗ (R.child ε) (e j)) := by
    unfold twoSlotForm
    rw [he, TestFun.truncateₗ_comp_update, TestFun.truncateₗ_comp_update,
      show (fun j => TestFun.truncateₗ (R.child ε) (TestFun.truncateₗ R (g j))) =
        fun j => TestFun.truncateₗ (R.child ε) (g j) from
        funext fun j => TestFun.truncateₗ_truncateₗ_of_subset hcR _]
  have hsupp : ∀ j, SupportedOn (e j) R := by
    intro j
    by_cases hjb : j = b
    · rw [hjb, he, Function.update_self]
      exact hρ'
    · rw [he, Function.update_of_ne hjb]
      by_cases hja : j = a
      · rw [hja, Function.update_self]
        exact hρR
      · rw [Function.update_of_ne hja]
        exact TestFun.truncateₗ_supportedOn R (g j)
  have ha : SupportedOn (e a) (R.child ε) := by
    rw [he, Function.update_of_ne hab, Function.update_self]
    exact hρ
  have h := T.abs_form_sub_truncate_child_le p R ε e a hsupp ha
  rw [h1, h2]
  refine h.trans (le_of_eq ?_)
  rw [he, prodNorm_update_update p hab]

/-- The constant of (2.32)–(2.35) for the mirrored data: `C_G' = 2^d (n+2)/ε`. -/
noncomputable abbrev CGs : ℝ := 2 ^ d * (n + 2) / D.ε

theorem CGs_pos : 0 < D.CGs := by
  have := D.ε_pos
  positivity

/-- `|S|^{1/q} |Q|^{-1/q} = (|S|/|Q|)^{1/q}`. [PROVED] -/
theorem rpow_div_eq {s V q : ℝ} (hs : 0 < s) (hV : 0 < V) :
    s ^ (1 / q) * V ^ (-(1 / q)) = (s / V) ^ (1 / q) := by
  rw [Real.div_rpow hs.le hV.le, Real.rpow_neg hV.le]
  exact (div_eq_mul_inv _ _).symm

section SecondLocal

variable {R : DyadicCube d} (hR : R ∈ D.tree) (hRs : D.NotInStopping R) (hFR : 0 < D.FP R)

/-- **(2.35) in real form**: on a good cube `S` of the second stopping time,
`‖u 𝟙_S‖_q ≤ (C_G' (2^d B/ε) |S|)^{1/q}`. [PROVED] -/
theorem lpNorm_truncateₗ_u_le_second {S : DyadicCube d} (hS : (D.second R hR hRs hFR).Good S) :
    lpNorm (TestFun.truncateₗ S D.u : (Fin d → ℝ) → ℝ) D.q ≤
      (D.CGs * (2 ^ d * D.B / D.ε) * S.vol) ^ (1 / D.q) := by
  have hq0 : 0 < D.q := by linarith [D.hq]
  have hε := D.ε_pos
  have hB0 : 0 ≤ D.B := by linarith [D.hB]
  have hRv := R.vol_pos
  have hR0 : R.vol ≠ 0 := hRv.ne'
  have hSv := S.vol_pos
  have hCGs := D.CGs_pos
  have hSR : S.toSet ⊆ R.toSet := hS.1.1
  have hgoodR : D.Good R := D.good_of_notInStopping hR hRs
  have h := D.second_bound_2_35 hR hRs hFR hS
  have h' := TestFun.setIntegral_rpow_le_of_avg_le (TestFun.truncateₗ R D.u) hq0 S R
    D.CGs_pos.le h
  rw [TestFun.setIntegral_rpow_truncateₗ_eq hSR, TestFun.setIntegral_rpow_truncateₗ_eq
    (subset_refl _)] at h'
  have hu := D.integral_u_rpow_le hgoodR
  refine TestFun.lpNorm_le_rpow_of_integral_le (TestFun.truncateₗ S D.u) hq0 ?_
  rw [← lpNorm_rpow_eq_integral hq0 (TestFun.memLp (TestFun.truncateₗ S D.u).2 _),
    TestFun.lpNorm_truncateₗ_rpow S D.u hq0]
  calc ∫ x in S.toSet, |(D.u : (Fin d → ℝ) → ℝ) x| ^ D.q
      ≤ D.CGs * (S.vol / R.vol) * ∫ x in R.toSet, |(D.u : (Fin d → ℝ) → ℝ) x| ^ D.q := h'
    _ ≤ D.CGs * (S.vol / R.vol) * (2 ^ d * D.B / D.ε * R.vol) :=
        mul_le_mul_of_nonneg_left hu (by positivity)
    _ = D.CGs * (2 ^ d * D.B / D.ε) * S.vol := by
        field_simp

/-- `F_S ≤ (C |S|/|Q'|)^{1-1/r-1/q} F_{Q'}` from average bounds for the entries. [PROVED] -/
theorem FP_le_of_avg {S Q' : DyadicCube d} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ j ∈ D.J, ∫ x in S.toSet, |(D.g j : (Fin d → ℝ) → ℝ) x| ^ D.p.p j ≤
      C * (S.vol / Q'.vol) * ∫ x in Q'.toSet, |(D.g j : (Fin d → ℝ) → ℝ) x| ^ D.p.p j) :
    D.FP S ≤ (C * (S.vol / Q'.vol)) ^ (1 - 1 / D.r - 1 / D.q) * D.FP Q' := by
  have hV := Q'.vol_pos
  have hS0 := S.vol_pos
  have hC' : 0 ≤ C * (S.vol / Q'.vol) := by positivity
  have hpj : ∀ j, 0 < D.p.p j := fun j => by linarith [D.p.one_lt j]
  have hterm : ∀ j ∈ D.J, lpNorm (TestFun.truncateₗ S (D.g j) : (Fin d → ℝ) → ℝ) (D.p.p j) ≤
      (C * (S.vol / Q'.vol)) ^ (1 / D.p.p j) *
        lpNorm (TestFun.truncateₗ Q' (D.g j) : (Fin d → ℝ) → ℝ) (D.p.p j) := by
    intro j hj
    have h2 := TestFun.lpNorm_le_rpow_of_integral_le (TestFun.truncateₗ S (D.g j)) (hpj j)
      (C := C * (S.vol / Q'.vol) *
        lpNorm (TestFun.truncateₗ Q' (D.g j) : (Fin d → ℝ) → ℝ) (D.p.p j) ^ D.p.p j) (by
        rw [← lpNorm_rpow_eq_integral (hpj j) (TestFun.memLp (TestFun.truncateₗ S (D.g j)).2 _),
          TestFun.lpNorm_truncateₗ_rpow S (D.g j) (hpj j),
          TestFun.lpNorm_truncateₗ_rpow Q' (D.g j) (hpj j)]
        exact h j hj)
    refine h2.trans (le_of_eq ?_)
    rw [Real.mul_rpow hC' (Real.rpow_nonneg (lpNorm_nonneg _ _) _), one_div,
      Real.rpow_rpow_inv (lpNorm_nonneg _ _) (hpj j).ne']
  unfold FP
  calc ∏ j ∈ D.J, lpNorm (TestFun.truncateₗ S (D.g j) : (Fin d → ℝ) → ℝ) (D.p.p j)
      ≤ ∏ j ∈ D.J, (C * (S.vol / Q'.vol)) ^ (1 / D.p.p j) *
          lpNorm (TestFun.truncateₗ Q' (D.g j) : (Fin d → ℝ) → ℝ) (D.p.p j) :=
        Finset.prod_le_prod₀ (fun _ _ => lpNorm_nonneg _ _) hterm
    _ = _ := by
        rw [Finset.prod_mul_distrib, ← Real.rpow_sum_of_nonneg hC'
          (fun j _ => one_div_nonneg.mpr (hpj j).le), D.sum_J_inv]

/-- **(2.32) in real form**: on a good cube `S` of the second stopping time,
`F_S ≤ (C_G' C_G |S|/|Q|)^{1-1/r-1/q} F`. [PROVED] -/
theorem FP_le_second {S : DyadicCube d} (hS : (D.second R hR hRs hFR).Good S) :
    D.FP S ≤ (D.CGs * D.CG * (S.vol / D.Q.vol)) ^ (1 - 1 / D.r - 1 / D.q) * D.F := by
  have hV := D.Q.vol_pos
  have hRv := R.vol_pos
  have hSv := S.vol_pos
  have hCG := D.CG_pos
  have hCGs := D.CGs_pos
  have hF0 := D.Fpos'.le
  have hSR : S.toSet ⊆ R.toSet := hS.1.1
  have hgoodR : D.Good R := D.good_of_notInStopping hR hRs
  have hpj : ∀ j, 0 < D.p.p j := fun j => by linarith [D.p.one_lt j]
  have h1 : D.FP S ≤ (D.CGs * (S.vol / R.vol)) ^ (1 - 1 / D.r - 1 / D.q) * D.FP R := by
    refine D.FP_le_of_avg hCGs.le fun j hj => ?_
    have h := TestFun.setIntegral_rpow_le_of_avg_le (TestFun.truncateₗ R (D.g j)) (hpj j) S R
      hCGs.le (D.second_bound_2_32 hR hRs hFR hS hj)
    rwa [TestFun.setIntegral_rpow_truncateₗ_eq hSR, TestFun.setIntegral_rpow_truncateₗ_eq
      (subset_refl _)] at h
  have h2 := D.FP_le hgoodR
  have hx : D.CGs * (S.vol / R.vol) * (D.CG * (R.vol / D.Q.vol)) =
      D.CGs * D.CG * (S.vol / D.Q.vol) := by
    have : S.vol / R.vol * (R.vol / D.Q.vol) = S.vol / D.Q.vol := by
      rw [div_mul_div_comm, mul_comm S.vol R.vol, mul_div_mul_left _ _ hRv.ne']
    rw [← this]
    ring
  calc D.FP S ≤ (D.CGs * (S.vol / R.vol)) ^ (1 - 1 / D.r - 1 / D.q) * D.FP R := h1
    _ ≤ (D.CGs * (S.vol / R.vol)) ^ (1 - 1 / D.r - 1 / D.q) *
          ((D.CG * (R.vol / D.Q.vol)) ^ (1 - 1 / D.r - 1 / D.q) * D.F) :=
        mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg (by positivity) _)
    _ = _ := by
        rw [← mul_assoc, ← Real.mul_rpow (by positivity) (by positivity), hx]

/-- The constant of the local bound for `𝔤̂` on good cubes of the second stopping time:
`C_𝔤̂ = C_ψ + (C_φ + 24 C_loc) (C_G' 2^d B/ε)^{1/q}`. -/
noncomputable def Cghat : ℝ :=
  D.psiConst + (D.Cφ + 24 * D.locConst) * (D.CGs * (2 ^ d * D.B / D.ε)) ^ (1 / D.q)

theorem Cghat_nonneg : 0 ≤ D.Cghat := by
  have := D.psiConst_nonneg
  have := D.Cφ_nonneg
  have := D.locConst_nonneg
  have := D.ε_pos
  have : 0 ≤ D.B := by linarith [D.hB]
  unfold Cghat
  positivity

/-- **The local bound for `𝔤̂`**: on a good cube `S` of the second stopping time,
`‖𝔤̂ 𝟙_S‖_q ≤ C_𝔤̂ (|S|/|Q|)^{1/q} ‖g‖_q`: with `𝔤̂ = ψ_S + (c_S − c_R) u` on `S` if `S` lies in no
first
stopping cube, and `𝔤̂ = (φ_S − c_R) u` on `S` otherwise. [PROVED] -/
theorem lpNorm_truncateₗ_ghat_le (hG : D.GBound) {S : DyadicCube d}
    (hS : (D.second R hR hRs hFR).Good S) :
    lpNorm (TestFun.truncateₗ S (D.ghat R) : (Fin d → ℝ) → ℝ) D.q ≤
      D.Cghat * (S.vol / D.Q.vol) ^ (1 / D.q) * lpNorm (D.G : (Fin d → ℝ) → ℝ) D.q := by
  have hq1 : 1 ≤ D.q := D.hq.le
  have hq0 : 0 < D.q := by linarith
  have hε := D.ε_pos
  have hB0 : 0 ≤ D.B := by linarith [D.hB]
  have hV := D.Q.vol_pos
  have hSv := S.vol_pos
  have hSR : S.toSet ⊆ R.toSet := hS.1.1
  have hL := D.locConst_nonneg
  have hCφ := D.Cφ_nonneg
  have hψ := D.psiConst_nonneg
  set N := lpNorm (D.G : (Fin d → ℝ) → ℝ) D.q with hN
  have hN0 : 0 ≤ N := lpNorm_nonneg _ _
  set ρ : ℝ := (S.vol / D.Q.vol) ^ (1 / D.q) with hρ
  have hρ0 : 0 ≤ ρ := Real.rpow_nonneg (by positivity) _
  set c₉ : ℝ := (D.CGs * (2 ^ d * D.B / D.ε)) ^ (1 / D.q) with hc₉
  have hc₉0 : 0 ≤ c₉ := Real.rpow_nonneg (by positivity) _
  have hu : lpNorm (TestFun.truncateₗ S D.u : (Fin d → ℝ) → ℝ) D.q ≤ c₉ * S.vol ^ (1 / D.q) := by
    have := D.lpNorm_truncateₗ_u_le_second hR hRs hFR hS
    rwa [Real.mul_rpow (by positivity) hSv.le] at this
  have hρeq : S.vol ^ (1 / D.q) * D.Q.vol ^ (-(1 / D.q)) = ρ := rpow_div_eq hSv hV
  by_cases hSs : D.NotInStopping S
  · have hSt : S ∈ D.tree := D.second_tree_subset hR hRs hFR hS.1
    set K := D.locConst * D.Q.vol ^ (-(1 / D.q)) * N with hK
    have hc : |D.cS S - D.cS R| ≤ 16 * K := by
      calc |D.cS S - D.cS R| ≤ |D.cS S| + |D.cS R| := abs_sub _ _
        _ ≤ 8 * K + 8 * K := add_le_add (D.abs_cS_le hG hSt hSs) (D.abs_cS_le hG hR hRs)
        _ = 16 * K := by ring
    have hψS := D.lpNorm_truncateₗ_psi_le hG hSt hSs
    rw [D.truncateₗ_ghat_eq hSR]
    refine (TestFun.lpNorm_add_le _ _ hq1).trans ?_
    rw [TestFun.lpNorm_smul]
    calc lpNorm (TestFun.truncateₗ S (D.psi S) : (Fin d → ℝ) → ℝ) D.q +
          |D.cS S - D.cS R| * lpNorm (TestFun.truncateₗ S D.u : (Fin d → ℝ) → ℝ) D.q
        ≤ D.psiConst * ρ * N + (16 * K) * (c₉ * S.vol ^ (1 / D.q)) :=
          add_le_add hψS (mul_le_mul hc hu (lpNorm_nonneg _ _) (by positivity))
      _ = (D.psiConst + 16 * D.locConst * c₉) * ρ * N := by
          rw [hK, ← hρeq]
          ring
      _ ≤ D.Cghat * ρ * N := by
          unfold Cghat
          rw [← hc₉]
          have : 16 * D.locConst * c₉ ≤ (D.Cφ + 24 * D.locConst) * c₉ := by nlinarith
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hρ0) hN0
  · obtain ⟨P, hP, hSP⟩ := D.exists_stopping_of_not_notInStopping hSs
    obtain ⟨φ, hφ, hφb⟩ := D.exists_phi hG hP hSP
    have hcR := D.abs_cS_le hG hR hRs
    have hcoef : |φ - D.cS R| ≤ (D.Cφ + 8 * D.locConst) * D.Q.vol ^ (-(1 / D.q)) * N := by
      calc |φ - D.cS R| ≤ |φ| + |D.cS R| := abs_sub _ _
        _ ≤ D.Cφ * D.Q.vol ^ (-(1 / D.q)) * N +
            8 * (D.locConst * D.Q.vol ^ (-(1 / D.q)) * N) := add_le_add hφb hcR
        _ = _ := by ring
    rw [D.truncateₗ_ghat_eq_phi hSR hφ, TestFun.lpNorm_smul]
    calc |φ - D.cS R| * lpNorm (TestFun.truncateₗ S D.u : (Fin d → ℝ) → ℝ) D.q
        ≤ ((D.Cφ + 8 * D.locConst) * D.Q.vol ^ (-(1 / D.q)) * N) * (c₉ * S.vol ^ (1 / D.q)) :=
          mul_le_mul hcoef hu (lpNorm_nonneg _ _) (by positivity)
      _ = (D.Cφ + 8 * D.locConst) * c₉ * ρ * N := by
          rw [← hρeq]
          ring
      _ ≤ D.Cghat * ρ * N := by
          unfold Cghat
          rw [← hc₉]
          have : (D.Cφ + 8 * D.locConst) * c₉ ≤ (D.Cφ + 24 * D.locConst) * c₉ := by nlinarith
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hρ0) hN0

/-- The constant of the testing-type term `Λ_S(b_S, 𝔤̂)`:
`C_v = B^{1+1/r} (C_G' C_G)^{1-1/r-1/q} C_𝔤̂`. -/
noncomputable def Cv : ℝ :=
  D.B ^ (1 + 1 / D.r) * (D.CGs * D.CG) ^ (1 - 1 / D.r - 1 / D.q) * D.Cghat

theorem Cv_nonneg : 0 ≤ D.Cv := by
  have := D.Cghat_nonneg
  have := D.CG_pos
  have := D.CGs_pos
  have : 0 ≤ D.B := by linarith [D.hB]
  unfold Cv
  positivity

/-- **The testing-type term**: for a good cube `S` of the second stopping time,
`|Λ_S(b_S, 𝔤̂)| ≤ C_v E_S`, by the testing condition (1.9) for `τ`, `𝐐_S` and the local bounds
for `F_S` and `𝔤̂ 𝟙_S`. [PROVED] -/
theorem abs_form2_vP_ghat_le (hG : D.GBound) {S : DyadicCube d}
    (hS : (D.second R hR hRs hFR).Good S) :
    |twoSlotForm D.T D.a D.b D.g S (D.vP S) (D.ghat R)| ≤ D.Cv * D.E S := by
  have hr0 : 0 < D.r := by linarith [D.hr]
  have hq0 : 0 < D.q := by linarith [D.hq]
  have hB0 : 0 ≤ D.B := by linarith [D.hB]
  have hV := D.Q.vol_pos
  have hSv := S.vol_pos
  have hCG := D.CG_pos
  have hCGs := D.CGs_pos
  have hF0 := D.Fpos'.le
  have hĝ0 := D.Cghat_nonneg
  have hN0 : 0 ≤ lpNorm (D.G : (Fin d → ℝ) → ℝ) D.q := lpNorm_nonneg _ _
  have hSQ : S.toSet ⊆ D.Q.toSet := hS.1.1.trans hR.1
  have ht := D.testing_vP S hSQ (TestFun.truncateₗ S (D.ghat R))
    (TestFun.truncateₗ_supportedOn S _)
  rw [twoSlotForm_truncateₗ_right] at ht
  have hFP := D.FP_le_second hR hRs hFR hS
  have hv := D.lpNorm_vP_le hSQ
  have hĝ := D.lpNorm_truncateₗ_ghat_le hR hRs hFR hG hS
  have hFP0 := D.FP_nonneg S
  have hv0 : 0 ≤ lpNorm (D.vP S : (Fin d → ℝ) → ℝ) D.r := lpNorm_nonneg _ _
  have hg0 : 0 ≤ lpNorm (TestFun.truncateₗ S (D.ghat R) : (Fin d → ℝ) → ℝ) D.q := lpNorm_nonneg _ _
  set x : ℝ := S.vol / D.Q.vol with hx
  have hx0 : 0 < x := by positivity
  have hexp : x ^ (1 - 1 / D.r - 1 / D.q) * S.vol ^ (1 / D.r) * x ^ (1 / D.q) =
      S.vol * D.Q.vol ^ (1 / D.r - 1) := by
    rw [mul_right_comm, ← Real.rpow_add hx0,
      show 1 - 1 / D.r - 1 / D.q + 1 / D.q = 1 - 1 / D.r by ring, hx, rpow_fact1 hSv hV]
  calc |twoSlotForm D.T D.a D.b D.g S (D.vP S) (D.ghat R)|
      ≤ D.B * D.FP S * lpNorm (D.vP S : (Fin d → ℝ) → ℝ) D.r *
          lpNorm (TestFun.truncateₗ S (D.ghat R) : (Fin d → ℝ) → ℝ) D.q := ht
    _ ≤ D.B * ((D.CGs * D.CG * x) ^ (1 - 1 / D.r - 1 / D.q) * D.F) * (D.B * S.vol) ^ (1 / D.r) *
          (D.Cghat * x ^ (1 / D.q) * lpNorm (D.G : (Fin d → ℝ) → ℝ) D.q) := by gcongr
    _ = D.Cv * (D.F * lpNorm (D.G : (Fin d → ℝ) → ℝ) D.q *
          (x ^ (1 - 1 / D.r - 1 / D.q) * S.vol ^ (1 / D.r) * x ^ (1 / D.q))) := by
        unfold Cv
        rw [Real.mul_rpow (by positivity) hx0.le, Real.mul_rpow hB0 hSv.le,
          Real.rpow_add' hB0 (by positivity), Real.rpow_one]
        ring
    _ = D.Cv * D.E S := by
        rw [hexp]
        unfold E
        ring

end SecondLocal

section Sum243

variable {R : DyadicCube d} (hR : R ∈ D.tree) (hRs : D.NotInStopping R) (hFR : 0 < D.FP R)

theorem Pbar4_second_good {R' : DyadicCube d} (hR' : R' ∈ (D.second R hR hRs hFR).Pbar4) :
    (D.second R hR hRs hFR).Good R' := (D.second R hR hRs hFR).good_of_Pbar4 hR'

theorem Pbar4_second_avg_v {R' : DyadicCube d} (hR' : R' ∈ (D.second R hR hRs hFR).Pbar4) :
    1 / 8 < |avg R' (D.vP R)| :=
  D.second_bound_2_30 hR hRs hFR ((D.second R hR hRs hFR).Pbar4_mem_tree hR')
    ((D.second R hR hRs hFR).Pbar4_not_in_P4 hR')

theorem Psib4_second_good {c : DyadicCube d} (hc : c ∈ (D.second R hR hRs hFR).Psib4) :
    (D.second R hR hRs hFR).Good c := (D.second R hR hRs hFR).good_of_Psib4 hc

theorem Psib4_second_avg_v {c : DyadicCube d} (hc : c ∈ (D.second R hR hRs hFR).Psib4) :
    1 / 8 < |avg c (D.vP R)| :=
  D.second_bound_2_30 hR hRs hFR ((D.second R hR hRs hFR).Psib4_mem_tree hc)
    ((D.second R hR hRs hFR).Psib4_not_in_P4 hc)

theorem PstIn4_second_good {c : DyadicCube d} (hc : c ∈ (D.second R hR hRs hFR).PstIn4) :
    (D.second R hR hRs hFR).Good c :=
  (D.second R hR hRs hFR).good_of_mem_stoppingCubes ((D.second R hR hRs hFR).mem_PstIn4.mp hc).1

/-- `[v]_S^{-1} v_S = b_S − (b_S − [v]_S^{-1} v_S)`. [PROVED] -/
theorem smul_truncateₗ_vP_eq (S : DyadicCube d) :
    (1 / avg S (D.vP R)) • TestFun.truncateₗ S (D.vP R) = D.vP S - D.yS R S := by
  unfold yS
  rw [sub_sub_cancel]

/-- **(2.43) regrouped over the parents** (the mirror of (2.21), (2.54)):
`∑_{S ∈ 𝐒∩𝐒₄} b_S − ∑_{S ∈ parents(𝐒)₄} [v]_S^{-1} v_S + ∑_{S ∈ 𝐒₄'} [v]_S^{-1} v_S =
∑_{parents(S) ∈ parents(𝐒)₄} ξ^{parents(S)}`.
[PROVED] -/
theorem sum243_eq :
    ∑ S ∈ (D.second R hR hRs hFR).PstIn4, D.vP S
      - ∑ S ∈ (D.second R hR hRs hFR).Pbar4, (1 / avg S (D.vP R)) • TestFun.truncateₗ S (D.vP R)
      + ∑ S ∈ (D.second R hR hRs hFR).Psib4, (1 / avg S (D.vP R)) • TestFun.truncateₗ S (D.vP R) =
      ∑ R' ∈ (D.second R hR hRs hFR).Pbar4, (D.second R hR hRs hFR).xi R' := by
  classical
  rw [(D.second R hR hRs hFR).sum_xi_eq]
  have hu : (D.second R hR hRs hFR).u = D.vP R := second_u _ _ _ _
  have hG : (D.second R hR hRs hFR).G = TestFun.ind R := rfl
  have hbP : (D.second R hR hRs hFR).bP = D.vP := rfl
  rw [hu, hG, hbP]
  have e3 : ∑ P ∈ (D.second R hR hRs hFR).PstIn4, avg P (TestFun.ind R) • D.vP P =
      ∑ S ∈ (D.second R hR hRs hFR).PstIn4, D.vP S :=
    Finset.sum_congr rfl fun S hS => by
      rw [avg_ind_of_subset (R := R)
        ((D.second R hR hRs hFR).Pst_subset_Q (Finset.mem_of_mem_filter S hS)), one_smul]
  have e4 : ∑ P ∈ (D.second R hR hRs hFR).Pbar4,
      (D.second R hR hRs hFR).coef P • TestFun.truncateₗ P (D.vP R) =
      ∑ S ∈ (D.second R hR hRs hFR).Pbar4, (1 / avg S (D.vP R)) • TestFun.truncateₗ S (D.vP R) :=
    Finset.sum_congr rfl fun S hS => by
      rw [D.second_coef hR hRs hFR ((D.second R hR hRs hFR).Pbar4_subset_Q hS)]
  have e5 : ∑ P ∈ (D.second R hR hRs hFR).Psib4,
      (D.second R hR hRs hFR).coef P • TestFun.truncateₗ P (D.vP R) =
      ∑ S ∈ (D.second R hR hRs hFR).Psib4, (1 / avg S (D.vP R)) • TestFun.truncateₗ S (D.vP R) :=
    Finset.sum_congr rfl fun S hS => by
      rw [D.second_coef hR hRs hFR ((D.second R hR hRs hFR).Psib4_subset_Q hS)]
  rw [e3, e4, e5]

/-- `Λ_{parents(S)}(ξ^{parents(S)}, 𝔤̂)` expanded (the mirror of (2.22), (2.55)): over the
children `c` of `parents(S)`,
`Λ_{parents(S)}(b_c, 𝔤̂)` for `c ∈ 𝐒∩𝐒₄` and `Λ_{parents(S)}(b_c − (b_c − [v]_c^{-1} v_c), 𝔤̂)`
for the siblings,
minus
`Λ_{parents(S)}(b_{parents(S)} − (b_{parents(S)} − [v]_{parents(S)}^{-1} v_{parents(S)}), 𝔤̂)`.
[PROVED] -/
theorem form2_xi2_eq {R' : DyadicCube d} (hR' : R' ∈ (D.second R hR hRs hFR).Pbar4) :
    twoSlotForm D.T D.a D.b D.g R' ((D.second R hR hRs hFR).xi R') (D.ghat R) =
      ∑ c ∈ children R', (if c ∈ (D.second R hR hRs hFR).PstIn4 then
          twoSlotForm D.T D.a D.b D.g R' (D.vP c) (D.ghat R)
        else twoSlotForm D.T D.a D.b D.g R' (D.vP c - D.yS R c) (D.ghat R))
      - twoSlotForm D.T D.a D.b D.g R' (D.vP R' - D.yS R R') (D.ghat R) := by
  have hR'R : R'.toSet ⊆ R.toSet := (D.second R hR hRs hFR).Pbar4_subset_Q hR'
  have hu : (D.second R hR hRs hFR).u = D.vP R := second_u _ _ _ _
  have hG : (D.second R hR hRs hFR).G = TestFun.ind R := rfl
  have hbP : (D.second R hR hRs hFR).bP = D.vP := rfl
  unfold xi
  rw [hu, hG, hbP, twoSlotForm_sub_left D.T D.hab, twoSlotForm_sum_left D.T D.hab,
    D.second_coef hR hRs hFR hR'R, D.smul_truncateₗ_vP_eq]
  congr 1
  refine Finset.sum_congr rfl fun c hc => ?_
  obtain ⟨ε, rfl⟩ := mem_children.mp hc
  have hcR : (R'.child ε).toSet ⊆ R.toSet := (R'.child_subset ε).trans hR'R
  split_ifs with h
  · rw [avg_ind_of_subset hcR, one_smul]
  · rw [D.second_coef hR hRs hFR hcR, D.smul_truncateₗ_vP_eq]

/-- The constant of the decay residual: `C_res = n 2^d (C_G' C_G)^{1-1/r-1/q} C_𝔤̂`. -/
noncomputable def Cres : ℝ := n * 2 ^ d * (D.CGs * D.CG) ^ (1 - 1 / D.r - 1 / D.q) * D.Cghat

theorem Cres_nonneg : 0 ≤ D.Cres := by
  have := D.Cghat_nonneg
  have := D.CG_pos
  have := D.CGs_pos
  unfold Cres
  positivity

/-- **The decay residual** (p. 50): for a good cube `parents(S)` of the second stopping time, a
child
`c = parents(S).child ε` and `x` supported on `c` with `‖x‖_r ≤ c_x |c|^{1/r}`,
`|Λ_{parents(S)}(x, 𝔤̂) − Λ_c(x, 𝔤̂)| ≤ c_x C_res E_{parents(S)}`. [PROVED] -/
theorem abs_residual_le (hG : D.GBound) {R' : DyadicCube d}
    (hR' : (D.second R hR hRs hFR).Good R') (ε : Fin d → Bool) {x : TestFun d}
    (hx : SupportedOn x (R'.child ε)) {cx : ℝ} (hcx : 0 ≤ cx)
    (hxn : lpNorm (x : (Fin d → ℝ) → ℝ) D.r ≤ cx * (R'.child ε).vol ^ (1 / D.r)) :
    |twoSlotForm D.T D.a D.b D.g R' x (D.ghat R) -
        twoSlotForm D.T D.a D.b D.g (R'.child ε) x (D.ghat R)| ≤ cx * D.Cres * D.E R' := by
  have hr0 : 0 < D.r := by linarith [D.hr]
  have hq0 : 0 < D.q := by linarith [D.hq]
  have hV := D.Q.vol_pos
  have hRv := R'.vol_pos
  have hcv := (R'.child ε).vol_pos
  have hCG := D.CG_pos
  have hCGs := D.CGs_pos
  have hF0 := D.Fpos'.le
  have hĝ0 := D.Cghat_nonneg
  have hN0 : 0 ≤ lpNorm (D.G : (Fin d → ℝ) → ℝ) D.q := lpNorm_nonneg _ _
  have hcR : (R'.child ε).toSet ⊆ R'.toSet := R'.child_subset ε
  have hvol : (R'.child ε).vol ≤ R'.vol := DyadicCube.vol_le_of_subset hcR
  have hx0 : 0 ≤ lpNorm (x : (Fin d → ℝ) → ℝ) D.r := lpNorm_nonneg _ _
  have hĝ := D.lpNorm_truncateₗ_ghat_le hR hRs hFR hG hR'
  have hFP := D.FP_le_second hR hRs hFR hR'
  have hFP0 := D.FP_nonneg R'
  have hg0 : 0 ≤ lpNorm (TestFun.truncateₗ R' (D.ghat R) : (Fin d → ℝ) → ℝ) D.q := lpNorm_nonneg _ _
  -- rewrite both forms with `𝔤̂ 𝟙_{parents(S)}` in the slot `k+1`
  have e1 : twoSlotForm D.T D.a D.b D.g R' x (D.ghat R) =
      twoSlotForm D.T D.a D.b D.g R' x (TestFun.truncateₗ R' (D.ghat R)) :=
    (twoSlotForm_truncateₗ_right _ _ _ _ _ _ _).symm
  have e2 : twoSlotForm D.T D.a D.b D.g (R'.child ε) x (D.ghat R) =
      twoSlotForm D.T D.a D.b D.g (R'.child ε) x (TestFun.truncateₗ R' (D.ghat R)) := by
    conv_rhs => rw [← twoSlotForm_truncateₗ_right, TestFun.truncateₗ_truncateₗ_of_subset hcR,
      twoSlotForm_truncateₗ_right]
  rw [e1, e2]
  have h := abs_twoSlotForm_sub_child_le D.T D.p D.hab D.g R' ε hx
    (TestFun.truncateₗ_supportedOn R' (D.ghat R))
  refine h.trans ?_
  set xq : ℝ := R'.vol / D.Q.vol with hxq
  have hxq0 : 0 < xq := by positivity
  have hcx' : lpNorm (x : (Fin d → ℝ) → ℝ) D.r ≤ cx * R'.vol ^ (1 / D.r) :=
    hxn.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hcv.le hvol (by positivity)) hcx)
  have hexp : xq ^ (1 - 1 / D.r - 1 / D.q) * R'.vol ^ (1 / D.r) * xq ^ (1 / D.q) =
      R'.vol * D.Q.vol ^ (1 / D.r - 1) := by
    rw [mul_right_comm, ← Real.rpow_add hxq0,
      show 1 - 1 / D.r - 1 / D.q + 1 / D.q = 1 - 1 / D.r by ring, hxq, rpow_fact1 hRv hV]
  calc (n : ℝ) * 2 ^ d * (D.FP R' * lpNorm (x : (Fin d → ℝ) → ℝ) D.r *
        lpNorm (TestFun.truncateₗ R' (D.ghat R) : (Fin d → ℝ) → ℝ) D.q)
      ≤ (n : ℝ) * 2 ^ d * (((D.CGs * D.CG * xq) ^ (1 - 1 / D.r - 1 / D.q) * D.F) *
          (cx * R'.vol ^ (1 / D.r)) *
          (D.Cghat * xq ^ (1 / D.q) * lpNorm (D.G : (Fin d → ℝ) → ℝ) D.q)) := by gcongr
    _ = cx * D.Cres * (D.F * lpNorm (D.G : (Fin d → ℝ) → ℝ) D.q *
          (xq ^ (1 - 1 / D.r - 1 / D.q) * R'.vol ^ (1 / D.r) * xq ^ (1 / D.q))) := by
        unfold Cres
        rw [Real.mul_rpow (by positivity) hxq0.le]
        ring
    _ = cx * D.Cres * D.E R' := by
        rw [hexp]
        unfold E
        ring

/-- **A child of `𝐒∩𝐒₄`** (the first sum of (2.55)): for `c = parents(S).child ε ∈ 𝐒∩𝐒₄`,
`|Λ_{parents(S)}(b_c, 𝔤̂)| ≤ C_v E_c + B^{1/r} C_res E_{parents(S)}`. [PROVED] -/
theorem abs_child_In4_le (hG : D.GBound) {R' : DyadicCube d}
    (hR' : (D.second R hR hRs hFR).Good R') (ε : Fin d → Bool)
    (hc : R'.child ε ∈ (D.second R hR hRs hFR).PstIn4) :
    |twoSlotForm D.T D.a D.b D.g R' (D.vP (R'.child ε)) (D.ghat R)| ≤
      D.Cv * D.E (R'.child ε) + D.B ^ (1 / D.r) * D.Cres * D.E R' := by
  have hB0 : 0 ≤ D.B := by linarith [D.hB]
  have hcg := D.PstIn4_second_good hR hRs hFR hc
  have hcQ : (R'.child ε).toSet ⊆ D.Q.toSet := hcg.1.1.trans hR.1
  have h1 := D.abs_form2_vP_ghat_le hR hRs hFR hG hcg
  have h2 := D.abs_residual_le hR hRs hFR hG hR' ε (D.vP_supp _ hcQ) (Real.rpow_nonneg hB0 _)
    (by rw [← Real.mul_rpow hB0 (R'.child ε).vol_pos.le]; exact D.lpNorm_vP_le hcQ)
  have := abs_sub_abs_le_abs_sub (twoSlotForm D.T D.a D.b D.g R' (D.vP (R'.child ε)) (D.ghat R))
    (twoSlotForm D.T D.a D.b D.g (R'.child ε) (D.vP (R'.child ε)) (D.ghat R))
  linarith

/-- The constant `C_{sib} = C_v + C₄₂`. -/
noncomputable def Csib : ℝ := D.Cv + D.C₄₂

/-- **A term `Λ_S(b_S − (b_S − [v]_S^{-1} v_S), 𝔤̂) = Λ_S([v]_S^{-1} v_S, 𝔤̂)`** for a good cube `S`
of
the second stopping time with `|[v]_S| > 1/8`: at most `(C_v + C₄₂) E_S`. [PROVED] -/
theorem abs_form2_vP_sub_yS_le (hG : D.GBound) {S : DyadicCube d}
    (hS : (D.second R hR hRs hFR).Good S) (hv8 : 1 / 8 < |avg S (D.vP R)|) :
    |twoSlotForm D.T D.a D.b D.g S (D.vP S - D.yS R S) (D.ghat R)| ≤ D.Csib * D.E S := by
  rw [twoSlotForm_sub_left D.T D.hab]
  have h1 := D.abs_form2_vP_ghat_le hR hRs hFR hG hS
  have h2 := D.abs_form2_yS_ghat_le hR hRs hFR hG hS hS.1.1 hv8
  unfold Csib
  have := abs_sub (twoSlotForm D.T D.a D.b D.g S (D.vP S) (D.ghat R))
    (twoSlotForm D.T D.a D.b D.g S (D.yS R S) (D.ghat R))
  linarith

/-- `‖[v]_c^{-1} v_c‖_r ≤ 8 (2^d B/ε)^{1/r} |c|^{1/r}` for a good cube `c` of the second stopping
time with `|[v]_c| > 1/8`, by (2.34). [PROVED] -/
theorem lpNorm_vP_sub_yS_le {c : DyadicCube d} (hc : (D.second R hR hRs hFR).Good c)
    (hv8 : 1 / 8 < |avg c (D.vP R)|) :
    lpNorm ((D.vP c - D.yS R c : TestFun d) : (Fin d → ℝ) → ℝ) D.r ≤
      8 * (2 ^ d * D.B / D.ε) ^ (1 / D.r) * c.vol ^ (1 / D.r) := by
  have hB0 : 0 ≤ D.B := by linarith [D.hB]
  have hε := D.ε_pos
  have hcv := c.vol_pos
  rw [← D.smul_truncateₗ_vP_eq, TestFun.lpNorm_smul]
  have hv : lpNorm (TestFun.truncateₗ c (D.vP R) : (Fin d → ℝ) → ℝ) D.r ≤
      (2 ^ d * D.B / D.ε * c.vol) ^ (1 / D.r) := by
    have h := (D.second R hR hRs hFR).lpNorm_truncateₗ_u_le hc
    rw [second_u] at h
    exact h
  have hc8 : |1 / avg c (D.vP R)| ≤ 8 := by
    rw [abs_div, abs_one, div_le_iff₀ (by linarith)]
    linarith
  calc |1 / avg c (D.vP R)| * lpNorm (TestFun.truncateₗ c (D.vP R) : (Fin d → ℝ) → ℝ) D.r
      ≤ 8 * (2 ^ d * D.B / D.ε * c.vol) ^ (1 / D.r) :=
        mul_le_mul hc8 hv (lpNorm_nonneg _ _) (by norm_num)
    _ = _ := by rw [Real.mul_rpow (by positivity) hcv.le, mul_assoc]

/-- **A sibling child** (the third sum of (2.55)): for `c = parents(S).child ε ∈ 𝐒₄'`,
`|Λ_{parents(S)}([v]_c^{-1} v_c, 𝔤̂)| ≤ C_{sib} E_c + 8 (2^d B/ε)^{1/r} C_res E_{parents(S)}`.
[PROVED] -/
theorem abs_child_sib_le (hG : D.GBound) {R' : DyadicCube d}
    (hR' : (D.second R hR hRs hFR).Good R') (ε : Fin d → Bool)
    (hc : R'.child ε ∈ (D.second R hR hRs hFR).Psib4) :
    |twoSlotForm D.T D.a D.b D.g R' (D.vP (R'.child ε) - D.yS R (R'.child ε)) (D.ghat R)| ≤
      D.Csib * D.E (R'.child ε) + 8 * (2 ^ d * D.B / D.ε) ^ (1 / D.r) * D.Cres * D.E R' := by
  have hB0 : 0 ≤ D.B := by linarith [D.hB]
  have hε := D.ε_pos
  have hcg := D.Psib4_second_good hR hRs hFR hc
  have hv8 := D.Psib4_second_avg_v hR hRs hFR hc
  have hcQ : (R'.child ε).toSet ⊆ D.Q.toSet := hcg.1.1.trans hR.1
  have hsupp : SupportedOn ((D.vP (R'.child ε) - D.yS R (R'.child ε) : TestFun d) :
      (Fin d → ℝ) → ℝ) (R'.child ε) := by
    rw [← D.smul_truncateₗ_vP_eq]
    intro x hx
    rw [Submodule.coe_smul, Pi.smul_apply, TestFun.truncateₗ_supportedOn _ _ x hx, smul_zero]
  have h1 := D.abs_form2_vP_sub_yS_le hR hRs hFR hG hcg hv8
  have h2 := D.abs_residual_le hR hRs hFR hG hR' ε hsupp (by positivity)
    (D.lpNorm_vP_sub_yS_le hR hRs hFR hcg hv8)
  have := abs_sub_abs_le_abs_sub
    (twoSlotForm D.T D.a D.b D.g R' (D.vP (R'.child ε) - D.yS R (R'.child ε)) (D.ghat R))
    (twoSlotForm D.T D.a D.b D.g (R'.child ε) (D.vP (R'.child ε) - D.yS R (R'.child ε)) (D.ghat R))
  linarith

/-- **The bound for `Λ_{parents(S)}(ξ^{parents(S)}, 𝔤̂)`** for a parent `parents(S) ∈ parents(𝐒)₄`:
`∑_{children c ∈ 𝐒∩𝐒₄} C_v E_c + ∑_{children c ∈ 𝐒₄'} C_{sib} E_c + (2^d C_y C_res + C_{sib})
E_{parents(S)}`.
[PROVED] -/
theorem abs_form2_xi2_le (hG : D.GBound) {R' : DyadicCube d}
    (hR' : R' ∈ (D.second R hR hRs hFR).Pbar4) :
    |twoSlotForm D.T D.a D.b D.g R' ((D.second R hR hRs hFR).xi R') (D.ghat R)| ≤
      ∑ c ∈ children R', (if c ∈ (D.second R hR hRs hFR).PstIn4 then D.Cv * D.E c
        else D.Csib * D.E c) + (2 ^ d * D.Cy * D.Cres + D.Csib) * D.E R' := by
  have hgood := D.Pbar4_second_good hR hRs hFR hR'
  have hB0 : 0 ≤ D.B := by linarith [D.hB]
  have hε := D.ε_pos
  have hCres := D.Cres_nonneg
  have hE0 := (D.E_pos R').le
  have hCy := D.Cy_nonneg
  -- each child contributes its own term plus at most `C_y C_res E_{parents(S)}` of residual
  have hchild : ∀ c ∈ children R',
      |if c ∈ (D.second R hR hRs hFR).PstIn4 then
          twoSlotForm D.T D.a D.b D.g R' (D.vP c) (D.ghat R)
        else twoSlotForm D.T D.a D.b D.g R' (D.vP c - D.yS R c) (D.ghat R)| ≤
      (if c ∈ (D.second R hR hRs hFR).PstIn4 then D.Cv * D.E c else D.Csib * D.E c) +
        D.Cy * D.Cres * D.E R' := by
    intro c hc
    obtain ⟨ε, rfl⟩ := mem_children.mp hc
    have hCy1 : D.B ^ (1 / D.r) ≤ D.Cy := by
      unfold Cy
      have : 0 ≤ 8 * (2 ^ d * D.B / D.ε) ^ (1 / D.r) := by positivity
      linarith
    have hCy2 : 8 * (2 ^ d * D.B / D.ε) ^ (1 / D.r) ≤ D.Cy := by
      unfold Cy
      have : 0 ≤ D.B ^ (1 / D.r) := Real.rpow_nonneg hB0 _
      linarith
    split_ifs with h
    · have := D.abs_child_In4_le hR hRs hFR hG hgood ε h
      have h' : D.B ^ (1 / D.r) * D.Cres * D.E R' ≤ D.Cy * D.Cres * D.E R' := by gcongr
      linarith
    · have hsib := (D.second R hR hRs hFR).child_mem_Psib4 hR' hc h
      have := D.abs_child_sib_le hR hRs hFR hG hgood ε hsib
      have h' : 8 * (2 ^ d * D.B / D.ε) ^ (1 / D.r) * D.Cres * D.E R' ≤
          D.Cy * D.Cres * D.E R' := by gcongr
      linarith
  have hpar := D.abs_form2_vP_sub_yS_le hR hRs hFR hG hgood (D.Pbar4_second_avg_v hR hRs hFR hR')
  rw [D.form2_xi2_eq hR hRs hFR hR']
  refine (abs_sub _ _).trans ?_
  refine (add_le_add ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hchild)) hpar).trans
    ?_
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
  have hcard := card_children_le R'
  have : ((children R').card : ℝ) * (D.Cy * D.Cres * D.E R') ≤
      2 ^ d * (D.Cy * D.Cres * D.E R') :=
    mul_le_mul_of_nonneg_right hcard (by positivity)
  linarith

/-- `∑_{S ∈ s} E_S ≤ c E_R` when `∑_{S ∈ s} |S| ≤ c |R|`. [PROVED] -/
theorem sum_E_le_of_vol (s : Finset (DyadicCube d)) {c : ℝ} (h : ∑ S ∈ s, S.vol ≤ c * R.vol) :
    ∑ S ∈ s, D.E S ≤ c * D.E R := by
  have hF := D.Fpos'.le
  have hN : 0 ≤ lpNorm (D.G : (Fin d → ℝ) → ℝ) D.q := lpNorm_nonneg _ _
  have hV : 0 ≤ D.Q.vol ^ (1 / D.r - 1) := Real.rpow_nonneg D.Q.vol_pos.le _
  unfold E
  calc ∑ S ∈ s, D.F * lpNorm (D.G : (Fin d → ℝ) → ℝ) D.q * S.vol * D.Q.vol ^ (1 / D.r - 1)
      = (D.F * lpNorm (D.G : (Fin d → ℝ) → ℝ) D.q * D.Q.vol ^ (1 / D.r - 1)) * ∑ S ∈ s, S.vol := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun S _ => by ring
    _ ≤ (D.F * lpNorm (D.G : (Fin d → ℝ) → ℝ) D.q * D.Q.vol ^ (1 / D.r - 1)) * (c * R.vol) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by ring

/-- `∑_{S ∈ parents(𝐒)₄} E_S ≤ (2^d/ε) E_R` and `∑_{S ∈ 𝐒₄'} E_S ≤ (2^d/ε) E_R` by the bounded
overlap.
[PROVED] -/
theorem sum_E_Pbar4_second_le :
    ∑ S ∈ (D.second R hR hRs hFR).Pbar4, D.E S ≤ (2 ^ d / D.ε) * D.E R := by
  have h := (D.second R hR hRs hFR).sum_vol_le_of_overlap (D.second R hR hRs hFR).Pbar4
    (fun P hP => (D.second R hR hRs hFR).Pbar4_subset_Q hP) (D.second R hR hRs hFR).overlap_Pbar4
  have hε : (D.second R hR hRs hFR).ε = D.ε := rfl
  have hQ : (D.second R hR hRs hFR).Q = R := rfl
  rw [hε, hQ] at h
  exact D.sum_E_le_of_vol _ h

theorem sum_E_Psib4_second_le :
    ∑ S ∈ (D.second R hR hRs hFR).Psib4, D.E S ≤ (2 ^ d / D.ε) * D.E R := by
  have h := (D.second R hR hRs hFR).sum_vol_le_of_overlap (D.second R hR hRs hFR).Psib4
    (fun P hP => (D.second R hR hRs hFR).Psib4_subset_Q hP) (D.second R hR hRs hFR).overlap_Psib4
  have hε : (D.second R hR hRs hFR).ε = D.ε := rfl
  have hQ : (D.second R hR hRs hFR).Q = R := rfl
  rw [hε, hQ] at h
  exact D.sum_E_le_of_vol _ h

/-- The constant of (2.43): `C₄₃ = C_v + M C_{sib} + M (2^d C_y C_res + C_{sib})`, `M = 2^d/ε`. -/
noncomputable def C₄₃ : ℝ :=
  D.Cv + (2 ^ d / D.ε) * D.Csib + (2 ^ d / D.ε) * (2 ^ d * D.Cy * D.Cres + D.Csib)

/-- **The sum (2.43)** (p. 50–51): `|Λ_R(∑_{𝐒∩𝐒₄} b_S − ∑_{parents(𝐒)₄} [v]_S^{-1} v_S + ∑_{𝐒₄'}
[v]_S^{-1}
v_S, 𝔤̂)|
≤ C₄₃ E_R`, by the smoothness condition for the functions `ξ^{parents(S)}`, the expansion over the
children with the decay condition, and the bounded overlap of `parents(𝐒)₄` and `𝐒₄'`. [PROVED] -/
theorem abs_form2_sum243_le (hG : D.GBound) :
    |twoSlotForm D.T D.a D.b D.g R
        (∑ S ∈ (D.second R hR hRs hFR).PstIn4, D.vP S
          - ∑ S ∈ (D.second R hR hRs hFR).Pbar4, (1 / avg S (D.vP R)) • TestFun.truncateₗ S (D.vP R)
          + ∑ S ∈ (D.second R hR hRs hFR).Psib4, (1 / avg S (D.vP R)) • TestFun.truncateₗ S (D.vP
            R))
        (D.ghat R)| ≤ D.C₄₃ * D.E R := by
  classical
  have hM0 : (0 : ℝ) ≤ 2 ^ d / D.ε := by have := D.ε_pos; positivity
  have hE0 : ∀ S, 0 ≤ D.E S := fun S => (D.E_pos S).le
  have hCv := D.Cv_nonneg
  have hCsib : 0 ≤ D.Csib := by
    have := D.C₄₂_nonneg
    unfold Csib
    positivity
  have hCres := D.Cres_nonneg
  have hCy := D.Cy_nonneg
  rw [D.sum243_eq hR hRs hFR, twoSlotForm_sum_left D.T D.hab]
  have hsm : ∀ R' ∈ (D.second R hR hRs hFR).Pbar4,
      twoSlotForm D.T D.a D.b D.g R ((D.second R hR hRs hFR).xi R') (D.ghat R) =
        twoSlotForm D.T D.a D.b D.g R' ((D.second R hR hRs hFR).xi R') (D.ghat R) := fun R' hR' =>
    (twoSlotForm_eq_of_subset_left D.T D.hab D.g ((D.second R hR hRs hFR).Pbar4_subset_Q hR')
      ((D.second R hR hRs hFR).xi_supported hR') ((D.second R hR hRs hFR).xi_meanZero hR') _).symm
  rw [Finset.sum_congr rfl hsm]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_sum fun R' hR' => D.abs_form2_xi2_le hR hRs hFR hG hR').trans ?_
  rw [Finset.sum_add_distrib, (D.second R hR hRs hFR).sum_Pbar4_children_ite
    (fun c => D.Cv * D.E c) (fun c => D.Csib * D.E c), ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.mul_sum]
  have hIn : ∑ S ∈ (D.second R hR hRs hFR).PstIn4, D.E S ≤ D.E R :=
    ((Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun S _ _ => hE0 S).trans
      (D.sum_E_second_le hR hRs hFR)).trans
      (mul_le_of_le_one_left (hE0 R) (by linarith [D.ε_pos]))
  have hSib := D.sum_E_Psib4_second_le hR hRs hFR
  have hBar := D.sum_E_Pbar4_second_le hR hRs hFR
  calc D.Cv * ∑ S ∈ (D.second R hR hRs hFR).PstIn4, D.E S +
        D.Csib * ∑ S ∈ (D.second R hR hRs hFR).Psib4, D.E S +
        (2 ^ d * D.Cy * D.Cres + D.Csib) * ∑ S ∈ (D.second R hR hRs hFR).Pbar4, D.E S
      ≤ D.Cv * D.E R + D.Csib * ((2 ^ d / D.ε) * D.E R) +
          (2 ^ d * D.Cy * D.Cres + D.Csib) * ((2 ^ d / D.ε) * D.E R) := by gcongr
    _ = D.C₄₃ * D.E R := by
        unfold C₄₃
        ring

end Sum243

/-! #### The estimate (2.39) (p. 47–51) -/

/-- The constant `C` of (2.39): `C₃₉ = C_α + (C_α + C₄₉ + C₄₅) + C₄₂ + C₄₃`. -/
noncomputable def C₃₉ : ℝ := D.Cα + (D.Cα + D.C₄₉ + D.C₄₅) + D.C₄₂ + D.C₄₃

/-- **The estimate (2.39)** (p. 47): for a cube `R` of the tree in no first stopping cube with
`F_R > 0`, `|Λ_R(h − 𝔥, 𝔤̂)| ≤ ((1−ε) A' + C) F |R||Q|^{-1} ‖g‖_q ‖h‖_r` (`‖h‖_r = |Q|^{1/r}`),
assembled from the expansion (2.41)–(2.43): the term `[h]_R v`, the sum (2.44) with its `A'`-term
carrying the factor `1 − ε`, the sum (2.42) and the sum (2.43). [PROVED] -/
theorem estimate_2_39 {R : DyadicCube d} (hR : R ∈ D.tree) (hRs : D.NotInStopping R)
    (hFR : 0 < D.FP R) (hG : D.GBound) :
    |twoSlotForm D.T D.a D.b D.g R (TestFun.ind R - D.prunedH hR hRs hFR) (D.ghat R)| ≤
      ((1 - D.ε) * D.A' + D.C₃₉) * D.E R := by
  rw [D.sub_prunedH_eq hR hRs hFR]
  have e : ∑ S ∈ (D.second R hR hRs hFR).PstOut4,
      (D.vP S - (1 / avg S (D.vP R)) • TestFun.truncateₗ S (D.vP R)) =
      ∑ S ∈ (D.second R hR hRs hFR).PstOut4, D.yS R S := rfl
  rw [e, show ∀ (a b c e f g : TestFun d), a + b + c + e - f + g = a + b + c + (e - f + g) from
    fun a b c e f g => by abel, twoSlotForm_add_left D.T D.hab, twoSlotForm_add_left D.T D.hab,
    twoSlotForm_add_left D.T D.hab]
  have h1 := D.abs_form2_v_ghat_le hR hRs hG
  have h2 := D.abs_form2_sum244_le hR hRs hFR hG
  have h3 := D.abs_form2_sum242_le hR hRs hFR hG
  have h4 := D.abs_form2_sum243_le hR hRs hFR hG
  set t1 := twoSlotForm D.T D.a D.b D.g R (D.vP R) (D.ghat R)
  set t2 := twoSlotForm D.T D.a D.b D.g R
    (∑ S ∈ (D.second R hR hRs hFR).Pst, (TestFun.ind S - D.vP S)) (D.ghat R)
  set t3 := twoSlotForm D.T D.a D.b D.g R (∑ S ∈ (D.second R hR hRs hFR).PstOut4, D.yS R S)
    (D.ghat R)
  set t4 := twoSlotForm D.T D.a D.b D.g R
    (∑ S ∈ (D.second R hR hRs hFR).PstIn4, D.vP S
      - ∑ S ∈ (D.second R hR hRs hFR).Pbar4, (1 / avg S (D.vP R)) • TestFun.truncateₗ S (D.vP R)
      + ∑ S ∈ (D.second R hR hRs hFR).Psib4, (1 / avg S (D.vP R)) • TestFun.truncateₗ S (D.vP R))
    (D.ghat R)
  have ha := abs_add_le (t1 + t2 + t3) t4
  have hb := abs_add_le (t1 + t2) t3
  have hc := abs_add_le t1 t2
  unfold C₃₉
  nlinarith [ha, hb, hc, h1, h2, h3, h4]

/-! ### §2.5 The main estimate (2.40): the numbers `φ_T`, `ψ_T` and the telescoping (2.56)–(2.60)
(p. 51–52)

The left-hand side `Λ_R(𝔥, 𝔤̂)` of (2.40) is written as `∑_{T,U} Λ_R(ψ_T v_T, φ_U u_U)` over the
cubes
`T`, `U` of the smallest side length `2^{-N}ℓ(R)` of the tree `𝒟_N(R)`, on which all functions
involved are constant (p. 51), and then telescoped level by level; the smoothness condition (1.2)
turns the sums over pairs `(T, U)` into diagonal sums. We formalise the levels
`𝒟_L(R) ∖ 𝒟_{L-1}(R)` of the tree (`level`), the cubes above the leaves (`nonleaf`), and the
telescoping identity for arbitrary families `x_T`, `y_T` of test functions supported on `T` whose
differences `x_T − ∑_{T' child of T} x_{T'}`, `y_T − ∑ y_{T'}` have mean zero (`telescoping`); the
paper's (2.57)–(2.60) is the case `x_T = ψ_T v_T`, `y_T = φ_T u_T` (`form2_prunedH_ghat_eq`), where
the mean-zero conditions come from `[ψ_T v_T]_T = [𝔥]_T`, `[φ_T u_T]_T = [𝔤̂]_T` and the identity
`[f]_T |T| = ∑_{T'} [f]_{T'} |T'|`, and the leaf identities `∑_{T leaf} ψ_T v_T = 𝔥`,
`∑_{T leaf} φ_T u_T = 𝔤̂` from the constancy on the leaves. -/

/-- The cubes `L` levels below `R`: `level 0 R = {R}` and `level (L+1) R` is the set of children of
the cubes of `level L R`. -/
noncomputable def level : ℕ → DyadicCube d → Finset (DyadicCube d)
  | 0, R => {R}
  | L + 1, R => (level L R).biUnion children

theorem level_zero (R : DyadicCube d) : level 0 R = {R} := rfl

theorem level_succ (L : ℕ) (R : DyadicCube d) :
    level (L + 1) R = (level L R).biUnion children := rfl

theorem subset_of_mem_level {L : ℕ} {R T : DyadicCube d} (hT : T ∈ level L R) :
    T.toSet ⊆ R.toSet := by
  induction L generalizing T with
  | zero =>
    rw [level_zero, Finset.mem_singleton] at hT
    rw [hT]
  | succ L ih =>
    rw [level_succ, Finset.mem_biUnion] at hT
    obtain ⟨S, hS, hTS⟩ := hT
    obtain ⟨ε, rfl⟩ := mem_children.mp hTS
    exact (S.child_subset ε).trans (ih hS)

theorem m_of_mem_level {L : ℕ} {R T : DyadicCube d} (hT : T ∈ level L R) : T.m = R.m - L := by
  induction L generalizing T with
  | zero =>
    rw [level_zero, Finset.mem_singleton] at hT
    rw [hT]
    simp
  | succ L ih =>
    rw [level_succ, Finset.mem_biUnion] at hT
    obtain ⟨S, hS, hTS⟩ := hT
    obtain ⟨ε, rfl⟩ := mem_children.mp hTS
    have := ih hS
    change S.m - 1 = R.m - ((L + 1 : ℕ) : ℤ)
    push_cast
    omega

/-- `level L R` consists of the subcubes of `R` of side length `2^{-L} ℓ(R)`. [PROVED] -/
theorem mem_level_iff {L : ℕ} {R T : DyadicCube d} :
    T ∈ level L R ↔ T.toSet ⊆ R.toSet ∧ T.m = R.m - L := by
  refine ⟨fun h => ⟨subset_of_mem_level h, m_of_mem_level h⟩, fun h => ?_⟩
  induction L generalizing T with
  | zero =>
    rw [level_zero, Finset.mem_singleton]
    exact DyadicCube.eq_of_subset_of_m_eq h.1 (by simpa using h.2)
  | succ L ih =>
    rw [level_succ, Finset.mem_biUnion]
    have hTp : T.toSet ⊆ T.parent.toSet := by
      have := T.parent.child_subset (fun i => decide (T.l i % 2 = 1))
      rwa [T.child_parent] at this
    have hm : T.parent.m = T.m + 1 := rfl
    have h2 := h.2
    push_cast at h2
    refine ⟨T.parent, ih ⟨?_, by omega⟩, mem_children.mpr ⟨_, T.child_parent⟩⟩
    rcases DyadicCube.subset_or_disjoint T.parent R (by omega) with hsub | hdis
    · exact hsub
    · exact absurd (h.1 T.corner_mem) (Set.disjoint_left.mp hdis (hTp T.corner_mem))

/-- Cubes of the same level are equal or disjoint. [PROVED] -/
theorem level_eq_or_disjoint {L : ℕ} {R S U : DyadicCube d} (hS : S ∈ level L R)
    (hU : U ∈ level L R) : S = U ∨ Disjoint S.toSet U.toSet :=
  DyadicCube.eq_or_disjoint_of_m_eq S U ((m_of_mem_level hS).trans (m_of_mem_level hU).symm)

theorem sum_level_succ {M : Type*} [AddCommMonoid M] (L : ℕ) (R : DyadicCube d)
    (f : DyadicCube d → M) :
    ∑ T ∈ level (L + 1) R, f T = ∑ S ∈ level L R, ∑ c ∈ children S, f c := by
  rw [level_succ, Finset.sum_biUnion (children_pairwiseDisjoint _)]

theorem mem_level_succ_of_mem_children {L : ℕ} {R S c : DyadicCube d} (hS : S ∈ level L R)
    (hc : c ∈ children S) : c ∈ level (L + 1) R := by
  rw [level_succ, Finset.mem_biUnion]
  exact ⟨S, hS, hc⟩

/-- Every point of `R` lies in a cube of each level. [PROVED] -/
theorem exists_mem_level (L : ℕ) {R : DyadicCube d} {x : Fin d → ℝ} (hx : x ∈ R.toSet) :
    ∃ T ∈ level L R, x ∈ T.toSet := by
  induction L with
  | zero => exact ⟨R, by rw [level_zero]; exact Finset.mem_singleton_self R, hx⟩
  | succ L ih =>
    obtain ⟨T, hT, hxT⟩ := ih
    exact ⟨T.childAt x, mem_level_succ_of_mem_children hT (mem_children.mpr ⟨_, rfl⟩),
      T.mem_childAt hxT⟩

theorem subset_of_mem_children {S c : DyadicCube d} (hc : c ∈ children S) : c.toSet ⊆ S.toSet := by
  obtain ⟨ε, rfl⟩ := mem_children.mp hc
  exact S.child_subset ε

/-- `∑_{c child of S} f 𝟙_c = f 𝟙_S`. [PROVED] -/
theorem sum_children_truncateₗ (S : DyadicCube d) (f : TestFun d) :
    ∑ c ∈ children S, TestFun.truncateₗ c f = TestFun.truncateₗ S f := by
  rw [children, Finset.sum_image fun ε _ ε' _ h => S.child_injective h,
    ← TestFun.sum_truncateₗ_children S (TestFun.truncateₗ S f)
      (TestFun.truncateₗ_supportedOn S f)]
  exact Finset.sum_congr rfl fun ε _ =>
    (TestFun.truncateₗ_truncateₗ_of_subset (S.child_subset ε) f).symm

/-- `∑_{T ∈ level L R} f 𝟙_T = f 𝟙_R`: the cubes of a level partition `R`. [PROVED] -/
theorem sum_level_truncateₗ (L : ℕ) (R : DyadicCube d) (f : TestFun d) :
    ∑ T ∈ level L R, TestFun.truncateₗ T f = TestFun.truncateₗ R f := by
  induction L with
  | zero => rw [level_zero, Finset.sum_singleton]
  | succ L ih =>
    rw [sum_level_succ, ← ih]
    exact Finset.sum_congr rfl fun S _ => sum_children_truncateₗ S f

/-- The cubes of the first `L` levels below `R`: the cubes of `𝒟_L(R)` which are not leaves. -/
noncomputable def nonleaf (L : ℕ) (R : DyadicCube d) : Finset (DyadicCube d) :=
  (Finset.range L).biUnion fun L' => level L' R

theorem nonleaf_zero (R : DyadicCube d) : nonleaf 0 R = ∅ := by
  simp [nonleaf]

theorem level_disjoint_of_ne {L L' : ℕ} (h : L ≠ L') (R : DyadicCube d) :
    Disjoint (level L R) (level L' R) := by
  rw [Finset.disjoint_left]
  intro T hT hT'
  have h1 := m_of_mem_level hT
  have h2 := m_of_mem_level hT'
  exact h (by omega)

theorem sum_nonleaf_succ {M : Type*} [AddCommMonoid M] (L : ℕ) (R : DyadicCube d)
    (f : DyadicCube d → M) :
    ∑ T ∈ nonleaf (L + 1) R, f T = ∑ T ∈ nonleaf L R, f T + ∑ T ∈ level L R, f T := by
  unfold nonleaf
  rw [Finset.range_add_one, Finset.biUnion_insert, Finset.sum_union, add_comm]
  rw [Finset.disjoint_left]
  intro T hT hT'
  rw [Finset.mem_biUnion] at hT'
  obtain ⟨L', hL', hT'⟩ := hT'
  rw [Finset.mem_range] at hL'
  exact Finset.disjoint_left.mp (level_disjoint_of_ne hL'.ne' R) hT hT'

theorem level_subset_nonleaf {L L' : ℕ} (h : L' < L) (R : DyadicCube d) :
    level L' R ⊆ nonleaf L R :=
  Finset.subset_biUnion_of_mem (fun L' => level L' R) (Finset.mem_range.mpr h)

theorem nonleaf_mono {L L' : ℕ} (h : L' ≤ L) (R : DyadicCube d) : nonleaf L' R ⊆ nonleaf L R :=
  Finset.biUnion_subset_biUnion_of_subset_left _ (Finset.range_mono h)

/-- `nonleaf L R` consists of the subcubes of `R` of side length `> 2^{-L} ℓ(R)` (for `d ≥ 1`).
[PROVED] -/
theorem mem_nonleaf_iff (hd : d ≠ 0) {L : ℕ} {R T : DyadicCube d} :
    T ∈ nonleaf L R ↔ T.toSet ⊆ R.toSet ∧ R.m - L < T.m := by
  unfold nonleaf
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨L', hL', hT⟩
    rw [Finset.mem_range] at hL'
    refine ⟨subset_of_mem_level hT, ?_⟩
    have := m_of_mem_level hT
    omega
  · rintro ⟨hsub, hm⟩
    have hle := DyadicCube.m_le_of_subset hd hsub
    refine ⟨(R.m - T.m).toNat, ?_, mem_level_iff.mpr ⟨hsub, ?_⟩⟩
    · rw [Finset.mem_range]
      omega
    · omega

theorem twoSlotForm_zero_left (T : PerfectCZForm d n) {a b : Fin n} (hab : a ≠ b)
    (g : Fin n → TestFun d) (P : DyadicCube d) (ρ' : TestFun d) :
    twoSlotForm T a b g P 0 ρ' = 0 := by
  rw [twoSlotForm_eq_slotForm T hab, map_zero]

theorem twoSlotForm_zero_right (T : PerfectCZForm d n) (a b : Fin n) (g : Fin n → TestFun d)
    (P : DyadicCube d) (ρ : TestFun d) : twoSlotForm T a b g P ρ 0 = 0 := by
  rw [twoSlotForm_eq_slotForm', map_zero]

/-- A mean-zero function supported on `S ⊆ R` against a function supported on a cube `U` disjoint
from `S`: `Λ_R(ρ, ρ') = Λ_S(ρ, ρ') = Λ_S(ρ, ρ' 𝟙_S) = 0`. [PROVED] -/
theorem twoSlotForm_eq_zero_of_disjoint_left (T : PerfectCZForm d n) {a b : Fin n} (hab : a ≠ b)
    (g : Fin n → TestFun d) {R S U : DyadicCube d} (hSR : S.toSet ⊆ R.toSet)
    (hSU : Disjoint S.toSet U.toSet) {ρ ρ' : TestFun d} (hρ : SupportedOn ρ S)
    (hρ0 : MeanZero (ρ : (Fin d → ℝ) → ℝ)) (hρ' : SupportedOn ρ' U) :
    twoSlotForm T a b g R ρ ρ' = 0 := by
  have h : TestFun.truncateₗ S ρ' = 0 := by
    rw [← TestFun.truncateₗ_of_supportedOn hρ', TestFun.truncateₗ_truncateₗ_of_disjoint hSU]
  rw [← twoSlotForm_eq_of_subset_left T hab g hSR hρ hρ0, ← twoSlotForm_truncateₗ_right, h,
    twoSlotForm_zero_right]

/-- The mirror image: a mean-zero function supported on `U ⊆ R` in the second slot against a
function supported on a cube `S` disjoint from `U`. [PROVED] -/
theorem twoSlotForm_eq_zero_of_disjoint_right (T : PerfectCZForm d n) {a b : Fin n} (hab : a ≠ b)
    (g : Fin n → TestFun d) {R S U : DyadicCube d} (hUR : U.toSet ⊆ R.toSet)
    (hSU : Disjoint S.toSet U.toSet) {ρ ρ' : TestFun d} (hρ : SupportedOn ρ S)
    (hρ' : SupportedOn ρ' U) (hρ'0 : MeanZero (ρ' : (Fin d → ℝ) → ℝ)) :
    twoSlotForm T a b g R ρ ρ' = 0 := by
  have h : TestFun.truncateₗ U ρ = 0 := by
    rw [← TestFun.truncateₗ_of_supportedOn hρ, TestFun.truncateₗ_truncateₗ_of_disjoint hSU.symm]
  rw [← twoSlotForm_eq_of_subset T a b g hUR ρ hρ' hρ'0, ← twoSlotForm_truncateₗ_left, h,
    twoSlotForm_zero_left T hab]

theorem supportedOn_sub {f g : TestFun d} {P : DyadicCube d} (hf : SupportedOn f P)
    (hg : SupportedOn g P) : SupportedOn ((f - g : TestFun d) : (Fin d → ℝ) → ℝ) P :=
  fun x hx => by rw [Submodule.coe_sub, Pi.sub_apply, hf x hx, hg x hx, sub_zero]

theorem supportedOn_sum_children {x : DyadicCube d → TestFun d} (hx : ∀ S, SupportedOn (x S) S)
    (S : DyadicCube d) :
    SupportedOn ((∑ c ∈ children S, x c : TestFun d) : (Fin d → ℝ) → ℝ) S := fun y hy => by
  rw [Submodule.coe_sum, Finset.sum_apply]
  refine Finset.sum_eq_zero fun c hc => ?_
  obtain ⟨ε, rfl⟩ := mem_children.mp hc
  exact hx _ y fun h => hy (S.child_subset ε h)

/-- If `∫ x_T = [f]_T |T|` for `T = S` and the children of `S`, then `x_S − ∑_{children} x_{T'}`
has mean zero (by `[f]_S |S| = ∑_{T'} [f]_{T'} |T'|`). [PROVED] -/
theorem meanZero_sub_sum_children {x : DyadicCube d → TestFun d} {f : TestFun d}
    {S : DyadicCube d} (hS : TestFun.integralₗ (x S) = avg S f * S.vol)
    (hc : ∀ c ∈ children S, TestFun.integralₗ (x c) = avg c f * c.vol) :
    MeanZero ((x S - ∑ c ∈ children S, x c : TestFun d) : (Fin d → ℝ) → ℝ) := by
  change TestFun.integralₗ (x S - ∑ c ∈ children S, x c) = 0
  rw [map_sub, map_sum, hS, Finset.sum_congr rfl hc, ← avg_mul_vol_children, sub_self]

/-- **The telescoping identity (2.56)** over the levels of `R` (p. 51–52): for families `x_T`, `y_T`
of test functions supported on `T` such that `x_T − ∑_{T' child of T} x_{T'}` and
`y_T − ∑_{T'} y_{T'}` have mean zero for every non-leaf cube `T`,
`Λ_R(∑_{T leaf} x_T, ∑_{U leaf} y_U) = Λ_R(x_R, y_R) − ∑_T Λ_R(x_T − ∑ x_{T'}, y_T)
   − ∑_T Λ_R(x_T, y_T − ∑ y_{T'}) + ∑_T Λ_R(x_T − ∑ x_{T'}, y_T − ∑ y_{T'})`,
the sums over the non-leaf cubes `T`. At each level the smoothness condition (1.2) kills the
off-diagonal terms (`twoSlotForm_eq_zero_of_disjoint_left/right`). [PROVED] -/
theorem telescoping (T : PerfectCZForm d n) {a b : Fin n} (hab : a ≠ b) (g : Fin n → TestFun d)
    (R : DyadicCube d) (L : ℕ) (x y : DyadicCube d → TestFun d)
    (hx : ∀ S, SupportedOn (x S) S) (hy : ∀ S, SupportedOn (y S) S)
    (hx0 : ∀ S ∈ nonleaf L R,
      MeanZero ((x S - ∑ c ∈ children S, x c : TestFun d) : (Fin d → ℝ) → ℝ))
    (hy0 : ∀ S ∈ nonleaf L R,
      MeanZero ((y S - ∑ c ∈ children S, y c : TestFun d) : (Fin d → ℝ) → ℝ)) :
    twoSlotForm T a b g R (∑ S ∈ level L R, x S) (∑ S ∈ level L R, y S) =
      twoSlotForm T a b g R (x R) (y R)
      - ∑ S ∈ nonleaf L R, twoSlotForm T a b g R (x S - ∑ c ∈ children S, x c) (y S)
      - ∑ S ∈ nonleaf L R, twoSlotForm T a b g R (x S) (y S - ∑ c ∈ children S, y c)
      + ∑ S ∈ nonleaf L R, twoSlotForm T a b g R (x S - ∑ c ∈ children S, x c)
          (y S - ∑ c ∈ children S, y c) := by
  induction L with
  | zero => simp [level_zero, nonleaf_zero]
  | succ L ih =>
    have hsub := nonleaf_mono (Nat.le_succ L) R
    have hlev := level_subset_nonleaf (Nat.lt_succ_self L) R
    have ih' := ih (fun S hS => hx0 S (hsub hS)) (fun S hS => hy0 S (hsub hS))
    rw [sum_level_succ, sum_level_succ, sum_nonleaf_succ, sum_nonleaf_succ, sum_nonleaf_succ]
    have key : twoSlotForm T a b g R (∑ S ∈ level L R, x S) (∑ S ∈ level L R, y S)
        - twoSlotForm T a b g R (∑ S ∈ level L R, ∑ c ∈ children S, x c)
            (∑ S ∈ level L R, ∑ c ∈ children S, y c)
        = ∑ S ∈ level L R, (twoSlotForm T a b g R (x S - ∑ c ∈ children S, x c) (y S)
          + twoSlotForm T a b g R (x S) (y S - ∑ c ∈ children S, y c)
          - twoSlotForm T a b g R (x S - ∑ c ∈ children S, x c)
              (y S - ∑ c ∈ children S, y c)) := by
      rw [twoSlotForm_sum_left T hab, twoSlotForm_sum_left T hab, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun S hS => ?_
      rw [twoSlotForm_sum_right, twoSlotForm_sum_right, ← Finset.sum_sub_distrib]
      have hxS := supportedOn_sub (hx S) (supportedOn_sum_children hx S)
      have hx0S := hx0 S (hlev hS)
      have e : ∀ U, twoSlotForm T a b g R (x S) (y U)
          - twoSlotForm T a b g R (∑ c ∈ children S, x c) (∑ c ∈ children U, y c)
          = twoSlotForm T a b g R (x S - ∑ c ∈ children S, x c) (y U)
            + twoSlotForm T a b g R (x S) (y U - ∑ c ∈ children U, y c)
            - twoSlotForm T a b g R (x S - ∑ c ∈ children S, x c)
                (y U - ∑ c ∈ children U, y c) := by
        intro U
        rw [twoSlotForm_sub_left T hab, twoSlotForm_sub_right, twoSlotForm_sub_left T hab,
          twoSlotForm_sub_right, twoSlotForm_sub_right]
        ring
      have hdiag : ∑ U ∈ level L R, (twoSlotForm T a b g R (x S) (y U)
          - twoSlotForm T a b g R (∑ c ∈ children S, x c) (∑ c ∈ children U, y c))
          = twoSlotForm T a b g R (x S) (y S)
            - twoSlotForm T a b g R (∑ c ∈ children S, x c) (∑ c ∈ children S, y c) := by
        refine Finset.sum_eq_single_of_mem S hS fun U hU hne => ?_
        rcases level_eq_or_disjoint hS hU with h | hSU
        · exact absurd h.symm hne
        · have hyU := supportedOn_sub (hy U) (supportedOn_sum_children hy U)
          rw [e U, twoSlotForm_eq_zero_of_disjoint_left T hab g (subset_of_mem_level hS) hSU hxS
              hx0S (hy U),
            twoSlotForm_eq_zero_of_disjoint_right T hab g (subset_of_mem_level hU) hSU (hx S) hyU
              (hy0 U (hlev hU)),
            twoSlotForm_eq_zero_of_disjoint_left T hab g (subset_of_mem_level hS) hSU hxS
              hx0S hyU]
          ring
      rw [hdiag, e S]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib] at key
    linarith [key, ih']

theorem constOn_smul {f : TestFun d} {P : DyadicCube d} (c : ℝ) (hf : ConstOn f P) :
    ConstOn ((c • f : TestFun d) : (Fin d → ℝ) → ℝ) P := fun x hx y hy => by
  rw [Submodule.coe_smul, Pi.smul_apply, Pi.smul_apply, hf x hx y hy]

theorem constOn_sub {f g : TestFun d} {P : DyadicCube d} (hf : ConstOn f P) (hg : ConstOn g P) :
    ConstOn ((f - g : TestFun d) : (Fin d → ℝ) → ℝ) P := fun x hx y hy => by
  rw [Submodule.coe_sub, Pi.sub_apply, Pi.sub_apply, hf x hx y hy, hg x hx y hy]

theorem constOn_add {f g : TestFun d} {P : DyadicCube d} (hf : ConstOn f P) (hg : ConstOn g P) :
    ConstOn ((f + g : TestFun d) : (Fin d → ℝ) → ℝ) P := fun x hx y hy => by
  rw [Submodule.coe_add, Pi.add_apply, Pi.add_apply, hf x hx y hy, hg x hx y hy]

theorem constOn_sum {ι : Type*} {s : Finset ι} {f : ι → TestFun d} {P : DyadicCube d}
    (hf : ∀ i ∈ s, ConstOn (f i) P) :
    ConstOn ((∑ i ∈ s, f i : TestFun d) : (Fin d → ℝ) → ℝ) P := fun x hx y hy => by
  rw [Submodule.coe_sum, Finset.sum_apply, Finset.sum_apply]
  exact Finset.sum_congr rfl fun i hi => hf i hi x hx y hy

/-- A test function constant on `T` satisfies `f 𝟙_T = [f]_T 𝟙_T`. [PROVED] -/
theorem truncateₗ_eq_of_constOn {f : TestFun d} {T : DyadicCube d} (hf : ConstOn f T) :
    TestFun.truncateₗ T f = avg T f • TestFun.ind T := by
  apply Subtype.ext
  rw [TestFun.coe_truncateₗ, Submodule.coe_smul, TestFun.coe_ind]
  funext x
  by_cases hx : x ∈ T.toSet
  · have e : ∫ y in T.toSet, (f : (Fin d → ℝ) → ℝ) y = ∫ y in T.toSet, (f : (Fin d → ℝ) → ℝ) x :=
      setIntegral_congr_fun T.measurableSet_toSet fun y hy => hf y hy x hx
    have ha : avg T f = (f : (Fin d → ℝ) → ℝ) x := by
      rw [avg, e, setIntegral_const, measureReal_def, T.volume_toSet,
        ENNReal.toReal_ofReal T.vol_pos.le, smul_eq_mul, mul_div_cancel_left₀ _ T.vol_pos.ne']
    simp [truncate, hx, ha]
  · simp [truncate, hx]

/-- `([f]_T/[v]_T) v 𝟙_T = f 𝟙_T` for `f`, `v` constant on `T`, provided `[f]_T = 0` whenever
`[v]_T = 0`. [PROVED] -/
theorem div_smul_truncateₗ_eq {f v : TestFun d} {T : DyadicCube d} (hf : ConstOn f T)
    (hv : ConstOn v T) (h0 : avg T v = 0 → avg T f = 0) :
    (avg T f / avg T v) • TestFun.truncateₗ T v = TestFun.truncateₗ T f := by
  rw [truncateₗ_eq_of_constOn hf, truncateₗ_eq_of_constOn hv, smul_smul]
  congr 1
  by_cases h : avg T v = 0
  · rw [h, div_zero, zero_mul, h0 h]
  · rw [div_mul_cancel₀ _ h]

open Classical in
/-- The coefficient of `f` relative to `v` on the cube `T` (p. 51): `[f]_T / [v]_T` when `[v]_T ≠ 0`
(`coefOn_eq_div`); when `[v]_T = 0` it is the number `c` with `f 𝟙_T = c v 𝟙_T` if there is one (it
is unique when `v 𝟙_T ≠ 0`, `coefOn_eq_of_eq`), and `0` if `v 𝟙_T = 0`. -/
noncomputable def coefOn (f v : TestFun d) (T : DyadicCube d) : ℝ :=
  if TestFun.truncateₗ T v = 0 then 0
  else if h : ∃ c : ℝ, TestFun.truncateₗ T f = c • TestFun.truncateₗ T v then Classical.choose h
  else avg T f / avg T v

theorem coefOn_of_eq_zero {f v : TestFun d} {T : DyadicCube d} (hv : TestFun.truncateₗ T v = 0) :
    coefOn f v T = 0 := by
  unfold coefOn
  split_ifs
  rfl

/-- If `v 𝟙_T ≠ 0` and `f 𝟙_T = c v 𝟙_T`, the coefficient is `c`. [PROVED] -/
theorem coefOn_eq_of_eq {f v : TestFun d} {T : DyadicCube d} {c : ℝ}
    (hv : TestFun.truncateₗ T v ≠ 0) (h : TestFun.truncateₗ T f = c • TestFun.truncateₗ T v) :
    coefOn f v T = c := by
  unfold coefOn
  split_ifs with h1 h2
  · exact absurd h1 hv
  · have hc : c • TestFun.truncateₗ T v = Classical.choose h2 • TestFun.truncateₗ T v :=
      h.symm.trans (Classical.choose_spec h2)
    exact (smul_left_injective ℝ hv hc).symm
  · exact absurd ⟨c, h⟩ h2

/-- `[v]_T ≠ 0` implies `v 𝟙_T ≠ 0`. [PROVED] -/
theorem truncateₗ_ne_zero_of_avg_ne_zero {v : TestFun d} {T : DyadicCube d} (hv : avg T v ≠ 0) :
    TestFun.truncateₗ T v ≠ 0 := by
  intro h0
  apply hv
  have := TestFun.integralₗ_truncateₗ T v
  rw [h0, map_zero] at this
  exact (mul_eq_zero.mp this.symm).resolve_right T.vol_pos.ne'

/-- When `[v]_T ≠ 0` the coefficient is `[f]_T / [v]_T`. [PROVED] -/
theorem coefOn_eq_div {f v : TestFun d} {T : DyadicCube d} (hv : avg T v ≠ 0) :
    coefOn f v T = avg T f / avg T v := by
  have hv' := truncateₗ_ne_zero_of_avg_ne_zero hv
  unfold coefOn
  split_ifs with h1 h2
  · exact absurd h1 hv'
  · have hc := Classical.choose_spec h2
    have h := TestFun.integralₗ_truncateₗ T f
    rw [hc, map_smul, TestFun.integralₗ_truncateₗ, smul_eq_mul] at h
    rw [eq_div_iff hv]
    apply mul_right_cancel₀ T.vol_pos.ne'
    rw [← h]
    ring
  · rfl

/-- If `f 𝟙_T` is a multiple of `v 𝟙_T`, then `f 𝟙_T = c_T v 𝟙_T` with the coefficient `c_T`.
[PROVED] -/
theorem truncateₗ_eq_coefOn_smul {f v : TestFun d} {T : DyadicCube d}
    (h : ∃ c : ℝ, TestFun.truncateₗ T f = c • TestFun.truncateₗ T v) :
    TestFun.truncateₗ T f = coefOn f v T • TestFun.truncateₗ T v := by
  obtain ⟨c, hc⟩ := h
  by_cases hv : TestFun.truncateₗ T v = 0
  · rw [hv, smul_zero] at hc ⊢
    exact hc
  · rw [coefOn_eq_of_eq hv hc]
    exact hc

/-- If `f 𝟙_T = c v 𝟙_T`, then `|c_T| ≤ |c|` (`c_T = c`, or `c_T = 0` when `v 𝟙_T = 0`). [PROVED] -/
theorem abs_coefOn_le_of_eq {f v : TestFun d} {T : DyadicCube d} {c : ℝ}
    (h : TestFun.truncateₗ T f = c • TestFun.truncateₗ T v) : |coefOn f v T| ≤ |c| := by
  by_cases hv : TestFun.truncateₗ T v = 0
  · rw [coefOn_of_eq_zero hv, abs_zero]
    exact abs_nonneg c
  · rw [coefOn_eq_of_eq hv h]

/-- `∫ c_T v 𝟙_T = [f]_T |T|`, provided `[f]_T = 0` whenever `[v]_T = 0`. [PROVED] -/
theorem integralₗ_coefOn_smul {f v : TestFun d} {T : DyadicCube d}
    (h0 : avg T v = 0 → avg T f = 0) :
    TestFun.integralₗ (coefOn f v T • TestFun.truncateₗ T v) = avg T f * T.vol := by
  rw [map_smul, TestFun.integralₗ_truncateₗ, smul_eq_mul]
  by_cases hv : avg T v = 0
  · rw [hv, h0 hv, zero_mul, mul_zero]
  · rw [coefOn_eq_div hv]
    field_simp

/-- `c_T v 𝟙_T = f 𝟙_T` for `f`, `v` constant on `T`, provided `[f]_T = 0` whenever `[v]_T = 0`.
[PROVED] -/
theorem coefOn_smul_eq_of_constOn {f v : TestFun d} {T : DyadicCube d} (hf : ConstOn f T)
    (hv : ConstOn v T) (h0 : avg T v = 0 → avg T f = 0) :
    coefOn f v T • TestFun.truncateₗ T v = TestFun.truncateₗ T f := by
  by_cases hv0 : avg T v = 0
  · have h1 : TestFun.truncateₗ T v = 0 := by
      rw [truncateₗ_eq_of_constOn hv, hv0, zero_smul]
    rw [h1, smul_zero, truncateₗ_eq_of_constOn hf, h0 hv0, zero_smul]
  · rw [coefOn_eq_div hv0]
    exact div_smul_truncateₗ_eq hf hv h0

/-- The number `φ_T` of p. 51: `[𝔤̂]_T / [u]_T` when `[u]_T ≠ 0`; when `[u]_T = 0` the cube `T` lies
in a first stopping cube, `𝔤̂` is a multiple of `u` on `T` and `φ_T` is defined by `𝔤̂ 𝟙_T = φ_T u
𝟙_T`
(`φ_T = 0` if `u` vanishes on `T`). -/
noncomputable def phiT (R T : DyadicCube d) : ℝ := coefOn (D.ghat R) D.u T

/-- The function `φ_T u 𝟙_T`. -/
noncomputable def yT (R T : DyadicCube d) : TestFun d := D.phiT R T • TestFun.truncateₗ T D.u

theorem yT_supportedOn (R T : DyadicCube d) : SupportedOn (D.yT R T) T := fun x hx => by
  rw [yT, Submodule.coe_smul, Pi.smul_apply, TestFun.truncateₗ_supportedOn T D.u x hx, smul_zero]

section Telescoping

variable {R : DyadicCube d} (hR : R ∈ D.tree) (hRs : D.NotInStopping R) (hFR : 0 < D.FP R)

/-- `𝔤̂ 𝟙_T = 𝔤 𝟙_T − ([𝔤]_R/[u]_R) u 𝟙_T` for `T ⊆ R`. [PROVED] -/
theorem truncateₗ_ghat_eq_sub {T : DyadicCube d} (hTR : T.toSet ⊆ R.toSet) :
    TestFun.truncateₗ T (D.ghat R) =
      TestFun.truncateₗ T D.pruned - D.cS R • TestFun.truncateₗ T D.u := by
  rw [ghat, TestFun.truncateₗ_truncateₗ_of_subset hTR, map_sub, map_smul]
  rfl

/-- `[𝔤̂]_T = [𝔤]_T − ([𝔤]_R/[u]_R) [u]_T` for `T ⊆ R`. [PROVED] -/
theorem avg_ghat_eq {T : DyadicCube d} (hTR : T.toSet ⊆ R.toSet) :
    avg T (D.ghat R) = avg T D.pruned - D.cS R * avg T D.u := by
  have h1 := TestFun.integralₗ_truncateₗ T (D.ghat R)
  rw [D.truncateₗ_ghat_eq_sub hTR, map_sub, map_smul, TestFun.integralₗ_truncateₗ,
    TestFun.integralₗ_truncateₗ, smul_eq_mul] at h1
  apply mul_right_cancel₀ T.vol_pos.ne'
  rw [← h1]
  ring

/-- `[𝔤̂]_T = 0` for a cube `T ⊆ R` of the tree with `[u]_T = 0`: such a `T` lies in a first
stopping
cube, where `𝔤̂` is a multiple of `u`. [PROVED] -/
theorem avg_ghat_eq_zero {T : DyadicCube d} (hT : T ∈ D.tree) (hTR : T.toSet ⊆ R.toSet)
    (hu : avg T D.u = 0) : avg T (D.ghat R) = 0 := by
  have h4 : ∃ S ∈ D.P4, T.toSet ⊆ S.toSet := by
    by_contra h
    exact D.avg_u_ne_zero hT (fun S hS hsub => h ⟨S, hS, hsub⟩) hu
  obtain ⟨S, hS, hTS⟩ := h4
  obtain ⟨P, hP, hSP⟩ := exists_maximal_superset D.hd D.union_subset_tree (D.P4_subset hS)
  obtain ⟨φ, hφ⟩ := D.exists_truncateₗ_pruned_eq_smul hP (hTS.trans hSP)
  have e : TestFun.truncateₗ T (D.ghat R) = (φ - D.cS R) • TestFun.truncateₗ T D.u := by
    rw [D.truncateₗ_ghat_eq_sub hTR, hφ]
    module
  have h1 := TestFun.integralₗ_truncateₗ T (D.ghat R)
  rw [e, map_smul, TestFun.integralₗ_truncateₗ, hu, zero_mul, smul_zero] at h1
  exact (mul_eq_zero.mp h1.symm).resolve_right T.vol_pos.ne'

/-- `∫ φ_T u 𝟙_T = [𝔤̂]_T |T|` for every cube `T ⊆ R` of the tree. [PROVED] -/
theorem integralₗ_yT {T : DyadicCube d} (hT : T ∈ D.tree) (hTR : T.toSet ⊆ R.toSet) :
    TestFun.integralₗ (D.yT R T) = avg T (D.ghat R) * T.vol :=
  integralₗ_coefOn_smul fun hu => D.avg_ghat_eq_zero hT hTR hu

include hR hRs in
/-- `φ_R = 0`, since `[𝔤̂]_R = 0` and `[u]_R ≠ 0`. [PROVED] -/
theorem phiT_self : D.phiT R R = 0 := by
  have h : ∫ x, (D.ghat R : (Fin d → ℝ) → ℝ) x = 0 := D.ghat_meanZero hR hRs
  have ha : avg R (D.ghat R) = 0 := by
    rw [avg, setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun x hx => D.ghat_supported R x hx), h, zero_div]
  have hu : avg R D.u ≠ 0 := D.avg_u_ne_zero hR (D.not_in_P4_of_notInStopping hRs)
  rw [phiT, coefOn_eq_div hu, ha, zero_div]

/-- The constant of the bound for `φ_T`: `C_{φ,T} = C_φ + 16 C_loc`. -/
noncomputable def CφT : ℝ := D.Cφ + 16 * D.locConst

include hR hRs in
/-- **The bound for `φ_T`** (p. 51): `|φ_T| ≤ C |Q|^{-1/q} ‖g‖_q` for every cube `T ⊆ R` of the
tree.
For `T` in no first stopping cube `φ_T = [𝔤]_T/[u]_T − [𝔤]_R/[u]_R`; for `T` inside a first stopping
cube `𝔤̂ 𝟙_T = (φ − [𝔤]_R/[u]_R) u 𝟙_T` with the `φ` of (2.45), (2.46). [PROVED] -/
theorem abs_phiT_le (hG : D.GBound) {T : DyadicCube d} (hT : T ∈ D.tree)
    (hTR : T.toSet ⊆ R.toSet) :
    |D.phiT R T| ≤ D.CφT * (D.Q.vol ^ (-(1 / D.q)) * lpNorm (D.G : (Fin d → ℝ) → ℝ) D.q) := by
  set K := D.Q.vol ^ (-(1 / D.q)) * lpNorm (D.G : (Fin d → ℝ) → ℝ) D.q with hK
  have hK0 : 0 ≤ K := mul_nonneg (Real.rpow_nonneg D.Q.vol_pos.le _) (lpNorm_nonneg _ _)
  have hcR : |D.cS R| ≤ 8 * (D.locConst * K) := by
    have := D.abs_cS_le hG hR hRs
    rwa [mul_assoc] at this
  have hloc := D.locConst_nonneg
  have hCφ := D.Cφ_nonneg
  by_cases hTs : D.NotInStopping T
  · have hcT : |D.cS T| ≤ 8 * (D.locConst * K) := by
      have := D.abs_cS_le hG hT hTs
      rwa [mul_assoc] at this
    have hu : avg T D.u ≠ 0 := D.avg_u_ne_zero hT (D.not_in_P4_of_notInStopping hTs)
    have e : D.phiT R T = D.cS T - D.cS R := by
      rw [phiT, coefOn_eq_div hu, D.avg_ghat_eq hTR]
      unfold cS
      rw [sub_div, mul_div_assoc, div_self hu, mul_one]
    rw [e]
    calc |D.cS T - D.cS R| ≤ |D.cS T| + |D.cS R| := abs_sub _ _
      _ ≤ 8 * (D.locConst * K) + 8 * (D.locConst * K) := add_le_add hcT hcR
      _ ≤ D.CφT * K := by
          unfold CφT
          nlinarith
  · simp only [NotInStopping, not_forall, not_not] at hTs
    obtain ⟨P, hP, hTP⟩ := hTs
    obtain ⟨φ, hφ, hφle⟩ := D.exists_phi hG hP hTP
    have e : TestFun.truncateₗ T (D.ghat R) = (φ - D.cS R) • TestFun.truncateₗ T D.u := by
      rw [D.truncateₗ_ghat_eq_sub hTR, hφ]
      module
    calc |D.phiT R T| ≤ |φ - D.cS R| := abs_coefOn_le_of_eq e
      _ ≤ |φ| + |D.cS R| := abs_sub _ _
      _ ≤ D.Cφ * K + 8 * (D.locConst * K) := by
          refine add_le_add ?_ hcR
          rw [hK, ← mul_assoc]
          exact hφle
      _ ≤ D.CφT * K := by
          unfold CφT
          nlinarith

/-- The number `ψ_T` of p. 51: `[𝔥]_T / [v]_T` when `[v]_T ≠ 0` (then it is the coefficient
`[𝔤]_T/[u]_T` of the mirrored data, `psiT_eq_cS`); when `[v]_T = 0` the cube `T` lies in a second
stopping cube, `𝔥` is a multiple of `v` on `T` and `ψ_T` is defined by `𝔥 𝟙_T = ψ_T v 𝟙_T` (`ψ_T =
0`
if `v` vanishes on `T`). -/
noncomputable def psiT (T : DyadicCube d) : ℝ := coefOn (D.prunedH hR hRs hFR) (D.vP R) T

theorem psiT_eq_cS {T : DyadicCube d} (hv : avg T (D.vP R) ≠ 0) :
    D.psiT hR hRs hFR T = (D.second R hR hRs hFR).cS T := by
  rw [psiT, coefOn_eq_div hv]
  unfold cS
  rw [second_u]
  rfl

/-- The function `ψ_T v 𝟙_T`. -/
noncomputable def xT (T : DyadicCube d) : TestFun d :=
  D.psiT hR hRs hFR T • TestFun.truncateₗ T (D.vP R)

theorem xT_supportedOn (T : DyadicCube d) : SupportedOn (D.xT hR hRs hFR T) T := fun x hx => by
  rw [xT, Submodule.coe_smul, Pi.smul_apply, TestFun.truncateₗ_supportedOn T (D.vP R) x hx,
    smul_zero]

/-- `[𝔥]_T = 0` for a cube `T` of the tree of the second stopping time with `[v]_T = 0`: such a `T`
lies in a second stopping cube, where `𝔥` is a multiple of `v`. [PROVED] -/
theorem avg_prunedH_eq_zero {T : DyadicCube d} (hT : T ∈ (D.second R hR hRs hFR).tree)
    (hv : avg T (D.vP R) = 0) : avg T (D.prunedH hR hRs hFR) = 0 := by
  have hv' : avg T (D.second R hR hRs hFR).u = 0 := by
    rw [second_u]
    exact hv
  have h4 : ∃ S ∈ (D.second R hR hRs hFR).P4, T.toSet ⊆ S.toSet := by
    by_contra h
    exact (D.second R hR hRs hFR).avg_u_ne_zero hT (fun S hS hsub => h ⟨S, hS, hsub⟩) hv'
  obtain ⟨S, hS, hTS⟩ := h4
  obtain ⟨P, hP, hSP⟩ := exists_maximal_superset (D.second R hR hRs hFR).hd
    (D.second R hR hRs hFR).union_subset_tree ((D.second R hR hRs hFR).P4_subset hS)
  obtain ⟨φ, hφ⟩ := (D.second R hR hRs hFR).exists_truncateₗ_pruned_eq_smul hP (hTS.trans hSP)
  have h1 := TestFun.integralₗ_truncateₗ T (D.second R hR hRs hFR).pruned
  rw [hφ, map_smul, TestFun.integralₗ_truncateₗ, hv', zero_mul, smul_zero] at h1
  exact (mul_eq_zero.mp h1.symm).resolve_right T.vol_pos.ne'

/-- `∫ ψ_T v 𝟙_T = [𝔥]_T |T|` for every cube `T` of the tree of the second stopping time. [PROVED]
-/
theorem integralₗ_xT {T : DyadicCube d} (hT : T ∈ (D.second R hR hRs hFR).tree) :
    TestFun.integralₗ (D.xT hR hRs hFR T) = avg T (D.prunedH hR hRs hFR) * T.vol :=
  integralₗ_coefOn_smul fun hv => D.avg_prunedH_eq_zero hR hRs hFR hT hv

include hR in
/-- `[v]_R = 1`. [PROVED] -/
theorem avg_vP_self : avg R (D.vP R) = 1 := by
  rw [avg, setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => D.vP_supp R hR.1 x hx),
    D.vP_mean R hR.1, div_self R.vol_pos.ne']

/-- `ψ_R = 0`, since `[𝔥]_R = 0` and `[v]_R = 1`. [PROVED] -/
theorem psiT_self : D.psiT hR hRs hFR R = 0 := by
  have h : ∫ x, (D.prunedH hR hRs hFR : (Fin d → ℝ) → ℝ) x = 0 := D.prunedH_meanZero hR hRs hFR
  have ha : avg R (D.prunedH hR hRs hFR) = 0 := by
    rw [avg, setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun x hx => D.prunedH_supported hR hRs hFR x hx), h, zero_div]
  rw [psiT, coefOn_eq_div (by rw [D.avg_vP_self hR]; exact one_ne_zero), ha, zero_div]

/-- The constant of the bound for `ψ_T`: `C_ψ = C_φ' + 8 C_loc'` with the constants `C_φ'`, `C_loc'`
of the mirrored data (they depend only on `B`, `n`, `d`, `ε` and `r`). -/
noncomputable def Cψ : ℝ :=
  (D.second R hR hRs hFR).Cφ + 8 * (D.second R hR hRs hFR).locConst

/-- `|R|^{-1/r} ‖h_R‖_r = 1` for `h_R = 𝟙_R`. [PROVED] -/
theorem second_unit :
    (D.second R hR hRs hFR).Q.vol ^ (-(1 / (D.second R hR hRs hFR).q)) *
      lpNorm ((D.second R hR hRs hFR).G : (Fin d → ℝ) → ℝ) (D.second R hR hRs hFR).q = 1 := by
  change R.vol ^ (-(1 / D.r)) * lpNorm ((TestFun.ind R : TestFun d) : (Fin d → ℝ) → ℝ) D.r = 1
  rw [TestFun.lpNorm_ind R (by linarith [D.hr]), Real.rpow_neg R.vol_pos.le,
    inv_mul_cancel₀ (Real.rpow_pos_of_pos R.vol_pos _).ne']

/-- **The bound for `ψ_T`** (p. 51): `|ψ_T| ≤ C_ψ = C_ψ |R|^{-1/r} ‖h_R‖_r` for every cube `T` of
the
tree of the second stopping time, by the mirror images of the bounds for `[𝔤]_T/[u]_T` (the
hypothesis (2.8) for `h_R = 𝟙_R` holds trivially, `GBound_of_ind`). [PROVED] -/
theorem abs_psiT_le {T : DyadicCube d} (hT : T ∈ (D.second R hR hRs hFR).tree) :
    |D.psiT hR hRs hFR T| ≤ D.Cψ hR hRs hFR := by
  have hG' : (D.second R hR hRs hFR).GBound := (D.second R hR hRs hFR).GBound_of_ind rfl
  have hK := D.second_unit hR hRs hFR
  have hloc := (D.second R hR hRs hFR).locConst_nonneg
  have hCφ := (D.second R hR hRs hFR).Cφ_nonneg
  by_cases hTs : (D.second R hR hRs hFR).NotInStopping T
  · have hv : avg T (D.vP R) ≠ 0 := by
      have h30 := D.second_bound_2_30 hR hRs hFR hT
        ((D.second R hR hRs hFR).not_in_P4_of_notInStopping hTs)
      intro h0
      rw [h0, abs_zero] at h30
      norm_num at h30
    have h := (D.second R hR hRs hFR).abs_cS_le hG' hT hTs
    rw [mul_assoc, hK, mul_one] at h
    rw [D.psiT_eq_cS hR hRs hFR hv]
    unfold Cψ
    linarith
  · simp only [NotInStopping, not_forall, not_not] at hTs
    obtain ⟨P, hP, hTP⟩ := hTs
    obtain ⟨φ, hφ, hφle⟩ := (D.second R hR hRs hFR).exists_phi hG' hP hTP
    rw [mul_assoc, hK, mul_one] at hφle
    rw [second_u] at hφ
    have h : |D.psiT hR hRs hFR T| ≤ |φ| := abs_coefOn_le_of_eq hφ
    unfold Cψ
    linarith

/-- The cubes of the levels `L ≤ N` of `R` belong to the tree of the second stopping time. [PROVED]
-/
theorem mem_second_tree_of_mem_level {L : ℕ} (hL : L ≤ (D.second R hR hRs hFR).N)
    {T : DyadicCube d} (hT : T ∈ level L R) : T ∈ (D.second R hR hRs hFR).tree := by
  refine ⟨subset_of_mem_level hT, ?_⟩
  have := m_of_mem_level hT
  change R.m - ((D.second R hR hRs hFR).N : ℤ) ≤ T.m
  omega

/-- The leaf identity `∑_{T leaf} ψ_T v_T = 𝔥`, when `𝔥` and `v` are constant on the leaves (the
cubes of side length `2^{-N} ℓ(R)`). [PROVED] -/
theorem sum_level_xT_eq
    (hconst : ∀ T ∈ level (D.second R hR hRs hFR).N R,
      ConstOn (D.prunedH hR hRs hFR) T ∧ ConstOn (D.vP R) T) :
    ∑ T ∈ level (D.second R hR hRs hFR).N R, D.xT hR hRs hFR T = D.prunedH hR hRs hFR := by
  rw [← TestFun.truncateₗ_of_supportedOn (D.prunedH_supported hR hRs hFR),
    ← sum_level_truncateₗ (D.second R hR hRs hFR).N R]
  refine Finset.sum_congr rfl fun T hT => ?_
  exact coefOn_smul_eq_of_constOn (hconst T hT).1 (hconst T hT).2
    (D.avg_prunedH_eq_zero hR hRs hFR (D.mem_second_tree_of_mem_level hR hRs hFR le_rfl hT))

/-- The leaf identity `∑_{T leaf} φ_T u_T = 𝔤̂`, when `𝔤̂` and `u` are constant on the leaves.
[PROVED] -/
theorem sum_level_yT_eq
    (hconst : ∀ T ∈ level (D.second R hR hRs hFR).N R, ConstOn (D.ghat R) T ∧ ConstOn D.u T) :
    ∑ T ∈ level (D.second R hR hRs hFR).N R, D.yT R T = D.ghat R := by
  rw [← TestFun.truncateₗ_of_supportedOn (D.ghat_supported R),
    ← sum_level_truncateₗ (D.second R hR hRs hFR).N R]
  refine Finset.sum_congr rfl fun T hT => ?_
  exact coefOn_smul_eq_of_constOn (hconst T hT).1 (hconst T hT).2
    (D.avg_ghat_eq_zero (D.second_tree_subset hR hRs hFR
      (D.mem_second_tree_of_mem_level hR hRs hFR le_rfl hT)) (subset_of_mem_level hT))

/-- `ψ_T v_T − ∑_{T' child of T} ψ_{T'} v_{T'}` has mean zero for a non-leaf cube `T`. [PROVED] -/
theorem xT_sub_sum_meanZero {S : DyadicCube d} (hS : S ∈ nonleaf (D.second R hR hRs hFR).N R) :
    MeanZero ((D.xT hR hRs hFR S - ∑ c ∈ children S, D.xT hR hRs hFR c : TestFun d) :
      (Fin d → ℝ) → ℝ) := by
  obtain ⟨L', hL', hS⟩ := Finset.mem_biUnion.mp hS
  rw [Finset.mem_range] at hL'
  refine meanZero_sub_sum_children (x := D.xT hR hRs hFR) (f := D.prunedH hR hRs hFR) ?_ ?_
  · exact D.integralₗ_xT hR hRs hFR (D.mem_second_tree_of_mem_level hR hRs hFR hL'.le hS)
  · intro c hc
    exact D.integralₗ_xT hR hRs hFR (D.mem_second_tree_of_mem_level hR hRs hFR hL'
      (mem_level_succ_of_mem_children hS hc))

/-- `φ_T u_T − ∑_{T' child of T} φ_{T'} u_{T'}` has mean zero for a non-leaf cube `T`. [PROVED] -/
theorem yT_sub_sum_meanZero {S : DyadicCube d} (hS : S ∈ nonleaf (D.second R hR hRs hFR).N R) :
    MeanZero ((D.yT R S - ∑ c ∈ children S, D.yT R c : TestFun d) : (Fin d → ℝ) → ℝ) := by
  obtain ⟨L', hL', hS⟩ := Finset.mem_biUnion.mp hS
  rw [Finset.mem_range] at hL'
  refine meanZero_sub_sum_children (x := D.yT R) (f := D.ghat R) ?_ ?_
  · exact D.integralₗ_yT (D.second_tree_subset hR hRs hFR
      (D.mem_second_tree_of_mem_level hR hRs hFR hL'.le hS)) (subset_of_mem_level hS)
  · intro c hc
    have hc' := mem_level_succ_of_mem_children hS hc
    exact D.integralₗ_yT (D.second_tree_subset hR hRs hFR
      (D.mem_second_tree_of_mem_level hR hRs hFR hL' hc')) (subset_of_mem_level hc')

/-- **The telescoping (2.56)–(2.60)** (p. 51–52). Let `N` be the depth of the tree `𝒟_N(R)` of the
second stopping time and assume, as on p. 51, that `𝔥`, `v`, `𝔤̂`, `u` are constant on the cubes of
side length `2^{-N} ℓ(R)`. Then
`Λ_R(𝔥, 𝔤̂) = Λ_R(ψ_R v_R, φ_R u_R)                                                      (2.57)
   − ∑_T Λ_R(ψ_T v_T − ∑_{T'} ψ_{T'} v_{T'}, φ_T u_T)                                     (2.58)
   − ∑_T Λ_R(ψ_T v_T, φ_T u_T − ∑_{T'} φ_{T'} u_{T'})                                     (2.59)
   + ∑_T Λ_R(ψ_T v_T − ∑_{T'} ψ_{T'} v_{T'}, φ_T u_T − ∑_{T'} φ_{T'} u_{T'})`,             (2.60)
the sums over the cubes `T ⊆ R` of the tree of side length `> 2^{-N} ℓ(R)` (`nonleaf`,
`mem_nonleaf_iff`) and `T'` over the children of `T`. The term (2.57) vanishes, since `ψ_R = φ_R =
0`
(`psiT_self`, `phiT_self`). [PROVED] -/
theorem form2_prunedH_ghat_eq
    (hconst : ∀ T ∈ level (D.second R hR hRs hFR).N R,
      (ConstOn (D.prunedH hR hRs hFR) T ∧ ConstOn (D.vP R) T) ∧
        (ConstOn (D.ghat R) T ∧ ConstOn D.u T)) :
    twoSlotForm D.T D.a D.b D.g R (D.prunedH hR hRs hFR) (D.ghat R) =
      twoSlotForm D.T D.a D.b D.g R (D.xT hR hRs hFR R) (D.yT R R)
      - ∑ T ∈ nonleaf (D.second R hR hRs hFR).N R, twoSlotForm D.T D.a D.b D.g R
          (D.xT hR hRs hFR T - ∑ T' ∈ children T, D.xT hR hRs hFR T') (D.yT R T)
      - ∑ T ∈ nonleaf (D.second R hR hRs hFR).N R, twoSlotForm D.T D.a D.b D.g R
          (D.xT hR hRs hFR T) (D.yT R T - ∑ T' ∈ children T, D.yT R T')
      + ∑ T ∈ nonleaf (D.second R hR hRs hFR).N R, twoSlotForm D.T D.a D.b D.g R
          (D.xT hR hRs hFR T - ∑ T' ∈ children T, D.xT hR hRs hFR T')
          (D.yT R T - ∑ T' ∈ children T, D.yT R T') := by
  have key := telescoping D.T D.hab D.g R (D.second R hR hRs hFR).N (D.xT hR hRs hFR) (D.yT R)
    (D.xT_supportedOn hR hRs hFR) (D.yT_supportedOn R) (fun S hS => D.xT_sub_sum_meanZero hR hRs hFR
      hS)
    (fun S hS => D.yT_sub_sum_meanZero hR hRs hFR hS)
  rw [D.sum_level_xT_eq hR hRs hFR fun T hT => (hconst T hT).1,
    D.sum_level_yT_eq hR hRs hFR fun T hT => (hconst T hT).2] at key
  exact key

/-! #### §2.6 The estimate of the term (2.58) (p. 52–54)

The term (2.58) is `Λ_R(θ, u)` for the mean-zero function `θ = v ∑_T θ^T` supported on `R`, with
`θ^T = φ_T (ψ_T 𝟙_T − ∑_{T'} ψ_{T'} 𝟙_{T'})`: `φ_T` is moved to the first entry by bilinearity, and
the
factor `𝟙_T` in the second entry is dropped by the smoothness condition. By (2.10) at `R`,
`|Λ_R(θ, u)| ≤ C F ‖u‖_q (|R|/|Q|)^{1−1/r} ‖θ‖_r`, and it remains to bound `‖θ‖_r` (p. 53–54). Only
the
cubes `T` not contained in a second stopping cube contribute to `θ`, since `v θ^T = 0` on a cube
inside a second stopping cube (`𝔥 = ψ v` there). -/

/-- The function `θ^T = φ_T (ψ_T 𝟙_T − ∑_{T' child of T} ψ_{T'} 𝟙_{T'})` of p. 53. -/
noncomputable def thetaT (T : DyadicCube d) : TestFun d :=
  D.phiT R T • (D.psiT hR hRs hFR T • TestFun.ind T
    - ∑ T' ∈ children T, D.psiT hR hRs hFR T' • TestFun.ind T')

/-- The function `θ = v ∑_T θ^T = ∑_T φ_T (ψ_T v_T − ∑_{T'} ψ_{T'} v_{T'})` of p. 53
(`theta_apply`),
the sum over the non-leaf cubes `T ⊆ R` of the tree. -/
noncomputable def theta : TestFun d :=
  ∑ T ∈ nonleaf (D.second R hR hRs hFR).N R,
    D.phiT R T • (D.xT hR hRs hFR T - ∑ T' ∈ children T, D.xT hR hRs hFR T')

/-- `v 𝟙_T (x) = v(x) 𝟙_T(x)`. [PROVED] -/
theorem truncate_apply_eq_mul (T : DyadicCube d) (v : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) :
    truncate T v x = v x * T.toSet.indicator 1 x := by
  by_cases hx : x ∈ T.toSet
  · simp [truncate, hx]
  · simp [truncate, hx]

/-- `∑_{T ∈ s} φ_T (ψ_T v_T − ∑_{T'} ψ_{T'} v_{T'}) = v ∑_{T ∈ s} θ^T` pointwise. [PROVED] -/
theorem sum_smul_xT_apply (s : Finset (DyadicCube d)) (x : Fin d → ℝ) :
    ((∑ T ∈ s, D.phiT R T • (D.xT hR hRs hFR T - ∑ T' ∈ children T, D.xT hR hRs hFR T') :
        TestFun d) : (Fin d → ℝ) → ℝ) x =
      (D.vP R : (Fin d → ℝ) → ℝ) x *
        ((∑ T ∈ s, D.thetaT hR hRs hFR T : TestFun d) : (Fin d → ℝ) → ℝ) x := by
  simp only [thetaT, xT, Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_sub,
    Finset.sum_apply, Pi.smul_apply, Pi.sub_apply, TestFun.coe_truncateₗ, TestFun.coe_ind,
    smul_eq_mul, truncate_apply_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun T _ => ?_
  have e : ∑ T' ∈ children T, D.psiT hR hRs hFR T' *
      ((D.vP R : (Fin d → ℝ) → ℝ) x * T'.toSet.indicator 1 x) =
      (D.vP R : (Fin d → ℝ) → ℝ) x *
        ∑ T' ∈ children T, D.psiT hR hRs hFR T' * T'.toSet.indicator 1 x := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun T' _ => by ring
  rw [e]
  ring

/-- `θ = v ∑_T θ^T` pointwise. [PROVED] -/
theorem theta_apply (x : Fin d → ℝ) :
    (D.theta hR hRs hFR : (Fin d → ℝ) → ℝ) x =
      (D.vP R : (Fin d → ℝ) → ℝ) x *
        ((∑ T ∈ nonleaf (D.second R hR hRs hFR).N R, D.thetaT hR hRs hFR T : TestFun d) :
          (Fin d → ℝ) → ℝ) x := by
  rw [theta]
  exact D.sum_smul_xT_apply hR hRs hFR _ x

theorem theta_supportedOn : SupportedOn (D.theta hR hRs hFR : (Fin d → ℝ) → ℝ) R := by
  intro x hx
  rw [theta, Submodule.coe_sum, Finset.sum_apply]
  refine Finset.sum_eq_zero fun T hT => ?_
  have hTR : T.toSet ⊆ R.toSet := ((mem_nonleaf_iff D.hd).mp hT).1
  rw [Submodule.coe_smul, Pi.smul_apply,
    supportedOn_sub (D.xT_supportedOn hR hRs hFR T)
      (supportedOn_sum_children (D.xT_supportedOn hR hRs hFR) T) x (fun h => hx (hTR h)),
    smul_zero]

/-- `θ` has mean zero (p. 53): each `ψ_T v_T − ∑_{T'} ψ_{T'} v_{T'}` has. [PROVED] -/
theorem theta_meanZero : MeanZero (D.theta hR hRs hFR : (Fin d → ℝ) → ℝ) := by
  change TestFun.integralₗ (D.theta hR hRs hFR) = 0
  rw [theta, map_sum]
  refine Finset.sum_eq_zero fun T hT => ?_
  have h : TestFun.integralₗ (D.xT hR hRs hFR T - ∑ T' ∈ children T, D.xT hR hRs hFR T') = 0 :=
    D.xT_sub_sum_meanZero hR hRs hFR hT
  rw [map_smul, h, smul_zero]

/-- **(2.58) as `Λ_R(θ, u)`** (p. 52–53):
`∑_T Λ_R(ψ_T v_T − ∑_{T'} ψ_{T'} v_{T'}, φ_T u_T) = Λ_R(θ, u)`. [PROVED] -/
theorem sum_2_58_eq :
    ∑ T ∈ nonleaf (D.second R hR hRs hFR).N R, twoSlotForm D.T D.a D.b D.g R
        (D.xT hR hRs hFR T - ∑ T' ∈ children T, D.xT hR hRs hFR T') (D.yT R T) =
      twoSlotForm D.T D.a D.b D.g R (D.theta hR hRs hFR) D.u := by
  rw [theta, twoSlotForm_sum_left D.T D.hab]
  refine Finset.sum_congr rfl fun T hT => ?_
  rw [yT, twoSlotForm_smul_right, twoSlotForm_smul_left D.T D.hab]
  congr 1
  have hTR : T.toSet ⊆ R.toSet := ((mem_nonleaf_iff D.hd).mp hT).1
  have hsupp := supportedOn_sub (D.xT_supportedOn hR hRs hFR T)
    (supportedOn_sum_children (D.xT_supportedOn hR hRs hFR) T)
  have h0 := D.xT_sub_sum_meanZero hR hRs hFR hT
  rw [← twoSlotForm_eq_of_subset_left D.T D.hab D.g hTR hsupp h0 (TestFun.truncateₗ T D.u),
    twoSlotForm_truncateₗ_right, twoSlotForm_eq_of_subset_left D.T D.hab D.g hTR hsupp h0 D.u]

/-- **The estimate of (2.58) by (2.10)** (p. 53):
`|Λ_R(θ, u)| ≤ 2^d B F ‖u‖_q ε^{-1} (|R|/|Q|)^{1−1/r} ‖θ‖_r`. [PROVED] -/
theorem abs_form2_theta_le :
    |twoSlotForm D.T D.a D.b D.g R (D.theta hR hRs hFR) D.u| ≤
      2 ^ d * (D.B * D.F * lpNorm (D.u : (Fin d → ℝ) → ℝ) D.q * D.ε⁻¹) *
        (R.vol / D.Q.vol) ^ (1 - 1 / D.r) * lpNorm (D.theta hR hRs hFR : (Fin d → ℝ) → ℝ) D.r := by
  rw [twoSlotForm_self D.T D.hab]
  exact D.bound_2_10 D.hd (D.good_of_notInStopping hR hRs) _ (D.theta_supportedOn hR hRs hFR)
    (D.theta_meanZero hR hRs hFR)

/-- On a cube `T` inside a second stopping cube `S`, `ψ_T v_T = 𝔥_T` (p. 51: `𝔥` is a multiple of
`v`
on `S`). [PROVED] -/
theorem xT_eq_truncateₗ_prunedH {T S : DyadicCube d} (hS : S ∈ (D.second R hR hRs
  hFR).stoppingCubes)
    (hTS : T.toSet ⊆ S.toSet) :
    D.xT hR hRs hFR T = TestFun.truncateₗ T (D.prunedH hR hRs hFR) := by
  have h := (D.second R hR hRs hFR).exists_truncateₗ_pruned_eq_smul hS hTS
  rw [second_u] at h
  exact (truncateₗ_eq_coefOn_smul h).symm

/-- `v θ^T = 0` for a cube `T` inside a second stopping cube `S` (p. 53): there
`ψ_T v_T − ∑_{T'} ψ_{T'} v_{T'} = 𝔥_T − ∑_{T'} 𝔥_{T'} = 0`. [PROVED] -/
theorem xT_sub_sum_eq_zero {T S : DyadicCube d} (hS : S ∈ (D.second R hR hRs hFR).stoppingCubes)
    (hTS : T.toSet ⊆ S.toSet) :
    D.xT hR hRs hFR T - ∑ T' ∈ children T, D.xT hR hRs hFR T' = 0 := by
  rw [D.xT_eq_truncateₗ_prunedH hR hRs hFR hS hTS,
    Finset.sum_congr rfl fun c hc =>
      D.xT_eq_truncateₗ_prunedH hR hRs hFR hS ((subset_of_mem_children hc).trans hTS),
    sum_children_truncateₗ, sub_self]

open Classical in
/-- Only the non-leaf cubes `T` in no second stopping cube contribute to `θ` (p. 53). [PROVED] -/
theorem theta_eq_filter :
    D.theta hR hRs hFR =
      ∑ T ∈ (nonleaf (D.second R hR hRs hFR).N R).filter
          (fun T => (D.second R hR hRs hFR).NotInStopping T),
        D.phiT R T • (D.xT hR hRs hFR T - ∑ T' ∈ children T, D.xT hR hRs hFR T') := by
  rw [theta]
  symm
  refine Finset.sum_filter_of_ne fun T _ hne => ?_
  by_contra hTs
  simp only [NotInStopping, not_forall, not_not] at hTs
  obtain ⟨S, hS, hTS⟩ := hTs
  exact hne (by rw [D.xT_sub_sum_eq_zero hR hRs hFR hS hTS, smul_zero])

/-! The reduction of `‖θ‖_r` to `‖∑_T θ^T‖_r` (p. 53): with the partition `𝐏_R` of `R` into the
second
stopping cubes and the leaves of the tree not contained in a second stopping cube, the function
`Θ = ∑_T θ^T` (over the non-leaf `T` in no second stopping cube) is constant on every `P ∈ 𝐏_R`, so
`∫_P |θ|^r = |Θ_P|^r ∫_P |v|^r ≤ 2^d ε^{-1} (|P|/|R|) ‖v‖_r^r |Θ_P|^r` by (2.34) (the cubes of `𝐏_R`
are
good cubes of the second stopping time), and summing over `𝐏_R` gives
`‖θ‖_r^r ≤ 2^d B ε^{-1} ‖Θ‖_r^r`. -/

open Classical in
/-- `Θ = ∑_T θ^T`, the sum over the non-leaf cubes `T ⊆ R` in no second stopping cube. -/
noncomputable def Theta : TestFun d :=
  ∑ T ∈ (nonleaf (D.second R hR hRs hFR).N R).filter
      (fun T => (D.second R hR hRs hFR).NotInStopping T),
    D.thetaT hR hRs hFR T

/-- `θ = v Θ` pointwise. [PROVED] -/
theorem theta_apply_Theta (x : Fin d → ℝ) :
    (D.theta hR hRs hFR : (Fin d → ℝ) → ℝ) x =
      (D.vP R : (Fin d → ℝ) → ℝ) x * (D.Theta hR hRs hFR : (Fin d → ℝ) → ℝ) x := by
  rw [D.theta_eq_filter hR hRs hFR, Theta]
  exact D.sum_smul_xT_apply hR hRs hFR _ x

theorem thetaT_supportedOn (T : DyadicCube d) : SupportedOn (D.thetaT hR hRs hFR T) T :=
  fun x hx => by
  have h1 : ((TestFun.ind T : TestFun d) : (Fin d → ℝ) → ℝ) x = 0 := Set.indicator_of_notMem hx _
  have h2 : ((∑ T' ∈ children T, D.psiT hR hRs hFR T' • TestFun.ind T' : TestFun d) :
      (Fin d → ℝ) → ℝ) x = 0 := by
    rw [Submodule.coe_sum, Finset.sum_apply]
    refine Finset.sum_eq_zero fun T' hc => ?_
    rw [Submodule.coe_smul, Pi.smul_apply, TestFun.coe_ind,
      Set.indicator_of_notMem (fun h => hx (subset_of_mem_children hc h)), smul_zero]
  rw [thetaT, Submodule.coe_smul, Pi.smul_apply, Submodule.coe_sub, Pi.sub_apply,
    Submodule.coe_smul, Pi.smul_apply, h1, h2, smul_zero, sub_zero, smul_zero]

open Classical in
theorem Theta_supportedOn : SupportedOn (D.Theta hR hRs hFR) R := fun x hx => by
  rw [Theta, Submodule.coe_sum, Finset.sum_apply]
  refine Finset.sum_eq_zero fun T hT => ?_
  rw [Finset.mem_filter] at hT
  exact D.thetaT_supportedOn hR hRs hFR T x fun h => hx (((mem_nonleaf_iff D.hd).mp hT.1).1 h)

open Classical in
/-- The partition `𝐏_R` of `R` (p. 53): the second stopping cubes and the leaves of the tree not
contained in a second stopping cube. -/
noncomputable def partR : Finset (DyadicCube d) :=
  (D.second R hR hRs hFR).Pst ∪
    (level (D.second R hR hRs hFR).N R).filter
      (fun T => (D.second R hR hRs hFR).NotInStopping T)

theorem subset_of_mem_partR {P : DyadicCube d} (hP : P ∈ D.partR hR hRs hFR) :
    P.toSet ⊆ R.toSet := by
  classical
  rw [partR, Finset.mem_union, Finset.mem_filter] at hP
  rcases hP with hP | hP
  · exact ((D.second R hR hRs hFR).stoppingCubes_subset_tree'
      ((D.second R hR hRs hFR).mem_Pst.mp hP)).1
  · exact subset_of_mem_level hP.1

/-- The cubes of `𝐏_R` are good cubes of the second stopping time. [PROVED] -/
theorem good_of_mem_partR {P : DyadicCube d} (hP : P ∈ D.partR hR hRs hFR) :
    (D.second R hR hRs hFR).Good P := by
  classical
  rw [partR, Finset.mem_union, Finset.mem_filter] at hP
  rcases hP with hP | hP
  · exact (D.second R hR hRs hFR).good_of_mem_stoppingCubes ((D.second R hR hRs hFR).mem_Pst.mp hP)
  · exact (D.second R hR hRs hFR).good_of_notInStopping
      (D.mem_second_tree_of_mem_level hR hRs hFR le_rfl hP.1) hP.2

/-- A second stopping cube and a leaf not contained in a second stopping cube are disjoint.
[PROVED] -/
theorem disjoint_of_mem_Pst_of_mem_leaf {S T : DyadicCube d}
    (hS : S ∈ (D.second R hR hRs hFR).Pst) (hT : T ∈ level (D.second R hR hRs hFR).N R)
    (hTs : (D.second R hR hRs hFR).NotInStopping T) : Disjoint S.toSet T.toSet := by
  have hS' := (D.second R hR hRs hFR).mem_Pst.mp hS
  have h1 : ¬ T.toSet ⊆ S.toSet := hTs S hS'
  refine DyadicCube.disjoint_of_not_subset h1 fun h2 => h1 ?_
  have hm1 := DyadicCube.m_le_of_subset D.hd h2
  have hm2 : R.m - ((D.second R hR hRs hFR).N : ℤ) ≤ S.m :=
    ((D.second R hR hRs hFR).stoppingCubes_subset_tree' hS').2
  have hm3 := m_of_mem_level hT
  have e := DyadicCube.eq_of_subset_of_m_eq h2 (by omega)
  subst e
  exact subset_rfl

/-- The cubes of `𝐏_R` are pairwise disjoint. [PROVED] -/
theorem partR_pairwiseDisjoint :
    (↑(D.partR hR hRs hFR) : Set (DyadicCube d)).PairwiseDisjoint DyadicCube.toSet := by
  classical
  intro P hP P' hP' hne
  rw [Finset.mem_coe, partR, Finset.mem_union, Finset.mem_filter] at hP hP'
  change Disjoint P.toSet P'.toSet
  rcases hP with hP | hP <;> rcases hP' with hP' | hP'
  · exact maximal_pairwiseDisjoint _ ((D.second R hR hRs hFR).mem_Pst.mp hP)
      ((D.second R hR hRs hFR).mem_Pst.mp hP') hne
  · exact D.disjoint_of_mem_Pst_of_mem_leaf hR hRs hFR hP hP'.1 hP'.2
  · exact (D.disjoint_of_mem_Pst_of_mem_leaf hR hRs hFR hP' hP.1 hP.2).symm
  · exact (level_eq_or_disjoint hP.1 hP'.1).resolve_left hne

/-- The cubes of `𝐏_R` cover `R`. [PROVED] -/
theorem partR_cover : ⋃ P ∈ D.partR hR hRs hFR, P.toSet = R.toSet := by
  classical
  apply Set.Subset.antisymm
  · exact Set.iUnion₂_subset fun P hP => D.subset_of_mem_partR hR hRs hFR hP
  · intro x hx
    obtain ⟨T, hT, hxT⟩ := exists_mem_level (D.second R hR hRs hFR).N hx
    rw [Set.mem_iUnion₂]
    by_cases hTs : (D.second R hR hRs hFR).NotInStopping T
    · exact ⟨T, by rw [partR, Finset.mem_union, Finset.mem_filter]; exact Or.inr ⟨hT, hTs⟩, hxT⟩
    · simp only [NotInStopping, not_forall, not_not] at hTs
      obtain ⟨S, hS, hTS⟩ := hTs
      exact ⟨S, by rw [partR, Finset.mem_union]; exact Or.inl ((D.second R hR hRs hFR).mem_Pst.mpr
        hS),
        hTS hxT⟩

/-- A non-leaf cube `T` in no second stopping cube and a cube `P ∈ 𝐏_R`: `P ⊆ T` or `P ∩ T = ∅`.
[PROVED] -/
theorem subset_or_disjoint_of_mem_partR {T P : DyadicCube d}
    (hT : T ∈ nonleaf (D.second R hR hRs hFR).N R) (hTs : (D.second R hR hRs hFR).NotInStopping T)
    (hP : P ∈ D.partR hR hRs hFR) : P.toSet ⊆ T.toSet ∨ Disjoint P.toSet T.toSet := by
  classical
  rw [partR, Finset.mem_union, Finset.mem_filter] at hP
  rcases hP with hP | hP
  · have h1 : ¬ T.toSet ⊆ P.toSet := hTs P ((D.second R hR hRs hFR).mem_Pst.mp hP)
    rcases le_total P.m T.m with hm | hm
    · rcases DyadicCube.subset_or_disjoint P T hm with h | h
      · exact Or.inl h
      · exact Or.inr h
    · rcases DyadicCube.subset_or_disjoint T P hm with h | h
      · exact absurd h h1
      · exact Or.inr h.symm
  · have hm1 := m_of_mem_level hP.1
    have hm2 := ((mem_nonleaf_iff D.hd).mp hT).2
    rcases DyadicCube.subset_or_disjoint P T (by omega) with h | h
    · exact Or.inl h
    · exact Or.inr h

/-- The same for the children `T'` of `T`: `P ⊆ T'` or `P ∩ T' = ∅`. [PROVED] -/
theorem child_subset_or_disjoint_of_mem_partR {T T' P : DyadicCube d}
    (hT : T ∈ nonleaf (D.second R hR hRs hFR).N R) (hTs : (D.second R hR hRs hFR).NotInStopping T)
    (hc : T' ∈ children T) (hP : P ∈ D.partR hR hRs hFR) :
    P.toSet ⊆ T'.toSet ∨ Disjoint P.toSet T'.toSet := by
  classical
  obtain ⟨ε, rfl⟩ := mem_children.mp hc
  have hm' : (T.child ε).m = T.m - 1 := rfl
  rw [partR, Finset.mem_union, Finset.mem_filter] at hP
  rcases hP with hP | hP
  · have h1 : ¬ T.toSet ⊆ P.toSet := hTs P ((D.second R hR hRs hFR).mem_Pst.mp hP)
    rcases le_total P.m (T.child ε).m with hm | hm
    · rcases DyadicCube.subset_or_disjoint P (T.child ε) hm with h | h
      · exact Or.inl h
      · exact Or.inr h
    · rcases DyadicCube.subset_or_disjoint (T.child ε) P hm with h | h
      · rcases le_or_gt T.m P.m with hm2 | hm2
        · rcases DyadicCube.subset_or_disjoint T P hm2 with h3 | h3
          · exact absurd h3 h1
          · exact absurd (h (T.child ε).corner_mem)
              (Set.disjoint_left.mp h3 (T.child_subset ε (T.child ε).corner_mem))
        · have e : T.child ε = P := DyadicCube.eq_of_subset_of_m_eq h (by omega)
          rw [e]
          exact Or.inl subset_rfl
      · exact Or.inr h.symm
  · have hm1 := m_of_mem_level hP.1
    have hm2 := ((mem_nonleaf_iff D.hd).mp hT).2
    rcases DyadicCube.subset_or_disjoint P (T.child ε) (by omega) with h | h
    · exact Or.inl h
    · exact Or.inr h

/-- `θ^T` is constant on every cube of `𝐏_R`, for `T` non-leaf in no second stopping cube. [PROVED]
-/
theorem thetaT_constOn {T P : DyadicCube d} (hT : T ∈ nonleaf (D.second R hR hRs hFR).N R)
    (hTs : (D.second R hR hRs hFR).NotInStopping T) (hP : P ∈ D.partR hR hRs hFR) :
    ConstOn (D.thetaT hR hRs hFR T) P := by
  unfold thetaT
  exact constOn_smul _ (constOn_sub
    (constOn_smul _ (constOn_ind (D.subset_or_disjoint_of_mem_partR hR hRs hFR hT hTs hP)))
    (constOn_sum fun T' hc => constOn_smul _
      (constOn_ind (D.child_subset_or_disjoint_of_mem_partR hR hRs hFR hT hTs hc hP))))

/-- `Θ` is constant on every cube of `𝐏_R`. [PROVED] -/
theorem Theta_constOn {P : DyadicCube d} (hP : P ∈ D.partR hR hRs hFR) :
    ConstOn (D.Theta hR hRs hFR) P := by
  classical
  unfold Theta
  refine constOn_sum fun T hT => ?_
  rw [Finset.mem_filter] at hT
  exact D.thetaT_constOn hR hRs hFR hT.1 hT.2 hP

/-- `∫ |f|^r = ∑_{P ∈ 𝐏_R} ∫_P |f|^r` for `f` supported on `R`. [PROVED] -/
theorem integral_abs_rpow_eq_sum_partR {f : TestFun d} (hf : SupportedOn f R) {r : ℝ}
    (hr : 0 < r) :
    ∫ x, |(f : (Fin d → ℝ) → ℝ) x| ^ r =
      ∑ P ∈ D.partR hR hRs hFR, ∫ x in P.toSet, |(f : (Fin d → ℝ) → ℝ) x| ^ r := by
  rw [← integral_biUnion_finset _ (fun P _ => P.measurableSet_toSet)
    (D.partR_pairwiseDisjoint hR hRs hFR)
    (fun P _ => (TestFun.integrable_abs_rpow f hr).integrableOn), D.partR_cover hR hRs hFR]
  exact (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
    rw [hf x hx, abs_zero, Real.zero_rpow hr.ne']).symm

/-- **(2.34) in real form**: `∫_P |v|^r ≤ 2^d ε^{-1} (|P|/|R|) B |R|` on good cubes of the second
stopping time. [PROVED] -/
theorem setIntegral_vP_rpow_le {P : DyadicCube d} (hP : (D.second R hR hRs hFR).Good P) :
    ∫ x in P.toSet, |(D.vP R : (Fin d → ℝ) → ℝ) x| ^ D.r ≤
      2 ^ d / D.ε * (P.vol / R.vol) * (D.B * R.vol) := by
  have hr0 : 0 < D.r := by linarith [D.hr]
  have hε := D.ε_pos
  have hP0 := P.vol_pos
  have hR0 := R.vol_pos
  have h := TestFun.setIntegral_rpow_le_of_avg_le (D.vP R) hr0 P R (by positivity)
    (D.second_bound_2_34 hR hRs hFR hP)
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  exact (setIntegral_le_integral (TestFun.integrable_abs_rpow _ hr0)
    (Filter.Eventually.of_forall fun x => by positivity)).trans (D.vP_norm R hR.1)

/-- **The reduction of `‖θ‖_r` to `‖Θ‖_r`** (p. 53): `‖θ‖_r^r ≤ 2^d B ε^{-1} ‖Θ‖_r^r`. [PROVED] -/
theorem lpNorm_theta_rpow_le :
    lpNorm (D.theta hR hRs hFR : (Fin d → ℝ) → ℝ) D.r ^ D.r ≤
      2 ^ d * D.B / D.ε * lpNorm (D.Theta hR hRs hFR : (Fin d → ℝ) → ℝ) D.r ^ D.r := by
  have hr0 : 0 < D.r := by linarith [D.hr]
  have hε := D.ε_pos
  have hB : 0 ≤ D.B := by linarith [D.hB]
  rw [lpNorm_rpow_eq_integral hr0 (TestFun.memLp (D.theta hR hRs hFR).2 _),
    lpNorm_rpow_eq_integral hr0 (TestFun.memLp (D.Theta hR hRs hFR).2 _),
    D.integral_abs_rpow_eq_sum_partR hR hRs hFR (D.theta_supportedOn hR hRs hFR) hr0,
    D.integral_abs_rpow_eq_sum_partR hR hRs hFR (D.Theta_supportedOn hR hRs hFR) hr0,
    Finset.mul_sum]
  refine Finset.sum_le_sum fun P hP => ?_
  have hconst := D.Theta_constOn hR hRs hFR hP
  obtain ⟨c, hc⟩ : ∃ c : ℝ, ∀ x ∈ P.toSet, (D.Theta hR hRs hFR : (Fin d → ℝ) → ℝ) x = c :=
    ⟨_, fun x hx => hconst x hx _ P.corner_mem⟩
  have e1 : ∫ x in P.toSet, |(D.theta hR hRs hFR : (Fin d → ℝ) → ℝ) x| ^ D.r =
      |c| ^ D.r * ∫ x in P.toSet, |(D.vP R : (Fin d → ℝ) → ℝ) x| ^ D.r := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun P.measurableSet_toSet fun x hx => ?_
    change |(D.theta hR hRs hFR : (Fin d → ℝ) → ℝ) x| ^ D.r =
      |c| ^ D.r * |(D.vP R : (Fin d → ℝ) → ℝ) x| ^ D.r
    rw [D.theta_apply_Theta hR hRs hFR x, hc x hx, abs_mul,
      Real.mul_rpow (abs_nonneg _) (abs_nonneg _), mul_comm]
  have e2 : ∫ x in P.toSet, |(D.Theta hR hRs hFR : (Fin d → ℝ) → ℝ) x| ^ D.r = |c| ^ D.r * P.vol :=
    by
    have e : ∫ x in P.toSet, |(D.Theta hR hRs hFR : (Fin d → ℝ) → ℝ) x| ^ D.r =
        ∫ x in P.toSet, |c| ^ D.r :=
      setIntegral_congr_fun P.measurableSet_toSet fun x hx => by
        show |(D.Theta hR hRs hFR : (Fin d → ℝ) → ℝ) x| ^ D.r = |c| ^ D.r
        rw [hc x hx]
    rw [e, setIntegral_const, measureReal_def, P.volume_toSet, ENNReal.toReal_ofReal P.vol_pos.le,
      smul_eq_mul, mul_comm]
  rw [e1, e2]
  have h34 := D.setIntegral_vP_rpow_le hR hRs hFR (D.good_of_mem_partR hR hRs hFR hP)
  have hc0 : 0 ≤ |c| ^ D.r := Real.rpow_nonneg (abs_nonneg _) _
  have hR0 := R.vol_pos.ne'
  calc |c| ^ D.r * ∫ x in P.toSet, |(D.vP R : (Fin d → ℝ) → ℝ) x| ^ D.r
      ≤ |c| ^ D.r * (2 ^ d / D.ε * (P.vol / R.vol) * (D.B * R.vol)) :=
        mul_le_mul_of_nonneg_left h34 hc0
    _ = 2 ^ d * D.B / D.ε * (|c| ^ D.r * P.vol) := by
        have : P.vol / R.vol * (D.B * R.vol) = D.B * P.vol := by
          field_simp
        rw [mul_assoc (2 ^ d / D.ε), this]
        ring

/-- `‖θ‖_r ≤ (2^d B/ε)^{1/r} ‖Θ‖_r` (p. 53). [PROVED] -/
theorem lpNorm_theta_le :
    lpNorm (D.theta hR hRs hFR : (Fin d → ℝ) → ℝ) D.r ≤
      (2 ^ d * D.B / D.ε) ^ (1 / D.r) * lpNorm (D.Theta hR hRs hFR : (Fin d → ℝ) → ℝ) D.r := by
  have hr0 : 0 < D.r := by linarith [D.hr]
  have hε := D.ε_pos
  have hB : 0 ≤ D.B := by linarith [D.hB]
  have hC : 0 ≤ 2 ^ d * D.B / D.ε := by positivity
  have h := TestFun.lpNorm_le_rpow_of_integral_le (D.theta hR hRs hFR) hr0
    (C := 2 ^ d * D.B / D.ε * lpNorm (D.Theta hR hRs hFR : (Fin d → ℝ) → ℝ) D.r ^ D.r) (by
      rw [← lpNorm_rpow_eq_integral hr0 (TestFun.memLp (D.theta hR hRs hFR).2 _)]
      exact D.lpNorm_theta_rpow_le hR hRs hFR)
  refine h.trans (le_of_eq ?_)
  rw [Real.mul_rpow hC (Real.rpow_nonneg (lpNorm_nonneg _ _) _), one_div,
    Real.rpow_rpow_inv (lpNorm_nonneg _ _) hr0.ne']

end Telescoping

end StoppingData

end StoppingCollections

/-! ## §2.9 Outer measure spaces (paper, p. 56–59) -/

/-- The martingale average `E_T f = |[f]_T|` (2.63). -/
noncomputable def martAvg (T : DyadicCube d) (f : (Fin d → ℝ) → ℝ) : ℝ := |avg T f|

/-- The martingale difference `Δ_T f = (|T|⁻¹ ∑_{T' child of T} |[f]_{T'} − [f]_T|² |T'|)^{1/2}`
(2.63). -/
noncomputable def martDiff (T : DyadicCube d) (f : (Fin d → ℝ) → ℝ) : ℝ :=
  Real.sqrt (T.vol⁻¹ * ∑ ε : Fin d → Bool, |avg (T.child ε) f - avg T f| ^ 2 * (T.child ε).vol)

/-- A size function assigns to `F : 𝒟 → ℝ` and a tree `𝒟(T)` a number `S(F)(𝒟(T)) ∈ [0, ∞]`. -/
abbrev Size (d : ℕ) := (DyadicCube d → ℝ) → DyadicCube d → ENNReal

/-- The size `S_p(F)(𝒟(T)) = (|T|⁻¹ ∑_{Q ∈ 𝒟(T)} |F(Q)|^p |Q|)^{1/p}` (valued in `[0, ∞]`). -/
noncomputable def sizeP (p : ℝ) : Size d := fun F T =>
  (ENNReal.ofReal T.vol⁻¹ *
    ∑' Q : T.tree, ‖F Q‖ₑ ^ p * ENNReal.ofReal (Q : DyadicCube d).vol) ^ (1 / p)

/-- The size `S_∞(F)(𝒟(T)) = sup_{Q ∈ 𝒟(T)} |F(Q)|` (valued in `[0, ∞]`). -/
noncomputable def sizeInf : Size d := fun F T => ⨆ Q : T.tree, ‖F Q‖ₑ

/-- The outer measure `μ` on `𝒟` generated by `κ(𝒟(T)) = |T|`. -/
noncomputable def outerMeasure (A : Set (DyadicCube d)) : ENNReal :=
  ⨅ (G : Set (DyadicCube d)) (_ : A ⊆ ⋃ T ∈ G, T.tree),
    ∑' T : G, ENNReal.ofReal (T : DyadicCube d).vol

/-- The superlevel measure `μ(S(F) > λ) = inf {μ(𝒢) : S(F 𝟙_{𝒟∖𝒢}) ≤ λ}`. -/
noncomputable def superlevel (S : Size d) (F : DyadicCube d → ℝ) (lam : ℝ) : ENNReal :=
  ⨅ (G : Set (DyadicCube d)) (_ : ∀ T, S (Gᶜ.indicator F) T ≤ ENNReal.ofReal lam),
    outerMeasure G

/-- The outer `L^∞(X, κ, S)` norm `sup_T S(F)(𝒟(T))`. -/
noncomputable def outerLinfNorm (S : Size d) (F : DyadicCube d → ℝ) : ENNReal := ⨆ T, S F T

/-- The outer `L^p(X, κ, S)` norm `(p ∫₀^∞ λ^{p-1} μ(S(F) > λ) dλ)^{1/p}`. -/
noncomputable def outerLpNorm (S : Size d) (p : ℝ) (F : DyadicCube d → ℝ) : ENNReal :=
  (ENNReal.ofReal p *
    ∫⁻ lam in Set.Ioi (0 : ℝ), ENNReal.ofReal (lam ^ (p - 1)) * superlevel S F lam) ^ (1 / p)

/-- The weak outer `L^{p,∞}(X, κ, S)` norm `(sup_λ λ^p μ(S(F) > λ))^{1/p}`. -/
noncomputable def outerWeakLpNorm (S : Size d) (p : ℝ) (F : DyadicCube d → ℝ) : ENNReal :=
  (⨆ lam : Set.Ioi (0 : ℝ), ENNReal.ofReal ((lam : ℝ) ^ p) * superlevel S F lam) ^ (1 / p)

/-- **Theorem 2.68** (discrete Carleson embedding): `‖E(f)‖_{L^p(X,κ,S_∞)} ≤ C ‖f‖_p` (2.69) and
`‖Δ(f)‖_{L^p(X,κ,S_2)} ≤ C ‖f‖_p` (2.70), for `1 < p < ∞`. (The paper states `p ∈ [1, ∞)`; at
`p = 1` only the weak-type bounds hold, and the interpolation argument of the paper gives the
strong bounds exactly for `1 < p < ∞`.) Proved below as `carlesonEmbedding`. [PROVED] -/
def CarlesonEmbedding (d : ℕ) (p : ℝ) : Prop :=
  1 < p → ∃ C : ℝ, 0 ≤ C ∧ ∀ f : (Fin d → ℝ) → ℝ, MemLp f (ENNReal.ofReal p) volume →
    outerLpNorm sizeInf p (fun T => martAvg T f) ≤
        ENNReal.ofReal C * eLpNorm f (ENNReal.ofReal p) volume ∧
    outerLpNorm (sizeP 2) p (fun T => martDiff T f) ≤
        ENNReal.ofReal C * eLpNorm f (ENNReal.ofReal p) volume

/-! ### Endpoint estimates in the proof of Theorem 2.68 (paper, p. 57) -/

instance : Inhabited (DyadicCube d) := ⟨⟨0, fun _ => 0⟩⟩

/-- `|[f]_Q| ≤ ‖f‖_∞` for `f ∈ L^∞`. [PROVED] -/
theorem memLp_top_ae_bound {f : (Fin d → ℝ) → ℝ} (hf : MemLp f ⊤ volume) :
    ∀ᵐ x ∂volume, ‖f x‖ ≤ supNorm f := by
  have hne : eLpNormEssSup f volume ≠ ⊤ := by
    have := hf.eLpNorm_lt_top
    rw [eLpNorm_exponent_top hf.aestronglyMeasurable] at this
    exact this.ne
  filter_upwards [(ae_le_eLpNormEssSup : ∀ᵐ x ∂volume, ‖f x‖ₑ ≤ eLpNormEssSup f volume)]
    with x hx
  rw [supNorm, eLpNorm_exponent_top hf.aestronglyMeasurable, ← toReal_enorm (f x)]
  exact ENNReal.toReal_mono hne hx

/-- Lebesgue measure restricted to a dyadic cube is finite. -/
theorem abs_avg_le_supNorm (Q : DyadicCube d) {f : (Fin d → ℝ) → ℝ} (hf : MemLp f ⊤ volume) :
    |avg Q f| ≤ supNorm f := by
  have hint := norm_integral_le_of_norm_le_const
    (ae_restrict_of_ae (s := Q.toSet) (memLp_top_ae_bound hf))
  rw [measureReal_def, Measure.restrict_apply_univ, DyadicCube.volume_toSet,
    ENNReal.toReal_ofReal Q.vol_pos.le, Real.norm_eq_abs] at hint
  rw [avg, abs_div, abs_of_pos Q.vol_pos, div_le_iff₀ Q.vol_pos]
  exact hint

/-- (2.69) at the endpoint `p = ∞`: `‖E(f)‖_{L^∞(X,κ,S_∞)} = sup_T sup_{Q ∈ 𝒟(T)} |[f]_Q| ≤ ‖f‖_∞`.
[PROVED] -/
theorem outerLinfNorm_martAvg_le {f : (Fin d → ℝ) → ℝ} (hf : MemLp f ⊤ volume) :
    outerLinfNorm sizeInf (fun T => martAvg T f) ≤ eLpNorm f ⊤ volume := by
  rw [← ENNReal.ofReal_toReal hf.eLpNorm_ne_top]
  simp only [outerLinfNorm, sizeInf, martAvg, Real.enorm_eq_ofReal_abs, abs_abs]
  exact iSup_le fun T => iSup_le fun Q => ENNReal.ofReal_le_ofReal (abs_avg_le_supNorm _ hf)

/-- The maximal-cube bound in the proof of (2.69) for `p = 1` (paper, p. 57): if finitely many
pairwise disjoint cubes `Q` satisfy `λ < |[f]_Q|`, then `∑ |Q| ≤ ‖f‖₁ / λ`. [PROVED] -/
theorem sum_vol_le_of_lt_abs_avg {ι : Type*} (S : Finset ι) (Q : ι → DyadicCube d)
    (hdisj : (S : Set ι).PairwiseDisjoint fun i => (Q i).toSet)
    {f : (Fin d → ℝ) → ℝ} (hf : Integrable f volume) {lam : ℝ} (hlam : 0 < lam)
    (hQ : ∀ i ∈ S, lam < |avg (Q i) f|) :
    ∑ i ∈ S, (Q i).vol ≤ (∫ x, |f x|) / lam := by
  rw [le_div_iff₀ hlam, Finset.sum_mul]
  calc ∑ i ∈ S, (Q i).vol * lam ≤ ∑ i ∈ S, ∫ x in (Q i).toSet, |f x| := by
        refine Finset.sum_le_sum fun i hi => ?_
        have h1 := hQ i hi
        rw [avg, abs_div, abs_of_pos (Q i).vol_pos, lt_div_iff₀ (Q i).vol_pos] at h1
        have h2 : (Q i).vol * lam ≤ |∫ x in (Q i).toSet, f x| := by
          rw [mul_comm]
          exact h1.le
        exact h2.trans abs_integral_le_integral_abs
    _ = ∫ x in ⋃ i ∈ S, (Q i).toSet, |f x| :=
        (integral_biUnion_finset S (fun i _ => (Q i).measurableSet_toSet) hdisj
          (fun i _ => hf.abs.integrableOn)).symm
    _ ≤ ∫ x, |f x| :=
        setIntegral_le_integral hf.abs (Filter.Eventually.of_forall fun x => abs_nonneg _)

/-! ### Martingale orthogonality: the case `p = ∞` of (2.70) (paper, p. 58)

We prove `S_2(Δ f)(𝒟(T))² = |T|⁻¹ ∑_{Q ∈ 𝒟(T)} ‖Δ_Q f‖² |Q| ≤ |T|⁻¹ ∫_T |f|² ≤ ‖f‖_∞²`. The
orthogonality of the martingale differences is encoded in the one-step Pythagoras identity
`V_Q f = ∑_ε V_{Q_ε} f + ‖Δ_Q f‖² |Q|` for the variance `V_Q f = ∫_Q f² − [f]_Q² |Q| ≥ 0`, which
is then iterated down the dyadic tree. -/

section Martingale


variable {f : (Fin d → ℝ) → ℝ}

/-- An a.e. bounded measurable function is integrable on every cube. [PROVED] -/
theorem integrableOn_of_ae_bound (Q : DyadicCube d) {g : (Fin d → ℝ) → ℝ}
    (hg : AEStronglyMeasurable g volume) {M : ℝ} (hM : ∀ᵐ x ∂volume, ‖g x‖ ≤ M) :
    IntegrableOn g Q.toSet volume :=
  Integrable.mono' (integrable_const M) hg.restrict (ae_restrict_of_ae hM)

/-- `‖f²‖ ≤ M²` a.e. if `‖f‖ ≤ M` a.e. [PROVED] -/
theorem ae_norm_sq_le {M : ℝ} (hM : ∀ᵐ x ∂volume, ‖f x‖ ≤ M) :
    ∀ᵐ x ∂volume, ‖f x ^ 2‖ ≤ M ^ 2 := by
  filter_upwards [hM] with x hx
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) hx 2

/-- `f²` is integrable on every cube if `f` is a.e. bounded and measurable. [PROVED] -/
theorem integrableOn_sq_of_ae_bound (Q : DyadicCube d) (hmeas : AEStronglyMeasurable f volume)
    {M : ℝ} (hM : ∀ᵐ x ∂volume, ‖f x‖ ≤ M) :
    IntegrableOn (fun x => f x ^ 2) Q.toSet volume :=
  integrableOn_of_ae_bound Q (hmeas.pow 2) (ae_norm_sq_le hM)

/-- `∑_ε |Q_ε| = |Q|`. [PROVED] -/
theorem DyadicCube.sum_vol_child (Q : DyadicCube d) :
    ∑ ε : Fin d → Bool, (Q.child ε).vol = Q.vol := by
  have h : ∀ ε : Fin d → Bool, (Q.child ε).vol = Q.vol / 2 ^ d := fun ε => by
    rw [eq_div_iff (by positivity)]
    exact Q.vol_child ε
  simp only [h, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin, nsmul_eq_mul]
  push_cast
  rw [mul_div_assoc', mul_div_cancel_left₀ _ (by positivity)]

/-- `∑_ε [f]_{Q_ε} |Q_ε| = [f]_Q |Q|`. [PROVED] -/
theorem sum_avg_child_mul_vol (Q : DyadicCube d) (hf : IntegrableOn f Q.toSet volume) :
    ∑ ε : Fin d → Bool, avg (Q.child ε) f * (Q.child ε).vol = avg Q f * Q.vol := by
  simp only [avg_mul_vol]
  exact (Q.integral_children hf).symm

/-- `‖Δ_Q f‖² |Q| = ∑_ε ([f]_{Q_ε} − [f]_Q)² |Q_ε|`, the quantity summed in `S_2(Δ f)`. -/
noncomputable def dsq (Q : DyadicCube d) (f : (Fin d → ℝ) → ℝ) : ℝ :=
  ∑ ε : Fin d → Bool, (avg (Q.child ε) f - avg Q f) ^ 2 * (Q.child ε).vol

theorem dsq_nonneg {Q : DyadicCube d} : 0 ≤ dsq Q f :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (sq_nonneg _) (DyadicCube.vol_pos _).le

/-- `|Δ_Q f|² |Q| = dsq Q f`. [PROVED] -/
theorem martDiff_sq_mul_vol (Q : DyadicCube d) (f : (Fin d → ℝ) → ℝ) :
    |martDiff Q f| ^ 2 * Q.vol = dsq Q f := by
  have h0 : 0 ≤ Q.vol⁻¹ * ∑ ε : Fin d → Bool,
      |avg (Q.child ε) f - avg Q f| ^ 2 * (Q.child ε).vol :=
    mul_nonneg (inv_nonneg.mpr Q.vol_pos.le)
      (Finset.sum_nonneg fun _ _ => mul_nonneg (sq_nonneg _) (DyadicCube.vol_pos _).le)
  rw [martDiff, abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt h0, dsq, mul_comm, ← mul_assoc,
    mul_inv_cancel₀ Q.vol_pos.ne', one_mul]
  simp only [sq_abs]

/-- The variance `V_Q f = ∫_Q f² − [f]_Q² |Q|`. -/
noncomputable def var (Q : DyadicCube d) (f : (Fin d → ℝ) → ℝ) : ℝ :=
  (∫ x in Q.toSet, f x ^ 2) - (avg Q f) ^ 2 * Q.vol

/-- `V_Q f = ∫_Q (f − [f]_Q)²`. [PROVED] -/
theorem var_eq (Q : DyadicCube d) (hf : IntegrableOn f Q.toSet volume)
    (hf2 : IntegrableOn (fun x => f x ^ 2) Q.toSet volume) :
    var Q f = ∫ x in Q.toSet, (f x - avg Q f) ^ 2 := by
  have e : (fun x => (f x - avg Q f) ^ 2) =
      fun x => (f x ^ 2 - 2 * avg Q f * f x) + avg Q f ^ 2 := by
    funext x
    ring
  have hint := avg_mul_vol Q f
  have hA : Integrable (fun x => f x ^ 2 - 2 * avg Q f * f x) (volume.restrict Q.toSet) :=
    hf2.sub (hf.const_mul _)
  have hB : Integrable (fun _ => avg Q f ^ 2) (volume.restrict Q.toSet) := integrable_const _
  rw [e, integral_add hA hB, integral_sub hf2 (hf.const_mul _), integral_const_mul,
    setIntegral_const, measureReal_def, Q.volume_toSet, ENNReal.toReal_ofReal Q.vol_pos.le,
    smul_eq_mul, var]
  linear_combination (-2 * avg Q f) * hint

/-- `V_Q f ≥ 0`. [PROVED] -/
theorem var_nonneg (Q : DyadicCube d) (hf : IntegrableOn f Q.toSet volume)
    (hf2 : IntegrableOn (fun x => f x ^ 2) Q.toSet volume) : 0 ≤ var Q f := by
  rw [var_eq Q hf hf2]
  exact integral_nonneg fun x => sq_nonneg _

/-- Pythagoras for one dyadic step: `V_Q f = ∑_ε V_{Q_ε} f + ‖Δ_Q f‖² |Q|`. [PROVED] -/
theorem var_eq_sum_children (Q : DyadicCube d)
    (hf : ∀ P : DyadicCube d, IntegrableOn f P.toSet volume)
    (hf2 : ∀ P : DyadicCube d, IntegrableOn (fun x => f x ^ 2) P.toSet volume) :
    var Q f = ∑ ε : Fin d → Bool, var (Q.child ε) f + dsq Q f := by
  have h1 := Q.integral_children (hf2 Q)
  have h2 := sum_avg_child_mul_vol Q (hf Q)
  have h3 := Q.sum_vol_child
  have e : ∑ ε : Fin d → Bool, (avg (Q.child ε) f - avg Q f) ^ 2 * (Q.child ε).vol
      = ∑ ε : Fin d → Bool, avg (Q.child ε) f ^ 2 * (Q.child ε).vol
        - 2 * avg Q f * ∑ ε : Fin d → Bool, avg (Q.child ε) f * (Q.child ε).vol
        + avg Q f ^ 2 * ∑ ε : Fin d → Bool, (Q.child ε).vol := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ε _ => ?_
    ring
  simp only [var, dsq]
  rw [h1, Finset.sum_sub_distrib, e, h2, h3]
  ring

open Classical in
/-- Bessel-type inequality: for a finite family `F` of cubes whose members inside `T` have
side length at least `2^{-n} ℓ(T)`, `∑_{Q ∈ F, Q ⊆ T} ‖Δ_Q f‖² |Q| ≤ V_T f`. Induction on `n`.
[PROVED] -/
theorem sum_dsq_le_var (hd : d ≠ 0) (hf : ∀ P : DyadicCube d, IntegrableOn f P.toSet volume)
    (hf2 : ∀ P : DyadicCube d, IntegrableOn (fun x => f x ^ 2) P.toSet volume)
    (F : Finset (DyadicCube d)) (n : ℕ) :
    ∀ T : DyadicCube d, (∀ Q ∈ F, Q.toSet ⊆ T.toSet → T.m - (n : ℤ) ≤ Q.m) →
      ∑ Q ∈ F.filter (fun Q => Q.toSet ⊆ T.toSet), dsq Q f ≤ var T f := by
  classical
  induction n with
  | zero =>
    intro T hT
    have hsub : F.filter (fun Q => Q.toSet ⊆ T.toSet) ⊆ {T} := by
      intro Q hQ
      rw [Finset.mem_filter] at hQ
      rw [Finset.mem_singleton]
      have h1 := hT Q hQ.1 hQ.2
      have h2 := DyadicCube.m_le_of_subset hd hQ.2
      exact DyadicCube.eq_of_subset_of_m_eq hQ.2 (by omega)
    have hV := var_eq_sum_children T hf hf2
    have hpos : 0 ≤ ∑ ε : Fin d → Bool, var (T.child ε) f :=
      Finset.sum_nonneg fun ε _ => var_nonneg (T.child ε) (hf _) (hf2 _)
    calc ∑ Q ∈ F.filter (fun Q => Q.toSet ⊆ T.toSet), dsq Q f
        ≤ ∑ Q ∈ ({T} : Finset (DyadicCube d)), dsq Q f :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => dsq_nonneg
      _ = dsq T f := Finset.sum_singleton _ _
      _ ≤ var T f := by linarith
  | succ n ih =>
    intro T hT
    -- separate the cube `T` itself
    have step1 : ∑ Q ∈ F.filter (fun Q => Q.toSet ⊆ T.toSet), dsq Q f ≤
        dsq T f + ∑ Q ∈ F.filter (fun Q => Q.toSet ⊆ T.toSet ∧ Q ≠ T), dsq Q f := by
      have hsub : F.filter (fun Q => Q.toSet ⊆ T.toSet) ⊆
          insert T (F.filter (fun Q => Q.toSet ⊆ T.toSet ∧ Q ≠ T)) := by
        intro Q hQ
        rw [Finset.mem_filter] at hQ
        rw [Finset.mem_insert, Finset.mem_filter]
        by_cases h : Q = T
        · exact Or.inl h
        · exact Or.inr ⟨hQ.1, hQ.2, h⟩
      have hT' : T ∉ F.filter (fun Q => Q.toSet ⊆ T.toSet ∧ Q ≠ T) := by
        simp
      refine (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => dsq_nonneg).trans ?_
      rw [Finset.sum_insert hT']
    -- the proper subcubes are distributed among the children
    have step2 : ∑ Q ∈ F.filter (fun Q => Q.toSet ⊆ T.toSet ∧ Q ≠ T), dsq Q f ≤
        ∑ ε : Fin d → Bool,
          ∑ Q ∈ F.filter (fun Q => Q.toSet ⊆ (T.child ε).toSet), dsq Q f := by
      calc ∑ Q ∈ F.filter (fun Q => Q.toSet ⊆ T.toSet ∧ Q ≠ T), dsq Q f
          ≤ ∑ Q ∈ F.filter (fun Q => Q.toSet ⊆ T.toSet ∧ Q ≠ T),
              ∑ ε : Fin d → Bool, if Q.toSet ⊆ (T.child ε).toSet then dsq Q f else 0 := by
            refine Finset.sum_le_sum fun Q hQ => ?_
            rw [Finset.mem_filter] at hQ
            obtain ⟨ε, hε⟩ := DyadicCube.exists_child_of_ssubset hd hQ.2.1 hQ.2.2
            have := Finset.single_le_sum (s := Finset.univ)
              (f := fun ε => if Q.toSet ⊆ (T.child ε).toSet then dsq Q f else 0)
              (fun ε _ => by
                split_ifs
                exacts [dsq_nonneg, le_rfl]) (Finset.mem_univ ε)
            simpa [hε] using this
        _ = ∑ ε : Fin d → Bool, ∑ Q ∈ (F.filter (fun Q => Q.toSet ⊆ T.toSet ∧ Q ≠ T)).filter
              (fun Q => Q.toSet ⊆ (T.child ε).toSet), dsq Q f := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun ε _ => ?_
            rw [← Finset.sum_filter]
        _ ≤ ∑ ε : Fin d → Bool,
              ∑ Q ∈ F.filter (fun Q => Q.toSet ⊆ (T.child ε).toSet), dsq Q f := by
            refine Finset.sum_le_sum fun ε _ => ?_
            exact Finset.sum_le_sum_of_subset_of_nonneg
              (Finset.filter_subset_filter _ (Finset.filter_subset _ _)) fun _ _ _ => dsq_nonneg
    -- the induction hypothesis on each child
    have step3 : ∀ ε : Fin d → Bool,
        ∑ Q ∈ F.filter (fun Q => Q.toSet ⊆ (T.child ε).toSet), dsq Q f ≤ var (T.child ε) f := by
      intro ε
      apply ih
      intro Q hQ hQε
      have := hT Q hQ (hQε.trans (T.child_subset ε))
      simp only [DyadicCube.child]
      omega
    have step4 := Finset.sum_le_sum fun ε (_ : ε ∈ (Finset.univ : Finset (Fin d → Bool))) =>
      step3 ε
    rw [var_eq_sum_children T hf hf2]
    linarith

/-- For a bounded measurable `f` and every finite subfamily `s ⊆ 𝒟(T)`:
`∑_{Q ∈ s} ‖Δ_Q f‖² |Q| ≤ ∫_T f²`. [PROVED] -/
theorem sum_dsq_le_integral (hd : d ≠ 0) (hmeas : AEStronglyMeasurable f volume) {M : ℝ}
    (hM : ∀ᵐ x ∂volume, ‖f x‖ ≤ M) (T : DyadicCube d) (s : Finset T.tree) :
    ∑ Q ∈ s, dsq (Q : DyadicCube d) f ≤ ∫ x in T.toSet, f x ^ 2 := by
  classical
  have hf : ∀ P : DyadicCube d, IntegrableOn f P.toSet volume :=
    fun P => integrableOn_of_ae_bound P hmeas hM
  have hf2 : ∀ P : DyadicCube d, IntegrableOn (fun x => f x ^ 2) P.toSet volume :=
    fun P => integrableOn_sq_of_ae_bound P hmeas hM
  set F : Finset (DyadicCube d) := s.map (Function.Embedding.subtype _) with hF
  have hmem : ∀ Q ∈ F, Q.toSet ⊆ T.toSet := by
    intro Q hQ
    rw [hF, Finset.mem_map] at hQ
    obtain ⟨⟨Q', hQ'⟩, _, rfl⟩ := hQ
    exact hQ'
  have hsum : ∑ Q ∈ s, dsq (Q : DyadicCube d) f =
      ∑ Q ∈ F.filter (fun Q => Q.toSet ⊆ T.toSet), dsq Q f := by
    rw [Finset.filter_true_of_mem hmem, hF, Finset.sum_map]
    rfl
  have key := sum_dsq_le_var hd hf hf2 F (F.sup fun Q => (T.m - Q.m).toNat) T (by
    intro Q hQ _
    have : (T.m - Q.m).toNat ≤ F.sup fun Q : DyadicCube d => (T.m - Q.m).toNat :=
      Finset.le_sup (f := fun Q : DyadicCube d => (T.m - Q.m).toNat) hQ
    omega)
  rw [hsum]
  refine key.trans ?_
  simp only [var]
  linarith [mul_nonneg (sq_nonneg (avg T f)) T.vol_pos.le]

/-- The family `Q ↦ ‖Δ_Q f‖² |Q|` is summable over `𝒟(T)` for bounded measurable `f`.
[PROVED] -/
theorem summable_dsq (hd : d ≠ 0) (hmeas : AEStronglyMeasurable f volume) {M : ℝ}
    (hM : ∀ᵐ x ∂volume, ‖f x‖ ≤ M) (T : DyadicCube d) :
    Summable fun Q : T.tree => dsq (Q : DyadicCube d) f :=
  summable_of_sum_le (fun _ => dsq_nonneg) (sum_dsq_le_integral hd hmeas hM T)

/-- For a bounded measurable `f`: `∑_{Q ∈ 𝒟(T)} ‖Δ_Q f‖² |Q| ≤ ∫_T f²`. [PROVED] -/
theorem tsum_dsq_le (hd : d ≠ 0) (hmeas : AEStronglyMeasurable f volume) {M : ℝ}
    (hM : ∀ᵐ x ∂volume, ‖f x‖ ≤ M) (T : DyadicCube d) :
    ∑' Q : T.tree, dsq (Q : DyadicCube d) f ≤ ∫ x in T.toSet, f x ^ 2 :=
  tsum_le_of_sum_le' (integral_nonneg fun _ => sq_nonneg _) (sum_dsq_le_integral hd hmeas hM T)

/-- `∫_T f² ≤ M² |T|` if `‖f‖ ≤ M` a.e. [PROVED] -/
theorem integral_sq_le (T : DyadicCube d) (hmeas : AEStronglyMeasurable f volume) {M : ℝ}
    (hM : ∀ᵐ x ∂volume, ‖f x‖ ≤ M) : ∫ x in T.toSet, f x ^ 2 ≤ M ^ 2 * T.vol := by
  have h := integral_mono_ae (integrableOn_sq_of_ae_bound T hmeas hM) (integrable_const (M ^ 2))
    (ae_restrict_of_ae (s := T.toSet) (hM.mono fun x hx => by
      change f x ^ 2 ≤ M ^ 2
      rw [← sq_abs (f x), ← Real.norm_eq_abs]
      exact pow_le_pow_left₀ (norm_nonneg _) hx 2))
  rwa [setIntegral_const, measureReal_def, T.volume_toSet, ENNReal.toReal_ofReal T.vol_pos.le,
    smul_eq_mul, mul_comm] at h

/-- `S_2(F)(𝒟(T))` as the `ENNReal.ofReal` of a real quantity, when the summands
`|F(Q)|² |Q|` are given by a summable nonnegative real family. [PROVED] -/
theorem sizeP_two_eq_ofReal (F : DyadicCube d → ℝ) (T : DyadicCube d) (a : T.tree → ℝ)
    (ha : ∀ Q : T.tree, |F Q| ^ 2 * (Q : DyadicCube d).vol = a Q) (h0 : ∀ Q, 0 ≤ a Q)
    (hs : Summable a) :
    sizeP 2 F T = ENNReal.ofReal ((T.vol⁻¹ * ∑' Q, a Q) ^ (1 / 2 : ℝ)) := by
  have hterm : ∀ Q : T.tree,
      ‖F Q‖ₑ ^ (2 : ℝ) * ENNReal.ofReal (Q : DyadicCube d).vol = ENNReal.ofReal (a Q) := by
    intro Q
    rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num),
      Real.rpow_two, ← ENNReal.ofReal_mul (sq_nonneg _), ha]
  simp only [sizeP, hterm]
  rw [← ENNReal.ofReal_tsum_of_nonneg h0 hs, ← ENNReal.ofReal_mul (inv_nonneg.mpr T.vol_pos.le),
    ENNReal.ofReal_rpow_of_nonneg (mul_nonneg (inv_nonneg.mpr T.vol_pos.le) (tsum_nonneg h0))
      (by norm_num)]

/-- A real bound `|T|⁻¹ ∑ a_Q ≤ M²` gives `S_2(F)(𝒟(T)) ≤ M`. [PROVED] -/
theorem sizeP_two_le_ofReal (F : DyadicCube d → ℝ) (T : DyadicCube d) (a : T.tree → ℝ)
    (ha : ∀ Q : T.tree, |F Q| ^ 2 * (Q : DyadicCube d).vol = a Q) (h0 : ∀ Q, 0 ≤ a Q)
    (hs : Summable a) {M : ℝ} (hM : 0 ≤ M) (hb : T.vol⁻¹ * ∑' Q, a Q ≤ M ^ 2) :
    sizeP 2 F T ≤ ENNReal.ofReal M := by
  rw [sizeP_two_eq_ofReal F T a ha h0 hs, ← Real.sqrt_eq_rpow]
  exact ENNReal.ofReal_le_ofReal ((Real.sqrt_le_sqrt hb).trans_eq (Real.sqrt_sq hM))

/-- (2.70) at the endpoint `p = ∞`: `‖Δ(f)‖_{L^∞(X,κ,S_2)} ≤ ‖f‖_∞` (paper, p. 58). [PROVED] -/
theorem outerLinfNorm_martDiff_le (hd : d ≠ 0) (hf : MemLp f ⊤ volume) :
    outerLinfNorm (sizeP 2) (fun T => martDiff T f) ≤ eLpNorm f ⊤ volume := by
  have hM := memLp_top_ae_bound hf
  have hM0 : 0 ≤ supNorm f := ENNReal.toReal_nonneg
  rw [← ENNReal.ofReal_toReal hf.eLpNorm_ne_top]
  refine iSup_le fun T => ?_
  refine sizeP_two_le_ofReal _ T (fun Q => dsq (Q : DyadicCube d) f)
    (fun Q => martDiff_sq_mul_vol _ f) (fun _ => dsq_nonneg)
    (summable_dsq hd hf.aestronglyMeasurable hM T) hM0 ?_
  have h2 := tsum_dsq_le hd hf.aestronglyMeasurable hM T
  have h3 := integral_sq_le T hf.aestronglyMeasurable hM
  calc T.vol⁻¹ * ∑' Q : T.tree, dsq (Q : DyadicCube d) f
      ≤ T.vol⁻¹ * (supNorm f ^ 2 * T.vol) :=
        mul_le_mul_of_nonneg_left (h2.trans h3) (inv_nonneg.mpr T.vol_pos.le)
    _ = supNorm f ^ 2 := by
        rw [mul_comm (supNorm f ^ 2), ← mul_assoc, inv_mul_cancel₀ T.vol_pos.ne', one_mul]

end Martingale

/-! ### The case `p = 1` of (2.69): `μ(S_∞(E f) > λ) ≤ ‖f‖₁/λ` (paper, p. 57–58)

Following the paper, `𝓕` is the collection of maximal cubes with `|[f]_Q| > λ` and
`𝒢 = ⋃_{Q ∈ 𝓕} 𝒟(Q)`; then `S_∞(E(f) 𝟙_{𝒟∖𝒢}) ≤ λ` on every tree and
`μ(𝒢) ≤ ∑_{Q ∈ 𝓕} |Q| ≤ ‖f‖₁/λ`. -/

section WeakType


variable {f : (Fin d → ℝ) → ℝ}

/-- The cubes with `|[f]_Q| > λ`. -/
def badCubes (f : (Fin d → ℝ) → ℝ) (lam : ℝ) : Set (DyadicCube d) := {Q | lam < |avg Q f|}

/-- The maximal cubes with `|[f]_Q| > λ` (the collection `𝓕` of p. 57). -/
def maxBadCubes (f : (Fin d → ℝ) → ℝ) (lam : ℝ) : Set (DyadicCube d) :=
  {Q | Q ∈ badCubes f lam ∧ ∀ R ∈ badCubes f lam, Q.toSet ⊆ R.toSet → R = Q}

/-- The collection `𝒢 = ⋃_{Q ∈ 𝓕} 𝒟(Q)` of p. 58. -/
def badTrees (f : (Fin d → ℝ) → ℝ) (lam : ℝ) : Set (DyadicCube d) :=
  {P | ∃ Q ∈ maxBadCubes f lam, P.toSet ⊆ Q.toSet}

/-- A cube with `|[f]_Q| > λ` has measure `< ‖f‖₁/λ`. [PROVED] -/
theorem vol_lt_of_mem_badCubes (hf : Integrable f volume) {lam : ℝ} (hlam : 0 < lam)
    {Q : DyadicCube d} (hQ : Q ∈ badCubes f lam) : Q.vol < (∫ x, |f x|) / lam := by
  have h1 : lam < |avg Q f| := hQ
  rw [avg, abs_div, abs_of_pos Q.vol_pos, lt_div_iff₀ Q.vol_pos] at h1
  have h2 : |∫ x in Q.toSet, f x| ≤ ∫ x, |f x| :=
    abs_integral_le_integral_abs.trans
      (setIntegral_le_integral hf.abs (Filter.Eventually.of_forall fun x => abs_nonneg _))
  rw [lt_div_iff₀ hlam]
  linarith

/-- The side lengths of cubes with `|[f]_Q| > λ` are bounded above. [PROVED] -/
theorem exists_scale_bound (hd : d ≠ 0) (hf : Integrable f volume) {lam : ℝ} (hlam : 0 < lam) :
    ∃ n : ℕ, ∀ Q ∈ badCubes f lam, Q.m < n := by
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt ((∫ x, |f x|) / lam) (by norm_num : (1 : ℝ) < 2)
  refine ⟨n, fun Q hQ => ?_⟩
  have h1 := vol_lt_of_mem_badCubes hf hlam hQ
  have h2 : (2 : ℝ) ^ (Q.m * d) < (2 : ℝ) ^ (n : ℤ) := by
    rw [zpow_natCast]
    exact h1.trans hn
  have h3 : Q.m * d < n := by
    by_contra hcon
    rw [not_lt] at hcon
    exact absurd h2 (not_lt.mpr ((zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mpr hcon))
  have hd' : (1 : ℤ) ≤ d := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hd
  rcases le_or_gt 0 Q.m with h | h
  · nlinarith
  · omega

/-- Every cube with `|[f]_Q| > λ` is contained in a maximal one. [PROVED] -/
theorem exists_maxBad_superset (hd : d ≠ 0) (hf : Integrable f volume) {lam : ℝ}
    (hlam : 0 < lam) {Q : DyadicCube d} (hQ : Q ∈ badCubes f lam) :
    ∃ R ∈ maxBadCubes f lam, Q.toSet ⊆ R.toSet := by
  classical
  obtain ⟨n, hn⟩ := exists_scale_bound hd hf hlam
  -- bad cubes containing `Q` have scale `Q.m + k` with `k ≤ (n - Q.m).toNat`; take `k` maximal
  have hP0 : ∃ R ∈ badCubes f lam, Q.toSet ⊆ R.toSet ∧ R.m = Q.m + ((0 : ℕ) : ℤ) :=
    ⟨Q, hQ, subset_rfl, by simp⟩
  have hbound : ∀ k : ℕ, (∃ R ∈ badCubes f lam, Q.toSet ⊆ R.toSet ∧ R.m = Q.m + (k : ℤ)) →
      k ≤ (n - Q.m).toNat := by
    rintro k ⟨R, hR, -, hRm⟩
    have := hn R hR
    omega
  obtain ⟨R, hR, hQR, hRm⟩ := Nat.findGreatest_spec
    (P := fun k : ℕ => ∃ R ∈ badCubes f lam, Q.toSet ⊆ R.toSet ∧ R.m = Q.m + (k : ℤ))
    (hbound 0 hP0) hP0
  refine ⟨R, ⟨hR, fun R' hR' hRR' => ?_⟩, hQR⟩
  have hmQ := DyadicCube.m_le_of_subset hd (hQR.trans hRR')
  have hk' : ∃ R'' ∈ badCubes f lam, Q.toSet ⊆ R''.toSet ∧
      R''.m = Q.m + (((R'.m - Q.m).toNat : ℕ) : ℤ) :=
    ⟨R', hR', hQR.trans hRR', by omega⟩
  have hle := Nat.le_findGreatest
    (P := fun k : ℕ => ∃ R ∈ badCubes f lam, Q.toSet ⊆ R.toSet ∧ R.m = Q.m + (k : ℤ))
    (hbound _ hk') hk'
  have hmR := DyadicCube.m_le_of_subset hd hRR'
  have hm : R'.m = R.m := by omega
  exact (DyadicCube.eq_of_subset_of_m_eq hRR' hm.symm).symm

/-- Outside `𝒢`, every cube has `|[f]_P| ≤ λ`. [PROVED] -/
theorem abs_avg_le_of_not_mem_badTrees (hd : d ≠ 0) (hf : Integrable f volume) {lam : ℝ}
    (hlam : 0 < lam) {P : DyadicCube d} (hP : P ∉ badTrees f lam) : |avg P f| ≤ lam := by
  by_contra h
  rw [not_le] at h
  obtain ⟨R, hR, hPR⟩ := exists_maxBad_superset hd hf hlam h
  exact hP ⟨R, hR, hPR⟩

/-- Distinct maximal cubes are disjoint. [PROVED] -/
theorem maxBad_disjoint {lam : ℝ} {Q R : DyadicCube d} (hQ : Q ∈ maxBadCubes f lam)
    (hR : R ∈ maxBadCubes f lam) (hne : Q ≠ R) : Disjoint Q.toSet R.toSet := by
  rcases le_total Q.m R.m with h | h
  · rcases DyadicCube.subset_or_disjoint Q R h with hsub | hdis
    · exact absurd (hQ.2 R hR.1 hsub) hne.symm
    · exact hdis
  · rcases DyadicCube.subset_or_disjoint R Q h with hsub | hdis
    · exact absurd (hR.2 Q hQ.1 hsub) hne
    · exact hdis.symm

/-- `S_∞(E(f) 𝟙_{𝒟∖𝒢})(𝒟(T)) ≤ λ` for every `T`. [PROVED] -/
theorem sizeInf_indicator_le (hd : d ≠ 0) (hf : Integrable f volume) {lam : ℝ} (hlam : 0 < lam)
    (T : DyadicCube d) :
    sizeInf ((badTrees f lam)ᶜ.indicator fun P => martAvg P f) T ≤ ENNReal.ofReal lam := by
  simp only [sizeInf]
  refine iSup_le fun P => ?_
  by_cases hP : (P : DyadicCube d) ∈ badTrees f lam
  · rw [Set.indicator_of_notMem (by simpa using hP)]
    simp
  · rw [Set.indicator_of_mem (by simpa using hP), martAvg, Real.enorm_eq_ofReal_abs, abs_abs]
    exact ENNReal.ofReal_le_ofReal (abs_avg_le_of_not_mem_badTrees hd hf hlam hP)

/-- `μ(𝒢) ≤ ∑_{Q ∈ 𝓕} |Q| ≤ ‖f‖₁/λ` for the collection `𝒢 = ⋃_{Q ∈ 𝓕} 𝒟(Q)`. [PROVED] -/
theorem outerMeasure_badTrees_le (hf : Integrable f volume) {lam : ℝ} (hlam : 0 < lam) :
    outerMeasure (badTrees f lam) ≤ ENNReal.ofReal ((∫ x, |f x|) / lam) := by
  refine (iInf₂_le (maxBadCubes f lam) ?_).trans ?_
  · intro P hP
    obtain ⟨Q, hQ, hPQ⟩ := hP
    exact Set.mem_biUnion hQ hPQ
  · rw [ENNReal.tsum_eq_iSup_sum]
    refine iSup_le fun s => ?_
    rw [← ENNReal.ofReal_sum_of_nonneg fun Q _ => (DyadicCube.vol_pos _).le]
    apply ENNReal.ofReal_le_ofReal
    refine sum_vol_le_of_lt_abs_avg s (fun Q => (Q : DyadicCube d)) ?_ hf hlam fun Q _ => Q.2.1
    intro Q _ R _ hne
    exact maxBad_disjoint Q.2 R.2 fun h => hne (Subtype.ext h)

/-- (2.69) at `p = 1` in weak form: `μ(S_∞(E f) > λ) ≤ ‖f‖₁/λ` (paper, p. 57–58). [PROVED] -/
theorem superlevel_martAvg_le (hd : d ≠ 0) (hf : Integrable f volume) {lam : ℝ}
    (hlam : 0 < lam) :
    superlevel sizeInf (fun T => martAvg T f) lam ≤ ENNReal.ofReal ((∫ x, |f x|) / lam) :=
  (iInf₂_le (badTrees f lam) (sizeInf_indicator_le hd hf hlam)).trans
    (outerMeasure_badTrees_le hf hlam)

/-- (2.69) at `p = 1`: `‖E(f)‖_{L^{1,∞}(X,κ,S_∞)} ≤ ‖f‖₁`. [PROVED] -/
theorem outerWeakL1Norm_martAvg_le (hd : d ≠ 0) (hf : Integrable f volume) :
    outerWeakLpNorm sizeInf 1 (fun T => martAvg T f) ≤ ENNReal.ofReal (∫ x, |f x|) := by
  simp only [outerWeakLpNorm, div_one, Real.rpow_one, ENNReal.rpow_one]
  refine iSup_le fun lam => ?_
  have hlam : 0 < (lam : ℝ) := lam.2
  calc ENNReal.ofReal (lam : ℝ) * superlevel sizeInf (fun T => martAvg T f) lam
      ≤ ENNReal.ofReal (lam : ℝ) * ENNReal.ofReal ((∫ x, |f x|) / lam) := by
        have hb := superlevel_martAvg_le hd hf hlam
        gcongr
    _ = ENNReal.ofReal (∫ x, |f x|) := by
        rw [← ENNReal.ofReal_mul hlam.le, mul_div_assoc', mul_div_cancel_left₀ _ hlam.ne']

end WeakType

/-! ### The case `p = 1` of (2.70): `μ(S_2(Δ f) > 2^d λ) ≤ ‖f‖₁/λ` (paper, p. 58)

The stopping cubes are the maximal cubes with `[|f|]_Q > λ` (the Calderón–Zygmund cubes at
height `λ`; the paper writes `|[f]_Q| > λ`, which for signed `f` does not give the bound
`‖g‖_∞ ≤ 2^d λ`). The good function `g` is not formed explicitly: the estimate
`∑_{Q ∈ 𝒟(T) ∖ 𝒢} ‖Δ_Q f‖² |Q| ≤ (2^d λ)² |T|` follows from the one-step Pythagoras identity
iterated down the tree and stopped at `𝒢`, using only that the averages of `|f|` on the cubes
outside `𝒢` are at most `λ` and on the stopping cubes at most `2^d λ`. This avoids the
Lebesgue differentiation theorem that the pointwise bound `‖g‖_∞ ≤ 2^d λ` would require. -/

section CZ


variable {f : (Fin d → ℝ) → ℝ}

open Classical in
/-- Splitting a filtered sum over subcubes of `T` into the term at `T` and the sums over the
children (nonnegative summands). [PROVED] -/
theorem sum_filter_le_add_children (hd : d ≠ 0) (F : Finset (DyadicCube d)) (T : DyadicCube d)
    (p : DyadicCube d → Prop) [DecidablePred p] (g : DyadicCube d → ℝ) (hg : ∀ Q, 0 ≤ g Q) :
    ∑ Q ∈ F.filter (fun Q => Q.toSet ⊆ T.toSet ∧ p Q), g Q ≤
      g T + ∑ ε : Fin d → Bool,
        ∑ Q ∈ F.filter (fun Q => Q.toSet ⊆ (T.child ε).toSet ∧ p Q), g Q := by
  have step1 : ∑ Q ∈ F.filter (fun Q => Q.toSet ⊆ T.toSet ∧ p Q), g Q ≤
      g T + ∑ Q ∈ F.filter (fun Q => Q.toSet ⊆ T.toSet ∧ p Q ∧ Q ≠ T), g Q := by
    have hsub : F.filter (fun Q => Q.toSet ⊆ T.toSet ∧ p Q) ⊆
        insert T (F.filter (fun Q => Q.toSet ⊆ T.toSet ∧ p Q ∧ Q ≠ T)) := by
      intro Q hQ
      rw [Finset.mem_filter] at hQ
      rw [Finset.mem_insert, Finset.mem_filter]
      by_cases h : Q = T
      · exact Or.inl h
      · exact Or.inr ⟨hQ.1, hQ.2.1, hQ.2.2, h⟩
    have hT' : T ∉ F.filter (fun Q => Q.toSet ⊆ T.toSet ∧ p Q ∧ Q ≠ T) := by
      simp
    refine (Finset.sum_le_sum_of_subset_of_nonneg hsub fun Q _ _ => hg Q).trans ?_
    rw [Finset.sum_insert hT']
  have step2 : ∑ Q ∈ F.filter (fun Q => Q.toSet ⊆ T.toSet ∧ p Q ∧ Q ≠ T), g Q ≤
      ∑ ε : Fin d → Bool,
        ∑ Q ∈ F.filter (fun Q => Q.toSet ⊆ (T.child ε).toSet ∧ p Q), g Q := by
    calc ∑ Q ∈ F.filter (fun Q => Q.toSet ⊆ T.toSet ∧ p Q ∧ Q ≠ T), g Q
        ≤ ∑ Q ∈ F.filter (fun Q => Q.toSet ⊆ T.toSet ∧ p Q ∧ Q ≠ T),
            ∑ ε : Fin d → Bool, if Q.toSet ⊆ (T.child ε).toSet then g Q else 0 := by
          refine Finset.sum_le_sum fun Q hQ => ?_
          rw [Finset.mem_filter] at hQ
          obtain ⟨ε, hε⟩ := DyadicCube.exists_child_of_ssubset hd hQ.2.1 hQ.2.2.2
          have := Finset.single_le_sum (s := Finset.univ)
            (f := fun ε => if Q.toSet ⊆ (T.child ε).toSet then g Q else 0)
            (fun ε _ => by
              split_ifs
              exacts [hg Q, le_rfl]) (Finset.mem_univ ε)
          simpa [hε] using this
      _ = ∑ ε : Fin d → Bool, ∑ Q ∈ (F.filter (fun Q => Q.toSet ⊆ T.toSet ∧ p Q ∧ Q ≠ T)).filter
            (fun Q => Q.toSet ⊆ (T.child ε).toSet), g Q := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun ε _ => ?_
          rw [← Finset.sum_filter]
      _ ≤ ∑ ε : Fin d → Bool,
            ∑ Q ∈ F.filter (fun Q => Q.toSet ⊆ (T.child ε).toSet ∧ p Q), g Q := by
          refine Finset.sum_le_sum fun ε _ => ?_
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun Q _ _ => hg Q
          intro Q hQ
          simp only [Finset.mem_filter] at hQ ⊢
          exact ⟨hQ.1.1, hQ.2, hQ.1.2.2.1⟩
  linarith

/-- The one-step Pythagoras identity in the form
`∑_ε [f]_{Q_ε}² |Q_ε| = [f]_Q² |Q| + ‖Δ_Q f‖² |Q|`. [PROVED] -/
theorem sum_sq_avg_child (Q : DyadicCube d) (hf : IntegrableOn f Q.toSet volume) :
    ∑ ε : Fin d → Bool, avg (Q.child ε) f ^ 2 * (Q.child ε).vol =
      avg Q f ^ 2 * Q.vol + dsq Q f := by
  have h2 := sum_avg_child_mul_vol Q hf
  have h3 := Q.sum_vol_child
  have e : dsq Q f = ∑ ε : Fin d → Bool, avg (Q.child ε) f ^ 2 * (Q.child ε).vol
        - 2 * avg Q f * ∑ ε : Fin d → Bool, avg (Q.child ε) f * (Q.child ε).vol
        + avg Q f ^ 2 * ∑ ε : Fin d → Bool, (Q.child ε).vol := by
    rw [dsq, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ε _ => ?_
    ring
  rw [e, h2, h3]
  ring

/-- `|[f]_Q| ≤ [|f|]_Q`. [PROVED] -/
theorem abs_avg_le_avg_abs (Q : DyadicCube d) (f : (Fin d → ℝ) → ℝ) :
    |avg Q f| ≤ avg Q (fun x => |f x|) := by
  rw [avg, avg, abs_div, abs_of_pos Q.vol_pos]
  exact div_le_div_of_nonneg_right abs_integral_le_integral_abs Q.vol_pos.le

/-- `∫_Q g ≤ ∫_{Q̂} g` for nonnegative integrable `g`. [PROVED] -/
theorem setIntegral_le_parent (Q : DyadicCube d) {g : (Fin d → ℝ) → ℝ}
    (hg : IntegrableOn g Q.parent.toSet volume) (hg0 : ∀ x, 0 ≤ g x) :
    ∫ x in Q.toSet, g x ≤ ∫ x in Q.parent.toSet, g x := by
  rw [Q.parent.integral_children hg]
  have := Finset.single_le_sum (s := Finset.univ)
    (f := fun ε => ∫ x in (Q.parent.child ε).toSet, g x)
    (fun ε _ => integral_nonneg fun x => hg0 x) (Finset.mem_univ (fun i => decide (Q.l i % 2 = 1)))
  simpa [Q.child_parent] using this

/-- The parent of a maximal cube is not a bad cube. [PROVED] -/
theorem parent_not_mem_badCubes {g : (Fin d → ℝ) → ℝ} {lam : ℝ} {Q : DyadicCube d}
    (hQ : Q ∈ maxBadCubes g lam) : Q.parent ∉ badCubes g lam := by
  intro h
  have hsub := DyadicCube.child_subset Q.parent (fun i => decide (Q.l i % 2 = 1))
  rw [Q.child_parent] at hsub
  have hm := congrArg DyadicCube.m (hQ.2 _ h hsub)
  simp only [DyadicCube.parent] at hm
  omega

/-- A maximal cube at height `λ` for `|f|` has `[|f|]_Q ≤ 2^d λ`. [PROVED] -/
theorem avg_abs_le_of_maxBad (hf : Integrable f volume) {lam : ℝ} {Q : DyadicCube d}
    (hQ : Q ∈ maxBadCubes (fun x => |f x|) lam) : avg Q (fun x => |f x|) ≤ 2 ^ d * lam := by
  have hP : avg Q.parent (fun x => |f x|) ≤ lam :=
    not_lt.mp fun h => parent_not_mem_badCubes hQ (lt_of_lt_of_le h (le_abs_self _))
  have h1 := setIntegral_le_parent Q hf.abs.integrableOn (fun x => abs_nonneg _)
  rw [← avg_mul_vol, ← avg_mul_vol, Q.vol_parent] at h1
  have h2d : (0 : ℝ) < 2 ^ d := by positivity
  have h3 : avg Q (fun x => |f x|) ≤ 2 ^ d * avg Q.parent (fun x => |f x|) :=
    le_of_mul_le_mul_right (h1.trans_eq (by ring)) Q.vol_pos
  exact h3.trans (mul_le_mul_of_nonneg_left hP h2d.le)

/-- The children of a cube `T ∉ 𝒢` have `[|f|]_{T_ε} ≤ 2^d λ`: either `T_ε` is itself a
stopping cube, or it is not a bad cube. [PROVED] -/
theorem avg_abs_child_le (hd : d ≠ 0) (hf : Integrable f volume) {lam : ℝ} (hlam : 0 < lam)
    {T : DyadicCube d} (hT : T ∉ badTrees (fun x => |f x|) lam) (ε : Fin d → Bool) :
    avg (T.child ε) (fun x => |f x|) ≤ 2 ^ d * lam := by
  have h2d : (1 : ℝ) ≤ 2 ^ d := one_le_pow₀ (by norm_num)
  by_cases hε : T.child ε ∈ badTrees (fun x => |f x|) lam
  · obtain ⟨Q, hQ, hεQ⟩ := hε
    have hQm : Q.m < T.m := by
      by_contra h
      rw [not_lt] at h
      rcases DyadicCube.subset_or_disjoint T Q h with hsub | hdis
      · exact hT ⟨Q, hQ, hsub⟩
      · exact Set.disjoint_left.mp hdis (T.child_subset ε (T.child ε).corner_mem)
          (hεQ (T.child ε).corner_mem)
    have hm : Q.m = (T.child ε).m := by
      have := DyadicCube.m_le_of_subset hd hεQ
      simp only [DyadicCube.child] at this ⊢
      omega
    have hQε : Q = T.child ε := (DyadicCube.eq_of_subset_of_m_eq hεQ hm.symm).symm
    rw [← hQε]
    exact avg_abs_le_of_maxBad hf hQ
  · have hnb : T.child ε ∉ badCubes (fun x => |f x|) lam := fun hb =>
      hε (exists_maxBad_superset hd hf.abs hlam hb)
    have : avg (T.child ε) (fun x => |f x|) ≤ lam :=
      not_lt.mp fun h => hnb (lt_of_lt_of_le h (le_abs_self _))
    calc avg (T.child ε) (fun x => |f x|) ≤ lam := this
      _ ≤ 2 ^ d * lam := by nlinarith

/-- `[f]_{T_ε}² |T_ε| ≤ (2^d λ)² |T_ε|` for the children of `T ∉ 𝒢`. [PROVED] -/
theorem energy_child_le (hd : d ≠ 0) (hf : Integrable f volume) {lam : ℝ} (hlam : 0 < lam)
    {T : DyadicCube d} (hT : T ∉ badTrees (fun x => |f x|) lam) (ε : Fin d → Bool) :
    avg (T.child ε) f ^ 2 * (T.child ε).vol ≤ (2 ^ d * lam) ^ 2 * (T.child ε).vol := by
  refine mul_le_mul_of_nonneg_right ?_ (DyadicCube.vol_pos _).le
  rw [← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _)
    ((abs_avg_le_avg_abs _ f).trans (avg_abs_child_le hd hf hlam hT ε)) 2

open Classical in
/-- The stopped Bessel inequality: for `T ∉ 𝒢` and a finite family `F` of cubes of bounded
depth below `T`, `∑_{Q ∈ F, Q ⊆ T, Q ∉ 𝒢} ‖Δ_Q f‖² |Q| ≤ (2^d λ)² |T| − [f]_T² |T|`.
Induction on the depth. [PROVED] -/
theorem sum_dsq_stopped_le (hd : d ≠ 0) (hf : Integrable f volume) {lam : ℝ} (hlam : 0 < lam)
    (F : Finset (DyadicCube d)) (n : ℕ) :
    ∀ T : DyadicCube d, T ∉ badTrees (fun x => |f x|) lam →
      (∀ Q ∈ F, Q.toSet ⊆ T.toSet → T.m - (n : ℤ) ≤ Q.m) →
      ∑ Q ∈ F.filter (fun Q => Q.toSet ⊆ T.toSet ∧ Q ∉ badTrees (fun x => |f x|) lam),
          dsq Q f ≤
        (2 ^ d * lam) ^ 2 * T.vol - avg T f ^ 2 * T.vol := by
  classical
  induction n with
  | zero =>
    intro T hT hdepth
    have hsplit := sum_filter_le_add_children hd F T
      (fun Q => Q ∉ badTrees (fun x => |f x|) lam) (fun Q => dsq Q f) (fun _ => dsq_nonneg)
    have hchild : ∀ ε : Fin d → Bool,
        ∑ Q ∈ F.filter (fun Q => Q.toSet ⊆ (T.child ε).toSet ∧
          Q ∉ badTrees (fun x => |f x|) lam), dsq Q f = 0 := by
      intro ε
      refine Finset.sum_eq_zero fun Q hQ => ?_
      rw [Finset.mem_filter] at hQ
      have h1 := hdepth Q hQ.1 (hQ.2.1.trans (T.child_subset ε))
      have h2 := DyadicCube.m_le_of_subset hd hQ.2.1
      simp only [DyadicCube.child] at h2
      exfalso
      omega
    have hsum := Finset.sum_le_sum fun ε (_ : ε ∈ (Finset.univ : Finset (Fin d → Bool))) =>
      energy_child_le hd hf hlam hT ε
    rw [← Finset.mul_sum, T.sum_vol_child, sum_sq_avg_child T hf.integrableOn] at hsum
    simp only [hchild, Finset.sum_const_zero, add_zero] at hsplit
    linarith
  | succ n ih =>
    intro T hT hdepth
    have hsplit := sum_filter_le_add_children hd F T
      (fun Q => Q ∉ badTrees (fun x => |f x|) lam) (fun Q => dsq Q f) (fun _ => dsq_nonneg)
    have hchild : ∀ ε : Fin d → Bool,
        ∑ Q ∈ F.filter (fun Q => Q.toSet ⊆ (T.child ε).toSet ∧
          Q ∉ badTrees (fun x => |f x|) lam), dsq Q f ≤
          (2 ^ d * lam) ^ 2 * (T.child ε).vol - avg (T.child ε) f ^ 2 * (T.child ε).vol := by
      intro ε
      by_cases hε : T.child ε ∈ badTrees (fun x => |f x|) lam
      · have h0 : ∑ Q ∈ F.filter (fun Q => Q.toSet ⊆ (T.child ε).toSet ∧
            Q ∉ badTrees (fun x => |f x|) lam), dsq Q f = 0 := by
          refine Finset.sum_eq_zero fun Q hQ => ?_
          rw [Finset.mem_filter] at hQ
          obtain ⟨R, hR, hεR⟩ := hε
          exact absurd ⟨R, hR, hQ.2.1.trans hεR⟩ hQ.2.2
        rw [h0]
        linarith [energy_child_le hd hf hlam hT ε]
      · apply ih (T.child ε) hε
        intro Q hQ hQε
        have := hdepth Q hQ (hQε.trans (T.child_subset ε))
        simp only [DyadicCube.child]
        omega
    have hsum := Finset.sum_le_sum fun ε (_ : ε ∈ (Finset.univ : Finset (Fin d → Bool))) =>
      hchild ε
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, T.sum_vol_child,
      sum_sq_avg_child T hf.integrableOn] at hsum
    linarith

open Classical in
/-- The summands of `S_2(Δ(f) 𝟙_{𝒟∖𝒢})`. [PROVED] -/
theorem indicator_martDiff_sq_mul_vol {lam : ℝ} (Q : DyadicCube d) :
    |(badTrees (fun x => |f x|) lam)ᶜ.indicator (fun P => martDiff P f) Q| ^ 2 * Q.vol =
      if Q ∉ badTrees (fun x => |f x|) lam then dsq Q f else 0 := by
  by_cases hQ : Q ∈ badTrees (fun x => |f x|) lam
  · rw [Set.indicator_of_notMem (by simpa using hQ), ite_eq_right (not_not.mpr hQ)]
    simp
  · rw [Set.indicator_of_mem (by simpa using hQ), martDiff_sq_mul_vol, ite_eq_left hQ]

open Classical in
/-- For every finite subfamily `s ⊆ 𝒟(T)`: `∑_{Q ∈ s, Q ∉ 𝒢} ‖Δ_Q f‖² |Q| ≤ (2^d λ)² |T|`
(the sum vanishes if `T ∈ 𝒢`). [PROVED] -/
theorem sum_dsq_stopped_le_finset (hd : d ≠ 0) (hf : Integrable f volume) {lam : ℝ}
    (hlam : 0 < lam) (T : DyadicCube d) (s : Finset T.tree) :
    ∑ Q ∈ s, (if (Q : DyadicCube d) ∉ badTrees (fun x => |f x|) lam then
      dsq (Q : DyadicCube d) f else 0) ≤ (2 ^ d * lam) ^ 2 * T.vol := by
  classical
  have hC : 0 ≤ (2 ^ d * lam) ^ 2 * T.vol := mul_nonneg (sq_nonneg _) T.vol_pos.le
  by_cases hT : T ∈ badTrees (fun x => |f x|) lam
  · refine le_trans (le_of_eq (Finset.sum_eq_zero fun Q _ => ?_)) hC
    obtain ⟨R, hR, hTR⟩ := hT
    have hQ' : (Q : DyadicCube d) ∈ badTrees (fun x => |f x|) lam :=
      ⟨R, hR, (DyadicCube.mem_tree.mp Q.2).trans hTR⟩
    simp [hQ']
  · set F : Finset (DyadicCube d) := s.map (Function.Embedding.subtype _) with hF
    have hsum : ∑ Q ∈ s, (if (Q : DyadicCube d) ∉ badTrees (fun x => |f x|) lam then
          dsq (Q : DyadicCube d) f else 0) =
        ∑ Q ∈ F.filter (fun Q => Q.toSet ⊆ T.toSet ∧ Q ∉ badTrees (fun x => |f x|) lam),
          dsq Q f := by
      rw [Finset.sum_filter, hF, Finset.sum_map]
      refine Finset.sum_congr rfl fun Q _ => ?_
      have hQT : (Q : DyadicCube d).toSet ⊆ T.toSet := DyadicCube.mem_tree.mp Q.2
      simp [hQT]
    rw [hsum]
    have key := sum_dsq_stopped_le hd hf hlam F (F.sup fun Q => (T.m - Q.m).toNat) T hT (by
      intro Q hQ _
      have : (T.m - Q.m).toNat ≤ F.sup fun Q : DyadicCube d => (T.m - Q.m).toNat :=
        Finset.le_sup (f := fun Q : DyadicCube d => (T.m - Q.m).toNat) hQ
      omega)
    linarith [mul_nonneg (sq_nonneg (avg T f)) T.vol_pos.le]

open Classical in
/-- The stopped family `Q ↦ 𝟙_{Q ∉ 𝒢} ‖Δ_Q f‖² |Q|` is summable over `𝒟(T)`. [PROVED] -/
theorem summable_dsq_stopped (hd : d ≠ 0) (hf : Integrable f volume) {lam : ℝ}
    (hlam : 0 < lam) (T : DyadicCube d) :
    Summable fun Q : T.tree => (if (Q : DyadicCube d) ∉ badTrees (fun x => |f x|) lam then
      dsq (Q : DyadicCube d) f else 0) :=
  summable_of_sum_le (fun Q => by
      change (0 : ℝ) ≤ _
      split_ifs <;> first | exact dsq_nonneg | exact le_rfl)
    (sum_dsq_stopped_le_finset hd hf hlam T)

open Classical in
/-- `∑_{Q ∈ 𝒟(T) ∖ 𝒢} ‖Δ_Q f‖² |Q| ≤ (2^d λ)² |T|` (the sum vanishes if `T ∈ 𝒢`). [PROVED] -/
theorem tsum_dsq_stopped_le (hd : d ≠ 0) (hf : Integrable f volume) {lam : ℝ} (hlam : 0 < lam)
    (T : DyadicCube d) :
    ∑' Q : T.tree, (if (Q : DyadicCube d) ∉ badTrees (fun x => |f x|) lam then
      dsq (Q : DyadicCube d) f else 0) ≤ (2 ^ d * lam) ^ 2 * T.vol :=
  tsum_le_of_sum_le' (mul_nonneg (sq_nonneg _) T.vol_pos.le)
    (sum_dsq_stopped_le_finset hd hf hlam T)

/-- `S_2(Δ(f) 𝟙_{𝒟∖𝒢})(𝒟(T)) ≤ 2^d λ` for every `T`. [PROVED] -/
theorem sizeP_indicator_martDiff_le (hd : d ≠ 0) (hf : Integrable f volume) {lam : ℝ}
    (hlam : 0 < lam) (T : DyadicCube d) :
    sizeP 2 ((badTrees (fun x => |f x|) lam)ᶜ.indicator fun P => martDiff P f) T ≤
      ENNReal.ofReal (2 ^ d * lam) := by
  classical
  have hC : (0 : ℝ) ≤ 2 ^ d * lam := by positivity
  refine sizeP_two_le_ofReal _ T
    (fun Q => if (Q : DyadicCube d) ∉ badTrees (fun x => |f x|) lam then
      dsq (Q : DyadicCube d) f else 0)
    (fun Q => indicator_martDiff_sq_mul_vol _)
    (fun Q => by split_ifs <;> first | exact dsq_nonneg | exact le_rfl)
    (summable_dsq_stopped hd hf hlam T) hC ?_
  have h2 := tsum_dsq_stopped_le hd hf hlam T
  calc _ ≤ T.vol⁻¹ * ((2 ^ d * lam) ^ 2 * T.vol) :=
        mul_le_mul_of_nonneg_left h2 (inv_nonneg.mpr T.vol_pos.le)
    _ = (2 ^ d * lam) ^ 2 := by
        rw [mul_comm ((2 ^ d * lam) ^ 2), ← mul_assoc, inv_mul_cancel₀ T.vol_pos.ne', one_mul]

/-- (2.70) at `p = 1` in weak form: `μ(S_2(Δ f) > 2^d λ) ≤ ‖f‖₁/λ` (paper, p. 58). [PROVED] -/
theorem superlevel_martDiff_le (hd : d ≠ 0) (hf : Integrable f volume) {lam : ℝ}
    (hlam : 0 < lam) :
    superlevel (sizeP 2) (fun T => martDiff T f) (2 ^ d * lam) ≤
      ENNReal.ofReal ((∫ x, |f x|) / lam) := by
  refine (iInf₂_le (badTrees (fun x => |f x|) lam)
    (sizeP_indicator_martDiff_le hd hf hlam)).trans ?_
  have := outerMeasure_badTrees_le hf.abs hlam
  simpa only [abs_abs] using this

/-- (2.70) at `p = 1`: `‖Δ(f)‖_{L^{1,∞}(X,κ,S_2)} ≤ 2^d ‖f‖₁`. [PROVED] -/
theorem outerWeakL1Norm_martDiff_le (hd : d ≠ 0) (hf : Integrable f volume) :
    outerWeakLpNorm (sizeP 2) 1 (fun T => martDiff T f) ≤
      ENNReal.ofReal (2 ^ d * ∫ x, |f x|) := by
  have h2d : (0 : ℝ) < 2 ^ d := by positivity
  simp only [outerWeakLpNorm, div_one, Real.rpow_one, ENNReal.rpow_one]
  refine iSup_le fun mu => ?_
  have hmu : 0 < (mu : ℝ) := mu.2
  have hlam : 0 < (mu : ℝ) / 2 ^ d := div_pos hmu h2d
  have hmu' : (2 : ℝ) ^ d * ((mu : ℝ) / 2 ^ d) = mu := by
    rw [mul_div_assoc', mul_div_cancel_left₀ _ h2d.ne']
  have hb := superlevel_martDiff_le hd hf hlam
  rw [hmu'] at hb
  calc ENNReal.ofReal (mu : ℝ) * superlevel (sizeP 2) (fun T => martDiff T f) mu
      ≤ ENNReal.ofReal (mu : ℝ) * ENNReal.ofReal ((∫ x, |f x|) / ((mu : ℝ) / 2 ^ d)) := by
        gcongr
    _ = ENNReal.ofReal (2 ^ d * ∫ x, |f x|) := by
        rw [← ENNReal.ofReal_mul hmu.le, div_div_eq_mul_div, mul_div_assoc',
          mul_div_cancel_left₀ _ hmu.ne', mul_comm]

end CZ

/-! ### Properties of the sizes; sublinearity of `E` and `Δ` -/

section SizeProperties

/-- `S_∞` is monotone. [PROVED] -/
theorem sizeInf_mono {F G : DyadicCube d → ℝ} (h : ∀ Q, ‖F Q‖ₑ ≤ ‖G Q‖ₑ) (T : DyadicCube d) :
    sizeInf F T ≤ sizeInf G T :=
  iSup_mono fun Q => h Q

/-- `S_∞` is subadditive. [PROVED] -/
theorem sizeInf_add (F G : DyadicCube d → ℝ) (T : DyadicCube d) :
    sizeInf (F + G) T ≤ sizeInf F T + sizeInf G T :=
  iSup_le fun Q => (enorm_add_le (F Q) (G Q)).trans
    (add_le_add (le_iSup (fun Q : T.tree => ‖F Q‖ₑ) Q) (le_iSup (fun Q : T.tree => ‖G Q‖ₑ) Q))

/-- `S_p` is monotone. [PROVED] -/
theorem sizeP_mono {p : ℝ} (hp : 0 ≤ p) {F G : DyadicCube d → ℝ} (h : ∀ Q, ‖F Q‖ₑ ≤ ‖G Q‖ₑ)
    (T : DyadicCube d) : sizeP p F T ≤ sizeP p G T := by
  simp only [sizeP]
  refine ENNReal.rpow_le_rpow (mul_le_mul' le_rfl (ENNReal.tsum_le_tsum fun Q => ?_))
    (one_div_nonneg.mpr hp)
  exact mul_le_mul' (ENNReal.rpow_le_rpow (h Q) hp) le_rfl

/-- `S_2(F)(𝒟(T))` as an `L²` norm with respect to counting measure on `𝒟`, with the weights
`|Q| 𝟙_{Q ∈ 𝒟(T)}` absorbed into the function. [PROVED] -/
theorem sizeP_two_eq_lintegral (F : DyadicCube d → ℝ) (T : DyadicCube d) :
    sizeP 2 F T = (ENNReal.ofReal T.vol⁻¹ *
      ∫⁻ Q, (‖F Q‖ₑ * (T.tree.indicator (fun Q => ENNReal.ofReal Q.vol) Q) ^ (1 / 2 : ℝ)) ^ (2 : ℝ)
        ∂Measure.count) ^ (1 / 2 : ℝ) := by
  simp only [sizeP]
  congr 2
  rw [lintegral_count, tsum_subtype T.tree (fun Q => ‖F Q‖ₑ ^ (2 : ℝ) * ENNReal.ofReal Q.vol)]
  refine tsum_congr fun Q => ?_
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul,
    one_div_mul_cancel (by norm_num : (2 : ℝ) ≠ 0), ENNReal.rpow_one]
  by_cases hQ : Q ∈ T.tree
  · simp [Set.indicator_of_mem hQ]
  · simp [Set.indicator_of_notMem hQ]

/-- `S_2` is subadditive (Minkowski's inequality). [PROVED] -/
theorem sizeP_two_add (F G : DyadicCube d → ℝ) (T : DyadicCube d) :
    sizeP 2 (F + G) T ≤ sizeP 2 F T + sizeP 2 G T := by
  rw [sizeP_two_eq_lintegral, sizeP_two_eq_lintegral, sizeP_two_eq_lintegral]
  set w : DyadicCube d → ENNReal :=
    fun Q => (T.tree.indicator (fun Q => ENNReal.ofReal Q.vol) Q) ^ (1 / 2 : ℝ)
  have h1 : ∫⁻ Q, (‖(F + G) Q‖ₑ * w Q) ^ (2 : ℝ) ∂Measure.count ≤
      ∫⁻ Q, ((fun Q => ‖F Q‖ₑ * w Q) + fun Q => ‖G Q‖ₑ * w Q) Q ^ (2 : ℝ) ∂Measure.count := by
    refine lintegral_mono fun Q => ?_
    refine ENNReal.rpow_le_rpow ?_ (by norm_num)
    rw [Pi.add_apply, Pi.add_apply, ← add_mul]
    exact mul_le_mul' (enorm_add_le _ _) le_rfl
  have h2 := ENNReal.lintegral_Lp_add_le (μ := Measure.count) (p := 2)
    (f := fun Q => ‖F Q‖ₑ * w Q) (g := fun Q => ‖G Q‖ₑ * w Q)
    Measurable.of_discrete.aemeasurable Measurable.of_discrete.aemeasurable (by norm_num)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← mul_add]
  exact mul_le_mul' le_rfl ((ENNReal.rpow_le_rpow h1 (by norm_num)).trans h2)

/-- `[f + g]_Q = [f]_Q + [g]_Q` for locally integrable `f`, `g`. [PROVED] -/
theorem avg_add (Q : DyadicCube d) {f g : (Fin d → ℝ) → ℝ} (hf : IntegrableOn f Q.toSet volume)
    (hg : IntegrableOn g Q.toSet volume) : avg Q (f + g) = avg Q f + avg Q g := by
  simp only [avg, Pi.add_apply]
  rw [integral_add hf hg, add_div]

/-- `E_T` is sublinear. [PROVED] -/
theorem martAvg_add_le (T : DyadicCube d) {f g : (Fin d → ℝ) → ℝ}
    (hf : IntegrableOn f T.toSet volume) (hg : IntegrableOn g T.toSet volume) :
    martAvg T (f + g) ≤ martAvg T f + martAvg T g := by
  simp only [martAvg, avg_add T hf hg]
  exact abs_add_le _ _

theorem martAvg_nonneg (T : DyadicCube d) (f : (Fin d → ℝ) → ℝ) : 0 ≤ martAvg T f :=
  abs_nonneg _

theorem martDiff_nonneg (T : DyadicCube d) (f : (Fin d → ℝ) → ℝ) : 0 ≤ martDiff T f :=
  Real.sqrt_nonneg _

/-- Weighted finite Minkowski inequality, from the Cauchy–Schwarz inequality. [PROVED] -/
theorem sqrt_sum_sq_add_le {ι : Type*} (s : Finset ι) (a b w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) :
    Real.sqrt (∑ i ∈ s, (a i + b i) ^ 2 * w i) ≤
      Real.sqrt (∑ i ∈ s, a i ^ 2 * w i) + Real.sqrt (∑ i ∈ s, b i ^ 2 * w i) := by
  set A := Real.sqrt (∑ i ∈ s, a i ^ 2 * w i)
  set B := Real.sqrt (∑ i ∈ s, b i ^ 2 * w i)
  have hA : 0 ≤ A := Real.sqrt_nonneg _
  have hB : 0 ≤ B := Real.sqrt_nonneg _
  have hA2 : A ^ 2 = ∑ i ∈ s, a i ^ 2 * w i :=
    Real.sq_sqrt (Finset.sum_nonneg fun i _ => mul_nonneg (sq_nonneg _) (hw i))
  have hB2 : B ^ 2 = ∑ i ∈ s, b i ^ 2 * w i :=
    Real.sq_sqrt (Finset.sum_nonneg fun i _ => mul_nonneg (sq_nonneg _) (hw i))
  have hcs : (∑ i ∈ s, a i * b i * w i) ^ 2 ≤ (A * B) ^ 2 := by
    rw [mul_pow, hA2, hB2]
    have := Finset.sum_mul_sq_le_sq_mul_sq s (fun i => a i * Real.sqrt (w i))
      (fun i => b i * Real.sqrt (w i))
    have e1 : ∀ i, a i * Real.sqrt (w i) * (b i * Real.sqrt (w i)) = a i * b i * w i := fun i => by
      rw [show a i * Real.sqrt (w i) * (b i * Real.sqrt (w i)) =
        a i * b i * (Real.sqrt (w i) * Real.sqrt (w i)) by ring, Real.mul_self_sqrt (hw i)]
    have e2 : ∀ i, (a i * Real.sqrt (w i)) ^ 2 = a i ^ 2 * w i := fun i => by
      rw [mul_pow, Real.sq_sqrt (hw i)]
    have e3 : ∀ i, (b i * Real.sqrt (w i)) ^ 2 = b i ^ 2 * w i := fun i => by
      rw [mul_pow, Real.sq_sqrt (hw i)]
    simp only [e1, e2, e3] at this
    exact this
  have hab : ∑ i ∈ s, a i * b i * w i ≤ A * B := by
    have h := Real.sqrt_le_sqrt hcs
    rw [Real.sqrt_sq_eq_abs, Real.sqrt_sq (mul_nonneg hA hB)] at h
    exact (le_abs_self _).trans h
  have hexp : ∑ i ∈ s, (a i + b i) ^ 2 * w i = A ^ 2 + 2 * ∑ i ∈ s, a i * b i * w i + B ^ 2 := by
    rw [hA2, hB2, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  calc Real.sqrt (∑ i ∈ s, (a i + b i) ^ 2 * w i) ≤ Real.sqrt ((A + B) ^ 2) := by
        apply Real.sqrt_le_sqrt
        rw [hexp]
        nlinarith [hab]
    _ = A + B := Real.sqrt_sq (add_nonneg hA hB)

/-- Weighted finite Minkowski inequality with a nonnegative prefactor. [PROVED] -/
theorem sqrt_sum_sq_add_le' {ι : Type*} (c : ℝ) (hc : 0 ≤ c) (s : Finset ι) (a b w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) :
    Real.sqrt (c * ∑ i ∈ s, (a i + b i) ^ 2 * w i) ≤
      Real.sqrt (c * ∑ i ∈ s, a i ^ 2 * w i) + Real.sqrt (c * ∑ i ∈ s, b i ^ 2 * w i) := by
  rw [Real.sqrt_mul hc, Real.sqrt_mul hc, Real.sqrt_mul hc, ← mul_add]
  exact mul_le_mul_of_nonneg_left (sqrt_sum_sq_add_le s a b w hw) (Real.sqrt_nonneg c)

/-- `Δ_T` is sublinear. [PROVED] -/
theorem martDiff_add_le (T : DyadicCube d) {f g : (Fin d → ℝ) → ℝ}
    (hf : IntegrableOn f T.toSet volume) (hg : IntegrableOn g T.toSet volume) :
    martDiff T (f + g) ≤ martDiff T f + martDiff T g := by
  have hfc : ∀ ε, IntegrableOn f (T.child ε).toSet volume := fun ε => hf.mono_set (T.child_subset ε)
  have hgc : ∀ ε, IntegrableOn g (T.child ε).toSet volume := fun ε => hg.mono_set (T.child_subset ε)
  have key := sqrt_sum_sq_add_le' T.vol⁻¹ (inv_nonneg.mpr T.vol_pos.le) Finset.univ
    (fun ε => avg (T.child ε) f - avg T f) (fun ε => avg (T.child ε) g - avg T g)
    (fun ε => (T.child ε).vol) (fun ε => (DyadicCube.vol_pos _).le)
  have e : ∀ ε : Fin d → Bool, (avg (T.child ε) (f + g) - avg T (f + g)) ^ 2 * (T.child ε).vol
      = ((avg (T.child ε) f - avg T f) + (avg (T.child ε) g - avg T g)) ^ 2 * (T.child ε).vol := by
    intro ε
    rw [avg_add T hf hg, avg_add (T.child ε) (hfc ε) (hgc ε)]
    ring
  simp only [martDiff, sq_abs, e]
  exact key

/-- `[f]_Q` only depends on the a.e. class of `f`. [PROVED] -/
theorem avg_congr_ae (Q : DyadicCube d) {f g : (Fin d → ℝ) → ℝ} (h : f =ᵐ[volume] g) :
    avg Q f = avg Q g := by
  simp only [avg]
  rw [integral_congr_ae (ae_restrict_of_ae h)]

theorem martAvg_congr_ae {f g : (Fin d → ℝ) → ℝ} (h : f =ᵐ[volume] g) :
    (fun T => martAvg T f) = fun T => martAvg T g :=
  funext fun T => by simp only [martAvg, avg_congr_ae T h]

theorem martDiff_congr_ae {f g : (Fin d → ℝ) → ℝ} (h : f =ᵐ[volume] g) :
    (fun T => martDiff T f) = fun T => martDiff T g :=
  funext fun T => by simp only [martDiff, avg_congr_ae _ h]

end SizeProperties

/-! ### Marcinkiewicz interpolation for outer measure spaces (Do–Thiele [7], Prop. 3.5)

We prove the version needed here: an operator `Op` which is sublinear, of weak type `(1, 1)`
and of strong type `(∞, ∞)` with respect to a monotone subadditive size `S` is of strong type
`(p, p)` for `1 < p < ∞`. The proof is the classical one: split `f = f 𝟙_{|f| > cλ} +
f 𝟙_{|f| ≤ cλ}`, use the subadditivity of the superlevel measure, and compute the layer-cake
integral by Tonelli's theorem. -/

section Marcinkiewicz

/-- A bound by a sum of two (doubly indexed) infima in `[0, ∞]`. [PROVED] -/
theorem le_iInf₂_add_iInf₂ {ι κ : Type*} {p : ι → Prop} {q : κ → Prop} {f : ι → ENNReal}
    {g : κ → ENNReal} {a : ENNReal} (h : ∀ i, p i → ∀ k, q k → a ≤ f i + g k) :
    a ≤ (⨅ i, ⨅ (_ : p i), f i) + ⨅ k, ⨅ (_ : q k), g k := by
  rw [ENNReal.iInf_add]
  refine le_iInf fun i => ?_
  rw [ENNReal.iInf_add]
  refine le_iInf fun hi => ?_
  rw [ENNReal.add_iInf]
  refine le_iInf fun k => ?_
  rw [ENNReal.add_iInf]
  exact le_iInf fun hk => h i hi k hk

/-- The outer measure of the empty collection is `0`. [PROVED] -/
theorem outerMeasure_empty : outerMeasure (∅ : Set (DyadicCube d)) = 0 := by
  refine le_antisymm ?_ zero_le
  unfold outerMeasure
  refine iInf_le_of_le ∅ (iInf_le_of_le (Set.empty_subset _) ?_)
  simp

/-- If `S(F) ≤ λ` on every tree, then `μ(S(F) > λ) = 0`. [PROVED] -/
theorem superlevel_eq_zero {S : Size d} {F : DyadicCube d → ℝ} {lam : ℝ}
    (h : ∀ T, S F T ≤ ENNReal.ofReal lam) : superlevel S F lam = 0 := by
  unfold superlevel
  refine le_antisymm (le_trans (iInf₂_le ∅ fun T => ?_) (le_of_eq outerMeasure_empty)) zero_le
  simpa using h T

/-- Subadditivity of the outer measure. [PROVED] -/
theorem outerMeasure_union_le (A B : Set (DyadicCube d)) :
    outerMeasure (A ∪ B) ≤ outerMeasure A + outerMeasure B := by
  simp only [outerMeasure]
  refine le_iInf₂_add_iInf₂ fun C₁ h₁ C₂ h₂ => ?_
  refine (iInf₂_le (C₁ ∪ C₂) ?_).trans
    (ENNReal.tsum_union_le (fun T : DyadicCube d => ENNReal.ofReal T.vol) C₁ C₂)
  intro P hP
  rcases hP with hP | hP
  · obtain ⟨T, hT, hPT⟩ := Set.mem_iUnion₂.mp (h₁ hP)
    exact Set.mem_iUnion₂.mpr ⟨T, Or.inl hT, hPT⟩
  · obtain ⟨T, hT, hPT⟩ := Set.mem_iUnion₂.mp (h₂ hP)
    exact Set.mem_iUnion₂.mpr ⟨T, Or.inr hT, hPT⟩

/-- Subadditivity of the superlevel measure (Do–Thiele, Prop. 3.1): if `|F| ≤ |F₁| + |F₂|`
pointwise and `S` is monotone and subadditive, then
`μ(S(F) > λ₁ + λ₂) ≤ μ(S(F₁) > λ₁) + μ(S(F₂) > λ₂)`. [PROVED] -/
theorem superlevel_le_add (S : Size d)
    (hS_mono : ∀ F G : DyadicCube d → ℝ, ∀ T, (∀ Q, ‖F Q‖ₑ ≤ ‖G Q‖ₑ) → S F T ≤ S G T)
    (hS_add : ∀ F G : DyadicCube d → ℝ, ∀ T, S (F + G) T ≤ S F T + S G T)
    {F F₁ F₂ : DyadicCube d → ℝ} (hF : ∀ Q, |F Q| ≤ |F₁ Q| + |F₂ Q|) {l₁ l₂ : ℝ}
    (h1 : 0 ≤ l₁) (h2 : 0 ≤ l₂) :
    superlevel S F (l₁ + l₂) ≤ superlevel S F₁ l₁ + superlevel S F₂ l₂ := by
  simp only [superlevel]
  refine le_iInf₂_add_iInf₂ fun G₁ hG₁ G₂ hG₂ => ?_
  refine (iInf₂_le (G₁ ∪ G₂) fun T => ?_).trans (outerMeasure_union_le G₁ G₂)
  have hmono1 : S ((G₁ ∪ G₂)ᶜ.indicator fun Q => |F₁ Q|) T ≤ S (G₁ᶜ.indicator F₁) T := by
    apply hS_mono
    intro Q
    by_cases hQ : Q ∈ (G₁ ∪ G₂)ᶜ
    · have hQ1 : Q ∈ G₁ᶜ := fun h => hQ (Or.inl h)
      simp only [Set.indicator_of_mem hQ, Set.indicator_of_mem hQ1, Real.enorm_eq_ofReal_abs,
        abs_abs, le_refl]
    · rw [Set.indicator_of_notMem hQ]
      simp
  have hmono2 : S ((G₁ ∪ G₂)ᶜ.indicator fun Q => |F₂ Q|) T ≤ S (G₂ᶜ.indicator F₂) T := by
    apply hS_mono
    intro Q
    by_cases hQ : Q ∈ (G₁ ∪ G₂)ᶜ
    · have hQ2 : Q ∈ G₂ᶜ := fun h => hQ (Or.inr h)
      simp only [Set.indicator_of_mem hQ, Set.indicator_of_mem hQ2, Real.enorm_eq_ofReal_abs,
        abs_abs, le_refl]
    · rw [Set.indicator_of_notMem hQ]
      simp
  calc S ((G₁ ∪ G₂)ᶜ.indicator F) T
      ≤ S ((G₁ ∪ G₂)ᶜ.indicator (fun Q => |F₁ Q|) + (G₁ ∪ G₂)ᶜ.indicator fun Q => |F₂ Q|) T := by
        apply hS_mono
        intro Q
        rw [Pi.add_apply]
        by_cases hQ : Q ∈ (G₁ ∪ G₂)ᶜ
        · simp only [Set.indicator_of_mem hQ]
          rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs,
            abs_of_nonneg (add_nonneg (abs_nonneg (F₁ Q)) (abs_nonneg (F₂ Q)))]
          exact ENNReal.ofReal_le_ofReal (hF Q)
        · rw [Set.indicator_of_notMem hQ]
          simp
    _ ≤ S ((G₁ ∪ G₂)ᶜ.indicator fun Q => |F₁ Q|) T + S ((G₁ ∪ G₂)ᶜ.indicator fun Q => |F₂ Q|) T :=
        hS_add _ _ _
    _ ≤ S (G₁ᶜ.indicator F₁) T + S (G₂ᶜ.indicator F₂) T := add_le_add hmono1 hmono2
    _ ≤ ENNReal.ofReal l₁ + ENNReal.ofReal l₂ := add_le_add (hG₁ T) (hG₂ T)
    _ = ENNReal.ofReal (l₁ + l₂) := (ENNReal.ofReal_add h1 h2).symm

/-- The constant in the Marcinkiewicz interpolation theorem below. -/
noncomputable def marcConst (A₁ A₂ p : ℝ) : ℝ :=
  (p * (2 * A₁ * (1 / (2 * (A₂ + 1))) ^ (1 - p) / (p - 1))) ^ (1 / p)

theorem marcConst_nonneg {A₁ A₂ p : ℝ} (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂) (hp : 1 < p) :
    0 ≤ marcConst A₁ A₂ p := by
  have hp0 : 0 < p := by linarith
  have hp1 : 0 < p - 1 := by linarith
  have hc : 0 < 1 / (2 * (A₂ + 1)) := by positivity
  exact Real.rpow_nonneg (mul_nonneg hp0.le (div_nonneg
    (mul_nonneg (mul_nonneg (by norm_num) hA₁) (Real.rpow_nonneg hc.le _)) hp1.le)) _

/-- **Marcinkiewicz interpolation for outer measure spaces** (measurable `f`). An operator
`Op` from functions on `ℝ^d` to functions on `𝒟`, sublinear on `L¹ + L^∞`, of weak type
`(1,1)` with constant `A₁` and of strong type `(∞,∞)` with constant `A₂` with respect to a
monotone subadditive size `S`, satisfies `‖Op f‖_{L^p(X,κ,S)} ≤ C ‖f‖_p` for `1 < p < ∞`.
[PROVED] -/
theorem marcinkiewicz_core (S : Size d) (Op : ((Fin d → ℝ) → ℝ) → DyadicCube d → ℝ)
    (hS_mono : ∀ F G : DyadicCube d → ℝ, ∀ T, (∀ Q, ‖F Q‖ₑ ≤ ‖G Q‖ₑ) → S F T ≤ S G T)
    (hS_add : ∀ F G : DyadicCube d → ℝ, ∀ T, S (F + G) T ≤ S F T + S G T)
    (hOp : ∀ f g : (Fin d → ℝ) → ℝ, Integrable f volume → MemLp g ⊤ volume →
      ∀ Q, |Op (f + g) Q| ≤ |Op f Q| + |Op g Q|)
    {A₁ A₂ : ℝ} (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂)
    (hweak : ∀ f : (Fin d → ℝ) → ℝ, Integrable f volume → ∀ lam : ℝ, 0 < lam →
      superlevel S (Op f) lam ≤ ENNReal.ofReal (A₁ * (∫ x, ‖f x‖) / lam))
    (hstrong : ∀ f : (Fin d → ℝ) → ℝ, MemLp f ⊤ volume → ∀ T,
      S (Op f) T ≤ ENNReal.ofReal A₂ * eLpNorm f ⊤ volume)
    {p : ℝ} (hp : 1 < p) (f : (Fin d → ℝ) → ℝ) (hfm : Measurable f)
    (hf : MemLp f (ENNReal.ofReal p) volume) :
    outerLpNorm S p (Op f) ≤
      ENNReal.ofReal (marcConst A₁ A₂ p) * eLpNorm f (ENNReal.ofReal p) volume := by
  set c : ℝ := 1 / (2 * (A₂ + 1)) with hc_def
  have hc : 0 < c := by positivity
  have hA₂c : A₂ * c ≤ 1 / 2 := by
    rw [hc_def, mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hp0 : 0 < p := by linarith
  have hp1 : 0 < p - 1 := by linarith
  have hptop : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp0.le
  have hpne : ENNReal.ofReal p ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero]
    linarith
  -- Step 1: the pointwise bound on the superlevel measure
  have key : ∀ lam : ℝ, 0 < lam →
      superlevel S (Op f) lam ≤ ENNReal.ofReal (2 * A₁ / lam) *
        ∫⁻ x, {x | c * lam < ‖f x‖}.indicator (fun x => ‖f x‖ₑ) x := by
    intro lam hlam
    set s : Set (Fin d → ℝ) := {x | c * lam < ‖f x‖} with hs_def
    have hs : MeasurableSet s := measurableSet_lt measurable_const hfm.norm
    -- the small part is bounded by `c λ`
    have hsmall_bound : ∀ x, ‖sᶜ.indicator f x‖ ≤ c * lam := by
      intro x
      by_cases hx : x ∈ sᶜ
      · rw [Set.indicator_of_mem hx]
        have hx' : ¬ (c * lam < ‖f x‖) := hx
        exact not_lt.mp hx'
      · rw [Set.indicator_of_notMem hx, norm_zero]
        positivity
    have hsmall : MemLp (sᶜ.indicator f) ⊤ volume :=
      memLp_top_of_bound (hfm.indicator hs.compl).aestronglyMeasurable _
        (Filter.Eventually.of_forall hsmall_bound)
    have hsmall_size : ∀ T, S (Op (sᶜ.indicator f)) T ≤ ENNReal.ofReal (lam / 2) := by
      intro T
      refine (hstrong _ hsmall T).trans ?_
      rw [eLpNorm_exponent_top hsmall.aestronglyMeasurable]
      calc ENNReal.ofReal A₂ * eLpNormEssSup (sᶜ.indicator f) volume
          ≤ ENNReal.ofReal A₂ * ENNReal.ofReal (c * lam) := by
            gcongr
            exact eLpNormEssSup_le_of_ae_bound (Filter.Eventually.of_forall hsmall_bound)
        _ = ENNReal.ofReal (A₂ * c * lam) := by rw [← ENNReal.ofReal_mul hA₂, mul_assoc]
        _ ≤ ENNReal.ofReal (lam / 2) := ENNReal.ofReal_le_ofReal (by nlinarith)
    have hsmall_zero : superlevel S (Op (sᶜ.indicator f)) (lam / 2) = 0 :=
      superlevel_eq_zero hsmall_size
    -- the big part is integrable
    have hbig : Integrable (s.indicator f) volume := by
      have hint : Integrable (fun x => ‖f x‖ ^ p * ((c * lam) ^ (p - 1))⁻¹) volume := by
        have := hf.integrable_norm_rpow hpne ENNReal.ofReal_ne_top
        rw [hptop] at this
        exact this.mul_const _
      refine Integrable.mono' hint (hfm.indicator hs).aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => ?_)
      by_cases hx : x ∈ s
      · rw [Set.indicator_of_mem hx]
        have hx' : c * lam < ‖f x‖ := hx
        have h1 : (c * lam) ^ (p - 1) ≤ ‖f x‖ ^ (p - 1) :=
          Real.rpow_le_rpow (by positivity) hx'.le hp1.le
        have hfp : ‖f x‖ ^ p = ‖f x‖ ^ (p - 1) * ‖f x‖ := by
          rw [← Real.rpow_add_one' (norm_nonneg (f x)) (y := p - 1) (by linarith)]
          congr 1
          ring
        rw [le_mul_inv_iff₀ (by positivity), hfp, mul_comm]
        exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      · rw [Set.indicator_of_notMem hx, norm_zero]
        positivity
    -- combine the two parts
    have hsplit : Op f = Op (s.indicator f + sᶜ.indicator f) := by
      rw [Set.indicator_self_add_compl]
    have hpt : ∀ Q, |Op f Q| ≤ |Op (s.indicator f) Q| + |Op (sᶜ.indicator f) Q| := by
      intro Q
      rw [hsplit]
      exact hOp _ _ hbig hsmall Q
    calc superlevel S (Op f) lam = superlevel S (Op f) (lam / 2 + lam / 2) := by rw [add_halves]
      _ ≤ superlevel S (Op (s.indicator f)) (lam / 2) +
          superlevel S (Op (sᶜ.indicator f)) (lam / 2) :=
          superlevel_le_add S hS_mono hS_add hpt (by positivity) (by positivity)
      _ ≤ ENNReal.ofReal (A₁ * (∫ x, ‖s.indicator f x‖) / (lam / 2)) + 0 := by
          rw [hsmall_zero]
          gcongr
          exact hweak _ hbig _ (by positivity)
      _ = ENNReal.ofReal (2 * A₁ / lam) * ∫⁻ x, s.indicator (fun x => ‖f x‖ₑ) x := by
          rw [add_zero, show A₁ * (∫ x, ‖s.indicator f x‖) / (lam / 2) =
              (2 * A₁ / lam) * ∫ x, ‖s.indicator f x‖ by rw [div_div_eq_mul_div]; ring,
            ENNReal.ofReal_mul (by positivity), ofReal_integral_norm_eq_lintegral_enorm hbig]
          congr 1
          exact lintegral_congr fun x => enorm_indicator_eq_indicator_enorm f x
  -- Step 2: the layer-cake integral
  have hI : ∫⁻ lam in Set.Ioi (0 : ℝ), ENNReal.ofReal (lam ^ (p - 1)) * superlevel S (Op f) lam
      ≤ ENNReal.ofReal (2 * A₁ * c ^ (1 - p) / (p - 1)) * ∫⁻ x, ‖f x‖ₑ ^ p := by
    calc ∫⁻ lam in Set.Ioi (0 : ℝ), ENNReal.ofReal (lam ^ (p - 1)) * superlevel S (Op f) lam
        ≤ ∫⁻ lam in Set.Ioi (0 : ℝ), ∫⁻ x, ENNReal.ofReal (2 * A₁ * lam ^ (p - 2)) *
            {x | c * lam < ‖f x‖}.indicator (fun x => ‖f x‖ₑ) x := by
          refine setLIntegral_mono' measurableSet_Ioi fun lam hlam => ?_
          have hlam : 0 < lam := hlam
          calc ENNReal.ofReal (lam ^ (p - 1)) * superlevel S (Op f) lam
              ≤ ENNReal.ofReal (lam ^ (p - 1)) * (ENNReal.ofReal (2 * A₁ / lam) *
                  ∫⁻ x, {x | c * lam < ‖f x‖}.indicator (fun x => ‖f x‖ₑ) x) := by
                gcongr
                exact key lam hlam
            _ = ∫⁻ x, ENNReal.ofReal (2 * A₁ * lam ^ (p - 2)) *
                  {x | c * lam < ‖f x‖}.indicator (fun x => ‖f x‖ₑ) x := by
                rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← mul_assoc,
                  ← ENNReal.ofReal_mul (Real.rpow_nonneg hlam.le _)]
                congr 2
                rw [show p - 2 = p - 1 - 1 by ring, Real.rpow_sub_one hlam.ne' (p - 1)]
                ring
      _ = ∫⁻ x, ∫⁻ lam in Set.Ioi (0 : ℝ), ENNReal.ofReal (2 * A₁ * lam ^ (p - 2)) *
            {x | c * lam < ‖f x‖}.indicator (fun x => ‖f x‖ₑ) x := by
          apply lintegral_lintegral_swap
          refine Measurable.aemeasurable ?_
          have hset : MeasurableSet {q : ℝ × (Fin d → ℝ) | c * q.1 < ‖f q.2‖} :=
            measurableSet_lt (measurable_const.mul measurable_fst) (hfm.comp measurable_snd).norm
          have h1 : Measurable fun q : ℝ × (Fin d → ℝ) =>
              ENNReal.ofReal (2 * A₁ * q.1 ^ (p - 2)) :=
            ENNReal.measurable_ofReal.comp (measurable_const.mul (measurable_fst.pow_const (p - 2)))
          have h2 : Measurable fun q : ℝ × (Fin d → ℝ) =>
              {x | c * q.1 < ‖f x‖}.indicator (fun x => ‖f x‖ₑ) q.2 := by
            simp only [Set.indicator_apply, Set.mem_ofPred_eq]
            exact Measurable.ite hset (hfm.comp measurable_snd).enorm measurable_const
          exact h1.mul h2
      _ = ∫⁻ x, ENNReal.ofReal (2 * A₁ * c ^ (1 - p) / (p - 1)) * ‖f x‖ₑ ^ p := by
          refine lintegral_congr fun x => ?_
          set b : ℝ := ‖f x‖ / c with hb_def
          have hb : 0 ≤ b := by positivity
          have hind : ∀ lam : ℝ, {x | c * lam < ‖f x‖}.indicator (fun x => ‖f x‖ₑ) x =
              (Set.Iio b).indicator (fun _ => ‖f x‖ₑ) lam := by
            intro lam
            simp only [Set.indicator_apply, Set.mem_ofPred_eq, Set.mem_Iio, hb_def,
              lt_div_iff₀ hc, mul_comm]
          simp_rw [hind]
          have hfun : (fun lam => ENNReal.ofReal (2 * A₁ * lam ^ (p - 2)) *
              (Set.Iio b).indicator (fun _ => ‖f x‖ₑ) lam) =
              (Set.Iio b).indicator fun lam => ENNReal.ofReal (2 * A₁ * lam ^ (p - 2)) * ‖f x‖ₑ :=
                by
            funext lam
            by_cases hlam : lam ∈ Set.Iio b
            · simp [Set.indicator_of_mem hlam]
            · simp [Set.indicator_of_notMem hlam]
          rw [hfun, lintegral_indicator measurableSet_Iio, Measure.restrict_restrict
            measurableSet_Iio,
            show Set.Iio b ∩ Set.Ioi 0 = Set.Ioo 0 b by
              ext t
              simp [and_comm],
            lintegral_mul_const' _ _ enorm_ne_top]
          have hint : IntegrableOn (fun lam : ℝ => 2 * A₁ * lam ^ (p - 2)) (Set.Ioo 0 b) volume :=
            by
            have := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := b)
              (by linarith : (-1 : ℝ) < p - 2)).const_mul (2 * A₁)
            rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hb] at this
            exact this.mono_set Set.Ioo_subset_Ioc_self
          have hK1 : 0 ≤ 2 * A₁ * (b ^ (p - 2 + 1) / (p - 2 + 1)) :=
            mul_nonneg (mul_nonneg (by norm_num) hA₁)
              (div_nonneg (Real.rpow_nonneg hb _) (by linarith))
          have hK2 : 0 ≤ 2 * A₁ * c ^ (1 - p) / (p - 1) :=
            div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hA₁) (Real.rpow_nonneg hc.le _))
              hp1.le
          rw [← ofReal_integral_eq_lintegral_ofReal hint
              (ae_restrict_of_forall_mem measurableSet_Ioo fun lam hlam => by
                have : 0 < lam := hlam.1
                positivity),
            ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hb,
            intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith)),
            Real.zero_rpow (by linarith), sub_zero, ← ofReal_norm, ← ENNReal.ofReal_mul hK1,
            ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp0.le, ← ENNReal.ofReal_mul hK2]
          congr 1
          have hfp : ‖f x‖ ^ p = ‖f x‖ ^ (p - 1) * ‖f x‖ := by
            rw [← Real.rpow_add_one' (norm_nonneg (f x)) (y := p - 1) (by linarith)]
            congr 1
            ring
          rw [show p - 2 + 1 = p - 1 by ring, hb_def, Real.div_rpow (norm_nonneg _) hc.le,
            show (1 : ℝ) - p = -(p - 1) by ring, Real.rpow_neg hc.le, hfp]
          ring
      _ = ENNReal.ofReal (2 * A₁ * c ^ (1 - p) / (p - 1)) * ∫⁻ x, ‖f x‖ₑ ^ p :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  -- Step 3: conclusion
  have hE : eLpNorm f (ENNReal.ofReal p) volume ^ p = ∫⁻ x, ‖f x‖ₑ ^ p := by
    rw [eLpNorm_eq_eLpNorm' hpne ENNReal.ofReal_ne_top hf.aestronglyMeasurable,
      eLpNorm'_eq_lintegral_enorm, hptop, ← ENNReal.rpow_mul, one_div_mul_cancel hp0.ne',
      ENNReal.rpow_one]
  have hcm : marcConst A₁ A₂ p = (p * (2 * A₁ * c ^ (1 - p) / (p - 1))) ^ (1 / p) := by
    rw [marcConst, hc_def]
  calc outerLpNorm S p (Op f)
      = (ENNReal.ofReal p * ∫⁻ lam in Set.Ioi (0 : ℝ),
          ENNReal.ofReal (lam ^ (p - 1)) * superlevel S (Op f) lam) ^ (1 / p) := rfl
    _ ≤ (ENNReal.ofReal p * (ENNReal.ofReal (2 * A₁ * c ^ (1 - p) / (p - 1)) *
          ∫⁻ x, ‖f x‖ₑ ^ p)) ^ (1 / p) := by gcongr
    _ = ENNReal.ofReal (marcConst A₁ A₂ p) * eLpNorm f (ENNReal.ofReal p) volume := by
        rw [← hE, ← mul_assoc, ← ENNReal.ofReal_mul hp0.le,
          ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
          mul_one_div_cancel hp0.ne', ENNReal.rpow_one, hcm,
          ENNReal.ofReal_rpow_of_nonneg (mul_nonneg hp0.le (div_nonneg
            (mul_nonneg (mul_nonneg (by norm_num) hA₁) (Real.rpow_nonneg hc.le _)) hp1.le))
            (by positivity)]

/-- **Marcinkiewicz interpolation for outer measure spaces.** The same as
`marcinkiewicz_core` for arbitrary `f ∈ L^p`, provided `Op` only depends on the a.e. class
of `f`. [PROVED] -/
theorem marcinkiewicz (S : Size d) (Op : ((Fin d → ℝ) → ℝ) → DyadicCube d → ℝ)
    (hS_mono : ∀ F G : DyadicCube d → ℝ, ∀ T, (∀ Q, ‖F Q‖ₑ ≤ ‖G Q‖ₑ) → S F T ≤ S G T)
    (hS_add : ∀ F G : DyadicCube d → ℝ, ∀ T, S (F + G) T ≤ S F T + S G T)
    (hOp : ∀ f g : (Fin d → ℝ) → ℝ, Integrable f volume → MemLp g ⊤ volume →
      ∀ Q, |Op (f + g) Q| ≤ |Op f Q| + |Op g Q|)
    (hOp_congr : ∀ f g : (Fin d → ℝ) → ℝ, f =ᵐ[volume] g → Op f = Op g)
    {A₁ A₂ : ℝ} (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂)
    (hweak : ∀ f : (Fin d → ℝ) → ℝ, Integrable f volume → ∀ lam : ℝ, 0 < lam →
      superlevel S (Op f) lam ≤ ENNReal.ofReal (A₁ * (∫ x, ‖f x‖) / lam))
    (hstrong : ∀ f : (Fin d → ℝ) → ℝ, MemLp f ⊤ volume → ∀ T,
      S (Op f) T ≤ ENNReal.ofReal A₂ * eLpNorm f ⊤ volume)
    {p : ℝ} (hp : 1 < p) (f : (Fin d → ℝ) → ℝ) (hf : MemLp f (ENNReal.ofReal p) volume) :
    outerLpNorm S p (Op f) ≤
      ENNReal.ofReal (marcConst A₁ A₂ p) * eLpNorm f (ENNReal.ofReal p) volume := by
  have hae := hf.aestronglyMeasurable.aemeasurable
  have hfg : f =ᵐ[volume] hae.mk f := hae.ae_eq_mk
  rw [hOp_congr f _ hfg, eLpNorm_congr_ae hfg]
  exact marcinkiewicz_core S Op hS_mono hS_add hOp hA₁ hA₂ hweak hstrong hp _ hae.measurable_mk
    (hf.ae_eq hfg)

end Marcinkiewicz

/-! ### Hölder's inequality for outer measure spaces (Do–Thiele [7], Prop. 3.4)

These are the tools behind Lemmas 2.71 and 2.72. -/

section OuterHolder

/-- The superlevel measure is antitone in `λ`. [PROVED] -/
theorem superlevel_anti (S : Size d) (F : DyadicCube d → ℝ) {l₁ l₂ : ℝ} (h : l₁ ≤ l₂) :
    superlevel S F l₂ ≤ superlevel S F l₁ :=
  le_iInf₂ fun G hG => iInf₂_le G fun T => (hG T).trans (ENNReal.ofReal_le_ofReal h)

/-- Restricting to a larger exceptional collection decreases a monotone size. [PROVED] -/
theorem size_indicator_mono (S : Size d)
    (hS : ∀ F G : DyadicCube d → ℝ, ∀ T, (∀ Q, ‖F Q‖ₑ ≤ ‖G Q‖ₑ) → S F T ≤ S G T)
    {G G' : Set (DyadicCube d)} (h : G ⊆ G') (F : DyadicCube d → ℝ) (T : DyadicCube d) :
    S (G'ᶜ.indicator F) T ≤ S (Gᶜ.indicator F) T := by
  apply hS
  intro Q
  by_cases hQ : Q ∈ G'ᶜ
  · have hQ' : Q ∈ Gᶜ := fun hG => hQ (h hG)
    rw [Set.indicator_of_mem hQ, Set.indicator_of_mem hQ']
  · rw [Set.indicator_of_notMem hQ]
    simp

/-- The product rule for superlevel measures: if `S(FG) ≤ S₁(F) S₂(G)` on every tree, then
`μ(S(FG) > λ₁λ₂) ≤ μ(S₁(F) > λ₁) + μ(S₂(G) > λ₂)`. [PROVED] -/
theorem superlevel_mul_le (S S₁ S₂ : Size d)
    (hS₁ : ∀ F G : DyadicCube d → ℝ, ∀ T, (∀ Q, ‖F Q‖ₑ ≤ ‖G Q‖ₑ) → S₁ F T ≤ S₁ G T)
    (hS₂ : ∀ F G : DyadicCube d → ℝ, ∀ T, (∀ Q, ‖F Q‖ₑ ≤ ‖G Q‖ₑ) → S₂ F T ≤ S₂ G T)
    (hprod : ∀ F G : DyadicCube d → ℝ, ∀ T, S (F * G) T ≤ S₁ F T * S₂ G T)
    (F G : DyadicCube d → ℝ) {l₁ l₂ : ℝ} (h1 : 0 ≤ l₁) :
    superlevel S (F * G) (l₁ * l₂) ≤ superlevel S₁ F l₁ + superlevel S₂ G l₂ := by
  simp only [superlevel]
  refine le_iInf₂_add_iInf₂ fun G₁ hG₁ G₂ hG₂ => ?_
  refine (iInf₂_le (G₁ ∪ G₂) fun T => ?_).trans (outerMeasure_union_le G₁ G₂)
  have e : (G₁ ∪ G₂)ᶜ.indicator (F * G) = (G₁ ∪ G₂)ᶜ.indicator F * (G₁ ∪ G₂)ᶜ.indicator G := by
    funext Q
    exact congrFun (Set.indicator_mul (G₁ ∪ G₂)ᶜ F G) Q
  calc S ((G₁ ∪ G₂)ᶜ.indicator (F * G)) T
      ≤ S₁ ((G₁ ∪ G₂)ᶜ.indicator F) T * S₂ ((G₁ ∪ G₂)ᶜ.indicator G) T := by
        rw [e]
        exact hprod _ _ T
    _ ≤ S₁ (G₁ᶜ.indicator F) T * S₂ (G₂ᶜ.indicator G) T :=
        mul_le_mul' (size_indicator_mono S₁ hS₁ Set.subset_union_left F T)
          (size_indicator_mono S₂ hS₂ Set.subset_union_right G T)
    _ ≤ ENNReal.ofReal l₁ * ENNReal.ofReal l₂ := mul_le_mul' (hG₁ T) (hG₂ T)
    _ = ENNReal.ofReal (l₁ * l₂) := (ENNReal.ofReal_mul h1).symm

/-- Scaling substitution in the layer-cake integral: `∫₀^∞ g(λ/m) dλ = m ∫₀^∞ g(u) du`.
[PROVED] -/
theorem lintegral_Ioi_comp_div {m : ℝ} (hm : 0 < m) (g : ℝ → ENNReal) :
    ∫⁻ lam in Set.Ioi (0 : ℝ), g (lam / m) =
      ENNReal.ofReal m * ∫⁻ u in Set.Ioi (0 : ℝ), g u := by
  have himg : (fun u : ℝ => m * u) '' Set.Ioi 0 = Set.Ioi 0 := by
    rw [Set.image_mul_left_Ioi hm, mul_zero]
  have hderiv : ∀ u ∈ Set.Ioi (0 : ℝ),
      HasDerivWithinAt (fun u : ℝ => m * u) m (Set.Ioi 0) u := by
    intro u _
    have := ((hasDerivAt_id u).const_mul m).hasDerivWithinAt (s := Set.Ioi 0)
    simpa using this
  have hinj : Set.InjOn (fun u : ℝ => m * u) (Set.Ioi 0) :=
    fun a _ b _ h => mul_left_cancel₀ hm.ne' h
  calc ∫⁻ lam in Set.Ioi (0 : ℝ), g (lam / m)
      = ∫⁻ lam in (fun u : ℝ => m * u) '' Set.Ioi 0, g (lam / m) := by rw [himg]
    _ = ∫⁻ u in Set.Ioi (0 : ℝ), ENNReal.ofReal |m| * g (m * u / m) :=
        lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi hderiv hinj _
    _ = ENNReal.ofReal m * ∫⁻ u in Set.Ioi (0 : ℝ), g u := by
        rw [abs_of_pos hm, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        congr 1
        exact lintegral_congr fun u => by rw [mul_div_cancel_left₀ _ hm.ne']

/-- Power substitution in the layer-cake integral:
`∫₀^∞ g(t λ^{1/p}) dλ = p t^{-p} ∫₀^∞ u^{p-1} g(u) du`. [PROVED] -/
theorem lintegral_Ioi_comp_rpow {p t : ℝ} (hp : 0 < p) (ht : 0 < t) (g : ℝ → ENNReal) :
    ∫⁻ lam in Set.Ioi (0 : ℝ), g (t * lam ^ (1 / p)) =
      ENNReal.ofReal (p * t ^ (-p)) *
        ∫⁻ u in Set.Ioi (0 : ℝ), ENNReal.ofReal (u ^ (p - 1)) * g u := by
  set φ : ℝ → ℝ := fun u => (u / t) ^ p with hφ
  have himg : φ '' Set.Ioi 0 = Set.Ioi 0 := by
    ext lam
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact Real.rpow_pos_of_pos (div_pos hu ht) p
    · intro hlam
      have hlam : 0 < lam := hlam
      refine ⟨t * lam ^ (1 / p), Set.mem_Ioi.mpr (by positivity), ?_⟩
      simp only [hφ]
      rw [mul_div_cancel_left₀ _ ht.ne', ← Real.rpow_mul hlam.le, one_div_mul_cancel hp.ne',
        Real.rpow_one]
  have hderiv : ∀ u ∈ Set.Ioi (0 : ℝ),
      HasDerivWithinAt φ (p * (u / t) ^ (p - 1) / t) (Set.Ioi 0) u := by
    intro u hu
    have hu : 0 < u := hu
    have h := ((hasDerivAt_id u).div_const t).rpow_const (p := p) (Or.inl (div_pos hu ht).ne')
    exact (h.hasDerivWithinAt (s := Set.Ioi 0)).congr_deriv (by simp only [id_eq]; ring)
  have hinj : Set.InjOn φ (Set.Ioi 0) := by
    intro a ha b hb h
    have ha : 0 < a := ha
    have hb : 0 < b := hb
    have h' : (a / t) ^ p = (b / t) ^ p := h
    have : ((a / t) ^ p) ^ (1 / p) = ((b / t) ^ p) ^ (1 / p) := by rw [h']
    rw [← Real.rpow_mul (div_pos ha ht).le, ← Real.rpow_mul (div_pos hb ht).le,
      mul_one_div_cancel hp.ne', Real.rpow_one, Real.rpow_one] at this
    exact (div_left_inj' ht.ne').mp this
  calc ∫⁻ lam in Set.Ioi (0 : ℝ), g (t * lam ^ (1 / p))
      = ∫⁻ lam in φ '' Set.Ioi 0, g (t * lam ^ (1 / p)) := by rw [himg]
    _ = ∫⁻ u in Set.Ioi (0 : ℝ),
          ENNReal.ofReal |p * (u / t) ^ (p - 1) / t| * g (t * (φ u) ^ (1 / p)) :=
        lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi hderiv hinj _
    _ = ∫⁻ u in Set.Ioi (0 : ℝ),
          ENNReal.ofReal (p * t ^ (-p)) * (ENNReal.ofReal (u ^ (p - 1)) * g u) := by
        refine lintegral_congr_ae (ae_restrict_of_forall_mem measurableSet_Ioi fun u hu => ?_)
        have hu : 0 < u := hu
        have e1 : t * (φ u) ^ (1 / p) = u := by
          simp only [hφ]
          rw [← Real.rpow_mul (div_pos hu ht).le, mul_one_div_cancel hp.ne', Real.rpow_one,
            mul_div_assoc', mul_div_cancel_left₀ _ ht.ne']
        have e2 : |p * (u / t) ^ (p - 1) / t| = p * t ^ (-p) * u ^ (p - 1) := by
          rw [abs_of_nonneg (by positivity), Real.div_rpow hu.le ht.le, Real.rpow_neg ht.le,
            Real.rpow_sub_one ht.ne']
          field_simp
        dsimp only
        rw [e1, e2, ENNReal.ofReal_mul (by positivity), mul_assoc]
    _ = ENNReal.ofReal (p * t ^ (-p)) *
          ∫⁻ u in Set.Ioi (0 : ℝ), ENNReal.ofReal (u ^ (p - 1)) * g u :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- Hölder's inequality for outer measure spaces with one `L^∞` factor: if
`S(FG) ≤ S₁(F) S₂(G)` on every tree, then `‖FG‖_{L^q(S)} ≤ ‖F‖_{L^q(S₁)} ‖G‖_{L^∞(S₂)}`
(for `0 < q` and `‖G‖_{L^∞(S₂)} < ∞`). [PROVED] -/
theorem outerLpNorm_mul_le_Linf (S S₁ S₂ : Size d)
    (hS₁ : ∀ F G : DyadicCube d → ℝ, ∀ T, (∀ Q, ‖F Q‖ₑ ≤ ‖G Q‖ₑ) → S₁ F T ≤ S₁ G T)
    (hS₂ : ∀ F G : DyadicCube d → ℝ, ∀ T, (∀ Q, ‖F Q‖ₑ ≤ ‖G Q‖ₑ) → S₂ F T ≤ S₂ G T)
    (hprod : ∀ F G : DyadicCube d → ℝ, ∀ T, S (F * G) T ≤ S₁ F T * S₂ G T)
    {q : ℝ} (hq : 0 < q) (F G : DyadicCube d → ℝ) (hG : outerLinfNorm S₂ G ≠ ⊤) :
    outerLpNorm S q (F * G) ≤ outerLpNorm S₁ q F * outerLinfNorm S₂ G := by
  set m : ℝ := (outerLinfNorm S₂ G).toReal with hm_def
  have hm0 : 0 ≤ m := ENNReal.toReal_nonneg
  have hM : outerLinfNorm S₂ G = ENNReal.ofReal m := (ENNReal.ofReal_toReal hG).symm
  have hGT : ∀ T, S₂ G T ≤ ENNReal.ofReal m := fun T => hM ▸ le_iSup (fun T => S₂ G T) T
  rcases hm0.lt_or_eq with hm | hm
  · -- `m > 0`: scale
    have hsl : ∀ lam : ℝ, 0 < lam → superlevel S (F * G) lam ≤ superlevel S₁ F (lam / m) := by
      intro lam hlam
      have h := superlevel_mul_le S S₁ S₂ hS₁ hS₂ hprod F G (l₁ := lam / m) (l₂ := m)
        (by positivity)
      rwa [div_mul_cancel₀ _ hm.ne', superlevel_eq_zero hGT, add_zero] at h
    simp only [outerLpNorm]
    rw [hM]
    have hint : ∫⁻ lam in Set.Ioi (0 : ℝ), ENNReal.ofReal (lam ^ (q - 1)) * superlevel S (F * G) lam
        ≤ ENNReal.ofReal (m ^ q) *
          ∫⁻ u in Set.Ioi (0 : ℝ), ENNReal.ofReal (u ^ (q - 1)) * superlevel S₁ F u := by
      calc ∫⁻ lam in Set.Ioi (0 : ℝ), ENNReal.ofReal (lam ^ (q - 1)) * superlevel S (F * G) lam
          ≤ ∫⁻ lam in Set.Ioi (0 : ℝ),
              ENNReal.ofReal (lam ^ (q - 1)) * superlevel S₁ F (lam / m) := by
            refine setLIntegral_mono' measurableSet_Ioi fun lam hlam => ?_
            gcongr
            exact hsl lam hlam
        _ = ∫⁻ lam in Set.Ioi (0 : ℝ), (fun u => ENNReal.ofReal (m ^ (q - 1)) *
              (ENNReal.ofReal (u ^ (q - 1)) * superlevel S₁ F u)) (lam / m) := by
            refine lintegral_congr_ae (ae_restrict_of_forall_mem measurableSet_Ioi
              fun lam hlam => ?_)
            have hlam : 0 < lam := hlam
            simp only
            rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg hm.le _),
              ← Real.mul_rpow hm.le (div_nonneg hlam.le hm.le), mul_div_assoc',
              mul_div_cancel_left₀ _ hm.ne']
        _ = ENNReal.ofReal m * ∫⁻ u in Set.Ioi (0 : ℝ), ENNReal.ofReal (m ^ (q - 1)) *
              (ENNReal.ofReal (u ^ (q - 1)) * superlevel S₁ F u) :=
            lintegral_Ioi_comp_div hm (fun u => ENNReal.ofReal (m ^ (q - 1)) *
              (ENNReal.ofReal (u ^ (q - 1)) * superlevel S₁ F u))
        _ = ENNReal.ofReal (m ^ q) *
              ∫⁻ u in Set.Ioi (0 : ℝ), ENNReal.ofReal (u ^ (q - 1)) * superlevel S₁ F u := by
            rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← mul_assoc,
              ← ENNReal.ofReal_mul hm.le]
            congr 2
            rw [mul_comm, ← Real.rpow_add_one' hm.le (by linarith)]
            congr 1
            ring
    calc (ENNReal.ofReal q *
            ∫⁻ lam in Set.Ioi (0 : ℝ), ENNReal.ofReal (lam ^ (q - 1)) * superlevel S (F * G) lam)
            ^ (1 / q)
        ≤ (ENNReal.ofReal q * (ENNReal.ofReal (m ^ q) *
            ∫⁻ u in Set.Ioi (0 : ℝ), ENNReal.ofReal (u ^ (q - 1)) * superlevel S₁ F u)) ^ (1 / q) :=
              by
          gcongr
      _ = (ENNReal.ofReal q *
            ∫⁻ u in Set.Ioi (0 : ℝ), ENNReal.ofReal (u ^ (q - 1)) * superlevel S₁ F u) ^ (1 / q) *
            ENNReal.ofReal m := by
          rw [mul_left_comm, ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
            ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity), ← Real.rpow_mul hm.le,
            mul_one_div_cancel hq.ne', Real.rpow_one, mul_comm]
  · -- `m = 0`: the product has size zero
    have h0 : ∀ T, S (F * G) T = 0 := by
      intro T
      have := hGT T
      rw [← hm, ENNReal.ofReal_zero, nonpos_iff_eq_zero] at this
      exact le_antisymm ((hprod F G T).trans (by rw [this, mul_zero])) zero_le
    have hz : ∀ lam : ℝ, 0 < lam → superlevel S (F * G) lam = 0 := fun lam _ =>
      superlevel_eq_zero fun T => by
        rw [h0 T]
        exact zero_le
    have : ∫⁻ lam in Set.Ioi (0 : ℝ), ENNReal.ofReal (lam ^ (q - 1)) * superlevel S (F * G) lam
        = 0 := by
      rw [lintegral_congr_ae (ae_restrict_of_forall_mem measurableSet_Ioi
        fun lam hlam => by rw [hz lam hlam, mul_zero])]
      simp
    simp only [outerLpNorm]
    rw [this, mul_zero, ENNReal.zero_rpow_of_pos (by positivity)]
    exact zero_le

/-- A quantity bounded by `s · B` for every `s > 0`, with `B < ∞`, vanishes. [PROVED] -/
theorem eq_zero_of_forall_le_ofReal_mul {N B : ENNReal} (hB : B ≠ ⊤)
    (h : ∀ s : ℝ, 0 < s → N ≤ ENNReal.ofReal s * B) : N = 0 := by
  refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_) zero_le
  rw [zero_add]
  have hε' : (0 : ℝ) < ε := hε
  have hB0 : 0 ≤ B.toReal := ENNReal.toReal_nonneg
  have hs : 0 < (ε : ℝ) / (B.toReal + 1) := div_pos hε' (by positivity)
  refine (h _ hs).trans ?_
  have hB' : ENNReal.ofReal ((ε : ℝ) / (B.toReal + 1)) * B =
      ENNReal.ofReal ((ε : ℝ) / (B.toReal + 1) * B.toReal) := by
    rw [ENNReal.ofReal_mul hs.le, ENNReal.ofReal_toReal hB]
  rw [hB', ← ENNReal.ofReal_coe_nnreal]
  apply ENNReal.ofReal_le_ofReal
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  nlinarith

/-- The balancing parameter in the proof of Hölder's inequality. [PROVED] -/
theorem exists_holder_balance {p p' α β : ℝ} (hp : 0 < p) (hp' : 0 < p')
    (hpp' : 1 / p + 1 / p' = 1) (hα : 0 < α) (hβ : 0 < β) :
    ∃ t : ℝ, 0 < t ∧ t ^ (-p) * α ^ p = α * β ∧ t ^ p' * β ^ p' = α * β := by
  have hq : 1 / p' = 1 - 1 / p := by linarith
  have hq' : 1 / p = 1 - 1 / p' := by linarith
  have e3 : p / p' = p - 1 := by
    rw [div_eq_mul_one_div, hq, mul_sub, mul_one, mul_one_div_cancel hp.ne']
  have e4 : p' / p = p' - 1 := by
    rw [div_eq_mul_one_div, hq', mul_sub, mul_one, mul_one_div_cancel hp'.ne']
  refine ⟨α ^ (1 / p') * β ^ (-(1 / p)), by positivity, ?_, ?_⟩
  · have e1 : (1 / p') * -p = -(p / p') := by ring
    have e2 : -(1 / p) * -p = 1 := by field_simp
    rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hα.le,
      ← Real.rpow_mul hβ.le, e1, e2, Real.rpow_one, mul_right_comm, ← Real.rpow_add hα, e3,
      show -(p - 1) + p = 1 by ring, Real.rpow_one]
  · have e1 : (1 / p') * p' = 1 := by field_simp
    have e2 : -(1 / p) * p' = -(p' / p) := by ring
    rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hα.le,
      ← Real.rpow_mul hβ.le, e1, e2, Real.rpow_one, mul_assoc, ← Real.rpow_add hβ, e4,
      show -(p' - 1) + p' = 1 by ring, Real.rpow_one]

/-- Hölder's inequality for outer measure spaces with target exponent `1`: if
`S(FG) ≤ S₁(F) S₂(G)` on every tree and `1/p + 1/p' = 1`, then
`‖FG‖_{L¹(S)} ≤ 2 ‖F‖_{L^p(S₁)} ‖G‖_{L^{p'}(S₂)}` (for finite right-hand side). [PROVED] -/
theorem outerL1Norm_mul_le (S S₁ S₂ : Size d)
    (hS₁ : ∀ F G : DyadicCube d → ℝ, ∀ T, (∀ Q, ‖F Q‖ₑ ≤ ‖G Q‖ₑ) → S₁ F T ≤ S₁ G T)
    (hS₂ : ∀ F G : DyadicCube d → ℝ, ∀ T, (∀ Q, ‖F Q‖ₑ ≤ ‖G Q‖ₑ) → S₂ F T ≤ S₂ G T)
    (hprod : ∀ F G : DyadicCube d → ℝ, ∀ T, S (F * G) T ≤ S₁ F T * S₂ G T)
    {p p' : ℝ} (hp : 1 < p) (hp' : 1 < p') (hpp' : 1 / p + 1 / p' = 1)
    (F G : DyadicCube d → ℝ) (hF : outerLpNorm S₁ p F ≠ ⊤) (hG : outerLpNorm S₂ p' G ≠ ⊤) :
    outerLpNorm S 1 (F * G) ≤ 2 * (outerLpNorm S₁ p F * outerLpNorm S₂ p' G) := by
  have hp0 : 0 < p := by linarith
  have hp'0 : 0 < p' := by linarith
  have hN : outerLpNorm S 1 (F * G) = ∫⁻ lam in Set.Ioi (0 : ℝ), superlevel S (F * G) lam := by
    simp [outerLpNorm]
  have hA : outerLpNorm S₁ p F ^ p = ENNReal.ofReal p *
      ∫⁻ u in Set.Ioi (0 : ℝ), ENNReal.ofReal (u ^ (p - 1)) * superlevel S₁ F u := by
    simp only [outerLpNorm]
    rw [one_div, ENNReal.rpow_inv_rpow hp0.ne']
  have hB : outerLpNorm S₂ p' G ^ p' = ENNReal.ofReal p' *
      ∫⁻ u in Set.Ioi (0 : ℝ), ENNReal.ofReal (u ^ (p' - 1)) * superlevel S₂ G u := by
    simp only [outerLpNorm]
    rw [one_div, ENNReal.rpow_inv_rpow hp'0.ne']
  have hanti : Antitone (superlevel S₁ F) := fun _ _ h => superlevel_anti S₁ F h
  have hmF : Measurable (superlevel S₁ F) := hanti.measurable
  -- the bound for every `t > 0`
  have key : ∀ t : ℝ, 0 < t → outerLpNorm S 1 (F * G) ≤
      ENNReal.ofReal (t ^ (-p)) * outerLpNorm S₁ p F ^ p +
        ENNReal.ofReal (t ^ p') * outerLpNorm S₂ p' G ^ p' := by
    intro t ht
    rw [hN, hA, hB]
    calc ∫⁻ lam in Set.Ioi (0 : ℝ), superlevel S (F * G) lam
        ≤ ∫⁻ lam in Set.Ioi (0 : ℝ), (superlevel S₁ F (t * lam ^ (1 / p)) +
            superlevel S₂ G (t⁻¹ * lam ^ (1 / p'))) := by
          refine setLIntegral_mono' measurableSet_Ioi fun lam hlam => ?_
          have hlam : 0 < lam := hlam
          have e : lam = (t * lam ^ (1 / p)) * (t⁻¹ * lam ^ (1 / p')) := by
            rw [mul_mul_mul_comm, mul_inv_cancel₀ ht.ne', one_mul, ← Real.rpow_add hlam, hpp',
              Real.rpow_one]
          conv_lhs => rw [e]
          exact superlevel_mul_le S S₁ S₂ hS₁ hS₂ hprod F G (by positivity)
      _ = (∫⁻ lam in Set.Ioi (0 : ℝ), superlevel S₁ F (t * lam ^ (1 / p))) +
            ∫⁻ lam in Set.Ioi (0 : ℝ), superlevel S₂ G (t⁻¹ * lam ^ (1 / p')) :=
          lintegral_add_left (hmF.comp (measurable_const.mul (measurable_id.pow_const _))) _
      _ = ENNReal.ofReal (p * t ^ (-p)) *
            (∫⁻ u in Set.Ioi (0 : ℝ), ENNReal.ofReal (u ^ (p - 1)) * superlevel S₁ F u) +
          ENNReal.ofReal (p' * t⁻¹ ^ (-p')) *
            ∫⁻ u in Set.Ioi (0 : ℝ), ENNReal.ofReal (u ^ (p' - 1)) * superlevel S₂ G u := by
          rw [lintegral_Ioi_comp_rpow hp0 ht, lintegral_Ioi_comp_rpow hp'0 (inv_pos.mpr ht)]
      _ = _ := by
          rw [Real.rpow_neg (inv_nonneg.mpr ht.le), Real.inv_rpow ht.le, inv_inv,
            ENNReal.ofReal_mul hp0.le, ENNReal.ofReal_mul hp'0.le]
          ring
  -- optimisation over `t`
  by_cases ha0 : outerLpNorm S₁ p F = 0
  · have : outerLpNorm S 1 (F * G) = 0 := by
      apply eq_zero_of_forall_le_ofReal_mul (B := outerLpNorm S₂ p' G ^ p')
        (ENNReal.rpow_ne_top_of_nonneg hp'0.le hG)
      intro s hs
      have := key (s ^ (1 / p')) (by positivity)
      rwa [ha0, ENNReal.zero_rpow_of_pos hp0, mul_zero, zero_add, ← Real.rpow_mul hs.le,
        one_div_mul_cancel hp'0.ne', Real.rpow_one] at this
    rw [this]
    exact zero_le
  by_cases hb0 : outerLpNorm S₂ p' G = 0
  · have : outerLpNorm S 1 (F * G) = 0 := by
      apply eq_zero_of_forall_le_ofReal_mul (B := outerLpNorm S₁ p F ^ p)
        (ENNReal.rpow_ne_top_of_nonneg hp0.le hF)
      intro s hs
      have := key (s ^ (-(1 / p))) (by positivity)
      rwa [hb0, ENNReal.zero_rpow_of_pos hp'0, mul_zero, add_zero, ← Real.rpow_mul hs.le,
        show -(1 / p) * -p = 1 by field_simp, Real.rpow_one] at this
    rw [this]
    exact zero_le
  have hα : 0 < (outerLpNorm S₁ p F).toReal := ENNReal.toReal_pos ha0 hF
  have hβ : 0 < (outerLpNorm S₂ p' G).toReal := ENNReal.toReal_pos hb0 hG
  obtain ⟨t, ht, h1, h2⟩ := exists_holder_balance hp0 hp'0 hpp' hα hβ
  have ea : outerLpNorm S₁ p F ^ p = ENNReal.ofReal ((outerLpNorm S₁ p F).toReal ^ p) := by
    rw [← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hp0.le, ENNReal.ofReal_toReal hF]
  have eb : outerLpNorm S₂ p' G ^ p' = ENNReal.ofReal ((outerLpNorm S₂ p' G).toReal ^ p') := by
    rw [← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hp'0.le, ENNReal.ofReal_toReal hG]
  have := key t ht
  rw [ea, eb, ← ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _),
    ← ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _), h1, h2, ← two_mul,
    ENNReal.ofReal_mul hα.le, ENNReal.ofReal_toReal hF, ENNReal.ofReal_toReal hG] at this
  exact this

/-- The balancing parameter in the proof of Hölder's inequality with target exponent `s`,
`1/p + 1/q = 1/s`: `t = α^{s/q} β^{-s/p}` gives `t^{-p} α^p = t^q β^q = (αβ)^s`. [PROVED] -/
theorem exists_holder_balance' {p q s α β : ℝ} (hp : 0 < p) (hq : 0 < q) (hs : 0 < s)
    (hpq : 1 / p + 1 / q = 1 / s) (hα : 0 < α) (hβ : 0 < β) :
    ∃ t : ℝ, 0 < t ∧ t ^ (-p) * α ^ p = (α * β) ^ s ∧ t ^ q * β ^ q = (α * β) ^ s := by
  have key : p * q = s * (p + q) := by
    have h := hpq
    rw [div_add_div _ _ hp.ne' hq.ne', div_eq_div_iff (by positivity) hs.ne'] at h
    linear_combination -h
  refine ⟨α ^ (s / q) * β ^ (-(s / p)), by positivity, ?_, ?_⟩
  · have e1 : s / q * -p = -(p * s / q) := by ring
    have e2 : -(s / p) * -p = s := by field_simp
    have e3 : -(p * s / q) + p = s := by
      field_simp
      linear_combination key
    rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hα.le,
      ← Real.rpow_mul hβ.le, e1, e2, mul_right_comm, ← Real.rpow_add hα, e3,
      Real.mul_rpow hα.le hβ.le]
  · have e1 : s / q * q = s := by field_simp
    have e2 : -(s / p) * q = -(q * s / p) := by ring
    have e3 : -(q * s / p) + q = s := by
      field_simp
      linear_combination key
    rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hα.le,
      ← Real.rpow_mul hβ.le, e1, e2, mul_assoc, ← Real.rpow_add hβ, e3,
      Real.mul_rpow hα.le hβ.le]

/-- Hölder's inequality for outer measure spaces with general target exponent: if
`S(FG) ≤ S₁(F) S₂(G)` on every tree and `1/p + 1/q = 1/s`, then
`‖FG‖_{L^s(S)} ≤ 2^{1/s} ‖F‖_{L^p(S₁)} ‖G‖_{L^q(S₂)}` (for finite right-hand side). The proof
is the layer-cake argument of `outerL1Norm_mul_le` after the substitution `λ ↦ λ^{1/s}`.
[PROVED] -/
theorem outerLpNorm_mul_le (S S₁ S₂ : Size d)
    (hS₁ : ∀ F G : DyadicCube d → ℝ, ∀ T, (∀ Q, ‖F Q‖ₑ ≤ ‖G Q‖ₑ) → S₁ F T ≤ S₁ G T)
    (hS₂ : ∀ F G : DyadicCube d → ℝ, ∀ T, (∀ Q, ‖F Q‖ₑ ≤ ‖G Q‖ₑ) → S₂ F T ≤ S₂ G T)
    (hprod : ∀ F G : DyadicCube d → ℝ, ∀ T, S (F * G) T ≤ S₁ F T * S₂ G T)
    {p q s : ℝ} (hp : 0 < p) (hq : 0 < q) (hs : 0 < s) (hpq : 1 / p + 1 / q = 1 / s)
    (F G : DyadicCube d → ℝ) (hF : outerLpNorm S₁ p F ≠ ⊤) (hG : outerLpNorm S₂ q G ≠ ⊤) :
    outerLpNorm S s (F * G) ≤
      (2 : ENNReal) ^ (1 / s) * (outerLpNorm S₁ p F * outerLpNorm S₂ q G) := by
  suffices h : outerLpNorm S s (F * G) ^ s ≤
      2 * (outerLpNorm S₁ p F * outerLpNorm S₂ q G) ^ s by
    calc outerLpNorm S s (F * G) = (outerLpNorm S s (F * G) ^ s) ^ (1 / s) := by
          rw [← ENNReal.rpow_mul, mul_one_div_cancel hs.ne', ENNReal.rpow_one]
      _ ≤ (2 * (outerLpNorm S₁ p F * outerLpNorm S₂ q G) ^ s) ^ (1 / s) :=
          ENNReal.rpow_le_rpow h (by positivity)
      _ = _ := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
            mul_one_div_cancel hs.ne', ENNReal.rpow_one]
  have hN : outerLpNorm S s (F * G) ^ s =
      ∫⁻ lam in Set.Ioi (0 : ℝ), superlevel S (F * G) (lam ^ (1 / s)) := by
    have h := lintegral_Ioi_comp_rpow hs one_pos (superlevel S (F * G))
    simp only [one_mul, Real.one_rpow, mul_one] at h
    simp only [outerLpNorm]
    rw [← ENNReal.rpow_mul, one_div_mul_cancel hs.ne', ENNReal.rpow_one, h]
  have hA : outerLpNorm S₁ p F ^ p = ENNReal.ofReal p *
      ∫⁻ u in Set.Ioi (0 : ℝ), ENNReal.ofReal (u ^ (p - 1)) * superlevel S₁ F u := by
    simp only [outerLpNorm]
    rw [one_div, ENNReal.rpow_inv_rpow hp.ne']
  have hB : outerLpNorm S₂ q G ^ q = ENNReal.ofReal q *
      ∫⁻ u in Set.Ioi (0 : ℝ), ENNReal.ofReal (u ^ (q - 1)) * superlevel S₂ G u := by
    simp only [outerLpNorm]
    rw [one_div, ENNReal.rpow_inv_rpow hq.ne']
  have hanti : Antitone (superlevel S₁ F) := fun _ _ h => superlevel_anti S₁ F h
  have hmF : Measurable (superlevel S₁ F) := hanti.measurable
  -- the bound for every `t > 0`
  have key : ∀ t : ℝ, 0 < t → outerLpNorm S s (F * G) ^ s ≤
      ENNReal.ofReal (t ^ (-p)) * outerLpNorm S₁ p F ^ p +
        ENNReal.ofReal (t ^ q) * outerLpNorm S₂ q G ^ q := by
    intro t ht
    rw [hN, hA, hB]
    calc ∫⁻ lam in Set.Ioi (0 : ℝ), superlevel S (F * G) (lam ^ (1 / s))
        ≤ ∫⁻ lam in Set.Ioi (0 : ℝ), (superlevel S₁ F (t * lam ^ (1 / p)) +
            superlevel S₂ G (t⁻¹ * lam ^ (1 / q))) := by
          refine setLIntegral_mono' measurableSet_Ioi fun lam hlam => ?_
          have hlam : 0 < lam := hlam
          have e : lam ^ (1 / s) = (t * lam ^ (1 / p)) * (t⁻¹ * lam ^ (1 / q)) := by
            rw [mul_mul_mul_comm, mul_inv_cancel₀ ht.ne', one_mul, ← Real.rpow_add hlam, hpq]
          rw [e]
          exact superlevel_mul_le S S₁ S₂ hS₁ hS₂ hprod F G (by positivity)
      _ = (∫⁻ lam in Set.Ioi (0 : ℝ), superlevel S₁ F (t * lam ^ (1 / p))) +
            ∫⁻ lam in Set.Ioi (0 : ℝ), superlevel S₂ G (t⁻¹ * lam ^ (1 / q)) :=
          lintegral_add_left (hmF.comp (measurable_const.mul (measurable_id.pow_const _))) _
      _ = ENNReal.ofReal (p * t ^ (-p)) *
            (∫⁻ u in Set.Ioi (0 : ℝ), ENNReal.ofReal (u ^ (p - 1)) * superlevel S₁ F u) +
          ENNReal.ofReal (q * t⁻¹ ^ (-q)) *
            ∫⁻ u in Set.Ioi (0 : ℝ), ENNReal.ofReal (u ^ (q - 1)) * superlevel S₂ G u := by
          rw [lintegral_Ioi_comp_rpow hp ht, lintegral_Ioi_comp_rpow hq (inv_pos.mpr ht)]
      _ = _ := by
          rw [Real.rpow_neg (inv_nonneg.mpr ht.le), Real.inv_rpow ht.le, inv_inv,
            ENNReal.ofReal_mul hp.le, ENNReal.ofReal_mul hq.le]
          ring
  -- optimisation over `t`
  by_cases ha0 : outerLpNorm S₁ p F = 0
  · have : outerLpNorm S s (F * G) ^ s = 0 := by
      apply eq_zero_of_forall_le_ofReal_mul (B := outerLpNorm S₂ q G ^ q)
        (ENNReal.rpow_ne_top_of_nonneg hq.le hG)
      intro r hr
      have := key (r ^ (1 / q)) (by positivity)
      rwa [ha0, ENNReal.zero_rpow_of_pos hp, mul_zero, zero_add, ← Real.rpow_mul hr.le,
        one_div_mul_cancel hq.ne', Real.rpow_one] at this
    rw [this]
    exact zero_le
  by_cases hb0 : outerLpNorm S₂ q G = 0
  · have : outerLpNorm S s (F * G) ^ s = 0 := by
      apply eq_zero_of_forall_le_ofReal_mul (B := outerLpNorm S₁ p F ^ p)
        (ENNReal.rpow_ne_top_of_nonneg hp.le hF)
      intro r hr
      have := key (r ^ (-(1 / p))) (by positivity)
      rwa [hb0, ENNReal.zero_rpow_of_pos hq, mul_zero, add_zero, ← Real.rpow_mul hr.le,
        show -(1 / p) * -p = 1 by field_simp, Real.rpow_one] at this
    rw [this]
    exact zero_le
  have hα : 0 < (outerLpNorm S₁ p F).toReal := ENNReal.toReal_pos ha0 hF
  have hβ : 0 < (outerLpNorm S₂ q G).toReal := ENNReal.toReal_pos hb0 hG
  obtain ⟨t, ht, h1, h2⟩ := exists_holder_balance' hp hq hs hpq hα hβ
  have ea : outerLpNorm S₁ p F ^ p = ENNReal.ofReal ((outerLpNorm S₁ p F).toReal ^ p) := by
    rw [← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hp.le, ENNReal.ofReal_toReal hF]
  have eb : outerLpNorm S₂ q G ^ q = ENNReal.ofReal ((outerLpNorm S₂ q G).toReal ^ q) := by
    rw [← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hq.le, ENNReal.ofReal_toReal hG]
  have := key t ht
  rw [ea, eb, ← ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _),
    ← ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _), h1, h2, ← two_mul,
    ← ENNReal.ofReal_rpow_of_nonneg (by positivity) hs.le, ENNReal.ofReal_mul hα.le,
    ENNReal.ofReal_toReal hF, ENNReal.ofReal_toReal hG] at this
  exact this

end OuterHolder

/-! ### The outer `L¹(S₁)` norm dominates the `κ`-integral (Do–Thiele [7], Prop. 3.6)

For `F : 𝒟 → ℝ` we prove `∑_Q |F(Q)| |Q| ≤ 4 ‖F‖_{L¹(X,κ,S₁)}`. The argument chooses
near-optimal admissible collections `E_k` at the levels `2^k`, `k ∈ ℤ`, charges every cube to
the largest level containing it, bounds each level through the size on the covering trees,
and compares `∑_k 2^{k+1} μ(S₁(F) > 2^k)` with the layer-cake integral. -/

section OuterL1Bound

/-- `S₁(F)(𝒟(T)) = |T|⁻¹ ∑_{Q ∈ 𝒟(T)} |F(Q)| |Q|`. [PROVED] -/
theorem sizeP_one_eq (F : DyadicCube d → ℝ) (T : DyadicCube d) :
    sizeP 1 F T =
      ENNReal.ofReal T.vol⁻¹ * ∑' Q : T.tree, ‖F Q‖ₑ * ENNReal.ofReal (Q : DyadicCube d).vol := by
  simp [sizeP]

/-- `∑_{Q ∈ 𝒟(T)} |F(Q)| |Q| = |T| S₁(F)(𝒟(T))`. [PROVED] -/
theorem tsum_tree_eq_vol_mul_sizeP_one (F : DyadicCube d → ℝ) (T : DyadicCube d) :
    ∑' Q : T.tree, ‖F Q‖ₑ * ENNReal.ofReal (Q : DyadicCube d).vol =
      ENNReal.ofReal T.vol * sizeP 1 F T := by
  rw [sizeP_one_eq, ← mul_assoc, ← ENNReal.ofReal_mul T.vol_pos.le, mul_inv_cancel₀ T.vol_pos.ne',
    ENNReal.ofReal_one, one_mul]

/-- Cubes outside an admissible collection at level `λ` satisfy `|F(Q)| ≤ λ`. [PROVED] -/
theorem enorm_le_of_notMem_admissible {F : DyadicCube d → ℝ} {G : Set (DyadicCube d)} {lam : ℝ}
    (hG : ∀ T, sizeP 1 (Gᶜ.indicator F) T ≤ ENNReal.ofReal lam) {Q : DyadicCube d} (hQ : Q ∉ G) :
    ‖F Q‖ₑ ≤ ENNReal.ofReal lam := by
  have h1 : ‖F Q‖ₑ * ENNReal.ofReal Q.vol ≤
      ∑' P : Q.tree, ‖Gᶜ.indicator F P‖ₑ * ENNReal.ofReal (P : DyadicCube d).vol := by
    have := ENNReal.le_tsum
      (f := fun P : Q.tree => ‖Gᶜ.indicator F P‖ₑ * ENNReal.ofReal (P : DyadicCube d).vol)
      ⟨Q, DyadicCube.mem_tree.mpr Set.Subset.rfl⟩
    simpa [Set.indicator_of_mem (show Q ∈ Gᶜ from hQ)] using this
  rw [tsum_tree_eq_vol_mul_sizeP_one] at h1
  have h2 := h1.trans (mul_le_mul' le_rfl (hG Q))
  rw [mul_comm (ENNReal.ofReal Q.vol)] at h2
  exact (ENNReal.mul_le_mul_iff_left (ENNReal.ofReal_pos.mpr Q.vol_pos).ne'
    ENNReal.ofReal_ne_top).mp h2

/-- The sum over `𝒟(T) ∖ G` of `|F(Q)| |Q|`, written as a sum over all cubes. [PROVED] -/
theorem tsum_indicator_tree_eq (F : DyadicCube d → ℝ) (G : Set (DyadicCube d))
    (T : DyadicCube d) :
    ∑' Q : DyadicCube d, (T.tree \ G).indicator (fun Q => ‖F Q‖ₑ * ENNReal.ofReal Q.vol) Q =
      ENNReal.ofReal T.vol * sizeP 1 (Gᶜ.indicator F) T := by
  rw [← tsum_tree_eq_vol_mul_sizeP_one,
    tsum_subtype T.tree (fun Q => ‖Gᶜ.indicator F Q‖ₑ * ENNReal.ofReal Q.vol)]
  refine tsum_congr fun Q => ?_
  by_cases hT : Q ∈ T.tree
  · by_cases hG : Q ∈ G
    · rw [Set.indicator_of_notMem (fun h : Q ∈ T.tree \ G => h.2 hG), Set.indicator_of_mem hT,
        Set.indicator_of_notMem (fun h : Q ∈ Gᶜ => h hG)]
      simp
    · rw [Set.indicator_of_mem (show Q ∈ T.tree \ G from ⟨hT, hG⟩), Set.indicator_of_mem hT,
        Set.indicator_of_mem (show Q ∈ Gᶜ from hG)]
  · rw [Set.indicator_of_notMem (fun h : Q ∈ T.tree \ G => hT h.1), Set.indicator_of_notMem hT]

/-- Dyadic samples give a lower bound for the outer layer-cake integral. -/
private theorem dyadic_layer_cake_le (S : Size d) (F : DyadicCube d → ℝ) :
    ∑' k : ℤ, ENNReal.ofReal ((2 : ℝ) ^ (k - 1)) * superlevel S F ((2 : ℝ) ^ k) ≤
      ∫⁻ lam in Set.Ioi (0 : ℝ), superlevel S F lam := by
  -- the intervals `(2^{k-1}, 2^k]` partition `(0, ∞)`
  have hU : Set.Ioi (0 : ℝ) = ⋃ k : ℤ, Set.Ioc ((2 : ℝ) ^ (k - 1)) ((2 : ℝ) ^ k) := by
    ext lam
    constructor
    · intro h
      obtain ⟨n, hn⟩ := exists_mem_Ioc_zpow (show (0 : ℝ) < lam from h) (by norm_num : (1 : ℝ) < 2)
      exact Set.mem_iUnion.mpr ⟨n + 1, by simpa using hn⟩
    · intro h
      obtain ⟨k, hk⟩ := Set.mem_iUnion.mp h
      exact lt_of_lt_of_le (zpow_pos (by norm_num) _) hk.1.le
  have hdisj : Pairwise (Function.onFun Disjoint
      fun k : ℤ => Set.Ioc ((2 : ℝ) ^ (k - 1)) ((2 : ℝ) ^ k)) := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact Set.Ioc_disjoint_Ioc_of_le (zpow_le_zpow_right₀ (by norm_num) (by omega))
    · exact (Set.Ioc_disjoint_Ioc_of_le (zpow_le_zpow_right₀ (by norm_num) (by omega))).symm
  have hpow : ∀ k : ℤ, (2 : ℝ) ^ k - (2 : ℝ) ^ (k - 1) = (2 : ℝ) ^ (k - 1) := by
    intro k
    rw [zpow_sub_one₀ (by norm_num : (2 : ℝ) ≠ 0)]
    ring
  -- layer-cake lower bound over the dyadic levels
  rw [hU, lintegral_iUnion (fun _ => measurableSet_Ioc) hdisj]
  refine ENNReal.tsum_le_tsum fun k => ?_
  calc ENNReal.ofReal ((2 : ℝ) ^ (k - 1)) * superlevel S F ((2 : ℝ) ^ k)
      = ∫⁻ _ in Set.Ioc ((2 : ℝ) ^ (k - 1)) ((2 : ℝ) ^ k),
          superlevel S F ((2 : ℝ) ^ k) := by
        rw [setLIntegral_const, Real.volume_Ioc, hpow, mul_comm]
    _ ≤ ∫⁻ lam in Set.Ioc ((2 : ℝ) ^ (k - 1)) ((2 : ℝ) ^ k), superlevel S F lam :=
        setLIntegral_mono' measurableSet_Ioc fun lam hlam => superlevel_anti _ _ hlam.2


/-- **Proposition 3.6 of Do–Thiele** in the dyadic setting:
`∑_Q |F(Q)| |Q| ≤ 4 ‖F‖_{L¹(X,κ,S₁)}`. [PROVED] -/
theorem tsum_enorm_mul_vol_le (F : DyadicCube d → ℝ) :
    ∑' Q : DyadicCube d, ‖F Q‖ₑ * ENNReal.ofReal Q.vol ≤ 4 * outerLpNorm (sizeP 1) 1 F := by
  have hN : outerLpNorm (sizeP 1) 1 F =
      ∫⁻ lam in Set.Ioi (0 : ℝ), superlevel (sizeP 1) F lam := by
    simp [outerLpNorm]
  rw [hN]
  have hlayer := dyadic_layer_cake_le (sizeP 1) F
  -- trivial case: infinite right-hand side
  by_cases hint : (∫⁻ lam in Set.Ioi (0 : ℝ), superlevel (sizeP 1) F lam) = ⊤
  · rw [hint, ENNReal.mul_top (by norm_num)]
    exact le_top
  have hfin : ∀ k : ℤ, superlevel (sizeP 1) F ((2 : ℝ) ^ k) ≠ ⊤ := by
    intro k hk
    apply hint
    have h1 : ENNReal.ofReal ((2 : ℝ) ^ (k - 1)) * superlevel (sizeP 1) F ((2 : ℝ) ^ k) = ⊤ := by
      rw [hk, ENNReal.mul_top (ENNReal.ofReal_pos.mpr (zpow_pos (by norm_num) _)).ne']
    have h2 := (ENNReal.le_tsum k).trans hlayer
    rw [h1] at h2
    exact top_le_iff.mp h2
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  obtain ⟨ε', hε'pos, hε'sum⟩ :=
    ENNReal.exists_pos_sum_of_countable (ENNReal.coe_pos.mpr hε).ne' ℤ
  -- near-optimal admissible collections and covers at the levels `2^k`
  have hchoice : ∀ k : ℤ, ∃ (E C : Set (DyadicCube d)),
      (∀ T, sizeP 1 (Eᶜ.indicator F) T ≤ ENNReal.ofReal ((2 : ℝ) ^ k)) ∧ E ⊆ ⋃ T ∈ C, T.tree ∧
      ∑' T : C, ENNReal.ofReal (T : DyadicCube d).vol ≤
        superlevel (sizeP 1) F ((2 : ℝ) ^ k) + ε' k * ENNReal.ofReal ((2 : ℝ) ^ (-(k + 1))) := by
    intro k
    have hne : (ε' k : ENNReal) * ENNReal.ofReal ((2 : ℝ) ^ (-(k + 1))) ≠ 0 :=
      mul_ne_zero (ENNReal.coe_pos.mpr (hε'pos k)).ne'
        (ENNReal.ofReal_pos.mpr (zpow_pos (by norm_num) _)).ne'
    set M := superlevel (sizeP 1) F ((2 : ℝ) ^ k) +
      ε' k * ENNReal.ofReal ((2 : ℝ) ^ (-(k + 1))) with hM
    have hlt : superlevel (sizeP 1) F ((2 : ℝ) ^ k) < M := ENNReal.lt_add_right (hfin k) hne
    unfold superlevel at hlt
    rw [iInf_lt_iff] at hlt
    obtain ⟨E, hlt⟩ := hlt
    rw [iInf_lt_iff] at hlt
    obtain ⟨hE, hlt⟩ := hlt
    unfold outerMeasure at hlt
    rw [iInf_lt_iff] at hlt
    obtain ⟨C, hlt⟩ := hlt
    rw [iInf_lt_iff] at hlt
    obtain ⟨hC, hlt⟩ := hlt
    exact ⟨E, C, hE, hC, hlt.le⟩
  choose E C hE hC hCsum using hchoice
  -- every cube with `F Q ≠ 0` lies in some `E k ∖ E (k+1)`
  have hlevel : ∀ Q : DyadicCube d, F Q ≠ 0 → ∃ k : ℤ, Q ∈ E k \ E (k + 1) := by
    intro Q hQ
    have hFQ : 0 < ‖F Q‖ := norm_pos_iff.mpr hQ
    have hvol : 0 < Q.vol := Q.vol_pos
    -- small levels contain `Q`
    have hsmall : ∀ k : ℤ, (2 : ℝ) ^ k < ‖F Q‖ → Q ∈ E k := by
      intro k hk
      by_contra h
      have := enorm_le_of_notMem_admissible (hE k) h
      rw [← ofReal_norm, ENNReal.ofReal_le_ofReal_iff (zpow_pos (by norm_num) _).le] at this
      linarith
    -- the superlevel measures become smaller than `|Q|/2`
    have hk0 : ∃ k₀ : ℤ, superlevel (sizeP 1) F ((2 : ℝ) ^ k₀) < ENNReal.ofReal Q.vol / 2 := by
      by_contra h
      simp only [not_exists, not_lt] at h
      have hc : ENNReal.ofReal Q.vol / 2 * ENNReal.ofReal ((2 : ℝ) ^ (-1 : ℤ)) ≠ 0 :=
        mul_ne_zero (ENNReal.div_pos_iff.mpr
            ⟨(ENNReal.ofReal_pos.mpr hvol).ne', ENNReal.ofNat_ne_top⟩).ne'
          (ENNReal.ofReal_pos.mpr (zpow_pos (by norm_num) _)).ne'
      have h1 : ∑' _ : ℕ, ENNReal.ofReal Q.vol / 2 * ENNReal.ofReal ((2 : ℝ) ^ (-1 : ℤ)) = ⊤ :=
        ENNReal.tsum_const_eq_top_of_ne_zero hc
      have h2 : ∑' _ : ℕ, ENNReal.ofReal Q.vol / 2 * ENNReal.ofReal ((2 : ℝ) ^ (-1 : ℤ)) ≤
          ∑' n : ℕ, ENNReal.ofReal ((2 : ℝ) ^ ((n : ℤ) - 1)) *
            superlevel (sizeP 1) F ((2 : ℝ) ^ (n : ℤ)) := by
        refine ENNReal.tsum_le_tsum fun n => ?_
        rw [mul_comm]
        exact mul_le_mul' (ENNReal.ofReal_le_ofReal (zpow_le_zpow_right₀ (by norm_num) (by omega)))
          (h n)
      have h3 := ENNReal.tsum_comp_le_tsum_of_injective (Nat.cast_injective (R := ℤ))
        (fun k : ℤ => ENNReal.ofReal ((2 : ℝ) ^ (k - 1)) * superlevel (sizeP 1) F ((2 : ℝ) ^ k))
      have h4 := h2.trans (h3.trans hlayer)
      rw [h1] at h4
      exact hint (top_le_iff.mp h4)
    obtain ⟨k₀, hk₀⟩ := hk0
    -- the error terms become smaller than `|Q|/2`
    have hεk : ∃ k₁ : ℤ, ∀ k, k₁ ≤ k →
        (ε' k : ENNReal) * ENNReal.ofReal ((2 : ℝ) ^ (-(k + 1))) < ENNReal.ofReal Q.vol / 2 := by
      have hεle : ∀ k, (ε' k : ENNReal) ≤ ε := fun k => (ENNReal.le_tsum k).trans hε'sum.le
      have hε0 : (0 : ℝ) < ε := hε
      obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos (half_pos hvol) hε0)
        (by norm_num : (1 / 2 : ℝ) < 1)
      refine ⟨n, fun k hk => ?_⟩
      calc (ε' k : ENNReal) * ENNReal.ofReal ((2 : ℝ) ^ (-(k + 1)))
          ≤ (ε : ENNReal) * ENNReal.ofReal ((2 : ℝ) ^ (-(k + 1))) := mul_le_mul' (hεle k) le_rfl
        _ = ENNReal.ofReal (ε * (2 : ℝ) ^ (-(k + 1))) := by
            rw [ENNReal.ofReal_mul hε0.le, ENNReal.ofReal_coe_nnreal]
        _ < ENNReal.ofReal (Q.vol / 2) := by
            apply (ENNReal.ofReal_lt_ofReal_iff (half_pos hvol)).mpr
            have h1 : (2 : ℝ) ^ (-(k + 1)) ≤ (1 / 2 : ℝ) ^ n := by
              rw [one_div, inv_pow, ← zpow_natCast, ← zpow_neg]
              exact zpow_le_zpow_right₀ (by norm_num) (by omega)
            calc ε * (2 : ℝ) ^ (-(k + 1)) ≤ ε * (1 / 2 : ℝ) ^ n :=
                  mul_le_mul_of_nonneg_left h1 hε0.le
              _ < ε * ((Q.vol / 2) / ε) := mul_lt_mul_of_pos_left hn hε0
              _ = Q.vol / 2 := by rw [mul_div_assoc', mul_div_cancel_left₀ _ hε0.ne']
        _ = ENNReal.ofReal Q.vol / 2 := by
            rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_ofNat]
    obtain ⟨k₁, hk₁⟩ := hεk
    have hbig : ∀ k : ℤ, max k₀ k₁ ≤ k → Q ∉ E k := by
      intro k hk hQk
      obtain ⟨T, hT, hQT⟩ := Set.mem_iUnion₂.mp (hC k hQk)
      have h1 : ENNReal.ofReal Q.vol ≤ ∑' T : C k, ENNReal.ofReal (T : DyadicCube d).vol :=
        (ENNReal.ofReal_le_ofReal (DyadicCube.vol_le_of_subset hQT)).trans
          (ENNReal.le_tsum (f := fun T : C k => ENNReal.ofReal (T : DyadicCube d).vol) ⟨T, hT⟩)
      have h2 : superlevel (sizeP 1) F ((2 : ℝ) ^ k) < ENNReal.ofReal Q.vol / 2 :=
        lt_of_le_of_lt (superlevel_anti _ _
          (zpow_le_zpow_right₀ (by norm_num) (le_of_max_le_left hk))) hk₀
      have h3 := hk₁ k (le_of_max_le_right hk)
      have h4 := h1.trans (hCsum k)
      rw [← ENNReal.add_halves (ENNReal.ofReal Q.vol)] at h4
      exact absurd h4 (not_le.mpr (ENNReal.add_lt_add h2 h3))
    -- a small level containing `Q`
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hFQ (by norm_num : (1 / 2 : ℝ) < 1)
    have hmem : Q ∈ E (-(n : ℤ)) := hsmall _ (by
      rw [zpow_neg, zpow_natCast, ← one_div, ← one_div_pow]
      exact hn)
    -- the largest level containing `Q`
    set K : Set ℤ := {k | Q ∈ E k} with hK
    have hne : K.Nonempty := Set.nonempty_of_mem (show (-(n : ℤ)) ∈ K from hmem)
    have hbdd : BddAbove K := bddAbove_def.mpr ⟨max k₀ k₁, fun k hk => by
      by_contra h
      exact hbig k (not_le.mp h).le hk⟩
    refine ⟨sSup K, Set.mem_sdiff_of_mem (Int.csSup_mem hne hbdd) fun h => ?_⟩
    have := le_csSup hbdd (show sSup K + 1 ∈ K from h)
    omega
  -- the main estimate
  have hf_le : ∀ Q : DyadicCube d, ‖F Q‖ₑ * ENNReal.ofReal Q.vol ≤
      ∑' k : ℤ, (E k \ E (k + 1)).indicator (fun Q => ‖F Q‖ₑ * ENNReal.ofReal Q.vol) Q := by
    intro Q
    by_cases hQ : F Q = 0
    · simp [hQ]
    · obtain ⟨k, hk⟩ := hlevel Q hQ
      calc ‖F Q‖ₑ * ENNReal.ofReal Q.vol
          = (E k \ E (k + 1)).indicator (fun Q => ‖F Q‖ₑ * ENNReal.ofReal Q.vol) Q :=
            (Set.indicator_of_mem hk (fun Q => ‖F Q‖ₑ * ENNReal.ofReal Q.vol)).symm
        _ ≤ _ := ENNReal.le_tsum
            (f := fun k : ℤ => (E k \ E (k + 1)).indicator
              (fun Q => ‖F Q‖ₑ * ENNReal.ofReal Q.vol) Q) k
  have hlevel_le : ∀ k : ℤ,
      ∑' Q : DyadicCube d, (E k \ E (k + 1)).indicator (fun Q => ‖F Q‖ₑ * ENNReal.ofReal Q.vol) Q ≤
        ENNReal.ofReal ((2 : ℝ) ^ (k + 1)) * superlevel (sizeP 1) F ((2 : ℝ) ^ k) + ε' k := by
    intro k
    calc ∑' Q : DyadicCube d, (E k \ E (k + 1)).indicator (fun Q => ‖F Q‖ₑ * ENNReal.ofReal Q.vol) Q
        ≤ ∑' Q : DyadicCube d, ∑' T : C k, ((T : DyadicCube d).tree \ E (k + 1)).indicator
            (fun Q => ‖F Q‖ₑ * ENNReal.ofReal Q.vol) Q := by
          refine ENNReal.tsum_le_tsum fun Q => ?_
          by_cases hQ : Q ∈ E k \ E (k + 1)
          · obtain ⟨T, hT, hQT⟩ := Set.mem_iUnion₂.mp (hC k hQ.1)
            calc (E k \ E (k + 1)).indicator (fun Q => ‖F Q‖ₑ * ENNReal.ofReal Q.vol) Q
                = (T.tree \ E (k + 1)).indicator (fun Q => ‖F Q‖ₑ * ENNReal.ofReal Q.vol) Q := by
                  rw [Set.indicator_of_mem hQ,
                    Set.indicator_of_mem (show Q ∈ T.tree \ E (k + 1) from ⟨hQT, hQ.2⟩)]
              _ ≤ _ := ENNReal.le_tsum
                  (f := fun T : C k => ((T : DyadicCube d).tree \ E (k + 1)).indicator
                    (fun Q => ‖F Q‖ₑ * ENNReal.ofReal Q.vol) Q) ⟨T, hT⟩
          · rw [Set.indicator_of_notMem hQ]
            exact zero_le
      _ = ∑' T : C k, ∑' Q : DyadicCube d, ((T : DyadicCube d).tree \ E (k + 1)).indicator
            (fun Q => ‖F Q‖ₑ * ENNReal.ofReal Q.vol) Q := ENNReal.tsum_comm
      _ ≤ ∑' T : C k, ENNReal.ofReal (T : DyadicCube d).vol * ENNReal.ofReal ((2 : ℝ) ^ (k + 1)) :=
        by
          refine ENNReal.tsum_le_tsum fun T => ?_
          rw [tsum_indicator_tree_eq]
          exact mul_le_mul' le_rfl (hE (k + 1) T)
      _ = ENNReal.ofReal ((2 : ℝ) ^ (k + 1)) * ∑' T : C k, ENNReal.ofReal (T : DyadicCube d).vol :=
        by
          rw [ENNReal.tsum_mul_right, mul_comm]
      _ ≤ ENNReal.ofReal ((2 : ℝ) ^ (k + 1)) * (superlevel (sizeP 1) F ((2 : ℝ) ^ k) +
            ε' k * ENNReal.ofReal ((2 : ℝ) ^ (-(k + 1)))) := by
          gcongr
          exact hCsum k
      _ = ENNReal.ofReal ((2 : ℝ) ^ (k + 1)) * superlevel (sizeP 1) F ((2 : ℝ) ^ k) + ε' k := by
          rw [mul_add, mul_left_comm, ← ENNReal.ofReal_mul (zpow_pos (by norm_num) _).le,
            ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), add_neg_cancel, zpow_zero, ENNReal.ofReal_one,
            mul_one]
  have h4 : ∀ k : ℤ, ENNReal.ofReal ((2 : ℝ) ^ (k + 1)) = 4 * ENNReal.ofReal ((2 : ℝ) ^ (k - 1)) :=
    by
    intro k
    have e : (2 : ℝ) ^ (k + 1) = 4 * (2 : ℝ) ^ (k - 1) := by
      rw [zpow_add_one₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_sub_one₀ (by norm_num : (2 : ℝ) ≠ 0)]
      ring
    rw [e, ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
  calc ∑' Q : DyadicCube d, ‖F Q‖ₑ * ENNReal.ofReal Q.vol
      ≤ ∑' Q : DyadicCube d, ∑' k : ℤ,
          (E k \ E (k + 1)).indicator (fun Q => ‖F Q‖ₑ * ENNReal.ofReal Q.vol) Q :=
        ENNReal.tsum_le_tsum hf_le
    _ = ∑' k : ℤ, ∑' Q : DyadicCube d,
          (E k \ E (k + 1)).indicator (fun Q => ‖F Q‖ₑ * ENNReal.ofReal Q.vol) Q :=
        ENNReal.tsum_comm
    _ ≤ ∑' k : ℤ, (ENNReal.ofReal ((2 : ℝ) ^ (k + 1)) * superlevel (sizeP 1) F ((2 : ℝ) ^ k) +
          ε' k) := ENNReal.tsum_le_tsum hlevel_le
    _ = ∑' k : ℤ, ENNReal.ofReal ((2 : ℝ) ^ (k + 1)) * superlevel (sizeP 1) F ((2 : ℝ) ^ k) +
          ∑' k : ℤ, (ε' k : ENNReal) := ENNReal.tsum_add
    _ ≤ 4 * (∫⁻ lam in Set.Ioi (0 : ℝ), superlevel (sizeP 1) F lam) + ε := by
        refine add_le_add ?_ hε'sum.le
        calc ∑' k : ℤ, ENNReal.ofReal ((2 : ℝ) ^ (k + 1)) * superlevel (sizeP 1) F ((2 : ℝ) ^ k)
            = 4 * ∑' k : ℤ, ENNReal.ofReal ((2 : ℝ) ^ (k - 1)) *
                superlevel (sizeP 1) F ((2 : ℝ) ^ k) := by
              rw [← ENNReal.tsum_mul_left]
              exact tsum_congr fun k => by rw [h4, mul_assoc]
          _ ≤ _ := by gcongr

end OuterL1Bound

/-! ### Theorem 2.68 for `1 < p < ∞` -/

section CarlesonProof


variable {f : (Fin d → ℝ) → ℝ}

/-- (2.70) at `p = 1`, restated with the level `λ` in place of `2^d λ`. [PROVED] -/
theorem superlevel_martDiff_le' (hd : d ≠ 0) (hf : Integrable f volume) {lam : ℝ}
    (hlam : 0 < lam) :
    superlevel (sizeP 2) (fun T => martDiff T f) lam ≤
      ENNReal.ofReal (2 ^ d * (∫ x, |f x|) / lam) := by
  have h2d : (0 : ℝ) < 2 ^ d := by positivity
  have hlam' : 0 < lam / 2 ^ d := div_pos hlam h2d
  have hmu' : (2 : ℝ) ^ d * (lam / 2 ^ d) = lam := by
    rw [mul_div_assoc', mul_div_cancel_left₀ _ h2d.ne']
  have hb := superlevel_martDiff_le hd hf hlam'
  rw [hmu'] at hb
  refine hb.trans (le_of_eq ?_)
  congr 1
  rw [div_div_eq_mul_div, mul_comm]

/-- **Theorem 2.68** (discrete Carleson embedding) for `1 < p < ∞`, deduced from the four
endpoint estimates by the Marcinkiewicz interpolation theorem for outer measure spaces.
[PROVED] -/
theorem carlesonEmbedding (hd : d ≠ 0) (p : ℝ) : CarlesonEmbedding d p := by
  intro hp
  refine ⟨max (marcConst 1 1 p) (marcConst (2 ^ d) 1 p),
    le_max_of_le_left (marcConst_nonneg zero_le_one zero_le_one hp), fun f hf => ⟨?_, ?_⟩⟩
  · -- the martingale averages `E`
    have h := marcinkiewicz sizeInf (fun f T => martAvg T f) (A₁ := 1) (A₂ := 1)
      (fun F G T h => sizeInf_mono h T) (fun F G T => sizeInf_add F G T)
      (fun f g hf hg Q => by
        simp only [abs_of_nonneg (martAvg_nonneg _ _)]
        exact martAvg_add_le Q hf.integrableOn
          (integrableOn_of_ae_bound Q hg.aestronglyMeasurable (memLp_top_ae_bound hg)))
      (fun f g hfg => martAvg_congr_ae hfg) zero_le_one zero_le_one
      (fun f hf lam hlam => by
        simpa only [Real.norm_eq_abs, one_mul] using superlevel_martAvg_le hd hf hlam)
      (fun f hf T => by
        rw [ENNReal.ofReal_one, one_mul]
        exact (le_iSup (fun T => sizeInf (fun T => martAvg T f) T) T).trans
          (outerLinfNorm_martAvg_le hf))
      hp f hf
    refine h.trans ?_
    gcongr
    exact le_max_left _ _
  · -- the martingale differences `Δ`
    have h := marcinkiewicz (sizeP 2) (fun f T => martDiff T f) (A₁ := 2 ^ d) (A₂ := 1)
      (fun F G T h => sizeP_mono (by norm_num) h T) (fun F G T => sizeP_two_add F G T)
      (fun f g hf hg Q => by
        simp only [abs_of_nonneg (martDiff_nonneg _ _)]
        exact martDiff_add_le Q hf.integrableOn
          (integrableOn_of_ae_bound Q hg.aestronglyMeasurable (memLp_top_ae_bound hg)))
      (fun f g hfg => martDiff_congr_ae hfg) (by positivity) zero_le_one
      (fun f hf lam hlam => by
        simpa only [Real.norm_eq_abs] using superlevel_martDiff_le' hd hf hlam)
      (fun f hf T => by
        rw [ENNReal.ofReal_one, one_mul]
        exact (le_iSup (fun T => sizeP 2 (fun T => martDiff T f) T) T).trans
          (outerLinfNorm_martDiff_le hd hf))
      hp f hf
    refine h.trans ?_
    gcongr
    exact le_max_right _ _

end CarlesonProof

/-! ### Lemma 2.71 -/

section Lemma271Proof

/-- The pointwise Cauchy–Schwarz inequality for sizes: `S₁(FG) ≤ S₂(F) S₂(G)`. [PROVED] -/
theorem sizeP_one_mul_le_sizeP_two (F G : DyadicCube d → ℝ) (T : DyadicCube d) :
    sizeP 1 (F * G) T ≤ sizeP 2 F T * sizeP 2 G T := by
  rw [sizeP_one_eq, sizeP_two_eq_lintegral, sizeP_two_eq_lintegral]
  set w : DyadicCube d → ENNReal :=
    fun Q => (T.tree.indicator (fun Q => ENNReal.ofReal Q.vol) Q) ^ (1 / 2 : ℝ) with hw_def
  have hw : ∀ Q, w Q * w Q = T.tree.indicator (fun Q => ENNReal.ofReal Q.vol) Q := by
    intro Q
    change (T.tree.indicator (fun Q => ENNReal.ofReal Q.vol) Q) ^ (1 / 2 : ℝ) *
      (T.tree.indicator (fun Q => ENNReal.ofReal Q.vol) Q) ^ (1 / 2 : ℝ) = _
    rw [← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
    norm_num
  have h1 : ∑' Q : T.tree, ‖(F * G) Q‖ₑ * ENNReal.ofReal (Q : DyadicCube d).vol =
      ∫⁻ Q, ((fun Q => ‖F Q‖ₑ * w Q) * fun Q => ‖G Q‖ₑ * w Q) Q ∂Measure.count := by
    rw [lintegral_count, tsum_subtype T.tree (fun Q => ‖(F * G) Q‖ₑ * ENNReal.ofReal Q.vol)]
    refine tsum_congr fun Q => ?_
    by_cases hQ : Q ∈ T.tree
    · have hwQ : w Q * w Q = ENNReal.ofReal Q.vol := by rw [hw Q, Set.indicator_of_mem hQ]
      rw [Set.indicator_of_mem hQ, Pi.mul_apply, Pi.mul_apply, enorm_mul, ← hwQ]
      ring
    · have hw0 : w Q = 0 := by
        change (T.tree.indicator (fun Q => ENNReal.ofReal Q.vol) Q) ^ (1 / 2 : ℝ) = 0
        rw [Set.indicator_of_notMem hQ]
        exact ENNReal.zero_rpow_of_pos (by norm_num)
      rw [Set.indicator_of_notMem hQ, Pi.mul_apply, hw0]
      simp
  have h2 := ENNReal.lintegral_mul_le_Lp_mul_Lq Measure.count Real.HolderConjugate.two_two
    (f := fun Q => ‖F Q‖ₑ * w Q) (g := fun Q => ‖G Q‖ₑ * w Q)
    Measurable.of_discrete.aemeasurable Measurable.of_discrete.aemeasurable
  rw [h1]
  calc ENNReal.ofReal T.vol⁻¹ *
        ∫⁻ Q, ((fun Q => ‖F Q‖ₑ * w Q) * fun Q => ‖G Q‖ₑ * w Q) Q ∂Measure.count
      ≤ ENNReal.ofReal T.vol⁻¹ *
          ((∫⁻ Q, (‖F Q‖ₑ * w Q) ^ (2 : ℝ) ∂Measure.count) ^ (1 / 2 : ℝ) *
            (∫⁻ Q, (‖G Q‖ₑ * w Q) ^ (2 : ℝ) ∂Measure.count) ^ (1 / 2 : ℝ)) := by
        gcongr
    _ = _ := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ENNReal.mul_rpow_of_nonneg _ _ (by
          norm_num)]
        have ha : ENNReal.ofReal T.vol⁻¹ =
            ENNReal.ofReal T.vol⁻¹ ^ (1 / 2 : ℝ) * ENNReal.ofReal T.vol⁻¹ ^ (1 / 2 : ℝ) := by
          rw [← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
          norm_num
        conv_lhs => rw [ha]
        ring

/-- `S₁(FG) ≤ S_∞(F) S₁(G)`. [PROVED] -/
theorem sizeP_one_mul_le_sizeInf (F G : DyadicCube d → ℝ) (T : DyadicCube d) :
    sizeP 1 (F * G) T ≤ sizeInf F T * sizeP 1 G T := by
  rw [sizeP_one_eq, sizeP_one_eq]
  simp only [sizeInf]
  rw [mul_left_comm]
  refine mul_le_mul' le_rfl ?_
  rw [← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun Q => ?_
  rw [Pi.mul_apply, enorm_mul, mul_assoc]
  exact mul_le_mul' (le_iSup (fun Q : T.tree => ‖F Q‖ₑ) Q) le_rfl

/-- `S₁(F²) = S₂(F)²`. [PROVED] -/
theorem sizeP_one_sq (F : DyadicCube d → ℝ) (T : DyadicCube d) :
    sizeP 1 (fun Q => F Q ^ 2) T = sizeP 2 F T ^ 2 := by
  rw [sizeP_one_eq]
  simp only [sizeP]
  rw [← ENNReal.rpow_natCast, Nat.cast_ofNat, ← ENNReal.rpow_mul,
    one_div_mul_cancel (by norm_num : (2 : ℝ) ≠ 0), ENNReal.rpow_one]
  congr 1
  refine tsum_congr fun Q => ?_
  rw [enorm_pow, ENNReal.rpow_two]

/-- Averages over `T ⊆ R` only see `f 𝟙_R`. [PROVED] -/
theorem avg_truncate_of_subset {T R : DyadicCube d} (h : T.toSet ⊆ R.toSet)
    (f : (Fin d → ℝ) → ℝ) : avg T (truncate R f) = avg T f := by
  simp only [avg, truncate]
  rw [setIntegral_indicator R.measurableSet_toSet, Set.inter_eq_left.mpr h]

theorem martAvg_truncate_of_subset {T R : DyadicCube d} (h : T.toSet ⊆ R.toSet)
    (f : (Fin d → ℝ) → ℝ) : martAvg T (truncate R f) = martAvg T f := by
  simp only [martAvg, avg_truncate_of_subset h]

theorem martDiff_truncate_of_subset {T R : DyadicCube d} (h : T.toSet ⊆ R.toSet)
    (f : (Fin d → ℝ) → ℝ) : martDiff T (truncate R f) = martDiff T f := by
  have hc : ∀ ε, avg (T.child ε) (truncate R f) = avg (T.child ε) f :=
    fun ε => avg_truncate_of_subset ((T.child_subset ε).trans h) f
  simp only [martDiff, avg_truncate_of_subset h, hc]

/-- **Lemma 2.71** (with the integrability hypotheses of the paper made explicit, and the
conclusion in `[0, ∞]`): if `f₁ ∈ L^p`, `f₂ ∈ L^{p'}` with `1/p + 1/p' = 1`, `f₃ ∈ L^∞` with
`‖f₃‖_∞ ≤ 1`, and the coefficients `α_T`, `T ⊆ R`, are dominated by
`C₀ (Δ_T f₁ Δ_T f₂ + E_T f₁ Δ_T f₂ Δ_T f₃ + E_T f₂ Δ_T f₁ Δ_T f₃ + E_T f₁ E_T f₂ (Δ_T f₃)²) |T|`,
then `∑_{T ⊆ R} |α_T| ≤ C C₀ ‖f₁ 𝟙_R‖_p ‖f₂ 𝟙_R‖_{p'}`. Proved below as `lemma271`. [PROVED] -/
def Lemma271 (d : ℕ) (p p' : ℝ) : Prop :=
  1 < p → 1 < p' → 1 / p + 1 / p' = 1 → ∃ C : ℝ, 0 ≤ C ∧
    ∀ (C₀ : ℝ) (R : DyadicCube d) (f₁ f₂ f₃ : (Fin d → ℝ) → ℝ) (α : DyadicCube d → ℝ),
      0 ≤ C₀ → MemLp f₁ (ENNReal.ofReal p) volume → MemLp f₂ (ENNReal.ofReal p') volume →
      MemLp f₃ ⊤ volume → eLpNorm f₃ ⊤ volume ≤ 1 →
      (∀ T ∈ R.tree, |α T| ≤ C₀ * (martDiff T f₁ * martDiff T f₂
        + martAvg T f₁ * martDiff T f₂ * martDiff T f₃
        + martAvg T f₂ * martDiff T f₁ * martDiff T f₃
        + martAvg T f₁ * martAvg T f₂ * martDiff T f₃ ^ 2) * T.vol) →
      ∑' T : R.tree, ‖α T‖ₑ ≤ ENNReal.ofReal (C * C₀) *
        (eLpNorm (truncate R f₁) (ENNReal.ofReal p) volume *
          eLpNorm (truncate R f₂) (ENNReal.ofReal p') volume)

/-- **Lemma 2.71**, deduced from Theorem 2.68, Hölder's inequality for outer measure spaces and
Proposition 3.6 of Do–Thiele. [PROVED] -/
theorem lemma271 (hd : d ≠ 0) (p p' : ℝ) : Lemma271 d p p' := by
  intro hp hp' hpp'
  obtain ⟨Cp, hCp0, hCp⟩ := carlesonEmbedding hd p hp
  obtain ⟨Cp', hCp'0, hCp'⟩ := carlesonEmbedding hd p' hp'
  refine ⟨32 * Cp * Cp', by positivity, ?_⟩
  intro C₀ R f₁ f₂ f₃ α hC₀ hf₁ hf₂ hf₃ hf₃1 hα
  -- the truncated functions and their outer norms
  set g₁ := truncate R f₁ with hg₁
  set g₂ := truncate R f₂ with hg₂
  have hg₁L : MemLp g₁ (ENNReal.ofReal p) volume :=
    hf₁.indicator R.measurableSet_toSet.nullMeasurableSet
  have hg₂L : MemLp g₂ (ENNReal.ofReal p') volume :=
    hf₂.indicator R.measurableSet_toSet.nullMeasurableSet
  obtain ⟨hE₁, hΔ₁⟩ := hCp g₁ hg₁L
  obtain ⟨hE₂, hΔ₂⟩ := hCp' g₂ hg₂L
  have hΔ₃1 : outerLinfNorm (sizeP 2) (fun T => martDiff T f₃) ≤ 1 :=
    (outerLinfNorm_martDiff_le hd hf₃).trans hf₃1
  set N₁ := eLpNorm g₁ (ENNReal.ofReal p) volume with hN₁def
  set N₂ := eLpNorm g₂ (ENNReal.ofReal p') volume with hN₂def
  have hN₁ : N₁ ≠ ⊤ := hg₁L.eLpNorm_ne_top
  have hN₂ : N₂ ≠ ⊤ := hg₂L.eLpNorm_ne_top
  have hE₁fin : outerLpNorm sizeInf p (fun T => martAvg T g₁) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hN₁) hE₁
  have hΔ₁fin : outerLpNorm (sizeP 2) p (fun T => martDiff T g₁) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hN₁) hΔ₁
  have hE₂fin : outerLpNorm sizeInf p' (fun T => martAvg T g₂) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hN₂) hE₂
  have hΔ₂fin : outerLpNorm (sizeP 2) p' (fun T => martDiff T g₂) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hN₂) hΔ₂
  -- monotonicity of the sizes
  have hS₂ : ∀ F G : DyadicCube d → ℝ, ∀ T, (∀ Q, ‖F Q‖ₑ ≤ ‖G Q‖ₑ) → sizeP 2 F T ≤ sizeP 2 G T :=
    fun F G T h => sizeP_mono (by norm_num) h T
  have hS₁ : ∀ F G : DyadicCube d → ℝ, ∀ T, (∀ Q, ‖F Q‖ₑ ≤ ‖G Q‖ₑ) → sizeP 1 F T ≤ sizeP 1 G T :=
    fun F G T h => sizeP_mono (by norm_num) h T
  have hSinf : ∀ F G : DyadicCube d → ℝ, ∀ T, (∀ Q, ‖F Q‖ₑ ≤ ‖G Q‖ₑ) → sizeInf F T ≤ sizeInf G T :=
    fun F G T h => sizeInf_mono h T
  have hpp'' : 1 / p' + 1 / p = 1 := by rw [add_comm]; exact hpp'
  -- the four terms
  set K : ENNReal := 2 * (ENNReal.ofReal Cp * N₁ * (ENNReal.ofReal Cp' * N₂)) with hK
  set A : DyadicCube d → ℝ := ((fun T => martDiff T g₁) * fun T => martDiff T g₂) with hAdef
  set B : DyadicCube d → ℝ :=
    ((fun T => martAvg T g₁) * ((fun T => martDiff T g₂) * fun T => martDiff T f₃)) with hBdef
  set Cf : DyadicCube d → ℝ :=
    ((fun T => martAvg T g₂) * ((fun T => martDiff T g₁) * fun T => martDiff T f₃)) with hCdef
  set D : DyadicCube d → ℝ :=
    ((fun T => martAvg T g₁) * ((fun T => martAvg T g₂) * fun T => martDiff T f₃ ^ 2)) with hDdef
  have hA : outerLpNorm (sizeP 1) 1 A ≤ K := by
    refine (outerL1Norm_mul_le (sizeP 1) (sizeP 2) (sizeP 2) hS₂ hS₂ sizeP_one_mul_le_sizeP_two
      hp hp' hpp' _ _ hΔ₁fin hΔ₂fin).trans ?_
    rw [hK]
    exact mul_le_mul' le_rfl (mul_le_mul' hΔ₁ hΔ₂)
  have hB : outerLpNorm (sizeP 1) 1 B ≤ K := by
    have h23 : outerLpNorm (sizeP 1) p' ((fun T => martDiff T g₂) * fun T => martDiff T f₃) ≤
        outerLpNorm (sizeP 2) p' (fun T => martDiff T g₂) := by
      refine (outerLpNorm_mul_le_Linf (sizeP 1) (sizeP 2) (sizeP 2) hS₂ hS₂
        sizeP_one_mul_le_sizeP_two (by linarith) _ _
        (ne_top_of_le_ne_top ENNReal.one_ne_top hΔ₃1)).trans ?_
      calc _ ≤ outerLpNorm (sizeP 2) p' (fun T => martDiff T g₂) * 1 := mul_le_mul' le_rfl hΔ₃1
        _ = _ := mul_one _
    have h23fin : outerLpNorm (sizeP 1) p' ((fun T => martDiff T g₂) * fun T => martDiff T f₃) ≠ ⊤
      :=
      ne_top_of_le_ne_top hΔ₂fin h23
    refine (outerL1Norm_mul_le (sizeP 1) sizeInf (sizeP 1) hSinf hS₁ sizeP_one_mul_le_sizeInf
      hp hp' hpp' _ _ hE₁fin h23fin).trans ?_
    rw [hK]
    exact mul_le_mul' le_rfl (mul_le_mul' hE₁ (h23.trans hΔ₂))
  have hC : outerLpNorm (sizeP 1) 1 Cf ≤ K := by
    have h13 : outerLpNorm (sizeP 1) p ((fun T => martDiff T g₁) * fun T => martDiff T f₃) ≤
        outerLpNorm (sizeP 2) p (fun T => martDiff T g₁) := by
      refine (outerLpNorm_mul_le_Linf (sizeP 1) (sizeP 2) (sizeP 2) hS₂ hS₂
        sizeP_one_mul_le_sizeP_two (by linarith) _ _
        (ne_top_of_le_ne_top ENNReal.one_ne_top hΔ₃1)).trans ?_
      calc _ ≤ outerLpNorm (sizeP 2) p (fun T => martDiff T g₁) * 1 := mul_le_mul' le_rfl hΔ₃1
        _ = _ := mul_one _
    have h13fin : outerLpNorm (sizeP 1) p ((fun T => martDiff T g₁) * fun T => martDiff T f₃) ≠ ⊤ :=
      ne_top_of_le_ne_top hΔ₁fin h13
    refine (outerL1Norm_mul_le (sizeP 1) sizeInf (sizeP 1) hSinf hS₁ sizeP_one_mul_le_sizeInf
      hp' hp hpp'' _ _ hE₂fin h13fin).trans ?_
    calc 2 * (outerLpNorm sizeInf p' (fun T => martAvg T g₂) *
          outerLpNorm (sizeP 1) p ((fun T => martDiff T g₁) * fun T => martDiff T f₃))
        ≤ 2 * (ENNReal.ofReal Cp' * N₂ * (ENNReal.ofReal Cp * N₁)) := by
          gcongr
          exact h13.trans hΔ₁
      _ = K := by rw [hK]; ring
  have hD : outerLpNorm (sizeP 1) 1 D ≤ K := by
    have hsq : outerLinfNorm (sizeP 1) (fun T => martDiff T f₃ ^ 2) ≤ 1 := by
      refine iSup_le fun T => ?_
      rw [sizeP_one_sq]
      exact pow_le_one₀ zero_le ((le_iSup (fun T => sizeP 2 (fun T => martDiff T f₃) T) T).trans
        hΔ₃1)
    have h23 : outerLpNorm (sizeP 1) p' ((fun T => martAvg T g₂) * fun T => martDiff T f₃ ^ 2) ≤
        outerLpNorm sizeInf p' (fun T => martAvg T g₂) := by
      refine (outerLpNorm_mul_le_Linf (sizeP 1) sizeInf (sizeP 1) hSinf hS₁
        sizeP_one_mul_le_sizeInf (by linarith) _ _
        (ne_top_of_le_ne_top ENNReal.one_ne_top hsq)).trans ?_
      calc _ ≤ outerLpNorm sizeInf p' (fun T => martAvg T g₂) * 1 := mul_le_mul' le_rfl hsq
        _ = _ := mul_one _
    have h23fin : outerLpNorm (sizeP 1) p' ((fun T => martAvg T g₂) * fun T => martDiff T f₃ ^ 2) ≠
      ⊤ :=
      ne_top_of_le_ne_top hE₂fin h23
    refine (outerL1Norm_mul_le (sizeP 1) sizeInf (sizeP 1) hSinf hS₁ sizeP_one_mul_le_sizeInf
      hp hp' hpp' _ _ hE₁fin h23fin).trans ?_
    rw [hK]
    exact mul_le_mul' le_rfl (mul_le_mul' hE₁ (h23.trans hE₂))
  -- nonnegativity of the four terms
  have hA0 : ∀ T, 0 ≤ A T := fun T => mul_nonneg (martDiff_nonneg _ _) (martDiff_nonneg _ _)
  have hB0 : ∀ T, 0 ≤ B T := fun T =>
    mul_nonneg (martAvg_nonneg _ _) (mul_nonneg (martDiff_nonneg _ _) (martDiff_nonneg _ _))
  have hC0 : ∀ T, 0 ≤ Cf T := fun T =>
    mul_nonneg (martAvg_nonneg _ _) (mul_nonneg (martDiff_nonneg _ _) (martDiff_nonneg _ _))
  have hD0 : ∀ T, 0 ≤ D T := fun T =>
    mul_nonneg (martAvg_nonneg _ _) (mul_nonneg (martAvg_nonneg _ _) (sq_nonneg _))
  have hnn : ∀ x : ℝ, ENNReal.ofReal x ≤ ‖x‖ₑ := fun x => by
    rw [Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_ofReal (le_abs_self x)
  -- the pointwise bound on `α`
  have hpt : ∀ T : R.tree, ‖α T‖ₑ ≤ ENNReal.ofReal C₀ *
      ((‖A T‖ₑ + ‖B T‖ₑ + ‖Cf T‖ₑ + ‖D T‖ₑ) * ENNReal.ofReal (T : DyadicCube d).vol) := by
    intro T
    have hT : (T : DyadicCube d).toSet ⊆ R.toSet := DyadicCube.mem_tree.mp T.2
    have h : |α T| ≤ C₀ * (A T + B T + Cf T + D T) * (T : DyadicCube d).vol := by
      have h0 := hα T T.2
      rw [← martDiff_truncate_of_subset hT f₁, ← martDiff_truncate_of_subset hT f₂,
        ← martAvg_truncate_of_subset hT f₁, ← martAvg_truncate_of_subset hT f₂] at h0
      simp only [hAdef, hBdef, hCdef, hDdef, Pi.mul_apply]
      linarith [h0]
    have hsum0 : 0 ≤ A T + B T + Cf T + D T := by
      have := hA0 T; have := hB0 T; have := hC0 T; have := hD0 T
      linarith
    calc ‖α T‖ₑ = ENNReal.ofReal |α T| := Real.enorm_eq_ofReal_abs _
      _ ≤ ENNReal.ofReal (C₀ * (A T + B T + Cf T + D T) * (T : DyadicCube d).vol) :=
          ENNReal.ofReal_le_ofReal h
      _ = ENNReal.ofReal C₀ *
          (ENNReal.ofReal (A T + B T + Cf T + D T) * ENNReal.ofReal (T : DyadicCube d).vol) := by
          rw [ENNReal.ofReal_mul (mul_nonneg hC₀ hsum0), ENNReal.ofReal_mul hC₀, mul_assoc]
      _ ≤ _ := by
          gcongr
          calc ENNReal.ofReal (A T + B T + Cf T + D T)
              = ENNReal.ofReal (A T) + ENNReal.ofReal (B T) + ENNReal.ofReal (Cf T) +
                  ENNReal.ofReal (D T) := by
                rw [ENNReal.ofReal_add (by linarith [hA0 T, hB0 T, hC0 T]) (hD0 T),
                  ENNReal.ofReal_add (by linarith [hA0 T, hB0 T]) (hC0 T),
                  ENNReal.ofReal_add (hA0 T) (hB0 T)]
            _ ≤ ‖A T‖ₑ + ‖B T‖ₑ + ‖Cf T‖ₑ + ‖D T‖ₑ :=
                add_le_add (add_le_add (add_le_add (hnn _) (hnn _)) (hnn _)) (hnn _)
  -- summation
  calc ∑' T : R.tree, ‖α T‖ₑ
      ≤ ∑' T : R.tree, ENNReal.ofReal C₀ *
          ((‖A T‖ₑ + ‖B T‖ₑ + ‖Cf T‖ₑ + ‖D T‖ₑ) * ENNReal.ofReal (T : DyadicCube d).vol) :=
        ENNReal.tsum_le_tsum hpt
    _ ≤ ∑' T : DyadicCube d, ENNReal.ofReal C₀ *
          ((‖A T‖ₑ + ‖B T‖ₑ + ‖Cf T‖ₑ + ‖D T‖ₑ) * ENNReal.ofReal T.vol) :=
        ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective
          (fun T : DyadicCube d => ENNReal.ofReal C₀ *
            ((‖A T‖ₑ + ‖B T‖ₑ + ‖Cf T‖ₑ + ‖D T‖ₑ) * ENNReal.ofReal T.vol))
    _ = ENNReal.ofReal C₀ * (∑' T : DyadicCube d, ‖A T‖ₑ * ENNReal.ofReal T.vol +
          ∑' T : DyadicCube d, ‖B T‖ₑ * ENNReal.ofReal T.vol +
          ∑' T : DyadicCube d, ‖Cf T‖ₑ * ENNReal.ofReal T.vol +
          ∑' T : DyadicCube d, ‖D T‖ₑ * ENNReal.ofReal T.vol) := by
        rw [ENNReal.tsum_mul_left]
        congr 1
        simp only [add_mul]
        rw [ENNReal.tsum_add, ENNReal.tsum_add, ENNReal.tsum_add]
    _ ≤ ENNReal.ofReal C₀ * (4 * outerLpNorm (sizeP 1) 1 A + 4 * outerLpNorm (sizeP 1) 1 B +
          4 * outerLpNorm (sizeP 1) 1 Cf + 4 * outerLpNorm (sizeP 1) 1 D) := by
        gcongr <;> exact tsum_enorm_mul_vol_le _
    _ ≤ ENNReal.ofReal C₀ * (4 * K + 4 * K + 4 * K + 4 * K) := by gcongr
    _ = ENNReal.ofReal (32 * Cp * Cp' * C₀) * (N₁ * N₂) := by
        rw [hK, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
        ring

end Lemma271Proof

/-! ### Lemma 2.72 -/

section Lemma272Proof

variable {d : ℕ}

/-- The exponents of Lemma 2.72: with `s = pq/(p+q)` one has `1/p + 1/q = 1/s`, `1 < s`
(precisely when `1/p + 1/q < 1`), and the dual exponent `r = (pq/(p+q))' = s/(s-1)` satisfies
`1 < r` and `1/s + 1/r = 1`. [PROVED] -/
theorem holder_exponents {p q s : ℝ} (hp : 1 < p) (hq : 1 < q) (hpq : 1 / p + 1 / q < 1)
    (hs : s = p * q / (p + q)) :
    0 < s ∧ 1 < s ∧ 1 / p + 1 / q = 1 / s ∧ 1 < s / (s - 1) ∧
      1 / s + 1 / (s / (s - 1)) = 1 := by
  have hp0 : 0 < p := by linarith
  have hq0 : 0 < q := by linarith
  have hs0 : 0 < s := by rw [hs]; positivity
  have hinv : 1 / p + 1 / q = 1 / s := by
    rw [hs, div_add_div _ _ hp0.ne' hq0.ne', one_div_div]
    ring
  have hs1 : 1 < s := by
    rw [hinv] at hpq
    exact (div_lt_one hs0).mp hpq
  have hs1' : 0 < s - 1 := by linarith
  refine ⟨hs0, hs1, hinv, (one_lt_div hs1').mpr (by linarith), ?_⟩
  rw [one_div_div, ← add_div, show (1 : ℝ) + (s - 1) = s by ring]
  exact div_self hs0.ne'

/-- `S₁(FG) ≤ S₁(F) S_∞(G)`. [PROVED] -/
theorem sizeP_one_mul_le_sizeInf' (F G : DyadicCube d → ℝ) (T : DyadicCube d) :
    sizeP 1 (F * G) T ≤ sizeP 1 F T * sizeInf G T := by
  rw [mul_comm F G, mul_comm (sizeP 1 F T)]
  exact sizeP_one_mul_le_sizeInf G F T

/-- `‖FG‖_{L^∞(S₁)} ≤ ‖F‖_{L^∞(S₂)} ‖G‖_{L^∞(S₂)}`. [PROVED] -/
theorem outerLinfNorm_sizeP_one_mul_le (F G : DyadicCube d → ℝ) :
    outerLinfNorm (sizeP 1) (F * G) ≤
      outerLinfNorm (sizeP 2) F * outerLinfNorm (sizeP 2) G :=
  iSup_le fun T => (sizeP_one_mul_le_sizeP_two F G T).trans
    (mul_le_mul' (le_iSup (fun T => sizeP 2 F T) T) (le_iSup (fun T => sizeP 2 G T) T))

/-- **Lemma 2.72** (with the integrability hypotheses of the paper made explicit, and the
`L^∞` hypotheses stated for the essential supremum): if `1 < p, q`, `1/p + 1/q < 1` (so that
the exponent `(pq/(p+q))'` of the paper is a finite exponent `> 1`), `f₁ ∈ L^p`, `f₂ ∈ L^q`,
`f₃ ∈ L^{(pq/(p+q))'}`, `‖f₄‖_∞, ‖f₅‖_∞ ≤ 1`, and
`|α_T| ≤ C₀ (Δ_T f₂ Δ_T f₁ + E_T f₁ Δ_T f₂ Δ_T f₅ + E_T f₂ Δ_T f₄ Δ_T f₁
  + E_T f₂ E_T f₁ Δ_T f₄ Δ_T f₅) E_T f₃ |T|` for every dyadic `T ⊆ R`, then
`∑_{T ⊆ R} |α_T| ≤ C C₀ ‖f₁ 𝟙_R‖_p ‖f₂ 𝟙_R‖_q ‖f₃ 𝟙_R‖_{(pq/(p+q))'}`. Proved below as
`lemma272`. [PROVED] -/
def Lemma272 (d : ℕ) (p q : ℝ) : Prop :=
  1 < p → 1 < q → 1 / p + 1 / q < 1 → ∃ C : ℝ, 0 ≤ C ∧
    ∀ (C₀ : ℝ) (R : DyadicCube d) (f₁ f₂ f₃ f₄ f₅ : (Fin d → ℝ) → ℝ) (α : DyadicCube d → ℝ),
      0 ≤ C₀ → MemLp f₁ (ENNReal.ofReal p) volume → MemLp f₂ (ENNReal.ofReal q) volume →
      MemLp f₃ (ENNReal.ofReal ((p * q / (p + q)) / (p * q / (p + q) - 1))) volume →
      MemLp f₄ ⊤ volume → eLpNorm f₄ ⊤ volume ≤ 1 →
      MemLp f₅ ⊤ volume → eLpNorm f₅ ⊤ volume ≤ 1 →
      (∀ T ∈ R.tree, |α T| ≤ C₀ * (martDiff T f₂ * martDiff T f₁
        + martAvg T f₁ * martDiff T f₂ * martDiff T f₅
        + martAvg T f₂ * martDiff T f₄ * martDiff T f₁
        + martAvg T f₂ * martAvg T f₁ * martDiff T f₄ * martDiff T f₅) * martAvg T f₃ * T.vol) →
      ∑' T : R.tree, ‖α T‖ₑ ≤ ENNReal.ofReal (C * C₀) *
        (eLpNorm (truncate R f₁) (ENNReal.ofReal p) volume *
          eLpNorm (truncate R f₂) (ENNReal.ofReal q) volume *
          eLpNorm (truncate R f₃)
            (ENNReal.ofReal ((p * q / (p + q)) / (p * q / (p + q) - 1))) volume)

/-- An outer Hölder product bound with a third factor of unit outer L∞ norm. -/
private theorem outerLpNorm_three_factor_le (S₂ S₃ : Size d)
    (hS₂ : ∀ F G : DyadicCube d → ℝ, ∀ T, (∀ Q, ‖F Q‖ₑ ≤ ‖G Q‖ₑ) → S₂ F T ≤ S₂ G T)
    (hS₃ : ∀ F G : DyadicCube d → ℝ, ∀ T, (∀ Q, ‖F Q‖ₑ ≤ ‖G Q‖ₑ) → S₃ F T ≤ S₃ G T)
    (hmul : ∀ F G T, sizeP 1 (F * G) T ≤ S₂ F T * S₃ G T)
    {p q s : ℝ} (hp : 0 < p) (hq : 0 < q) (hs : 0 < s)
    (hpqs : 1 / p + 1 / q = 1 / s) (F G H : DyadicCube d → ℝ)
    (hF : outerLpNorm sizeInf p F ≠ ⊤) (hG : outerLpNorm S₂ q G ≠ ⊤)
    (hH : outerLinfNorm S₃ H ≤ 1) :
    outerLpNorm (sizeP 1) s (F * (G * H)) ≤
      (2 : ENNReal) ^ (1 / s) * (outerLpNorm sizeInf p F * outerLpNorm S₂ q G) := by
  have hS₁ : ∀ F G : DyadicCube d → ℝ, ∀ T,
      (∀ Q, ‖F Q‖ₑ ≤ ‖G Q‖ₑ) → sizeP 1 F T ≤ sizeP 1 G T :=
    fun F G T h => sizeP_mono (by norm_num) h T
  have hSinf : ∀ F G : DyadicCube d → ℝ, ∀ T,
      (∀ Q, ‖F Q‖ₑ ≤ ‖G Q‖ₑ) → sizeInf F T ≤ sizeInf G T :=
    fun F G T h => sizeInf_mono h T
  have hGH : outerLpNorm (sizeP 1) q (G * H) ≤ outerLpNorm S₂ q G := by
    refine (outerLpNorm_mul_le_Linf (sizeP 1) S₂ S₃ hS₂ hS₃ hmul hq G H
      (ne_top_of_le_ne_top ENNReal.one_ne_top hH)).trans ?_
    calc _ ≤ outerLpNorm S₂ q G * 1 := mul_le_mul' le_rfl hH
      _ = _ := mul_one _
  refine (outerLpNorm_mul_le (sizeP 1) sizeInf (sizeP 1) hSinf hS₁
    sizeP_one_mul_le_sizeInf hp hq hs hpqs F (G * H) hF
    (ne_top_of_le_ne_top hG hGH)).trans ?_
  exact mul_le_mul' le_rfl (mul_le_mul' le_rfl hGH)

/-- Convert a real four-term bound to the corresponding weighted enorm bound. -/
private theorem enorm_le_four_term_bound {a a₁ a₂ a₃ a₄ C v : ℝ}
    (hC : 0 ≤ C) (h₁ : 0 ≤ a₁) (h₂ : 0 ≤ a₂) (h₃ : 0 ≤ a₃) (h₄ : 0 ≤ a₄)
    (h : |a| ≤ C * (a₁ + a₂ + a₃ + a₄) * v) :
    ‖a‖ₑ ≤ ENNReal.ofReal C *
      ((‖a₁‖ₑ + ‖a₂‖ₑ + ‖a₃‖ₑ + ‖a₄‖ₑ) * ENNReal.ofReal v) := by
  have hsum : 0 ≤ a₁ + a₂ + a₃ + a₄ := add_nonneg (add_nonneg (add_nonneg h₁ h₂) h₃) h₄
  calc ‖a‖ₑ = ENNReal.ofReal |a| := Real.enorm_eq_ofReal_abs _
    _ ≤ ENNReal.ofReal (C * (a₁ + a₂ + a₃ + a₄) * v) := ENNReal.ofReal_le_ofReal h
    _ = _ := by
      simp only [Real.enorm_eq_ofReal_abs, abs_of_nonneg h₁, abs_of_nonneg h₂,
        abs_of_nonneg h₃, abs_of_nonneg h₄]
      rw [ENNReal.ofReal_mul (mul_nonneg hC hsum), ENNReal.ofReal_mul hC,
        ENNReal.ofReal_add (add_nonneg (add_nonneg h₁ h₂) h₃) h₄,
        ENNReal.ofReal_add (add_nonneg h₁ h₂) h₃, ENNReal.ofReal_add h₁ h₂, mul_assoc]

/-- **Lemma 2.72**, deduced from Theorem 2.68 (for the exponents `p`, `q` and
`r = (pq/(p+q))'`), Hölder's inequality for outer measure spaces (with target exponents
`s = pq/(p+q)` and `1`) and Proposition 3.6 of Do–Thiele. [PROVED] -/
theorem lemma272 (hd : d ≠ 0) (p q : ℝ) : Lemma272 d p q := by
  intro hp hq hpq
  set s : ℝ := p * q / (p + q) with hs_def
  set r : ℝ := s / (s - 1) with hr_def
  obtain ⟨hs0, hs1, hpqs, hr1, hsr⟩ := holder_exponents hp hq hpq hs_def
  rw [← hr_def] at hr1 hsr
  have hp0 : 0 < p := by linarith
  have hq0 : 0 < q := by linarith
  have hqps : 1 / q + 1 / p = 1 / s := by rw [add_comm]; exact hpqs
  have h2s : (2 : ENNReal) ^ (1 / s) ≤ 2 := by
    calc (2 : ENNReal) ^ (1 / s) ≤ (2 : ENNReal) ^ (1 : ℝ) :=
          ENNReal.rpow_le_rpow_of_exponent_le one_le_two ((div_le_one hs0).mpr hs1.le)
      _ = 2 := ENNReal.rpow_one 2
  obtain ⟨Cp, hCp0, hCp⟩ := carlesonEmbedding hd p hp
  obtain ⟨Cq, hCq0, hCq⟩ := carlesonEmbedding hd q hq
  obtain ⟨Cr, hCr0, hCr⟩ := carlesonEmbedding hd r hr1
  refine ⟨64 * Cp * Cq * Cr, by positivity, ?_⟩
  intro C₀ R f₁ f₂ f₃ f₄ f₅ α hC₀ hf₁ hf₂ hf₃ hf₄ hf₄1 hf₅ hf₅1 hα
  -- the truncated functions and their outer norms
  set g₁ := truncate R f₁ with hg₁
  set g₂ := truncate R f₂ with hg₂
  set g₃ := truncate R f₃ with hg₃
  have hg₁L : MemLp g₁ (ENNReal.ofReal p) volume :=
    hf₁.indicator R.measurableSet_toSet.nullMeasurableSet
  have hg₂L : MemLp g₂ (ENNReal.ofReal q) volume :=
    hf₂.indicator R.measurableSet_toSet.nullMeasurableSet
  have hg₃L : MemLp g₃ (ENNReal.ofReal r) volume :=
    hf₃.indicator R.measurableSet_toSet.nullMeasurableSet
  obtain ⟨hE₁, hΔ₁⟩ := hCp g₁ hg₁L
  obtain ⟨hE₂, hΔ₂⟩ := hCq g₂ hg₂L
  obtain ⟨hE₃, -⟩ := hCr g₃ hg₃L
  have hΔ₄1 : outerLinfNorm (sizeP 2) (fun T => martDiff T f₄) ≤ 1 :=
    (outerLinfNorm_martDiff_le hd hf₄).trans hf₄1
  have hΔ₅1 : outerLinfNorm (sizeP 2) (fun T => martDiff T f₅) ≤ 1 :=
    (outerLinfNorm_martDiff_le hd hf₅).trans hf₅1
  set N₁ := eLpNorm g₁ (ENNReal.ofReal p) volume with hN₁def
  set N₂ := eLpNorm g₂ (ENNReal.ofReal q) volume with hN₂def
  set N₃ := eLpNorm g₃ (ENNReal.ofReal r) volume with hN₃def
  have hN₁ : N₁ ≠ ⊤ := hg₁L.eLpNorm_ne_top
  have hN₂ : N₂ ≠ ⊤ := hg₂L.eLpNorm_ne_top
  have hN₃ : N₃ ≠ ⊤ := hg₃L.eLpNorm_ne_top
  have hE₁fin : outerLpNorm sizeInf p (fun T => martAvg T g₁) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hN₁) hE₁
  have hΔ₁fin : outerLpNorm (sizeP 2) p (fun T => martDiff T g₁) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hN₁) hΔ₁
  have hE₂fin : outerLpNorm sizeInf q (fun T => martAvg T g₂) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hN₂) hE₂
  have hΔ₂fin : outerLpNorm (sizeP 2) q (fun T => martDiff T g₂) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hN₂) hΔ₂
  have hE₃fin : outerLpNorm sizeInf r (fun T => martAvg T g₃) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hN₃) hE₃
  -- monotonicity of the sizes
  have hS₂ : ∀ F G : DyadicCube d → ℝ, ∀ T, (∀ Q, ‖F Q‖ₑ ≤ ‖G Q‖ₑ) → sizeP 2 F T ≤ sizeP 2 G T :=
    fun F G T h => sizeP_mono (by norm_num) h T
  have hS₁ : ∀ F G : DyadicCube d → ℝ, ∀ T, (∀ Q, ‖F Q‖ₑ ≤ ‖G Q‖ₑ) → sizeP 1 F T ≤ sizeP 1 G T :=
    fun F G T h => sizeP_mono (by norm_num) h T
  have hSinf : ∀ F G : DyadicCube d → ℝ, ∀ T, (∀ Q, ‖F Q‖ₑ ≤ ‖G Q‖ₑ) → sizeInf F T ≤ sizeInf G T :=
    fun F G T h => sizeInf_mono h T
  -- the four `L^s(S₁)` terms
  set M : ENNReal := ENNReal.ofReal Cp * N₁ * (ENNReal.ofReal Cq * N₂) with hM
  set K : ENNReal := (2 : ENNReal) ^ (1 / s) * M with hK
  have hK_ne : K ≠ ⊤ := by
    rw [hK, hM]
    exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofNat_ne_top)
      (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hN₁)
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hN₂))
  set A : DyadicCube d → ℝ := ((fun T => martDiff T g₂) * fun T => martDiff T g₁) with hAdef
  set B : DyadicCube d → ℝ :=
    ((fun T => martAvg T g₁) * ((fun T => martDiff T g₂) * fun T => martDiff T f₅)) with hBdef
  set Cf : DyadicCube d → ℝ :=
    ((fun T => martAvg T g₂) * ((fun T => martDiff T g₁) * fun T => martDiff T f₄)) with hCdef
  set D : DyadicCube d → ℝ :=
    ((fun T => martAvg T g₂) * ((fun T => martAvg T g₁) *
      ((fun T => martDiff T f₄) * fun T => martDiff T f₅))) with hDdef
  have hA : outerLpNorm (sizeP 1) s A ≤ K := by
    refine (outerLpNorm_mul_le (sizeP 1) (sizeP 2) (sizeP 2) hS₂ hS₂ sizeP_one_mul_le_sizeP_two
      hq0 hp0 hs0 hqps _ _ hΔ₂fin hΔ₁fin).trans ?_
    rw [hK, hM]
    calc _ ≤ (2 : ENNReal) ^ (1 / s) * (ENNReal.ofReal Cq * N₂ * (ENNReal.ofReal Cp * N₁)) :=
          mul_le_mul' le_rfl (mul_le_mul' hΔ₂ hΔ₁)
      _ = _ := by ring
  have hB : outerLpNorm (sizeP 1) s B ≤ K := by
    refine (outerLpNorm_three_factor_le (sizeP 2) (sizeP 2) hS₂ hS₂
      sizeP_one_mul_le_sizeP_two hp0 hq0 hs0 hpqs
      (fun T => martAvg T g₁) (fun T => martDiff T g₂) (fun T => martDiff T f₅)
      hE₁fin hΔ₂fin hΔ₅1).trans ?_
    rw [hK, hM]
    exact mul_le_mul' le_rfl (mul_le_mul' hE₁ hΔ₂)
  have hC : outerLpNorm (sizeP 1) s Cf ≤ K := by
    refine (outerLpNorm_three_factor_le (sizeP 2) (sizeP 2) hS₂ hS₂
      sizeP_one_mul_le_sizeP_two hq0 hp0 hs0 hqps
      (fun T => martAvg T g₂) (fun T => martDiff T g₁) (fun T => martDiff T f₄)
      hE₂fin hΔ₁fin hΔ₄1).trans ?_
    rw [hK, hM]
    calc _ ≤ (2 : ENNReal) ^ (1 / s) * (ENNReal.ofReal Cq * N₂ * (ENNReal.ofReal Cp * N₁)) :=
          mul_le_mul' le_rfl (mul_le_mul' hE₂ hΔ₁)
      _ = _ := by ring
  have hD : outerLpNorm (sizeP 1) s D ≤ K := by
    have h45 : outerLinfNorm (sizeP 1) ((fun T => martDiff T f₄) * fun T => martDiff T f₅) ≤ 1 := by
      refine (outerLinfNorm_sizeP_one_mul_le _ _).trans ?_
      calc _ ≤ (1 : ENNReal) * 1 := mul_le_mul' hΔ₄1 hΔ₅1
        _ = 1 := mul_one 1
    refine (outerLpNorm_three_factor_le sizeInf (sizeP 1) hSinf hS₁
      sizeP_one_mul_le_sizeInf hq0 hp0 hs0 hqps
      (fun T => martAvg T g₂) (fun T => martAvg T g₁)
      ((fun T => martDiff T f₄) * fun T => martDiff T f₅) hE₂fin hE₁fin h45).trans ?_
    rw [hK, hM]
    calc _ ≤ (2 : ENNReal) ^ (1 / s) * (ENNReal.ofReal Cq * N₂ * (ENNReal.ofReal Cp * N₁)) :=
          mul_le_mul' le_rfl (mul_le_mul' hE₂ hE₁)
      _ = _ := by ring
  -- multiplication by `E(g₃)` and Hölder with exponents `s`, `r`
  set G₃ : DyadicCube d → ℝ := fun T => martAvg T g₃ with hG₃def
  set L : ENNReal := 2 * (K * (ENNReal.ofReal Cr * N₃)) with hL
  have hmul : ∀ X : DyadicCube d → ℝ, outerLpNorm (sizeP 1) s X ≤ K →
      outerLpNorm (sizeP 1) 1 (X * G₃) ≤ L := by
    intro X hX
    refine (outerL1Norm_mul_le (sizeP 1) (sizeP 1) sizeInf hS₁ hSinf sizeP_one_mul_le_sizeInf'
      hs1 hr1 hsr _ _ (ne_top_of_le_ne_top hK_ne hX) hE₃fin).trans ?_
    rw [hL]
    exact mul_le_mul' le_rfl (mul_le_mul' hX hE₃)
  have hA' := hmul A hA
  have hB' := hmul B hB
  have hC' := hmul Cf hC
  have hD' := hmul D hD
  -- nonnegativity of the four terms
  have hA0 : ∀ T, 0 ≤ (A * G₃) T := fun T =>
    mul_nonneg (mul_nonneg (martDiff_nonneg _ _) (martDiff_nonneg _ _)) (martAvg_nonneg _ _)
  have hB0 : ∀ T, 0 ≤ (B * G₃) T := fun T =>
    mul_nonneg (mul_nonneg (martAvg_nonneg _ _)
      (mul_nonneg (martDiff_nonneg _ _) (martDiff_nonneg _ _))) (martAvg_nonneg _ _)
  have hC0 : ∀ T, 0 ≤ (Cf * G₃) T := fun T =>
    mul_nonneg (mul_nonneg (martAvg_nonneg _ _)
      (mul_nonneg (martDiff_nonneg _ _) (martDiff_nonneg _ _))) (martAvg_nonneg _ _)
  have hD0 : ∀ T, 0 ≤ (D * G₃) T := fun T =>
    mul_nonneg (mul_nonneg (martAvg_nonneg _ _) (mul_nonneg (martAvg_nonneg _ _)
      (mul_nonneg (martDiff_nonneg _ _) (martDiff_nonneg _ _)))) (martAvg_nonneg _ _)
  -- the pointwise bound on `α`
  have hpt : ∀ T : R.tree, ‖α T‖ₑ ≤ ENNReal.ofReal C₀ *
      ((‖(A * G₃) T‖ₑ + ‖(B * G₃) T‖ₑ + ‖(Cf * G₃) T‖ₑ + ‖(D * G₃) T‖ₑ) *
        ENNReal.ofReal (T : DyadicCube d).vol) := by
    intro T
    have hT : (T : DyadicCube d).toSet ⊆ R.toSet := DyadicCube.mem_tree.mp T.2
    have h : |α T| ≤ C₀ * ((A * G₃) T + (B * G₃) T + (Cf * G₃) T + (D * G₃) T) *
        (T : DyadicCube d).vol := by
      have h0 := hα T T.2
      rw [← martDiff_truncate_of_subset hT f₁, ← martDiff_truncate_of_subset hT f₂,
        ← martAvg_truncate_of_subset hT f₁, ← martAvg_truncate_of_subset hT f₂,
        ← martAvg_truncate_of_subset hT f₃] at h0
      refine h0.trans_eq ?_
      simp only [hAdef, hBdef, hCdef, hDdef, hG₃def, Pi.mul_apply]
      ring
    exact enorm_le_four_term_bound hC₀ (hA0 T) (hB0 T) (hC0 T) (hD0 T) h
  -- summation
  calc ∑' T : R.tree, ‖α T‖ₑ
      ≤ ∑' T : R.tree, ENNReal.ofReal C₀ *
          ((‖(A * G₃) T‖ₑ + ‖(B * G₃) T‖ₑ + ‖(Cf * G₃) T‖ₑ + ‖(D * G₃) T‖ₑ) *
            ENNReal.ofReal (T : DyadicCube d).vol) :=
        ENNReal.tsum_le_tsum hpt
    _ ≤ ∑' T : DyadicCube d, ENNReal.ofReal C₀ *
          ((‖(A * G₃) T‖ₑ + ‖(B * G₃) T‖ₑ + ‖(Cf * G₃) T‖ₑ + ‖(D * G₃) T‖ₑ) *
            ENNReal.ofReal T.vol) :=
        ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective
          (fun T : DyadicCube d => ENNReal.ofReal C₀ *
            ((‖(A * G₃) T‖ₑ + ‖(B * G₃) T‖ₑ + ‖(Cf * G₃) T‖ₑ + ‖(D * G₃) T‖ₑ) *
              ENNReal.ofReal T.vol))
    _ = ENNReal.ofReal C₀ * (∑' T : DyadicCube d, ‖(A * G₃) T‖ₑ * ENNReal.ofReal T.vol +
          ∑' T : DyadicCube d, ‖(B * G₃) T‖ₑ * ENNReal.ofReal T.vol +
          ∑' T : DyadicCube d, ‖(Cf * G₃) T‖ₑ * ENNReal.ofReal T.vol +
          ∑' T : DyadicCube d, ‖(D * G₃) T‖ₑ * ENNReal.ofReal T.vol) := by
        rw [ENNReal.tsum_mul_left]
        congr 1
        simp only [add_mul]
        rw [ENNReal.tsum_add, ENNReal.tsum_add, ENNReal.tsum_add]
    _ ≤ ENNReal.ofReal C₀ * (4 * outerLpNorm (sizeP 1) 1 (A * G₃) +
          4 * outerLpNorm (sizeP 1) 1 (B * G₃) + 4 * outerLpNorm (sizeP 1) 1 (Cf * G₃) +
          4 * outerLpNorm (sizeP 1) 1 (D * G₃)) := by
        gcongr <;> exact tsum_enorm_mul_vol_le _
    _ ≤ ENNReal.ofReal C₀ * (4 * L + 4 * L + 4 * L + 4 * L) := by gcongr
    _ = ENNReal.ofReal C₀ * (32 * ((2 : ENNReal) ^ (1 / s) *
          (ENNReal.ofReal Cp * N₁ * (ENNReal.ofReal Cq * N₂) * (ENNReal.ofReal Cr * N₃)))) := by
        rw [hL, hK, hM]
        ring
    _ ≤ ENNReal.ofReal C₀ * (32 * (2 *
          (ENNReal.ofReal Cp * N₁ * (ENNReal.ofReal Cq * N₂) * (ENNReal.ofReal Cr * N₃)))) :=
        mul_le_mul' le_rfl (mul_le_mul' le_rfl (mul_le_mul' h2s le_rfl))
    _ = ENNReal.ofReal (64 * Cp * Cq * Cr * C₀) * (N₁ * N₂ * N₃) := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num),
          ENNReal.ofReal_ofNat]
        ring

/-- **Lemma 2.72 in the endpoint case `1/p + 1/q = 1`** (the case `n = 2` of (2.60), where there
is no third entry): without the factor `E_T f₃`, if `f₁ ∈ L^p`, `f₂ ∈ L^q`, `‖f₄‖_∞, ‖f₅‖_∞ ≤ 1`
and `|α_T| ≤ C₀ (Δ_T f₂ Δ_T f₁ + E_T f₁ Δ_T f₂ Δ_T f₅ + E_T f₂ Δ_T f₄ Δ_T f₁
  + E_T f₂ E_T f₁ Δ_T f₄ Δ_T f₅) |T|` for every dyadic `T ⊆ R`, then
`∑_{T ⊆ R} |α_T| ≤ C C₀ ‖f₁ 𝟙_R‖_p ‖f₂ 𝟙_R‖_q`. Proved below as `lemma272one`. [PROVED] -/
def Lemma272one (d : ℕ) (p q : ℝ) : Prop :=
  1 < p → 1 < q → 1 / p + 1 / q = 1 → ∃ C : ℝ, 0 ≤ C ∧
    ∀ (C₀ : ℝ) (R : DyadicCube d) (f₁ f₂ f₄ f₅ : (Fin d → ℝ) → ℝ) (α : DyadicCube d → ℝ),
      0 ≤ C₀ → MemLp f₁ (ENNReal.ofReal p) volume → MemLp f₂ (ENNReal.ofReal q) volume →
      MemLp f₄ ⊤ volume → eLpNorm f₄ ⊤ volume ≤ 1 →
      MemLp f₅ ⊤ volume → eLpNorm f₅ ⊤ volume ≤ 1 →
      (∀ T ∈ R.tree, |α T| ≤ C₀ * (martDiff T f₂ * martDiff T f₁
        + martAvg T f₁ * martDiff T f₂ * martDiff T f₅
        + martAvg T f₂ * martDiff T f₄ * martDiff T f₁
        + martAvg T f₂ * martAvg T f₁ * martDiff T f₄ * martDiff T f₅) * T.vol) →
      ∑' T : R.tree, ‖α T‖ₑ ≤ ENNReal.ofReal (C * C₀) *
        (eLpNorm (truncate R f₁) (ENNReal.ofReal p) volume *
          eLpNorm (truncate R f₂) (ENNReal.ofReal q) volume)

/-- **Lemma 2.72 in the endpoint case**, deduced from Theorem 2.68 (for the exponents `p`, `q`),
Hölder's inequality for outer measure spaces with target exponent `s = 1` and Proposition 3.6 of
Do–Thiele; the constant is `32 C_p C_q`. [PROVED] -/
theorem lemma272one (hd : d ≠ 0) (p q : ℝ) : Lemma272one d p q := by
  intro hp hq hpq
  have hp0 : 0 < p := by linarith
  have hq0 : 0 < q := by linarith
  have hs0 : (0 : ℝ) < 1 := one_pos
  have hpqs : 1 / p + 1 / q = 1 / (1 : ℝ) := by rw [div_one]; exact hpq
  have hqps : 1 / q + 1 / p = 1 / (1 : ℝ) := by rw [add_comm]; exact hpqs
  have h2s : (2 : ENNReal) ^ (1 / (1 : ℝ)) = 2 := by rw [div_one, ENNReal.rpow_one]
  obtain ⟨Cp, hCp0, hCp⟩ := carlesonEmbedding hd p hp
  obtain ⟨Cq, hCq0, hCq⟩ := carlesonEmbedding hd q hq
  refine ⟨32 * Cp * Cq, by positivity, ?_⟩
  intro C₀ R f₁ f₂ f₄ f₅ α hC₀ hf₁ hf₂ hf₄ hf₄1 hf₅ hf₅1 hα
  -- the truncated functions and their outer norms
  set g₁ := truncate R f₁ with hg₁
  set g₂ := truncate R f₂ with hg₂
  have hg₁L : MemLp g₁ (ENNReal.ofReal p) volume :=
    hf₁.indicator R.measurableSet_toSet.nullMeasurableSet
  have hg₂L : MemLp g₂ (ENNReal.ofReal q) volume :=
    hf₂.indicator R.measurableSet_toSet.nullMeasurableSet
  obtain ⟨hE₁, hΔ₁⟩ := hCp g₁ hg₁L
  obtain ⟨hE₂, hΔ₂⟩ := hCq g₂ hg₂L
  have hΔ₄1 : outerLinfNorm (sizeP 2) (fun T => martDiff T f₄) ≤ 1 :=
    (outerLinfNorm_martDiff_le hd hf₄).trans hf₄1
  have hΔ₅1 : outerLinfNorm (sizeP 2) (fun T => martDiff T f₅) ≤ 1 :=
    (outerLinfNorm_martDiff_le hd hf₅).trans hf₅1
  set N₁ := eLpNorm g₁ (ENNReal.ofReal p) volume with hN₁def
  set N₂ := eLpNorm g₂ (ENNReal.ofReal q) volume with hN₂def
  have hN₁ : N₁ ≠ ⊤ := hg₁L.eLpNorm_ne_top
  have hN₂ : N₂ ≠ ⊤ := hg₂L.eLpNorm_ne_top
  have hE₁fin : outerLpNorm sizeInf p (fun T => martAvg T g₁) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hN₁) hE₁
  have hΔ₁fin : outerLpNorm (sizeP 2) p (fun T => martDiff T g₁) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hN₁) hΔ₁
  have hE₂fin : outerLpNorm sizeInf q (fun T => martAvg T g₂) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hN₂) hE₂
  have hΔ₂fin : outerLpNorm (sizeP 2) q (fun T => martDiff T g₂) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hN₂) hΔ₂
  -- monotonicity of the sizes
  have hS₂ : ∀ F G : DyadicCube d → ℝ, ∀ T, (∀ Q, ‖F Q‖ₑ ≤ ‖G Q‖ₑ) → sizeP 2 F T ≤ sizeP 2 G T :=
    fun F G T h => sizeP_mono (by norm_num) h T
  have hS₁ : ∀ F G : DyadicCube d → ℝ, ∀ T, (∀ Q, ‖F Q‖ₑ ≤ ‖G Q‖ₑ) → sizeP 1 F T ≤ sizeP 1 G T :=
    fun F G T h => sizeP_mono (by norm_num) h T
  have hSinf : ∀ F G : DyadicCube d → ℝ, ∀ T, (∀ Q, ‖F Q‖ₑ ≤ ‖G Q‖ₑ) → sizeInf F T ≤ sizeInf G T :=
    fun F G T h => sizeInf_mono h T
  -- the four `L¹(S₁)` terms
  set M : ENNReal := ENNReal.ofReal Cp * N₁ * (ENNReal.ofReal Cq * N₂) with hM
  set K : ENNReal := (2 : ENNReal) ^ (1 / (1 : ℝ)) * M with hK
  set A : DyadicCube d → ℝ := ((fun T => martDiff T g₂) * fun T => martDiff T g₁) with hAdef
  set B : DyadicCube d → ℝ :=
    ((fun T => martAvg T g₁) * ((fun T => martDiff T g₂) * fun T => martDiff T f₅)) with hBdef
  set Cf : DyadicCube d → ℝ :=
    ((fun T => martAvg T g₂) * ((fun T => martDiff T g₁) * fun T => martDiff T f₄)) with hCdef
  set D : DyadicCube d → ℝ :=
    ((fun T => martAvg T g₂) * ((fun T => martAvg T g₁) *
      ((fun T => martDiff T f₄) * fun T => martDiff T f₅))) with hDdef
  have hA : outerLpNorm (sizeP 1) 1 A ≤ K := by
    refine (outerLpNorm_mul_le (sizeP 1) (sizeP 2) (sizeP 2) hS₂ hS₂ sizeP_one_mul_le_sizeP_two
      hq0 hp0 hs0 hqps _ _ hΔ₂fin hΔ₁fin).trans ?_
    rw [hK, hM]
    calc _ ≤ (2 : ENNReal) ^ (1 / (1 : ℝ)) * (ENNReal.ofReal Cq * N₂ * (ENNReal.ofReal Cp * N₁)) :=
          mul_le_mul' le_rfl (mul_le_mul' hΔ₂ hΔ₁)
      _ = _ := by ring
  have hB : outerLpNorm (sizeP 1) 1 B ≤ K := by
    have h25 : outerLpNorm (sizeP 1) q ((fun T => martDiff T g₂) * fun T => martDiff T f₅) ≤
        outerLpNorm (sizeP 2) q (fun T => martDiff T g₂) := by
      refine (outerLpNorm_mul_le_Linf (sizeP 1) (sizeP 2) (sizeP 2) hS₂ hS₂
        sizeP_one_mul_le_sizeP_two hq0 _ _
        (ne_top_of_le_ne_top ENNReal.one_ne_top hΔ₅1)).trans ?_
      calc _ ≤ outerLpNorm (sizeP 2) q (fun T => martDiff T g₂) * 1 := mul_le_mul' le_rfl hΔ₅1
        _ = _ := mul_one _
    have h25fin : outerLpNorm (sizeP 1) q ((fun T => martDiff T g₂) * fun T => martDiff T f₅) ≠ ⊤ :=
      ne_top_of_le_ne_top hΔ₂fin h25
    refine (outerLpNorm_mul_le (sizeP 1) sizeInf (sizeP 1) hSinf hS₁ sizeP_one_mul_le_sizeInf
      hp0 hq0 hs0 hpqs _ _ hE₁fin h25fin).trans ?_
    rw [hK, hM]
    exact mul_le_mul' le_rfl (mul_le_mul' hE₁ (h25.trans hΔ₂))
  have hC : outerLpNorm (sizeP 1) 1 Cf ≤ K := by
    have h14 : outerLpNorm (sizeP 1) p ((fun T => martDiff T g₁) * fun T => martDiff T f₄) ≤
        outerLpNorm (sizeP 2) p (fun T => martDiff T g₁) := by
      refine (outerLpNorm_mul_le_Linf (sizeP 1) (sizeP 2) (sizeP 2) hS₂ hS₂
        sizeP_one_mul_le_sizeP_two hp0 _ _
        (ne_top_of_le_ne_top ENNReal.one_ne_top hΔ₄1)).trans ?_
      calc _ ≤ outerLpNorm (sizeP 2) p (fun T => martDiff T g₁) * 1 := mul_le_mul' le_rfl hΔ₄1
        _ = _ := mul_one _
    have h14fin : outerLpNorm (sizeP 1) p ((fun T => martDiff T g₁) * fun T => martDiff T f₄) ≠ ⊤ :=
      ne_top_of_le_ne_top hΔ₁fin h14
    refine (outerLpNorm_mul_le (sizeP 1) sizeInf (sizeP 1) hSinf hS₁ sizeP_one_mul_le_sizeInf
      hq0 hp0 hs0 hqps _ _ hE₂fin h14fin).trans ?_
    rw [hK, hM]
    calc _ ≤ (2 : ENNReal) ^ (1 / (1 : ℝ)) * (ENNReal.ofReal Cq * N₂ * (ENNReal.ofReal Cp * N₁)) :=
          mul_le_mul' le_rfl (mul_le_mul' hE₂ (h14.trans hΔ₁))
      _ = _ := by ring
  have hD : outerLpNorm (sizeP 1) 1 D ≤ K := by
    have h45 : outerLinfNorm (sizeP 1) ((fun T => martDiff T f₄) * fun T => martDiff T f₅) ≤ 1 := by
      refine (outerLinfNorm_sizeP_one_mul_le _ _).trans ?_
      calc _ ≤ (1 : ENNReal) * 1 := mul_le_mul' hΔ₄1 hΔ₅1
        _ = 1 := mul_one 1
    have h145 : outerLpNorm (sizeP 1) p ((fun T => martAvg T g₁) *
        ((fun T => martDiff T f₄) * fun T => martDiff T f₅)) ≤
        outerLpNorm sizeInf p (fun T => martAvg T g₁) := by
      refine (outerLpNorm_mul_le_Linf (sizeP 1) sizeInf (sizeP 1) hSinf hS₁
        sizeP_one_mul_le_sizeInf hp0 _ _ (ne_top_of_le_ne_top ENNReal.one_ne_top h45)).trans ?_
      calc _ ≤ outerLpNorm sizeInf p (fun T => martAvg T g₁) * 1 := mul_le_mul' le_rfl h45
        _ = _ := mul_one _
    have h145fin : outerLpNorm (sizeP 1) p ((fun T => martAvg T g₁) *
        ((fun T => martDiff T f₄) * fun T => martDiff T f₅)) ≠ ⊤ :=
      ne_top_of_le_ne_top hE₁fin h145
    refine (outerLpNorm_mul_le (sizeP 1) sizeInf (sizeP 1) hSinf hS₁ sizeP_one_mul_le_sizeInf
      hq0 hp0 hs0 hqps _ _ hE₂fin h145fin).trans ?_
    rw [hK, hM]
    calc _ ≤ (2 : ENNReal) ^ (1 / (1 : ℝ)) * (ENNReal.ofReal Cq * N₂ * (ENNReal.ofReal Cp * N₁)) :=
          mul_le_mul' le_rfl (mul_le_mul' hE₂ (h145.trans hE₁))
      _ = _ := by ring
  -- nonnegativity of the four terms
  have hA0 : ∀ T, 0 ≤ A T := fun T => mul_nonneg (martDiff_nonneg _ _) (martDiff_nonneg _ _)
  have hB0 : ∀ T, 0 ≤ B T := fun T =>
    mul_nonneg (martAvg_nonneg _ _) (mul_nonneg (martDiff_nonneg _ _) (martDiff_nonneg _ _))
  have hC0 : ∀ T, 0 ≤ Cf T := fun T =>
    mul_nonneg (martAvg_nonneg _ _) (mul_nonneg (martDiff_nonneg _ _) (martDiff_nonneg _ _))
  have hD0 : ∀ T, 0 ≤ D T := fun T =>
    mul_nonneg (martAvg_nonneg _ _) (mul_nonneg (martAvg_nonneg _ _)
      (mul_nonneg (martDiff_nonneg _ _) (martDiff_nonneg _ _)))
  have hnn : ∀ x : ℝ, ENNReal.ofReal x ≤ ‖x‖ₑ := fun x => by
    rw [Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_ofReal (le_abs_self x)
  -- the pointwise bound on `α`
  have hpt : ∀ T : R.tree, ‖α T‖ₑ ≤ ENNReal.ofReal C₀ *
      ((‖A T‖ₑ + ‖B T‖ₑ + ‖Cf T‖ₑ + ‖D T‖ₑ) * ENNReal.ofReal (T : DyadicCube d).vol) := by
    intro T
    have hT : (T : DyadicCube d).toSet ⊆ R.toSet := DyadicCube.mem_tree.mp T.2
    have h : |α T| ≤ C₀ * (A T + B T + Cf T + D T) * (T : DyadicCube d).vol := by
      have h0 := hα T T.2
      rw [← martDiff_truncate_of_subset hT f₁, ← martDiff_truncate_of_subset hT f₂,
        ← martAvg_truncate_of_subset hT f₁, ← martAvg_truncate_of_subset hT f₂] at h0
      refine h0.trans_eq ?_
      simp only [hAdef, hBdef, hCdef, hDdef, Pi.mul_apply]
      ring
    have hsum0 : 0 ≤ A T + B T + Cf T + D T := by
      have := hA0 T; have := hB0 T; have := hC0 T; have := hD0 T
      linarith
    calc ‖α T‖ₑ = ENNReal.ofReal |α T| := Real.enorm_eq_ofReal_abs _
      _ ≤ ENNReal.ofReal (C₀ * (A T + B T + Cf T + D T) * (T : DyadicCube d).vol) :=
          ENNReal.ofReal_le_ofReal h
      _ = ENNReal.ofReal C₀ *
          (ENNReal.ofReal (A T + B T + Cf T + D T) * ENNReal.ofReal (T : DyadicCube d).vol) := by
          rw [ENNReal.ofReal_mul (mul_nonneg hC₀ hsum0), ENNReal.ofReal_mul hC₀, mul_assoc]
      _ ≤ _ := by
          gcongr
          calc ENNReal.ofReal (A T + B T + Cf T + D T)
              = ENNReal.ofReal (A T) + ENNReal.ofReal (B T) + ENNReal.ofReal (Cf T) +
                  ENNReal.ofReal (D T) := by
                rw [ENNReal.ofReal_add (by linarith [hA0 T, hB0 T, hC0 T]) (hD0 T),
                  ENNReal.ofReal_add (by linarith [hA0 T, hB0 T]) (hC0 T),
                  ENNReal.ofReal_add (hA0 T) (hB0 T)]
            _ ≤ ‖A T‖ₑ + ‖B T‖ₑ + ‖Cf T‖ₑ + ‖D T‖ₑ :=
                add_le_add (add_le_add (add_le_add (hnn _) (hnn _)) (hnn _)) (hnn _)
  -- summation
  calc ∑' T : R.tree, ‖α T‖ₑ
      ≤ ∑' T : R.tree, ENNReal.ofReal C₀ *
          ((‖A T‖ₑ + ‖B T‖ₑ + ‖Cf T‖ₑ + ‖D T‖ₑ) * ENNReal.ofReal (T : DyadicCube d).vol) :=
        ENNReal.tsum_le_tsum hpt
    _ ≤ ∑' T : DyadicCube d, ENNReal.ofReal C₀ *
          ((‖A T‖ₑ + ‖B T‖ₑ + ‖Cf T‖ₑ + ‖D T‖ₑ) * ENNReal.ofReal T.vol) :=
        ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective
          (fun T : DyadicCube d => ENNReal.ofReal C₀ *
            ((‖A T‖ₑ + ‖B T‖ₑ + ‖Cf T‖ₑ + ‖D T‖ₑ) * ENNReal.ofReal T.vol))
    _ = ENNReal.ofReal C₀ * (∑' T : DyadicCube d, ‖A T‖ₑ * ENNReal.ofReal T.vol +
          ∑' T : DyadicCube d, ‖B T‖ₑ * ENNReal.ofReal T.vol +
          ∑' T : DyadicCube d, ‖Cf T‖ₑ * ENNReal.ofReal T.vol +
          ∑' T : DyadicCube d, ‖D T‖ₑ * ENNReal.ofReal T.vol) := by
        rw [ENNReal.tsum_mul_left]
        congr 1
        simp only [add_mul]
        rw [ENNReal.tsum_add, ENNReal.tsum_add, ENNReal.tsum_add]
    _ ≤ ENNReal.ofReal C₀ * (4 * outerLpNorm (sizeP 1) 1 A + 4 * outerLpNorm (sizeP 1) 1 B +
          4 * outerLpNorm (sizeP 1) 1 Cf + 4 * outerLpNorm (sizeP 1) 1 D) := by
        gcongr <;> exact tsum_enorm_mul_vol_le _
    _ ≤ ENNReal.ofReal C₀ * (4 * K + 4 * K + 4 * K + 4 * K) := by gcongr
    _ = ENNReal.ofReal (32 * Cp * Cq * C₀) * (N₁ * N₂) := by
        rw [hK, hM, h2s, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
        ring

end Lemma272Proof

end MirekThiele
