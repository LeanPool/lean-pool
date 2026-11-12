/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.TopologicalDisk
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.Order.Lattice

-- [TABLET NODE: P3092T1CenteredRectangleDisk]

/-!
# P3092T1CenteredRectangleDisk

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace CenteredRectangleDiskConstruction

private noncomputable abbrev q (a : Nat → ℝ) (b : Nat → ℝ) : Nat → (ℝ × ℝ) → ℝ := by
  classical
  exact fun j x => max (|x.1| / a j) (|x.2| / b j)

private noncomputable abbrev g (J : Finset Nat) (hJ : J.Nonempty) (a : Nat → ℝ) (b : Nat → ℝ) :
    (ℝ × ℝ) → ℝ := by
  classical
  let q : Nat → (ℝ × ℝ) → ℝ := fun j x => max (|x.1| / a j) (|x.2| / b j)
  exact fun x => J.inf' hJ (fun j => q j x)

private noncomputable abbrev R (J : Finset Nat) (hJ : J.Nonempty) (a : Nat → ℝ) (b : Nat → ℝ) :
    (ℝ × ℝ) → ℝ := by
  classical
  let q : Nat → (ℝ × ℝ) → ℝ := fun j x => max (|x.1| / a j) (|x.2| / b j)
  exact fun x => J.sup' hJ (fun j => (q j x)⁻¹)

private theorem hq_nonneg (J : Finset Nat) (a : Nat → ℝ) (b : Nat → ℝ) (ha : ∀ j ∈ J, 0 < a j) (j
    : Nat) (hj : j ∈ J) (x : ℝ × ℝ) : 0 ≤ (q a b) j x := by
  classical
  let q : Nat → (ℝ × ℝ) → ℝ := fun j x => max (|x.1| / a j) (|x.2| / b j)
  change (0 ≤ q j x)
  exact le_trans (div_nonneg (abs_nonneg _) (ha j hj).le) (le_max_left _ _)

private theorem hq_pos (J : Finset Nat) (a : Nat → ℝ) (b : Nat → ℝ) (ha : ∀ j ∈ J, 0 < a j) (hb :
    ∀ j ∈ J, 0 < b j) (j : Nat) (hj : j ∈ J) (x : ℝ × ℝ) (hx : x ≠ 0) : 0 < (q a b) j x := by
  classical
  let q : Nat → (ℝ × ℝ) → ℝ := fun j x => max (|x.1| / a j) (|x.2| / b j)
  change (0 < q j x)
  by_contra hn
  have hh := max_le_iff.mp (le_of_not_gt hn)
  have h1 : x.1 = 0 := abs_eq_zero.mp (le_antisymm
    (by have := (div_le_iff₀ (ha j hj)).mp hh.1; linarith) (abs_nonneg _))
  have h2 : x.2 = 0 := abs_eq_zero.mp (le_antisymm
    (by have := (div_le_iff₀ (hb j hj)).mp hh.2; linarith) (abs_nonneg _))
  exact hx (Prod.ext h1 h2)

private theorem hg_nonneg (J : Finset Nat) (hJ : J.Nonempty) (a : Nat → ℝ) (b : Nat → ℝ) (ha : ∀
    j ∈ J, 0 < a j) (x : ℝ × ℝ) : 0 ≤ (g J hJ a b) x := by
  classical
  let q : Nat → (ℝ × ℝ) → ℝ := fun j x => max (|x.1| / a j) (|x.2| / b j)
  let g : (ℝ × ℝ) → ℝ := fun x => J.inf' hJ (fun j => q j x)
  have hq_nonneg (j : Nat) (hj : j ∈ J) (x : ℝ × ℝ) : 0 ≤ q j x := hq_nonneg J a b ha j hj x
  change (0 ≤ g x)
  exact Finset.le_inf' hJ _ (fun j hj => hq_nonneg j hj x)

private theorem hg_pos (J : Finset Nat) (hJ : J.Nonempty) (a : Nat → ℝ) (b : Nat → ℝ) (ha : ∀ j ∈
    J, 0 < a j) (hb : ∀ j ∈ J, 0 < b j) (x : ℝ × ℝ) (hx : x ≠ 0) : 0 < (g J hJ a b) x := by
  classical
  let q : Nat → (ℝ × ℝ) → ℝ := fun j x => max (|x.1| / a j) (|x.2| / b j)
  let g : (ℝ × ℝ) → ℝ := fun x => J.inf' hJ (fun j => q j x)
  have hq_pos (j : Nat) (hj : j ∈ J) (x : ℝ × ℝ) (hx : x ≠ 0) : 0 < q j x := hq_pos J a b ha hb j
      hj x hx
  change (0 < g x)
  exact (Finset.lt_inf'_iff hJ).mpr (fun j hj => hq_pos j hj x hx)

private theorem hg_zero (J : Finset Nat) (hJ : J.Nonempty) (a : Nat → ℝ) (b : Nat → ℝ) : (g J hJ
    a b) 0 = 0 := by
  classical
  let q : Nat → (ℝ × ℝ) → ℝ := fun j x => max (|x.1| / a j) (|x.2| / b j)
  let g : (ℝ × ℝ) → ℝ := fun x => J.inf' hJ (fun j => q j x)
  change (g 0 = 0)
  exact Finset.inf'_eq_of_forall hJ (fun j => q j 0) (by simp [q])

private theorem hq_smul (a : Nat → ℝ) (b : Nat → ℝ) (t : ℝ) (ht : 0 ≤ t) (j : Nat) (x : ℝ × ℝ) :
      (q a b) j (t • x) = t * (q a b) j x := by
  classical
  let q : Nat → (ℝ × ℝ) → ℝ := fun j x => max (|x.1| / a j) (|x.2| / b j)
  change (q j (t • x) = t * q j x)
  simp only [q, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, abs_mul,
    abs_of_nonneg ht, mul_div_assoc, mul_max_of_nonneg _ _ ht]

private theorem hg_smul (J : Finset Nat) (hJ : J.Nonempty) (a : Nat → ℝ) (b : Nat → ℝ) (t : ℝ)
    (ht : 0 ≤ t) (x : ℝ × ℝ) : (g J hJ a b) (t • x) = t * (g J hJ a b) x := by
  classical
  let q : Nat → (ℝ × ℝ) → ℝ := fun j x => max (|x.1| / a j) (|x.2| / b j)
  let g : (ℝ × ℝ) → ℝ := fun x => J.inf' hJ (fun j => q j x)
  have hq_smul (t : ℝ) (ht : 0 ≤ t) (j : Nat) (x : ℝ × ℝ) :
      q j (t • x) = t * q j x := hq_smul a b t ht j x
  change (g (t • x) = t * g x)
  simp only [g, hq_smul t ht]
  exact (Finset.apply_inf'_eq_inf'_comp hJ (fun y : ℝ => t * y)
    (fun y z => mul_min_of_nonneg y z ht)).symm

private theorem hg_cont (J : Finset Nat) (hJ : J.Nonempty) (a : Nat → ℝ) (b : Nat → ℝ) :
    Continuous (g J hJ a b) := by
  classical
  let q : Nat → (ℝ × ℝ) → ℝ := fun j x => max (|x.1| / a j) (|x.2| / b j)
  let g : (ℝ × ℝ) → ℝ := fun x => J.inf' hJ (fun j => q j x)
  change (Continuous g)
  apply Continuous.finset_inf'_apply hJ
  intro j hj
  exact (continuous_fst.abs.div_const _).max (continuous_snd.abs.div_const _)

private theorem hR_eq (J : Finset Nat) (hJ : J.Nonempty) (a : Nat → ℝ) (b : Nat → ℝ) (ha : ∀ j ∈
    J, 0 < a j) (hb : ∀ j ∈ J, 0 < b j) (x : ℝ × ℝ) (hx : x ≠ 0) : (R J hJ a b) x = ((g J hJ a b)
    x)⁻¹ := by
  classical
  let q : Nat → (ℝ × ℝ) → ℝ := fun j x => max (|x.1| / a j) (|x.2| / b j)
  let g : (ℝ × ℝ) → ℝ := fun x => J.inf' hJ (fun j => q j x)
  let R : (ℝ × ℝ) → ℝ := fun x => J.sup' hJ (fun j => (q j x)⁻¹)
  have hq_pos (j : Nat) (hj : j ∈ J) (x : ℝ × ℝ) (hx : x ≠ 0) : 0 < q j x := hq_pos J a b ha hb j
      hj x hx
  have hg_pos (x : ℝ × ℝ) (hx : x ≠ 0) : 0 < g x := hg_pos J hJ a b ha hb x hx
  change (R x = (g x)⁻¹)
  apply le_antisymm
  · apply Finset.sup'_le
    intro j hj
    exact (inv_le_inv₀ (hq_pos j hj x hx) (hg_pos x hx)).mpr
      (Finset.inf'_le _ hj)
  · obtain ⟨j, hj, heq⟩ := Finset.exists_mem_eq_inf' hJ (fun j => q j x)
    change (J.inf' hJ (fun j => q j x))⁻¹ ≤ R x
    rw [heq]
    exact Finset.le_sup' (fun j => (q j x)⁻¹) hj

private theorem hR_attained (J : Finset Nat) (hJ : J.Nonempty) (a : Nat → ℝ) (b : Nat → ℝ) (x : ℝ
    × ℝ) : ∃ j ∈ J, (R J hJ a b) x = ((q a b) j x)⁻¹ := by
  classical
  let q : Nat → (ℝ × ℝ) → ℝ := fun j x => max (|x.1| / a j) (|x.2| / b j)
  let R : (ℝ × ℝ) → ℝ := fun x => J.sup' hJ (fun j => (q j x)⁻¹)
  change (∃ j ∈ J, R x = (q j x)⁻¹)
  exact Finset.exists_mem_eq_sup' hJ _

private theorem hR_pos (J : Finset Nat) (hJ : J.Nonempty) (a : Nat → ℝ) (b : Nat → ℝ) (ha : ∀ j ∈
    J, 0 < a j) (hb : ∀ j ∈ J, 0 < b j) (x : ℝ × ℝ) (hx : x ≠ 0) : 0 < (R J hJ a b) x := by
  classical
  let q : Nat → (ℝ × ℝ) → ℝ := fun j x => max (|x.1| / a j) (|x.2| / b j)
  let g : (ℝ × ℝ) → ℝ := fun x => J.inf' hJ (fun j => q j x)
  let R : (ℝ × ℝ) → ℝ := fun x => J.sup' hJ (fun j => (q j x)⁻¹)
  have hg_pos (x : ℝ × ℝ) (hx : x ≠ 0) : 0 < g x := hg_pos J hJ a b ha hb x hx
  have hR_eq (x : ℝ × ℝ) (hx : x ≠ 0) : R x = (g x)⁻¹ := hR_eq J hJ a b ha hb x hx
  change (0 < R x)
  rw [hR_eq x hx]
  exact inv_pos.mpr (hg_pos x hx)

private theorem hR_cont (J : Finset Nat) (hJ : J.Nonempty) (a : Nat → ℝ) (b : Nat → ℝ) (ha : ∀ j
    ∈ J, 0 < a j) (hb : ∀ j ∈ J, 0 < b j) (x : ℝ × ℝ) (hx : x ≠ 0) : ContinuousAt (R J hJ a b) x
    := by
  classical
  let q : Nat → (ℝ × ℝ) → ℝ := fun j x => max (|x.1| / a j) (|x.2| / b j)
  let R : (ℝ × ℝ) → ℝ := fun x => J.sup' hJ (fun j => (q j x)⁻¹)
  have hq_pos (j : Nat) (hj : j ∈ J) (x : ℝ × ℝ) (hx : x ≠ 0) : 0 < q j x := hq_pos J a b ha hb j
      hj x hx
  change (ContinuousAt R x)
  apply ContinuousAt.finset_sup'_apply hJ
  intro j hj
  exact ((continuous_fst.abs.div_const _).max
    (continuous_snd.abs.div_const _)).continuousAt.inv₀ (hq_pos j hj x hx).ne'

private theorem hmem (J : Finset Nat) (hJ : J.Nonempty) (c : ℝ × ℝ) (a : Nat → ℝ) (b : Nat → ℝ)
    (ha : ∀ j ∈ J, 0 < a j) (hb : ∀ j ∈ J, 0 < b j) (x : ℝ × ℝ) :
      c + x ∈ (⋃ j ∈ J, Set.Icc (c.1 - a j, c.2 - b j)
          (c.1 + a j, c.2 + b j)) ↔ (g J hJ a b) x ≤ 1 := by
  classical
  let q : Nat → (ℝ × ℝ) → ℝ := fun j x => max (|x.1| / a j) (|x.2| / b j)
  let g : (ℝ × ℝ) → ℝ := fun x => J.inf' hJ (fun j => q j x)
  change (c + x ∈ (⋃ j ∈ J, Set.Icc (c.1 - a j, c.2 - b j)
          (c.1 + a j, c.2 + b j)) ↔ g x ≤ 1)
  simp only [Set.mem_iUnion, exists_prop, Set.mem_Icc, Prod.le_def,
    Prod.fst_add, Prod.snd_add]
  change (∃ j ∈ J, (c.1 - a j ≤ c.1 + x.1 ∧ c.2 - b j ≤ c.2 + x.2) ∧
    c.1 + x.1 ≤ c.1 + a j ∧ c.2 + x.2 ≤ c.2 + b j) ↔ _
  change _ ↔ J.inf' hJ (fun j => q j x) ≤ 1
  rw [Finset.inf'_le_iff]
  apply exists_congr
  intro j
  apply and_congr_right
  intro hj
  change _ ↔ max (|x.1| / a j) (|x.2| / b j) ≤ 1
  rw [max_le_iff, div_le_iff₀ (ha j hj), div_le_iff₀ (hb j hj)]
  simp only [one_mul, abs_le]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩

private theorem hray (J : Finset Nat) (hJ : J.Nonempty) (c : ℝ × ℝ) (a : Nat → ℝ) (b : Nat → ℝ)
    (ha : ∀ j ∈ J, 0 < a j) (hb : ∀ j ∈ J, 0 < b j) (u : ℝ × ℝ) (hu : ‖u‖ = 1) (t : ℝ) (ht : 0 ≤
    t) :
      c + t • u ∈ (⋃ j ∈ J, Set.Icc (c.1 - a j, c.2 - b j)
          (c.1 + a j, c.2 + b j)) ↔ t ≤ (R J hJ a b) u := by
  classical
  let q : Nat → (ℝ × ℝ) → ℝ := fun j x => max (|x.1| / a j) (|x.2| / b j)
  let g : (ℝ × ℝ) → ℝ := fun x => J.inf' hJ (fun j => q j x)
  let R : (ℝ × ℝ) → ℝ := fun x => J.sup' hJ (fun j => (q j x)⁻¹)
  have hg_pos (x : ℝ × ℝ) (hx : x ≠ 0) : 0 < g x := hg_pos J hJ a b ha hb x hx
  have hg_smul (t : ℝ) (ht : 0 ≤ t) (x : ℝ × ℝ) : g (t • x) = t * g x := hg_smul J hJ a b t ht x
  have hR_eq (x : ℝ × ℝ) (hx : x ≠ 0) : R x = (g x)⁻¹ := hR_eq J hJ a b ha hb x hx
  have hmem (x : ℝ × ℝ) :
      c + x ∈ (⋃ j ∈ J, Set.Icc (c.1 - a j, c.2 - b j)
          (c.1 + a j, c.2 + b j)) ↔ g x ≤ 1 := hmem J hJ c a b ha hb x
  change (c + t • u ∈ (⋃ j ∈ J, Set.Icc (c.1 - a j, c.2 - b j)
          (c.1 + a j, c.2 + b j)) ↔ t ≤ R u)
  have hu0 : u ≠ 0 := by intro h; simp [h] at hu
  rw [hmem, hg_smul t ht, hR_eq u hu0, ← one_div,
    le_div_iff₀ (hg_pos u hu0)]

private noncomputable abbrev j₀ (J : Finset Nat) (hJ : J.Nonempty) := hJ.choose

private theorem hj₀ (J : Finset Nat) (hJ : J.Nonempty) : (j₀ J hJ) ∈ J := by
  classical
  let j₀ := hJ.choose
  change (j₀ ∈ J)
  exact hJ.choose_spec

private noncomputable abbrev M (J : Finset Nat) (hJ : J.Nonempty) (a : Nat → ℝ) (b : Nat → ℝ) :=
    J.sup' hJ (fun j => max (a j) (b j))

private noncomputable abbrev C (J : Finset Nat) (hJ : J.Nonempty) (a : Nat → ℝ) (b : Nat → ℝ) :=
    max (a (j₀ J hJ))⁻¹ (b (j₀ J hJ))⁻¹

private theorem hM_pos (J : Finset Nat) (hJ : J.Nonempty) (a : Nat → ℝ) (b : Nat → ℝ) (ha : ∀ j ∈
    J, 0 < a j) : 0 < (M J hJ a b) := by
  classical
  let j₀ := hJ.choose
  have hj₀ : j₀ ∈ J := hj₀ J hJ
  let M := J.sup' hJ (fun j => max (a j) (b j))
  dsimp only [CenteredRectangleDiskConstruction.M] at *
  change (0 < M)
  exact (ha j₀ hj₀).trans_le ((le_max_left _ _).trans
      (Finset.le_sup' (fun j => max (a j) (b j)) hj₀))

private theorem hC_pos (J : Finset Nat) (hJ : J.Nonempty) (a : Nat → ℝ) (b : Nat → ℝ) (ha : ∀ j ∈
    J, 0 < a j) : 0 < (C J hJ a b) := by
  classical
  let j₀ := hJ.choose
  have hj₀ : j₀ ∈ J := hj₀ J hJ
  let C := max (a j₀)⁻¹ (b j₀)⁻¹
  change (0 < C)
  exact (inv_pos.mpr (ha j₀ hj₀)).trans_le (le_max_left _ _)

private theorem hq_bound (J : Finset Nat) (hJ : J.Nonempty) (a : Nat → ℝ) (b : Nat → ℝ) (ha : ∀ j
    ∈ J, 0 < a j) (hb : ∀ j ∈ J, 0 < b j) (j : Nat) (hj : j ∈ J) (x : ℝ × ℝ) : ‖x‖ ≤ (M J hJ a b)
    * (q a b) j x := by
  classical
  let q : Nat → (ℝ × ℝ) → ℝ := fun j x => max (|x.1| / a j) (|x.2| / b j)
  have hq_nonneg (j : Nat) (hj : j ∈ J) (x : ℝ × ℝ) : 0 ≤ q j x := hq_nonneg J a b ha j hj x
  let M := J.sup' hJ (fun j => max (a j) (b j))
  dsimp only [CenteredRectangleDiskConstruction.M] at *
  change (‖x‖ ≤ M * q j x)
  have h1 : |x.1| ≤ q j x * a j :=
    (div_le_iff₀ (ha j hj)).mp (le_max_left _ _)
  have h2 : |x.2| ≤ q j x * b j :=
    (div_le_iff₀ (hb j hj)).mp (le_max_right _ _)
  have hMa : a j ≤ M := (le_max_left _ _).trans
    (Finset.le_sup' (fun j => max (a j) (b j)) hj)
  have hMb : b j ≤ M := (le_max_right _ _).trans
    (Finset.le_sup' (fun j => max (a j) (b j)) hj)
  rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
  apply max_le
  · nlinarith [mul_le_mul_of_nonneg_left hMa (hq_nonneg j hj x)]
  · nlinarith [mul_le_mul_of_nonneg_left hMb (hq_nonneg j hj x)]

private theorem hg_lower (J : Finset Nat) (hJ : J.Nonempty) (a : Nat → ℝ) (b : Nat → ℝ) (ha : ∀ j
    ∈ J, 0 < a j) (hb : ∀ j ∈ J, 0 < b j) (x : ℝ × ℝ) : ‖x‖ ≤ (M J hJ a b) * (g J hJ a b) x := by
  classical
  let q : Nat → (ℝ × ℝ) → ℝ := fun j x => max (|x.1| / a j) (|x.2| / b j)
  let g : (ℝ × ℝ) → ℝ := fun x => J.inf' hJ (fun j => q j x)
  let M := J.sup' hJ (fun j => max (a j) (b j))
  have hq_bound (j : Nat) (hj : j ∈ J) (x : ℝ × ℝ) : ‖x‖ ≤ M * q j x := hq_bound J hJ a b ha hb j
      hj x
  dsimp only [CenteredRectangleDiskConstruction.M] at *
  change (‖x‖ ≤ M * g x)
  obtain ⟨j, hj, heq⟩ := Finset.exists_mem_eq_inf' hJ (fun j => q j x)
  change ‖x‖ ≤ M * J.inf' hJ (fun j => q j x)
  rw [heq]
  exact hq_bound j hj x

private theorem hg_upper (J : Finset Nat) (hJ : J.Nonempty) (a : Nat → ℝ) (b : Nat → ℝ) (ha : ∀ j
    ∈ J, 0 < a j) (hb : ∀ j ∈ J, 0 < b j) (x : ℝ × ℝ) : (g J hJ a b) x ≤ (C J hJ a b) * ‖x‖ := by
  classical
  let q : Nat → (ℝ × ℝ) → ℝ := fun j x => max (|x.1| / a j) (|x.2| / b j)
  let g : (ℝ × ℝ) → ℝ := fun x => J.inf' hJ (fun j => q j x)
  let j₀ := hJ.choose
  have hj₀ : j₀ ∈ J := hj₀ J hJ
  let C := max (a j₀)⁻¹ (b j₀)⁻¹
  change (g x ≤ C * ‖x‖)
  apply (Finset.inf'_le (fun j => q j x) hj₀).trans
  change max (|x.1| / a j₀) (|x.2| / b j₀) ≤ C * ‖x‖
  apply max_le
  · rw [div_eq_mul_inv, mul_comm C]
    exact mul_le_mul (by simpa using norm_fst_le x) (le_max_left _ _)
      (inv_nonneg.mpr (ha j₀ hj₀).le) (norm_nonneg x)
  · rw [div_eq_mul_inv, mul_comm C]
    exact mul_le_mul (by simpa using norm_snd_le x) (le_max_right _ _)
      (inv_nonneg.mpr (hb j₀ hj₀).le) (norm_nonneg x)

private theorem hunit (x : ℝ × ℝ) (hx : x ≠ 0) : ‖‖x‖⁻¹ • x‖ = 1 := by
  classical
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg x)),
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]

private theorem hR_normalized (J : Finset Nat) (hJ : J.Nonempty) (a : Nat → ℝ) (b : Nat → ℝ) (ha
    : ∀ j ∈ J, 0 < a j) (hb : ∀ j ∈ J, 0 < b j) (x : ℝ × ℝ) (hx : x ≠ 0) : (R J hJ a b) (‖x‖⁻¹ •
    x) = ‖x‖ / (g J hJ a b) x := by
  classical
  let q : Nat → (ℝ × ℝ) → ℝ := fun j x => max (|x.1| / a j) (|x.2| / b j)
  let g : (ℝ × ℝ) → ℝ := fun x => J.inf' hJ (fun j => q j x)
  let R : (ℝ × ℝ) → ℝ := fun x => J.sup' hJ (fun j => (q j x)⁻¹)
  have hg_smul (t : ℝ) (ht : 0 ≤ t) (x : ℝ × ℝ) : g (t • x) = t * g x := hg_smul J hJ a b t ht x
  have hR_eq (x : ℝ × ℝ) (hx : x ≠ 0) : R x = (g x)⁻¹ := hR_eq J hJ a b ha hb x hx
  have hunit (x : ℝ × ℝ) (hx : x ≠ 0) : ‖‖x‖⁻¹ • x‖ = 1 := hunit x hx
  change (R (‖x‖⁻¹ • x) = ‖x‖ / g x)
  have hu0 : ‖x‖⁻¹ • x ≠ 0 := by
    intro h
    have hh := hunit x hx
    simp [h] at hh
  rw [hR_eq _ hu0, hg_smul _ (inv_nonneg.mpr (norm_nonneg x)), mul_inv_rev, inv_inv]
  simp only [div_eq_mul_inv, mul_comm]

private noncomputable abbrev F (J : Finset Nat) (hJ : J.Nonempty) (a : Nat → ℝ) (b : Nat → ℝ) :
    (ℝ × ℝ) → (ℝ × ℝ) := by
  classical
  let q : Nat → (ℝ × ℝ) → ℝ := fun j x => max (|x.1| / a j) (|x.2| / b j)
  let R : (ℝ × ℝ) → ℝ := fun x => J.sup' hJ (fun j => (q j x)⁻¹)
  exact fun x => R (‖x‖⁻¹ • x) • x

private noncomputable abbrev G (J : Finset Nat) (hJ : J.Nonempty) (a : Nat → ℝ) (b : Nat → ℝ) :
    (ℝ × ℝ) → (ℝ × ℝ) := by
  classical
  let q : Nat → (ℝ × ℝ) → ℝ := fun j x => max (|x.1| / a j) (|x.2| / b j)
  let R : (ℝ × ℝ) → ℝ := fun x => J.sup' hJ (fun j => (q j x)⁻¹)
  exact fun x => (R (‖x‖⁻¹ • x))⁻¹ • x

private theorem hF_zero (J : Finset Nat) (hJ : J.Nonempty) (a : Nat → ℝ) (b : Nat → ℝ) : (F J hJ
    a b) 0 = 0 := by
  classical
  let q : Nat → (ℝ × ℝ) → ℝ := fun j x => max (|x.1| / a j) (|x.2| / b j)
  let R : (ℝ × ℝ) → ℝ := fun x => J.sup' hJ (fun j => (q j x)⁻¹)
  let F : (ℝ × ℝ) → (ℝ × ℝ) := fun x => R (‖x‖⁻¹ • x) • x
  change (F 0 = 0)
  simp [F]

private theorem hG_zero (J : Finset Nat) (hJ : J.Nonempty) (a : Nat → ℝ) (b : Nat → ℝ) : (G J hJ
    a b) 0 = 0 := by
  classical
  let q : Nat → (ℝ × ℝ) → ℝ := fun j x => max (|x.1| / a j) (|x.2| / b j)
  let R : (ℝ × ℝ) → ℝ := fun x => J.sup' hJ (fun j => (q j x)⁻¹)
  let G : (ℝ × ℝ) → (ℝ × ℝ) := fun x => (R (‖x‖⁻¹ • x))⁻¹ • x
  change (G 0 = 0)
  simp [G]

private theorem hF_formula (J : Finset Nat) (hJ : J.Nonempty) (a : Nat → ℝ) (b : Nat → ℝ) (ha : ∀
    j ∈ J, 0 < a j) (hb : ∀ j ∈ J, 0 < b j) (x : ℝ × ℝ) : (F J hJ a b) x = (‖x‖ / (g J hJ a b) x)
    • x := by
  classical
  let q : Nat → (ℝ × ℝ) → ℝ := fun j x => max (|x.1| / a j) (|x.2| / b j)
  let g : (ℝ × ℝ) → ℝ := fun x => J.inf' hJ (fun j => q j x)
  let R : (ℝ × ℝ) → ℝ := fun x => J.sup' hJ (fun j => (q j x)⁻¹)
  have hR_normalized (x : ℝ × ℝ) (hx : x ≠ 0) : R (‖x‖⁻¹ • x) = ‖x‖ / g x := hR_normalized J hJ a
      b ha hb x hx
  let F : (ℝ × ℝ) → (ℝ × ℝ) := fun x => R (‖x‖⁻¹ • x) • x
  have hF_zero : F 0 = 0 := hF_zero J hJ a b
  change (F x = (‖x‖ / g x) • x)
  by_cases hx : x = 0
  · simp [hx, hF_zero]
  · change R (‖x‖⁻¹ • x) • x = _
    rw [hR_normalized x hx]

private theorem hG_formula (J : Finset Nat) (hJ : J.Nonempty) (a : Nat → ℝ) (b : Nat → ℝ) (ha : ∀
    j ∈ J, 0 < a j) (hb : ∀ j ∈ J, 0 < b j) (x : ℝ × ℝ) : (G J hJ a b) x = ((g J hJ a b) x / ‖x‖)
    • x := by
  classical
  let q : Nat → (ℝ × ℝ) → ℝ := fun j x => max (|x.1| / a j) (|x.2| / b j)
  let g : (ℝ × ℝ) → ℝ := fun x => J.inf' hJ (fun j => q j x)
  let R : (ℝ × ℝ) → ℝ := fun x => J.sup' hJ (fun j => (q j x)⁻¹)
  have hR_normalized (x : ℝ × ℝ) (hx : x ≠ 0) : R (‖x‖⁻¹ • x) = ‖x‖ / g x := hR_normalized J hJ a
      b ha hb x hx
  let G : (ℝ × ℝ) → (ℝ × ℝ) := fun x => (R (‖x‖⁻¹ • x))⁻¹ • x
  have hG_zero : G 0 = 0 := hG_zero J hJ a b
  change (G x = (g x / ‖x‖) • x)
  by_cases hx : x = 0
  · simp [hx, hG_zero]
  · change (R (‖x‖⁻¹ • x))⁻¹ • x = _
    rw [hR_normalized x hx, inv_div]

private theorem hF_norm (J : Finset Nat) (hJ : J.Nonempty) (a : Nat → ℝ) (b : Nat → ℝ) (ha : ∀ j
    ∈ J, 0 < a j) (hb : ∀ j ∈ J, 0 < b j) (x : ℝ × ℝ) : ‖(F J hJ a b) x‖ = (‖x‖ / (g J hJ a b) x)
    * ‖x‖ := by
  classical
  let q : Nat → (ℝ × ℝ) → ℝ := fun j x => max (|x.1| / a j) (|x.2| / b j)
  let g : (ℝ × ℝ) → ℝ := fun x => J.inf' hJ (fun j => q j x)
  let R : (ℝ × ℝ) → ℝ := fun x => J.sup' hJ (fun j => (q j x)⁻¹)
  have hg_nonneg (x : ℝ × ℝ) : 0 ≤ g x := hg_nonneg J hJ a b ha x
  let F : (ℝ × ℝ) → (ℝ × ℝ) := fun x => R (‖x‖⁻¹ • x) • x
  have hF_formula (x : ℝ × ℝ) : F x = (‖x‖ / g x) • x := hF_formula J hJ a b ha hb x
  change (‖F x‖ = (‖x‖ / g x) * ‖x‖)
  rw [hF_formula, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (norm_nonneg x) (hg_nonneg x))]

private theorem hG_norm (J : Finset Nat) (hJ : J.Nonempty) (a : Nat → ℝ) (b : Nat → ℝ) (ha : ∀ j
    ∈ J, 0 < a j) (hb : ∀ j ∈ J, 0 < b j) (x : ℝ × ℝ) : ‖(G J hJ a b) x‖ = (g J hJ a b) x := by
  classical
  let q : Nat → (ℝ × ℝ) → ℝ := fun j x => max (|x.1| / a j) (|x.2| / b j)
  let g : (ℝ × ℝ) → ℝ := fun x => J.inf' hJ (fun j => q j x)
  let R : (ℝ × ℝ) → ℝ := fun x => J.sup' hJ (fun j => (q j x)⁻¹)
  have hg_nonneg (x : ℝ × ℝ) : 0 ≤ g x := hg_nonneg J hJ a b ha x
  have hg_zero : g 0 = 0 := hg_zero J hJ a b
  let G : (ℝ × ℝ) → (ℝ × ℝ) := fun x => (R (‖x‖⁻¹ • x))⁻¹ • x
  have hG_zero : G 0 = 0 := hG_zero J hJ a b
  have hG_formula (x : ℝ × ℝ) : G x = (g x / ‖x‖) • x := hG_formula J hJ a b ha hb x
  change (‖G x‖ = g x)
  by_cases hx : x = 0
  · simp [hx, hG_zero, hg_zero]
  · rw [hG_formula, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg (hg_nonneg x) (norm_nonneg x)),
      div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hx)]

private theorem hgF (J : Finset Nat) (hJ : J.Nonempty) (a : Nat → ℝ) (b : Nat → ℝ) (ha : ∀ j ∈ J,
    0 < a j) (hb : ∀ j ∈ J, 0 < b j) (x : ℝ × ℝ) : (g J hJ a b) ((F J hJ a b) x) = ‖x‖ := by
  classical
  let q : Nat → (ℝ × ℝ) → ℝ := fun j x => max (|x.1| / a j) (|x.2| / b j)
  let g : (ℝ × ℝ) → ℝ := fun x => J.inf' hJ (fun j => q j x)
  let R : (ℝ × ℝ) → ℝ := fun x => J.sup' hJ (fun j => (q j x)⁻¹)
  have hg_nonneg (x : ℝ × ℝ) : 0 ≤ g x := hg_nonneg J hJ a b ha x
  have hg_pos (x : ℝ × ℝ) (hx : x ≠ 0) : 0 < g x := hg_pos J hJ a b ha hb x hx
  have hg_zero : g 0 = 0 := hg_zero J hJ a b
  have hg_smul (t : ℝ) (ht : 0 ≤ t) (x : ℝ × ℝ) : g (t • x) = t * g x := hg_smul J hJ a b t ht x
  let F : (ℝ × ℝ) → (ℝ × ℝ) := fun x => R (‖x‖⁻¹ • x) • x
  have hF_zero : F 0 = 0 := hF_zero J hJ a b
  have hF_formula (x : ℝ × ℝ) : F x = (‖x‖ / g x) • x := hF_formula J hJ a b ha hb x
  change (g (F x) = ‖x‖)
  by_cases hx : x = 0
  · simp [hx, hF_zero, hg_zero]
  · rw [hF_formula, hg_smul _ (div_nonneg (norm_nonneg x) (hg_nonneg x)),
      div_mul_cancel₀ _ (hg_pos x hx).ne']

private theorem hGF (J : Finset Nat) (hJ : J.Nonempty) (a : Nat → ℝ) (b : Nat → ℝ) (ha : ∀ j ∈ J,
    0 < a j) (hb : ∀ j ∈ J, 0 < b j) (x : ℝ × ℝ) : (G J hJ a b) ((F J hJ a b) x) = x := by
  classical
  let q : Nat → (ℝ × ℝ) → ℝ := fun j x => max (|x.1| / a j) (|x.2| / b j)
  let g : (ℝ × ℝ) → ℝ := fun x => J.inf' hJ (fun j => q j x)
  let R : (ℝ × ℝ) → ℝ := fun x => J.sup' hJ (fun j => (q j x)⁻¹)
  have hg_pos (x : ℝ × ℝ) (hx : x ≠ 0) : 0 < g x := hg_pos J hJ a b ha hb x hx
  let F : (ℝ × ℝ) → (ℝ × ℝ) := fun x => R (‖x‖⁻¹ • x) • x
  let G : (ℝ × ℝ) → (ℝ × ℝ) := fun x => (R (‖x‖⁻¹ • x))⁻¹ • x
  have hF_zero : F 0 = 0 := hF_zero J hJ a b
  have hG_zero : G 0 = 0 := hG_zero J hJ a b
  have hF_formula (x : ℝ × ℝ) : F x = (‖x‖ / g x) • x := hF_formula J hJ a b ha hb x
  have hG_formula (x : ℝ × ℝ) : G x = (g x / ‖x‖) • x := hG_formula J hJ a b ha hb x
  have hF_norm (x : ℝ × ℝ) : ‖F x‖ = (‖x‖ / g x) * ‖x‖ := hF_norm J hJ a b ha hb x
  have hgF (x : ℝ × ℝ) : g (F x) = ‖x‖ := hgF J hJ a b ha hb x
  change (G (F x) = x)
  by_cases hx : x = 0
  · simp [hx, hF_zero, hG_zero]
  · have hn := norm_ne_zero_iff.mpr hx
    have hg := (hg_pos x hx).ne'
    rw [hG_formula, hgF, hF_norm, hF_formula, smul_smul]
    have he : ‖x‖ / (‖x‖ / g x * ‖x‖) * (‖x‖ / g x) = 1 := by
      field_simp
    rw [he, one_smul]

private theorem hFG (J : Finset Nat) (hJ : J.Nonempty) (a : Nat → ℝ) (b : Nat → ℝ) (ha : ∀ j ∈ J,
    0 < a j) (hb : ∀ j ∈ J, 0 < b j) (x : ℝ × ℝ) : (F J hJ a b) ((G J hJ a b) x) = x := by
  classical
  let q : Nat → (ℝ × ℝ) → ℝ := fun j x => max (|x.1| / a j) (|x.2| / b j)
  let g : (ℝ × ℝ) → ℝ := fun x => J.inf' hJ (fun j => q j x)
  let R : (ℝ × ℝ) → ℝ := fun x => J.sup' hJ (fun j => (q j x)⁻¹)
  have hg_nonneg (x : ℝ × ℝ) : 0 ≤ g x := hg_nonneg J hJ a b ha x
  have hg_pos (x : ℝ × ℝ) (hx : x ≠ 0) : 0 < g x := hg_pos J hJ a b ha hb x hx
  have hg_smul (t : ℝ) (ht : 0 ≤ t) (x : ℝ × ℝ) : g (t • x) = t * g x := hg_smul J hJ a b t ht x
  let F : (ℝ × ℝ) → (ℝ × ℝ) := fun x => R (‖x‖⁻¹ • x) • x
  let G : (ℝ × ℝ) → (ℝ × ℝ) := fun x => (R (‖x‖⁻¹ • x))⁻¹ • x
  have hF_zero : F 0 = 0 := hF_zero J hJ a b
  have hG_zero : G 0 = 0 := hG_zero J hJ a b
  have hF_formula (x : ℝ × ℝ) : F x = (‖x‖ / g x) • x := hF_formula J hJ a b ha hb x
  have hG_formula (x : ℝ × ℝ) : G x = (g x / ‖x‖) • x := hG_formula J hJ a b ha hb x
  have hG_norm (x : ℝ × ℝ) : ‖G x‖ = g x := hG_norm J hJ a b ha hb x
  change (F (G x) = x)
  by_cases hx : x = 0
  · simp [hx, hF_zero, hG_zero]
  · have hn := norm_ne_zero_iff.mpr hx
    have hg := (hg_pos x hx).ne'
    rw [hF_formula, hG_norm]
    rw [show g (G x) = (g x / ‖x‖) * g x from
      by rw [hG_formula, hg_smul _ (div_nonneg (hg_nonneg x) (norm_nonneg x))],
      hG_formula, smul_smul]
    have he : g x / (g x / ‖x‖ * g x) * (g x / ‖x‖) = 1 := by
      field_simp
    rw [he, one_smul]

private theorem hF_bound (J : Finset Nat) (hJ : J.Nonempty) (a : Nat → ℝ) (b : Nat → ℝ) (ha : ∀ j
    ∈ J, 0 < a j) (hb : ∀ j ∈ J, 0 < b j) (x : ℝ × ℝ) : ‖(F J hJ a b) x‖ ≤ (M J hJ a b) * ‖x‖ := by
  classical
  let q : Nat → (ℝ × ℝ) → ℝ := fun j x => max (|x.1| / a j) (|x.2| / b j)
  let g : (ℝ × ℝ) → ℝ := fun x => J.inf' hJ (fun j => q j x)
  let R : (ℝ × ℝ) → ℝ := fun x => J.sup' hJ (fun j => (q j x)⁻¹)
  have hg_pos (x : ℝ × ℝ) (hx : x ≠ 0) : 0 < g x := hg_pos J hJ a b ha hb x hx
  let M := J.sup' hJ (fun j => max (a j) (b j))
  have hg_lower (x : ℝ × ℝ) : ‖x‖ ≤ M * g x := hg_lower J hJ a b ha hb x
  let F : (ℝ × ℝ) → (ℝ × ℝ) := fun x => R (‖x‖⁻¹ • x) • x
  have hF_zero : F 0 = 0 := hF_zero J hJ a b
  have hF_norm (x : ℝ × ℝ) : ‖F x‖ = (‖x‖ / g x) * ‖x‖ := hF_norm J hJ a b ha hb x
  dsimp only [CenteredRectangleDiskConstruction.M] at *
  change (‖F x‖ ≤ M * ‖x‖)
  by_cases hx : x = 0
  · simp [hx, hF_zero]
  · rw [hF_norm]
    exact mul_le_mul_of_nonneg_right
      ((div_le_iff₀ (hg_pos x hx)).mpr (hg_lower x)) (norm_nonneg x)

private theorem hG_bound (J : Finset Nat) (hJ : J.Nonempty) (a : Nat → ℝ) (b : Nat → ℝ) (ha : ∀ j
    ∈ J, 0 < a j) (hb : ∀ j ∈ J, 0 < b j) (x : ℝ × ℝ) : ‖(G J hJ a b) x‖ ≤ (C J hJ a b) * ‖x‖ := by
  classical
  let q : Nat → (ℝ × ℝ) → ℝ := fun j x => max (|x.1| / a j) (|x.2| / b j)
  let g : (ℝ × ℝ) → ℝ := fun x => J.inf' hJ (fun j => q j x)
  let R : (ℝ × ℝ) → ℝ := fun x => J.sup' hJ (fun j => (q j x)⁻¹)
  let j₀ := hJ.choose
  let C := max (a j₀)⁻¹ (b j₀)⁻¹
  have hg_upper (x : ℝ × ℝ) : g x ≤ C * ‖x‖ := hg_upper J hJ a b ha hb x
  let G : (ℝ × ℝ) → (ℝ × ℝ) := fun x => (R (‖x‖⁻¹ • x))⁻¹ • x
  have hG_norm (x : ℝ × ℝ) : ‖G x‖ = g x := hG_norm J hJ a b ha hb x
  change (‖G x‖ ≤ C * ‖x‖)
  rw [hG_norm]
  exact hg_upper x

private theorem hradial_cont (f : (ℝ × ℝ) → (ℝ × ℝ)) (K : ℝ) (hK : 0 ≤ K)
      (hf0 : f 0 = 0) (hf_bound : ∀ x, ‖f x‖ ≤ K * ‖x‖)
      (hf_off : ∀ x, x ≠ 0 → ContinuousAt f x) : Continuous f := by
  classical
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : x = 0
  · subst x
    apply Metric.continuousAt_iff.mpr
    intro ε hε
    refine ⟨ε / (K + 1), div_pos hε (by linarith), ?_⟩
    intro x hx
    rw [dist_zero_right] at hx
    rw [hf0, dist_zero_right]
    apply lt_of_le_of_lt (hf_bound x)
    have hh := (lt_div_iff₀ (by linarith : 0 < K + 1)).mp hx
    nlinarith [norm_nonneg x]
  · exact hf_off x hx

private theorem hF_cont (J : Finset Nat) (hJ : J.Nonempty) (a : Nat → ℝ) (b : Nat → ℝ) (ha : ∀ j
    ∈ J, 0 < a j) (hb : ∀ j ∈ J, 0 < b j) : Continuous (F J hJ a b) := by
  classical
  let q : Nat → (ℝ × ℝ) → ℝ := fun j x => max (|x.1| / a j) (|x.2| / b j)
  let g : (ℝ × ℝ) → ℝ := fun x => J.inf' hJ (fun j => q j x)
  let R : (ℝ × ℝ) → ℝ := fun x => J.sup' hJ (fun j => (q j x)⁻¹)
  have hg_pos (x : ℝ × ℝ) (hx : x ≠ 0) : 0 < g x := hg_pos J hJ a b ha hb x hx
  have hg_cont : Continuous g := hg_cont J hJ a b
  let M := J.sup' hJ (fun j => max (a j) (b j))
  have hM_pos : 0 < M := hM_pos J hJ a b ha
  let F : (ℝ × ℝ) → (ℝ × ℝ) := fun x => R (‖x‖⁻¹ • x) • x
  have hF_zero : F 0 = 0 := hF_zero J hJ a b
  have hF_formula (x : ℝ × ℝ) : F x = (‖x‖ / g x) • x := hF_formula J hJ a b ha hb x
  have hF_bound (x : ℝ × ℝ) : ‖F x‖ ≤ M * ‖x‖ := hF_bound J hJ a b ha hb x
  have hradial_cont (f : (ℝ × ℝ) → (ℝ × ℝ)) (K : ℝ) (hK : 0 ≤ K)
      (hf0 : f 0 = 0) (hf_bound : ∀ x, ‖f x‖ ≤ K * ‖x‖)
      (hf_off : ∀ x, x ≠ 0 → ContinuousAt f x) : Continuous f := hradial_cont f K hK hf0 hf_bound
          hf_off
  change (Continuous F)
  have he : F = fun x => (‖x‖ / g x) • x := funext hF_formula
  apply hradial_cont F M hM_pos.le hF_zero hF_bound
  intro x hx
  rw [he]
  exact (continuous_norm.continuousAt.div hg_cont.continuousAt
    (hg_pos x hx).ne').smul continuousAt_id

private theorem hG_cont (J : Finset Nat) (hJ : J.Nonempty) (a : Nat → ℝ) (b : Nat → ℝ) (ha : ∀ j
    ∈ J, 0 < a j) (hb : ∀ j ∈ J, 0 < b j) : Continuous (G J hJ a b) := by
  classical
  let q : Nat → (ℝ × ℝ) → ℝ := fun j x => max (|x.1| / a j) (|x.2| / b j)
  let g : (ℝ × ℝ) → ℝ := fun x => J.inf' hJ (fun j => q j x)
  let R : (ℝ × ℝ) → ℝ := fun x => J.sup' hJ (fun j => (q j x)⁻¹)
  have hg_cont : Continuous g := hg_cont J hJ a b
  let j₀ := hJ.choose
  let C := max (a j₀)⁻¹ (b j₀)⁻¹
  have hC_pos : 0 < C := hC_pos J hJ a b ha
  let G : (ℝ × ℝ) → (ℝ × ℝ) := fun x => (R (‖x‖⁻¹ • x))⁻¹ • x
  have hG_zero : G 0 = 0 := hG_zero J hJ a b
  have hG_formula (x : ℝ × ℝ) : G x = (g x / ‖x‖) • x := hG_formula J hJ a b ha hb x
  have hG_bound (x : ℝ × ℝ) : ‖G x‖ ≤ C * ‖x‖ := hG_bound J hJ a b ha hb x
  have hradial_cont (f : (ℝ × ℝ) → (ℝ × ℝ)) (K : ℝ) (hK : 0 ≤ K)
      (hf0 : f 0 = 0) (hf_bound : ∀ x, ‖f x‖ ≤ K * ‖x‖)
      (hf_off : ∀ x, x ≠ 0 → ContinuousAt f x) : Continuous f := hradial_cont f K hK hf0 hf_bound
          hf_off
  change (Continuous G)
  have he : G = fun x => (g x / ‖x‖) • x := funext hG_formula
  apply hradial_cont G C hC_pos.le hG_zero hG_bound
  intro x hx
  rw [he]
  exact (hg_cont.continuousAt.div continuous_norm.continuousAt
    (norm_ne_zero_iff.mpr hx)).smul continuousAt_id

private noncomputable abbrev H (J : Finset Nat) (hJ : J.Nonempty) (c : ℝ × ℝ) (a : Nat → ℝ) (b :
    Nat → ℝ) (ha : ∀ j ∈ J, 0 < a j) (hb : ∀ j ∈ J, 0 < b j) : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) := by
  classical
  let q : Nat → (ℝ × ℝ) → ℝ := fun j x => max (|x.1| / a j) (|x.2| / b j)
  let R : (ℝ × ℝ) → ℝ := fun x => J.sup' hJ (fun j => (q j x)⁻¹)
  let F : (ℝ × ℝ) → (ℝ × ℝ) := fun x => R (‖x‖⁻¹ • x) • x
  let G : (ℝ × ℝ) → (ℝ × ℝ) := fun x => (R (‖x‖⁻¹ • x))⁻¹ • x
  have hGF (x : ℝ × ℝ) : G (F x) = x := hGF J hJ a b ha hb x
  have hFG (x : ℝ × ℝ) : F (G x) = x := hFG J hJ a b ha hb x
  have hF_cont : Continuous F := hF_cont J hJ a b ha hb
  have hG_cont : Continuous G := hG_cont J hJ a b ha hb
  exact {
      toFun := fun x => c + F x
      invFun := fun x => G (x - c)
      left_inv := fun x => by simpa using hGF x
      right_inv := fun x => by
        change c + F (G (x - c)) = x
        rw [hFG]
        simp
      continuous_toFun := continuous_const.add hF_cont
      continuous_invFun := hG_cont.comp (continuous_id.sub continuous_const) }

end CenteredRectangleDiskConstruction

theorem P3092T1CenteredRectangleDisk
    (J : Finset Nat) (hJ : J.Nonempty) (c : Real × Real)
    (a b : Nat → Real)
    (ha : ∀ j ∈ J, 0 < a j) (hb : ∀ j ∈ J, 0 < b j) :
    TopologicalDisk
      (⋃ j ∈ J,
        Set.Icc (c.1 - a j, c.2 - b j) (c.1 + a j, c.2 + b j)) := by
-- BODY
  classical
  let q : Nat → (ℝ × ℝ) → ℝ := fun j x => max (|x.1| / a j) (|x.2| / b j)
  let g : (ℝ × ℝ) → ℝ := fun x => J.inf' hJ (fun j => q j x)
  let R : (ℝ × ℝ) → ℝ := fun x => J.sup' hJ (fun j => (q j x)⁻¹)
  have hq_nonneg (j : Nat) (hj : j ∈ J) (x : ℝ × ℝ) : 0 ≤ q j x :=
      CenteredRectangleDiskConstruction.hq_nonneg J a b ha j hj x
  have hq_pos (j : Nat) (hj : j ∈ J) (x : ℝ × ℝ) (hx : x ≠ 0) : 0 < q j x :=
      CenteredRectangleDiskConstruction.hq_pos J a b ha hb j hj x hx
  have hg_nonneg (x : ℝ × ℝ) : 0 ≤ g x := CenteredRectangleDiskConstruction.hg_nonneg J hJ a b ha x
  have hg_pos (x : ℝ × ℝ) (hx : x ≠ 0) : 0 < g x := CenteredRectangleDiskConstruction.hg_pos J hJ
      a b ha hb x hx
  have hg_zero : g 0 = 0 := CenteredRectangleDiskConstruction.hg_zero J hJ a b
  have hq_smul (t : ℝ) (ht : 0 ≤ t) (j : Nat) (x : ℝ × ℝ) :
      q j (t • x) = t * q j x := CenteredRectangleDiskConstruction.hq_smul a b t ht j x
  have hg_smul (t : ℝ) (ht : 0 ≤ t) (x : ℝ × ℝ) : g (t • x) = t * g x :=
      CenteredRectangleDiskConstruction.hg_smul J hJ a b t ht x
  have hg_cont : Continuous g := CenteredRectangleDiskConstruction.hg_cont J hJ a b
  -- The reciprocal of the minimum gauge is the attained outer ray radius.
  have hR_eq (x : ℝ × ℝ) (hx : x ≠ 0) : R x = (g x)⁻¹ := CenteredRectangleDiskConstruction.hR_eq
      J hJ a b ha hb x hx
  have hR_attained (x : ℝ × ℝ) : ∃ j ∈ J, R x = (q j x)⁻¹ :=
      CenteredRectangleDiskConstruction.hR_attained J hJ a b x
  have hR_pos (x : ℝ × ℝ) (hx : x ≠ 0) : 0 < R x := CenteredRectangleDiskConstruction.hR_pos J hJ
      a b ha hb x hx
  have hR_cont (x : ℝ × ℝ) (hx : x ≠ 0) : ContinuousAt R x :=
      CenteredRectangleDiskConstruction.hR_cont J hJ a b ha hb x hx
  have hmem (x : ℝ × ℝ) :
      c + x ∈ (⋃ j ∈ J, Set.Icc (c.1 - a j, c.2 - b j)
          (c.1 + a j, c.2 + b j)) ↔ g x ≤ 1 := CenteredRectangleDiskConstruction.hmem J hJ c a b
              ha hb x
  have hray (u : ℝ × ℝ) (hu : ‖u‖ = 1) (t : ℝ) (ht : 0 ≤ t) :
      c + t • u ∈ (⋃ j ∈ J, Set.Icc (c.1 - a j, c.2 - b j)
          (c.1 + a j, c.2 + b j)) ↔ t ≤ R u := CenteredRectangleDiskConstruction.hray J hJ c a b
              ha hb u hu t ht
  -- Uniform bounds suffice for continuity at the center in both directions.
  let j₀ := hJ.choose
  have hj₀ : j₀ ∈ J := CenteredRectangleDiskConstruction.hj₀ J hJ
  let M := J.sup' hJ (fun j => max (a j) (b j))
  let C := max (a j₀)⁻¹ (b j₀)⁻¹
  have hM_pos : 0 < M := CenteredRectangleDiskConstruction.hM_pos J hJ a b ha
  have hC_pos : 0 < C := CenteredRectangleDiskConstruction.hC_pos J hJ a b ha
  have hq_bound (j : Nat) (hj : j ∈ J) (x : ℝ × ℝ) : ‖x‖ ≤ M * q j x :=
      CenteredRectangleDiskConstruction.hq_bound J hJ a b ha hb j hj x
  have hg_lower (x : ℝ × ℝ) : ‖x‖ ≤ M * g x := CenteredRectangleDiskConstruction.hg_lower J hJ a
      b ha hb x
  have hg_upper (x : ℝ × ℝ) : g x ≤ C * ‖x‖ := CenteredRectangleDiskConstruction.hg_upper J hJ a
      b ha hb x
  have hunit (x : ℝ × ℝ) (hx : x ≠ 0) : ‖‖x‖⁻¹ • x‖ = 1 :=
      CenteredRectangleDiskConstruction.hunit x hx
  have hR_normalized (x : ℝ × ℝ) (hx : x ≠ 0) : R (‖x‖⁻¹ • x) = ‖x‖ / g x :=
      CenteredRectangleDiskConstruction.hR_normalized J hJ a b ha hb x hx
  let F : (ℝ × ℝ) → (ℝ × ℝ) := fun x => R (‖x‖⁻¹ • x) • x
  let G : (ℝ × ℝ) → (ℝ × ℝ) := fun x => (R (‖x‖⁻¹ • x))⁻¹ • x
  have hF_zero : F 0 = 0 := CenteredRectangleDiskConstruction.hF_zero J hJ a b
  have hG_zero : G 0 = 0 := CenteredRectangleDiskConstruction.hG_zero J hJ a b
  have hF_formula (x : ℝ × ℝ) : F x = (‖x‖ / g x) • x :=
      CenteredRectangleDiskConstruction.hF_formula J hJ a b ha hb x
  have hG_formula (x : ℝ × ℝ) : G x = (g x / ‖x‖) • x :=
      CenteredRectangleDiskConstruction.hG_formula J hJ a b ha hb x
  have hF_norm (x : ℝ × ℝ) : ‖F x‖ = (‖x‖ / g x) * ‖x‖ :=
      CenteredRectangleDiskConstruction.hF_norm J hJ a b ha hb x
  have hG_norm (x : ℝ × ℝ) : ‖G x‖ = g x := CenteredRectangleDiskConstruction.hG_norm J hJ a b ha
      hb x
  have hgF (x : ℝ × ℝ) : g (F x) = ‖x‖ := CenteredRectangleDiskConstruction.hgF J hJ a b ha hb x
  have hGF (x : ℝ × ℝ) : G (F x) = x := CenteredRectangleDiskConstruction.hGF J hJ a b ha hb x
  have hFG (x : ℝ × ℝ) : F (G x) = x := CenteredRectangleDiskConstruction.hFG J hJ a b ha hb x
  have hF_bound (x : ℝ × ℝ) : ‖F x‖ ≤ M * ‖x‖ := CenteredRectangleDiskConstruction.hF_bound J hJ
      a b ha hb x
  have hG_bound (x : ℝ × ℝ) : ‖G x‖ ≤ C * ‖x‖ := CenteredRectangleDiskConstruction.hG_bound J hJ
      a b ha hb x
  have hradial_cont (f : (ℝ × ℝ) → (ℝ × ℝ)) (K : ℝ) (hK : 0 ≤ K)
      (hf0 : f 0 = 0) (hf_bound : ∀ x, ‖f x‖ ≤ K * ‖x‖)
      (hf_off : ∀ x, x ≠ 0 → ContinuousAt f x) : Continuous f :=
          CenteredRectangleDiskConstruction.hradial_cont f K hK hf0 hf_bound hf_off
  have hF_cont : Continuous F := CenteredRectangleDiskConstruction.hF_cont J hJ a b ha hb
  have hG_cont : Continuous G := CenteredRectangleDiskConstruction.hG_cont J hJ a b ha hb
  let H : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) :=
    { toFun := fun x => c + F x
      invFun := fun x => G (x - c)
      left_inv := fun x => by simpa using hGF x
      right_inv := fun x => by
        change c + F (G (x - c)) = x
        rw [hFG]
        simp
      continuous_toFun := continuous_const.add hF_cont
      continuous_invFun := hG_cont.comp (continuous_id.sub continuous_const) }
  refine ⟨H.subtype ?_⟩
  intro x
  change x ∈ Metric.closedBall (0 : ℝ × ℝ) 1 ↔ c + F x ∈ _
  rw [hmem, hgF, Metric.mem_closedBall, dist_zero_right]

end ApollonianSuperharmonic

end
