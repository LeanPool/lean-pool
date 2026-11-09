/-
Copyright (c) 2026 Stefanos Lappas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefanos Lappas
-/
module

public import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Int
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Choose
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Tauto

/-!
# Dyadic geometry and multilinear testing conditions

This project formalizes Mirek and Thiele's perfect multilinear local T(1) and T(b)
theorems, together with a global variant for locally dyadic testing functions.
The source is *A local T(b) theorem for perfect multilinear Calderón–Zygmund
operators*, Proc. London Math. Soc. 114 (2017), 35–59, doi:10.1112/plms.12000.

This module develops dyadic cubes, test functions, perfect forms, admissible
paths, stopping times, pruning, and the outer-measure formulation of Carleson
embedding. `Estimates` proves the analytic bounds, `Contraction` assembles the
stopping argument, and `T1Theorem` closes the testing theorems.

The global variant uses scale-normalized weak boundedness, locally dyadic
pseudo-accretive functions, and BMO testing restricted to functions with
integrable dyadic square function. These choices are stated in
`GlobalTbHypotheses`; they differ from the literal presentation of Theorem 1.11.

The upstream formalization was written by Claude Code under Stefanos Lappas's
mathematical direction, at the Mathematical Institute of the University of Bonn,
with support from ERC Synergy grant HALF 101224275.
-/

@[expose] public section

open MeasureTheory

namespace MirekThiele

/-! ## §0 Dyadic cubes in `ℝ^d` (paper, p. 35) -/

/-- A dyadic cube in `ℝ^d`: the product `∏ᵢ [2^m lᵢ, 2^m (lᵢ + 1))` with `m ∈ ℤ`,
`l ∈ ℤ^d`. -/
@[ext]
structure DyadicCube (d : ℕ) where
  /-- the scale: the side length is `2^m` -/
  m : ℤ
  /-- the integer position -/
  l : Fin d → ℤ

deriving instance DecidableEq for DyadicCube

namespace DyadicCube

variable {d : ℕ}

/-- The side length `ℓ(P) = 2^m`. -/
noncomputable def side (P : DyadicCube d) : ℝ := (2 : ℝ) ^ P.m

/-- The cube as a subset of `ℝ^d = (Fin d → ℝ)`. -/
def toSet (P : DyadicCube d) : Set (Fin d → ℝ) :=
  {x | ∀ i, (2 : ℝ) ^ P.m * P.l i ≤ x i ∧ x i < (2 : ℝ) ^ P.m * (P.l i + 1)}

/-- The Lebesgue measure `|P| = 2^{md}`. -/
noncomputable def vol (P : DyadicCube d) : ℝ := (2 : ℝ) ^ (P.m * d)

/-- The dyadic child of `P` selected by `ε ∈ {0,1}^d`. -/
def child (P : DyadicCube d) (ε : Fin d → Bool) : DyadicCube d :=
  ⟨P.m - 1, fun i => 2 * P.l i + if ε i then 1 else 0⟩

/-- The dyadic parent `parents(P)` of `P`. -/
def parent (P : DyadicCube d) : DyadicCube d := ⟨P.m + 1, fun i => P.l i / 2⟩

/-- The child of `P` containing `x` (meaningful for `x ∈ P`). -/
noncomputable def childAt (P : DyadicCube d) (x : Fin d → ℝ) : DyadicCube d :=
  P.child fun i => decide ((2 : ℝ) ^ (P.m - 1) * (2 * P.l i + 1) ≤ x i)

/-- The characteristic function `𝟙_P`. -/
noncomputable def indicator (P : DyadicCube d) : (Fin d → ℝ) → ℝ := P.toSet.indicator 1

/-- `𝒟(T)`: the dyadic cubes contained in `T`. -/
def tree (T : DyadicCube d) : Set (DyadicCube d) := {Q | Q.toSet ⊆ T.toSet}

/-- `|P| > 0`. [PROVED] -/
theorem vol_pos (P : DyadicCube d) : 0 < P.vol := zpow_pos (by norm_num) _

/-- The parent of a child is the cube itself. [PROVED] -/
theorem parent_child (P : DyadicCube d) (ε : Fin d → Bool) : (P.child ε).parent = P := by
  ext i
  · simp [child, parent]
  · simp only [child, parent]
    split_ifs <;> omega

/-- Each child has measure `2^{-d} |P|`. [PROVED] -/
theorem vol_child (P : DyadicCube d) (ε : Fin d → Bool) :
    (P.child ε).vol * 2 ^ d = P.vol := by
  simp only [vol, child]
  rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  congr 1
  ring

/-- A child is contained in its parent. [PROVED] -/
theorem child_subset (P : DyadicCube d) (ε : Fin d → Bool) : (P.child ε).toSet ⊆ P.toSet := by
  intro x hx
  change ∀ i, (2 : ℝ) ^ P.m * P.l i ≤ x i ∧ x i < (2 : ℝ) ^ P.m * (P.l i + 1)
  intro i
  obtain ⟨h1, h2⟩ := hx i
  simp only [child] at h1 h2
  have h2m : (2 : ℝ) ^ P.m = 2 * (2 : ℝ) ^ (P.m - 1) := by
    rw [zpow_sub_one₀ (by norm_num : (2 : ℝ) ≠ 0)]
    ring
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (P.m - 1) := zpow_pos (by norm_num) _
  rw [h2m]
  split_ifs at h1 h2 <;> push_cast at h1 h2 <;> constructor <;> nlinarith [hpos]

/-- The corner `2^m l` of a cube lies in the cube. [PROVED] -/
theorem corner_mem (P : DyadicCube d) : (fun i => (2 : ℝ) ^ P.m * P.l i) ∈ P.toSet := by
  change ∀ i, (2 : ℝ) ^ P.m * P.l i ≤ (2 : ℝ) ^ P.m * P.l i ∧
    (2 : ℝ) ^ P.m * P.l i < (2 : ℝ) ^ P.m * (P.l i + 1)
  intro i
  have hpos : (0 : ℝ) < (2 : ℝ) ^ P.m := zpow_pos (by norm_num) _
  exact ⟨le_rfl, by nlinarith [hpos]⟩

/-- Membership in a dyadic cube through integer parts: `x ∈ P ↔ ∀ i, ⌊xᵢ / 2^m⌋ = lᵢ`.
[PROVED] -/
theorem mem_toSet_iff (P : DyadicCube d) (x : Fin d → ℝ) :
    x ∈ P.toSet ↔ ∀ i, ⌊x i / (2 : ℝ) ^ P.m⌋ = P.l i := by
  have hpos : (0 : ℝ) < (2 : ℝ) ^ P.m := zpow_pos (by norm_num) _
  change (∀ i, (2 : ℝ) ^ P.m * P.l i ≤ x i ∧ x i < (2 : ℝ) ^ P.m * (P.l i + 1)) ↔ _
  refine forall_congr' fun i => ?_
  rw [Int.floor_eq_iff, le_div_iff₀ hpos, div_lt_iff₀ hpos]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, by linarith⟩

/-- Two dyadic cubes with `ℓ(P) ≤ ℓ(R)` are either nested or disjoint. [PROVED] -/
theorem subset_or_disjoint (P R : DyadicCube d) (h : P.m ≤ R.m) :
    P.toSet ⊆ R.toSet ∨ Disjoint P.toSet R.toSet := by
  obtain ⟨t, ht⟩ : ∃ t : ℕ, (t : ℝ) = (2 : ℝ) ^ (R.m - P.m) :=
    ⟨2 ^ (R.m - P.m).toNat, by
      rw [Nat.cast_pow, Nat.cast_ofNat, ← zpow_natCast, Int.toNat_of_nonneg (by omega)]⟩
  have key : ∀ x ∈ P.toSet, ∀ i, ⌊x i / (2 : ℝ) ^ R.m⌋ = P.l i / t := by
    intro x hx i
    rw [mem_toSet_iff] at hx
    rw [← hx i, ← Int.floor_div_natCast, ht, div_div, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),
      show P.m + (R.m - P.m) = R.m by ring]
  by_cases hl : ∀ i, P.l i / t = R.l i
  · left
    intro x hx
    rw [mem_toSet_iff]
    intro i
    rw [key x hx i, hl i]
  · right
    rw [not_forall] at hl
    obtain ⟨i, hi⟩ := hl
    rw [Set.disjoint_left]
    intro x hxP hxR
    rw [mem_toSet_iff] at hxR
    exact hi ((key x hxP i).symm.trans (hxR i))

/-- Two dyadic cubes of the same side length are equal or disjoint. [PROVED] -/
theorem eq_or_disjoint_of_m_eq (P R : DyadicCube d) (h : P.m = R.m) :
    P = R ∨ Disjoint P.toSet R.toSet := by
  rcases subset_or_disjoint P R h.le with hsub | hdis
  · left
    have hc := hsub (corner_mem P)
    rw [mem_toSet_iff] at hc
    ext i
    · exact h
    · have := hc i
      rw [← h, mul_div_cancel_left₀ _ (zpow_pos (by norm_num) _).ne', Int.floor_intCast] at this
      exact this
  · right
    exact hdis

/-- Distinct `ε` give distinct children. [PROVED] -/
theorem child_injective (P : DyadicCube d) : Function.Injective P.child := by
  intro ε ε' h
  funext i
  have h1 := congrArg (fun Q : DyadicCube d => Q.l i) h
  simp only [child] at h1
  have h2 : (if ε i then (1 : ℤ) else 0) = if ε' i then 1 else 0 := by linarith
  revert h2
  cases ε i <;> cases ε' i <;> simp

/-- Distinct children of a cube are disjoint. [PROVED] -/
theorem child_disjoint (P : DyadicCube d) {ε ε' : Fin d → Bool} (h : ε ≠ ε') :
    Disjoint (P.child ε).toSet (P.child ε').toSet :=
  (eq_or_disjoint_of_m_eq (P.child ε) (P.child ε') rfl).resolve_left fun h' =>
    h (P.child_injective h')

/-- A point of `P` lies in the child `childAt P x`. [PROVED] -/
theorem mem_childAt (P : DyadicCube d) {x : Fin d → ℝ} (hx : x ∈ P.toSet) :
    x ∈ (P.childAt x).toSet := by
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (P.m - 1) := zpow_pos (by norm_num) _
  have h2m : (2 : ℝ) ^ P.m = 2 * (2 : ℝ) ^ (P.m - 1) := by
    rw [zpow_sub_one₀ (by norm_num : (2 : ℝ) ≠ 0)]
    ring
  have key : ∀ i, (2 : ℝ) ^ (P.m - 1) * ((P.childAt x).l i) ≤ x i ∧
      x i < (2 : ℝ) ^ (P.m - 1) * ((P.childAt x).l i + 1) := by
    intro i
    obtain ⟨h1, h2⟩ := hx i
    rw [h2m] at h1 h2
    simp only [childAt, child]
    split_ifs with hc <;> simp only [decide_eq_true_eq] at hc <;> push_cast <;>
      constructor <;> nlinarith [hpos]
  exact key

/-- The children of a cube cover the cube. [PROVED] -/
theorem iUnion_child (P : DyadicCube d) : ⋃ ε, (P.child ε).toSet = P.toSet := by
  apply Set.Subset.antisymm
  · exact Set.iUnion_subset fun ε => P.child_subset ε
  · intro x hx
    exact Set.mem_iUnion.mpr ⟨_, P.mem_childAt hx⟩

/-- A dyadic cube is a product of half-open intervals. [PROVED] -/
theorem toSet_eq_pi (P : DyadicCube d) :
    P.toSet = Set.pi Set.univ
      (fun i => Set.Ico ((2 : ℝ) ^ P.m * P.l i) ((2 : ℝ) ^ P.m * (P.l i + 1))) := by
  ext x
  simp only [Set.mem_univ_pi, Set.mem_Ico]
  rfl

/-- The Lebesgue measure of a dyadic cube is `|P| = 2^{md}`. [PROVED] -/
theorem volume_toSet (P : DyadicCube d) : volume P.toSet = ENNReal.ofReal P.vol := by
  rw [toSet_eq_pi, volume_pi_pi]
  have h : ∀ i : Fin d, (2 : ℝ) ^ P.m * (P.l i + 1) - (2 : ℝ) ^ P.m * P.l i = (2 : ℝ) ^ P.m :=
    fun i => by ring
  simp only [Real.volume_Ico, h, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← ENNReal.ofReal_pow (zpow_pos (by norm_num) _).le, vol, ← zpow_natCast, ← zpow_mul]

/-- `Q ∈ 𝒟(T)` iff `Q ⊆ T`. -/
theorem mem_tree {Q T : DyadicCube d} : Q ∈ T.tree ↔ Q.toSet ⊆ T.toSet := Iff.rfl

/-- Dyadic cubes are measurable. [PROVED] -/
theorem measurableSet_toSet (P : DyadicCube d) : MeasurableSet P.toSet := by
  rw [toSet_eq_pi]
  exact MeasurableSet.univ_pi fun _ => measurableSet_Ico

/-- Dyadic cubes carry the discrete σ-algebra (used only to invoke Hölder's and Minkowski's
inequalities for `lintegral` with respect to counting measure). -/
instance : MeasurableSpace (DyadicCube d) := ⊤

instance : DiscreteMeasurableSpace (DyadicCube d) := ⟨fun _ => MeasurableSpace.measurableSet_top⟩

/-- `P ⊆ R` implies `|P| ≤ |R|`. [PROVED] -/
theorem vol_le_of_subset {P R : DyadicCube d} (h : P.toSet ⊆ R.toSet) :
    P.vol ≤ R.vol := by
  have := measure_mono (μ := volume) h
  rwa [P.volume_toSet, R.volume_toSet, ENNReal.ofReal_le_ofReal_iff R.vol_pos.le] at this

/-- `P ⊆ R` implies `ℓ(P) ≤ ℓ(R)` (for `d ≥ 1`). [PROVED] -/
theorem m_le_of_subset (hd : d ≠ 0) {P R : DyadicCube d} (h : P.toSet ⊆ R.toSet) :
    P.m ≤ R.m := by
  have h1 := DyadicCube.vol_le_of_subset h
  simp only [DyadicCube.vol] at h1
  rw [zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)] at h1
  have hd' : (0 : ℤ) < d := by exact_mod_cast Nat.pos_of_ne_zero hd
  exact le_of_mul_le_mul_right h1 hd'

/-- A subcube of the same side length is the cube itself. [PROVED] -/
theorem eq_of_subset_of_m_eq {P R : DyadicCube d} (h : P.toSet ⊆ R.toSet)
    (hm : P.m = R.m) : P = R :=
  (DyadicCube.eq_or_disjoint_of_m_eq P R hm).resolve_right fun hdis =>
    Set.disjoint_left.mp hdis P.corner_mem (h P.corner_mem)

/-- A proper subcube of `T` is contained in a child of `T` (for `d ≥ 1`). [PROVED] -/
theorem exists_child_of_ssubset (hd : d ≠ 0) {Q T : DyadicCube d}
    (hQT : Q.toSet ⊆ T.toSet) (hne : Q ≠ T) : ∃ ε, Q.toSet ⊆ (T.child ε).toSet := by
  have hm : Q.m < T.m := lt_of_le_of_ne (DyadicCube.m_le_of_subset hd hQT)
    fun h => hne (DyadicCube.eq_of_subset_of_m_eq hQT h)
  have hc := hQT Q.corner_mem
  rw [← T.iUnion_child, Set.mem_iUnion] at hc
  obtain ⟨ε, hε⟩ := hc
  refine ⟨ε, ?_⟩
  rcases DyadicCube.subset_or_disjoint Q (T.child ε) (by simp only [DyadicCube.child]; omega)
    with h | h
  · exact h
  · exact absurd hε (Set.disjoint_left.mp h Q.corner_mem)

/-- Every cube is a child of its parent. [PROVED] -/
theorem child_parent (P : DyadicCube d) :
    P.parent.child (fun i => decide (P.l i % 2 = 1)) = P := by
  ext i
  · simp [DyadicCube.child, DyadicCube.parent]
  · simp only [DyadicCube.child, DyadicCube.parent]
    split_ifs with h
    · simp only [decide_eq_true_eq] at h
      omega
    · simp only [decide_eq_true_eq] at h
      omega

/-- `|Q̂| = 2^d |Q|`. [PROVED] -/
theorem vol_parent (Q : DyadicCube d) : Q.parent.vol = 2 ^ d * Q.vol := by
  have := Q.parent.vol_child (fun i => decide (Q.l i % 2 = 1))
  rw [Q.child_parent] at this
  rw [← this]
  ring

/-- The integral over a cube is the sum of the integrals over its children. [PROVED] -/
theorem integral_children (Q : DyadicCube d) {g : (Fin d → ℝ) → ℝ}
    (hg : IntegrableOn g Q.toSet volume) :
    ∫ x in Q.toSet, g x = ∑ ε : Fin d → Bool, ∫ x in (Q.child ε).toSet, g x := by
  have hU : (⋃ ε ∈ (Finset.univ : Finset (Fin d → Bool)), (Q.child ε).toSet) = Q.toSet := by
    rw [← Q.iUnion_child]
    ext x
    simp
  have := integral_biUnion_finset (μ := volume) (f := g) Finset.univ
    (fun ε _ => (Q.child ε).measurableSet_toSet)
    (fun ε _ ε' _ hne => Q.child_disjoint hne)
    (fun ε _ => hg.mono_set (Q.child_subset ε))
  rwa [hU] at this

end DyadicCube

/-! ## §0' Dyadic test functions, norms, averages -/

variable {d : ℕ}

/-- Dyadic test functions on `ℝ^d`: finite linear combinations of characteristic functions
of dyadic cubes. -/
noncomputable def TestFun (d : ℕ) : Submodule ℝ ((Fin d → ℝ) → ℝ) :=
  Submodule.span ℝ (Set.range (DyadicCube.indicator (d := d)))

/-- `𝟙_P` is a dyadic test function. [PROVED] -/
theorem indicator_mem_testFun (P : DyadicCube d) : P.indicator ∈ TestFun d :=
  Submodule.subset_span ⟨P, rfl⟩

/-- `g` is supported on the cube `P`. -/
def SupportedOn (g : (Fin d → ℝ) → ℝ) (P : DyadicCube d) : Prop :=
  ∀ x, x ∉ P.toSet → g x = 0

/-- `g` vanishes on the cube `P`. -/
def VanishesOn (g : (Fin d → ℝ) → ℝ) (P : DyadicCube d) : Prop :=
  ∀ x ∈ P.toSet, g x = 0

/-- `g` has mean zero. -/
def MeanZero (g : (Fin d → ℝ) → ℝ) : Prop := ∫ x, g x = 0

/-- The average `[g]_P = |P|⁻¹ ∫_P g`. -/
noncomputable def avg (P : DyadicCube d) (g : (Fin d → ℝ) → ℝ) : ℝ :=
  (∫ x in P.toSet, g x) / P.vol

/-- `[g]_P |P| = ∫_P g`. [PROVED] -/
theorem avg_mul_vol (P : DyadicCube d) (g : (Fin d → ℝ) → ℝ) :
    avg P g * P.vol = ∫ x in P.toSet, g x := by
  rw [avg, div_mul_cancel₀ _ P.vol_pos.ne']

/-- Lebesgue measure restricted to a dyadic cube is finite. -/
instance (Q : DyadicCube d) : IsFiniteMeasure (volume.restrict Q.toSet) :=
  isFiniteMeasure_restrict.mpr (by rw [DyadicCube.volume_toSet]; exact ENNReal.ofReal_ne_top)

/-- The truncation `g_P = g 𝟙_P`. -/
noncomputable def truncate (P : DyadicCube d) (g : (Fin d → ℝ) → ℝ) : (Fin d → ℝ) → ℝ :=
  P.toSet.indicator g

/-- The `L^p` norm `‖g‖_p` (as a real number). -/
noncomputable def lpNorm (g : (Fin d → ℝ) → ℝ) (p : ℝ) : ℝ :=
  (eLpNorm g (ENNReal.ofReal p) volume).toReal

/-- The `L^∞` norm `‖g‖_∞` (as a real number). -/
noncomputable def supNorm (g : (Fin d → ℝ) → ℝ) : ℝ :=
  (eLpNorm g ⊤ volume).toReal

/-- A Hölder tuple of finite exponents: `1 < p_j < ∞` and `∑ 1/p_j = 1`. -/
structure HolderTuple (n : ℕ) where
  /-- the exponents -/
  p : Fin n → ℝ
  one_lt : ∀ j, 1 < p j
  sum_inv : ∑ j, (p j)⁻¹ = 1

/-- The product `∏_j ‖f_j‖_{p_j}`. -/
noncomputable def prodNorm {n : ℕ} (p : HolderTuple n) (f : Fin n → TestFun d) : ℝ :=
  ∏ j, lpNorm (f j : (Fin d → ℝ) → ℝ) (p.p j)

/-- Products of `n` dyadic cubes in `ℝ^d` with a common side length, i.e. dyadic cubes in
`ℝ^{dn}`. -/
def DyadicCube.prodSet {n : ℕ} (P : Fin n → DyadicCube d) : Set (Fin n → Fin d → ℝ) :=
  {x | ∀ j, x j ∈ (P j).toSet}

/-- Dyadic test functions on `ℝ^{dn}`. -/
noncomputable def TestFunProd (d n : ℕ) : Submodule ℝ ((Fin n → Fin d → ℝ) → ℝ) :=
  Submodule.span ℝ {K | ∃ P : Fin n → DyadicCube d,
    (∀ i j, (P i).m = (P j).m) ∧ K = (DyadicCube.prodSet P).indicator 1}

/-! ## §1 Perfect Calderón–Zygmund forms (paper, p. 35–36, conditions (i)–(iii)) -/

/-- A perfect `n`-linear Calderón–Zygmund form on `ℝ^d`. -/
structure PerfectCZForm (d n : ℕ) where
  /-- the `n`-linear form `Λ` on dyadic test functions -/
  form : MultilinearMap ℝ (fun _ : Fin n => TestFun d) ℝ
  /-- (i) dyadic decay (1.1): for every Hölder tuple, if all `f_j` are supported on `P` and two
  of them on different children of `P`, then `|Λ(f)| ≤ ∏ ‖f_j‖_{p_j}`. -/
  decay : ∀ (p : HolderTuple n) (P : DyadicCube d) (f : Fin n → TestFun d),
    (∀ j, SupportedOn (f j) P) →
    (∃ i j : Fin n, i ≠ j ∧ ∃ ε ε' : Fin d → Bool, ε ≠ ε' ∧
      SupportedOn (f i) (P.child ε) ∧ SupportedOn (f j) (P.child ε')) →
    |form f| ≤ prodNorm p f
  /-- (ii) perfect smoothness (1.2): if `f_i` is supported on `P` with mean zero and `f_j`
  (`j ≠ i`) vanishes on `P`, then `Λ(f) = 0`. -/
  smooth : ∀ (P : DyadicCube d) (f : Fin n → TestFun d) (i j : Fin n), i ≠ j →
    SupportedOn (f i) P → MeanZero (f i : (Fin d → ℝ) → ℝ) → VanishesOn (f j) P →
    form f = 0
  /-- (iii) qualitative truncation: `Λ` is given by a kernel which is a dyadic test function on
  `ℝ^{dn}`. -/
  truncation : ∃ K : (Fin n → Fin d → ℝ) → ℝ, K ∈ TestFunProd d n ∧
    ∀ f : Fin n → TestFun d, form f = ∫ x, K x * ∏ j, (f j : (Fin d → ℝ) → ℝ) (x j)

/-! ## §1' Paths in `I_n` and admissible collections (paper, p. 37–38)

We index `I_n = {1, …, n}` by `Fin n = {0, …, n-1}`; a path of length `k` is an injective map
`Fin k ↪ Fin n`. -/

/-- A path of length `k` in `I_n`: an injective map `I_k → I_n`. -/
abbrev IPath (n k : ℕ) := Fin k ↪ Fin n

namespace IPath

variable {n k : ℕ}

/-- Restriction of a path of length `k+1` to `I_k`. -/
def restrict (σ : IPath n (k + 1)) : IPath n k :=
  ⟨fun i => σ i.castSucc, fun _ _ h => Fin.castSucc_injective k (σ.injective h)⟩

@[simp] theorem restrict_apply (σ : IPath n (k + 1)) (i : Fin k) :
    σ.restrict i = σ i.castSucc := rfl

/-- Extension of a path of length `k` by a new value `a ∉ range σ`. -/
def extend (σ : IPath n k) (a : Fin n) (ha : a ∉ Set.range σ) : IPath n (k + 1) where
  toFun := Fin.snoc (fun i => σ i) a
  inj' := by
    intro i j hij
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => rfl
      | cast j =>
        simp only [Fin.snoc_last, Fin.snoc_castSucc] at hij
        exact absurd ⟨j, hij.symm⟩ ha
    | cast i =>
      induction j using Fin.lastCases with
      | last =>
        simp only [Fin.snoc_last, Fin.snoc_castSucc] at hij
        exact absurd ⟨i, hij⟩ ha
      | cast j =>
        simp only [Fin.snoc_castSucc] at hij
        exact congrArg Fin.castSucc (σ.injective hij)

@[simp] theorem extend_castSucc (σ : IPath n k) (a : Fin n) (ha : a ∉ Set.range σ)
    (i : Fin k) : σ.extend a ha i.castSucc = σ i := by
  change Fin.snoc (α := fun _ => Fin n) (fun i => σ i) a i.castSucc = σ i
  simp

@[simp] theorem extend_last (σ : IPath n k) (a : Fin n) (ha : a ∉ Set.range σ) :
    σ.extend a ha (Fin.last k) = a := by
  change Fin.snoc (α := fun _ => Fin n) (fun i => σ i) a (Fin.last k) = a
  simp

/-- Restricting an extension gives back the path. [PROVED] -/
theorem restrict_extend (σ : IPath n k) (a : Fin n) (ha : a ∉ Set.range σ) :
    (σ.extend a ha).restrict = σ := by
  ext i
  simp

/-- The path obtained by interchanging the last two steps of a path of length `k+2`
(condition (3), p. 37). -/
def swapLast (σ : IPath n (k + 2)) : IPath n (k + 2) :=
  (Equiv.swap (Fin.last (k + 1)) (Fin.castSucc (Fin.last k))).toEmbedding.trans σ

@[simp] theorem swapLast_last (σ : IPath n (k + 2)) :
    σ.swapLast (Fin.last (k + 1)) = σ (Fin.castSucc (Fin.last k)) := by
  simp [swapLast]

@[simp] theorem swapLast_castSucc_last (σ : IPath n (k + 2)) :
    σ.swapLast (Fin.castSucc (Fin.last k)) = σ (Fin.last (k + 1)) := by
  simp [swapLast]

/-- A collection of paths in `I_n`, one set of paths for each length. -/
abbrev Collection (n : ℕ) := ∀ k : ℕ, Set (IPath n k)

/-- Admissibility of a collection of paths (conditions (1)–(3), p. 37). -/
structure Admissible (C : Collection n) : Prop where
  /-- (1) for each `j ∈ I_n` there is a path of length 1 with `σ(1) = j` -/
  singletons : ∀ j : Fin n, ∃ σ ∈ C 1, σ 0 = j
  /-- (2) every path of length `k < n` extends to a path of length `k+1` in the collection -/
  extension : ∀ k, k < n → ∀ σ ∈ C k, ∃ τ ∈ C (k + 1), τ.restrict = σ
  /-- (3) the collection is closed under interchanging the last two steps -/
  swap : ∀ k, ∀ σ ∈ C (k + 2), σ.swapLast ∈ C (k + 2)

/-- An `n`-tuple `𝐐` of dyadic cubes is `σ`-nested for a path `σ` of length `k+1` (p. 37):
`Q_{σ(i)} ⊇ Q_{σ(j)}` for `i < j`, `Q_s = Q_{σ(k)}` for `s` outside the range, and, if the
path has full length `n`, `Q_{σ(n-1)} = Q_{σ(n)}`. -/
structure Nested (σ : IPath n (k + 1)) (Q : Fin n → DyadicCube d) : Prop where
  mono : ∀ i j : Fin (k + 1), i < j → (Q (σ j)).toSet ⊆ (Q (σ i)).toSet
  outside : ∀ s : Fin n, s ∉ Set.range σ → Q s = Q (σ (Fin.last k))
  top : k + 1 = n → ∀ _ : 1 ≤ k, Q (σ ⟨k - 1, Nat.lt_of_le_of_lt (Nat.sub_le k 1) (Nat.lt_add_one
    k)⟩) = Q (σ (Fin.last k))

/-! ### The example of an admissible collection (paper, p. 38) -/

/-- The values `σ(i)` (as natural numbers) at the positions `i < j`, i.e. the image
`σ(I_j)` of `I_j` under the path. -/
def img (σ : IPath n k) (j : ℕ) : Finset ℕ :=
  (Finset.univ.filter (fun i : Fin k => i.val < j)).image (fun i => (σ i).val)

theorem mem_img {σ : IPath n k} {j x : ℕ} :
    x ∈ img σ j ↔ ∃ i : Fin k, i.val < j ∧ (σ i).val = x := by
  simp [img]

theorem val_mem_img_iff (σ : IPath n k) (a : Fin n) :
    a.val ∈ img σ k ↔ a ∈ Set.range σ := by
  rw [mem_img, Set.mem_range]
  constructor
  · rintro ⟨i, -, h⟩
    exact ⟨i, Fin.ext h⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i, i.isLt, rfl⟩

theorem img_succ (σ : IPath n k) {j : ℕ} (hj : j < k) :
    img σ (j + 1) = insert (σ ⟨j, hj⟩).val (img σ j) := by
  ext x
  rw [Finset.mem_insert, mem_img, mem_img]
  constructor
  · rintro ⟨i, hi, rfl⟩
    by_cases h : i.val = j
    · left
      have : i = ⟨j, hj⟩ := Fin.ext h
      rw [this]
    · right
      exact ⟨i, by omega, rfl⟩
  · rintro (rfl | ⟨i, hi, rfl⟩)
    · exact ⟨⟨j, hj⟩, by simp, rfl⟩
    · exact ⟨i, by omega, rfl⟩

theorem img_extend_of_le (σ : IPath n k) (a : Fin n) (ha : a ∉ Set.range σ) {j : ℕ}
    (hj : j ≤ k) : img (σ.extend a ha) j = img σ j := by
  ext x
  rw [mem_img, mem_img]
  constructor
  · rintro ⟨i, hi, rfl⟩
    induction i using Fin.lastCases with
    | last =>
      simp only [Fin.val_last] at hi
      omega
    | cast i => exact ⟨i, by simpa using hi, by simp⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i.castSucc, by simpa using hi, by simp⟩

theorem img_swapLast_of_le (σ : IPath n (k + 2)) {j : ℕ} (hj : j ≤ k) :
    img σ.swapLast j = img σ j := by
  have key : ∀ i : Fin (k + 2), i.val < j → σ.swapLast i = σ i := by
    intro i hi
    simp only [swapLast, Function.Embedding.trans_apply, Equiv.coe_toEmbedding]
    rw [Equiv.swap_apply_of_ne_of_ne]
    · exact Fin.ne_of_val_ne (by simp only [Fin.val_last]; omega)
    · exact Fin.ne_of_val_ne (by simp only [Fin.val_castSucc, Fin.val_last]; omega)
  ext x
  rw [mem_img, mem_img]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, hi, by rw [key i hi]⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, hi, by rw [key i hi]⟩

theorem img_swapLast_full (σ : IPath n (k + 2)) :
    img σ.swapLast (k + 2) = img σ (k + 2) := by
  ext x
  rw [mem_img, mem_img]
  constructor
  · rintro ⟨i, -, rfl⟩
    refine ⟨Equiv.swap (Fin.last (k + 1)) (Fin.castSucc (Fin.last k)) i, Fin.isLt _, ?_⟩
    simp [swapLast]
  · rintro ⟨i, -, rfl⟩
    refine ⟨Equiv.swap (Fin.last (k + 1)) (Fin.castSucc (Fin.last k)) i, Fin.isLt _, ?_⟩
    simp [swapLast]

/-- Condition (i) of the example (p. 38): the range of a path of length `k` contains
`I_{k-1}`. -/
def RangeCond (σ : IPath n k) : Prop := Finset.range (k - 1) ⊆ img σ k

/-- Condition (ii) of the example (p. 38): for `j ≤ k`, `I_j` contains at least `j - 1`
elements of `σ(I_j)`. -/
def CountCond (σ : IPath n k) : Prop :=
  ∀ j ≤ k, j ≤ (img σ j ∩ Finset.range j).card + 1

/-- The example collection: all paths satisfying (i) and (ii). -/
def exampleCollection (n : ℕ) : Collection n := fun _ => {σ | RangeCond σ ∧ CountCond σ}

theorem mem_exampleCollection {σ : IPath n k} :
    σ ∈ exampleCollection n k ↔ RangeCond σ ∧ CountCond σ := Iff.rfl

/-- Condition (ii) at `j = k+1` is preserved by interchanging the last two steps of a path of
length `k+2` (the only nontrivial case in the verification of (3) on p. 38). [PROVED] -/
theorem countCond_swapLast_mid (σ : IPath n (k + 2)) (hR : RangeCond σ)
    (hC : k + 1 ≤ (img σ (k + 1) ∩ Finset.range (k + 1)).card + 1) :
    k + 1 ≤ (img σ.swapLast (k + 1) ∩ Finset.range (k + 1)).card + 1 := by
  set x := (σ (Fin.castSucc (Fin.last k))).val
  set y := (σ (Fin.last (k + 1))).val
  have e1 : img σ (k + 1) = insert x (img σ k) := img_succ σ (by omega)
  have e2 : img σ.swapLast (k + 1) = insert y (img σ k) := by
    rw [img_succ σ.swapLast (by omega), img_swapLast_of_le σ le_rfl]
    congr 1
    exact congrArg Fin.val (swapLast_castSucc_last σ)
  have e3 : img σ (k + 2) = insert y (insert x (img σ k)) :=
    (img_succ σ (by omega)).trans (congrArg _ e1)
  have hyk : y ∉ img σ k := by
    intro h
    obtain ⟨i, hi, hiy⟩ := mem_img.mp h
    have : i = Fin.last (k + 1) := σ.injective (Fin.ext hiy)
    rw [this, Fin.val_last] at hi
    omega
  rw [e2]
  rw [e1] at hC
  by_cases hyk' : y < k + 1
  · -- `y ∈ I_{k+1}`: the count increases
    have h1 : (insert x (img σ k) ∩ Finset.range (k + 1)).card ≤
        (img σ k ∩ Finset.range (k + 1)).card + 1 := by
      calc (insert x (img σ k) ∩ Finset.range (k + 1)).card
          ≤ (insert x (img σ k ∩ Finset.range (k + 1))).card := Finset.card_le_card (by
            intro z hz
            rw [Finset.mem_inter, Finset.mem_insert] at hz
            rw [Finset.mem_insert, Finset.mem_inter]
            tauto)
        _ ≤ (img σ k ∩ Finset.range (k + 1)).card + 1 := Finset.card_insert_le _ _
    have hsub : insert y (img σ k ∩ Finset.range (k + 1)) ⊆
        insert y (img σ k) ∩ Finset.range (k + 1) := by
      intro z hz
      rw [Finset.mem_insert] at hz
      rw [Finset.mem_inter, Finset.mem_insert, Finset.mem_range]
      rcases hz with rfl | hz
      · exact ⟨Or.inl rfl, hyk'⟩
      · rw [Finset.mem_inter, Finset.mem_range] at hz
        exact ⟨Or.inr hz.1, hz.2⟩
    have hc := Finset.card_le_card hsub
    have hyS : y ∉ img σ k ∩ Finset.range (k + 1) := fun h => hyk (Finset.mem_inter.mp h).1
    rw [Finset.card_insert_of_notMem hyS] at hc
    omega
  · -- `y ∉ I_{k+1}`: by (i), `σ(I_{k+1}) ⊇ I_{k+1} ∖ {x}`
    have hsub : (Finset.range (k + 1)).erase x ⊆
        insert y (img σ k) ∩ Finset.range (k + 1) := by
      intro z hz
      rw [Finset.mem_erase, Finset.mem_range] at hz
      have hz' : z ∈ img σ (k + 2) := hR (Finset.mem_range.mpr (by omega))
      rw [e3, Finset.mem_insert, Finset.mem_insert] at hz'
      rw [Finset.mem_inter, Finset.mem_insert, Finset.mem_range]
      refine ⟨?_, hz.2⟩
      rcases hz' with rfl | rfl | hz'
      · exact absurd hz.2 hyk'
      · exact absurd rfl hz.1
      · exact Or.inr hz'
    have hc := Finset.card_le_card hsub
    have hpred := Finset.pred_card_le_card_erase (s := Finset.range (k + 1)) (a := x)
    rw [Finset.card_range] at hpred
    omega

/-- The collection of all paths satisfying (i) and (ii) is admissible (paper, p. 38).
[PROVED] -/
theorem exampleCollection_admissible (n : ℕ) : Admissible (exampleCollection n) where
  singletons := by
    intro j
    refine ⟨⟨fun _ => j, fun a b _ => Subsingleton.elim a b⟩,
      mem_exampleCollection.mpr ⟨?_, ?_⟩, rfl⟩
    · simp [RangeCond]
    · intro j _
      omega
  extension := by
    intro k hk σ hσ
    obtain ⟨hR, hC⟩ := mem_exampleCollection.mp hσ
    -- `a` is the minimal element of `I_n` not in the range of `σ`
    have hne : (Finset.univ.map σ)ᶜ.Nonempty := by
      rw [← Finset.card_pos, Finset.card_compl, Finset.card_map, Finset.card_univ,
        Fintype.card_fin, Fintype.card_fin]
      omega
    obtain ⟨a, haC, hamin⟩ : ∃ a ∈ (Finset.univ.map σ)ᶜ, ∀ x ∈ (Finset.univ.map σ)ᶜ, a ≤ x :=
      ⟨_, Finset.min'_mem _ hne, fun x hx => Finset.min'_le _ x hx⟩
    have ha : a ∉ Set.range σ := fun ⟨i, hi⟩ =>
      (Finset.mem_compl.mp haC) (Finset.mem_map.mpr ⟨i, Finset.mem_univ _, hi⟩)
    have hmin : ∀ x : Fin n, x ∉ Set.range σ → a ≤ x := fun x hx =>
      hamin x (Finset.mem_compl.mpr fun hx' => by
        obtain ⟨i, -, hi⟩ := Finset.mem_map.mp hx'
        exact hx ⟨i, hi⟩)
    have hbelow : ∀ x : Fin n, x < a → x ∈ Set.range σ := fun x hx => by
      by_contra h
      exact absurd (hmin x h) (not_le.mpr hx)
    -- `a ≤ k`, since `I_{k+1}` cannot be contained in the range of `σ`
    have hak : a.val ≤ k := by
      by_contra h
      rw [not_le] at h
      have hsub : ∀ i : Fin (k + 1), (Fin.castLE (by omega) i : Fin n) ∈ Finset.univ.map σ := by
        intro i
        have hi := i.isLt
        obtain ⟨i', hi'⟩ := hbelow (Fin.castLE (by omega) i)
          (by rw [Fin.lt_def, Fin.val_castLE]; omega)
        exact Finset.mem_map.mpr ⟨i', Finset.mem_univ _, hi'⟩
      have := Finset.card_le_card_of_injOn (s := Finset.univ) (t := Finset.univ.map σ)
        (fun i : Fin (k + 1) => (Fin.castLE (by omega) i : Fin n))
        (by intro i _; exact hsub i) (by intro i _ i' _ h; exact Fin.castLE_injective _ h)
      simp only [Finset.card_map, Finset.card_univ, Fintype.card_fin] at this
      omega
    -- `a ≥ k - 1`, since `I_{k-1}` is contained in the range of `σ`
    have hak' : k - 1 ≤ a.val := by
      by_contra h
      rw [not_le] at h
      exact ha ((val_mem_img_iff σ a).mp (hR (Finset.mem_range.mpr h)))
    have e1 : img (σ.extend a ha) (k + 1) = insert a.val (img σ k) := by
      rw [img_succ _ (Nat.lt_succ_self k), img_extend_of_le σ a ha le_rfl]
      congr 1
      exact congrArg Fin.val (extend_last σ a ha)
    refine ⟨σ.extend a ha, mem_exampleCollection.mpr ⟨?_, ?_⟩, restrict_extend σ a ha⟩
    · -- (i) for the extended path
      intro x hx
      rw [Finset.mem_range] at hx
      rw [e1, Finset.mem_insert]
      by_cases hx1 : x < k - 1
      · exact Or.inr (hR (Finset.mem_range.mpr hx1))
      · have hxe : x = k - 1 := by omega
        subst hxe
        by_cases hx2 : k - 1 ∈ img σ k
        · exact Or.inr hx2
        · left
          have hnot : (⟨k - 1, by omega⟩ : Fin n) ∉ Set.range σ := fun hr =>
            hx2 ((val_mem_img_iff σ ⟨k - 1, by omega⟩).mpr hr)
          have h' : a.val ≤ k - 1 := hmin _ hnot
          omega
    · -- (ii) for the extended path
      intro j hj
      rcases Nat.lt_or_ge j (k + 1) with hjk | hjk
      · rw [img_extend_of_le σ a ha (by omega)]
        exact hC j (by omega)
      · have hj' : j = k + 1 := by omega
        subst hj'
        rw [e1]
        have hsub : insert a.val (Finset.range (k - 1)) ⊆
            insert a.val (img σ k) ∩ Finset.range (k + 1) := by
          intro x hx
          rw [Finset.mem_insert] at hx
          rw [Finset.mem_inter, Finset.mem_insert, Finset.mem_range]
          rcases hx with rfl | hx
          · exact ⟨Or.inl rfl, by omega⟩
          · rw [Finset.mem_range] at hx
            exact ⟨Or.inr (hR (Finset.mem_range.mpr hx)), by omega⟩
        have hcard : (insert a.val (Finset.range (k - 1))).card = k - 1 + 1 := by
          rw [Finset.card_insert_of_notMem, Finset.card_range]
          rw [Finset.mem_range]
          omega
        have := Finset.card_le_card hsub
        omega
  swap := by
    intro k σ hσ
    obtain ⟨hR, hC⟩ := mem_exampleCollection.mp hσ
    refine mem_exampleCollection.mpr ⟨?_, ?_⟩
    · change Finset.range (k + 2 - 1) ⊆ img σ.swapLast (k + 2)
      rw [img_swapLast_full]
      exact hR
    · intro j hj
      rcases Nat.lt_or_ge j (k + 1) with h1 | h1
      · rw [img_swapLast_of_le σ (by omega)]
        exact hC j (by omega)
      rcases Nat.lt_or_ge j (k + 2) with h2 | h2
      · have hj' : j = k + 1 := by omega
        subst hj'
        exact countCond_swapLast_mid σ hR (hC (k + 1) (by omega))
      · have hj' : j = k + 2 := by omega
        subst hj'
        rw [img_swapLast_full]
        exact hC (k + 2) le_rfl

end IPath

/-! ## §1'' The main theorems (statements) -/

/-- The testing hypothesis of Theorem 1.3: all but one entry are `𝟙_P`, the remaining entry is an
arbitrary dyadic test function supported on `P`. -/
def T1Testing {n : ℕ} (T : PerfectCZForm d n) (p : HolderTuple n) (B : ℝ) : Prop :=
  ∀ (P : DyadicCube d) (j₀ : Fin n) (f : Fin n → TestFun d),
    (∀ j, j ≠ j₀ → (f j : (Fin d → ℝ) → ℝ) = P.indicator) → SupportedOn (f j₀) P →
    |T.form f| ≤ B * prodNorm p f

/-- **Theorem 1.3** (perfect multilinear local T(1) theorem). [STATEMENT; proved at the end of
the file as `localT1`] -/
def LocalT1 (d n : ℕ) (p : HolderTuple n) : Prop :=
  1 ≤ d → 2 ≤ n → ∀ B : ℝ, 1 ≤ B → ∃ C : ℝ, ∀ T : PerfectCZForm d n,
    T1Testing T p B → ∀ f : Fin n → TestFun d, |T.form f| ≤ C * prodNorm p f

/-- The testing functions `b_{σ,𝐐,·}` of Theorem 1.4 for paths of length `k+1`: for each path
`σ`, each tuple `𝐐` and each position `l < k` in the path (so that `σ(l) ∈ σ(I_{k})`) a
function on `ℝ^d`. -/
abbrev TestingFamily (d n k : ℕ) :=
  IPath n (k + 1) → (Fin n → DyadicCube d) → Fin k → (Fin d → ℝ) → ℝ

/-- The testing condition (1.9) of Theorem 1.4 for a family `b` of testing functions on paths of
length `k+1`, with constant `B`: for every admissible `σ`, every `σ`-nested `𝐐` and every dyadic
test function `g` supported on `Q_{σ(k)}`, `|Λ(f)| ≤ B ∏ ‖f_j‖_{p_j}` where `f_{σ(k)} = g`,
`f_{σ(l)} = 𝟙_{Q_{σ(k)}} b_{σ,𝐐,σ(l)}` for `l < k` and `f_s = 𝟙_{Q_{σ(k)}}` outside the range. -/
abbrev TestingCondition {n : ℕ} (T : PerfectCZForm d n) (p : HolderTuple n)
    (C : IPath.Collection n) {k : ℕ} (b : TestingFamily d n k) (B : ℝ) : Prop :=
  ∀ σ ∈ C (k + 1), ∀ Q, IPath.Nested σ Q →
    ∀ g : TestFun d, SupportedOn g (Q (σ (Fin.last k))) →
    ∀ f : Fin n → TestFun d, f (σ (Fin.last k)) = g →
    (∀ l : Fin k, (f (σ l.castSucc) : (Fin d → ℝ) → ℝ) =
      truncate (Q (σ (Fin.last k))) (b σ Q l)) →
    (∀ s, s ∉ Set.range σ → (f s : (Fin d → ℝ) → ℝ) = (Q (σ (Fin.last k))).indicator) →
    |T.form f| ≤ B * prodNorm p f

/-- Hypotheses (1.5)–(1.9) of Theorem 1.4 for paths of length `k+1`, with constant `B`. -/
structure LocalTbHypotheses {n : ℕ} (T : PerfectCZForm d n) (p : HolderTuple n)
    (C : IPath.Collection n) {k : ℕ} (b : TestingFamily d n k) (B : ℝ) : Prop where
  /-- support condition (1.5) -/
  support : ∀ σ ∈ C (k + 1), ∀ Q, IPath.Nested σ Q → ∀ l : Fin k,
    SupportedOn (b σ Q l) (Q (σ l.castSucc))
  /-- the testing functions are dyadic test functions (implicit in the paper, where the form
  `Λ` is only defined on dyadic test functions) -/
  testFun : ∀ σ ∈ C (k + 1), ∀ Q, IPath.Nested σ Q → ∀ l : Fin k, b σ Q l ∈ TestFun d
  /-- mean condition (1.6) -/
  mean : ∀ σ ∈ C (k + 1), ∀ Q, IPath.Nested σ Q → ∀ l : Fin k,
    ∫ x, b σ Q l x = (Q (σ l.castSucc)).vol
  /-- norm bound condition (1.7) -/
  norm : ∀ σ ∈ C (k + 1), ∀ Q, IPath.Nested σ Q → ∀ l : Fin k,
    ∫ x, |b σ Q l x| ^ p.p (σ l.castSucc) ≤ B * (Q (σ l.castSucc)).vol
  /-- interdependence condition (1.8) -/
  interdep : ∀ σ ∈ C (k + 1), ∀ σ' ∈ C (k + 1), ∀ Q Q', IPath.Nested σ Q → IPath.Nested σ' Q' →
    ∀ l : Fin k,
    (∀ l' : Fin k, l' ≤ l →
      σ l'.castSucc = σ' l'.castSucc ∧ Q (σ l'.castSucc) = Q' (σ' l'.castSucc)) →
    b σ Q l = b σ' Q' l
  /-- testing condition (1.9) -/
  testing : TestingCondition T p C b B

/-- **Theorem 1.4** (perfect multilinear local T(b) theorem), for paths of length `k` with
`1 ≤ k ≤ n`. (The paper writes `n ≥ min(k, 2)`; since the hypotheses concern paths of length
`k` in `I_n`, which exist only for `k ≤ n`, and are vacuous otherwise, the intended range is
`1 ≤ k ≤ n`, which implies `n ≥ min(k, 2)`. Moreover `n ≥ 2` is automatic for a Hölder tuple of
finite exponents, `HolderTuple.two_le`, so the case `n = 1` is void.) [STATEMENT; proved at the
end of the file for all `n`, `k` as `localTb_all`] -/
def LocalTb (d n k : ℕ) (p : HolderTuple n) : Prop :=
  1 ≤ d → 1 ≤ k → k ≤ n → ∀ B : ℝ, 1 ≤ B → ∃ C : ℝ,
    ∀ (T : PerfectCZForm d n) (𝒞 : IPath.Collection n), IPath.Admissible 𝒞 →
    ∀ b : TestingFamily d n (k - 1), LocalTbHypotheses T p 𝒞 b B →
    ∀ f : Fin n → TestFun d, |T.form f| ≤ C * prodNorm p f

/-- The case `k = 1` of Theorem 1.4 is Theorem 1.3 (remark on p. 38): for `n ≥ 2` the two
statements are equivalent. The direction `1.4 ⇒ 1.3` uses the admissible example collection,
the direction `1.3 ⇒ 1.4` uses condition (1) of admissibility. [PROVED] -/
theorem localTb_one_iff_localT1 {n : ℕ} (hn : 2 ≤ n) (p : HolderTuple n) :
    LocalTb d n 1 p ↔ LocalT1 d n p := by
  constructor
  · intro H hd _ B hB
    obtain ⟨C, hC⟩ := H hd le_rfl (by omega) B hB
    refine ⟨C, fun T hT f =>
      hC T _ (IPath.exampleCollection_admissible n) (fun _ _ _ => 0) ?_ f⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro _ _ _ _ l
      exact l.elim0
    · intro _ _ _ _ l
      exact l.elim0
    · intro _ _ _ _ l
      exact l.elim0
    · intro _ _ _ _ l
      exact l.elim0
    · intro _ _ _ _ _ _ _ _ l
      exact l.elim0
    · intro σ _ Q _ g hg f hf _ hout
      apply hT (Q (σ (Fin.last 0))) (σ (Fin.last 0)) f
      · intro j hj
        apply hout
        rintro ⟨i, rfl⟩
        exact hj (congrArg σ (Fin.ext (by
          have := i.isLt
          simp only [Fin.val_last]
          omega)))
      · rw [hf]
        exact hg
  · intro H hd _ _ B hB
    obtain ⟨C, hC⟩ := H hd hn B hB
    refine ⟨C, fun T 𝒞 h𝒞 b hb f => hC T ?_ f⟩
    intro P j₀ f hf hj₀
    obtain ⟨σ, hσ, hσ0⟩ := h𝒞.singletons j₀
    have hσ0' : σ (Fin.last 0) = j₀ := hσ0
    have hQ : IPath.Nested σ (fun _ => P) :=
      ⟨fun i j hij => absurd hij (by
          rw [Fin.lt_def]
          have := i.isLt
          have := j.isLt
          omega),
        fun _ _ => rfl, fun _ _ => rfl⟩
    exact hb.testing σ hσ (fun _ => P) hQ (f j₀) hj₀ f (by rw [hσ0']) (fun l => l.elim0)
      (fun s hs => hf s fun h => hs ⟨Fin.last 0, by rw [hσ0', h]⟩)

/-! ### §2.1 The induction on `k` (paper, p. 39–40)

Theorem 1.4 is proved by induction on `k`; the case `k = 1` is Theorem 1.3. For the inductive
step, a family `b` of testing functions for paths of length `k+2` is restricted to paths of
length `k+1` by `b'_{σ',𝐐,j} := b_{σ,𝐐,j}` for an admissible extension `σ` of `σ'`. The restricted
family satisfies (1.5)–(1.8), and the main part of the proof (§2.2–2.8) establishes the testing
condition (1.9) for it with a new constant; the induction hypothesis then gives the bound. -/

/-- `∏_j ‖f_j‖_{p_j} ≥ 0`. [PROVED] -/
theorem prodNorm_nonneg {n : ℕ} (p : HolderTuple n) (f : Fin n → TestFun d) :
    0 ≤ prodNorm p f :=
  Finset.prod_nonneg fun _ _ => ENNReal.toReal_nonneg

/-- The testing condition is monotone in the constant. [PROVED] -/
theorem TestingCondition.mono {n : ℕ} {T : PerfectCZForm d n} {p : HolderTuple n}
    {C : IPath.Collection n} {k : ℕ} {b : TestingFamily d n k} {B B' : ℝ} (hB : B ≤ B')
    (h : TestingCondition T p C b B) : TestingCondition T p C b B' :=
  fun σ hσ Q hQ g hg f hf hl hs =>
    (h σ hσ Q hQ g hg f hf hl hs).trans (mul_le_mul_of_nonneg_right hB (prodNorm_nonneg p f))

/-- If `𝐐` is `σ'`-nested and `σ` extends `σ'` by one step, then `𝐐` is `σ`-nested (p. 40,
"note that `𝐐` is also `σ`-nested"). [PROVED] -/
theorem IPath.Nested.of_restrict {n k : ℕ} {τ : IPath n (k + 2)} {σ : IPath n (k + 1)}
    (hτ : τ.restrict = σ) {Q : Fin n → DyadicCube d} (hQ : IPath.Nested σ Q) :
    IPath.Nested τ Q := by
  have hcs : ∀ i : Fin (k + 1), τ i.castSucc = σ i := fun i => by rw [← hτ]; rfl
  have hlast_not : τ (Fin.last (k + 1)) ∉ Set.range σ := by
    rintro ⟨i, hi⟩
    rw [← hcs i] at hi
    have h := congrArg Fin.val (τ.injective hi)
    simp only [Fin.val_castSucc, Fin.val_last] at h
    omega
  have hlast : Q (τ (Fin.last (k + 1))) = Q (σ (Fin.last k)) := hQ.outside _ hlast_not
  refine ⟨?_, ?_, ?_⟩
  · intro i j hij
    induction j using Fin.lastCases with
    | last =>
      rw [hlast]
      induction i using Fin.lastCases with
      | last => exact absurd hij (lt_irrefl _)
      | cast i =>
        rw [hcs]
        rcases eq_or_lt_of_le (Fin.le_last i) with h | h
        · rw [h]
        · exact hQ.mono i (Fin.last k) h
    | cast j =>
      induction i using Fin.lastCases with
      | last => exact absurd hij (not_lt.mpr (Fin.le_last _))
      | cast i =>
        rw [hcs, hcs]
        exact hQ.mono i j (Fin.castSucc_lt_castSucc_iff.mp hij)
  · intro s hs
    rw [hlast]
    apply hQ.outside
    rintro ⟨i, hi⟩
    exact hs ⟨i.castSucc, by rw [hcs, hi]⟩
  · intro _ _
    rw [hlast]
    have e : (⟨k + 1 - 1, by omega⟩ : Fin (k + 2)) = Fin.castSucc (Fin.last k) := by
      ext
      simp
    rw [e, hcs]

open Classical in
/-- The restriction of a family of testing functions for paths of length `k+2` to paths of
length `k+1` (p. 40): `b'_{σ',𝐐,j} := b_{σ,𝐐,j}` for an admissible extension `σ` of `σ'` (chosen
with the axiom of choice; by the interdependence condition (1.8) the value does not depend on
the choice). -/
noncomputable def restrictFamily {n k : ℕ} (C : IPath.Collection n)
    (b : TestingFamily d n (k + 1)) : TestingFamily d n k := fun σ Q j =>
  if h : ∃ τ ∈ C (k + 2), τ.restrict = σ then b (Classical.choose h) Q j.castSucc else 0

/-- For an admissible path `σ'` of length `k+1 < n`, the restricted family is given by some
admissible extension. [PROVED] -/
theorem restrictFamily_eq {n k : ℕ} {C : IPath.Collection n} (hC : IPath.Admissible C)
    (hk : k + 1 < n) (b : TestingFamily d n (k + 1)) {σ : IPath n (k + 1)} (hσ : σ ∈ C (k + 1))
    (Q : Fin n → DyadicCube d) (j : Fin k) :
    ∃ τ ∈ C (k + 2), τ.restrict = σ ∧ restrictFamily C b σ Q j = b τ Q j.castSucc := by
  have h : ∃ τ ∈ C (k + 2), τ.restrict = σ := hC.extension (k + 1) hk σ hσ
  refine ⟨Classical.choose h, (Classical.choose_spec h).1, (Classical.choose_spec h).2, ?_⟩
  simp only [restrictFamily, dite_eq_left h]

section RestrictedFamily

variable {n k : ℕ} {T : PerfectCZForm d n} {p : HolderTuple n} {C : IPath.Collection n}
  {b : TestingFamily d n (k + 1)} {B : ℝ}

/-- The restricted family satisfies the support condition (1.5). [PROVED] -/
theorem restrictFamily_support (hC : IPath.Admissible C) (hk : k + 1 < n)
    (hb : LocalTbHypotheses T p C b B) :
    ∀ σ ∈ C (k + 1), ∀ Q, IPath.Nested σ Q → ∀ l : Fin k,
      SupportedOn (restrictFamily C b σ Q l) (Q (σ l.castSucc)) := by
  intro σ hσ Q hQ l
  obtain ⟨τ, hτ, hτσ, e⟩ := restrictFamily_eq hC hk b hσ Q l
  have c : τ l.castSucc.castSucc = σ l.castSucc := by rw [← hτσ]; rfl
  rw [e, ← c]
  exact hb.support τ hτ Q (hQ.of_restrict hτσ) l.castSucc

/-- The restricted family consists of dyadic test functions. [PROVED] -/
theorem restrictFamily_testFun (hC : IPath.Admissible C) (hk : k + 1 < n)
    (hb : LocalTbHypotheses T p C b B) :
    ∀ σ ∈ C (k + 1), ∀ Q, IPath.Nested σ Q → ∀ l : Fin k,
      restrictFamily C b σ Q l ∈ TestFun d := by
  intro σ hσ Q hQ l
  obtain ⟨τ, hτ, hτσ, e⟩ := restrictFamily_eq hC hk b hσ Q l
  rw [e]
  exact hb.testFun τ hτ Q (hQ.of_restrict hτσ) l.castSucc

/-- The restricted family satisfies the mean condition (1.6). [PROVED] -/
theorem restrictFamily_mean (hC : IPath.Admissible C) (hk : k + 1 < n)
    (hb : LocalTbHypotheses T p C b B) :
    ∀ σ ∈ C (k + 1), ∀ Q, IPath.Nested σ Q → ∀ l : Fin k,
      ∫ x, restrictFamily C b σ Q l x = (Q (σ l.castSucc)).vol := by
  intro σ hσ Q hQ l
  obtain ⟨τ, hτ, hτσ, e⟩ := restrictFamily_eq hC hk b hσ Q l
  have c : τ l.castSucc.castSucc = σ l.castSucc := by rw [← hτσ]; rfl
  rw [e, ← c]
  exact hb.mean τ hτ Q (hQ.of_restrict hτσ) l.castSucc

/-- The restricted family satisfies the norm bound condition (1.7). [PROVED] -/
theorem restrictFamily_norm (hC : IPath.Admissible C) (hk : k + 1 < n)
    (hb : LocalTbHypotheses T p C b B) :
    ∀ σ ∈ C (k + 1), ∀ Q, IPath.Nested σ Q → ∀ l : Fin k,
      ∫ x, |restrictFamily C b σ Q l x| ^ p.p (σ l.castSucc) ≤ B * (Q (σ l.castSucc)).vol := by
  intro σ hσ Q hQ l
  obtain ⟨τ, hτ, hτσ, e⟩ := restrictFamily_eq hC hk b hσ Q l
  have c : τ l.castSucc.castSucc = σ l.castSucc := by rw [← hτσ]; rfl
  rw [e, ← c]
  exact hb.norm τ hτ Q (hQ.of_restrict hτσ) l.castSucc

/-- The restricted family satisfies the interdependence condition (1.8). [PROVED] -/
theorem restrictFamily_interdep (hC : IPath.Admissible C) (hk : k + 1 < n)
    (hb : LocalTbHypotheses T p C b B) :
    ∀ σ ∈ C (k + 1), ∀ σ' ∈ C (k + 1), ∀ Q Q', IPath.Nested σ Q → IPath.Nested σ' Q' →
      ∀ l : Fin k,
      (∀ l' : Fin k, l' ≤ l →
        σ l'.castSucc = σ' l'.castSucc ∧ Q (σ l'.castSucc) = Q' (σ' l'.castSucc)) →
      restrictFamily C b σ Q l = restrictFamily C b σ' Q' l := by
  intro σ hσ σ' hσ' Q Q' hQ hQ' l hl
  obtain ⟨τ, hτ, hτσ, e⟩ := restrictFamily_eq hC hk b hσ Q l
  obtain ⟨τ', hτ', hτσ', e'⟩ := restrictFamily_eq hC hk b hσ' Q' l
  rw [e, e']
  apply hb.interdep τ hτ τ' hτ' Q Q' (hQ.of_restrict hτσ) (hQ'.of_restrict hτσ') l.castSucc
  intro l' hl'
  induction l' using Fin.lastCases with
  | last => exact absurd hl' (not_le.mpr (Fin.castSucc_lt_last l))
  | cast l'' =>
    have c1 : τ l''.castSucc.castSucc = σ l''.castSucc := by rw [← hτσ]; rfl
    have c2 : τ' l''.castSucc.castSucc = σ' l''.castSucc := by rw [← hτσ']; rfl
    rw [c1, c2]
    exact hl l'' (Fin.castSucc_le_castSucc_iff.mp hl')

/-- Hypotheses (1.5)–(1.9) for the restricted family, given the testing condition (1.9) for it
with a constant `B₀ ≥ B` (p. 40). [PROVED] -/
theorem restrictFamily_hypotheses (hC : IPath.Admissible C) (hk : k + 1 < n)
    (hb : LocalTbHypotheses T p C b B) {B₀ : ℝ} (hB : B ≤ B₀)
    (htest : TestingCondition T p C (restrictFamily C b) B₀) :
    LocalTbHypotheses T p C (restrictFamily C b) B₀ where
  support := restrictFamily_support hC hk hb
  testFun := restrictFamily_testFun hC hk hb
  mean := restrictFamily_mean hC hk hb
  norm := fun σ hσ Q hQ l => (restrictFamily_norm hC hk hb σ hσ Q hQ l).trans
    (mul_le_mul_of_nonneg_right hB (Q _).vol_pos.le)
  interdep := restrictFamily_interdep hC hk hb
  testing := htest

end RestrictedFamily

/-- **The main part of the proof of Theorem 1.4** (p. 40, established in §2.2–2.8): for every
`B ≥ 1` there is `B' ≥ 1` (depending only on `n`, `d`, `B` and the exponents) such that, for
every perfect Calderón–Zygmund form, every admissible collection and every family `b` of
testing functions for paths of length `k+2` satisfying (1.5)–(1.9) with constant `B`, the
restricted family satisfies the testing condition (1.9) with constant `B'`. [STATEMENT] -/
def RestrictedTesting (d n k : ℕ) (p : HolderTuple n) : Prop :=
  ∀ B : ℝ, 1 ≤ B → ∃ B' : ℝ, 1 ≤ B' ∧
    ∀ (T : PerfectCZForm d n) (C : IPath.Collection n), IPath.Admissible C →
    ∀ b : TestingFamily d n (k + 1), LocalTbHypotheses T p C b B →
    TestingCondition T p C (restrictFamily C b) B'

/-- The inductive step of Theorem 1.4 (p. 40): the main estimate for paths of length `k+2`
together with Theorem 1.4 for `k+1` gives Theorem 1.4 for `k+2`. [PROVED] -/
theorem localTb_succ {n k : ℕ} {p : HolderTuple n} (hk : k + 2 ≤ n)
    (hR : RestrictedTesting d n k p) (hind : LocalTb d n (k + 1) p) :
    LocalTb d n (k + 2) p := by
  intro hd _ _ B hB
  obtain ⟨B', hB'1, hB'⟩ := hR B hB
  obtain ⟨C, hC⟩ := hind hd (by omega) (by omega) (max B B') (le_max_of_le_left hB)
  refine ⟨C, fun T 𝒞 h𝒞 b hb f => hC T 𝒞 h𝒞 (restrictFamily 𝒞 b) ?_ f⟩
  exact restrictFamily_hypotheses h𝒞 (by omega) hb (le_max_left _ _)
    ((hB' T 𝒞 h𝒞 b hb).mono (le_max_right _ _))

/-- **Theorem 1.4 by induction on `k`** (p. 39–40): Theorem 1.3 (the case `k = 1`) together with
the main estimate for every `k` gives Theorem 1.4 for all `1 ≤ k ≤ n`. [PROVED] -/
theorem localTb_of_localT1 {n : ℕ} (hn : 2 ≤ n) (p : HolderTuple n) (h13 : LocalT1 d n p)
    (hstep : ∀ k, k + 2 ≤ n → RestrictedTesting d n k p) :
    ∀ k, 1 ≤ k → k ≤ n → LocalTb d n k p := by
  intro k hk1 hkn
  induction k with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · exact (localTb_one_iff_localT1 hn p).mpr h13
    · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      exact localTb_succ hkn (hstep k' hkn) (ih (by omega) (by omega))

/-! ### §2.1 (continued) The best constant `A` (paper, p. 40 and p. 43)

By the truncation assumption (iii) every perfect Calderón–Zygmund form satisfies a bound
`|Λ(f)| ≤ A ∏_j ‖f_j‖_{p_j}` with some finite `A` depending on the form, so the best constant
`A` in (2.1) is finite. The main estimate of §2.2–2.8 shows that any constant `A` valid in the
testing condition for the restricted family may be replaced by `A θ + C`, `θ = (1-ε)^{1/p_k} < 1`,
with `C` depending only on `n`, `d`, `B` and the exponents ("`A ≤ A(1-ε)^{1/p_k} + C`", p. 43).
Instead of an extremal function we iterate: starting from the truncation bound `A₀`, the
constants `θ^m A₀ + C/(1-θ)` are all valid, and letting `m → ∞` gives the constant `C/(1-θ)`.
This formalises the reduction of p. 43 and isolates the main estimate as `ContractionStep`. -/

/-- Dyadic test functions lie in every `L^p`. [PROVED] -/
theorem TestFun.memLp {f : (Fin d → ℝ) → ℝ} (hf : f ∈ TestFun d) (p : ENNReal) :
    MemLp f p volume := by
  have hf' : f ∈ Submodule.span ℝ (Set.range (DyadicCube.indicator (d := d))) := hf
  clear hf
  induction hf' using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨P, rfl⟩ := hg
    exact memLp_indicator_const p P.measurableSet_toSet.nullMeasurableSet 1
      (Or.inr (by rw [DyadicCube.volume_toSet]; exact ENNReal.ofReal_ne_top))
  | zero => exact MemLp.zero
  | add g₁ g₂ _ _ h₁ h₂ => exact h₁.add h₂
  | smul c g _ h => exact h.const_smul c

/-- Hölder's inequality on a cube: `|∫_P f| ≤ |P|^{1-1/p} ‖f‖_p` for `f ∈ L^p`, `p ≥ 1`.
[PROVED] -/
theorem abs_integral_indicator_le {f : (Fin d → ℝ) → ℝ} {p : ℝ} (hp : 1 ≤ p)
    (hf : MemLp f (ENNReal.ofReal p) volume) (P : DyadicCube d) :
    |∫ x, P.toSet.indicator f x| ≤ P.vol ^ (1 - 1 / p) * lpNorm f p := by
  have hmeas := P.measurableSet_toSet
  have hp0 : (0 : ℝ) ≤ p := by linarith
  have h0 : 0 ≤ 1 - 1 / p := sub_nonneg.mpr ((div_le_one (by linarith)).mpr hp)
  have h1 : eLpNorm (P.toSet.indicator f) 1 volume ≤
      eLpNorm f (ENNReal.ofReal p) volume * ENNReal.ofReal (P.vol ^ (1 - 1 / p)) := by
    calc eLpNorm (P.toSet.indicator f) 1 volume
        = eLpNorm f 1 (volume.restrict P.toSet) :=
          eLpNorm_indicator_eq_eLpNorm_restrict hmeas.nullMeasurableSet
      _ ≤ eLpNorm f (ENNReal.ofReal p) (volume.restrict P.toSet) *
          (volume.restrict P.toSet) Set.univ ^
            (1 / (1 : ENNReal).toReal - 1 / (ENNReal.ofReal p).toReal) :=
          eLpNorm_le_eLpNorm_mul_rpow_measure_univ (ENNReal.one_le_ofReal.mpr hp)
            hf.aestronglyMeasurable.restrict
      _ = eLpNorm (P.toSet.indicator f) (ENNReal.ofReal p) volume *
          ENNReal.ofReal (P.vol ^ (1 - 1 / p)) := by
          rw [← eLpNorm_indicator_eq_eLpNorm_restrict hmeas.nullMeasurableSet,
            Measure.restrict_apply_univ, DyadicCube.volume_toSet, ENNReal.toReal_one, div_one,
            ENNReal.toReal_ofReal hp0, ENNReal.ofReal_rpow_of_nonneg P.vol_pos.le h0]
      _ ≤ _ := mul_le_mul' (eLpNorm_indicator_le f hmeas.nullMeasurableSet) le_rfl
  have hind : AEStronglyMeasurable (P.toSet.indicator f) volume :=
    hf.aestronglyMeasurable.indicator hmeas
  calc |∫ x, P.toSet.indicator f x| ≤ ∫ x, |P.toSet.indicator f x| := abs_integral_le_integral_abs
    _ = (eLpNorm (P.toSet.indicator f) 1 volume).toReal := by
        rw [eLpNorm_one_eq_lintegral_enorm hind, ← integral_norm_eq_lintegral_enorm hind]
        simp only [Real.norm_eq_abs]
    _ ≤ (eLpNorm f (ENNReal.ofReal p) volume * ENNReal.ofReal (P.vol ^ (1 - 1 / p))).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top hf.eLpNorm_ne_top ENNReal.ofReal_ne_top) h1
    _ = P.vol ^ (1 - 1 / p) * (eLpNorm f (ENNReal.ofReal p) volume).toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.rpow_nonneg P.vol_pos.le _), mul_comm]

/-- The generator case of the truncation bound: for a product `∏_j P_j` of dyadic cubes,
`x ↦ 𝟙_{∏ P_j}(x) ∏_j f_j(x_j)` is integrable and
`|∫ 𝟙_{∏ P_j}(x) ∏_j f_j(x_j) dx| ≤ ∏_j |P_j|^{1-1/p_j} · ∏_j ‖f_j‖_{p_j}`. [PROVED] -/
theorem prodSet_integral_bound {n : ℕ} (p : HolderTuple n) (P : Fin n → DyadicCube d)
    (f : Fin n → TestFun d) :
    Integrable (fun x : Fin n → Fin d → ℝ =>
      (DyadicCube.prodSet P).indicator 1 x * ∏ j, (f j : (Fin d → ℝ) → ℝ) (x j)) volume ∧
    |∫ x, (DyadicCube.prodSet P).indicator 1 x * ∏ j, (f j : (Fin d → ℝ) → ℝ) (x j)| ≤
      (∏ j, (P j).vol ^ (1 - 1 / p.p j)) * prodNorm p f := by
  have hfun : (fun x : Fin n → Fin d → ℝ =>
      (DyadicCube.prodSet P).indicator 1 x * ∏ j, (f j : (Fin d → ℝ) → ℝ) (x j)) =
      fun x => ∏ j, (P j).toSet.indicator (f j : (Fin d → ℝ) → ℝ) (x j) := by
    funext x
    by_cases hx : x ∈ DyadicCube.prodSet P
    · rw [Set.indicator_of_mem hx, Pi.one_apply, one_mul]
      exact Finset.prod_congr rfl fun j _ =>
        (Set.indicator_of_mem ((show ∀ j, x j ∈ (P j).toSet from hx) j) _).symm
    · rw [Set.indicator_of_notMem hx, zero_mul]
      have hx' : ¬ ∀ j, x j ∈ (P j).toSet := fun h => hx h
      obtain ⟨j, hj⟩ := not_forall.mp hx'
      exact (Finset.prod_eq_zero (Finset.mem_univ j) (Set.indicator_of_notMem hj _)).symm
  have hint : ∀ j, Integrable ((P j).toSet.indicator (f j : (Fin d → ℝ) → ℝ)) volume := fun j =>
    (memLp_one_iff_integrable.mp (TestFun.memLp (f j).2 1)).indicator (P j).measurableSet_toSet
  rw [hfun]
  refine ⟨?_, ?_⟩
  · rw [volume_pi]
    exact Integrable.fintype_prod (f := fun j => (P j).toSet.indicator (f j : (Fin d → ℝ) → ℝ))
      hint
  · rw [volume_pi,
      integral_fintype_prod_eq_prod (fun j => (P j).toSet.indicator (f j : (Fin d → ℝ) → ℝ)),
      Finset.abs_prod, prodNorm, ← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod₀ (fun j _ => abs_nonneg _) fun j _ => ?_
    exact abs_integral_indicator_le (p.one_lt j).le (TestFun.memLp (f j).2 _) (P j)

/-- The truncation bound for kernels: for every `K ∈ TestFunProd d n` there is `A ≥ 0` such that
`x ↦ K(x) ∏_j f_j(x_j)` is integrable and `|∫ K(x) ∏_j f_j(x_j) dx| ≤ A ∏_j ‖f_j‖_{p_j}` for all
tuples of dyadic test functions. [PROVED] -/
theorem TestFunProd.exists_bound {n : ℕ} (p : HolderTuple n) {K : (Fin n → Fin d → ℝ) → ℝ}
    (hK : K ∈ TestFunProd d n) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ f : Fin n → TestFun d,
      Integrable (fun x => K x * ∏ j, (f j : (Fin d → ℝ) → ℝ) (x j)) volume ∧
      |∫ x, K x * ∏ j, (f j : (Fin d → ℝ) → ℝ) (x j)| ≤ A * prodNorm p f := by
  have hK' : K ∈ Submodule.span ℝ {K : (Fin n → Fin d → ℝ) → ℝ | ∃ P : Fin n → DyadicCube d,
      (∀ i j, (P i).m = (P j).m) ∧ K = (DyadicCube.prodSet P).indicator 1} := hK
  clear hK
  induction hK' using Submodule.span_induction with
  | mem K hK =>
    obtain ⟨P, -, rfl⟩ := hK
    exact ⟨_, Finset.prod_nonneg fun j _ => Real.rpow_nonneg (P j).vol_pos.le _,
      fun f => prodSet_integral_bound p P f⟩
  | zero =>
    refine ⟨0, le_rfl, fun f => ⟨?_, ?_⟩⟩
    · simp
    · simp
  | add K₁ K₂ _ _ h₁ h₂ =>
    obtain ⟨A₁, hA₁, h₁⟩ := h₁
    obtain ⟨A₂, hA₂, h₂⟩ := h₂
    refine ⟨A₁ + A₂, by positivity, fun f => ?_⟩
    obtain ⟨i₁, b₁⟩ := h₁ f
    obtain ⟨i₂, b₂⟩ := h₂ f
    have e : (fun x => (K₁ + K₂) x * ∏ j, (f j : (Fin d → ℝ) → ℝ) (x j)) =
        fun x => K₁ x * ∏ j, (f j : (Fin d → ℝ) → ℝ) (x j) +
          K₂ x * ∏ j, (f j : (Fin d → ℝ) → ℝ) (x j) := by
      funext x
      simp [add_mul]
    refine ⟨by rw [e]; exact i₁.add i₂, ?_⟩
    rw [e, integral_add i₁ i₂, add_mul]
    exact (abs_add_le _ _).trans (add_le_add b₁ b₂)
  | smul c K _ h =>
    obtain ⟨A, hA, h⟩ := h
    refine ⟨|c| * A, by positivity, fun f => ?_⟩
    obtain ⟨i, b⟩ := h f
    have e : (fun x => (c • K) x * ∏ j, (f j : (Fin d → ℝ) → ℝ) (x j)) =
        fun x => c * (K x * ∏ j, (f j : (Fin d → ℝ) → ℝ) (x j)) := by
      funext x
      simp [mul_assoc]
    refine ⟨by rw [e]; exact i.const_mul c, ?_⟩
    rw [e, integral_const_mul, abs_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left b (abs_nonneg c)

/-- Every perfect Calderón–Zygmund form is bounded on dyadic test functions,
`|Λ(f)| ≤ A ∏_j ‖f_j‖_{p_j}` for some finite `A` depending on the form (p. 40, "by the
truncation assumption on the form `Λ`, the constant `A` is finite"). [PROVED] -/
theorem PerfectCZForm.exists_bound {n : ℕ} (T : PerfectCZForm d n) (p : HolderTuple n) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ f : Fin n → TestFun d, |T.form f| ≤ A * prodNorm p f := by
  obtain ⟨K, hK, hform⟩ := T.truncation
  obtain ⟨A, hA, h⟩ := TestFunProd.exists_bound p hK
  exact ⟨A, hA, fun f => by rw [hform]; exact (h f).2⟩

/-- Passing to the limit in `X ≤ (θ^m A₀ + D) Y`, `0 ≤ θ < 1`. [PROVED] -/
theorem le_of_forall_pow_le {X Y θ A₀ D : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hm : ∀ m : ℕ, X ≤ (θ ^ m * A₀ + D) * Y) : X ≤ D * Y := by
  have hlim : Filter.Tendsto (fun m : ℕ => (θ ^ m * A₀ + D) * Y) Filter.atTop
      (nhds ((0 * A₀ + D) * Y)) :=
    (((tendsto_pow_atTop_nhds_zero_of_lt_one hθ0 hθ1).mul_const A₀).add_const D).mul_const Y
  simpa using ge_of_tendsto' hlim hm

/-- **The contraction step** (the main estimate of §2.2–2.8 in the form of p. 43,
`A ≤ A(1-ε)^{1/p_k} + C`): for every `B ≥ 1` there are `0 ≤ θ < 1` and `C₁ ≥ 0`, depending only
on `n`, `d`, `B` and the exponents, such that for every perfect Calderón–Zygmund form, every
admissible collection and every family `b` of testing functions for paths of length `k+2`
satisfying (1.5)–(1.9) with constant `B`, any constant `A ≥ 0` in the testing condition for the
restricted family may be replaced by `A θ + C₁`. [STATEMENT] -/
def ContractionStep (d n k : ℕ) (p : HolderTuple n) : Prop :=
  ∀ B : ℝ, 1 ≤ B → ∃ θ C₁ : ℝ, 0 ≤ θ ∧ θ < 1 ∧ 0 ≤ C₁ ∧
    ∀ (T : PerfectCZForm d n) (C : IPath.Collection n), IPath.Admissible C →
    ∀ b : TestingFamily d n (k + 1), LocalTbHypotheses T p C b B →
    ∀ A : ℝ, 0 ≤ A → TestingCondition T p C (restrictFamily C b) A →
      TestingCondition T p C (restrictFamily C b) (A * θ + C₁)

/-- The main estimate follows from the contraction step by iteration, starting from the
truncation bound (p. 40 and p. 43). [PROVED] -/
theorem restrictedTesting_of_contractionStep {n k : ℕ} {p : HolderTuple n}
    (h : ContractionStep d n k p) : RestrictedTesting d n k p := by
  intro B hB
  obtain ⟨θ, C₁, hθ0, hθ1, hC₁, hstep⟩ := h B hB
  set D : ℝ := C₁ / (1 - θ) with hD
  have h1θ : (1 : ℝ) - θ ≠ 0 := (sub_pos.mpr hθ1).ne'
  have hD0 : 0 ≤ D := div_nonneg hC₁ (by linarith)
  have hDeq : D * θ + C₁ = D := by
    rw [hD]
    field_simp
    ring
  refine ⟨max 1 D, le_max_left _ _, ?_⟩
  intro T C hC b hb
  obtain ⟨A₀, hA₀, hbound⟩ := T.exists_bound p
  have hA₀test : TestingCondition T p C (restrictFamily C b) A₀ :=
    fun _ _ _ _ _ _ f _ _ _ => hbound f
  have hm : ∀ m : ℕ, TestingCondition T p C (restrictFamily C b) (θ ^ m * A₀ + D) := by
    intro m
    induction m with
    | zero =>
      exact hA₀test.mono (by rw [pow_zero, one_mul]; exact le_add_of_nonneg_right hD0)
    | succ m ih =>
      have := hstep T C hC b hb _ (by positivity) ih
      have e : (θ ^ m * A₀ + D) * θ + C₁ = θ ^ (m + 1) * A₀ + D := by
        linear_combination hDeq
      rwa [e] at this
  intro σ hσ Q hQ g hg f hf hl hs
  calc |T.form f| ≤ D * prodNorm p f :=
        le_of_forall_pow_le hθ0 hθ1 fun m => hm m σ hσ Q hQ g hg f hf hl hs
    _ ≤ max 1 D * prodNorm p f :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (prodNorm_nonneg p f)

/-! ### §2.2 The first stopping time (paper, p. 41–42)

A stopping collection is the set of maximal dyadic cubes `P ⊆ Q` with a given property. Such
cubes are pairwise disjoint, every cube with the property lies in a maximal one, and the total
measure `∑_{P} |P|` of the collection is the Lebesgue measure of `⋃_P P` (the collections may
be infinite, so we work with measures of unions throughout). We prove the measure bounds of
p. 41–42 for `𝐏₁`, `𝐏₂` (the Chebyshev argument), `𝐏₄` (through the set `E = Q ∖ ⋃ 𝐏₄`) and
`𝐏₅` (bounded overlap of the parents of the cubes of `𝐏₄`), and deduce the claim (2.7) from the
five bounds. The bound for `𝐏₃`, which involves the form `Λ` and the testing condition, is
treated separately. -/

section StoppingTime

/-- The lower bound for `|E|` in the treatment of `𝐏₄` (p. 42): from
`(7/8)|Q| ≤ |E|^{1-1/q} ‖u‖_q` and `‖u‖_q^q ≤ B|Q|` one obtains
`(7/8)^{q/(q-1)} B^{-1/(q-1)} |Q| ≤ |E|`. [PROVED] -/
theorem P4_lower_bound {x N V B q : ℝ} (hx : 0 ≤ x) (hN : 0 ≤ N) (hV : 0 < V) (hB : 1 ≤ B)
    (hq : 1 < q) (h1 : (7 / 8) * V ≤ x ^ (1 - 1 / q) * N) (h2 : N ^ q ≤ B * V) :
    (7 / 8 : ℝ) ^ (q / (q - 1)) * B ^ (-(1 / (q - 1))) * V ≤ x := by
  have hq0 : 0 < q := by linarith
  have hs : 0 < q - 1 := by linarith
  have hB0 : 0 < B := by linarith
  have hV0 : V ≠ 0 := hV.ne'
  -- raise `h1` to the power `q`
  have hA : ((7 / 8 : ℝ) * V) ^ q ≤ x ^ (q - 1) * N ^ q := by
    have := Real.rpow_le_rpow (by positivity) h1 hq0.le
    rwa [Real.mul_rpow (Real.rpow_nonneg hx _) hN, ← Real.rpow_mul hx,
      show (1 - 1 / q) * q = q - 1 by rw [sub_mul, one_mul, one_div, inv_mul_cancel₀ hq0.ne']]
      at this
  -- use `h2` and divide by `V`
  have hB' : (7 / 8 : ℝ) ^ q * V ^ (q - 1) ≤ x ^ (q - 1) * B := by
    have h3 : x ^ (q - 1) * N ^ q ≤ x ^ (q - 1) * (B * V) :=
      mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg hx _)
    have h4 : ((7 / 8 : ℝ) * V) ^ q = (7 / 8 : ℝ) ^ q * V ^ (q - 1) * V := by
      rw [Real.mul_rpow (by norm_num) hV.le, Real.rpow_sub_one hV0 q]
      field_simp
    have h5 := hA.trans h3
    rw [h4] at h5
    exact le_of_mul_le_mul_right (by linarith) hV
  -- take the power `1/(q-1)`
  have hC : ((7 / 8 : ℝ) ^ q * V ^ (q - 1) / B) ^ (1 / (q - 1)) ≤
      (x ^ (q - 1)) ^ (1 / (q - 1)) := by
    apply Real.rpow_le_rpow (by positivity) _ (by positivity)
    rwa [div_le_iff₀ hB0]
  have hxx : (x ^ (q - 1)) ^ (1 / (q - 1)) = x := by
    rw [one_div, Real.rpow_rpow_inv hx hs.ne']
  have hL : ((7 / 8 : ℝ) ^ q * V ^ (q - 1) / B) ^ (1 / (q - 1)) =
      (7 / 8 : ℝ) ^ (q / (q - 1)) * B ^ (-(1 / (q - 1))) * V := by
    rw [Real.div_rpow (by positivity) hB0.le, Real.mul_rpow (by positivity) (by positivity),
      ← Real.rpow_mul (by norm_num), ← Real.rpow_mul hV.le, Real.rpow_neg hB0.le,
      mul_one_div_cancel hs.ne', Real.rpow_one, show q * (1 / (q - 1)) = q / (q - 1) by ring]
    ring
  rw [hL, hxx] at hC
  exact hC

/-- There are countably many dyadic cubes. -/
instance : Countable (DyadicCube d) :=
  Function.Injective.countable (f := fun P : DyadicCube d => (P.m, P.l)) fun P R h => by
    ext i
    · exact congrArg Prod.fst h
    · exact congrArg (fun q : ℤ × (Fin d → ℤ) => q.2 i) h

/-- The maximal cubes of a collection of dyadic cubes. -/
def maximal (S : Set (DyadicCube d)) : Set (DyadicCube d) :=
  {P | P ∈ S ∧ ∀ P' ∈ S, P.toSet ⊆ P'.toSet → P' = P}

theorem maximal_subset (S : Set (DyadicCube d)) : maximal S ⊆ S := fun _ h => h.1

/-- The maximal cubes of `{P ∈ S | X P}` satisfy `X`. [PROVED] -/
theorem prop_of_mem_maximal_sep {S : Set (DyadicCube d)} {X : DyadicCube d → Prop}
    {P : DyadicCube d} (h : P ∈ maximal {P ∈ S | X P}) : X P := h.1.2

/-- The maximal cubes of `{P ∈ S | X P}` lie in `S`. [PROVED] -/
theorem mem_of_mem_maximal_sep {S : Set (DyadicCube d)} {X : DyadicCube d → Prop}
    {P : DyadicCube d} (h : P ∈ maximal {P ∈ S | X P}) : P ∈ S := h.1.1

/-- Maximal cubes are pairwise disjoint (nested-or-disjoint). [PROVED] -/
theorem maximal_pairwiseDisjoint (S : Set (DyadicCube d)) :
    (maximal S).PairwiseDisjoint DyadicCube.toSet := by
  intro P hP R hR hne
  change Disjoint P.toSet R.toSet
  rcases le_total P.m R.m with h | h
  · rcases DyadicCube.subset_or_disjoint P R h with hsub | hdis
    · exact absurd (hP.2 R hR.1 hsub).symm hne
    · exact hdis
  · rcases DyadicCube.subset_or_disjoint R P h with hsub | hdis
    · exact absurd (hR.2 P hP.1 hsub) hne
    · exact hdis.symm

/-- Every cube of a collection of subcubes of `Q` lies in a maximal cube of the collection
(induction on the number of scales between the cube and `Q`). [PROVED] -/
theorem exists_maximal_superset (hd : d ≠ 0) {Q : DyadicCube d} {S : Set (DyadicCube d)}
    (hS : S ⊆ Q.tree) {P : DyadicCube d} (hP : P ∈ S) :
    ∃ P' ∈ maximal S, P.toSet ⊆ P'.toSet := by
  suffices h : ∀ N : ℕ, ∀ P ∈ S, Q.m - P.m ≤ (N : ℤ) →
      ∃ P' ∈ maximal S, P.toSet ⊆ P'.toSet from h _ P hP (Int.self_le_toNat _)
  intro N
  induction N with
  | zero =>
    intro P hP hN
    refine ⟨P, ⟨hP, fun P' hP' hsub => ?_⟩, le_rfl⟩
    have h1 := DyadicCube.m_le_of_subset hd hsub
    have h2 := DyadicCube.m_le_of_subset hd (hS hP')
    exact (DyadicCube.eq_of_subset_of_m_eq hsub (by omega)).symm
  | succ N ih =>
    intro P hP hN
    by_cases hmax : ∀ P' ∈ S, P.toSet ⊆ P'.toSet → P' = P
    · exact ⟨P, ⟨hP, hmax⟩, le_rfl⟩
    · obtain ⟨P', hP', hsub, hne⟩ : ∃ P' ∈ S, P.toSet ⊆ P'.toSet ∧ P' ≠ P := by
        by_contra h
        exact hmax fun P' hP' hsub =>
          Classical.byContradiction fun hne => h ⟨P', hP', hsub, hne⟩
      have hlt : P.m < P'.m := lt_of_le_of_ne (DyadicCube.m_le_of_subset hd hsub)
        fun h => hne (DyadicCube.eq_of_subset_of_m_eq hsub h).symm
      have h2 := DyadicCube.m_le_of_subset hd (hS hP')
      obtain ⟨P'', hP'', hsub'⟩ := ih P' hP' (by omega)
      exact ⟨P'', hP'', hsub.trans hsub'⟩

/-- Pairwise disjointness of a collection, indexed by the collection itself. [PROVED] -/
theorem pairwise_disjoint_subtype {Ps : Set (DyadicCube d)}
    (h : Ps.PairwiseDisjoint DyadicCube.toSet) :
    Pairwise (Function.onFun Disjoint fun P : Ps => (P : DyadicCube d).toSet) :=
  fun P R hne => h P.2 R.2 fun hPR => hne (Subtype.ext hPR)

/-- The union of a collection of cubes is measurable. [PROVED] -/
theorem measurableSet_biUnion_toSet (Ps : Set (DyadicCube d)) :
    MeasurableSet (⋃ P ∈ Ps, P.toSet) :=
  MeasurableSet.biUnion Ps.to_countable fun P _ => P.measurableSet_toSet

/-- The union of subcubes of `Q` lies in `Q`. [PROVED] -/
theorem biUnion_toSet_subset {Q : DyadicCube d} {Ps : Set (DyadicCube d)} (h : Ps ⊆ Q.tree) :
    (⋃ P ∈ Ps, P.toSet) ⊆ Q.toSet :=
  Set.iUnion₂_subset fun _ hP => h hP

/-- `|⋃_{P ∈ 𝐏} P| = ∑_{P ∈ 𝐏} |P|` for a pairwise disjoint collection. [PROVED] -/
theorem volume_biUnion_eq_tsum {Ps : Set (DyadicCube d)}
    (h : Ps.PairwiseDisjoint DyadicCube.toSet) :
    volume (⋃ P ∈ Ps, P.toSet) = ∑' P : Ps, ENNReal.ofReal (P : DyadicCube d).vol := by
  rw [measure_biUnion Ps.to_countable h fun P _ => P.measurableSet_toSet]
  simp only [DyadicCube.volume_toSet]

/-- **The Chebyshev argument for `𝐏₁`, `𝐏₂`** (p. 41): if the cubes of a pairwise disjoint
collection `𝐏 ⊆ 𝒟(Q)` satisfy `|P| ∫_Q F_j ≤ a ∫_P F_j` for one of the functions `F_j`,
`j ∈ J`, then `|⋃ 𝐏| ≤ a · #J`. [PROVED] -/
theorem volume_biUnion_le_of_chebyshev {Q : DyadicCube d} {Ps : Set (DyadicCube d)}
    (hPs : Ps ⊆ Q.tree) (hdisj : Ps.PairwiseDisjoint DyadicCube.toSet) {ι : Type*}
    (J : Finset ι) (F : ι → (Fin d → ℝ) → ENNReal) (hF0 : ∀ j ∈ J, ∫⁻ x in Q.toSet, F j x ≠ 0)
    (hF : ∀ j ∈ J, ∫⁻ x in Q.toSet, F j x ≠ ⊤) {a : ENNReal}
    (h : ∀ P ∈ Ps, ∃ j ∈ J, volume P.toSet * ∫⁻ x in Q.toSet, F j x ≤
      a * ∫⁻ x in P.toSet, F j x) :
    volume (⋃ P ∈ Ps, P.toSet) ≤ a * J.card := by
  have hU : (⋃ P ∈ Ps, P.toSet) = ⋃ P : Ps, (P : DyadicCube d).toSet :=
    Set.biUnion_eq_iUnion Ps _
  calc volume (⋃ P ∈ Ps, P.toSet)
      = ∑' P : Ps, volume (P : DyadicCube d).toSet :=
        measure_biUnion Ps.to_countable hdisj fun P _ => P.measurableSet_toSet
    _ ≤ ∑' P : Ps, ∑ j ∈ J, (a / ∫⁻ x in Q.toSet, F j x) *
          ∫⁻ x in (P : DyadicCube d).toSet, F j x := by
        refine ENNReal.tsum_le_tsum fun P => ?_
        obtain ⟨j, hj, hPj⟩ := h P P.2
        calc volume (P : DyadicCube d).toSet
            = volume (P : DyadicCube d).toSet * (∫⁻ x in Q.toSet, F j x) /
                ∫⁻ x in Q.toSet, F j x := by
              rw [ENNReal.mul_div_cancel_right (hF0 j hj) (hF j hj)]
          _ ≤ a * (∫⁻ x in (P : DyadicCube d).toSet, F j x) / ∫⁻ x in Q.toSet, F j x :=
              ENNReal.div_le_div_right hPj _
          _ = (a / ∫⁻ x in Q.toSet, F j x) * ∫⁻ x in (P : DyadicCube d).toSet, F j x :=
              ENNReal.mul_div_right_comm
          _ ≤ ∑ j ∈ J, (a / ∫⁻ x in Q.toSet, F j x) *
                ∫⁻ x in (P : DyadicCube d).toSet, F j x :=
              Finset.single_le_sum (f := fun j => (a / ∫⁻ x in Q.toSet, F j x) *
                ∫⁻ x in (P : DyadicCube d).toSet, F j x) (fun _ _ => zero_le) hj
    _ = ∑ j ∈ J, (a / ∫⁻ x in Q.toSet, F j x) *
          ∑' P : Ps, ∫⁻ x in (P : DyadicCube d).toSet, F j x := by
        rw [Summable.tsum_finsetSum fun _ _ => ENNReal.summable]
        exact Finset.sum_congr rfl fun j _ => ENNReal.tsum_mul_left
    _ = ∑ j ∈ J, (a / ∫⁻ x in Q.toSet, F j x) * ∫⁻ x in ⋃ P ∈ Ps, P.toSet, F j x := by
        rw [hU]
        exact Finset.sum_congr rfl fun j _ => by
          rw [lintegral_iUnion (fun P => DyadicCube.measurableSet_toSet _)
            (pairwise_disjoint_subtype hdisj)]
    _ ≤ ∑ j ∈ J, (a / ∫⁻ x in Q.toSet, F j x) * ∫⁻ x in Q.toSet, F j x :=
        Finset.sum_le_sum fun j _ =>
          mul_le_mul' le_rfl (lintegral_mono_set (biUnion_toSet_subset hPs))
    _ = ∑ _j ∈ J, a :=
        Finset.sum_congr rfl fun j hj => ENNReal.div_mul_cancel (hF0 j hj) (hF j hj)
    _ = a * J.card := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]

/-- The stopping conditions (2.3), (2.4) in the form used by the Chebyshev argument: from
`c ∫_Q F ≤ |P|⁻¹ ∫_P F` one gets `|P| ∫_Q F ≤ c⁻¹ ∫_P F`. [PROVED] -/
theorem chebyshev_condition (P : DyadicCube d) {I J : ENNReal} {c : ℝ} (hc : 0 < c)
    (h : ENNReal.ofReal c * I ≤ (volume P.toSet)⁻¹ * J) :
    volume P.toSet * I ≤ ENNReal.ofReal c⁻¹ * J := by
  have hP0 : volume P.toSet ≠ 0 := by
    rw [P.volume_toSet]
    exact (ENNReal.ofReal_pos.mpr P.vol_pos).ne'
  have hPt : volume P.toSet ≠ ⊤ := by
    rw [P.volume_toSet]
    exact ENNReal.ofReal_ne_top
  have hc0 : ENNReal.ofReal c ≠ 0 := (ENNReal.ofReal_pos.mpr hc).ne'
  calc volume P.toSet * I
      = (ENNReal.ofReal c)⁻¹ * ENNReal.ofReal c * (volume P.toSet * I) := by
        rw [ENNReal.inv_mul_cancel hc0 ENNReal.ofReal_ne_top, one_mul]
    _ = ENNReal.ofReal c⁻¹ * (volume P.toSet * (ENNReal.ofReal c * I)) := by
        rw [ENNReal.ofReal_inv_of_pos hc]
        ring
    _ ≤ ENNReal.ofReal c⁻¹ * (volume P.toSet * ((volume P.toSet)⁻¹ * J)) :=
        mul_le_mul' le_rfl (mul_le_mul' le_rfl h)
    _ = ENNReal.ofReal c⁻¹ * J := by
        rw [← mul_assoc (volume P.toSet) (volume P.toSet)⁻¹ J, ENNReal.mul_inv_cancel hP0 hPt,
          one_mul]

/-- Hölder's inequality on a measurable set of finite measure:
`|∫_s f| ≤ |s|^{1-1/p} ‖f‖_p` for `f ∈ L^p`, `p ≥ 1`. [PROVED] -/
theorem abs_setIntegral_le_rpow_mul_lpNorm {f : (Fin d → ℝ) → ℝ} {p : ℝ} (hp : 1 ≤ p)
    (hf : MemLp f (ENNReal.ofReal p) volume) {s : Set (Fin d → ℝ)} (hs : MeasurableSet s)
    (hfin : volume s ≠ ⊤) :
    |∫ x in s, f x| ≤ (volume s).toReal ^ (1 - 1 / p) * lpNorm f p := by
  have hp0 : (0 : ℝ) ≤ p := by linarith
  have h0 : 0 ≤ 1 - 1 / p := sub_nonneg.mpr ((div_le_one (by linarith)).mpr hp)
  have h1 : eLpNorm (s.indicator f) 1 volume ≤
      eLpNorm f (ENNReal.ofReal p) volume * volume s ^ (1 - 1 / p) := by
    calc eLpNorm (s.indicator f) 1 volume
        = eLpNorm f 1 (volume.restrict s) :=
          eLpNorm_indicator_eq_eLpNorm_restrict hs.nullMeasurableSet
      _ ≤ eLpNorm f (ENNReal.ofReal p) (volume.restrict s) *
          (volume.restrict s) Set.univ ^
            (1 / (1 : ENNReal).toReal - 1 / (ENNReal.ofReal p).toReal) :=
          eLpNorm_le_eLpNorm_mul_rpow_measure_univ (ENNReal.one_le_ofReal.mpr hp)
            hf.aestronglyMeasurable.restrict
      _ = eLpNorm (s.indicator f) (ENNReal.ofReal p) volume * volume s ^ (1 - 1 / p) := by
          rw [← eLpNorm_indicator_eq_eLpNorm_restrict hs.nullMeasurableSet,
            Measure.restrict_apply_univ, ENNReal.toReal_one, div_one, ENNReal.toReal_ofReal hp0]
      _ ≤ _ := mul_le_mul' (eLpNorm_indicator_le f hs.nullMeasurableSet) le_rfl
  have hind : AEStronglyMeasurable (s.indicator f) volume := hf.aestronglyMeasurable.indicator hs
  have hfin' : volume s ^ (1 - 1 / p) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg h0 hfin
  calc |∫ x in s, f x| = |∫ x, s.indicator f x| := by rw [integral_indicator hs]
    _ ≤ ∫ x, |s.indicator f x| := abs_integral_le_integral_abs
    _ = (eLpNorm (s.indicator f) 1 volume).toReal := by
        rw [eLpNorm_one_eq_lintegral_enorm hind, ← integral_norm_eq_lintegral_enorm hind]
        simp only [Real.norm_eq_abs]
    _ ≤ (eLpNorm f (ENNReal.ofReal p) volume * volume s ^ (1 - 1 / p)).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top hf.eLpNorm_ne_top hfin') h1
    _ = (volume s).toReal ^ (1 - 1 / p) * (eLpNorm f (ENNReal.ofReal p) volume).toReal := by
        rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, mul_comm]

/-- `‖u‖_q^q = ∫ |u|^q` for `u ∈ L^q`, `q > 0`. [PROVED] -/
theorem lpNorm_rpow_eq_integral {u : (Fin d → ℝ) → ℝ} {q : ℝ} (hq : 0 < q)
    (hu : MemLp u (ENNReal.ofReal q) volume) : lpNorm u q ^ q = ∫ x, |u x| ^ q := by
  have h := hu.eLpNorm_eq_integral_rpow_norm (ENNReal.ofReal_pos.mpr hq).ne' ENNReal.ofReal_ne_top
  have hnn : 0 ≤ ∫ x, ‖u x‖ ^ q := integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _
  unfold lpNorm
  rw [h, ENNReal.toReal_ofReal hq.le, ENNReal.toReal_ofReal (Real.rpow_nonneg hnn _),
    Real.rpow_inv_rpow hnn hq.ne']
  simp only [Real.norm_eq_abs]

/-- **The bound for `𝐏₄`** (p. 42): if `u` is supported on `Q` with `∫ u = |Q|` and
`∫ |u|^q ≤ B |Q|`, and `𝐏 ⊆ 𝒟(Q)` is a pairwise disjoint collection with `|[u]_P| ≤ 1/8` on
its cubes, then `|⋃ 𝐏| ≤ (1 - 8ε)|Q|` whenever `8ε ≤ (7/8)^{q/(q-1)} B^{-1/(q-1)}`. The proof
estimates `|∫_E u| ≥ (7/8)|Q|` on `E = Q ∖ ⋃ 𝐏` and applies Hölder's inequality. [PROVED] -/
theorem volume_biUnion_le_of_small_avg {Q : DyadicCube d} {Ps : Set (DyadicCube d)}
    (hPs : Ps ⊆ Q.tree) (hdisj : Ps.PairwiseDisjoint DyadicCube.toSet) {u : (Fin d → ℝ) → ℝ}
    {q B ε : ℝ} (hq : 1 < q) (hB : 1 ≤ B)
    (h8ε : 8 * ε ≤ (7 / 8 : ℝ) ^ (q / (q - 1)) * B ^ (-(1 / (q - 1))))
    (hu : MemLp u (ENNReal.ofReal q) volume) (husupp : SupportedOn u Q)
    (humean : ∫ x, u x = Q.vol) (hunorm : ∫ x, |u x| ^ q ≤ B * Q.vol)
    (hsmall : ∀ P ∈ Ps, |avg P u| ≤ 1 / 8) :
    volume (⋃ P ∈ Ps, P.toSet) ≤ ENNReal.ofReal ((1 - 8 * ε) * Q.vol) := by
  set U := ⋃ P ∈ Ps, P.toSet with hUdef
  have hUmeas : MeasurableSet U := measurableSet_biUnion_toSet Ps
  have hUQ : U ⊆ Q.toSet := biUnion_toSet_subset hPs
  have hQfin : volume Q.toSet ≠ ⊤ := by
    rw [Q.volume_toSet]
    exact ENNReal.ofReal_ne_top
  have hUfin : volume U ≠ ⊤ := ne_top_of_le_ne_top hQfin (measure_mono hUQ)
  set E := Q.toSet \ U with hEdef
  have hEmeas : MeasurableSet E := Q.measurableSet_toSet.diff hUmeas
  have hEfin : volume E ≠ ⊤ := ne_top_of_le_ne_top hQfin (measure_mono Set.sdiff_subset)
  have hV := Q.vol_pos
  -- the real volumes `y = |U|`, `x = |E| = |Q| - |U|`
  set y := (volume U).toReal with hy
  set x := (volume E).toReal with hx
  have hyV : y ≤ Q.vol := by
    rw [hy, ← ENNReal.toReal_ofReal hV.le, ← Q.volume_toSet]
    exact ENNReal.toReal_mono hQfin (measure_mono hUQ)
  have hxy : x = Q.vol - y := by
    rw [hx, hEdef, measure_sdiff hUQ hUmeas.nullMeasurableSet hUfin,
      ENNReal.toReal_sub_of_le (measure_mono hUQ) hQfin, Q.volume_toSet,
      ENNReal.toReal_ofReal hV.le]
  have hx0 : 0 ≤ x := ENNReal.toReal_nonneg
  -- integrability
  have hint : IntegrableOn u Q.toSet volume :=
    (hu.restrict Q.toSet).integrable (ENNReal.one_le_ofReal.mpr hq.le)
  have hintU : IntegrableOn u U volume := hint.mono_set hUQ
  have hintE : IntegrableOn u E volume := hint.mono_set Set.sdiff_subset
  have hQint : ∫ x in Q.toSet, u x = Q.vol := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => husupp x hx, humean]
  have hsplit : ∫ x in Q.toSet, u x = (∫ x in E, u x) + ∫ x in U, u x := by
    have := setIntegral_union Set.disjoint_sdiff_left hUmeas hintE hintU
    rw [Set.sdiff_union_of_subset hUQ, ← hEdef] at this
    exact this
  -- `|∫_U u| ≤ |U|/8`
  have hUint : |∫ x in U, u x| ≤ y / 8 := by
    have hU' : U = ⋃ P : Ps, (P : DyadicCube d).toSet := Set.biUnion_eq_iUnion Ps _
    have hsum : volume U = ∑' P : Ps, volume (P : DyadicCube d).toSet :=
      measure_biUnion Ps.to_countable hdisj fun P _ => P.measurableSet_toSet
    have hsumm : Summable fun P : Ps => (volume (P : DyadicCube d).toSet).toReal :=
      ENNReal.summable_toReal (by rw [← hsum]; exact hUfin)
    have hterm : ∀ P : Ps, |∫ x in (P : DyadicCube d).toSet, u x| ≤
        (volume (P : DyadicCube d).toSet).toReal / 8 := by
      intro P
      rw [← avg_mul_vol, abs_mul, abs_of_pos (P : DyadicCube d).vol_pos, DyadicCube.volume_toSet,
        ENNReal.toReal_ofReal (P : DyadicCube d).vol_pos.le]
      have := mul_le_mul_of_nonneg_right (hsmall P P.2) (P : DyadicCube d).vol_pos.le
      linarith
    have hsumm' : Summable fun P : Ps => |∫ x in (P : DyadicCube d).toSet, u x| :=
      Summable.of_nonneg_of_le (fun _ => abs_nonneg _) hterm (hsumm.div_const 8)
    have hintU' : IntegrableOn u (⋃ P : Ps, (P : DyadicCube d).toSet) volume := by
      rw [← hU']
      exact hintU
    calc |∫ x in U, u x| = |∑' P : Ps, ∫ x in (P : DyadicCube d).toSet, u x| := by
          rw [hU', integral_iUnion (fun P => DyadicCube.measurableSet_toSet _)
            (pairwise_disjoint_subtype hdisj) hintU']
      _ ≤ ∑' P : Ps, |∫ x in (P : DyadicCube d).toSet, u x| := by
          have := norm_tsum_le_tsum_norm
            (f := fun P : Ps => ∫ x in (P : DyadicCube d).toSet, u x)
            (by simpa only [Real.norm_eq_abs] using hsumm')
          simpa only [Real.norm_eq_abs] using this
      _ ≤ ∑' P : Ps, (volume (P : DyadicCube d).toSet).toReal / 8 :=
          hsumm'.tsum_le_tsum hterm (hsumm.div_const 8)
      _ = y / 8 := by
          rw [tsum_div_const, hy, hsum, ENNReal.tsum_toReal_eq fun P =>
            ne_top_of_le_ne_top hQfin (measure_mono (hPs P.2))]
  -- `(7/8)|Q| ≤ |∫_E u|`
  have hE78 : (7 / 8) * Q.vol ≤ |∫ x in E, u x| := by
    have h2 : Q.vol - |∫ x in U, u x| ≤ |∫ x in E, u x| := by
      have := abs_sub_abs_le_abs_sub (∫ x in Q.toSet, u x) (∫ x in U, u x)
      have e : (∫ x in Q.toSet, u x) - ∫ x in U, u x = ∫ x in E, u x := by
        rw [hsplit]
        ring
      rw [e, hQint, abs_of_pos hV] at this
      exact this
    linarith [hUint, hyV]
  -- Hölder and the norm bound
  have hH : |∫ x in E, u x| ≤ x ^ (1 - 1 / q) * lpNorm u q :=
    abs_setIntegral_le_rpow_mul_lpNorm hq.le hu hEmeas hEfin
  have hN : lpNorm u q ^ q ≤ B * Q.vol := by
    rw [lpNorm_rpow_eq_integral (by linarith) hu]
    exact hunorm
  have hlow := P4_lower_bound hx0 ENNReal.toReal_nonneg hV hB hq (hE78.trans hH) hN
  have hyle : y ≤ (1 - 8 * ε) * Q.vol := by
    linarith [hlow, mul_le_mul_of_nonneg_right h8ε hV.le, hxy]
  calc volume U = ENNReal.ofReal y := by rw [hy, ENNReal.ofReal_toReal hUfin]
    _ ≤ ENNReal.ofReal ((1 - 8 * ε) * Q.vol) := ENNReal.ofReal_le_ofReal hyle

/-- **The bound for `𝐏₅`** (p. 42): if every cube of `𝐏₅` is contained in at least `M` cubes
which are parents of cubes of the pairwise disjoint collection `𝐏₄`, then
`M |⋃ 𝐏₅| ≤ 2^d |⋃ 𝐏₄|`. The proof integrates the counting function
`x ↦ #{P' ∈ 𝐏₄ : x ∈ parents(P)'}`. [PROVED] -/
theorem volume_biUnion_le_of_overlap {Ps₄ Ps₅ : Set (DyadicCube d)}
    (hdisj : Ps₄.PairwiseDisjoint DyadicCube.toSet) {M : ℝ}
    (h5 : ∀ P ∈ Ps₅, ∃ S : Finset (DyadicCube d), M ≤ S.card ∧
      ∀ R ∈ S, (∃ P' ∈ Ps₄, R = P'.parent) ∧ P.toSet ⊆ R.toSet) :
    ENNReal.ofReal M * volume (⋃ P ∈ Ps₅, P.toSet) ≤ 2 ^ d * volume (⋃ P ∈ Ps₄, P.toSet) := by
  have hNint : ∫⁻ x, ∑' P' : Ps₄, (P' : DyadicCube d).parent.toSet.indicator 1 x =
      2 ^ d * volume (⋃ P ∈ Ps₄, P.toSet) := by
    rw [lintegral_tsum fun P' => (measurable_one.indicator (DyadicCube.measurableSet_toSet
      _)).aemeasurable,
      measure_biUnion Ps₄.to_countable hdisj fun P _ => P.measurableSet_toSet,
      ← ENNReal.tsum_mul_left]
    refine tsum_congr fun P' => ?_
    rw [lintegral_indicator_one (DyadicCube.measurableSet_toSet _), DyadicCube.volume_toSet,
      DyadicCube.volume_toSet, DyadicCube.vol_parent, ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
  have hlow : ∀ x ∈ ⋃ P ∈ Ps₅, P.toSet,
      ENNReal.ofReal M ≤ ∑' P' : Ps₄, (P' : DyadicCube d).parent.toSet.indicator 1 x := by
    intro x hx
    obtain ⟨P, hP, hxP⟩ := Set.mem_iUnion₂.mp hx
    obtain ⟨S, hM, hS⟩ := h5 P hP
    choose φ hφ using fun R : S => (hS R R.2).1
    have hψ : Function.Injective fun R : S => (⟨φ R, (hφ R).1⟩ : Ps₄) := by
      intro R R' h
      apply Subtype.ext
      rw [(hφ R).2, (hφ R').2]
      exact congrArg DyadicCube.parent (congrArg Subtype.val h)
    calc ENNReal.ofReal M ≤ (S.card : ENNReal) := by
          rw [← ENNReal.ofReal_natCast]
          exact ENNReal.ofReal_le_ofReal hM
      _ = ∑ _R : S, (1 : ENNReal) := by simp
      _ = ∑ R : S, (φ R).parent.toSet.indicator 1 x :=
          Finset.sum_congr rfl fun R _ => by
            rw [Set.indicator_of_mem (show x ∈ (φ R).parent.toSet by
              rw [← (hφ R).2]; exact (hS R R.2).2 hxP)]
            rfl
      _ = ∑' R : S, (φ R).parent.toSet.indicator 1 x := (tsum_fintype _).symm
      _ ≤ ∑' P' : Ps₄, (P' : DyadicCube d).parent.toSet.indicator 1 x :=
          ENNReal.tsum_comp_le_tsum_of_injective hψ
            fun P' : Ps₄ => (P' : DyadicCube d).parent.toSet.indicator 1 x
  calc ENNReal.ofReal M * volume (⋃ P ∈ Ps₅, P.toSet)
      = ∫⁻ x in ⋃ P ∈ Ps₅, P.toSet, ENNReal.ofReal M := (setLIntegral_const _ _).symm
    _ ≤ ∫⁻ x in ⋃ P ∈ Ps₅, P.toSet,
          ∑' P' : Ps₄, (P' : DyadicCube d).parent.toSet.indicator 1 x :=
        setLIntegral_mono' (measurableSet_biUnion_toSet Ps₅) hlow
    _ ≤ ∫⁻ x, ∑' P' : Ps₄, (P' : DyadicCube d).parent.toSet.indicator 1 x :=
        setLIntegral_le_lintegral _ _
    _ = _ := hNint

/-- **The claim (2.7)** (p. 41–42): if the five collections satisfy
`|⋃ 𝐏₁|, |⋃ 𝐏₂|, |⋃ 𝐏₃|, |⋃ 𝐏₅| ≤ ε|Q|` and `|⋃ 𝐏₄| ≤ (1 - 8ε)|Q|`, then the maximal cubes
of `𝐏₁ ∪ ⋯ ∪ 𝐏₅` have total measure at most `(1 - ε)|Q|`. [PROVED] -/
theorem volume_maximal_union_le {Q : DyadicCube d} {S₁ S₂ S₃ S₄ S₅ : Set (DyadicCube d)}
    {ε : ℝ} (hε : 0 ≤ ε) (hε8 : ε ≤ 1 / 8)
    (h₁ : volume (⋃ P ∈ S₁, P.toSet) ≤ ENNReal.ofReal (ε * Q.vol))
    (h₂ : volume (⋃ P ∈ S₂, P.toSet) ≤ ENNReal.ofReal (ε * Q.vol))
    (h₃ : volume (⋃ P ∈ S₃, P.toSet) ≤ ENNReal.ofReal (2 * ε * Q.vol))
    (h₄ : volume (⋃ P ∈ S₄, P.toSet) ≤ ENNReal.ofReal ((1 - 8 * ε) * Q.vol))
    (h₅ : volume (⋃ P ∈ S₅, P.toSet) ≤ ENNReal.ofReal (ε * Q.vol)) :
    volume (⋃ P ∈ maximal (S₁ ∪ S₂ ∪ S₃ ∪ S₄ ∪ S₅), P.toSet) ≤
      ENNReal.ofReal ((1 - ε) * Q.vol) := by
  have hV := Q.vol_pos
  have e1 : 0 ≤ ε * Q.vol := mul_nonneg hε hV.le
  have e3 : 0 ≤ 2 * ε * Q.vol := by positivity
  have e4 : 0 ≤ (1 - 8 * ε) * Q.vol := mul_nonneg (by linarith) hV.le
  calc volume (⋃ P ∈ maximal (S₁ ∪ S₂ ∪ S₃ ∪ S₄ ∪ S₅), P.toSet)
      ≤ volume (⋃ P ∈ S₁ ∪ S₂ ∪ S₃ ∪ S₄ ∪ S₅, P.toSet) :=
        measure_mono (Set.biUnion_subset_biUnion_left (maximal_subset _))
    _ = volume ((⋃ P ∈ S₁, P.toSet) ∪ (⋃ P ∈ S₂, P.toSet) ∪ (⋃ P ∈ S₃, P.toSet) ∪
          (⋃ P ∈ S₄, P.toSet) ∪ (⋃ P ∈ S₅, P.toSet)) := by
        simp only [Set.biUnion_union]
    _ ≤ volume (⋃ P ∈ S₁, P.toSet) + volume (⋃ P ∈ S₂, P.toSet) + volume (⋃ P ∈ S₃, P.toSet) +
          volume (⋃ P ∈ S₄, P.toSet) + volume (⋃ P ∈ S₅, P.toSet) := by
        refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
        refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
        refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
        exact measure_union_le _ _
    _ ≤ ENNReal.ofReal (ε * Q.vol) + ENNReal.ofReal (ε * Q.vol) +
          ENNReal.ofReal (2 * ε * Q.vol) +
          ENNReal.ofReal ((1 - 8 * ε) * Q.vol) + ENNReal.ofReal (ε * Q.vol) := by
        gcongr
    _ = ENNReal.ofReal (ε * Q.vol + ε * Q.vol + 2 * ε * Q.vol + (1 - 8 * ε) * Q.vol +
          ε * Q.vol) := by
        rw [ENNReal.ofReal_add (by linarith) e1, ENNReal.ofReal_add (by linarith) e4,
          ENNReal.ofReal_add (by linarith) e3, ENNReal.ofReal_add e1 e1]
    _ ≤ ENNReal.ofReal ((1 - ε) * Q.vol) := ENNReal.ofReal_le_ofReal (by nlinarith [e1])

end StoppingTime

/-! ### §2.2 (continued) The collection `𝐏₃` (paper, p. 41–42)

The cubes of `𝐏₃` are detected by the form itself: `P ∈ 𝐏₃` if some nonzero mean-zero `ρ`
supported on `P` has `|Λ_P(ρ, u)| ≥ B F ε^{-1} (|P|/|Q|)^{1-1/r} ‖ρ‖_r ‖u‖_q`, where
`Λ_P(ρ, u) = Λ(f₁𝟙_P, …, ρ𝟙_P, u𝟙_P, …, f_n𝟙_P)` is the form with all entries truncated to `P`,
`ρ` in the slot of `h` and `u` in its own slot. We write `Λ_P(·, u)` as the linear map
`slotForm T a g P`, where `g` collects the frozen entries (with `u` in its slot) and `a` is the
free slot. The bound `∑_{𝐏₃} |P| ≤ ε|Q|` is obtained by normalising the `ρ_P`, moving the
truncations from `P` to `Q` (perfect smoothness (1.2)), summing, and applying the testing
condition to `∑ ρ_P`. Since the collection may be infinite, the argument runs over finite
subfamilies; this replaces the paper's implicit finiteness of `𝐏₃`. -/

section P3Bound

/-- A dyadic test function truncated to a dyadic cube is a dyadic test function (the product
of two cube indicators is a cube indicator or zero). [PROVED] -/
theorem TestFun.truncate_mem (P : DyadicCube d) {g : (Fin d → ℝ) → ℝ} (hg : g ∈ TestFun d) :
    truncate P g ∈ TestFun d := by
  have hg' : g ∈ Submodule.span ℝ (Set.range (DyadicCube.indicator (d := d))) := hg
  clear hg
  induction hg' using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨R, rfl⟩ := hg
    change P.toSet.indicator (R.toSet.indicator 1) ∈ TestFun d
    rw [Set.indicator_indicator]
    rcases le_total P.m R.m with h | h
    · rcases DyadicCube.subset_or_disjoint P R h with hsub | hdis
      · rw [Set.inter_eq_left.mpr hsub]
        exact indicator_mem_testFun P
      · rw [Set.disjoint_iff_inter_eq_empty.mp hdis, Set.indicator_empty]
        exact Submodule.zero_mem _
    · rcases DyadicCube.subset_or_disjoint R P h with hsub | hdis
      · rw [Set.inter_eq_right.mpr hsub]
        exact indicator_mem_testFun R
      · rw [Set.disjoint_iff_inter_eq_empty.mp hdis.symm, Set.indicator_empty]
        exact Submodule.zero_mem _
  | zero =>
    have e : truncate P (0 : (Fin d → ℝ) → ℝ) = 0 := by
      funext x
      simp [truncate]
    rw [e]
    exact Submodule.zero_mem _
  | add g₁ g₂ _ _ h₁ h₂ =>
    have e : truncate P (g₁ + g₂) = truncate P g₁ + truncate P g₂ := by
      funext x
      by_cases hx : x ∈ P.toSet <;> simp [truncate, hx]
    rw [e]
    exact Submodule.add_mem _ h₁ h₂
  | smul c g _ h =>
    have e : truncate P (c • g) = c • truncate P g := by
      funext x
      by_cases hx : x ∈ P.toSet <;> simp [truncate, hx]
    rw [e]
    exact Submodule.smul_mem _ c h

/-- Truncation `g ↦ g 𝟙_P` as a linear map on dyadic test functions. -/
noncomputable def TestFun.truncateₗ (P : DyadicCube d) : TestFun d →ₗ[ℝ] TestFun d where
  toFun g := ⟨truncate P g, TestFun.truncate_mem P g.2⟩
  map_add' g₁ g₂ := Subtype.ext (by
    funext x
    by_cases hx : x ∈ P.toSet <;> simp [truncate, hx])
  map_smul' c g := Subtype.ext (by
    funext x
    by_cases hx : x ∈ P.toSet <;> simp [truncate, hx])

@[simp] theorem TestFun.coe_truncateₗ (P : DyadicCube d) (g : TestFun d) :
    ((TestFun.truncateₗ P g : TestFun d) : (Fin d → ℝ) → ℝ) = truncate P g := rfl

/-- Truncation to `P` leaves a function supported on `P` unchanged. [PROVED] -/
theorem TestFun.truncateₗ_of_supportedOn {P : DyadicCube d} {g : TestFun d}
    (h : SupportedOn g P) : TestFun.truncateₗ P g = g := by
  apply Subtype.ext
  rw [TestFun.coe_truncateₗ]
  funext x
  by_cases hx : x ∈ P.toSet
  · simp [truncate, hx]
  · simp [truncate, hx, h x hx]

/-- `‖c g‖_p = |c| ‖g‖_p`. [PROVED] -/
theorem lpNorm_const_smul (c : ℝ) (g : (Fin d → ℝ) → ℝ) (p : ℝ) :
    lpNorm (c • g) p = |c| * lpNorm g p := by
  unfold lpNorm
  rw [eLpNorm_const_smul, ENNReal.toReal_mul, toReal_enorm, Real.norm_eq_abs]

variable {n : ℕ}

/-- `Λ_P(ρ, u)` as a linear map in `ρ` (p. 40–41): all entries `g_j` are truncated to `P`, and
the slot `a` carries `ρ 𝟙_P`. -/
noncomputable def slotForm (T : PerfectCZForm d n) (a : Fin n) (g : Fin n → TestFun d)
    (P : DyadicCube d) : TestFun d →ₗ[ℝ] ℝ :=
  (T.form.toLinearMap (fun j => TestFun.truncateₗ P (g j)) a).comp (TestFun.truncateₗ P)

theorem slotForm_apply (T : PerfectCZForm d n) (a : Fin n) (g : Fin n → TestFun d)
    (P : DyadicCube d) (ρ : TestFun d) :
    slotForm T a g P ρ =
      T.form (Function.update (fun j => TestFun.truncateₗ P (g j)) a (TestFun.truncateₗ P ρ)) :=
  rfl

/-- **Perfect smoothness moves truncations** (p. 42, "with multilinearity and the smoothness
condition (1.2)"): for `P ⊆ Q` and a mean-zero `ρ` supported on `P`, `Λ_P(ρ, u) = Λ_Q(ρ, u)`,
since replacing an entry `g_j 𝟙_P` by `g_j 𝟙_Q` changes the form by `Λ(…, g_j 𝟙_{Q∖P}, …) = 0`.
[PROVED] -/
theorem slotForm_eq_of_subset (T : PerfectCZForm d n) (a : Fin n) (g : Fin n → TestFun d)
    {P Q : DyadicCube d} (hPQ : P.toSet ⊆ Q.toSet) {ρ : TestFun d} (hρ : SupportedOn ρ P)
    (hρ0 : MeanZero (ρ : (Fin d → ℝ) → ℝ)) : slotForm T a g P ρ = slotForm T a g Q ρ := by
  classical
  have hρQ : SupportedOn ρ Q := fun x hx => hρ x fun h => hx (hPQ h)
  -- hybrid entries: `Q`-truncation on `s`, `P`-truncation elsewhere, `ρ` in the slot `a`
  set hyb : Finset (Fin n) → Fin n → TestFun d := fun s j =>
    if j = a then ρ else
      if j ∈ s then TestFun.truncateₗ Q (g j) else TestFun.truncateₗ P (g j) with hhyb
  have key : ∀ s : Finset (Fin n), T.form (hyb s) = T.form (hyb ∅) := by
    intro s
    induction s using Finset.induction_on with
    | empty => rfl
    | insert j s hj ih =>
      rw [← ih]
      by_cases hja : j = a
      · subst hja
        congr 1
        funext i
        by_cases hia : i = j
        · simp [hhyb, hia]
        · simp [hhyb, hia]
      · have e1 : hyb (insert j s) = Function.update (hyb s) j (TestFun.truncateₗ Q (g j)) := by
          funext i
          by_cases hij : i = j
          · subst hij
            simp [hhyb, hja]
          · simp [hhyb, hij]
        have e2 : Function.update (hyb s) j (TestFun.truncateₗ P (g j)) = hyb s := by
          rw [Function.update_eq_self_iff]
          simp [hhyb, hja, hj]
        have hsub : T.form (Function.update (hyb s) j (TestFun.truncateₗ Q (g j))) -
            T.form (Function.update (hyb s) j (TestFun.truncateₗ P (g j))) = 0 := by
          rw [← MultilinearMap.map_update_sub]
          apply T.smooth P _ a j (Ne.symm hja)
          · rw [Function.update_of_ne (Ne.symm hja)]
            simpa [hhyb] using hρ
          · rw [Function.update_of_ne (Ne.symm hja)]
            simpa [hhyb] using hρ0
          · rw [Function.update_self]
            intro x hx
            simp [truncate, Set.indicator_of_mem hx, Set.indicator_of_mem (hPQ hx)]
        calc T.form (hyb (insert j s))
            = T.form (Function.update (hyb s) j (TestFun.truncateₗ Q (g j))) := by rw [e1]
          _ = T.form (Function.update (hyb s) j (TestFun.truncateₗ P (g j))) :=
              sub_eq_zero.mp hsub
          _ = T.form (hyb s) := by rw [e2]
  have hP : Function.update (fun j => TestFun.truncateₗ P (g j)) a (TestFun.truncateₗ P ρ) =
      hyb ∅ := by
    funext i
    by_cases hia : i = a
    · subst hia
      simp [hhyb, TestFun.truncateₗ_of_supportedOn hρ]
    · simp [hhyb, hia]
  have hQ : Function.update (fun j => TestFun.truncateₗ Q (g j)) a (TestFun.truncateₗ Q ρ) =
      hyb Finset.univ := by
    funext i
    by_cases hia : i = a
    · subst hia
      simp [hhyb, TestFun.truncateₗ_of_supportedOn hρQ]
    · simp [hhyb, hia]
  rw [slotForm_apply, slotForm_apply, hP, hQ, key Finset.univ]

/-- **Normalisation of `ρ`** (p. 42): a mean-zero `ρ` supported on `P` with `c ‖ρ‖_r ≤ |L ρ|`
can be rescaled to `ρ'` with `‖ρ'‖_r = |P|^{1/r}` and `c |P|^{1/r} ≤ L ρ'`. [PROVED] -/
theorem exists_normalized_rho {r : ℝ} (L : TestFun d →ₗ[ℝ] ℝ) {P : DyadicCube d}
    {ρ : TestFun d} (hsupp : SupportedOn ρ P) (h0 : MeanZero (ρ : (Fin d → ℝ) → ℝ))
    (hpos : 0 < lpNorm (ρ : (Fin d → ℝ) → ℝ) r)
    {c : ℝ} (hL : c * lpNorm (ρ : (Fin d → ℝ) → ℝ) r ≤ |L ρ|) :
    ∃ ρ' : TestFun d, SupportedOn ρ' P ∧ MeanZero (ρ' : (Fin d → ℝ) → ℝ) ∧
      lpNorm (ρ' : (Fin d → ℝ) → ℝ) r = P.vol ^ (1 / r) ∧ c * P.vol ^ (1 / r) ≤ L ρ' := by
  set t : ℝ := P.vol ^ (1 / r) / lpNorm (ρ : (Fin d → ℝ) → ℝ) r with ht
  have ht0 : 0 < t := div_pos (Real.rpow_pos_of_pos P.vol_pos _) hpos
  set sg : ℝ := if 0 ≤ L ρ then 1 else -1 with hsg
  have hsgabs : |sg| = 1 := by
    rw [hsg]
    split_ifs <;> simp
  have hsgL : sg * L ρ = |L ρ| := by
    rw [hsg]
    split_ifs with h
    · rw [one_mul, abs_of_nonneg h]
    · rw [neg_one_mul, abs_of_neg (not_le.mp h)]
  have h0' : ∫ x, (ρ : (Fin d → ℝ) → ℝ) x = 0 := h0
  refine ⟨(sg * t) • ρ, ?_, ?_, ?_, ?_⟩
  · intro x hx
    simp [hsupp x hx]
  · change ∫ x, (((sg * t) • ρ : TestFun d) : (Fin d → ℝ) → ℝ) x = 0
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
    rw [integral_const_mul, h0', mul_zero]
  · rw [Submodule.coe_smul, lpNorm_const_smul, abs_mul, hsgabs, one_mul, abs_of_pos ht0, ht,
      div_mul_cancel₀ _ hpos.ne']
  · rw [map_smul, smul_eq_mul]
    calc c * P.vol ^ (1 / r) = t * (c * lpNorm (ρ : (Fin d → ℝ) → ℝ) r) := by
          rw [ht, mul_left_comm, div_mul_cancel₀ _ hpos.ne']
      _ ≤ t * |L ρ| := mul_le_mul_of_nonneg_left hL ht0.le
      _ = sg * t * L ρ := by rw [← hsgL]; ring

/-- `‖∑ g_i‖_r^r = ∑ ‖g_i‖_r^r` for test functions with pairwise disjoint supports. [PROVED] -/
theorem lpNorm_sum_rpow_eq {ι : Type*} {r : ℝ} (hr : 0 < r) (s : Finset ι) (g : ι → TestFun d)
    (P : ι → DyadicCube d) (hsupp : ∀ i, SupportedOn (g i) (P i))
    (hdisj : (s : Set ι).PairwiseDisjoint fun i => (P i).toSet) :
    lpNorm ((∑ i ∈ s, g i : TestFun d) : (Fin d → ℝ) → ℝ) r ^ r =
      ∑ i ∈ s, lpNorm (g i : (Fin d → ℝ) → ℝ) r ^ r := by
  have hmem : ∀ h : TestFun d, MemLp (h : (Fin d → ℝ) → ℝ) (ENNReal.ofReal r) volume :=
    fun h => TestFun.memLp h.2 _
  have hint : ∀ i, Integrable (fun x => |(g i : (Fin d → ℝ) → ℝ) x| ^ r) volume := fun i => by
    have := (hmem (g i)).integrable_norm_rpow (ENNReal.ofReal_pos.mpr hr).ne' ENNReal.ofReal_ne_top
    simpa [Real.norm_eq_abs, ENNReal.toReal_ofReal hr.le] using this
  have hpt : ∀ x, |((∑ i ∈ s, g i : TestFun d) : (Fin d → ℝ) → ℝ) x| ^ r =
      ∑ i ∈ s, |(g i : (Fin d → ℝ) → ℝ) x| ^ r := by
    intro x
    rw [Submodule.coe_sum, Finset.sum_apply]
    by_cases hx : ∃ i ∈ s, x ∈ (P i).toSet
    · obtain ⟨i₀, hi₀, hxi₀⟩ := hx
      have hz : ∀ i ∈ s, i ≠ i₀ → (g i : (Fin d → ℝ) → ℝ) x = 0 := fun i hi hne =>
        hsupp i x fun hxi => Set.disjoint_left.mp (hdisj hi hi₀ hne) hxi hxi₀
      rw [Finset.sum_eq_single i₀ hz fun h => absurd hi₀ h,
        Finset.sum_eq_single i₀ (fun i hi hne => by rw [hz i hi hne, abs_zero, Real.zero_rpow
          hr.ne'])
          fun h => absurd hi₀ h]
    · have hz : ∀ i ∈ s, (g i : (Fin d → ℝ) → ℝ) x = 0 := fun i hi =>
        hsupp i x fun hxi => hx ⟨i, hi, hxi⟩
      rw [Finset.sum_eq_zero hz, abs_zero, Real.zero_rpow hr.ne',
        Finset.sum_eq_zero fun i hi => by rw [hz i hi, abs_zero, Real.zero_rpow hr.ne']]
  rw [lpNorm_rpow_eq_integral hr (hmem _),
    Finset.sum_congr rfl fun i _ => lpNorm_rpow_eq_integral hr (hmem (g i))]
  simp_rw [hpt]
  exact integral_finsetSum s fun i _ => hint i

/-- **The bound for `𝐏₃`** (p. 42): let `Λ_P(·, u) = slotForm T a g P` and suppose the testing
condition `|Λ_Q(ρ, u)| ≤ K ‖ρ‖_r` for all `ρ` supported on `Q` (here `K = B F ‖u‖_q`). If the
cubes of a pairwise disjoint collection `𝐏 ⊆ 𝒟(Q)` each carry a nonzero mean-zero `ρ` supported
on the cube with `K ε^{-1} (|P|/|Q|)^{1-1/r} ‖ρ‖_r ≤ |Λ_P(ρ, u)|`, then `|⋃ 𝐏| ≤ ε|Q|`. [PROVED] -/
theorem volume_biUnion_le_of_P3 {Q : DyadicCube d} {Ps : Set (DyadicCube d)} (hPs : Ps ⊆ Q.tree)
    (hdisj : Ps.PairwiseDisjoint DyadicCube.toSet) (T : PerfectCZForm d n) (a : Fin n)
    (g : Fin n → TestFun d) {r ε K : ℝ} (hr : 1 < r) (hε : 0 < ε) (hK : 0 < K)
    (htest : ∀ ρ : TestFun d, SupportedOn ρ Q → MeanZero (ρ : (Fin d → ℝ) → ℝ) →
      |slotForm T a g Q ρ| ≤ K * lpNorm (ρ : (Fin d → ℝ) → ℝ) r)
    (hP3 : ∀ P ∈ Ps, ∃ ρ : TestFun d, SupportedOn ρ P ∧ MeanZero (ρ : (Fin d → ℝ) → ℝ) ∧
      0 < lpNorm (ρ : (Fin d → ℝ) → ℝ) r ∧
      K * ε⁻¹ * (P.vol / Q.vol) ^ (1 - 1 / r) * lpNorm (ρ : (Fin d → ℝ) → ℝ) r ≤
        |slotForm T a g P ρ|) :
    volume (⋃ P ∈ Ps, P.toSet) ≤ ENNReal.ofReal (ε * Q.vol) := by
  have hr0 : 0 < r := by linarith
  have hV := Q.vol_pos
  have hA : 0 < Q.vol ^ (1 - 1 / r) := Real.rpow_pos_of_pos hV _
  have hB : 0 < Q.vol ^ (1 / r) := Real.rpow_pos_of_pos hV _
  -- the normalised test functions `ρ_P`
  have hchoice : ∀ P : Ps, ∃ ρ' : TestFun d,
      SupportedOn (ρ' : (Fin d → ℝ) → ℝ) (P : DyadicCube d) ∧
      MeanZero (ρ' : (Fin d → ℝ) → ℝ) ∧
      lpNorm (ρ' : (Fin d → ℝ) → ℝ) r = (P : DyadicCube d).vol ^ (1 / r) ∧
      K * ε⁻¹ * ((P : DyadicCube d).vol / Q.vol) ^ (1 - 1 / r) * (P : DyadicCube d).vol ^ (1 / r) ≤
        slotForm T a g P ρ' := by
    intro P
    obtain ⟨ρ, hs, h0, hpos, hL⟩ := hP3 P P.2
    exact exists_normalized_rho (slotForm T a g P) hs h0 hpos hL
  choose ρ' hρ' using hchoice
  -- reduction to finite subfamilies
  rw [volume_biUnion_eq_tsum hdisj, ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun s => ?_
  rw [← ENNReal.ofReal_sum_of_nonneg (f := fun P : Ps => (P : DyadicCube d).vol)
    fun P _ => (P : DyadicCube d).vol_pos.le]
  apply ENNReal.ofReal_le_ofReal
  set S : ℝ := ∑ P ∈ s, (P : DyadicCube d).vol with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun P _ => (P : DyadicCube d).vol_pos.le
  have hdisj' : (s : Set Ps).PairwiseDisjoint fun P : Ps => (P : DyadicCube d).toSet :=
    fun P _ R _ hne => hdisj P.2 R.2 fun h => hne (Subtype.ext h)
  -- `S ≤ |Q|`
  have hSQ : S ≤ Q.vol := by
    have h1 : volume (⋃ P ∈ s, (P : DyadicCube d).toSet) =
        ∑ P ∈ s, volume (P : DyadicCube d).toSet :=
      measure_biUnion_finset hdisj' fun P _ => DyadicCube.measurableSet_toSet _
    have h2 : volume (⋃ P ∈ s, (P : DyadicCube d).toSet) ≤ volume Q.toSet :=
      measure_mono (Set.iUnion₂_subset fun P _ => hPs P.2)
    rw [h1, Q.volume_toSet] at h2
    simp only [DyadicCube.volume_toSet] at h2
    rwa [← ENNReal.ofReal_sum_of_nonneg (f := fun P : Ps => (P : DyadicCube d).vol)
      fun P _ => (P : DyadicCube d).vol_pos.le, ENNReal.ofReal_le_ofReal_iff hV.le] at h2
  -- the test function `G = ∑ ρ_P`
  set G : TestFun d := ∑ P ∈ s, ρ' P with hG
  have hGsupp : SupportedOn G Q := by
    intro x hx
    rw [hG, Submodule.coe_sum, Finset.sum_apply]
    exact Finset.sum_eq_zero fun P _ => (hρ' P).1 x fun h => hx (hPs P.2 h)
  have hG0 : MeanZero (G : (Fin d → ℝ) → ℝ) := by
    change ∫ x, (G : (Fin d → ℝ) → ℝ) x = 0
    rw [hG, Submodule.coe_sum]
    simp only [Finset.sum_apply]
    rw [integral_finsetSum _ fun P _ => memLp_one_iff_integrable.mp (TestFun.memLp (ρ' P).2 1)]
    exact Finset.sum_eq_zero fun P _ => (hρ' P).2.1
  -- lower bound `K ε⁻¹ |Q|^{-(1-1/r)} S ≤ Λ_Q(G, u)`
  have hlow : K * ε⁻¹ * (Q.vol ^ (1 - 1 / r))⁻¹ * S ≤ slotForm T a g Q G := by
    have hterm : ∀ P : Ps, K * ε⁻¹ * (Q.vol ^ (1 - 1 / r))⁻¹ * (P : DyadicCube d).vol ≤
        slotForm T a g Q (ρ' P) := by
      intro P
      have h := (hρ' P).2.2.2
      rw [slotForm_eq_of_subset T a g (hPs P.2) (hρ' P).1 (hρ' P).2.1] at h
      refine le_trans (le_of_eq ?_) h
      have hPQ : ((P : DyadicCube d).vol / Q.vol) ^ (1 - 1 / r) =
          (P : DyadicCube d).vol ^ (1 - 1 / r) * (Q.vol ^ (1 - 1 / r))⁻¹ := by
        rw [Real.div_rpow (P : DyadicCube d).vol_pos.le hV.le, div_eq_mul_inv]
      have hPP : (P : DyadicCube d).vol ^ (1 - 1 / r) * (P : DyadicCube d).vol ^ (1 / r) =
          (P : DyadicCube d).vol := by
        rw [← Real.rpow_add (P : DyadicCube d).vol_pos, sub_add_cancel, Real.rpow_one]
      calc K * ε⁻¹ * (Q.vol ^ (1 - 1 / r))⁻¹ * (P : DyadicCube d).vol
          = K * ε⁻¹ * (Q.vol ^ (1 - 1 / r))⁻¹ *
              ((P : DyadicCube d).vol ^ (1 - 1 / r) * (P : DyadicCube d).vol ^ (1 / r)) := by
            rw [hPP]
        _ = K * ε⁻¹ * ((P : DyadicCube d).vol / Q.vol) ^ (1 - 1 / r) *
              (P : DyadicCube d).vol ^ (1 / r) := by
            rw [hPQ]
            ring
    calc K * ε⁻¹ * (Q.vol ^ (1 - 1 / r))⁻¹ * S
        = ∑ P ∈ s, K * ε⁻¹ * (Q.vol ^ (1 - 1 / r))⁻¹ * (P : DyadicCube d).vol := by
          rw [hS, Finset.mul_sum]
      _ ≤ ∑ P ∈ s, slotForm T a g Q (ρ' P) := Finset.sum_le_sum fun P _ => hterm P
      _ = slotForm T a g Q G := by rw [hG, map_sum]
  -- `‖G‖_r = S^{1/r}`
  have hGnorm : lpNorm (G : (Fin d → ℝ) → ℝ) r = S ^ (1 / r) := by
    have h := lpNorm_sum_rpow_eq hr0 s ρ' (fun P : Ps => (P : DyadicCube d))
      (fun P => (hρ' P).1) hdisj'
    rw [← hG, Finset.sum_congr rfl fun P _ => (show lpNorm (ρ' P : (Fin d → ℝ) → ℝ) r ^ r =
      (P : DyadicCube d).vol by
        rw [(hρ' P).2.2.1, ← Real.rpow_mul (P : DyadicCube d).vol_pos.le,
          one_div_mul_cancel hr0.ne', Real.rpow_one])] at h
    have hnn : 0 ≤ lpNorm (G : (Fin d → ℝ) → ℝ) r := ENNReal.toReal_nonneg
    calc lpNorm (G : (Fin d → ℝ) → ℝ) r = (lpNorm (G : (Fin d → ℝ) → ℝ) r ^ r) ^ r⁻¹ :=
          (Real.rpow_rpow_inv hnn hr0.ne').symm
      _ = S ^ (1 / r) := by rw [h, one_div, hS]
  -- upper bound `Λ_Q(G, u) ≤ K ‖G‖_r ≤ K |Q|^{1/r}`
  have hup : slotForm T a g Q G ≤ K * Q.vol ^ (1 / r) := by
    calc slotForm T a g Q G ≤ |slotForm T a g Q G| := le_abs_self _
      _ ≤ K * lpNorm (G : (Fin d → ℝ) → ℝ) r := htest G hGsupp hG0
      _ = K * S ^ (1 / r) := by rw [hGnorm]
      _ ≤ K * Q.vol ^ (1 / r) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hS0 hSQ (by positivity)) hK.le
  -- conclusion
  have hAB : Q.vol ^ (1 - 1 / r) * Q.vol ^ (1 / r) = Q.vol := by
    rw [← Real.rpow_add hV, sub_add_cancel, Real.rpow_one]
  have h1 : ε⁻¹ * (Q.vol ^ (1 - 1 / r))⁻¹ * S ≤ Q.vol ^ (1 / r) := by
    have := hlow.trans hup
    have e : K * ε⁻¹ * (Q.vol ^ (1 - 1 / r))⁻¹ * S = K * (ε⁻¹ * (Q.vol ^ (1 - 1 / r))⁻¹ * S) := by
      ring
    rw [e] at this
    exact le_of_mul_le_mul_left this hK
  calc S = ε * Q.vol ^ (1 - 1 / r) * (ε⁻¹ * (Q.vol ^ (1 - 1 / r))⁻¹ * S) := by
        rw [show ε * Q.vol ^ (1 - 1 / r) * (ε⁻¹ * (Q.vol ^ (1 - 1 / r))⁻¹ * S) =
          (ε * ε⁻¹) * (Q.vol ^ (1 - 1 / r) * (Q.vol ^ (1 - 1 / r))⁻¹) * S by ring,
          mul_inv_cancel₀ hε.ne', mul_inv_cancel₀ hA.ne', one_mul, one_mul]
    _ ≤ ε * Q.vol ^ (1 - 1 / r) * Q.vol ^ (1 / r) :=
        mul_le_mul_of_nonneg_left h1 (mul_nonneg hε.le hA.le)
    _ = ε * Q.vol := by rw [mul_assoc, hAB]

end P3Bound

/-- The dyadic square function `S g(x) = (∑_{P ∋ x} |[g]_{P_x} − [g]_P|²)^{1/2}`, the sum running
over the dyadic cubes `P` containing `x`, with `P_x` the child of `P` containing `x`. For a dyadic
test function `g` the series converges at every point: the terms of the cubes on which `g` is
constant vanish, and the others decay geometrically with the side length. -/
noncomputable def dyadicSquareFun (g : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) : ℝ :=
  Real.sqrt (∑' P : DyadicCube d,
    P.toSet.indicator (fun y => (avg (P.childAt y) g - avg P g) ^ 2) x)

/-- The dyadic Hardy-space norm `‖g‖_{H¹} = ∫ S g` (pre-dual of dyadic BMO). It is the norm of `g`
when `S g` is integrable, that is, when `‖g‖_{H¹} < ∞`; otherwise the integral takes Lean's default
value `0`, so the BMO condition (1.15) below assumes that `S g` is integrable. -/
noncomputable def hardyNorm (g : (Fin d → ℝ) → ℝ) : ℝ :=
  ∫ x, dyadicSquareFun g x

/-- A *locally dyadic test function*: a function `b` on `ℝ^d` whose truncation `b 𝟙_Q` to every
dyadic cube `Q` is a dyadic test function. Constant functions, in particular `b = 1`, are of this
kind, so a locally dyadic test function need not have bounded support. -/
def LocTestFun (d : ℕ) : Set ((Fin d → ℝ) → ℝ) :=
  {b | ∀ Q : DyadicCube d, truncate Q b ∈ TestFun d}

/-- Hypotheses (1.12)–(1.15) of Theorem 1.11, for locally dyadic test functions `b_1, …, b_n` (for
example `b_j = 1`). The weak boundedness condition (1.14) is taken in its standard scale-invariant
form `|Λ(b₁𝟙_Q, …, b_n𝟙_Q)| ≤ B |Q|` (the paper writes `≤ B`, which is not dimensionally consistent
with (1.16): a bounded form satisfies `|Λ(b₁𝟙_Q, …, b_n𝟙_Q)| ≤ C B^n |Q|`, and the factor `|Q|` is
needed in the global/local reduction). In the BMO condition (1.15) the entries `b_j` need not be
dyadic test functions, so `Λ(b_1, …, g, …, b_n)` is evaluated through a kernel `K` of `Λ` as in the
qualitative truncation (iii), `∫ K(x) ∏_j f_j(x_j) dx`; the bound is required for every such kernel
(two kernels of `Λ` agree almost everywhere) and for every dyadic test function `g` with
`‖g‖_{H¹} < ∞`, i.e. with integrable square function (for the other `g` the paper's bound is
`+∞` and says nothing). -/
structure GlobalTbHypotheses {n : ℕ} (T : PerfectCZForm d n) (b : Fin n → (Fin d → ℝ) → ℝ)
    (B : ℝ) : Prop where
  /-- the functions `b_j` are locally dyadic test functions -/
  loc : ∀ j, b j ∈ LocTestFun d
  /-- pseudo-accretivity (1.12) -/
  accretive : ∀ (Q : DyadicCube d) (j : Fin n), 1 ≤ |avg Q (b j)|
  /-- norm bound (1.13): `‖b_j‖_∞ ≤ B` -/
  bound : ∀ j, eLpNorm (b j) ⊤ volume ≤ ENNReal.ofReal B
  /-- weak boundedness (1.14) -/
  weak : ∀ (Q : DyadicCube d) (f : Fin n → TestFun d),
    (∀ j, (f j : (Fin d → ℝ) → ℝ) = truncate Q (b j)) → |T.form f| ≤ B * Q.vol
  /-- BMO condition (1.15) for every `g` with `‖g‖_{H¹} < ∞`, with `Λ(b_1, …, g, …, b_n)`
  evaluated through a kernel of `Λ` -/
  bmo : ∀ K ∈ TestFunProd d n,
    (∀ f : Fin n → TestFun d, T.form f = ∫ x, K x * ∏ j, (f j : (Fin d → ℝ) → ℝ) (x j)) →
    ∀ (j₀ : Fin n) (g : TestFun d), Integrable (dyadicSquareFun (g : (Fin d → ℝ) → ℝ)) →
      |∫ x, K x * ∏ j, (Function.update b j₀ (g : (Fin d → ℝ) → ℝ)) j (x j)| ≤
        B * hardyNorm (g : (Fin d → ℝ) → ℝ)

/-- **A variant of Theorem 1.11** (perfect multilinear global `T(b)` theorem):
for `d ≥ 1`, `n ≥ 2` and
`B ≥ 1` there is a constant `C`, depending only on `d`, `n`, `B` and the Hölder tuple, such that
for every perfect Calderón–Zygmund form and all locally dyadic test functions `b_1, …, b_n`
satisfying (1.12)–(1.15) with constant `B`, `|Λ(f)| ≤ C ∏ ‖f_j‖_{p_j}` for all tuples of dyadic
test functions. -/
def GlobalTb (d n : ℕ) (p : HolderTuple n) : Prop :=
  1 ≤ d → 2 ≤ n → ∀ B : ℝ, 1 ≤ B → ∃ C : ℝ,
    ∀ (T : PerfectCZForm d n) (b : Fin n → (Fin d → ℝ) → ℝ), GlobalTbHypotheses T b B →
    ∀ f : Fin n → TestFun d, |T.form f| ≤ C * prodNorm p f

/-! ## §2 Ingredients of the proof of Theorem 1.4

The elementary identities and inequalities below support the analytic core of §2.
The remaining modules prove the stopping, pruning, and telescoping estimates of §2.5–2.8. -/

/-- The induction constant `A ≤ A(1-ε)^{1/p_k} + C` (p. 43) is solved for `A`:
if `θ < 1` and `A ≤ A θ + C` then `A ≤ C / (1 - θ)`. [PROVED] -/
theorem solve_best_constant {A θ C : ℝ} (hθ1 : θ < 1) (h : A ≤ A * θ + C) :
    A ≤ C / (1 - θ) := by
  rw [le_div_iff₀ (by linarith)]
  linarith

/-- The Chebyshev-type estimate for the stopping collections `𝐏₁`, `𝐏₂` (p. 41): if each
cube satisfies `|P| ≤ c ∑_j w_j(P)` and `∑_P w_j(P) ≤ 1` for every `j`, then
`∑_P |P| ≤ c n`. [PROVED] -/
theorem stopping_chebyshev {ι : Type*} (S : Finset ι) {n : ℕ} (a : ι → ℝ) (w : Fin n → ι → ℝ)
    {c : ℝ} (hc : 0 ≤ c) (ha : ∀ P ∈ S, a P ≤ c * ∑ j, w j P) (hw : ∀ j, ∑ P ∈ S, w j P ≤ 1) :
    ∑ P ∈ S, a P ≤ c * n := by
  calc ∑ P ∈ S, a P ≤ ∑ P ∈ S, c * ∑ j, w j P := Finset.sum_le_sum ha
    _ = c * ∑ j, ∑ P ∈ S, w j P := by rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ c * ∑ _j : Fin n, (1 : ℝ) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => hw j) hc
    _ = c * n := by simp

/-- The measure count (2.7): if the five stopping collections satisfy the bounds
`∑_{𝐏₁}, ∑_{𝐏₂}, ∑_{𝐏₃}, ∑_{𝐏₅} ≤ ε|Q|` and `∑_{𝐏₄} ≤ (1-8ε)|Q|`, then the maximal cubes
have total measure at most `(1-ε)|Q|`. [PROVED] -/
theorem stopping_measure_bound {s₁ s₂ s₃ s₄ s₅ ε V total : ℝ} (hε : 0 ≤ ε) (hV : 0 ≤ V)
    (h₁ : s₁ ≤ ε * V) (h₂ : s₂ ≤ ε * V) (h₃ : s₃ ≤ ε * V) (h₄ : s₄ ≤ (1 - 8 * ε) * V)
    (h₅ : s₅ ≤ ε * V) (htot : total ≤ s₁ + s₂ + s₃ + s₄ + s₅) :
    total ≤ (1 - ε) * V := by
  nlinarith [mul_nonneg hε hV]

/-- The parameter `ε = (1/8) min_j (7/8)^{p_j/(p_j-1)} B^{-1/(p_j-1)}` of p. 41. -/
noncomputable def eps {n : ℕ} (p : HolderTuple (n + 1)) (B : ℝ) : ℝ :=
  (1 / 8) * Finset.univ.inf' Finset.univ_nonempty
    (fun j => (7 / 8 : ℝ) ^ (p.p j / (p.p j - 1)) * B ^ (-(1 / (p.p j - 1))))

/-- Each factor in the definition of `ε` lies in `(0, 1]`. [PROVED] -/
theorem eps_factor_bounds {n : ℕ} (p : HolderTuple n) {B : ℝ} (hB : 1 ≤ B)
    (j : Fin n) :
    0 < (7 / 8 : ℝ) ^ (p.p j / (p.p j - 1)) * B ^ (-(1 / (p.p j - 1))) ∧
      (7 / 8 : ℝ) ^ (p.p j / (p.p j - 1)) * B ^ (-(1 / (p.p j - 1))) ≤ 1 := by
  have h1 : 1 < p.p j := p.one_lt j
  have hs : 0 < p.p j - 1 := by linarith
  refine ⟨mul_pos (Real.rpow_pos_of_pos (by norm_num) _)
    (Real.rpow_pos_of_pos (by linarith) _), ?_⟩
  have e1 : (7 / 8 : ℝ) ^ (p.p j / (p.p j - 1)) ≤ 1 :=
    Real.rpow_le_one (by norm_num) (by norm_num) (div_nonneg (by linarith) hs.le)
  have e2 : B ^ (-(1 / (p.p j - 1))) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hB (by
      have : 0 < 1 / (p.p j - 1) := div_pos one_pos hs
      linarith)
  calc (7 / 8 : ℝ) ^ (p.p j / (p.p j - 1)) * B ^ (-(1 / (p.p j - 1))) ≤ 1 * 1 :=
        mul_le_mul e1 e2 (Real.rpow_nonneg (by linarith) _) one_pos.le
    _ = 1 := by ring

/-- `ε > 0`. [PROVED] -/
theorem eps_pos {n : ℕ} (p : HolderTuple (n + 1)) {B : ℝ} (hB : 1 ≤ B) : 0 < eps p B := by
  unfold eps
  apply mul_pos (by norm_num)
  rw [Finset.lt_inf'_iff]
  intro j _
  exact (eps_factor_bounds p hB j).1

/-- `ε ≤ 1/8`. [PROVED] -/
theorem eps_le {n : ℕ} (p : HolderTuple (n + 1)) {B : ℝ} (hB : 1 ≤ B) : eps p B ≤ 1 / 8 := by
  unfold eps
  have h := Finset.inf'_le
    (fun j : Fin (n + 1) => (7 / 8 : ℝ) ^ (p.p j / (p.p j - 1)) * B ^ (-(1 / (p.p j - 1))))
    (Finset.mem_univ (0 : Fin (n + 1)))
  have h2 := (eps_factor_bounds p hB 0).2
  linarith

/-- The algebraic expansion (2.15)–(2.17) of `g − 𝔤`, where `𝔤` is defined by (2.12).
Here `Ps` is the first stopping collection, `Ps₄` the subcollection `𝐏₄`, `Pb` the parents
`parents(𝐏)₄` and `Pp` the siblings `𝐏₄'`; `gP P = g_P`, `uP P = u_P`, `r P = [g]_P/[u]_P`,
`s P = [g]_P b_{σ,𝐐_P,k+1}` and `c = [g]_Q`. The same identity gives (2.41)–(2.43) for
`h_R − 𝔥` with `𝔥` as in (2.38). [PROVED] -/
theorem pruning_expansion {ι M : Type*} [DecidableEq ι] [AddCommGroup M] [Module ℝ M]
    (Pst P4 Pb Pp : Finset ι) (g u gg : M) (c : ℝ) (gP s uP : ι → M) (r : ι → ℝ)
    (hgg : gg = g - c • u - ∑ P ∈ Pst.filter (· ∉ P4), gP P
      + ∑ P ∈ Pst.filter (· ∉ P4), r P • uP P
      - ∑ P ∈ Pst.filter (· ∈ P4), gP P + ∑ P ∈ Pb, r P • uP P - ∑ P ∈ Pp, r P • uP P) :
    g - gg = c • u + ∑ P ∈ Pst, (gP P - s P) + ∑ P ∈ Pst.filter (· ∉ P4), (s P - r P • uP P)
      + ∑ P ∈ Pst.filter (· ∈ P4), s P - ∑ P ∈ Pb, r P • uP P + ∑ P ∈ Pp, r P • uP P := by
  subst hgg
  simp only [Finset.sum_sub_distrib]
  rw [← Finset.sum_filter_add_sum_filter_not Pst (· ∈ P4) s,
    ← Finset.sum_filter_add_sum_filter_not Pst (· ∈ P4) gP]
  abel

/-! ### §2.2 (continued) The stopping collections for the data of §2.2

We now fix the data of §2.1–2.2 (the form, the exponents, the cube `Q`, the slots of `h` and
`u`, the frozen entries `f_j 𝟙_Q`, the testing function `u = b_{σ,𝐐,k+1}` with its support,
mean and norm conditions, and the testing condition (1.9)), define the five stopping
collections `𝐏₁`–`𝐏₅` of p. 41 literally, and derive the claim (2.7) from the five bounds. -/

section StoppingCollections

variable {n : ℕ}

/-- Dyadic test functions are integrable. [PROVED] -/
theorem TestFun.integrable {g : (Fin d → ℝ) → ℝ} (hg : g ∈ TestFun d) : Integrable g volume :=
  memLp_one_iff_integrable.mp (TestFun.memLp hg 1)

/-- The integral as a linear map on dyadic test functions. -/
noncomputable def TestFun.integralₗ : TestFun d →ₗ[ℝ] ℝ where
  toFun g := ∫ x, (g : (Fin d → ℝ) → ℝ) x
  map_add' g₁ g₂ := by
    simp only [Submodule.coe_add, Pi.add_apply]
    exact integral_add (TestFun.integrable g₁.2) (TestFun.integrable g₂.2)
  map_smul' c g := by
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    exact integral_const_mul c _

theorem TestFun.integralₗ_apply (g : TestFun d) :
    TestFun.integralₗ g = ∫ x, (g : (Fin d → ℝ) → ℝ) x := rfl

/-- `∫ g 𝟙_P = [g]_P |P|`. [PROVED] -/
theorem TestFun.integralₗ_truncateₗ (P : DyadicCube d) (h : TestFun d) :
    TestFun.integralₗ (TestFun.truncateₗ P h) = avg P h * P.vol := by
  change ∫ x, P.toSet.indicator (h : (Fin d → ℝ) → ℝ) x = _
  rw [integral_indicator P.measurableSet_toSet]
  exact (avg_mul_vol P _).symm

/-- `|f|^q` is integrable for a dyadic test function `f`. [PROVED] -/
theorem TestFun.integrable_abs_rpow (f : TestFun d) {q : ℝ} (hq : 0 < q) :
    Integrable (fun x => |(f : (Fin d → ℝ) → ℝ) x| ^ q) volume := by
  have := (TestFun.memLp f.2 (ENNReal.ofReal q)).integrable_norm_rpow
    (ENNReal.ofReal_pos.mpr hq).ne' ENNReal.ofReal_ne_top
  simpa [Real.norm_eq_abs, ENNReal.toReal_ofReal hq.le] using this

/-- The triangle inequality for `‖·‖_q` on dyadic test functions. [PROVED] -/
theorem TestFun.lpNorm_add_le (f g : TestFun d) {q : ℝ} (hq : 1 ≤ q) :
    lpNorm ((f + g : TestFun d) : (Fin d → ℝ) → ℝ) q ≤
      lpNorm (f : (Fin d → ℝ) → ℝ) q + lpNorm (g : (Fin d → ℝ) → ℝ) q := by
  unfold lpNorm
  have hf := (TestFun.memLp f.2 (ENNReal.ofReal q)).eLpNorm_ne_top
  have hg := (TestFun.memLp g.2 (ENNReal.ofReal q)).eLpNorm_ne_top
  rw [Submodule.coe_add, ← ENNReal.toReal_add hf hg]
  exact ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hf, hg⟩)
    (eLpNorm_add_le (ENNReal.one_le_ofReal.mpr hq))

theorem TestFun.lpNorm_neg (f : TestFun d) (q : ℝ) :
    lpNorm ((-f : TestFun d) : (Fin d → ℝ) → ℝ) q = lpNorm (f : (Fin d → ℝ) → ℝ) q := by
  unfold lpNorm
  rw [Submodule.coe_neg, eLpNorm_neg]

theorem TestFun.lpNorm_sub_le (f g : TestFun d) {q : ℝ} (hq : 1 ≤ q) :
    lpNorm ((f - g : TestFun d) : (Fin d → ℝ) → ℝ) q ≤
      lpNorm (f : (Fin d → ℝ) → ℝ) q + lpNorm (g : (Fin d → ℝ) → ℝ) q := by
  rw [sub_eq_add_neg]
  exact (TestFun.lpNorm_add_le f (-g) hq).trans_eq (by rw [TestFun.lpNorm_neg])

theorem TestFun.lpNorm_smul (c : ℝ) (f : TestFun d) (q : ℝ) :
    lpNorm ((c • f : TestFun d) : (Fin d → ℝ) → ℝ) q = |c| * lpNorm (f : (Fin d → ℝ) → ℝ) q := by
  rw [Submodule.coe_smul, lpNorm_const_smul]

theorem TestFun.truncateₗ_supportedOn (P : DyadicCube d) (f : TestFun d) :
    SupportedOn (TestFun.truncateₗ P f : (Fin d → ℝ) → ℝ) P := fun x hx => by
  rw [TestFun.coe_truncateₗ]
  exact Set.indicator_of_notMem hx _

/-- `‖f 𝟙_P‖_q^q = ∫_P |f|^q`. [PROVED] -/
theorem TestFun.lpNorm_truncateₗ_rpow (P : DyadicCube d) (f : TestFun d) {q : ℝ} (hq : 0 < q) :
    lpNorm (TestFun.truncateₗ P f : (Fin d → ℝ) → ℝ) q ^ q =
      ∫ x in P.toSet, |(f : (Fin d → ℝ) → ℝ) x| ^ q := by
  rw [lpNorm_rpow_eq_integral hq (TestFun.memLp (TestFun.truncateₗ P f).2 _),
    TestFun.coe_truncateₗ, ← integral_indicator P.measurableSet_toSet]
  congr 1
  funext x
  by_cases hx : x ∈ P.toSet <;> simp [truncate, hx, Real.zero_rpow hq.ne']

/-- `|[f]_P| ≤ |P|^{-1/q} ‖f‖_q`. [PROVED] -/
theorem abs_avg_le (P : DyadicCube d) (f : TestFun d) {q : ℝ} (hq : 1 ≤ q) :
    |avg P f| ≤ P.vol ^ (-(1 / q)) * lpNorm (f : (Fin d → ℝ) → ℝ) q := by
  have hV := P.vol_pos
  have hH := abs_setIntegral_le_rpow_mul_lpNorm hq (TestFun.memLp f.2 _) P.measurableSet_toSet
    (by rw [P.volume_toSet]; exact ENNReal.ofReal_ne_top)
  rw [P.volume_toSet, ENNReal.toReal_ofReal hV.le] at hH
  rw [avg, abs_div, abs_of_pos hV, div_le_iff₀ hV]
  calc |∫ x in P.toSet, (f : (Fin d → ℝ) → ℝ) x|
      ≤ P.vol ^ (1 - 1 / q) * lpNorm (f : (Fin d → ℝ) → ℝ) q := hH
    _ = P.vol ^ (-(1 / q)) * lpNorm (f : (Fin d → ℝ) → ℝ) q * P.vol := by
        rw [show (1 : ℝ) - 1 / q = -(1 / q) + 1 by ring, Real.rpow_add hV, Real.rpow_one]
        ring

/-- Jensen's inequality for averages: `|[f]_P|^q |P| ≤ ∫_P |f|^q` for `q ≥ 1`. [PROVED] -/
theorem abs_avg_rpow_mul_vol_le (P : DyadicCube d) (f : TestFun d) {q : ℝ} (hq : 1 ≤ q) :
    |avg P f| ^ q * P.vol ≤ ∫ x in P.toSet, |(f : (Fin d → ℝ) → ℝ) x| ^ q := by
  have hq0 : 0 < q := by linarith
  have hq1 : q ≠ 0 := hq0.ne'
  have hV := P.vol_pos
  set L := lpNorm (TestFun.truncateₗ P f : (Fin d → ℝ) → ℝ) q with hL
  have hL0 : 0 ≤ L := ENNReal.toReal_nonneg
  have h1 : |avg P f| ≤ P.vol ^ (-(1 / q)) * L := by
    have := abs_avg_le P (TestFun.truncateₗ P f) hq
    rwa [show avg P (TestFun.truncateₗ P f : (Fin d → ℝ) → ℝ) = avg P f by
      rw [avg, avg, TestFun.coe_truncateₗ, setIntegral_congr_fun (f := truncate P (f : (Fin d → ℝ) →
        ℝ))
        (g := (f : (Fin d → ℝ) → ℝ)) P.measurableSet_toSet
        (fun x hx => Set.indicator_of_mem hx _)]] at this
  calc |avg P f| ^ q * P.vol ≤ (P.vol ^ (-(1 / q)) * L) ^ q * P.vol :=
        mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (abs_nonneg _) h1 hq0.le) hV.le
    _ = L ^ q := by
        rw [Real.mul_rpow (Real.rpow_nonneg hV.le _) hL0, ← Real.rpow_mul hV.le,
          show -(1 / q) * q = -1 by field_simp, Real.rpow_neg_one, mul_right_comm,
          inv_mul_cancel₀ hV.ne', one_mul]
    _ = _ := TestFun.lpNorm_truncateₗ_rpow P f hq0

/-- The power-mean inequality `(∑ a_i)^q ≤ m^{q-1} ∑ a_i^q` for `m` terms `a_i ≥ 0`, `q ≥ 1`.
[PROVED] -/
theorem sum_rpow_le_card_mul_sum_rpow {ι : Type*} (t : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ t, 0 ≤ a i) {q : ℝ} (hq : 1 ≤ q) :
    (∑ i ∈ t, a i) ^ q ≤ (t.card : ℝ) ^ (q - 1) * ∑ i ∈ t, a i ^ q := by
  rcases t.eq_empty_or_nonempty with rfl | hne
  · simp [Real.zero_rpow (by linarith : q ≠ 0)]
  · have hc : (0 : ℝ) < t.card := by exact_mod_cast hne.card_pos
    have h := Real.rpow_arith_mean_le_arith_mean_rpow t (fun _ => (t.card : ℝ)⁻¹) a
      (fun _ _ => by positivity)
      (by rw [Finset.sum_const, nsmul_eq_mul, mul_inv_cancel₀ hc.ne']) ha hq
    rw [← Finset.mul_sum, ← Finset.mul_sum, Real.mul_rpow (by positivity) (Finset.sum_nonneg ha),
      Real.inv_rpow hc.le] at h
    have hpow : (t.card : ℝ) ^ (q - 1) = (t.card : ℝ) ^ q * (t.card : ℝ)⁻¹ := by
      rw [Real.rpow_sub_one hc.ne', div_eq_mul_inv]
    rw [hpow]
    calc (∑ i ∈ t, a i) ^ q
        = (t.card : ℝ) ^ q * (((t.card : ℝ) ^ q)⁻¹ * (∑ i ∈ t, a i) ^ q) := by
          rw [← mul_assoc, mul_inv_cancel₀ (Real.rpow_pos_of_pos hc _).ne', one_mul]
      _ ≤ (t.card : ℝ) ^ q * ((t.card : ℝ)⁻¹ * ∑ i ∈ t, a i ^ q) :=
          mul_le_mul_of_nonneg_left h (Real.rpow_nonneg hc.le _)
      _ = _ := by ring

open Classical in
/-- Bounded overlap: if every point lies in at most `M` cubes of `s`, then
`∑_{P ∈ s} ∫_P |f|^q ≤ M ∫ |f|^q`. [PROVED] -/
theorem sum_setIntegral_le_of_overlap (s : Finset (DyadicCube d)) {M : ℕ}
    (hM : ∀ x, (s.filter fun P => x ∈ P.toSet).card ≤ M) (f : TestFun d) {q : ℝ} (hq : 0 < q) :
    ∑ P ∈ s, ∫ x in P.toSet, |(f : (Fin d → ℝ) → ℝ) x| ^ q ≤
      M * ∫ x, |(f : (Fin d → ℝ) → ℝ) x| ^ q := by
  have hint := TestFun.integrable_abs_rpow f hq
  rw [Finset.sum_congr rfl fun P _ => (integral_indicator P.measurableSet_toSet).symm,
    ← integral_finsetSum s fun P _ => hint.indicator P.measurableSet_toSet, ← integral_const_mul]
  refine integral_mono (integrable_finsetSum s fun P _ => hint.indicator P.measurableSet_toSet)
    (hint.const_mul _) fun x => ?_
  change ∑ P ∈ s, P.toSet.indicator (fun x => |(f : (Fin d → ℝ) → ℝ) x| ^ q) x ≤
    (M : ℝ) * |(f : (Fin d → ℝ) → ℝ) x| ^ q
  simp only [Set.indicator_apply]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hM x) (by positivity)

open Classical in
/-- Bounded overlap for sums of truncations:
`‖∑_{P ∈ s} c_P u 𝟙_P‖_q^q ≤ M^{q-1} ∑_{P ∈ s} |c_P|^q ∫_P |u|^q`. [PROVED] -/
theorem lpNorm_sum_smul_truncateₗ_rpow_le (s : Finset (DyadicCube d)) {M : ℕ}
    (hM : ∀ x, (s.filter fun P => x ∈ P.toSet).card ≤ M) (c : DyadicCube d → ℝ) (u : TestFun d)
    {q : ℝ} (hq : 1 ≤ q) :
    lpNorm ((∑ P ∈ s, c P • TestFun.truncateₗ P u : TestFun d) : (Fin d → ℝ) → ℝ) q ^ q ≤
      (M : ℝ) ^ (q - 1) * ∑ P ∈ s, |c P| ^ q * ∫ x in P.toSet, |(u : (Fin d → ℝ) → ℝ) x| ^ q := by
  have hq0 : 0 < q := by linarith
  have hint := TestFun.integrable_abs_rpow u hq0
  rw [lpNorm_rpow_eq_integral hq0
    (TestFun.memLp (∑ P ∈ s, c P • TestFun.truncateₗ P u : TestFun d).2 _)]
  have hR : ∑ P ∈ s, |c P| ^ q * ∫ x in P.toSet, |(u : (Fin d → ℝ) → ℝ) x| ^ q =
      ∫ x, ∑ P ∈ s, |c P| ^ q * P.toSet.indicator (fun x => |(u : (Fin d → ℝ) → ℝ) x| ^ q) x := by
    rw [integral_finsetSum s fun P _ => (hint.indicator P.measurableSet_toSet).const_mul _]
    exact Finset.sum_congr rfl fun P _ => by
      rw [integral_const_mul, integral_indicator P.measurableSet_toSet]
  rw [hR, ← integral_const_mul]
  refine integral_mono (TestFun.integrable_abs_rpow _ hq0)
    ((integrable_finsetSum s fun P _ =>
      (hint.indicator P.measurableSet_toSet).const_mul _).const_mul _) fun x => ?_
  change |((∑ P ∈ s, c P • TestFun.truncateₗ P u : TestFun d) : (Fin d → ℝ) → ℝ) x| ^ q ≤
    (M : ℝ) ^ (q - 1) *
      ∑ P ∈ s, |c P| ^ q * P.toSet.indicator (fun x => |(u : (Fin d → ℝ) → ℝ) x| ^ q) x
  rw [Submodule.coe_sum, Finset.sum_apply]
  simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, TestFun.coe_truncateₗ, truncate,
    Set.indicator_apply]
  set t := s.filter fun P => x ∈ P.toSet with ht
  have e1 : ∑ P ∈ s, c P * (if x ∈ P.toSet then (u : (Fin d → ℝ) → ℝ) x else 0) =
      (∑ P ∈ t, c P) * (u : (Fin d → ℝ) → ℝ) x := by
    rw [Finset.sum_mul, ht, Finset.sum_filter]
    exact Finset.sum_congr rfl fun P _ => by split_ifs <;> simp
  have e2 : ∑ P ∈ s, |c P| ^ q * (if x ∈ P.toSet then |(u : (Fin d → ℝ) → ℝ) x| ^ q else 0) =
      (∑ P ∈ t, |c P| ^ q) * |(u : (Fin d → ℝ) → ℝ) x| ^ q := by
    rw [Finset.sum_mul, ht, Finset.sum_filter]
    exact Finset.sum_congr rfl fun P _ => by split_ifs <;> simp
  rw [e1, e2, abs_mul, Real.mul_rpow (abs_nonneg _) (abs_nonneg _)]
  have hcard : (t.card : ℝ) ^ (q - 1) ≤ (M : ℝ) ^ (q - 1) :=
    Real.rpow_le_rpow (by positivity) (by exact_mod_cast hM x) (by linarith)
  calc |∑ P ∈ t, c P| ^ q * |(u : (Fin d → ℝ) → ℝ) x| ^ q
      ≤ (∑ P ∈ t, |c P|) ^ q * |(u : (Fin d → ℝ) → ℝ) x| ^ q :=
        mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow (abs_nonneg _) (Finset.abs_sum_le_sum_abs _ _) hq0.le) (by positivity)
    _ ≤ ((t.card : ℝ) ^ (q - 1) * ∑ P ∈ t, |c P| ^ q) * |(u : (Fin d → ℝ) → ℝ) x| ^ q :=
        mul_le_mul_of_nonneg_right
          (sum_rpow_le_card_mul_sum_rpow t _ (fun _ _ => abs_nonneg _) hq) (by positivity)
    _ ≤ ((M : ℝ) ^ (q - 1) * ∑ P ∈ t, |c P| ^ q) * |(u : (Fin d → ℝ) → ℝ) x| ^ q :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hcard (Finset.sum_nonneg fun _ _ => by positivity))
          (by positivity)
    _ = _ := by ring

/-- `‖∑_{P ∈ s} f 𝟙_P‖_q ≤ ‖f‖_q` for a pairwise disjoint collection `s`. [PROVED] -/
theorem lpNorm_sum_truncateₗ_le (s : Finset (DyadicCube d))
    (hdisj : (↑s : Set (DyadicCube d)).PairwiseDisjoint DyadicCube.toSet) (f : TestFun d)
    {q : ℝ} (hq : 1 ≤ q) :
    lpNorm ((∑ P ∈ s, TestFun.truncateₗ P f : TestFun d) : (Fin d → ℝ) → ℝ) q ≤
      lpNorm (f : (Fin d → ℝ) → ℝ) q := by
  have hq0 : 0 < q := by linarith
  have hpow : lpNorm ((∑ P ∈ s, TestFun.truncateₗ P f : TestFun d) : (Fin d → ℝ) → ℝ) q ^ q ≤
      lpNorm (f : (Fin d → ℝ) → ℝ) q ^ q := by
    rw [lpNorm_sum_rpow_eq hq0 s (fun P => TestFun.truncateₗ P f) (fun P => P)
      (fun P => TestFun.truncateₗ_supportedOn P f) hdisj]
    simp only [TestFun.lpNorm_truncateₗ_rpow _ _ hq0]
    rw [lpNorm_rpow_eq_integral hq0 (TestFun.memLp f.2 _),
      ← integral_biUnion_finset s (fun P _ => P.measurableSet_toSet) hdisj
        (fun P _ => (TestFun.integrable_abs_rpow f hq0).integrableOn)]
    exact setIntegral_le_integral (TestFun.integrable_abs_rpow f hq0)
      (Filter.Eventually.of_forall fun x => by positivity)
  exact (Real.rpow_le_rpow_iff ENNReal.toReal_nonneg ENNReal.toReal_nonneg hq0).mp hpow

/-- A cube is contained in its parent. [PROVED] -/
theorem DyadicCube.subset_parent (P : DyadicCube d) : P.toSet ⊆ P.parent.toSet := by
  have := P.parent.child_subset (fun i => decide (P.l i % 2 = 1))
  rwa [P.child_parent] at this

theorem DyadicCube.parent_m (P : DyadicCube d) : P.parent.m = P.m + 1 := rfl

/-- The parent of a proper subcube of `Q` lies in `Q` (for `d ≥ 1`). [PROVED] -/
theorem DyadicCube.parent_subset_of_ssubset (hd : d ≠ 0) {P Q : DyadicCube d}
    (hPQ : P.toSet ⊆ Q.toSet) (hne : P ≠ Q) : P.parent.toSet ⊆ Q.toSet := by
  have hm : P.m < Q.m := lt_of_le_of_ne (DyadicCube.m_le_of_subset hd hPQ)
    fun h => hne (DyadicCube.eq_of_subset_of_m_eq hPQ h)
  have hm' : P.parent.m ≤ Q.m := by
    rw [DyadicCube.parent_m]
    omega
  rcases DyadicCube.subset_or_disjoint P.parent Q hm' with h | h
  · exact h
  · exact absurd (hPQ P.corner_mem) (Set.disjoint_left.mp h (P.subset_parent P.corner_mem))

/-- The average of a nonnegative function over a cube is at most `2^d` times the average over
its parent. [PROVED] -/
theorem avg_le_parent (w : (Fin d → ℝ) → ENNReal) (P : DyadicCube d) :
    (volume P.toSet)⁻¹ * ∫⁻ x in P.toSet, w x ≤
      2 ^ d * ((volume P.parent.toSet)⁻¹ * ∫⁻ x in P.parent.toSet, w x) := by
  have hV := P.vol_pos
  have hV0 := hV.ne'
  have hinv : (volume P.toSet)⁻¹ = 2 ^ d * (volume P.parent.toSet)⁻¹ := by
    rw [DyadicCube.volume_toSet, DyadicCube.volume_toSet, DyadicCube.vol_parent,
      ← ENNReal.ofReal_inv_of_pos hV, ← ENNReal.ofReal_inv_of_pos (by positivity),
      show (2 : ENNReal) ^ d = ENNReal.ofReal (2 ^ d) by
        rw [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat],
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp
  rw [hinv, mul_assoc]
  exact mul_le_mul' le_rfl (mul_le_mul' le_rfl (lintegral_mono_set P.subset_parent))

/-- A perfect Calderón–Zygmund form vanishes if one entry vanishes almost everywhere (through
the kernel representation (iii)). [PROVED] -/
theorem PerfectCZForm.form_eq_zero_of_ae_zero (T : PerfectCZForm d n) (f : Fin n → TestFun d)
    (i : Fin n) (h : (f i : (Fin d → ℝ) → ℝ) =ᵐ[volume] 0) : T.form f = 0 := by
  obtain ⟨K, -, hform⟩ := T.truncation
  rw [hform]
  apply integral_eq_zero_of_ae
  have hnull : volume {y : Fin d → ℝ | ¬ (f i : (Fin d → ℝ) → ℝ) y = 0} = 0 := by
    have := ae_iff.mp h
    simpa using this
  have hpre : volume ((Function.eval i : (Fin n → Fin d → ℝ) → Fin d → ℝ) ⁻¹'
      {y : Fin d → ℝ | ¬ (f i : (Fin d → ℝ) → ℝ) y = 0}) = 0 := by
    rw [volume_pi]
    exact Measure.pi_eval_preimage_null _ hnull
  rw [Filter.EventuallyEq, ae_iff]
  refine measure_mono_null ?_ hpre
  intro x hx
  simp only [Set.mem_ofPred_eq, Set.mem_preimage, Function.eval] at hx ⊢
  intro hfi
  apply hx
  rw [Finset.prod_eq_zero (f := fun j => (f j : (Fin d → ℝ) → ℝ) (x j)) (Finset.mem_univ i) hfi,
    mul_zero]
  rfl

/-- `Λ_P(ρ, u) = 0` if `‖ρ‖_r = 0`. [PROVED] -/
theorem slotForm_eq_zero_of_lpNorm_eq_zero (T : PerfectCZForm d n) (a : Fin n)
    (g : Fin n → TestFun d) (P : DyadicCube d) {r : ℝ} (hr : 0 < r) {ρ : TestFun d}
    (h : lpNorm (ρ : (Fin d → ℝ) → ℝ) r = 0) : slotForm T a g P ρ = 0 := by
  rw [slotForm_apply]
  apply T.form_eq_zero_of_ae_zero _ a
  rw [Function.update_self]
  have hmem := TestFun.memLp ρ.2 (ENNReal.ofReal r)
  have h0 : eLpNorm (ρ : (Fin d → ℝ) → ℝ) (ENNReal.ofReal r) volume = 0 := by
    unfold lpNorm at h
    exact ((ENNReal.toReal_eq_zero_iff _).mp h).resolve_right hmem.eLpNorm_ne_top
  have hae : (ρ : (Fin d → ℝ) → ℝ) =ᵐ[volume] 0 :=
    (eLpNorm_eq_zero_iff (ENNReal.ofReal_pos.mpr hr).ne').mp h0
  change truncate P (ρ : (Fin d → ℝ) → ℝ) =ᵐ[volume] 0
  filter_upwards [hae] with x hx
  simp [truncate, hx]

/-- `𝟙_P` as a dyadic test function. -/
noncomputable def TestFun.ind (P : DyadicCube d) : TestFun d := ⟨P.indicator, indicator_mem_testFun
  P⟩

theorem TestFun.coe_ind (P : DyadicCube d) :
    ((TestFun.ind P : TestFun d) : (Fin d → ℝ) → ℝ) = P.toSet.indicator 1 := rfl

/-- `𝟙_Q 𝟙_P = 𝟙_P` for `P ⊆ Q`. [PROVED] -/
theorem TestFun.truncateₗ_ind_of_subset {P Q : DyadicCube d} (h : P.toSet ⊆ Q.toSet) :
    TestFun.truncateₗ P (TestFun.ind Q) = TestFun.ind P := by
  apply Subtype.ext
  rw [TestFun.coe_truncateₗ, TestFun.coe_ind, TestFun.coe_ind]
  change P.toSet.indicator (Q.toSet.indicator 1) = P.toSet.indicator 1
  rw [Set.indicator_indicator, Set.inter_eq_left.mpr h]

/-- `‖𝟙_P‖_p = |P|^{1/p}`. [PROVED] -/
theorem TestFun.lpNorm_ind (P : DyadicCube d) {p : ℝ} (hp : 0 < p) :
    lpNorm ((TestFun.ind P : TestFun d) : (Fin d → ℝ) → ℝ) p = P.vol ^ (1 / p) := by
  have hpow : lpNorm ((TestFun.ind P : TestFun d) : (Fin d → ℝ) → ℝ) p ^ p = P.vol := by
    rw [lpNorm_rpow_eq_integral hp (TestFun.memLp (TestFun.ind P).2 _), TestFun.coe_ind]
    have e : (fun x => |P.toSet.indicator (1 : (Fin d → ℝ) → ℝ) x| ^ p) =
        P.toSet.indicator (fun _ => (1 : ℝ)) := by
      funext x
      by_cases hx : x ∈ P.toSet <;> simp [hx, Real.zero_rpow hp.ne']
    rw [e, integral_indicator P.measurableSet_toSet, setIntegral_const, measureReal_def,
      P.volume_toSet, ENNReal.toReal_ofReal P.vol_pos.le, smul_eq_mul, mul_one]
  rw [← hpow, one_div]
  exact (Real.rpow_rpow_inv ENNReal.toReal_nonneg hp.ne').symm

/-- `Λ_P(ρ, ρ')`: the form with the entries `g_j 𝟙_P`, `ρ 𝟙_P` in the slot `a` and `ρ' 𝟙_P` in
the slot `b` (p. 40). -/
noncomputable def twoSlotForm (T : PerfectCZForm d n) (a b : Fin n) (g : Fin n → TestFun d)
    (P : DyadicCube d) (ρ ρ' : TestFun d) : ℝ :=
  T.form (Function.update (Function.update (fun j => TestFun.truncateₗ P (g j)) a
    (TestFun.truncateₗ P ρ)) b (TestFun.truncateₗ P ρ'))

/-- `Λ_P(ρ, ρ') = Λ_P(·, ρ')(ρ)`: the two-slot form is the slot form with `ρ'` frozen in the
slot `b`. [PROVED] -/
theorem twoSlotForm_eq_slotForm (T : PerfectCZForm d n) {a b : Fin n} (hab : a ≠ b)
    (g : Fin n → TestFun d) (P : DyadicCube d) (ρ ρ' : TestFun d) :
    twoSlotForm T a b g P ρ ρ' = slotForm T a (Function.update g b ρ') P ρ := by
  rw [slotForm_apply, twoSlotForm]
  have e : (fun j => TestFun.truncateₗ P (Function.update g b ρ' j)) =
      Function.update (fun j => TestFun.truncateₗ P (g j)) b (TestFun.truncateₗ P ρ') := by
    funext j
    by_cases hj : j = b
    · subst hj
      simp
    · simp [Function.update_of_ne hj]
  rw [e, Function.update_comm hab]

/-- `Λ_P(ρ, u)` in the notation of the slot form. [PROVED] -/
theorem twoSlotForm_self (T : PerfectCZForm d n) {a b : Fin n} (hab : a ≠ b)
    (g : Fin n → TestFun d) (P : DyadicCube d) (ρ : TestFun d) :
    twoSlotForm T a b g P ρ (g b) = slotForm T a g P ρ := by
  rw [twoSlotForm_eq_slotForm T hab, Function.update_eq_self]

/-- `Λ_P(ρ, ·)` is linear. [PROVED] -/
theorem twoSlotForm_smul_right (T : PerfectCZForm d n) (a b : Fin n) (g : Fin n → TestFun d)
    (P : DyadicCube d) (ρ : TestFun d) (c : ℝ) (ρ' : TestFun d) :
    twoSlotForm T a b g P ρ (c • ρ') = c * twoSlotForm T a b g P ρ ρ' := by
  unfold twoSlotForm
  rw [map_smul, MultilinearMap.map_update_smul, smul_eq_mul]

theorem twoSlotForm_add_right (T : PerfectCZForm d n) (a b : Fin n) (g : Fin n → TestFun d)
    (P : DyadicCube d) (ρ ρ₁ ρ₂ : TestFun d) :
    twoSlotForm T a b g P ρ (ρ₁ + ρ₂) =
      twoSlotForm T a b g P ρ ρ₁ + twoSlotForm T a b g P ρ ρ₂ := by
  unfold twoSlotForm
  rw [map_add, MultilinearMap.map_update_add]

theorem twoSlotForm_sub_right (T : PerfectCZForm d n) (a b : Fin n) (g : Fin n → TestFun d)
    (P : DyadicCube d) (ρ ρ₁ ρ₂ : TestFun d) :
    twoSlotForm T a b g P ρ (ρ₁ - ρ₂) =
      twoSlotForm T a b g P ρ ρ₁ - twoSlotForm T a b g P ρ ρ₂ := by
  unfold twoSlotForm
  rw [map_sub, MultilinearMap.map_update_sub]

theorem twoSlotForm_sum_right {ι : Type*} (T : PerfectCZForm d n) (a b : Fin n)
    (g : Fin n → TestFun d) (P : DyadicCube d) (ρ : TestFun d) (s : Finset ι)
    (f : ι → TestFun d) :
    twoSlotForm T a b g P ρ (∑ i ∈ s, f i) = ∑ i ∈ s, twoSlotForm T a b g P ρ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    unfold twoSlotForm
    rw [map_zero, MultilinearMap.map_update_zero]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, twoSlotForm_add_right, ih]

/-- `Λ_P(ρ, ρ') = Λ_P(ρ, ·)(ρ')`: the two-slot form as a slot form in the slot `b` with `ρ` frozen
in
the slot `a`. [PROVED] -/
theorem twoSlotForm_eq_slotForm' (T : PerfectCZForm d n) (a b : Fin n) (g : Fin n → TestFun d)
    (P : DyadicCube d) (ρ ρ' : TestFun d) :
    twoSlotForm T a b g P ρ ρ' = slotForm T b (Function.update g a ρ) P ρ' := by
  rw [slotForm_apply, twoSlotForm]
  have e : (fun j => TestFun.truncateₗ P (Function.update g a ρ j)) =
      Function.update (fun j => TestFun.truncateₗ P (g j)) a (TestFun.truncateₗ P ρ) := by
    funext j
    by_cases hj : j = a
    · subst hj
      simp
    · simp [Function.update_of_ne hj]
  rw [e]

theorem twoSlotForm_sub_left (T : PerfectCZForm d n) {a b : Fin n} (hab : a ≠ b)
    (g : Fin n → TestFun d) (P : DyadicCube d) (ρ₁ ρ₂ ρ' : TestFun d) :
    twoSlotForm T a b g P (ρ₁ - ρ₂) ρ' =
      twoSlotForm T a b g P ρ₁ ρ' - twoSlotForm T a b g P ρ₂ ρ' := by
  simp only [twoSlotForm_eq_slotForm T hab, map_sub]

theorem twoSlotForm_add_left (T : PerfectCZForm d n) {a b : Fin n} (hab : a ≠ b)
    (g : Fin n → TestFun d) (P : DyadicCube d) (ρ₁ ρ₂ ρ' : TestFun d) :
    twoSlotForm T a b g P (ρ₁ + ρ₂) ρ' =
      twoSlotForm T a b g P ρ₁ ρ' + twoSlotForm T a b g P ρ₂ ρ' := by
  simp only [twoSlotForm_eq_slotForm T hab, map_add]

/-- Truncation of the entries is idempotent in the two-slot form. [PROVED] -/
theorem twoSlotForm_truncateₗ_right (T : PerfectCZForm d n) (a b : Fin n) (g : Fin n → TestFun d)
    (P : DyadicCube d) (ρ ρ' : TestFun d) :
    twoSlotForm T a b g P ρ (TestFun.truncateₗ P ρ') = twoSlotForm T a b g P ρ ρ' := by
  unfold twoSlotForm
  rw [TestFun.truncateₗ_of_supportedOn (TestFun.truncateₗ_supportedOn P ρ')]

theorem twoSlotForm_truncateₗ_left (T : PerfectCZForm d n) (a b : Fin n) (g : Fin n → TestFun d)
    (P : DyadicCube d) (ρ ρ' : TestFun d) :
    twoSlotForm T a b g P (TestFun.truncateₗ P ρ) ρ' = twoSlotForm T a b g P ρ ρ' := by
  unfold twoSlotForm
  rw [TestFun.truncateₗ_of_supportedOn (TestFun.truncateₗ_supportedOn P ρ)]

/-- **The smoothness step for the two-slot form** (the "vanishing mean" argument of p. 44): if
`ρ'` is supported on `P ⊆ Q` and has mean zero, then `Λ_Q(ρ, ρ') = Λ_P(ρ, ρ')`. [PROVED] -/
theorem twoSlotForm_eq_of_subset (T : PerfectCZForm d n) (a b : Fin n) (g : Fin n → TestFun d)
    {P Q : DyadicCube d} (hPQ : P.toSet ⊆ Q.toSet) (ρ : TestFun d) {ρ' : TestFun d}
    (hρ' : SupportedOn ρ' P) (hρ0 : MeanZero (ρ' : (Fin d → ℝ) → ℝ)) :
    twoSlotForm T a b g P ρ ρ' = twoSlotForm T a b g Q ρ ρ' := by
  rw [twoSlotForm_eq_slotForm', twoSlotForm_eq_slotForm']
  exact slotForm_eq_of_subset T b _ hPQ hρ' hρ0

theorem lpNorm_nonneg (g : (Fin d → ℝ) → ℝ) (p : ℝ) : 0 ≤ lpNorm g p := ENNReal.toReal_nonneg

/-- Truncation does not increase the `L^q` norm. [PROVED] -/
theorem TestFun.lpNorm_truncateₗ_le (P : DyadicCube d) (f : TestFun d) {q : ℝ} (hq : 0 < q) :
    lpNorm (TestFun.truncateₗ P f : (Fin d → ℝ) → ℝ) q ≤ lpNorm (f : (Fin d → ℝ) → ℝ) q := by
  refine (Real.rpow_le_rpow_iff (lpNorm_nonneg _ _) (lpNorm_nonneg _ _) hq).mp ?_
  rw [TestFun.lpNorm_truncateₗ_rpow P f hq, lpNorm_rpow_eq_integral hq (TestFun.memLp f.2 _)]
  exact setIntegral_le_integral (TestFun.integrable_abs_rpow f hq)
    (Filter.Eventually.of_forall fun x => by positivity)

/-- `|[f]_P| |P|^{1/q} ≤ ‖f 𝟙_P‖_q` (Jensen's inequality). [PROVED] -/
theorem abs_avg_mul_rpow_le (P : DyadicCube d) (f : TestFun d) {q : ℝ} (hq : 1 ≤ q) :
    |avg P f| * P.vol ^ (1 / q) ≤ lpNorm (TestFun.truncateₗ P f : (Fin d → ℝ) → ℝ) q := by
  have hq0 : 0 < q := by linarith
  have hV := P.vol_pos
  refine (Real.rpow_le_rpow_iff (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg hV.le _))
    (lpNorm_nonneg _ _) hq0).mp ?_
  rw [Real.mul_rpow (abs_nonneg _) (Real.rpow_nonneg hV.le _),
    ← Real.rpow_mul hV.le, one_div_mul_cancel hq0.ne', Real.rpow_one,
    TestFun.lpNorm_truncateₗ_rpow P f hq0]
  exact abs_avg_rpow_mul_vol_le P f hq

/-- `‖f‖_q ≤ C^{1/q}` when `∫ |f|^q ≤ C`. [PROVED] -/
theorem TestFun.lpNorm_le_rpow_of_integral_le (f : TestFun d) {q : ℝ} (hq : 0 < q) {C : ℝ}
    (h : ∫ x, |(f : (Fin d → ℝ) → ℝ) x| ^ q ≤ C) :
    lpNorm (f : (Fin d → ℝ) → ℝ) q ≤ C ^ (1 / q) := by
  have h2 : lpNorm (f : (Fin d → ℝ) → ℝ) q ^ q ≤ C :=
    (lpNorm_rpow_eq_integral hq (TestFun.memLp f.2 _)).trans_le h
  calc lpNorm (f : (Fin d → ℝ) → ℝ) q
      = (lpNorm (f : (Fin d → ℝ) → ℝ) q ^ q) ^ (1 / q) := by
        rw [one_div]
        exact (Real.rpow_rpow_inv ENNReal.toReal_nonneg hq.ne').symm
    _ ≤ C ^ (1 / q) :=
        Real.rpow_le_rpow (Real.rpow_nonneg ENNReal.toReal_nonneg _) h2 (by positivity)

/-- `∫ 𝟙_P = |P|`. [PROVED] -/
theorem TestFun.integral_ind (P : DyadicCube d) :
    ∫ x, ((TestFun.ind P : TestFun d) : (Fin d → ℝ) → ℝ) x = P.vol := by
  rw [TestFun.coe_ind, integral_indicator_one P.measurableSet_toSet, measureReal_def,
    P.volume_toSet, ENNReal.toReal_ofReal P.vol_pos.le]

/-- `∫_P |𝟙_Q| = |P|` for `P ⊆ Q`. [PROVED] -/
theorem TestFun.setIntegral_abs_ind {P Q : DyadicCube d} (h : P.toSet ⊆ Q.toSet) :
    ∫ x in P.toSet, |((TestFun.ind Q : TestFun d) : (Fin d → ℝ) → ℝ) x| = P.vol := by
  rw [TestFun.coe_ind, setIntegral_congr_fun P.measurableSet_toSet
    (f := fun x => |Q.toSet.indicator (1 : (Fin d → ℝ) → ℝ) x|) (g := fun _ => (1 : ℝ))
    (fun x hx => by simp [Set.indicator_of_mem (h hx)]), setIntegral_const, measureReal_def,
    P.volume_toSet, ENNReal.toReal_ofReal P.vol_pos.le, smul_eq_mul, mul_one]

/-- `∑_ε f 𝟙_{child ε} = f` for `f` supported on `R`. [PROVED] -/
theorem TestFun.sum_truncateₗ_children (R : DyadicCube d) (f : TestFun d)
    (hf : SupportedOn (f : (Fin d → ℝ) → ℝ) R) :
    ∑ ε : Fin d → Bool, TestFun.truncateₗ (R.child ε) f = f := by
  apply Subtype.ext
  rw [Submodule.coe_sum]
  funext x
  simp only [Finset.sum_apply, TestFun.coe_truncateₗ, truncate]
  by_cases hx : x ∈ R.toSet
  · obtain ⟨ε₀, hε₀⟩ : ∃ ε₀, x ∈ (R.child ε₀).toSet := ⟨_, R.mem_childAt hx⟩
    rw [Finset.sum_eq_single ε₀]
    · exact Set.indicator_of_mem hε₀ _
    · intro ε _ hne
      apply Set.indicator_of_notMem
      exact fun hx' => Set.disjoint_left.mp (R.child_disjoint hne) hx' hε₀
    · exact fun h => absurd (Finset.mem_univ _) h
  · rw [hf x hx]
    exact Finset.sum_eq_zero fun ε _ => Set.indicator_of_notMem
      (fun h => hx (R.child_subset ε h)) _

/-- Truncating the entries after an update. [PROVED] -/
theorem TestFun.truncateₗ_comp_update {ι : Type*} [DecidableEq ι] (P : DyadicCube d)
    (m : ι → TestFun d) (i : ι) (x : TestFun d) :
    (fun j => TestFun.truncateₗ P (Function.update m i x j)) =
      Function.update (fun j => TestFun.truncateₗ P (m j)) i (TestFun.truncateₗ P x) := by
  funext j
  by_cases hj : j = i
  · subst hj
    simp
  · simp [Function.update_of_ne hj]

/-- `𝟙_P 𝟙_R f = 𝟙_P f` for `P ⊆ R`. [PROVED] -/
theorem TestFun.truncateₗ_truncateₗ_of_subset {P R : DyadicCube d} (h : P.toSet ⊆ R.toSet)
    (f : TestFun d) : TestFun.truncateₗ P (TestFun.truncateₗ R f) = TestFun.truncateₗ P f := by
  apply Subtype.ext
  simp only [TestFun.coe_truncateₗ, truncate]
  rw [Set.indicator_indicator, Set.inter_eq_left.mpr h]

theorem TestFun.ind_supportedOn (P : DyadicCube d) :
    SupportedOn ((TestFun.ind P : TestFun d) : (Fin d → ℝ) → ℝ) P :=
  fun _ hx => Set.indicator_of_notMem hx _

theorem TestFun.truncateₗ_ind (P : DyadicCube d) :
    TestFun.truncateₗ P (TestFun.ind P) = TestFun.ind P :=
  TestFun.truncateₗ_ind_of_subset (subset_refl _)

/-- `‖f 𝟙_P‖_q ≤ ‖f 𝟙_R‖_q` for `P ⊆ R`. [PROVED] -/
theorem TestFun.lpNorm_truncateₗ_mono {P R : DyadicCube d} (h : P.toSet ⊆ R.toSet)
    (f : TestFun d) {q : ℝ} (hq : 0 < q) :
    lpNorm (TestFun.truncateₗ P f : (Fin d → ℝ) → ℝ) q ≤
      lpNorm (TestFun.truncateₗ R f : (Fin d → ℝ) → ℝ) q := by
  rw [← TestFun.truncateₗ_truncateₗ_of_subset h f]
  exact TestFun.lpNorm_truncateₗ_le P _ hq

/-- **Expansion over the children and the decay condition** (p. 45): if all entries `f_j` are
supported on `R` and the entry `f_b` on a child `P` of `R`, then replacing every entry `f_j` by
`f_j 𝟙_P` changes `Λ(f)` by at most `n 2^d ∏_j ‖f_j‖_{p_j}`. Writing `f_j = ∑_{P'} f_j 𝟙_{P'}` over
the children `P'` of `R`, slot by slot, every term with an entry supported on a child `P' ≠ P` has
two entries on different children of `R` and is bounded by the decay condition (1.1). [PROVED] -/
theorem PerfectCZForm.abs_form_sub_truncate_child_le (T : PerfectCZForm d n) (p : HolderTuple n)
    (R : DyadicCube d) (ε : Fin d → Bool) (f : Fin n → TestFun d) (b : Fin n)
    (hsupp : ∀ j, SupportedOn (f j) R) (hb : SupportedOn (f b) (R.child ε)) :
    |T.form f - T.form (fun j => TestFun.truncateₗ (R.child ε) (f j))| ≤
      n * 2 ^ d * prodNorm p f := by
  classical
  set N := prodNorm p f with hN
  have hN0 : 0 ≤ N := prodNorm_nonneg p f
  have hpj : ∀ j, 0 < p.p j := fun j => by linarith [p.one_lt j]
  -- hybrid entries: truncated to the child on the slots of `s`
  set hyb : Finset (Fin n) → Fin n → TestFun d := fun s j =>
    if j ∈ s then TestFun.truncateₗ (R.child ε) (f j) else f j with hhyb
  have hyb_supp : ∀ s j, SupportedOn (hyb s j) R := by
    intro s j x hx
    simp only [hhyb]
    split_ifs
    · exact TestFun.truncateₗ_supportedOn (R.child ε) (f j) x fun h => hx (R.child_subset ε h)
    · exact hsupp j x hx
  have hyb_norm : ∀ s j, lpNorm (hyb s j : (Fin d → ℝ) → ℝ) (p.p j) ≤
      lpNorm (f j : (Fin d → ℝ) → ℝ) (p.p j) := by
    intro s j
    simp only [hhyb]
    split_ifs
    · exact TestFun.lpNorm_truncateₗ_le (R.child ε) (f j) (hpj j)
    · exact le_rfl
  -- one step: truncating one more slot `i ≠ b`
  have hstep : ∀ s : Finset (Fin n), b ∉ s → ∀ i, i ∉ s → i ≠ b →
      |T.form (hyb s) - T.form (hyb (insert i s))| ≤ 2 ^ d * N := by
    intro s hbs i hi hib
    have h1 : hyb (insert i s) =
        Function.update (hyb s) i (TestFun.truncateₗ (R.child ε) (f i)) := by
      funext j
      by_cases hj : j = i
      · rw [hj]
        simp [hhyb]
      · simp [hhyb, hj]
    have h2' : Function.update (hyb s) i (f i) = hyb s := by
      have : f i = hyb s i := by simp [hhyb, hi]
      rw [this]
      exact Function.update_eq_self i (hyb s)
    have h2 : T.form (hyb s) = T.form (Function.update (hyb s) i (f i)) := by rw [h2']
    have hsum : f i - TestFun.truncateₗ (R.child ε) (f i) =
        ∑ ε' ∈ Finset.univ.erase ε, TestFun.truncateₗ (R.child ε') (f i) := by
      rw [sub_eq_iff_eq_add, Finset.sum_erase_add _ _ (Finset.mem_univ ε)]
      exact (TestFun.sum_truncateₗ_children R (f i) (hsupp i)).symm
    rw [h1, h2, ← MultilinearMap.map_update_sub, hsum, MultilinearMap.map_update_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hterm : ∀ ε' ∈ Finset.univ.erase ε,
        |T.form (Function.update (hyb s) i (TestFun.truncateₗ (R.child ε') (f i)))| ≤ N := by
      intro ε' hε'
      have hne : ε' ≠ ε := (Finset.mem_erase.mp hε').1
      set e := Function.update (hyb s) i (TestFun.truncateₗ (R.child ε') (f i)) with he
      have he_supp : ∀ j, SupportedOn (e j) R := by
        intro j
        by_cases hj : j = i
        · rw [hj, he, Function.update_self]
          exact fun x hx => TestFun.truncateₗ_supportedOn _ (f i) x
            fun h => hx (R.child_subset _ h)
        · rw [he, Function.update_of_ne hj]
          exact hyb_supp s j
      have hei : SupportedOn (e i) (R.child ε') := by
        rw [he, Function.update_self]
        exact TestFun.truncateₗ_supportedOn _ _
      have heb : SupportedOn (e b) (R.child ε) := by
        rw [he, Function.update_of_ne (Ne.symm hib)]
        simpa [hhyb, hbs] using hb
      have hdecay := T.decay p R e he_supp ⟨i, b, hib, ε', ε, hne, hei, heb⟩
      refine hdecay.trans ?_
      unfold prodNorm
      refine Finset.prod_le_prod₀ (fun _ _ => ENNReal.toReal_nonneg) fun j _ => ?_
      by_cases hj : j = i
      · rw [hj, he, Function.update_self]
        exact TestFun.lpNorm_truncateₗ_le _ (f i) (hpj i)
      · rw [he, Function.update_of_ne hj]
        exact hyb_norm s j
    calc ∑ ε' ∈ Finset.univ.erase ε,
          |T.form (Function.update (hyb s) i (TestFun.truncateₗ (R.child ε') (f i)))|
        ≤ ∑ _ε' ∈ Finset.univ.erase ε, N := Finset.sum_le_sum hterm
      _ = ((Finset.univ.erase ε).card : ℝ) * N := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 2 ^ d * N := by
          refine mul_le_mul_of_nonneg_right ?_ hN0
          calc ((Finset.univ.erase ε).card : ℝ)
              ≤ (Finset.univ : Finset (Fin d → Bool)).card := by
                exact_mod_cast Finset.card_le_card (Finset.erase_subset _ _)
            _ = 2 ^ d := by simp [Finset.card_univ]
  -- induction over the truncated slots
  have hind : ∀ s : Finset (Fin n), s ⊆ Finset.univ.erase b →
      |T.form f - T.form (hyb s)| ≤ s.card * (2 ^ d * N) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro _
      have : hyb ∅ = f := by
        funext j
        simp [hhyb]
      simp [this]
    | insert i s hi ih =>
      intro hsub
      have hib : i ≠ b := (Finset.mem_erase.mp (hsub (Finset.mem_insert_self i s))).1
      have hs : s ⊆ Finset.univ.erase b := (Finset.subset_insert i s).trans hsub
      have hbs : b ∉ s := fun h => (Finset.mem_erase.mp (hs h)).1 rfl
      calc |T.form f - T.form (hyb (insert i s))|
          ≤ |T.form f - T.form (hyb s)| + |T.form (hyb s) - T.form (hyb (insert i s))| :=
            abs_sub_le _ _ _
        _ ≤ s.card * (2 ^ d * N) + 2 ^ d * N := add_le_add (ih hs) (hstep s hbs i hi hib)
        _ = (insert i s).card * (2 ^ d * N) := by
            rw [Finset.card_insert_of_notMem hi]
            push_cast
            ring
  have hfin : hyb (Finset.univ.erase b) = fun j => TestFun.truncateₗ (R.child ε) (f j) := by
    funext j
    by_cases hj : j = b
    · have hbb : b ∉ Finset.univ.erase b := fun h => (Finset.mem_erase.mp h).1 rfl
      rw [hj, show hyb (Finset.univ.erase b) b = f b by simp [hhyb, hbb]]
      exact (TestFun.truncateₗ_of_supportedOn hb).symm
    · simp [hhyb, hj]
  have h := hind (Finset.univ.erase b) (Finset.Subset.refl _)
  rw [hfin] at h
  refine h.trans ?_
  calc ((Finset.univ.erase b).card : ℝ) * (2 ^ d * N)
      ≤ n * (2 ^ d * N) := by
        refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (by positivity) hN0)
        calc ((Finset.univ.erase b).card : ℝ) ≤ (Finset.univ : Finset (Fin n)).card := by
              exact_mod_cast Finset.card_le_card (Finset.erase_subset _ _)
          _ = n := by simp
    _ = n * 2 ^ d * prodNorm p f := by rw [hN]; ring

open Classical in
/-- Bounded overlap with a real bound `M`: `∑_{P ∈ s} ∫_P |f|^q ≤ M ∫ |f|^q` if every point lies in
at most `M` cubes of `s`. [PROVED] -/
theorem sum_setIntegral_le_of_overlap_real (s : Finset (DyadicCube d)) {M : ℝ}
    (hM : ∀ x, ((s.filter fun P => x ∈ P.toSet).card : ℝ) ≤ M) (f : TestFun d) {q : ℝ}
    (hq : 0 < q) :
    ∑ P ∈ s, ∫ x in P.toSet, |(f : (Fin d → ℝ) → ℝ) x| ^ q ≤
      M * ∫ x, |(f : (Fin d → ℝ) → ℝ) x| ^ q := by
  have hint := TestFun.integrable_abs_rpow f hq
  rw [Finset.sum_congr rfl fun P _ => (integral_indicator P.measurableSet_toSet).symm,
    ← integral_finsetSum s fun P _ => hint.indicator P.measurableSet_toSet, ← integral_const_mul]
  refine integral_mono (integrable_finsetSum s fun P _ => hint.indicator P.measurableSet_toSet)
    (hint.const_mul _) fun x => ?_
  change ∑ P ∈ s, P.toSet.indicator (fun x => |(f : (Fin d → ℝ) → ℝ) x| ^ q) x ≤
    M * |(f : (Fin d → ℝ) → ℝ) x| ^ q
  simp only [Set.indicator_apply]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (hM x) (by positivity)

/-- **Hölder's inequality for finite sums with finitely many factors**: if `∑_j 1/p_j = 1` with
`p_j > 0`, then `∑_i ∏_j a_{j,i} ≤ ∏_j (∑_i a_{j,i}^{p_j})^{1/p_j}` for nonnegative `a`.
Derived from Mathlib's `ENNReal.lintegral_prod_norm_pow_le` for the counting measure. [PROVED] -/
theorem sum_prod_le_prod_sum_rpow {ι : Type*} [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (s : Finset ι) {κ : Type*} (J : Finset κ) (p : κ → ℝ) (hp : ∀ j ∈ J, 0 < p j)
    (hp1 : ∑ j ∈ J, 1 / p j = 1) (a : κ → ι → ℝ) (ha : ∀ j ∈ J, ∀ i ∈ s, 0 ≤ a j i) :
    ∑ i ∈ s, ∏ j ∈ J, a j i ≤ ∏ j ∈ J, (∑ i ∈ s, a j i ^ p j) ^ (1 / p j) := by
  have key := ENNReal.lintegral_prod_norm_pow_le (μ := (Measure.count : Measure s)) J
    (f := fun j (i : s) => ENNReal.ofReal (a j i ^ p j))
    (fun j _ => (measurable_of_countable _).aemeasurable) (p := fun j => 1 / p j) hp1
    (fun j hj => by have := hp j hj; positivity)
  simp only [lintegral_fintype, Measure.count_singleton, mul_one] at key
  have hL : ∑ i : s, ∏ j ∈ J, ENNReal.ofReal (a j i ^ p j) ^ (1 / p j) =
      ENNReal.ofReal (∑ i ∈ s, ∏ j ∈ J, a j i) := by
    rw [← Finset.sum_coe_sort s (fun i => ∏ j ∈ J, a j i),
      ENNReal.ofReal_sum_of_nonneg fun (i : s) _ => Finset.prod_nonneg fun j hj => ha j hj i i.2]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ENNReal.ofReal_prod_of_nonneg fun j hj => ha j hj i i.2]
    refine Finset.prod_congr rfl fun j hj => ?_
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg (ha j hj i i.2) _)
      (one_div_nonneg.mpr (hp j hj).le),
      one_div, Real.rpow_rpow_inv (ha j hj i i.2) (hp j hj).ne']
  have hR : ∏ j ∈ J, (∑ i : s, ENNReal.ofReal (a j i ^ p j)) ^ (1 / p j) =
      ENNReal.ofReal (∏ j ∈ J, (∑ i ∈ s, a j i ^ p j) ^ (1 / p j)) := by
    rw [ENNReal.ofReal_prod_of_nonneg fun j _ => Real.rpow_nonneg
      (Finset.sum_nonneg fun i hi => Real.rpow_nonneg (ha j ‹_› i hi) _) _]
    refine Finset.prod_congr rfl fun j hj => ?_
    rw [← Finset.sum_coe_sort s (fun i => a j i ^ p j)]
    have h0 : 0 ≤ ∑ i : s, a j i ^ p j :=
      Finset.sum_nonneg fun i _ => Real.rpow_nonneg (ha j hj i i.2) _
    rw [← ENNReal.ofReal_rpow_of_nonneg h0 (one_div_nonneg.mpr (hp j hj).le),
      ENNReal.ofReal_sum_of_nonneg fun (i : s) _ => Real.rpow_nonneg (ha j hj i i.2) _]
  rw [hL, hR] at key
  exact (ENNReal.ofReal_le_ofReal_iff (Finset.prod_nonneg fun j _ => Real.rpow_nonneg
    (Finset.sum_nonneg fun i hi => Real.rpow_nonneg (ha j ‹_› i hi) _) _)).mp key

/-- The product of the norms of the entries `m_j` (`j ≠ a, b`), `x` in the slot `a`, `y` in the
slot `b`. [PROVED] -/
theorem prodNorm_update_update (p : HolderTuple n) {a b : Fin n} (hab : a ≠ b)
    (m : Fin n → TestFun d) (x y : TestFun d) :
    prodNorm p (Function.update (Function.update m a x) b y) =
      (∏ j ∈ (Finset.univ.erase a).erase b, lpNorm (m j : (Fin d → ℝ) → ℝ) (p.p j)) *
        lpNorm (x : (Fin d → ℝ) → ℝ) (p.p a) * lpNorm (y : (Fin d → ℝ) → ℝ) (p.p b) := by
  unfold prodNorm
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ b),
    ← Finset.mul_prod_erase (Finset.univ.erase b) _
      (Finset.mem_erase.mpr ⟨hab, Finset.mem_univ a⟩)]
  have hb : Function.update (Function.update m a x) b y b = y := by simp
  have ha : Function.update (Function.update m a x) b y a = x := by
    rw [Function.update_of_ne hab, Function.update_self]
  have hJ : (Finset.univ.erase b).erase a = (Finset.univ.erase a).erase b :=
    Finset.erase_right_comm
  have hent : ∀ j ∈ (Finset.univ.erase a).erase b,
      Function.update (Function.update m a x) b y j = m j := by
    intro j hj
    rw [Finset.mem_erase, Finset.mem_erase] at hj
    rw [Function.update_of_ne hj.1, Function.update_of_ne hj.2.1]
  rw [hb, ha, hJ, Finset.prod_congr rfl fun j hj => by rw [hent j hj]]
  ring

/-- A bound `|Λ(f)| ≤ A₀ ∏ ‖f_j‖_{p_j}` for all entries gives the bound
`|Λ_P(ρ, ρ')| ≤ A₀ F_P ‖ρ 𝟙_P‖_{p_a} ‖ρ' 𝟙_P‖_{p_b}` for the two-slot form. [PROVED] -/
theorem abs_twoSlotForm_le_of_bound (T : PerfectCZForm d n) (p : HolderTuple n) {a b : Fin n}
    (hab : a ≠ b) (g : Fin n → TestFun d) (P : DyadicCube d) (ρ ρ' : TestFun d) {A₀ : ℝ}
    (hA : ∀ f, |T.form f| ≤ A₀ * prodNorm p f) :
    |twoSlotForm T a b g P ρ ρ'| ≤
      A₀ * (∏ j ∈ (Finset.univ.erase a).erase b,
          lpNorm (TestFun.truncateₗ P (g j) : (Fin d → ℝ) → ℝ) (p.p j)) *
        lpNorm (TestFun.truncateₗ P ρ : (Fin d → ℝ) → ℝ) (p.p a) *
        lpNorm (TestFun.truncateₗ P ρ' : (Fin d → ℝ) → ℝ) (p.p b) := by
  unfold twoSlotForm
  refine (hA _).trans (le_of_eq ?_)
  rw [prodNorm_update_update p hab]
  ring

/-- A constant `A₀` with `|Λ(f)| ≤ A₀ ∏ ‖f_j‖_{p_j}` for all entries (which exists by the
truncation assumption, `PerfectCZForm.exists_bound`). -/
noncomputable def PerfectCZForm.A₀ (T : PerfectCZForm d n) (p : HolderTuple n) : ℝ :=
  Classical.choose (T.exists_bound p)

theorem PerfectCZForm.A₀_nonneg (T : PerfectCZForm d n) (p : HolderTuple n) : 0 ≤ T.A₀ p :=
  (Classical.choose_spec (T.exists_bound p)).1

theorem PerfectCZForm.abs_form_le_A₀ (T : PerfectCZForm d n) (p : HolderTuple n)
    (f : Fin n → TestFun d) : |T.form f| ≤ T.A₀ p * prodNorm p f :=
  (Classical.choose_spec (T.exists_bound p)).2 f

/-- `∫⁻_s ‖f‖^p < ∞` for a dyadic test function `f`. [PROVED] -/
theorem TestFun.setLIntegral_enorm_rpow_ne_top (f : TestFun d) {p : ℝ} (hp : 0 < p)
    (s : Set (Fin d → ℝ)) : ∫⁻ x in s, ‖(f : (Fin d → ℝ) → ℝ) x‖ₑ ^ p ≠ ⊤ := by
  have hmem : MemLp (f : (Fin d → ℝ) → ℝ) (ENNReal.ofReal p) volume := TestFun.memLp f.2 _
  have h : ∫⁻ x, ‖(f : (Fin d → ℝ) → ℝ) x‖ₑ ^ p =
      eLpNorm (f : (Fin d → ℝ) → ℝ) (ENNReal.ofReal p) volume ^ p := by
    rw [eLpNorm_eq_eLpNorm' (ENNReal.ofReal_pos.mpr hp).ne' ENNReal.ofReal_ne_top
      hmem.aestronglyMeasurable, eLpNorm'_eq_lintegral_enorm, ENNReal.toReal_ofReal hp.le,
      one_div, ENNReal.rpow_inv_rpow hp.ne']
  refine ne_top_of_le_ne_top ?_ (setLIntegral_le_lintegral s _)
  rw [h]
  exact ENNReal.rpow_ne_top_of_nonneg hp.le hmem.eLpNorm_ne_top

/-- Two dyadic cubes are nested or disjoint. [PROVED] -/
theorem DyadicCube.disjoint_of_not_subset {P S : DyadicCube d} (h1 : ¬ P.toSet ⊆ S.toSet)
    (h2 : ¬ S.toSet ⊆ P.toSet) : Disjoint S.toSet P.toSet := by
  rcases le_total P.m S.m with hm | hm
  · rcases DyadicCube.subset_or_disjoint P S hm with h | h
    · exact absurd h h1
    · exact h.symm
  · rcases DyadicCube.subset_or_disjoint S P hm with h | h
    · exact absurd h h2
    · exact h

/-- `𝟙_S 𝟙_P f = 0` for disjoint cubes. [PROVED] -/
theorem TestFun.truncateₗ_truncateₗ_of_disjoint {S P : DyadicCube d}
    (h : Disjoint S.toSet P.toSet) (f : TestFun d) :
    TestFun.truncateₗ S (TestFun.truncateₗ P f) = 0 := by
  apply Subtype.ext
  simp only [TestFun.coe_truncateₗ, truncate]
  rw [Set.indicator_indicator, Set.disjoint_iff_inter_eq_empty.mp h, Set.indicator_empty]
  rfl

open Classical in
/-- **Truncating a sum of truncations to a cube `S`** (p. 47): the cubes inside `S` keep their
terms, the cubes strictly containing `S` contribute multiples of `f 𝟙_S`, and the others vanish.
[PROVED] -/
theorem TestFun.truncateₗ_sum_smul_truncateₗ (S : DyadicCube d) (s : Finset (DyadicCube d))
    (c : DyadicCube d → ℝ) (f : TestFun d) :
    TestFun.truncateₗ S (∑ P ∈ s, c P • TestFun.truncateₗ P f) =
      ∑ P ∈ s with P.toSet ⊆ S.toSet, c P • TestFun.truncateₗ P f +
      (∑ P ∈ s with ¬ P.toSet ⊆ S.toSet ∧ S.toSet ⊆ P.toSet, c P) • TestFun.truncateₗ S f := by
  rw [map_sum]
  simp only [map_smul]
  rw [← Finset.sum_filter_add_sum_filter_not s (fun P => P.toSet ⊆ S.toSet)]
  congr 1
  · refine Finset.sum_congr rfl fun P hP => ?_
    have hPS : P.toSet ⊆ S.toSet := (Finset.mem_filter.mp hP).2
    rw [TestFun.truncateₗ_of_supportedOn
      (fun x hx => TestFun.truncateₗ_supportedOn P f x fun h => hx (hPS h))]
  · rw [Finset.sum_smul, ← Finset.sum_filter_add_sum_filter_not
      (s.filter fun P => ¬ P.toSet ⊆ S.toSet) (fun P => S.toSet ⊆ P.toSet), Finset.filter_filter,
      Finset.filter_filter]
    have h0 : ∑ P ∈ s with ¬ P.toSet ⊆ S.toSet ∧ ¬ S.toSet ⊆ P.toSet,
        c P • TestFun.truncateₗ S (TestFun.truncateₗ P f) = 0 := by
      refine Finset.sum_eq_zero fun P hP => ?_
      have h := (Finset.mem_filter.mp hP).2
      rw [TestFun.truncateₗ_truncateₗ_of_disjoint (DyadicCube.disjoint_of_not_subset h.1 h.2),
        smul_zero]
    rw [h0, add_zero]
    refine Finset.sum_congr rfl fun P hP => ?_
    rw [TestFun.truncateₗ_truncateₗ_of_subset (Finset.mem_filter.mp hP).2.2]

/-- The real form of an average bound: from
`|S|^{-1} ∫_S ‖f‖^q ≤ C |Q|^{-1} ∫_Q ‖f‖^q` (as `lintegral`s) to
`∫_S |f|^q ≤ C (|S|/|Q|) ∫_Q |f|^q`. [PROVED] -/
theorem TestFun.setIntegral_rpow_le_of_avg_le (f : TestFun d) {q : ℝ} (hq : 0 < q)
    (S Q : DyadicCube d) {C : ℝ} (hC : 0 ≤ C)
    (h : (volume S.toSet)⁻¹ * ∫⁻ x in S.toSet, ‖(f : (Fin d → ℝ) → ℝ) x‖ₑ ^ q ≤
      ENNReal.ofReal C *
        ((volume Q.toSet)⁻¹ * ∫⁻ x in Q.toSet, ‖(f : (Fin d → ℝ) → ℝ) x‖ₑ ^ q)) :
    ∫ x in S.toSet, |(f : (Fin d → ℝ) → ℝ) x| ^ q ≤
      C * (S.vol / Q.vol) * ∫ x in Q.toSet, |(f : (Fin d → ℝ) → ℝ) x| ^ q := by
  have hV := Q.vol_pos
  have hS := S.vol_pos
  have hmeas : ∀ s : Set (Fin d → ℝ), AEStronglyMeasurable (fun x => |(f : (Fin d → ℝ) → ℝ) x| ^ q)
      (volume.restrict s) := fun s =>
    (TestFun.integrable_abs_rpow f hq).aestronglyMeasurable.restrict
  have heq : ∀ s : Set (Fin d → ℝ), ∫⁻ x in s, ENNReal.ofReal (|(f : (Fin d → ℝ) → ℝ) x| ^ q) =
      ∫⁻ x in s, ‖(f : (Fin d → ℝ) → ℝ) x‖ₑ ^ q := fun s =>
    lintegral_congr fun x => by
      rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hq.le]
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun x => by positivity)
    (hmeas S.toSet), integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun x => by positivity) (hmeas Q.toSet), heq, heq]
  have hQt : ∫⁻ x in Q.toSet, ‖(f : (Fin d → ℝ) → ℝ) x‖ₑ ^ q ≠ ⊤ :=
    TestFun.setLIntegral_enorm_rpow_ne_top f hq _
  rw [← ENNReal.toReal_ofReal (by positivity : 0 ≤ C * (S.vol / Q.vol)), ← ENNReal.toReal_mul]
  refine ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hQt) ?_
  have hS0 : volume S.toSet ≠ 0 := by
    rw [S.volume_toSet]
    exact (ENNReal.ofReal_pos.mpr hS).ne'
  have hSt : volume S.toSet ≠ ⊤ := by
    rw [S.volume_toSet]
    exact ENNReal.ofReal_ne_top
  calc ∫⁻ x in S.toSet, ‖(f : (Fin d → ℝ) → ℝ) x‖ₑ ^ q
      = volume S.toSet * ((volume S.toSet)⁻¹ * ∫⁻ x in S.toSet, ‖(f : (Fin d → ℝ) → ℝ) x‖ₑ ^ q) :=
        by
        rw [← mul_assoc, ENNReal.mul_inv_cancel hS0 hSt, one_mul]
    _ ≤ volume S.toSet * (ENNReal.ofReal C *
          ((volume Q.toSet)⁻¹ * ∫⁻ x in Q.toSet, ‖(f : (Fin d → ℝ) → ℝ) x‖ₑ ^ q)) :=
        mul_le_mul' le_rfl h
    _ = ENNReal.ofReal (C * (S.vol / Q.vol)) *
          ∫⁻ x in Q.toSet, ‖(f : (Fin d → ℝ) → ℝ) x‖ₑ ^ q := by
        rw [S.volume_toSet, Q.volume_toSet, ← ENNReal.ofReal_inv_of_pos hV, ← mul_assoc,
          ← mul_assoc, ← ENNReal.ofReal_mul hS.le, ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        rw [div_eq_mul_inv]
        ring

/-- `∫_P |f|^q = ∫_P |f 𝟙_S|^q` for `P ⊆ S`. [PROVED] -/
theorem TestFun.setIntegral_rpow_truncateₗ_eq {P S : DyadicCube d} (h : P.toSet ⊆ S.toSet)
    (f : TestFun d) (q : ℝ) :
    ∫ x in P.toSet, |(TestFun.truncateₗ S f : (Fin d → ℝ) → ℝ) x| ^ q =
      ∫ x in P.toSet, |(f : (Fin d → ℝ) → ℝ) x| ^ q := by
  refine setIntegral_congr_fun P.measurableSet_toSet fun x hx => ?_
  simp only [TestFun.coe_truncateₗ, truncate, Set.indicator_of_mem (h hx)]

/-- `f` is constant on the cube `T`. -/
def ConstOn (f : (Fin d → ℝ) → ℝ) (T : DyadicCube d) : Prop :=
  ∀ x ∈ T.toSet, ∀ y ∈ T.toSet, f x = f y

/-- `𝟙_C` is constant on `P` when `P ⊆ C` or `P ∩ C = ∅`. [PROVED] -/
theorem constOn_ind {P C : DyadicCube d} (h : P.toSet ⊆ C.toSet ∨ Disjoint P.toSet C.toSet) :
    ConstOn ((TestFun.ind C : TestFun d) : (Fin d → ℝ) → ℝ) P := fun x hx y hy => by
  rw [TestFun.coe_ind]
  rcases h with h | h
  · rw [Set.indicator_of_mem (h hx), Set.indicator_of_mem (h hy), Pi.one_apply, Pi.one_apply]
  · rw [Set.indicator_of_notMem (Set.disjoint_left.mp h hx),
      Set.indicator_of_notMem (Set.disjoint_left.mp h hy)]

/-- `f 𝟙_C` is constant on `P` when `f` is and `P ⊆ C` or `P ∩ C = ∅`. [PROVED] -/
theorem constOn_truncateₗ {f : TestFun d} {P C : DyadicCube d}
    (h : P.toSet ⊆ C.toSet ∨ Disjoint P.toSet C.toSet) (hf : ConstOn f P) :
    ConstOn ((TestFun.truncateₗ C f : TestFun d) : (Fin d → ℝ) → ℝ) P := fun x hx y hy => by
  rw [TestFun.coe_truncateₗ]
  rcases h with h | h
  · rw [truncate, Set.indicator_of_mem (h hx), Set.indicator_of_mem (h hy), hf x hx y hy]
  · rw [truncate, Set.indicator_of_notMem (Set.disjoint_left.mp h hx),
      Set.indicator_of_notMem (Set.disjoint_left.mp h hy)]

/-- The data of §2.2 (p. 40–41): the form `Λ`, the Hölder tuple, the constant `B`, the cube `Q`,
the slot `a` of `h` (the `k`-th entry) and the slot `b` of `u` (the `(k+1)`-st entry), and the
frozen entries `g`: `g_j = f_j 𝟙_Q` for `j ≠ a, b` and `g_b = u = b_{σ,𝐐,k+1}` (the entry `g_a` is
irrelevant). The hypotheses are: all entries are supported on `Q`; the mean and norm conditions
(1.6), (1.7) for `u`; `F = ∏_{j ≠ a,b} ‖f_j 𝟙_Q‖_{p_j} > 0`; and the testing condition (1.9) in
the form `|Λ_Q(ρ, u)| ≤ B F ‖u‖_q ‖ρ‖_r` for all `ρ` supported on `Q`. -/
structure StoppingData (d n : ℕ) where
  /-- the perfect Calderón–Zygmund form -/
  T : PerfectCZForm d n
  /-- the Hölder tuple -/
  p : HolderTuple n
  /-- the constant `B ≥ 1` -/
  B : ℝ
  /-- the cube `Q` -/
  Q : DyadicCube d
  /-- `d ≥ 1` -/
  hd : d ≠ 0
  /-- the truncation scale: only subcubes of `Q` of side length at least `2^{-N} ℓ(Q)` are
  considered (the paper's collection `X`, p. 51 and p. 56) -/
  N : ℕ
  /-- the slot of `h` -/
  a : Fin n
  /-- the slot of `u` -/
  b : Fin n
  hab : a ≠ b
  /-- the frozen entries -/
  g : Fin n → TestFun d
  /-- the extremal function `g = f_{k+1}` of (2.2) (in the slot `b`) -/
  G : TestFun d
  hB : 1 ≤ B
  supp : ∀ j, SupportedOn (g j) Q
  Gsupp : SupportedOn G Q
  /-- `‖g‖_q > 0` (otherwise the estimate (2.2) is trivial) -/
  Gpos : 0 < lpNorm (G : (Fin d → ℝ) → ℝ) (p.p b)
  mean : ∫ x, (g b : (Fin d → ℝ) → ℝ) x = Q.vol
  norm : ∫ x, |(g b : (Fin d → ℝ) → ℝ) x| ^ p.p b ≤ B * Q.vol
  Fpos : 0 < ∏ j ∈ (Finset.univ.erase a).erase b, lpNorm (g j : (Fin d → ℝ) → ℝ) (p.p j)
  testing : ∀ ρ : TestFun d, SupportedOn ρ Q → |slotForm T a g Q ρ| ≤
    B * (∏ j ∈ (Finset.univ.erase a).erase b, lpNorm (g j : (Fin d → ℝ) → ℝ) (p.p j)) *
      lpNorm (g b : (Fin d → ℝ) → ℝ) (p.p b) * lpNorm (ρ : (Fin d → ℝ) → ℝ) (p.p a)
  /-- the testing functions `b_{σ,𝐐_P,k+1}` for the chains `𝐐_P` (p. 43), one for each `P ⊆ Q` -/
  bP : DyadicCube d → TestFun d
  /-- the testing functions `b_{τ,𝐐_P,k}` of the path `τ` for the chains `𝐐_P` (p. 44) -/
  vP : DyadicCube d → TestFun d
  /-- the constant `A` of (2.1) -/
  A : ℝ
  hA0 : 0 ≤ A
  bP_supp : ∀ P : DyadicCube d, P.toSet ⊆ Q.toSet → SupportedOn (bP P) P
  bP_mean : ∀ P : DyadicCube d, P.toSet ⊆ Q.toSet → ∫ x, (bP P : (Fin d → ℝ) → ℝ) x = P.vol
  bP_norm : ∀ P : DyadicCube d, P.toSet ⊆ Q.toSet →
    ∫ x, |(bP P : (Fin d → ℝ) → ℝ) x| ^ p.p b ≤ B * P.vol
  vP_supp : ∀ P : DyadicCube d, P.toSet ⊆ Q.toSet → SupportedOn (vP P) P
  vP_mean : ∀ P : DyadicCube d, P.toSet ⊆ Q.toSet → ∫ x, (vP P : (Fin d → ℝ) → ℝ) x = P.vol
  vP_norm : ∀ P : DyadicCube d, P.toSet ⊆ Q.toSet →
    ∫ x, |(vP P : (Fin d → ℝ) → ℝ) x| ^ p.p a ≤ B * P.vol
  /-- the testing condition (1.9) for `σ` and the chain `𝐐_P`: `|Λ_P(ρ, b_{σ,𝐐_P,k+1})| ≤
  B F_P ‖b_{σ,𝐐_P,k+1}‖_q ‖ρ‖_r`, with `F_P = ∏_{j ≠ k,k+1} ‖f_j 𝟙_P‖_{p_j}` -/
  testing_bP : ∀ P : DyadicCube d, P.toSet ⊆ Q.toSet → ∀ ρ : TestFun d, SupportedOn ρ P →
    |twoSlotForm T a b g P ρ (bP P)| ≤
      B * (∏ j ∈ (Finset.univ.erase a).erase b,
          lpNorm (TestFun.truncateₗ P (g j) : (Fin d → ℝ) → ℝ) (p.p j)) *
        lpNorm (bP P : (Fin d → ℝ) → ℝ) (p.p b) * lpNorm (ρ : (Fin d → ℝ) → ℝ) (p.p a)
  /-- the testing condition (1.9) for `τ` and the chain `𝐐_P`: `|Λ_P(b_{τ,𝐐_P,k}, ρ)| ≤
  B F_P ‖b_{τ,𝐐_P,k}‖_r ‖ρ‖_q` -/
  testing_vP : ∀ P : DyadicCube d, P.toSet ⊆ Q.toSet → ∀ ρ : TestFun d, SupportedOn ρ P →
    |twoSlotForm T a b g P (vP P) ρ| ≤
      B * (∏ j ∈ (Finset.univ.erase a).erase b,
          lpNorm (TestFun.truncateₗ P (g j) : (Fin d → ℝ) → ℝ) (p.p j)) *
        lpNorm (vP P : (Fin d → ℝ) → ℝ) (p.p a) * lpNorm (ρ : (Fin d → ℝ) → ℝ) (p.p b)
  /-- the estimate (2.1) with the constant `A` for the data `σ'`, `𝐐_P`:
  `|Λ_P(𝟙_P, ρ)| ≤ A F_P |P|^{1/r} ‖ρ‖_q` -/
  estimateA : ∀ P : DyadicCube d, P.toSet ⊆ Q.toSet → ∀ ρ : TestFun d, SupportedOn ρ P →
    |twoSlotForm T a b g P (TestFun.ind P) ρ| ≤
      A * (∏ j ∈ (Finset.univ.erase a).erase b,
          lpNorm (TestFun.truncateₗ P (g j) : (Fin d → ℝ) → ℝ) (p.p j)) *
        P.vol ^ (1 / p.p a) * lpNorm (ρ : (Fin d → ℝ) → ℝ) (p.p b)
  /-- the number of auxiliary functions with Chebyshev-type stopping conditions (none for the
  first stopping time of §2.2; `𝔤_R` and `u_R`, (2.25) and (2.27), for the second stopping time
  of §2.4) -/
  m : ℕ
  /-- the auxiliary functions -/
  aux : Fin m → TestFun d
  /-- their exponents -/
  auxExp : Fin m → ℝ
  aux_pos : ∀ i, 0 < auxExp i
  aux_supp : ∀ i, SupportedOn (aux i) Q
  /-- the function in the slot `a` of the extra `𝐏₃`-type stopping condition (zero for the first
  stopping time; `u_R`, (2.29), for the second) -/
  w : TestFun d
  /-- its testing-type constant -/
  K : ℝ
  hK : 0 < K
  /-- the testing-type bound for `w`: `|Λ_Q(w, ρ)| ≤ K ‖ρ‖_q` for mean-zero `ρ` supported on `Q`
  -/
  w_test : ∀ ρ : TestFun d, SupportedOn ρ Q → MeanZero (ρ : (Fin d → ℝ) → ℝ) →
    |twoSlotForm T a b g Q w ρ| ≤ K * lpNorm (ρ : (Fin d → ℝ) → ℝ) (p.p b)
  /-- the frozen entries are constant on the leaves of the tree `𝒟_N(Q)`, the cubes `T ⊆ Q` of
  side length `2^{-N} ℓ(Q)` ("without loss of generality", p. 51 and p. 56: all functions are
  constant on the cubes of the finest scale) -/
  g_const : ∀ j, ∀ T : DyadicCube d, T.toSet ⊆ Q.toSet → T.m = Q.m - N → ConstOn (g j) T
  /-- the extremal function `g` is constant on the leaves -/
  G_const : ∀ T : DyadicCube d, T.toSet ⊆ Q.toSet → T.m = Q.m - N → ConstOn G T
  /-- the testing functions `b_{σ,𝐐_P,k+1}` for the cubes `P` of the tree `𝒟_N(Q)` are constant
  on the leaves -/
  bP_const : ∀ P : DyadicCube d, P.toSet ⊆ Q.toSet → Q.m - N ≤ P.m →
    ∀ T : DyadicCube d, T.toSet ⊆ Q.toSet → T.m = Q.m - N → ConstOn (bP P) T
  /-- the testing functions `b_{τ,𝐐_P,k}` for the cubes `P` of the tree `𝒟_N(Q)` are constant on
  the leaves -/
  vP_const : ∀ P : DyadicCube d, P.toSet ⊆ Q.toSet → Q.m - N ≤ P.m →
    ∀ T : DyadicCube d, T.toSet ⊆ Q.toSet → T.m = Q.m - N → ConstOn (vP P) T

namespace StoppingData

variable (D : StoppingData d n)

/-- The finite tree `𝒟_N(Q)` of the dyadic subcubes of `Q` of side length at least
`2^{-N} ℓ(Q)` (the paper's collection `X`). -/
def tree : Set (DyadicCube d) := {P | P.toSet ⊆ D.Q.toSet ∧ D.Q.m - D.N ≤ P.m}

theorem tree_subset : D.tree ⊆ D.Q.tree := fun _ h => h.1

theorem maximal_sep_subset (X : DyadicCube d → Prop) :
    maximal {P ∈ D.tree | X P} ⊆ D.Q.tree := fun _ h => h.1.1.1

theorem Q_mem_tree : D.Q ∈ D.tree := ⟨subset_rfl, by omega⟩

/-- The tree `𝒟_N(Q)` is finite: a cube `P ⊆ Q` with `ℓ(P) ≥ 2^{-N} ℓ(Q)` has scale in
`[m_Q - N, m_Q]` and position bounded by `2^N (|l_Q| + 1)`. [PROVED] -/
theorem tree_finite : D.tree.Finite := by
  have hd := D.hd
  set R : Fin d → ℤ := fun i => 2 ^ D.N * (|D.Q.l i| + 1) with hR
  refine Set.Finite.subset ((Finset.finite_toSet (Finset.Icc (D.Q.m - D.N) D.Q.m ×ˢ
    Fintype.piFinset fun i => Finset.Icc (-R i) (R i))).image
      fun q : ℤ × (Fin d → ℤ) => (⟨q.1, q.2⟩ : DyadicCube d)) ?_
  intro P hP
  obtain ⟨hPQ, hm⟩ := hP
  have hmQ : P.m ≤ D.Q.m := DyadicCube.m_le_of_subset hd hPQ
  refine ⟨(P.m, P.l), ?_, rfl⟩
  rw [Finset.mem_coe, Finset.mem_product, Finset.mem_Icc, Fintype.mem_piFinset]
  refine ⟨⟨hm, hmQ⟩, fun i => ?_⟩
  rw [Finset.mem_Icc]
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (k : ℤ) = D.Q.m - P.m := ⟨(D.Q.m - P.m).toNat,
    Int.toNat_of_nonneg (by omega)⟩
  have hkN : k ≤ D.N := by omega
  have hc := hPQ P.corner_mem
  rw [DyadicCube.mem_toSet_iff] at hc
  have h2P : (0 : ℝ) < 2 ^ P.m := zpow_pos (by norm_num) _
  have hpow : (2 : ℝ) ^ D.Q.m = 2 ^ P.m * ((2 ^ k : ℕ) : ℝ) := by
    rw [Nat.cast_pow, Nat.cast_ofNat, ← zpow_natCast, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), hk]
    congr 1
    ring
  have hfl : ⌊((2 : ℝ) ^ P.m * P.l i) / 2 ^ D.Q.m⌋ = D.Q.l i := hc i
  rw [hpow, mul_div_mul_left _ _ h2P.ne', Int.floor_div_natCast, Int.floor_intCast] at hfl
  have h2k : (0 : ℤ) < ((2 ^ k : ℕ) : ℤ) := by positivity
  have hlo : ((2 ^ k : ℕ) : ℤ) * D.Q.l i ≤ P.l i := by
    have := Int.ediv_mul_le (P.l i) h2k.ne'
    rw [hfl] at this
    linarith
  have hhi : P.l i < ((2 ^ k : ℕ) : ℤ) * (D.Q.l i + 1) := by
    have := Int.lt_ediv_add_one_mul_self (P.l i) h2k
    rw [hfl] at this
    linarith
  have hk2 : ((2 ^ k : ℕ) : ℤ) ≤ 2 ^ D.N := by
    exact_mod_cast Nat.pow_le_pow_right (by norm_num) hkN
  have hpos : (0 : ℤ) ≤ ((2 ^ k : ℕ) : ℤ) := h2k.le
  have hA : ((2 ^ k : ℕ) : ℤ) * (-|D.Q.l i|) ≤ ((2 ^ k : ℕ) : ℤ) * D.Q.l i :=
    mul_le_mul_of_nonneg_left (neg_abs_le _) hpos
  have hB : ((2 ^ k : ℕ) : ℤ) * |D.Q.l i| ≤ 2 ^ D.N * |D.Q.l i| :=
    mul_le_mul_of_nonneg_right hk2 (abs_nonneg _)
  have hC : ((2 ^ k : ℕ) : ℤ) * (D.Q.l i + 1) ≤ ((2 ^ k : ℕ) : ℤ) * (|D.Q.l i| + 1) :=
    mul_le_mul_of_nonneg_left (by linarith [le_abs_self (D.Q.l i)]) hpos
  have hD : ((2 ^ k : ℕ) : ℤ) * (|D.Q.l i| + 1) ≤ 2 ^ D.N * (|D.Q.l i| + 1) :=
    mul_le_mul_of_nonneg_right hk2 (by linarith [abs_nonneg (D.Q.l i)])
  constructor
  · simp only [hR]
    linarith
  · simp only [hR]
    linarith

/-- The index set `{j : j ≠ k, k+1}`. -/
abbrev J : Finset (Fin n) := (Finset.univ.erase D.a).erase D.b

/-- `F = ∏_{j ≠ k, k+1} ‖f_j 𝟙_Q‖_{p_j}`. -/
noncomputable def F : ℝ := ∏ j ∈ D.J, lpNorm (D.g j : (Fin d → ℝ) → ℝ) (D.p.p j)

/-- The testing function `u`. -/
abbrev u : TestFun d := D.g D.b

/-- The exponent `r = p_k`. -/
abbrev r : ℝ := D.p.p D.a

/-- The exponent `q = p_{k+1}`. -/
abbrev q : ℝ := D.p.p D.b

/-- `ε = (1/8) min_j (7/8)^{p_j/(p_j-1)} B^{-1/(p_j-1)}` (p. 41). -/
noncomputable def ε : ℝ :=
  (1 / 8) * Finset.univ.inf' (⟨D.a, Finset.mem_univ _⟩ : (Finset.univ : Finset (Fin n)).Nonempty)
    (fun j => (7 / 8 : ℝ) ^ (D.p.p j / (D.p.p j - 1)) * D.B ^ (-(1 / (D.p.p j - 1))))

theorem hr : 1 < D.r := D.p.one_lt D.a

theorem hq : 1 < D.q := D.p.one_lt D.b

include D in
theorem n_pos : 0 < n := Fin.pos D.a

theorem Fpos' : 0 < D.F := D.Fpos

/-- `ε > 0`. [PROVED] -/
theorem ε_pos : 0 < D.ε := by
  unfold ε
  apply mul_pos (by norm_num)
  exact (Finset.lt_inf'_iff _).mpr fun j _ => (eps_factor_bounds D.p D.hB j).1

/-- `ε ≤ 1/8`. [PROVED] -/
theorem ε_le : D.ε ≤ 1 / 8 := by
  unfold ε
  have h := Finset.inf'_le (fun j : Fin n =>
    (7 / 8 : ℝ) ^ (D.p.p j / (D.p.p j - 1)) * D.B ^ (-(1 / (D.p.p j - 1)))) (Finset.mem_univ D.a)
  have h2 := (eps_factor_bounds D.p D.hB D.a).2
  linarith

/-- `8ε ≤ (7/8)^{q/(q-1)} B^{-1/(q-1)}`, the bound used for `𝐏₄`. [PROVED] -/
theorem eight_ε_le : 8 * D.ε ≤ (7 / 8 : ℝ) ^ (D.q / (D.q - 1)) * D.B ^ (-(1 / (D.q - 1))) := by
  unfold ε
  have h := Finset.inf'_le (fun j : Fin n =>
    (7 / 8 : ℝ) ^ (D.p.p j / (D.p.p j - 1)) * D.B ^ (-(1 / (D.p.p j - 1)))) (Finset.mem_univ D.b)
  linarith

/-- `∫_Q |g_j|^{p_j} = ‖g_j‖_{p_j}^{p_j}` (as lintegrals; the entries are supported on `Q`).
[PROVED] -/
theorem setLIntegral_eq (j : Fin n) :
    ∫⁻ x in D.Q.toSet, ‖(D.g j : (Fin d → ℝ) → ℝ) x‖ₑ ^ D.p.p j =
      eLpNorm (D.g j : (Fin d → ℝ) → ℝ) (ENNReal.ofReal (D.p.p j)) volume ^ D.p.p j := by
  have hp : 0 < D.p.p j := by linarith [D.p.one_lt j]
  rw [eLpNorm_eq_eLpNorm' (ENNReal.ofReal_pos.mpr hp).ne' ENNReal.ofReal_ne_top
      (TestFun.memLp (D.g j).2 1).aestronglyMeasurable,
    eLpNorm'_eq_lintegral_enorm, ENNReal.toReal_ofReal hp.le, one_div,
    ENNReal.rpow_inv_rpow hp.ne']
  have hsupp : Function.support (fun x => ‖(D.g j : (Fin d → ℝ) → ℝ) x‖ₑ ^ D.p.p j) ⊆
      D.Q.toSet := by
    intro x hx
    by_contra hxQ
    apply hx
    simp [D.supp j x hxQ, ENNReal.zero_rpow_of_pos hp]
  exact setLIntegral_eq_of_support_subset hsupp

theorem lintegral_ne_top (j : Fin n) :
    ∫⁻ x in D.Q.toSet, ‖(D.g j : (Fin d → ℝ) → ℝ) x‖ₑ ^ D.p.p j ≠ ⊤ := by
  rw [D.setLIntegral_eq j]
  exact ENNReal.rpow_ne_top_of_nonneg (by linarith [D.p.one_lt j])
    (TestFun.memLp (D.g j).2 _).eLpNorm_ne_top

theorem lintegral_ne_zero_of_pos {j : Fin n}
    (h : 0 < lpNorm (D.g j : (Fin d → ℝ) → ℝ) (D.p.p j)) :
    ∫⁻ x in D.Q.toSet, ‖(D.g j : (Fin d → ℝ) → ℝ) x‖ₑ ^ D.p.p j ≠ 0 := by
  rw [D.setLIntegral_eq j]
  have hne : eLpNorm (D.g j : (Fin d → ℝ) → ℝ) (ENNReal.ofReal (D.p.p j)) volume ≠ 0 := by
    intro h0
    rw [lpNorm, h0, ENNReal.toReal_zero] at h
    exact lt_irrefl _ h
  exact (ENNReal.rpow_pos (pos_iff_ne_zero.mpr hne)
    (TestFun.memLp (D.g j).2 _).eLpNorm_ne_top).ne'

/-- `‖u‖_q > 0`, from the mean condition `∫ u = |Q|` and Hölder's inequality. [PROVED] -/
theorem lpNorm_u_pos : 0 < lpNorm (D.u : (Fin d → ℝ) → ℝ) D.q := by
  have hq := D.hq
  have hmem : MemLp (D.u : (Fin d → ℝ) → ℝ) (ENNReal.ofReal D.q) volume :=
    TestFun.memLp D.u.2 _
  have hH := abs_setIntegral_le_rpow_mul_lpNorm hq.le hmem D.Q.measurableSet_toSet
    (by rw [D.Q.volume_toSet]; exact ENNReal.ofReal_ne_top)
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => D.supp D.b x hx), D.mean,
    abs_of_pos D.Q.vol_pos] at hH
  by_contra hle
  rw [not_lt] at hle
  have h0 : lpNorm (D.u : (Fin d → ℝ) → ℝ) D.q = 0 := le_antisymm hle ENNReal.toReal_nonneg
  rw [h0, mul_zero] at hH
  exact absurd hH (not_le.mpr D.Q.vol_pos)

/-- `𝐏₁` (2.3): the maximal `P ⊆ Q` with
`|P|^{-1} ‖f_j 𝟙_P‖_{p_j}^{p_j} ≥ n ε^{-1} |Q|^{-1} ‖f_j‖_{p_j}^{p_j}` for some `j ≠ k, k+1`
(the norms written as lintegrals). -/
def P1 : Set (DyadicCube d) := maximal {P ∈ D.tree | (∃ j ∈ D.J,
  ENNReal.ofReal ((n + D.m) / (D.ε * D.Q.vol)) *
      ∫⁻ x in D.Q.toSet, ‖(D.g j : (Fin d → ℝ) → ℝ) x‖ₑ ^ D.p.p j ≤
    (volume P.toSet)⁻¹ * ∫⁻ x in P.toSet, ‖(D.g j : (Fin d → ℝ) → ℝ) x‖ₑ ^ D.p.p j) ∨
  (∃ i : Fin D.m, ∫⁻ x in D.Q.toSet, ‖(D.aux i : (Fin d → ℝ) → ℝ) x‖ₑ ^ D.auxExp i ≠ 0 ∧
  ENNReal.ofReal ((n + D.m) / (D.ε * D.Q.vol)) *
      ∫⁻ x in D.Q.toSet, ‖(D.aux i : (Fin d → ℝ) → ℝ) x‖ₑ ^ D.auxExp i ≤
    (volume P.toSet)⁻¹ * ∫⁻ x in P.toSet, ‖(D.aux i : (Fin d → ℝ) → ℝ) x‖ₑ ^ D.auxExp i)}

/-- `𝐏₂` (2.4): the maximal `P ⊆ Q` with `|P|^{-1} ‖u_P‖_q^q ≥ ε^{-1} |Q|^{-1} ‖u‖_q^q`. -/
def P2 : Set (DyadicCube d) := maximal {P ∈ D.tree |
  ENNReal.ofReal (1 / (D.ε * D.Q.vol)) *
      ∫⁻ x in D.Q.toSet, ‖(D.u : (Fin d → ℝ) → ℝ) x‖ₑ ^ D.q ≤
    (volume P.toSet)⁻¹ * ∫⁻ x in P.toSet, ‖(D.u : (Fin d → ℝ) → ℝ) x‖ₑ ^ D.q}

/-- `𝐏₃` (2.5): the maximal `P ⊆ Q` for which there is a nonzero mean-zero `ρ` supported on `P`
with `|Λ_P(ρ, u)| ≥ B F ε^{-1} (|P|/|Q|)^{1-1/r} ‖ρ‖_r ‖u‖_q`. -/
def P3 : Set (DyadicCube d) := maximal {P ∈ D.tree | (∃ ρ : TestFun d,
  SupportedOn ρ P ∧ MeanZero (ρ : (Fin d → ℝ) → ℝ) ∧ 0 < lpNorm (ρ : (Fin d → ℝ) → ℝ) D.r ∧
  D.B * D.F * lpNorm (D.u : (Fin d → ℝ) → ℝ) D.q * D.ε⁻¹ * (P.vol / D.Q.vol) ^ (1 - 1 / D.r) *
      lpNorm (ρ : (Fin d → ℝ) → ℝ) D.r ≤ |slotForm D.T D.a D.g P ρ|) ∨
  (∃ ρ : TestFun d,
  SupportedOn ρ P ∧ MeanZero (ρ : (Fin d → ℝ) → ℝ) ∧ 0 < lpNorm (ρ : (Fin d → ℝ) → ℝ) D.q ∧
  D.K * D.ε⁻¹ * (P.vol / D.Q.vol) ^ (1 - 1 / D.q) * lpNorm (ρ : (Fin d → ℝ) → ℝ) D.q ≤
    |twoSlotForm D.T D.a D.b D.g P D.w ρ|)}

/-- `𝐏₄` (2.6): the maximal `P ⊆ Q` with `|[u]_P| ≤ 1/8`. -/
def P4 : Set (DyadicCube d) := maximal {P ∈ D.tree | |avg P D.u| ≤ 1 / 8}

/-- `𝐏₅`: the maximal `P ⊆ Q` contained in at least `2^d ε^{-1}` dyadic cubes which are parents
of cubes of `𝐏₄`. -/
def P5 : Set (DyadicCube d) := maximal {P ∈ D.tree | ∃ S : Finset (DyadicCube d),
  (2 : ℝ) ^ d / D.ε ≤ S.card ∧ ∀ R ∈ S, (∃ P' ∈ D.P4, R = P'.parent) ∧ P.toSet ⊆ R.toSet}

/-- The stopping cubes `𝐏`: the maximal cubes of `𝐏₁ ∪ ⋯ ∪ 𝐏₅`. -/
def stoppingCubes : Set (DyadicCube d) := maximal (D.P1 ∪ D.P2 ∪ D.P3 ∪ D.P4 ∪ D.P5)

/-- `∑_{𝐏₁} |P| ≤ ε|Q|` (p. 41). [PROVED] -/
theorem volume_P1_le : volume (⋃ P ∈ D.P1, P.toSet) ≤ ENNReal.ofReal (D.ε * D.Q.vol) := by
  classical
  have hε := D.ε_pos
  have hV := D.Q.vol_pos
  have hn : (0 : ℝ) < n := by exact_mod_cast D.n_pos
  have hnm : (0 : ℝ) < n + D.m := by positivity
  have hc : 0 < ((n : ℝ) + D.m) / (D.ε * D.Q.vol) := by positivity
  have hFj : ∀ j ∈ D.J, 0 < lpNorm (D.g j : (Fin d → ℝ) → ℝ) (D.p.p j) := by
    intro j hj
    have hne : lpNorm (D.g j : (Fin d → ℝ) → ℝ) (D.p.p j) ≠ 0 :=
      Finset.prod_ne_zero_iff.mp D.Fpos.ne' j hj
    exact lt_of_le_of_ne ENNReal.toReal_nonneg hne.symm
  -- the index set: `J` and the auxiliary functions with nonzero integral
  set I : Finset (Fin D.m) := Finset.univ.filter fun i =>
    ∫⁻ x in D.Q.toSet, ‖(D.aux i : (Fin d → ℝ) → ℝ) x‖ₑ ^ D.auxExp i ≠ 0 with hI
  set idx : Finset (Fin n ⊕ Fin D.m) :=
    D.J.map Function.Embedding.inl ∪ I.map Function.Embedding.inr with hidx
  have hcard : (idx.card : ℝ) ≤ n + D.m := by
    have h1 : idx.card ≤ (D.J.map Function.Embedding.inl).card +
        (I.map Function.Embedding.inr).card := Finset.card_union_le _ _
    rw [Finset.card_map, Finset.card_map] at h1
    have h2 : D.J.card ≤ n := (Finset.card_le_univ _).trans_eq (Fintype.card_fin n)
    have h3 : I.card ≤ D.m := (Finset.card_le_univ _).trans_eq (Fintype.card_fin D.m)
    exact_mod_cast h1.trans (add_le_add h2 h3)
  set F : Fin n ⊕ Fin D.m → (Fin d → ℝ) → ENNReal := Sum.elim
    (fun j x => ‖(D.g j : (Fin d → ℝ) → ℝ) x‖ₑ ^ D.p.p j)
    (fun i x => ‖(D.aux i : (Fin d → ℝ) → ℝ) x‖ₑ ^ D.auxExp i) with hF
  have hF0 : ∀ k ∈ idx, ∫⁻ x in D.Q.toSet, F k x ≠ 0 := by
    intro k hk
    rw [hidx, Finset.mem_union, Finset.mem_map, Finset.mem_map] at hk
    rcases hk with ⟨j, hj, rfl⟩ | ⟨i, hi, rfl⟩
    · exact D.lintegral_ne_zero_of_pos (hFj j hj)
    · exact (Finset.mem_filter.mp hi).2
  have hFt : ∀ k ∈ idx, ∫⁻ x in D.Q.toSet, F k x ≠ ⊤ := by
    intro k _
    rcases k with j | i
    · exact D.lintegral_ne_top j
    · exact TestFun.setLIntegral_enorm_rpow_ne_top (D.aux i) (D.aux_pos i) _
  refine (volume_biUnion_le_of_chebyshev (D.maximal_sep_subset _) (maximal_pairwiseDisjoint _)
    idx F hF0 hFt (a := ENNReal.ofReal (D.ε * D.Q.vol / (n + D.m))) ?_).trans ?_
  · intro P hP
    rcases prop_of_mem_maximal_sep hP with ⟨j, hj, h⟩ | ⟨i, hi, h⟩
    · refine ⟨Sum.inl j, ?_, ?_⟩
      · rw [hidx, Finset.mem_union, Finset.mem_map, Finset.mem_map]
        exact Or.inl ⟨j, hj, rfl⟩
      · have := chebyshev_condition P hc h
        rwa [inv_div] at this
    · refine ⟨Sum.inr i, ?_, ?_⟩
      · rw [hidx, Finset.mem_union, Finset.mem_map, Finset.mem_map]
        exact Or.inr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩, rfl⟩
      · have := chebyshev_condition P hc h
        rwa [inv_div] at this
  · calc ENNReal.ofReal (D.ε * D.Q.vol / (n + D.m)) * (idx.card : ENNReal)
        ≤ ENNReal.ofReal (D.ε * D.Q.vol / (n + D.m)) * ENNReal.ofReal (n + D.m) := by
          refine mul_le_mul' le_rfl ?_
          rw [← ENNReal.ofReal_natCast]
          exact ENNReal.ofReal_le_ofReal hcard
      _ = ENNReal.ofReal (D.ε * D.Q.vol) := by
          rw [← ENNReal.ofReal_mul (by positivity), div_mul_cancel₀ _ hnm.ne']

/-- `∑_{𝐏₂} |P| ≤ ε|Q|` (p. 42). [PROVED] -/
theorem volume_P2_le : volume (⋃ P ∈ D.P2, P.toSet) ≤ ENNReal.ofReal (D.ε * D.Q.vol) := by
  have hε := D.ε_pos
  have hV := D.Q.vol_pos
  have hc : 0 < 1 / (D.ε * D.Q.vol) := by positivity
  have hu := D.lpNorm_u_pos
  refine (volume_biUnion_le_of_chebyshev (D.maximal_sep_subset _)
    (maximal_pairwiseDisjoint _) {D.b} (fun _ x => ‖(D.u : (Fin d → ℝ) → ℝ) x‖ₑ ^ D.q)
    (fun _ _ => D.lintegral_ne_zero_of_pos hu) (fun _ _ => D.lintegral_ne_top D.b)
    (a := ENNReal.ofReal (D.ε * D.Q.vol)) ?_).trans ?_
  · intro P hP
    refine ⟨D.b, Finset.mem_singleton_self _, ?_⟩
    have := chebyshev_condition P hc (prop_of_mem_maximal_sep hP)
    rwa [inv_div, div_one] at this
  · rw [Finset.card_singleton, Nat.cast_one, mul_one]

/-- `∑_{𝐏₃} |P| ≤ ε|Q|` (p. 42). [PROVED] -/
theorem volume_P3_le : volume (⋃ P ∈ D.P3, P.toSet) ≤ ENNReal.ofReal (2 * D.ε * D.Q.vol) := by
  have hK : 0 < D.B * D.F * lpNorm (D.u : (Fin d → ℝ) → ℝ) D.q :=
    mul_pos (mul_pos (by linarith [D.hB]) D.Fpos') D.lpNorm_u_pos
  have hV := D.Q.vol_pos
  have hε := D.ε_pos
  set C₁ : DyadicCube d → Prop := fun P => ∃ ρ : TestFun d,
    SupportedOn ρ P ∧ MeanZero (ρ : (Fin d → ℝ) → ℝ) ∧ 0 < lpNorm (ρ : (Fin d → ℝ) → ℝ) D.r ∧
    D.B * D.F * lpNorm (D.u : (Fin d → ℝ) → ℝ) D.q * D.ε⁻¹ * (P.vol / D.Q.vol) ^ (1 - 1 / D.r) *
      lpNorm (ρ : (Fin d → ℝ) → ℝ) D.r ≤ |slotForm D.T D.a D.g P ρ| with hC₁
  set C₂ : DyadicCube d → Prop := fun P => ∃ ρ : TestFun d,
    SupportedOn ρ P ∧ MeanZero (ρ : (Fin d → ℝ) → ℝ) ∧ 0 < lpNorm (ρ : (Fin d → ℝ) → ℝ) D.q ∧
    D.K * D.ε⁻¹ * (P.vol / D.Q.vol) ^ (1 - 1 / D.q) * lpNorm (ρ : (Fin d → ℝ) → ℝ) D.q ≤
      |twoSlotForm D.T D.a D.b D.g P D.w ρ| with hC₂
  have hsub : D.P3 ⊆ {P ∈ D.P3 | C₁ P} ∪ {P ∈ D.P3 | C₂ P} := by
    intro P hP
    rcases prop_of_mem_maximal_sep hP with h | h
    · exact Or.inl ⟨hP, h⟩
    · exact Or.inr ⟨hP, h⟩
  have hsub₁ : {P ∈ D.P3 | C₁ P} ⊆ D.P3 := fun _ h => (Set.mem_sep_iff.mp h).1
  have hsub₂ : {P ∈ D.P3 | C₂ P} ⊆ D.P3 := fun _ h => (Set.mem_sep_iff.mp h).1
  have h1 : volume (⋃ P ∈ {P ∈ D.P3 | C₁ P}, P.toSet) ≤ ENNReal.ofReal (D.ε * D.Q.vol) :=
    volume_biUnion_le_of_P3 (Ps := {P ∈ D.P3 | C₁ P}) (hsub₁.trans (D.maximal_sep_subset _))
      ((maximal_pairwiseDisjoint _).subset hsub₁) D.T D.a D.g D.hr hε hK
      (fun ρ hρ _ => D.testing ρ hρ) fun _ hP => (Set.mem_sep_iff.mp hP).2
  have h2 : volume (⋃ P ∈ {P ∈ D.P3 | C₂ P}, P.toSet) ≤ ENNReal.ofReal (D.ε * D.Q.vol) := by
    refine volume_biUnion_le_of_P3 (Ps := {P ∈ D.P3 | C₂ P}) (hsub₂.trans (D.maximal_sep_subset _))
      ((maximal_pairwiseDisjoint _).subset hsub₂) D.T D.b (Function.update D.g D.a D.w)
      D.hq hε D.hK (fun ρ hρ hρ0 => ?_) fun P hP => ?_
    · rw [← twoSlotForm_eq_slotForm']
      exact D.w_test ρ hρ hρ0
    · obtain ⟨ρ, hs, h0, hpos, hL⟩ := (Set.mem_sep_iff.mp hP).2
      exact ⟨ρ, hs, h0, hpos, by rwa [← twoSlotForm_eq_slotForm']⟩
  calc volume (⋃ P ∈ D.P3, P.toSet)
      ≤ volume (⋃ P ∈ {P ∈ D.P3 | C₁ P} ∪ {P ∈ D.P3 | C₂ P}, P.toSet) :=
        measure_mono (Set.biUnion_subset_biUnion_left hsub)
    _ = volume ((⋃ P ∈ {P ∈ D.P3 | C₁ P}, P.toSet) ∪ ⋃ P ∈ {P ∈ D.P3 | C₂ P}, P.toSet) := by
        rw [Set.biUnion_union]
    _ ≤ volume (⋃ P ∈ {P ∈ D.P3 | C₁ P}, P.toSet) +
          volume (⋃ P ∈ {P ∈ D.P3 | C₂ P}, P.toSet) := measure_union_le _ _
    _ ≤ ENNReal.ofReal (D.ε * D.Q.vol) + ENNReal.ofReal (D.ε * D.Q.vol) := add_le_add h1 h2
    _ = ENNReal.ofReal (2 * D.ε * D.Q.vol) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

/-- `∑_{𝐏₄} |P| ≤ (1 - 8ε)|Q|` (p. 42). [PROVED] -/
theorem volume_P4_le :
    volume (⋃ P ∈ D.P4, P.toSet) ≤ ENNReal.ofReal ((1 - 8 * D.ε) * D.Q.vol) :=
  volume_biUnion_le_of_small_avg (D.maximal_sep_subset _) (maximal_pairwiseDisjoint _)
    D.hq D.hB D.eight_ε_le (TestFun.memLp D.u.2 _) (D.supp D.b) D.mean D.norm
    fun _ hP => prop_of_mem_maximal_sep hP

/-- `∑_{𝐏₅} |P| ≤ ε|Q|` (p. 42). [PROVED] -/
theorem volume_P5_le : volume (⋃ P ∈ D.P5, P.toSet) ≤ ENNReal.ofReal (D.ε * D.Q.vol) := by
  have hε := D.ε_pos
  have hε0 := hε.ne'
  have h2 : (0 : ℝ) < 2 ^ d := by positivity
  have h20 := h2.ne'
  have h := volume_biUnion_le_of_overlap (Ps₄ := D.P4) (Ps₅ := D.P5)
    (maximal_pairwiseDisjoint _) (M := (2 : ℝ) ^ d / D.ε)
    fun _ hP => prop_of_mem_maximal_sep hP
  have hQ : volume (⋃ P ∈ D.P4, P.toSet) ≤ ENNReal.ofReal D.Q.vol := by
    rw [← D.Q.volume_toSet]
    exact measure_mono (biUnion_toSet_subset (D.maximal_sep_subset _))
  have h2' : (2 : ENNReal) ^ d = ENNReal.ofReal (2 ^ d) := by
    rw [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
  have e : D.ε / 2 ^ d * (2 ^ d / D.ε) = 1 := by field_simp
  calc volume (⋃ P ∈ D.P5, P.toSet)
      = ENNReal.ofReal (D.ε / 2 ^ d) *
          (ENNReal.ofReal (2 ^ d / D.ε) * volume (⋃ P ∈ D.P5, P.toSet)) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), e, ENNReal.ofReal_one, one_mul]
    _ ≤ ENNReal.ofReal (D.ε / 2 ^ d) * (2 ^ d * ENNReal.ofReal D.Q.vol) :=
        mul_le_mul' le_rfl (h.trans (mul_le_mul' le_rfl hQ))
    _ = ENNReal.ofReal (D.ε * D.Q.vol) := by
        rw [h2', ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity), div_mul_cancel₀ _ h20]

/-- **The claim (2.7)** (p. 41) for the stopping cubes of the data `D`:
`∑_{P ∈ 𝐏} |P| ≤ (1 - ε)|Q|`. [PROVED] -/
theorem volume_stoppingCubes_le :
    volume (⋃ P ∈ D.stoppingCubes, P.toSet) ≤ ENNReal.ofReal ((1 - D.ε) * D.Q.vol) :=
  volume_maximal_union_le D.ε_pos.le D.ε_le D.volume_P1_le D.volume_P2_le D.volume_P3_le
    D.volume_P4_le D.volume_P5_le

/-! #### The upper bounds (2.8)–(2.11) off the stopping cubes (p. 42)

"If `P` is not contained in any child or grandchild of a stopping cube" means: `P ⊆ Q` is not
contained in any child of a stopping cube, i.e. `P` lies in no stopping cube or `P` is itself a
stopping cube. In the first case the stopping conditions (2.3)–(2.5) fail at `P` (every cube
with one of the properties lies in a maximal one), which gives (2.8)–(2.10) with the threshold
constants. In the second case, for `P ≠ Q`, the parent `parents(P) ⊆ Q` lies in no stopping cube by
maximality, and the bounds are transferred from `parents(P)` to `P` at the cost of a factor `2^d`
(for (2.10) through the smoothness step `Λ_P(ρ, u) = Λ_{parents(P)}(ρ, u)`); for `P = Q` the
bounds are
trivial. The lower bound (2.11) holds for all cubes not contained in a cube of `𝐏₄`. -/

/-- `P` is contained in no stopping cube. -/
def NotInStopping (P : DyadicCube d) : Prop := ∀ S ∈ D.stoppingCubes, ¬ P.toSet ⊆ S.toSet

/-- `P ⊆ Q` is not contained in any child of a stopping cube. -/
def Good (P : DyadicCube d) : Prop :=
  P ∈ D.tree ∧ ∀ S ∈ D.stoppingCubes, ∀ ε : Fin d → Bool, ¬ P.toSet ⊆ (S.child ε).toSet

theorem union_subset_tree : D.P1 ∪ D.P2 ∪ D.P3 ∪ D.P4 ∪ D.P5 ⊆ D.Q.tree :=
  Set.union_subset (Set.union_subset (Set.union_subset (Set.union_subset
    (D.maximal_sep_subset _) (D.maximal_sep_subset _)) (D.maximal_sep_subset _))
    (D.maximal_sep_subset _)) (D.maximal_sep_subset _)

theorem P1_subset : D.P1 ⊆ D.P1 ∪ D.P2 ∪ D.P3 ∪ D.P4 ∪ D.P5 :=
  fun _ h => Or.inl (Or.inl (Or.inl (Or.inl h)))

theorem P2_subset : D.P2 ⊆ D.P1 ∪ D.P2 ∪ D.P3 ∪ D.P4 ∪ D.P5 :=
  fun _ h => Or.inl (Or.inl (Or.inl (Or.inr h)))

theorem P3_subset : D.P3 ⊆ D.P1 ∪ D.P2 ∪ D.P3 ∪ D.P4 ∪ D.P5 :=
  fun _ h => Or.inl (Or.inl (Or.inr h))

theorem P4_subset : D.P4 ⊆ D.P1 ∪ D.P2 ∪ D.P3 ∪ D.P4 ∪ D.P5 := fun _ h => Or.inl (Or.inr h)

theorem union_subset_tree' : D.P1 ∪ D.P2 ∪ D.P3 ∪ D.P4 ∪ D.P5 ⊆ D.tree :=
  Set.union_subset (Set.union_subset (Set.union_subset (Set.union_subset
    (fun _ h => mem_of_mem_maximal_sep h) (fun _ h => mem_of_mem_maximal_sep h))
    (fun _ h => mem_of_mem_maximal_sep h)) (fun _ h => mem_of_mem_maximal_sep h))
    (fun _ h => mem_of_mem_maximal_sep h)

theorem stoppingCubes_subset_tree' : D.stoppingCubes ⊆ D.tree :=
  (maximal_subset _).trans D.union_subset_tree'

theorem stoppingCubes_finite : D.stoppingCubes.Finite :=
  D.tree_finite.subset D.stoppingCubes_subset_tree'

/-- A cube of `𝒟(Q)` with one of the stopping properties lies in a stopping cube; hence a cube
in no stopping cube has none of the properties. [PROVED] -/
theorem not_prop_of_notInStopping (hd : d ≠ 0) {X : DyadicCube d → Prop}
    (hX : maximal {P ∈ D.tree | X P} ⊆ D.P1 ∪ D.P2 ∪ D.P3 ∪ D.P4 ∪ D.P5) {P : DyadicCube d}
    (hPQ : P ∈ D.tree) (hP : D.NotInStopping P) : ¬ X P := by
  intro h
  obtain ⟨S₁, hS₁, hsub₁⟩ := exists_maximal_superset hd (S := {P ∈ D.tree | X P})
    (fun _ h => D.tree_subset h.1) ⟨hPQ, h⟩
  obtain ⟨S, hS, hsub⟩ := exists_maximal_superset hd D.union_subset_tree (hX hS₁)
  exact hP S hS (hsub₁.trans hsub)

/-- Off the stopping cubes, (2.3) fails. [PROVED] -/
theorem lt_of_notInStopping_P1 (hd : d ≠ 0) {P : DyadicCube d} (hPQ : P ∈ D.tree)
    (hP : D.NotInStopping P) {j : Fin n} (hj : j ∈ D.J) :
    (volume P.toSet)⁻¹ * ∫⁻ x in P.toSet, ‖(D.g j : (Fin d → ℝ) → ℝ) x‖ₑ ^ D.p.p j <
      ENNReal.ofReal ((n + D.m) / (D.ε * D.Q.vol)) *
        ∫⁻ x in D.Q.toSet, ‖(D.g j : (Fin d → ℝ) → ℝ) x‖ₑ ^ D.p.p j := by
  have hnot := D.not_prop_of_notInStopping hd D.P1_subset hPQ hP
  exact not_le.mp fun h => hnot (Or.inl ⟨j, hj, h⟩)

/-- Off the stopping cubes, the Chebyshev condition for the auxiliary functions fails. [PROVED] -/
theorem lt_of_notInStopping_aux (hd : d ≠ 0) {P : DyadicCube d} (hPQ : P ∈ D.tree)
    (hP : D.NotInStopping P) (i : Fin D.m)
    (hi : ∫⁻ x in D.Q.toSet, ‖(D.aux i : (Fin d → ℝ) → ℝ) x‖ₑ ^ D.auxExp i ≠ 0) :
    (volume P.toSet)⁻¹ * ∫⁻ x in P.toSet, ‖(D.aux i : (Fin d → ℝ) → ℝ) x‖ₑ ^ D.auxExp i <
      ENNReal.ofReal ((n + D.m) / (D.ε * D.Q.vol)) *
        ∫⁻ x in D.Q.toSet, ‖(D.aux i : (Fin d → ℝ) → ℝ) x‖ₑ ^ D.auxExp i := by
  have hnot := D.not_prop_of_notInStopping hd D.P1_subset hPQ hP
  exact not_le.mp fun h => hnot (Or.inr ⟨i, hi, h⟩)

/-- Off the stopping cubes, (2.4) fails. [PROVED] -/
theorem lt_of_notInStopping_P2 (hd : d ≠ 0) {P : DyadicCube d} (hPQ : P ∈ D.tree)
    (hP : D.NotInStopping P) :
    (volume P.toSet)⁻¹ * ∫⁻ x in P.toSet, ‖(D.u : (Fin d → ℝ) → ℝ) x‖ₑ ^ D.q <
      ENNReal.ofReal (1 / (D.ε * D.Q.vol)) *
        ∫⁻ x in D.Q.toSet, ‖(D.u : (Fin d → ℝ) → ℝ) x‖ₑ ^ D.q :=
  not_le.mp (D.not_prop_of_notInStopping hd D.P2_subset hPQ hP)

/-- Off the stopping cubes, (2.5) fails: `|Λ_P(ρ, u)| ≤ B F ‖u‖_q ε^{-1} (|P|/|Q|)^{1-1/r} ‖ρ‖_r`
for every mean-zero `ρ` supported on `P`. [PROVED] -/
theorem le_of_notInStopping_P3 (hd : d ≠ 0) {P : DyadicCube d} (hPQ : P ∈ D.tree)
    (hP : D.NotInStopping P) (ρ : TestFun d) (hρ : SupportedOn ρ P)
    (hρ0 : MeanZero (ρ : (Fin d → ℝ) → ℝ)) :
    |slotForm D.T D.a D.g P ρ| ≤ D.B * D.F * lpNorm (D.u : (Fin d → ℝ) → ℝ) D.q * D.ε⁻¹ *
      (P.vol / D.Q.vol) ^ (1 - 1 / D.r) * lpNorm (ρ : (Fin d → ℝ) → ℝ) D.r := by
  have hnot := D.not_prop_of_notInStopping hd D.P3_subset hPQ hP
  by_cases h0 : lpNorm (ρ : (Fin d → ℝ) → ℝ) D.r = 0
  · rw [slotForm_eq_zero_of_lpNorm_eq_zero D.T D.a D.g P (by linarith [D.hr]) h0, abs_zero, h0,
      mul_zero]
  · have hpos : 0 < lpNorm (ρ : (Fin d → ℝ) → ℝ) D.r :=
      lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm h0)
    by_contra hlt
    rw [not_le] at hlt
    exact hnot (Or.inl ⟨ρ, hρ, hρ0, hpos, hlt.le⟩)

/-- Off the stopping cubes, the extra `𝐏₃`-type condition fails:
`|Λ_P(w, ρ)| ≤ K ε^{-1} (|P|/|Q|)^{1-1/q} ‖ρ‖_q` for every mean-zero `ρ` supported on `P`.
[PROVED] -/
theorem le_of_notInStopping_w (hd : d ≠ 0) {P : DyadicCube d} (hPQ : P ∈ D.tree)
    (hP : D.NotInStopping P) (ρ : TestFun d) (hρ : SupportedOn ρ P)
    (hρ0 : MeanZero (ρ : (Fin d → ℝ) → ℝ)) :
    |twoSlotForm D.T D.a D.b D.g P D.w ρ| ≤
      D.K * D.ε⁻¹ * (P.vol / D.Q.vol) ^ (1 - 1 / D.q) * lpNorm (ρ : (Fin d → ℝ) → ℝ) D.q := by
  have hnot := D.not_prop_of_notInStopping hd D.P3_subset hPQ hP
  by_cases h0 : lpNorm (ρ : (Fin d → ℝ) → ℝ) D.q = 0
  · rw [twoSlotForm_eq_slotForm', slotForm_eq_zero_of_lpNorm_eq_zero D.T D.b _ P
      (by linarith [D.hq]) h0, abs_zero, h0, mul_zero]
  · have hpos : 0 < lpNorm (ρ : (Fin d → ℝ) → ℝ) D.q :=
      lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm h0)
    by_contra hlt
    rw [not_le] at hlt
    exact hnot (Or.inr ⟨ρ, hρ, hρ0, hpos, hlt.le⟩)

/-- **(2.11)**: `|[u]_P| > 1/8` for every `P ⊆ Q` not contained in a cube of `𝐏₄`. [PROVED] -/
theorem bound_2_11 (hd : d ≠ 0) {P : DyadicCube d} (hPQ : P ∈ D.tree)
    (hP : ∀ S ∈ D.P4, ¬ P.toSet ⊆ S.toSet) : 1 / 8 < |avg P D.u| := by
  by_contra h
  rw [not_lt] at h
  obtain ⟨S, hS, hsub⟩ := exists_maximal_superset hd
    (S := {P ∈ D.tree | |avg P D.u| ≤ 1 / 8}) (fun _ h => D.tree_subset h.1) ⟨hPQ, h⟩
  exact hP S hS hsub

/-- A good cube lies in no stopping cube or is itself a stopping cube. [PROVED] -/
theorem good_cases (hd : d ≠ 0) {P : DyadicCube d} (hP : D.Good P) :
    D.NotInStopping P ∨ P ∈ D.stoppingCubes := by
  by_cases h : D.NotInStopping P
  · exact Or.inl h
  · right
    obtain ⟨S, hS, hsub⟩ : ∃ S ∈ D.stoppingCubes, P.toSet ⊆ S.toSet := by
      by_contra h'
      exact h fun S hS hsub => h' ⟨S, hS, hsub⟩
    by_cases hPS : P = S
    · rw [hPS]
      exact hS
    · obtain ⟨ε, hε⟩ := DyadicCube.exists_child_of_ssubset hd hsub hPS
      exact absurd hε (hP.2 S hS ε)

/-- The parent of a stopping cube `P ≠ Q` lies in `Q` and in no stopping cube (maximality).
[PROVED] -/
theorem parent_notInStopping (hd : d ≠ 0) {P : DyadicCube d} (hP : P ∈ D.stoppingCubes)
    (hne : P ≠ D.Q) : D.NotInStopping P.parent ∧ P.parent ∈ D.tree := by
  have hPt : P ∈ D.tree := D.stoppingCubes_subset_tree' hP
  have hPQ : P.toSet ⊆ D.Q.toSet := hPt.1
  refine ⟨?_, DyadicCube.parent_subset_of_ssubset hd hPQ hne, ?_⟩
  · intro S hS hsub
    have hSP : S = P := hP.2 S hS.1 (P.subset_parent.trans hsub)
    have hsub' : P.parent.toSet ⊆ P.toSet := by
      rw [hSP] at hsub
      exact hsub
    have hm := DyadicCube.m_le_of_subset hd hsub'
    rw [DyadicCube.parent_m] at hm
    omega
  · rw [DyadicCube.parent_m]
    have := hPt.2
    omega

/-- The common pattern of (2.8) and (2.9): a threshold `|P|^{-1} ∫_P w ≤ c (ε|Q|)^{-1} ∫_Q w` off
the stopping cubes gives `|P|^{-1} ∫_P w ≤ 2^d c ε^{-1} |Q|^{-1} ∫_Q w` on all good cubes.
[PROVED] -/
theorem avg_bound_of_good (hd : d ≠ 0) {w : (Fin d → ℝ) → ENNReal} {c : ℝ} (hc : 1 ≤ c)
    {P : DyadicCube d} (hP : D.Good P)
    (hthr : ∀ P' ∈ D.tree, D.NotInStopping P' →
      (volume P'.toSet)⁻¹ * ∫⁻ x in P'.toSet, w x ≤
        ENNReal.ofReal (c / (D.ε * D.Q.vol)) * ∫⁻ x in D.Q.toSet, w x) :
    (volume P.toSet)⁻¹ * ∫⁻ x in P.toSet, w x ≤
      ENNReal.ofReal (2 ^ d * c / D.ε) * ((volume D.Q.toSet)⁻¹ * ∫⁻ x in D.Q.toSet, w x) := by
  have hε := D.ε_pos
  have hε8 := D.ε_le
  have hV := D.Q.vol_pos
  have hc0 : 0 ≤ c := by linarith
  have hkey : ENNReal.ofReal (c / (D.ε * D.Q.vol)) * ∫⁻ x in D.Q.toSet, w x =
      ENNReal.ofReal (c / D.ε) * ((volume D.Q.toSet)⁻¹ * ∫⁻ x in D.Q.toSet, w x) := by
    rw [D.Q.volume_toSet, ← ENNReal.ofReal_inv_of_pos hV, ← mul_assoc,
      ← ENNReal.ofReal_mul (by positivity)]
    congr 2
    ring
  have h2d : (2 : ENNReal) ^ d = ENNReal.ofReal (2 ^ d) := by
    rw [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
  have h2d1 : (1 : ENNReal) ≤ 2 ^ d := one_le_pow₀ one_le_two
  have hC : ENNReal.ofReal (2 ^ d * c / D.ε) = 2 ^ d * ENNReal.ofReal (c / D.ε) := by
    rw [h2d, ← ENNReal.ofReal_mul (by positivity), mul_div_assoc]
  rcases D.good_cases hd hP with hA | hB
  · calc (volume P.toSet)⁻¹ * ∫⁻ x in P.toSet, w x
        ≤ ENNReal.ofReal (c / (D.ε * D.Q.vol)) * ∫⁻ x in D.Q.toSet, w x := hthr P hP.1 hA
      _ = ENNReal.ofReal (c / D.ε) * ((volume D.Q.toSet)⁻¹ * ∫⁻ x in D.Q.toSet, w x) := hkey
      _ ≤ 2 ^ d * ENNReal.ofReal (c / D.ε) *
            ((volume D.Q.toSet)⁻¹ * ∫⁻ x in D.Q.toSet, w x) := by
          rw [mul_assoc]
          exact le_mul_of_one_le_left zero_le h2d1
      _ = _ := by rw [hC]
  · by_cases hPQ : P = D.Q
    · subst hPQ
      have h1 : (1 : ENNReal) ≤ ENNReal.ofReal (2 ^ d * c / D.ε) := by
        rw [ENNReal.one_le_ofReal, le_div_iff₀ hε, one_mul]
        have : (1 : ℝ) ≤ 2 ^ d * c := one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) hc
        linarith
      exact le_mul_of_one_le_left zero_le h1
    · obtain ⟨hpar, hparQ⟩ := D.parent_notInStopping hd hB hPQ
      calc (volume P.toSet)⁻¹ * ∫⁻ x in P.toSet, w x
          ≤ 2 ^ d * ((volume P.parent.toSet)⁻¹ * ∫⁻ x in P.parent.toSet, w x) :=
            avg_le_parent w P
        _ ≤ 2 ^ d * (ENNReal.ofReal (c / (D.ε * D.Q.vol)) * ∫⁻ x in D.Q.toSet, w x) :=
            mul_le_mul' le_rfl (hthr _ hparQ hpar)
        _ = _ := by rw [hkey, hC, mul_assoc]

/-- **(2.8)**: for a good cube `P` and `j ≠ k, k+1`,
`|P|^{-1} ‖f_j 𝟙_P‖_{p_j}^{p_j} ≤ 2^d n ε^{-1} |Q|^{-1} ‖f_j‖_{p_j}^{p_j}`. [PROVED] -/
theorem one_le_n_add_m : (1 : ℝ) ≤ n + D.m := by
  have h := D.n_pos
  exact_mod_cast (Nat.succ_le_of_lt h).trans (Nat.le_add_right n D.m)

theorem bound_2_8 (hd : d ≠ 0) {P : DyadicCube d} (hP : D.Good P) {j : Fin n} (hj : j ∈ D.J) :
    (volume P.toSet)⁻¹ * ∫⁻ x in P.toSet, ‖(D.g j : (Fin d → ℝ) → ℝ) x‖ₑ ^ D.p.p j ≤
      ENNReal.ofReal (2 ^ d * (n + D.m) / D.ε) *
        ((volume D.Q.toSet)⁻¹ * ∫⁻ x in D.Q.toSet, ‖(D.g j : (Fin d → ℝ) → ℝ) x‖ₑ ^ D.p.p j) :=
  D.avg_bound_of_good hd D.one_le_n_add_m hP fun _ hP'Q hP' =>
    (D.lt_of_notInStopping_P1 hd hP'Q hP' hj).le

/-- The analogue of (2.8) for the auxiliary functions ((2.33), (2.35) in §2.4): for a good cube
`P`, `|P|^{-1} ‖aux_i 𝟙_P‖^{e_i} ≤ 2^d (n+m) ε^{-1} |Q|^{-1} ‖aux_i‖^{e_i}`. [PROVED] -/
theorem bound_2_8_aux (hd : d ≠ 0) {P : DyadicCube d} (hP : D.Good P) (i : Fin D.m) :
    (volume P.toSet)⁻¹ * ∫⁻ x in P.toSet, ‖(D.aux i : (Fin d → ℝ) → ℝ) x‖ₑ ^ D.auxExp i ≤
      ENNReal.ofReal (2 ^ d * (n + D.m) / D.ε) *
        ((volume D.Q.toSet)⁻¹ *
          ∫⁻ x in D.Q.toSet, ‖(D.aux i : (Fin d → ℝ) → ℝ) x‖ₑ ^ D.auxExp i) := by
  by_cases hi : ∫⁻ x in D.Q.toSet, ‖(D.aux i : (Fin d → ℝ) → ℝ) x‖ₑ ^ D.auxExp i = 0
  · have hPQ : P.toSet ⊆ D.Q.toSet := hP.1.1
    have h0 : ∫⁻ x in P.toSet, ‖(D.aux i : (Fin d → ℝ) → ℝ) x‖ₑ ^ D.auxExp i = 0 :=
      le_antisymm ((lintegral_mono_set hPQ).trans_eq hi) zero_le
    rw [h0, mul_zero]
    exact zero_le
  · exact D.avg_bound_of_good hd D.one_le_n_add_m hP fun _ hP'Q hP' =>
      (D.lt_of_notInStopping_aux hd hP'Q hP' i hi).le

/-- **(2.9)**, first inequality: for a good cube `P`,
`|P|^{-1} ‖u_P‖_q^q ≤ 2^d ε^{-1} |Q|^{-1} ‖u‖_q^q`. [PROVED] -/
theorem bound_2_9 (hd : d ≠ 0) {P : DyadicCube d} (hP : D.Good P) :
    (volume P.toSet)⁻¹ * ∫⁻ x in P.toSet, ‖(D.u : (Fin d → ℝ) → ℝ) x‖ₑ ^ D.q ≤
      ENNReal.ofReal (2 ^ d / D.ε) *
        ((volume D.Q.toSet)⁻¹ * ∫⁻ x in D.Q.toSet, ‖(D.u : (Fin d → ℝ) → ℝ) x‖ₑ ^ D.q) := by
  have := D.avg_bound_of_good hd le_rfl hP fun P' hP'Q hP' =>
    (D.lt_of_notInStopping_P2 hd hP'Q hP').le
  rwa [mul_one] at this

/-- `∫_Q |u|^q ≤ B|Q|` as lintegrals (the norm condition (1.7)). [PROVED] -/
theorem lintegral_u_le :
    ∫⁻ x in D.Q.toSet, ‖(D.u : (Fin d → ℝ) → ℝ) x‖ₑ ^ D.q ≤ ENNReal.ofReal (D.B * D.Q.vol) := by
  have hq0 : 0 < D.q := by linarith [D.hq]
  have hmem : MemLp (D.u : (Fin d → ℝ) → ℝ) (ENNReal.ofReal D.q) volume :=
    TestFun.memLp D.u.2 _
  rw [D.setLIntegral_eq D.b, ← ENNReal.ofReal_toReal hmem.eLpNorm_ne_top,
    ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hq0.le]
  exact ENNReal.ofReal_le_ofReal ((lpNorm_rpow_eq_integral hq0 hmem).trans_le D.norm)

/-- **(2.9)**, second inequality: for a good cube `P`, `|P|^{-1} ‖u_P‖_q^q ≤ 2^d B ε^{-1}`.
[PROVED] -/
theorem bound_2_9' (hd : d ≠ 0) {P : DyadicCube d} (hP : D.Good P) :
    (volume P.toSet)⁻¹ * ∫⁻ x in P.toSet, ‖(D.u : (Fin d → ℝ) → ℝ) x‖ₑ ^ D.q ≤
      ENNReal.ofReal (2 ^ d * D.B / D.ε) := by
  have hε := D.ε_pos
  have hV := D.Q.vol_pos
  have hB0 : 0 ≤ D.B := by linarith [D.hB]
  calc (volume P.toSet)⁻¹ * ∫⁻ x in P.toSet, ‖(D.u : (Fin d → ℝ) → ℝ) x‖ₑ ^ D.q
      ≤ ENNReal.ofReal (2 ^ d / D.ε) *
        ((volume D.Q.toSet)⁻¹ * ∫⁻ x in D.Q.toSet, ‖(D.u : (Fin d → ℝ) → ℝ) x‖ₑ ^ D.q) :=
        D.bound_2_9 hd hP
    _ ≤ ENNReal.ofReal (2 ^ d / D.ε) * ((volume D.Q.toSet)⁻¹ * ENNReal.ofReal (D.B * D.Q.vol)) :=
        mul_le_mul' le_rfl (mul_le_mul' le_rfl D.lintegral_u_le)
    _ = ENNReal.ofReal (2 ^ d * D.B / D.ε) := by
        rw [D.Q.volume_toSet, ← ENNReal.ofReal_inv_of_pos hV, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [show (2 : ℝ) ^ d / D.ε * (D.Q.vol⁻¹ * (D.B * D.Q.vol)) =
          2 ^ d * D.B / D.ε * (D.Q.vol⁻¹ * D.Q.vol) by ring, inv_mul_cancel₀ hV.ne', mul_one]

/-- **(2.10)**: for a good cube `P` and every mean-zero `ρ` supported on `P`,
`|Λ_P(ρ, u)| ≤ 2^d B F ‖u‖_q ε^{-1} (|P|/|Q|)^{1-1/r} ‖ρ‖_r`. [PROVED] -/
theorem bound_2_10 (hd : d ≠ 0) {P : DyadicCube d} (hP : D.Good P) (ρ : TestFun d)
    (hρ : SupportedOn ρ P) (hρ0 : MeanZero (ρ : (Fin d → ℝ) → ℝ)) :
    |slotForm D.T D.a D.g P ρ| ≤
      2 ^ d * (D.B * D.F * lpNorm (D.u : (Fin d → ℝ) → ℝ) D.q * D.ε⁻¹) *
        (P.vol / D.Q.vol) ^ (1 - 1 / D.r) * lpNorm (ρ : (Fin d → ℝ) → ℝ) D.r := by
  set K := D.B * D.F * lpNorm (D.u : (Fin d → ℝ) → ℝ) D.q with hK
  have hK0 : 0 ≤ K := le_of_lt (mul_pos (mul_pos (by linarith [D.hB]) D.Fpos') D.lpNorm_u_pos)
  have hε := D.ε_pos
  have hε1 : 1 ≤ D.ε⁻¹ := (one_le_inv₀ hε).mpr (by linarith [D.ε_le])
  have hKε : 0 ≤ K * D.ε⁻¹ := mul_nonneg hK0 (inv_nonneg.mpr hε.le)
  have h2d : (1 : ℝ) ≤ 2 ^ d := one_le_pow₀ (by norm_num)
  have hρnn : 0 ≤ lpNorm (ρ : (Fin d → ℝ) → ℝ) D.r := ENNReal.toReal_nonneg
  have hV := D.Q.vol_pos
  have hr0 : 0 < D.r := by linarith [D.hr]
  have hX : 0 ≤ (P.vol / D.Q.vol) ^ (1 - 1 / D.r) :=
    Real.rpow_nonneg (div_nonneg P.vol_pos.le hV.le) _
  rcases D.good_cases hd hP with hA | hB
  · calc |slotForm D.T D.a D.g P ρ|
        ≤ K * D.ε⁻¹ * (P.vol / D.Q.vol) ^ (1 - 1 / D.r) * lpNorm (ρ : (Fin d → ℝ) → ℝ) D.r :=
          D.le_of_notInStopping_P3 hd hP.1 hA ρ hρ hρ0
      _ ≤ 2 ^ d * (K * D.ε⁻¹) * (P.vol / D.Q.vol) ^ (1 - 1 / D.r) *
            lpNorm (ρ : (Fin d → ℝ) → ℝ) D.r :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_mul_of_one_le_left hKε h2d) hX) hρnn
  · by_cases hPQ : P = D.Q
    · subst hPQ
      have h : |slotForm D.T D.a D.g D.Q ρ| ≤ K * lpNorm (ρ : (Fin d → ℝ) → ℝ) D.r :=
        D.testing ρ hρ
      rw [div_self hV.ne', Real.one_rpow, mul_one]
      have hK' : K ≤ 2 ^ d * (K * D.ε⁻¹) := by
        calc K = 1 * (K * 1) := by ring
          _ ≤ 2 ^ d * (K * D.ε⁻¹) :=
            mul_le_mul h2d (mul_le_mul_of_nonneg_left hε1 hK0) (by positivity) (by positivity)
      exact h.trans (mul_le_mul_of_nonneg_right hK' hρnn)
    · obtain ⟨hpar, hparQ⟩ := D.parent_notInStopping hd hB hPQ
      have hsub := P.subset_parent
      have hρ' : SupportedOn ρ P.parent := fun x hx => hρ x fun h => hx (hsub h)
      rw [slotForm_eq_of_subset D.T D.a D.g hsub hρ hρ0]
      have h := D.le_of_notInStopping_P3 hd hparQ hpar ρ hρ' hρ0
      have hexp : (P.parent.vol / D.Q.vol) ^ (1 - 1 / D.r) ≤
          2 ^ d * (P.vol / D.Q.vol) ^ (1 - 1 / D.r) := by
        rw [DyadicCube.vol_parent, mul_div_assoc,
          Real.mul_rpow (by positivity) (div_nonneg P.vol_pos.le hV.le)]
        refine mul_le_mul_of_nonneg_right ?_ hX
        calc ((2 : ℝ) ^ d) ^ (1 - 1 / D.r) ≤ ((2 : ℝ) ^ d) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le h2d (by linarith [div_pos one_pos hr0])
          _ = 2 ^ d := Real.rpow_one _
      calc |slotForm D.T D.a D.g P.parent ρ|
          ≤ K * D.ε⁻¹ * (P.parent.vol / D.Q.vol) ^ (1 - 1 / D.r) *
              lpNorm (ρ : (Fin d → ℝ) → ℝ) D.r := h
        _ ≤ K * D.ε⁻¹ * (2 ^ d * (P.vol / D.Q.vol) ^ (1 - 1 / D.r)) *
              lpNorm (ρ : (Fin d → ℝ) → ℝ) D.r :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp hKε) hρnn
        _ = 2 ^ d * (K * D.ε⁻¹) * (P.vol / D.Q.vol) ^ (1 - 1 / D.r) *
              lpNorm (ρ : (Fin d → ℝ) → ℝ) D.r := by ring

/-- The analogue of (2.10) for the extra `𝐏₃`-type condition ((2.37) in §2.4): for a good cube
`P` and a mean-zero `ρ` supported on `P`,
`|Λ_P(w, ρ)| ≤ 2^d K ε^{-1} (|P|/|Q|)^{1-1/q} ‖ρ‖_q`. [PROVED] -/
theorem bound_2_10_w (hd : d ≠ 0) {P : DyadicCube d} (hP : D.Good P) (ρ : TestFun d)
    (hρ : SupportedOn ρ P) (hρ0 : MeanZero (ρ : (Fin d → ℝ) → ℝ)) :
    |twoSlotForm D.T D.a D.b D.g P D.w ρ| ≤
      2 ^ d * (D.K * D.ε⁻¹) * (P.vol / D.Q.vol) ^ (1 - 1 / D.q) *
        lpNorm (ρ : (Fin d → ℝ) → ℝ) D.q := by
  have hK0 : 0 ≤ D.K := D.hK.le
  have hε := D.ε_pos
  have hε1 : 1 ≤ D.ε⁻¹ := (one_le_inv₀ hε).mpr (by linarith [D.ε_le])
  have hKε : 0 ≤ D.K * D.ε⁻¹ := mul_nonneg hK0 (inv_nonneg.mpr hε.le)
  have h2d : (1 : ℝ) ≤ 2 ^ d := one_le_pow₀ (by norm_num)
  have hρnn : 0 ≤ lpNorm (ρ : (Fin d → ℝ) → ℝ) D.q := ENNReal.toReal_nonneg
  have hV := D.Q.vol_pos
  have hq0 : 0 < D.q := by linarith [D.hq]
  have hX : 0 ≤ (P.vol / D.Q.vol) ^ (1 - 1 / D.q) :=
    Real.rpow_nonneg (div_nonneg P.vol_pos.le hV.le) _
  rcases D.good_cases hd hP with hA | hB
  · calc |twoSlotForm D.T D.a D.b D.g P D.w ρ|
        ≤ D.K * D.ε⁻¹ * (P.vol / D.Q.vol) ^ (1 - 1 / D.q) * lpNorm (ρ : (Fin d → ℝ) → ℝ) D.q :=
          D.le_of_notInStopping_w hd hP.1 hA ρ hρ hρ0
      _ ≤ 2 ^ d * (D.K * D.ε⁻¹) * (P.vol / D.Q.vol) ^ (1 - 1 / D.q) *
            lpNorm (ρ : (Fin d → ℝ) → ℝ) D.q :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_mul_of_one_le_left hKε h2d) hX) hρnn
  · by_cases hPQ : P = D.Q
    · subst hPQ
      have h := D.w_test ρ hρ hρ0
      rw [div_self hV.ne', Real.one_rpow, mul_one]
      have hK' : D.K ≤ 2 ^ d * (D.K * D.ε⁻¹) := by
        calc D.K = 1 * (D.K * 1) := by ring
          _ ≤ 2 ^ d * (D.K * D.ε⁻¹) :=
            mul_le_mul h2d (mul_le_mul_of_nonneg_left hε1 hK0) (by positivity) (by positivity)
      exact h.trans (mul_le_mul_of_nonneg_right hK' hρnn)
    · obtain ⟨hpar, hparQ⟩ := D.parent_notInStopping hd hB hPQ
      have hsub := P.subset_parent
      have hρ' : SupportedOn ρ P.parent := fun x hx => hρ x fun h => hx (hsub h)
      rw [twoSlotForm_eq_of_subset D.T D.a D.b D.g hsub D.w hρ hρ0]
      have h := D.le_of_notInStopping_w hd hparQ hpar ρ hρ' hρ0
      have hexp : (P.parent.vol / D.Q.vol) ^ (1 - 1 / D.q) ≤
          2 ^ d * (P.vol / D.Q.vol) ^ (1 - 1 / D.q) := by
        rw [DyadicCube.vol_parent, mul_div_assoc,
          Real.mul_rpow (by positivity) (div_nonneg P.vol_pos.le hV.le)]
        refine mul_le_mul_of_nonneg_right ?_ hX
        calc ((2 : ℝ) ^ d) ^ (1 - 1 / D.q) ≤ ((2 : ℝ) ^ d) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le h2d (by linarith [div_pos one_pos hq0])
          _ = 2 ^ d := Real.rpow_one _
      calc |twoSlotForm D.T D.a D.b D.g P.parent D.w ρ|
          ≤ D.K * D.ε⁻¹ * (P.parent.vol / D.Q.vol) ^ (1 - 1 / D.q) *
              lpNorm (ρ : (Fin d → ℝ) → ℝ) D.q := h
        _ ≤ D.K * D.ε⁻¹ * (2 ^ d * (P.vol / D.Q.vol) ^ (1 - 1 / D.q)) *
              lpNorm (ρ : (Fin d → ℝ) → ℝ) D.q :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp hKε) hρnn
        _ = 2 ^ d * (D.K * D.ε⁻¹) * (P.vol / D.Q.vol) ^ (1 - 1 / D.q) *
              lpNorm (ρ : (Fin d → ℝ) → ℝ) D.q := by ring

/-! #### §2.3 The pruned function `𝔤` (paper, p. 43, (2.12))

`𝔤 = g - [g]_Q u - ∑_{P ∈ 𝐏∖𝐏₄} g_P + ∑_{P ∈ 𝐏∖𝐏₄} ([g]_P/[u]_P) u_P - ∑_{P ∈ 𝐏∩𝐏₄} g_P
     + ∑_{P ∈ parents(𝐏)₄} ([g]_P/[u]_P) u_P - ∑_{P ∈ 𝐏₄'} ([g]_P/[u]_P) u_P`,
where `parents(𝐏)₄` are the parents of the cubes of `𝐏 ∩ 𝐏₄` and `𝐏₄'` their siblings not in `𝐏 ∩
𝐏₄`.
All sums are finite because the stopping cubes lie in the finite tree `𝒟_N(Q)`. -/

/-- `𝐏` as a finite set. -/
noncomputable def Pst : Finset (DyadicCube d) := D.stoppingCubes_finite.toFinset

theorem mem_Pst {P : DyadicCube d} : P ∈ D.Pst ↔ P ∈ D.stoppingCubes :=
  Set.Finite.mem_toFinset _


/-- `𝐏 ∩ 𝐏₄`. -/
noncomputable def PstIn4 : Finset (DyadicCube d) := by
  classical
  exact D.Pst.filter (· ∈ D.P4)

/-- `𝐏 ∖ 𝐏₄`. -/
noncomputable def PstOut4 : Finset (DyadicCube d) := by
  classical
  exact D.Pst.filter (· ∉ D.P4)

/-- `parents(𝐏)₄`: the parents of the cubes of `𝐏 ∩ 𝐏₄`. -/
noncomputable def Pbar4 : Finset (DyadicCube d) := D.PstIn4.image DyadicCube.parent

/-- The children of a cube, as a finite set. -/
noncomputable def children (R : DyadicCube d) : Finset (DyadicCube d) :=
  Finset.univ.image R.child

/-- `𝐏₄'`: the siblings of the cubes of `𝐏 ∩ 𝐏₄` (the children of the cubes of `parents(𝐏)₄`)
which are
not themselves in `𝐏 ∩ 𝐏₄`. -/
noncomputable def Psib4 : Finset (DyadicCube d) :=
  (D.Pbar4.biUnion children).filter (· ∉ D.PstIn4)

/-- The coefficient `[g]_P / [u]_P`. -/
noncomputable def coef (P : DyadicCube d) : ℝ := avg P D.G / avg P D.u

/-- The pruned function `𝔤` of (2.12). -/
noncomputable def pruned : TestFun d :=
  D.G - avg D.Q D.G • D.u - ∑ P ∈ D.PstOut4, TestFun.truncateₗ P D.G
    + ∑ P ∈ D.PstOut4, D.coef P • TestFun.truncateₗ P D.u
    - ∑ P ∈ D.PstIn4, TestFun.truncateₗ P D.G
    + ∑ P ∈ D.Pbar4, D.coef P • TestFun.truncateₗ P D.u
    - ∑ P ∈ D.Psib4, D.coef P • TestFun.truncateₗ P D.u

theorem mem_children {R c : DyadicCube d} : c ∈ children R ↔ ∃ ε, R.child ε = c := by
  simp [children]

theorem mem_PstIn4 {P : DyadicCube d} : P ∈ D.PstIn4 ↔ P ∈ D.stoppingCubes ∧ P ∈ D.P4 := by
  classical
  rw [PstIn4, Finset.mem_filter, mem_Pst]

theorem mem_PstOut4 {P : DyadicCube d} : P ∈ D.PstOut4 ↔ P ∈ D.stoppingCubes ∧ P ∉ D.P4 := by
  classical
  rw [PstOut4, Finset.mem_filter, mem_Pst]

theorem mem_Pbar4 {R : DyadicCube d} : R ∈ D.Pbar4 ↔ ∃ P ∈ D.PstIn4, P.parent = R := by
  rw [Pbar4, Finset.mem_image]

theorem mem_Psib4 {P' : DyadicCube d} :
    P' ∈ D.Psib4 ↔ (∃ R ∈ D.Pbar4, P' ∈ children R) ∧ P' ∉ D.PstIn4 := by
  rw [Psib4, Finset.mem_filter, Finset.mem_biUnion]

/-- `[u]_Q = 1`, so `Q ∉ 𝐏₄`. [PROVED] -/
theorem avg_u_Q : avg D.Q D.u = 1 := by
  rw [avg, setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => D.supp D.b x hx), D.mean,
    div_self D.Q.vol_pos.ne']

theorem Q_notMem_P4 : D.Q ∉ D.P4 := by
  intro h
  have := prop_of_mem_maximal_sep h
  rw [D.avg_u_Q] at this
  norm_num at this

theorem PstIn4_ne_Q {P : DyadicCube d} (hP : P ∈ D.PstIn4) : P ≠ D.Q := by
  intro h
  exact D.Q_notMem_P4 (h ▸ (D.mem_PstIn4.mp hP).2)

theorem Pst_subset_Q {P : DyadicCube d} (hP : P ∈ D.Pst) : P.toSet ⊆ D.Q.toSet :=
  (D.stoppingCubes_subset_tree' (D.mem_Pst.mp hP)).1

theorem Pbar4_subset_Q {R : DyadicCube d} (hR : R ∈ D.Pbar4) : R.toSet ⊆ D.Q.toSet := by
  classical
  obtain ⟨P, hP, rfl⟩ := D.mem_Pbar4.mp hR
  exact DyadicCube.parent_subset_of_ssubset D.hd
    (D.Pst_subset_Q (Finset.mem_of_mem_filter P hP)) (D.PstIn4_ne_Q hP)

theorem Psib4_subset_Q {P' : DyadicCube d} (hP' : P' ∈ D.Psib4) : P'.toSet ⊆ D.Q.toSet := by
  obtain ⟨⟨R, hR, hc⟩, -⟩ := D.mem_Psib4.mp hP'
  obtain ⟨ε, rfl⟩ := mem_children.mp hc
  exact (DyadicCube.child_subset R ε).trans (D.Pbar4_subset_Q hR)

/-- `𝔤` is supported on `Q`. [PROVED] -/
theorem pruned_supported : SupportedOn (D.pruned : (Fin d → ℝ) → ℝ) D.Q := by
  classical
  intro x hx
  have htr : ∀ P : DyadicCube d, P.toSet ⊆ D.Q.toSet → ∀ h : TestFun d,
      (TestFun.truncateₗ P h : (Fin d → ℝ) → ℝ) x = 0 := fun P hP h => by
    rw [TestFun.coe_truncateₗ]
    exact Set.indicator_of_notMem (fun h' => hx (hP h')) _
  have e1 : ∀ P ∈ D.PstOut4, (TestFun.truncateₗ P D.G : (Fin d → ℝ) → ℝ) x = 0 :=
    fun P hP => htr P (D.Pst_subset_Q (Finset.mem_of_mem_filter P hP)) _
  have e2 : ∀ P ∈ D.PstOut4, D.coef P * (TestFun.truncateₗ P D.u : (Fin d → ℝ) → ℝ) x = 0 :=
    fun P hP => by rw [htr P (D.Pst_subset_Q (Finset.mem_of_mem_filter P hP)), mul_zero]
  have e3 : ∀ P ∈ D.PstIn4, (TestFun.truncateₗ P D.G : (Fin d → ℝ) → ℝ) x = 0 :=
    fun P hP => htr P (D.Pst_subset_Q (Finset.mem_of_mem_filter P hP)) _
  have e4 : ∀ P ∈ D.Pbar4, D.coef P * (TestFun.truncateₗ P D.u : (Fin d → ℝ) → ℝ) x = 0 :=
    fun P hP => by rw [htr P (D.Pbar4_subset_Q hP), mul_zero]
  have e5 : ∀ P ∈ D.Psib4, D.coef P * (TestFun.truncateₗ P D.u : (Fin d → ℝ) → ℝ) x = 0 :=
    fun P hP => by rw [htr P (D.Psib4_subset_Q hP), mul_zero]
  simp only [pruned, Submodule.coe_sub, Submodule.coe_add, Submodule.coe_smul, Submodule.coe_sum,
    Pi.sub_apply, Pi.add_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul, D.Gsupp x hx,
    D.supp D.b x hx, Finset.sum_eq_zero e1, Finset.sum_eq_zero e2, Finset.sum_eq_zero e3,
    Finset.sum_eq_zero e4, Finset.sum_eq_zero e5]
  ring

/-- The cubes of `𝐏 ∖ 𝐏₄` lie in no cube of `𝐏₄`. [PROVED] -/
theorem PstOut4_not_in_P4 {P : DyadicCube d} (hP : P ∈ D.PstOut4) :
    ∀ S ∈ D.P4, ¬ P.toSet ⊆ S.toSet := by
  intro S hS hsub
  obtain ⟨hPs, hP4⟩ := D.mem_PstOut4.mp hP
  have := hPs.2 S (D.P4_subset hS) hsub
  exact hP4 (this ▸ hS)

/-- The cubes of `parents(𝐏)₄` lie in no cube of `𝐏₄`. [PROVED] -/
theorem Pbar4_not_in_P4 {R : DyadicCube d} (hR : R ∈ D.Pbar4) :
    ∀ S ∈ D.P4, ¬ R.toSet ⊆ S.toSet := by
  intro S hS hsub
  obtain ⟨P, hP, rfl⟩ := D.mem_Pbar4.mp hR
  have hnot := (D.parent_notInStopping D.hd (D.mem_PstIn4.mp hP).1 (D.PstIn4_ne_Q hP)).1
  obtain ⟨S', hS', hsub'⟩ := exists_maximal_superset D.hd D.union_subset_tree (D.P4_subset hS)
  exact hnot S' hS' (hsub.trans hsub')

theorem Pbar4_mem_tree {R : DyadicCube d} (hR : R ∈ D.Pbar4) : R ∈ D.tree := by
  obtain ⟨P, hP, rfl⟩ := D.mem_Pbar4.mp hR
  exact (D.parent_notInStopping D.hd (D.mem_PstIn4.mp hP).1 (D.PstIn4_ne_Q hP)).2

/-- A cube containing a sibling `P'` of `P ∈ 𝐏 ∩ 𝐏₄` with larger side length contains the
parent, hence contains `P`; by maximality of `P` this is impossible. [PROVED] -/
theorem sib_aux {P P' S : DyadicCube d} (hP : P ∈ D.stoppingCubes) (hP' : P'.toSet ⊆ P.parent.toSet)
    (hm : P.parent.m ≤ S.m) (hS : S ∈ D.P1 ∪ D.P2 ∪ D.P3 ∪ D.P4 ∪ D.P5)
    (hsub : P'.toSet ⊆ S.toSet) : False := by
  have hd := D.hd
  have hps : P.parent.toSet ⊆ S.toSet := by
    rcases DyadicCube.subset_or_disjoint P.parent S hm with h | h
    · exact h
    · exact absurd (hsub P'.corner_mem) (Set.disjoint_left.mp h (hP' P'.corner_mem))
  have hSP : S = P := hP.2 S hS (P.subset_parent.trans hps)
  rw [hSP] at hps
  have h2 := DyadicCube.m_le_of_subset hd hps
  rw [DyadicCube.parent_m] at h2
  omega

/-- The cubes of `𝐏₄'` lie in no cube of `𝐏₄`. [PROVED] -/
theorem Psib4_not_in_P4 {P' : DyadicCube d} (hP' : P' ∈ D.Psib4) :
    ∀ S ∈ D.P4, ¬ P'.toSet ⊆ S.toSet := by
  intro S hS hsub
  have hd := D.hd
  obtain ⟨⟨R, hR, hc⟩, hnot⟩ := D.mem_Psib4.mp hP'
  obtain ⟨P, hP, rfl⟩ := D.mem_Pbar4.mp hR
  obtain ⟨ε, rfl⟩ := mem_children.mp hc
  have hPs : P ∈ D.stoppingCubes := (D.mem_PstIn4.mp hP).1
  have hsubpar : (P.parent.child ε).toSet ⊆ P.parent.toSet := DyadicCube.child_subset _ _
  have hm' : (P.parent.child ε).m = P.m := by
    simp [DyadicCube.child, DyadicCube.parent]
  rcases le_or_gt P.parent.m S.m with hle | hlt
  · exact D.sib_aux hPs hsubpar hle (D.P4_subset hS) hsub
  · -- `S` has the side length of the sibling, so `S` is the sibling, which then lies in `𝐏`
    have hSm : S.m ≤ (P.parent.child ε).m := by
      rw [hm', DyadicCube.parent_m] at *
      omega
    have hSP' : P.parent.child ε = S :=
      DyadicCube.eq_of_subset_of_m_eq hsub (le_antisymm (DyadicCube.m_le_of_subset hd hsub) hSm)
    have hP'4 : P.parent.child ε ∈ D.P4 := by
      rw [hSP']
      exact hS
    obtain ⟨S', hS', hsub'⟩ := exists_maximal_superset hd D.union_subset_tree (D.P4_subset hP'4)
    have hS'eq : S' = P.parent.child ε := by
      by_contra hne
      have hlt' : (P.parent.child ε).m < S'.m := lt_of_le_of_ne
        (DyadicCube.m_le_of_subset hd hsub') fun h => hne (DyadicCube.eq_of_subset_of_m_eq hsub'
          h).symm
      exact D.sib_aux hPs hsubpar (by rw [DyadicCube.parent_m, ← hm']; omega) hS'.1 hsub'
    apply hnot
    rw [D.mem_PstIn4]
    exact ⟨hS'eq ▸ hS', hP'4⟩

theorem Psib4_mem_tree {P' : DyadicCube d} (hP' : P' ∈ D.Psib4) : P' ∈ D.tree := by
  obtain ⟨⟨R, hR, hc⟩, -⟩ := D.mem_Psib4.mp hP'
  obtain ⟨P, hP, rfl⟩ := D.mem_Pbar4.mp hR
  obtain ⟨ε, rfl⟩ := mem_children.mp hc
  refine ⟨(DyadicCube.child_subset _ _).trans (D.Pbar4_subset_Q hR), ?_⟩
  have hPt := D.stoppingCubes_subset_tree' (D.mem_PstIn4.mp hP).1
  have hm' : (P.parent.child ε).m = P.m := by
    simp [DyadicCube.child, DyadicCube.parent]
  rw [hm']
  exact hPt.2

/-- `[u]_P ≠ 0` on the cubes carrying a coefficient, by (2.11). [PROVED] -/
theorem avg_u_ne_zero {P : DyadicCube d} (hPt : P ∈ D.tree)
    (hP : ∀ S ∈ D.P4, ¬ P.toSet ⊆ S.toSet) : avg P D.u ≠ 0 := by
  intro h
  have := D.bound_2_11 D.hd hPt hP
  rw [h, abs_zero] at this
  norm_num at this

theorem coef_mul {P : DyadicCube d} (h : avg P D.u ≠ 0) :
    D.coef P * (avg P D.u * P.vol) = avg P D.G * P.vol := by
  unfold coef
  field_simp

/-- The children of distinct cubes are disjoint. [PROVED] -/
theorem children_pairwiseDisjoint (s : Finset (DyadicCube d)) :
    (↑s : Set (DyadicCube d)).PairwiseDisjoint children := by
  intro R _ R' _ hne
  rw [Function.onFun, Finset.disjoint_left]
  intro c hc hc'
  obtain ⟨ε, rfl⟩ := mem_children.mp hc
  obtain ⟨ε', h⟩ := mem_children.mp hc'
  exact hne (by rw [← R.parent_child ε, ← h, R'.parent_child])

theorem PstIn4_subset_biUnion : D.PstIn4 ⊆ D.Pbar4.biUnion children := by
  intro P hP
  rw [Finset.mem_biUnion]
  exact ⟨P.parent, Finset.mem_image_of_mem _ hP, mem_children.mpr ⟨_, P.child_parent⟩⟩

/-- `∑_{parents(P) ∈ parents(𝐏)₄} F(parents(P)) = ∑_{P ∈ 𝐏∩𝐏₄} F(P) + ∑_{P' ∈ 𝐏₄'} F(P')` for an
additive function `F`
of cubes (`F(R) = ∑_{children} F`): the children of the cubes of `parents(𝐏)₄` are exactly the
cubes of
`𝐏 ∩ 𝐏₄` and their siblings. [PROVED] -/
theorem sum_Pbar4_eq (F : DyadicCube d → ℝ) (hF : ∀ R, F R = ∑ c ∈ children R, F c) :
    ∑ R ∈ D.Pbar4, F R = ∑ P ∈ D.PstIn4, F P + ∑ P ∈ D.Psib4, F P := by
  classical
  rw [Finset.sum_congr rfl fun R _ => hF R, ← Finset.sum_biUnion (children_pairwiseDisjoint _),
    ← Finset.sum_filter_add_sum_filter_not (D.Pbar4.biUnion children) (· ∈ D.PstIn4)]
  congr 1
  exact Finset.sum_congr (Finset.filter_mem_eq_inter.trans
    (Finset.inter_eq_right.mpr D.PstIn4_subset_biUnion)) fun _ _ => rfl

/-- `[g]_R |R| = ∑_{children c} [g]_c |c|`. [PROVED] -/
theorem avg_mul_vol_children (R : DyadicCube d) (h : TestFun d) :
    avg R h * R.vol = ∑ c ∈ children R, avg c h * c.vol := by
  rw [children, Finset.sum_image fun ε _ ε' _ h => R.child_injective h]
  simp only [avg_mul_vol]
  exact R.integral_children (TestFun.integrable h.2).integrableOn

/-- **`[𝔤]_Q = 0`** (p. 43): the mean of `𝔤` over `Q` vanishes. [PROVED] -/
theorem pruned_meanZero : MeanZero (D.pruned : (Fin d → ℝ) → ℝ) := by
  change TestFun.integralₗ D.pruned = 0
  simp only [pruned, map_sub, map_add, map_sum, map_smul, smul_eq_mul,
    TestFun.integralₗ_truncateₗ]
  have hGQ : TestFun.integralₗ D.G = avg D.Q D.G * D.Q.vol := by
    rw [TestFun.integralₗ_apply, avg_mul_vol,
      setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => D.Gsupp x hx]
  have huQ : TestFun.integralₗ D.u = D.Q.vol := D.mean
  have hOut : ∀ P ∈ D.PstOut4, D.coef P * (avg P D.u * P.vol) = avg P D.G * P.vol := fun P hP =>
    D.coef_mul (D.avg_u_ne_zero (D.stoppingCubes_subset_tree' (D.mem_PstOut4.mp hP).1)
      (D.PstOut4_not_in_P4 hP))
  have hBar : ∀ P ∈ D.Pbar4, D.coef P * (avg P D.u * P.vol) = avg P D.G * P.vol := fun P hP =>
    D.coef_mul (D.avg_u_ne_zero (D.Pbar4_mem_tree hP) (D.Pbar4_not_in_P4 hP))
  have hSib : ∀ P ∈ D.Psib4, D.coef P * (avg P D.u * P.vol) = avg P D.G * P.vol := fun P hP =>
    D.coef_mul (D.avg_u_ne_zero (D.Psib4_mem_tree hP) (D.Psib4_not_in_P4 hP))
  have hkey := D.sum_Pbar4_eq (fun P => avg P D.G * P.vol) fun R => avg_mul_vol_children R D.G
  rw [Finset.sum_congr rfl hOut, Finset.sum_congr rfl hBar, Finset.sum_congr rfl hSib, hGQ, huQ,
    hkey]
  ring

/-! #### The norm bound `‖𝔤‖_q ≤ C ‖g‖_q` (p. 43)

The seven terms of (2.12) are estimated separately: `‖g‖_q`; `|[g]_Q| ‖u‖_q ≤ B^{1/q} ‖g‖_q`
(Hölder and (1.7)); `‖∑_{𝐏∖𝐏₄} g_P‖_q ≤ ‖g‖_q` and `‖∑_{𝐏∩𝐏₄} g_P‖_q ≤ ‖g‖_q` (disjointness);
and for the three sums `∑ ([g]_P/[u]_P) u_P` the bound `|[g]_P/[u]_P| ≤ 8 |[g]_P|` from (2.11),
`∫_P |u|^q ≤ 2^d B ε^{-1} |P|` from (2.9), Jensen's inequality `|[g]_P|^q |P| ≤ ∫_P |g|^q`, and
the overlap of the collection (`1` for `𝐏 ∖ 𝐏₄`, at most `2^d/ε` for `parents(𝐏)₄` and `𝐏₄'`, p.
45). -/

theorem good_of_mem_stoppingCubes {P : DyadicCube d} (hP : P ∈ D.stoppingCubes) : D.Good P := by
  refine ⟨D.stoppingCubes_subset_tree' hP, fun S hS ε hsub => ?_⟩
  have hSP : S = P := hP.2 S hS.1 (hsub.trans (DyadicCube.child_subset S ε))
  rw [hSP] at hsub
  have hm := DyadicCube.m_le_of_subset D.hd hsub
  have : (P.child ε).m = P.m - 1 := rfl
  omega

theorem good_of_notInStopping {P : DyadicCube d} (hPt : P ∈ D.tree) (h : D.NotInStopping P) :
    D.Good P :=
  ⟨hPt, fun S hS ε hsub => h S hS (hsub.trans (DyadicCube.child_subset S ε))⟩

theorem good_of_Pbar4 {R : DyadicCube d} (hR : R ∈ D.Pbar4) : D.Good R := by
  obtain ⟨P, hP, rfl⟩ := D.mem_Pbar4.mp hR
  have h := D.parent_notInStopping D.hd (D.mem_PstIn4.mp hP).1 (D.PstIn4_ne_Q hP)
  exact D.good_of_notInStopping h.2 h.1

theorem good_of_Psib4 {P' : DyadicCube d} (hP' : P' ∈ D.Psib4) : D.Good P' := by
  refine ⟨D.Psib4_mem_tree hP', fun S hS ε hsub => ?_⟩
  obtain ⟨⟨R, hR, hc⟩, -⟩ := D.mem_Psib4.mp hP'
  obtain ⟨P, hP, rfl⟩ := D.mem_Pbar4.mp hR
  obtain ⟨ε', rfl⟩ := mem_children.mp hc
  have hPs : P ∈ D.stoppingCubes := (D.mem_PstIn4.mp hP).1
  have hm := DyadicCube.m_le_of_subset D.hd hsub
  have h1 : (P.parent.child ε').m = P.m := by
    simp [DyadicCube.child, DyadicCube.parent]
  have h2 : (S.child ε).m = S.m - 1 := rfl
  exact D.sib_aux hPs (DyadicCube.child_subset _ _) (by rw [DyadicCube.parent_m]; omega) hS.1
    (hsub.trans (DyadicCube.child_subset S ε))

/-- `|[g]_P / [u]_P| ≤ 8 |[g]_P|` when `|[u]_P| > 1/8`. [PROVED] -/
theorem abs_coef_le {P : DyadicCube d} (h : 1 / 8 < |avg P D.u|) :
    |D.coef P| ≤ 8 * |avg P D.G| := by
  rw [coef, abs_div, div_le_iff₀ (by linarith)]
  have := mul_le_mul_of_nonneg_left h.le (by positivity : (0 : ℝ) ≤ 8 * |avg P D.G|)
  linarith

/-- `∫_P |u|^q ≤ 2^d B ε^{-1} |P|` on good cubes (from (2.9)). [PROVED] -/
theorem integral_u_rpow_le {P : DyadicCube d} (hP : D.Good P) :
    ∫ x in P.toSet, |(D.u : (Fin d → ℝ) → ℝ) x| ^ D.q ≤ 2 ^ d * D.B / D.ε * P.vol := by
  have hq0 : 0 < D.q := by linarith [D.hq]
  have hε := D.ε_pos
  have hB0 : 0 ≤ D.B := by linarith [D.hB]
  have hC0 : 0 ≤ 2 ^ d * D.B / D.ε := by positivity
  have hmeas : AEStronglyMeasurable (fun x => |(D.u : (Fin d → ℝ) → ℝ) x| ^ D.q)
      (volume.restrict P.toSet) :=
    (TestFun.integrable_abs_rpow D.u hq0).aestronglyMeasurable.restrict
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun x => by positivity) hmeas]
  have heq : ∫⁻ x in P.toSet, ENNReal.ofReal (|(D.u : (Fin d → ℝ) → ℝ) x| ^ D.q) =
      ∫⁻ x in P.toSet, ‖(D.u : (Fin d → ℝ) → ℝ) x‖ₑ ^ D.q :=
    lintegral_congr fun x => by
      rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hq0.le]
  rw [heq]
  apply ENNReal.toReal_le_of_le_ofReal (mul_nonneg hC0 P.vol_pos.le)
  have h := D.bound_2_9' D.hd hP
  have hV0 : volume P.toSet ≠ 0 := by
    rw [P.volume_toSet]
    exact (ENNReal.ofReal_pos.mpr P.vol_pos).ne'
  have hVt : volume P.toSet ≠ ⊤ := by
    rw [P.volume_toSet]
    exact ENNReal.ofReal_ne_top
  rw [← ENNReal.div_eq_inv_mul, ENNReal.div_le_iff hV0 hVt] at h
  rw [ENNReal.ofReal_mul hC0, ← P.volume_toSet]
  exact h

open Classical in
/-- **Bounded overlap of `parents(𝐏)₄`** (p. 45): a point lies in at most `2^d/ε` cubes of
`parents(𝐏)₄`. Otherwise
the smallest of the parents containing it would have the defining property of `𝐏₅`, hence lie in
a stopping cube strictly containing its child in `𝐏`, contradicting maximality. [PROVED] -/
theorem card_Pbar4_filter_le (x : Fin d → ℝ) :
    ((D.Pbar4.filter fun R => x ∈ R.toSet).card : ℝ) ≤ 2 ^ d / D.ε := by
  classical
  have hε := D.ε_pos
  by_contra hlt
  rw [not_le] at hlt
  set t := D.Pbar4.filter fun R => x ∈ R.toSet with ht
  have hne : t.Nonempty := by
    rw [← Finset.card_pos]
    have : (0 : ℝ) < t.card := lt_of_le_of_lt (by positivity) hlt
    exact_mod_cast this
  obtain ⟨R₀, hR₀, hmin⟩ := Finset.exists_min_image t (fun R => R.m) hne
  have hR₀' := Finset.mem_filter.mp hR₀
  obtain ⟨P₀, hP₀, hP₀R⟩ := D.mem_Pbar4.mp hR₀'.1
  subst hP₀R
  have hPs : P₀ ∈ D.stoppingCubes := (D.mem_PstIn4.mp hP₀).1
  have hprop : ∃ S : Finset (DyadicCube d), (2 : ℝ) ^ d / D.ε ≤ S.card ∧
      ∀ R ∈ S, (∃ P' ∈ D.P4, R = P'.parent) ∧ P₀.parent.toSet ⊆ R.toSet := by
    refine ⟨t, hlt.le, fun R hR => ⟨?_, ?_⟩⟩
    · obtain ⟨P, hP, hPR⟩ := D.mem_Pbar4.mp (Finset.mem_filter.mp hR).1
      exact ⟨P, (D.mem_PstIn4.mp hP).2, hPR.symm⟩
    · rcases DyadicCube.subset_or_disjoint P₀.parent R (hmin R hR) with h | h
      · exact h
      · exact absurd (Finset.mem_filter.mp hR).2 (Set.disjoint_left.mp h hR₀'.2)
  obtain ⟨S₅, hS₅, hsub⟩ := exists_maximal_superset D.hd
    (S := {P ∈ D.tree | ∃ S : Finset (DyadicCube d), (2 : ℝ) ^ d / D.ε ≤ S.card ∧
      ∀ R ∈ S, (∃ P' ∈ D.P4, R = P'.parent) ∧ P.toSet ⊆ R.toSet})
    (fun _ h => D.tree_subset h.1) ⟨D.Pbar4_mem_tree hR₀'.1, hprop⟩
  have hS₅u : S₅ ∈ D.P1 ∪ D.P2 ∪ D.P3 ∪ D.P4 ∪ D.P5 := Or.inr hS₅
  have hSP : S₅ = P₀ := hPs.2 S₅ hS₅u (P₀.subset_parent.trans hsub)
  rw [hSP] at hsub
  have hm := DyadicCube.m_le_of_subset D.hd hsub
  rw [DyadicCube.parent_m] at hm
  omega

open Classical in
/-- **Bounded overlap of `𝐏₄'`** (p. 45): distinct siblings containing a point have distinct
parents, so the overlap of `𝐏₄'` is at most that of `parents(𝐏)₄`. [PROVED] -/
theorem card_Psib4_filter_le (x : Fin d → ℝ) :
    ((D.Psib4.filter fun P' => x ∈ P'.toSet).card : ℝ) ≤ 2 ^ d / D.ε := by
  classical
  refine le_trans ?_ (D.card_Pbar4_filter_le x)
  have hmaps : Set.MapsTo DyadicCube.parent
      (↑(D.Psib4.filter fun P' => x ∈ P'.toSet) : Set (DyadicCube d))
      (↑(D.Pbar4.filter fun R => x ∈ R.toSet) : Set (DyadicCube d)) := by
    intro P' hP'
    rw [Finset.mem_coe, Finset.mem_filter] at hP' ⊢
    obtain ⟨⟨R, hR, hc⟩, -⟩ := D.mem_Psib4.mp hP'.1
    obtain ⟨ε, rfl⟩ := mem_children.mp hc
    rw [R.parent_child]
    exact ⟨hR, (DyadicCube.child_subset R ε) hP'.2⟩
  have hinj : Set.InjOn DyadicCube.parent
      (↑(D.Psib4.filter fun P' => x ∈ P'.toSet) : Set (DyadicCube d)) := by
    intro P₁ hP₁ P₂ hP₂ h
    rw [Finset.mem_coe, Finset.mem_filter] at hP₁ hP₂
    have hm : P₁.m = P₂.m := by
      have := congrArg DyadicCube.m h
      simp only [DyadicCube.parent_m] at this
      omega
    rcases DyadicCube.eq_or_disjoint_of_m_eq P₁ P₂ hm with h' | h'
    · exact h'
    · exact absurd hP₂.2 (Set.disjoint_left.mp h' hP₁.2)
  exact_mod_cast Finset.card_le_card_of_injOn DyadicCube.parent hmaps hinj

open Classical in
/-- The common estimate for the three coefficient sums of (2.12): for a collection `s` of good
cubes with `|[u]_P| > 1/8` and overlap at most `M`,
`‖∑_{P ∈ s} ([g]_P/[u]_P) u_P‖_q ≤ 8 (2^d B/ε)^{1/q} M ‖g‖_q`. [PROVED] -/
theorem lpNorm_sum_coef_le (s : Finset (DyadicCube d)) {M : ℕ}
    (hM : ∀ x, (s.filter fun P => x ∈ P.toSet).card ≤ M) (hgood : ∀ P ∈ s, D.Good P)
    (hu : ∀ P ∈ s, 1 / 8 < |avg P D.u|) {S : DyadicCube d} (hS : ∀ P ∈ s, P.toSet ⊆ S.toSet) :
    lpNorm ((∑ P ∈ s, D.coef P • TestFun.truncateₗ P D.u : TestFun d) : (Fin d → ℝ) → ℝ) D.q ≤
      8 * (2 ^ d * D.B / D.ε) ^ (1 / D.q) * M *
        lpNorm (TestFun.truncateₗ S D.G : (Fin d → ℝ) → ℝ) D.q := by
  have hq := D.hq
  have hq0 : 0 < D.q := by linarith
  have hq1 : 1 ≤ D.q := hq.le
  have hε := D.ε_pos
  have hB0 : 0 ≤ D.B := by linarith [D.hB]
  set C₉ : ℝ := 2 ^ d * D.B / D.ε with hC₉
  have hC₉0 : 0 ≤ C₉ := by positivity
  set N := lpNorm (TestFun.truncateₗ S D.G : (Fin d → ℝ) → ℝ) D.q with hN
  have hN0 : 0 ≤ N := ENNReal.toReal_nonneg
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hterm : ∀ P ∈ s, |D.coef P| ^ D.q * ∫ x in P.toSet, |(D.u : (Fin d → ℝ) → ℝ) x| ^ D.q ≤
      8 ^ D.q * C₉ * (|avg P D.G| ^ D.q * P.vol) := by
    intro P hP
    have h1 : |D.coef P| ^ D.q ≤ (8 * |avg P D.G|) ^ D.q :=
      Real.rpow_le_rpow (abs_nonneg _) (D.abs_coef_le (hu P hP)) hq0.le
    have h2 := D.integral_u_rpow_le (hgood P hP)
    calc |D.coef P| ^ D.q * ∫ x in P.toSet, |(D.u : (Fin d → ℝ) → ℝ) x| ^ D.q
        ≤ (8 * |avg P D.G|) ^ D.q * (C₉ * P.vol) :=
          mul_le_mul h1 h2 (integral_nonneg fun x => by positivity) (by positivity)
      _ = 8 ^ D.q * C₉ * (|avg P D.G| ^ D.q * P.vol) := by
          rw [Real.mul_rpow (by norm_num) (abs_nonneg _)]
          ring
  have hMq : (M : ℝ) ^ (D.q - 1) * M = (M : ℝ) ^ D.q := by
    rw [← Real.rpow_add_one' hM0 (by linarith : D.q - 1 + 1 ≠ 0), sub_add_cancel]
  have hE : (8 * C₉ ^ (1 / D.q) * (M : ℝ) * N) ^ D.q = 8 ^ D.q * C₉ * (M : ℝ) ^ D.q * N ^ D.q := by
    rw [Real.mul_rpow (by positivity) hN0, Real.mul_rpow (by positivity) hM0,
      Real.mul_rpow (by norm_num) (Real.rpow_nonneg hC₉0 _), ← Real.rpow_mul hC₉0,
      one_div_mul_cancel hq0.ne', Real.rpow_one]
  have hpow : lpNorm ((∑ P ∈ s, D.coef P • TestFun.truncateₗ P D.u : TestFun d) :
      (Fin d → ℝ) → ℝ) D.q ^ D.q ≤ (8 * C₉ ^ (1 / D.q) * (M : ℝ) * N) ^ D.q := by
    calc lpNorm ((∑ P ∈ s, D.coef P • TestFun.truncateₗ P D.u : TestFun d) :
          (Fin d → ℝ) → ℝ) D.q ^ D.q
        ≤ (M : ℝ) ^ (D.q - 1) *
            ∑ P ∈ s, |D.coef P| ^ D.q * ∫ x in P.toSet, |(D.u : (Fin d → ℝ) → ℝ) x| ^ D.q :=
          lpNorm_sum_smul_truncateₗ_rpow_le s hM D.coef D.u hq1
      _ ≤ (M : ℝ) ^ (D.q - 1) * ∑ P ∈ s, 8 ^ D.q * C₉ * (|avg P D.G| ^ D.q * P.vol) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) (Real.rpow_nonneg hM0 _)
      _ = (8 ^ D.q * C₉ * (M : ℝ) ^ (D.q - 1)) * ∑ P ∈ s, |avg P D.G| ^ D.q * P.vol := by
          rw [← Finset.mul_sum]
          ring
      _ ≤ (8 ^ D.q * C₉ * (M : ℝ) ^ (D.q - 1)) *
            ∑ P ∈ s, ∫ x in P.toSet, |(D.G : (Fin d → ℝ) → ℝ) x| ^ D.q :=
          mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum fun P _ => abs_avg_rpow_mul_vol_le P D.G hq1) (by positivity)
      _ = (8 ^ D.q * C₉ * (M : ℝ) ^ (D.q - 1)) *
            ∑ P ∈ s, ∫ x in P.toSet, |(TestFun.truncateₗ S D.G : (Fin d → ℝ) → ℝ) x| ^ D.q := by
          rw [Finset.sum_congr rfl fun P hP => TestFun.setIntegral_rpow_truncateₗ_eq (hS P hP) D.G
            D.q]
      _ ≤ (8 ^ D.q * C₉ * (M : ℝ) ^ (D.q - 1)) *
            (M * ∫ x, |(TestFun.truncateₗ S D.G : (Fin d → ℝ) → ℝ) x| ^ D.q) :=
          mul_le_mul_of_nonneg_left (sum_setIntegral_le_of_overlap s hM _ hq0) (by positivity)
      _ = (8 * C₉ ^ (1 / D.q) * (M : ℝ) * N) ^ D.q := by
          rw [hE, ← lpNorm_rpow_eq_integral hq0 (TestFun.memLp (TestFun.truncateₗ S D.G).2 _),
            ← hN, ← hMq]
          ring
  exact (Real.rpow_le_rpow_iff ENNReal.toReal_nonneg (by positivity) hq0).mp hpow

/-- The constant in the norm bound for `𝔤`: `3 + B^{1/q} + 8 (2^d B/ε)^{1/q} (1 + 2 ⌊2^d/ε⌋)`. -/
noncomputable def pruneConst : ℝ :=
  3 + D.B ^ (1 / D.q) + 8 * (2 ^ d * D.B / D.ε) ^ (1 / D.q) * (1 + 2 * ⌊(2 : ℝ) ^ d / D.ε⌋₊)

/-- **The norm bound `‖𝔤‖_q ≤ C ‖g‖_q`** (p. 43), with `C = pruneConst` depending only on
`d`, `B` and the exponents. [PROVED] -/
theorem pruned_lpNorm_le :
    lpNorm (D.pruned : (Fin d → ℝ) → ℝ) D.q ≤ D.pruneConst * lpNorm (D.G : (Fin d → ℝ) → ℝ) D.q :=
      by
  have hq := D.hq
  have hq0 : 0 < D.q := by linarith
  classical
  have hq1 : 1 ≤ D.q := hq.le
  have hε := D.ε_pos
  have hB0 : 0 ≤ D.B := by linarith [D.hB]
  have hV := D.Q.vol_pos
  set N := lpNorm (D.G : (Fin d → ℝ) → ℝ) D.q with hN
  have hN0 : 0 ≤ N := ENNReal.toReal_nonneg
  set M := ⌊(2 : ℝ) ^ d / D.ε⌋₊ with hM
  set C₉ : ℝ := 2 ^ d * D.B / D.ε with hC₉
  have hC₉0 : 0 ≤ C₉ := by positivity
  -- overlap bounds
  have hM4 : ∀ x, (D.Pbar4.filter fun R => x ∈ R.toSet).card ≤ M := fun x =>
    Nat.le_floor (D.card_Pbar4_filter_le x)
  have hM4' : ∀ x, (D.Psib4.filter fun R => x ∈ R.toSet).card ≤ M := fun x =>
    Nat.le_floor (D.card_Psib4_filter_le x)
  have hdisjOut : (↑D.PstOut4 : Set (DyadicCube d)).PairwiseDisjoint DyadicCube.toSet :=
    fun P hP R hR hne => maximal_pairwiseDisjoint _ (D.mem_PstOut4.mp hP).1
      (D.mem_PstOut4.mp hR).1 hne
  have hdisjIn : (↑D.PstIn4 : Set (DyadicCube d)).PairwiseDisjoint DyadicCube.toSet :=
    fun P hP R hR hne => maximal_pairwiseDisjoint _ (D.mem_PstIn4.mp hP).1
      (D.mem_PstIn4.mp hR).1 hne
  have hM1 : ∀ x, (D.PstOut4.filter fun P => x ∈ P.toSet).card ≤ 1 := fun x =>
    Finset.card_le_one.mpr fun P hP R hR => by
      rw [Finset.mem_filter] at hP hR
      by_contra hne
      exact Set.disjoint_left.mp (hdisjOut hP.1 hR.1 hne) hP.2 hR.2
  -- the seven terms
  set S₁ : TestFun d := ∑ P ∈ D.PstOut4, TestFun.truncateₗ P D.G with hS₁
  set S₂ : TestFun d := ∑ P ∈ D.PstOut4, D.coef P • TestFun.truncateₗ P D.u with hS₂
  set S₃ : TestFun d := ∑ P ∈ D.PstIn4, TestFun.truncateₗ P D.G with hS₃
  set S₄ : TestFun d := ∑ P ∈ D.Pbar4, D.coef P • TestFun.truncateₗ P D.u with hS₄
  set S₅ : TestFun d := ∑ P ∈ D.Psib4, D.coef P • TestFun.truncateₗ P D.u with hS₅
  have h1 : lpNorm ((avg D.Q D.G • D.u : TestFun d) : (Fin d → ℝ) → ℝ) D.q ≤ D.B ^ (1 / D.q) * N :=
    by
    rw [TestFun.lpNorm_smul]
    have hG := abs_avg_le D.Q D.G hq1
    have hu : lpNorm (D.u : (Fin d → ℝ) → ℝ) D.q ≤ (D.B * D.Q.vol) ^ (1 / D.q) := by
      have h2 : lpNorm (D.u : (Fin d → ℝ) → ℝ) D.q ^ D.q ≤ D.B * D.Q.vol :=
        (lpNorm_rpow_eq_integral hq0 (TestFun.memLp D.u.2 _)).trans_le D.norm
      calc lpNorm (D.u : (Fin d → ℝ) → ℝ) D.q
          = (lpNorm (D.u : (Fin d → ℝ) → ℝ) D.q ^ D.q) ^ (1 / D.q) := by
            rw [one_div]
            exact (Real.rpow_rpow_inv ENNReal.toReal_nonneg hq0.ne').symm
        _ ≤ (D.B * D.Q.vol) ^ (1 / D.q) :=
            Real.rpow_le_rpow (Real.rpow_nonneg ENNReal.toReal_nonneg _) h2 (by positivity)
    have hone : D.Q.vol ^ (-(1 / D.q)) * D.Q.vol ^ (1 / D.q) = 1 := by
      rw [← Real.rpow_add hV, neg_add_cancel, Real.rpow_zero]
    calc |avg D.Q D.G| * lpNorm (D.u : (Fin d → ℝ) → ℝ) D.q
        ≤ (D.Q.vol ^ (-(1 / D.q)) * N) * (D.B * D.Q.vol) ^ (1 / D.q) :=
          mul_le_mul hG hu ENNReal.toReal_nonneg (by positivity)
      _ = (D.Q.vol ^ (-(1 / D.q)) * D.Q.vol ^ (1 / D.q)) * (D.B ^ (1 / D.q) * N) := by
          rw [Real.mul_rpow hB0 hV.le]
          ring
      _ = D.B ^ (1 / D.q) * N := by rw [hone, one_mul]
  have h2 : lpNorm (S₁ : (Fin d → ℝ) → ℝ) D.q ≤ N := lpNorm_sum_truncateₗ_le D.PstOut4 hdisjOut D.G
    hq1
  have h4 : lpNorm (S₃ : (Fin d → ℝ) → ℝ) D.q ≤ N := lpNorm_sum_truncateₗ_le D.PstIn4 hdisjIn D.G
    hq1
  have hGQ : TestFun.truncateₗ D.Q D.G = D.G := TestFun.truncateₗ_of_supportedOn D.Gsupp
  have h3 : lpNorm (S₂ : (Fin d → ℝ) → ℝ) D.q ≤ 8 * C₉ ^ (1 / D.q) * N := by
    have := D.lpNorm_sum_coef_le D.PstOut4 hM1
      (fun P hP => D.good_of_mem_stoppingCubes (D.mem_PstOut4.mp hP).1)
      (fun P hP => D.bound_2_11 D.hd (D.stoppingCubes_subset_tree' (D.mem_PstOut4.mp hP).1)
        (D.PstOut4_not_in_P4 hP)) (S := D.Q)
      (fun P hP => D.Pst_subset_Q (Finset.mem_of_mem_filter P hP))
    rwa [Nat.cast_one, mul_one, hGQ] at this
  have h5 : lpNorm (S₄ : (Fin d → ℝ) → ℝ) D.q ≤ 8 * C₉ ^ (1 / D.q) * M * N := by
    have := D.lpNorm_sum_coef_le D.Pbar4 hM4 (fun P hP => D.good_of_Pbar4 hP)
      (fun P hP => D.bound_2_11 D.hd (D.Pbar4_mem_tree hP) (D.Pbar4_not_in_P4 hP)) (S := D.Q)
      (fun P hP => D.Pbar4_subset_Q hP)
    rwa [hGQ] at this
  have h6 : lpNorm (S₅ : (Fin d → ℝ) → ℝ) D.q ≤ 8 * C₉ ^ (1 / D.q) * M * N := by
    have := D.lpNorm_sum_coef_le D.Psib4 hM4' (fun P hP => D.good_of_Psib4 hP)
      (fun P hP => D.bound_2_11 D.hd (D.Psib4_mem_tree hP) (D.Psib4_not_in_P4 hP)) (S := D.Q)
      (fun P hP => D.Psib4_subset_Q hP)
    rwa [hGQ] at this
  -- the triangle inequality
  have t1 := TestFun.lpNorm_sub_le (D.G - avg D.Q D.G • D.u - S₁ + S₂ - S₃ + S₄) S₅ hq1
  have t2 := TestFun.lpNorm_add_le (D.G - avg D.Q D.G • D.u - S₁ + S₂ - S₃) S₄ hq1
  have t3 := TestFun.lpNorm_sub_le (D.G - avg D.Q D.G • D.u - S₁ + S₂) S₃ hq1
  have t4 := TestFun.lpNorm_add_le (D.G - avg D.Q D.G • D.u - S₁) S₂ hq1
  have t5 := TestFun.lpNorm_sub_le (D.G - avg D.Q D.G • D.u) S₁ hq1
  have t6 := TestFun.lpNorm_sub_le D.G (avg D.Q D.G • D.u) hq1
  have hpr : D.pruned = D.G - avg D.Q D.G • D.u - S₁ + S₂ - S₃ + S₄ - S₅ := rfl
  rw [hpr]
  calc lpNorm ((D.G - avg D.Q D.G • D.u - S₁ + S₂ - S₃ + S₄ - S₅ : TestFun d) :
        (Fin d → ℝ) → ℝ) D.q
      ≤ N + lpNorm ((avg D.Q D.G • D.u : TestFun d) : (Fin d → ℝ) → ℝ) D.q +
          lpNorm (S₁ : (Fin d → ℝ) → ℝ) D.q + lpNorm (S₂ : (Fin d → ℝ) → ℝ) D.q +
          lpNorm (S₃ : (Fin d → ℝ) → ℝ) D.q + lpNorm (S₄ : (Fin d → ℝ) → ℝ) D.q +
          lpNorm (S₅ : (Fin d → ℝ) → ℝ) D.q := by linarith
    _ ≤ N + D.B ^ (1 / D.q) * N + N + 8 * C₉ ^ (1 / D.q) * N + N +
          8 * C₉ ^ (1 / D.q) * M * N + 8 * C₉ ^ (1 / D.q) * M * N :=
        add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add le_rfl h1) h2) h3)
          h4) h5) h6
    _ = D.pruneConst * N := by
        unfold pruneConst
        ring

/-! #### The expansion (2.15)–(2.17) of `g − 𝔤` and the first terms of (2.13) (p. 43–44)

`g − 𝔤 = [g]_Q u + ∑_{P ∈ 𝐏} (g_P − [g]_P b_P) + ∑_{P ∈ 𝐏∖𝐏₄} ([g]_P b_P − ([g]_P/[u]_P) u_P)
         + ∑_{P ∈ 𝐏∩𝐏₄} [g]_P b_P − ∑_{P ∈ parents(𝐏)₄} ([g]_P/[u]_P) u_P + ∑_{P ∈ 𝐏₄'}
         ([g]_P/[u]_P) u_P`
with `b_P = b_{σ,𝐐_P,k+1}`. We write `Λ_P(ρ, ρ') = twoSlotForm T a b g P ρ ρ'`, `h_P = 𝟙_P`, and
`F_P = ∏_{j ≠ k,k+1} ‖f_j 𝟙_P‖_{p_j}`. -/

/-- `Λ_P(ρ, ρ')` for the data `D`. -/
noncomputable def form2 (P : DyadicCube d) (ρ ρ' : TestFun d) : ℝ :=
  twoSlotForm D.T D.a D.b D.g P ρ ρ'

/-- `F_P = ∏_{j ≠ k,k+1} ‖f_j 𝟙_P‖_{p_j}`. -/
noncomputable def FP (P : DyadicCube d) : ℝ :=
  ∏ j ∈ D.J, lpNorm (TestFun.truncateₗ P (D.g j) : (Fin d → ℝ) → ℝ) (D.p.p j)

theorem FP_nonneg (P : DyadicCube d) : 0 ≤ D.FP P :=
  Finset.prod_nonneg fun _ _ => ENNReal.toReal_nonneg

/-- `∑_{P ∈ 𝐏} = ∑_{P ∈ 𝐏∖𝐏₄} + ∑_{P ∈ 𝐏∩𝐏₄}`. [PROVED] -/
theorem sum_Pst_eq (F : DyadicCube d → TestFun d) :
    ∑ P ∈ D.Pst, F P = ∑ P ∈ D.PstOut4, F P + ∑ P ∈ D.PstIn4, F P := by
  rw [PstOut4, PstIn4, add_comm, Finset.sum_filter_add_sum_filter_not]

/-- **The expansion (2.15)–(2.17)** of `g − 𝔤`. [PROVED] -/
theorem sub_pruned_eq : D.G - D.pruned =
    avg D.Q D.G • D.u
    + ∑ P ∈ D.Pst, (TestFun.truncateₗ P D.G - avg P D.G • D.bP P)
    + ∑ P ∈ D.PstOut4, (avg P D.G • D.bP P - D.coef P • TestFun.truncateₗ P D.u)
    + ∑ P ∈ D.PstIn4, avg P D.G • D.bP P
    - ∑ P ∈ D.Pbar4, D.coef P • TestFun.truncateₗ P D.u
    + ∑ P ∈ D.Psib4, D.coef P • TestFun.truncateₗ P D.u := by
  rw [D.sum_Pst_eq]
  unfold pruned
  simp only [Finset.sum_sub_distrib]
  abel

/-- `Λ_Q(𝟙_Q, u)` is bounded by the testing condition: `|Λ_Q(h, u)| ≤ B F ‖u‖_q |Q|^{1/r}`.
[PROVED] -/
theorem form2_hQ_u_le :
    |D.form2 D.Q (TestFun.ind D.Q) D.u| ≤
      D.B * D.F * lpNorm (D.u : (Fin d → ℝ) → ℝ) D.q * D.Q.vol ^ (1 / D.r) := by
  rw [form2, twoSlotForm_self D.T D.hab]
  have := D.testing (TestFun.ind D.Q) (fun x hx => Set.indicator_of_notMem hx _)
  rwa [TestFun.lpNorm_ind D.Q (by linarith [D.hr])] at this

/-- `‖u‖_q ≤ (B |Q|)^{1/q}`. [PROVED] -/
theorem lpNorm_u_le : lpNorm (D.u : (Fin d → ℝ) → ℝ) D.q ≤ (D.B * D.Q.vol) ^ (1 / D.q) := by
  have hq0 : 0 < D.q := by linarith [D.hq]
  have h2 : lpNorm (D.u : (Fin d → ℝ) → ℝ) D.q ^ D.q ≤ D.B * D.Q.vol :=
    (lpNorm_rpow_eq_integral hq0 (TestFun.memLp D.u.2 _)).trans_le D.norm
  calc lpNorm (D.u : (Fin d → ℝ) → ℝ) D.q
      = (lpNorm (D.u : (Fin d → ℝ) → ℝ) D.q ^ D.q) ^ (1 / D.q) := by
        rw [one_div]
        exact (Real.rpow_rpow_inv ENNReal.toReal_nonneg hq0.ne').symm
    _ ≤ (D.B * D.Q.vol) ^ (1 / D.q) :=
        Real.rpow_le_rpow (Real.rpow_nonneg ENNReal.toReal_nonneg _) h2 (by positivity)

/-- **The first term of (2.15)** (p. 43): `|Λ_Q(h, [g]_Q u)| ≤ B^{1+1/q} F ‖g‖_q ‖h‖_r`, where
`‖h‖_r = |Q|^{1/r}`. [PROVED] -/
theorem form2_hQ_avg_u_le :
    |D.form2 D.Q (TestFun.ind D.Q) (avg D.Q D.G • D.u)| ≤
      D.B ^ (1 + 1 / D.q) * D.F * lpNorm (D.G : (Fin d → ℝ) → ℝ) D.q * D.Q.vol ^ (1 / D.r) := by
  have hq1 : 1 ≤ D.q := D.hq.le
  have hB0 : 0 ≤ D.B := by linarith [D.hB]
  have hV := D.Q.vol_pos
  have hF0 : 0 ≤ D.F := D.Fpos'.le
  rw [form2, twoSlotForm_smul_right, ← form2, abs_mul]
  have hG := abs_avg_le D.Q D.G hq1
  have hone : D.Q.vol ^ (-(1 / D.q)) * D.Q.vol ^ (1 / D.q) = 1 := by
    rw [← Real.rpow_add hV, neg_add_cancel, Real.rpow_zero]
  calc |avg D.Q D.G| * |D.form2 D.Q (TestFun.ind D.Q) D.u|
      ≤ (D.Q.vol ^ (-(1 / D.q)) * lpNorm (D.G : (Fin d → ℝ) → ℝ) D.q) *
          (D.B * D.F * (D.B * D.Q.vol) ^ (1 / D.q) * D.Q.vol ^ (1 / D.r)) := by
        refine mul_le_mul hG (D.form2_hQ_u_le.trans ?_) (abs_nonneg _)
          (mul_nonneg (Real.rpow_nonneg hV.le _) ENNReal.toReal_nonneg)
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left D.lpNorm_u_le
          (mul_nonneg hB0 hF0)) (Real.rpow_nonneg hV.le _)
    _ = (D.Q.vol ^ (-(1 / D.q)) * D.Q.vol ^ (1 / D.q)) *
          (D.B ^ (1 + 1 / D.q) * D.F * lpNorm (D.G : (Fin d → ℝ) → ℝ) D.q * D.Q.vol ^ (1 / D.r)) :=
            by
        rw [Real.mul_rpow hB0 hV.le, Real.rpow_add' hB0 (by positivity), Real.rpow_one]
        ring
    _ = _ := by rw [hone, one_mul]

/-- The entries of `Λ_Q(h, g)`: `f_j 𝟙_Q` for `j ≠ k, k+1`, `𝟙_Q` in the slot `k` and `g` in the
slot `k+1`. -/
noncomputable def entries : Fin n → TestFun d :=
  Function.update (Function.update D.g D.a (TestFun.ind D.Q)) D.b D.G

/-- `∑_{P ∈ 𝐏} |P| ≤ (1 - ε)|Q|`, the claim (2.7) as a finite sum. [PROVED] -/
theorem sum_Pst_vol_le : ∑ P ∈ D.Pst, P.vol ≤ (1 - D.ε) * D.Q.vol := by
  have hdisj : (↑D.Pst : Set (DyadicCube d)).PairwiseDisjoint DyadicCube.toSet :=
    fun P hP R hR hne => maximal_pairwiseDisjoint _ (D.mem_Pst.mp hP) (D.mem_Pst.mp hR) hne
  have h1 : volume (⋃ P ∈ D.Pst, P.toSet) = ∑ P ∈ D.Pst, volume P.toSet :=
    measure_biUnion_finset hdisj fun P _ => P.measurableSet_toSet
  have hU : (⋃ P ∈ D.Pst, P.toSet) = ⋃ P ∈ D.stoppingCubes, P.toSet := by
    ext x
    simp only [Set.mem_iUnion, exists_prop, D.mem_Pst]
  have h2 := D.volume_stoppingCubes_le
  rw [← hU, h1] at h2
  simp only [DyadicCube.volume_toSet] at h2
  rwa [← ENNReal.ofReal_sum_of_nonneg fun P _ => P.vol_pos.le,
    ENNReal.ofReal_le_ofReal_iff (mul_nonneg (by linarith [D.ε_le]) D.Q.vol_pos.le)] at h2

/-- `∑_{P ∈ 𝐏} ∫_P |f|^q ≤ ∫ |f|^q` for a dyadic test function `f`. [PROVED] -/
theorem sum_Pst_setIntegral_le (f : TestFun d) {q : ℝ} (hq : 0 < q) :
    ∑ P ∈ D.Pst, ∫ x in P.toSet, |(f : (Fin d → ℝ) → ℝ) x| ^ q ≤
      ∫ x, |(f : (Fin d → ℝ) → ℝ) x| ^ q := by
  have hdisj : (↑D.Pst : Set (DyadicCube d)).PairwiseDisjoint DyadicCube.toSet :=
    fun P hP R hR hne => maximal_pairwiseDisjoint _ (D.mem_Pst.mp hP) (D.mem_Pst.mp hR) hne
  rw [← integral_biUnion_finset D.Pst (fun P _ => P.measurableSet_toSet) hdisj
    (fun P _ => (TestFun.integrable_abs_rpow f hq).integrableOn)]
  exact setIntegral_le_integral (TestFun.integrable_abs_rpow f hq)
    (Filter.Eventually.of_forall fun x => by positivity)

/-- The weight `W(P) = F_P |P|^{1/r} ‖g 𝟙_P‖_q = ∏_j ‖e_j 𝟙_P‖_{p_j}`, the product of the norms of
the entries of `Λ_P(h, g)`. -/
noncomputable def W (P : DyadicCube d) : ℝ :=
  D.FP P * P.vol ^ (1 / D.r) * lpNorm (TestFun.truncateₗ P D.G : (Fin d → ℝ) → ℝ) D.q

theorem W_nonneg (P : DyadicCube d) : 0 ≤ D.W P :=
  mul_nonneg (mul_nonneg (D.FP_nonneg P) (Real.rpow_nonneg P.vol_pos.le _)) ENNReal.toReal_nonneg

/-- `∑_{P ∈ S} |P| ≤ M |Q|` for a collection of subcubes of `Q` with overlap `M`. [PROVED] -/
theorem sum_vol_le_of_overlap (S : Finset (DyadicCube d)) (hS : ∀ P ∈ S, P.toSet ⊆ D.Q.toSet)
    {M : ℝ} (hM : ∀ f : TestFun d, ∀ q : ℝ, 0 < q →
      ∑ P ∈ S, ∫ x in P.toSet, |(f : (Fin d → ℝ) → ℝ) x| ^ q ≤
        M * ∫ x, |(f : (Fin d → ℝ) → ℝ) x| ^ q) :
    ∑ P ∈ S, P.vol ≤ M * D.Q.vol := by
  have h := hM (TestFun.ind D.Q) 1 one_pos
  simp only [Real.rpow_one] at h
  have h2 : ∫ x, |((TestFun.ind D.Q : TestFun d) : (Fin d → ℝ) → ℝ) x| = D.Q.vol := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun x hx => by rw [TestFun.coe_ind, Set.indicator_of_notMem hx, abs_zero])]
    exact TestFun.setIntegral_abs_ind (subset_refl _)
  rwa [Finset.sum_congr rfl fun P hP => TestFun.setIntegral_abs_ind (hS P hP), h2] at h

/-- **Hölder's inequality over a collection of cubes** (p. 44–45): for a collection `S` of
subcubes of `Q` with overlap `M` and `∑_{P ∈ S} |P| ≤ V`,
`∑_{P ∈ S} W(P) ≤ V^{1/r} M^{1 - 1/r} F ‖g‖_q`. [PROVED] -/
theorem sum_W_le (S : Finset (DyadicCube d)) (hS : ∀ P ∈ S, P.toSet ⊆ D.Q.toSet)
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ f : TestFun d, ∀ q : ℝ, 0 < q →
      ∑ P ∈ S, ∫ x in P.toSet, |(f : (Fin d → ℝ) → ℝ) x| ^ q ≤
        M * ∫ x, |(f : (Fin d → ℝ) → ℝ) x| ^ q)
    {V : ℝ} (hV : ∑ P ∈ S, P.vol ≤ V) :
    ∑ P ∈ S, D.W P ≤
      V ^ (1 / D.r) * M ^ (1 - 1 / D.r) * D.F * lpNorm (D.G : (Fin d → ℝ) → ℝ) D.q := by
  have hab := D.hab
  have hr0 : 0 < D.r := by linarith [D.hr]
  have hpj : ∀ j, 0 < D.p.p j := fun j => by linarith [D.p.one_lt j]
  -- the weights `w j P = ‖e_j 𝟙_P‖_{p_j}`, with `e` the entries of `Λ_Q(h, g)`
  set w : Fin n → DyadicCube d → ℝ := fun j P =>
    lpNorm (TestFun.truncateₗ P (D.entries j) : (Fin d → ℝ) → ℝ) (D.p.p j) with hw
  have hw0 : ∀ j P, 0 ≤ w j P := fun j P => ENNReal.toReal_nonneg
  have hwa : ∀ P ∈ S, w D.a P = P.vol ^ (1 / D.r) := by
    intro P hP
    simp only [hw, entries, Function.update_of_ne hab, Function.update_self]
    rw [TestFun.truncateₗ_ind_of_subset (hS P hP), TestFun.lpNorm_ind P hr0]
  have hwb : ∀ P, w D.b P = lpNorm (TestFun.truncateₗ P D.G : (Fin d → ℝ) → ℝ) D.q := by
    intro P
    simp [hw, entries]
  have hwj : ∀ j ∈ D.J, ∀ P,
      w j P = lpNorm (TestFun.truncateₗ P (D.g j) : (Fin d → ℝ) → ℝ) (D.p.p j) := by
    intro j hj P
    rw [J, Finset.mem_erase, Finset.mem_erase] at hj
    simp [hw, entries, Function.update_of_ne hj.1, Function.update_of_ne hj.2.1]
  have hJ : (Finset.univ.erase D.b).erase D.a = D.J := by
    rw [J, Finset.erase_right_comm]
  -- the product of the weights at `P` is `W(P)`
  have hprod : ∀ P ∈ S, ∏ j, w j P = D.W P := by
    intro P hP
    rw [← Finset.mul_prod_erase Finset.univ (fun j => w j P) (Finset.mem_univ D.b),
      ← Finset.mul_prod_erase (Finset.univ.erase D.b) (fun j => w j P)
        (Finset.mem_erase.mpr ⟨hab, Finset.mem_univ D.a⟩), hwb, hwa P hP, hJ,
      Finset.prod_congr rfl fun j hj => hwj j hj P]
    unfold W FP
    ring
  -- Hölder's inequality over the cubes
  have hp1 : ∑ j, 1 / D.p.p j = 1 := by
    simp only [one_div]
    exact D.p.sum_inv
  have hholder := sum_prod_le_prod_sum_rpow S Finset.univ D.p.p (fun j _ => hpj j) hp1 w
    (fun j _ P _ => hw0 j P)
  -- the sums of the `p_j`-th powers
  have hsum : ∀ j, ∑ P ∈ S, w j P ^ D.p.p j ≤
      if j = D.a then V
      else M * lpNorm (D.entries j : (Fin d → ℝ) → ℝ) (D.p.p j) ^ D.p.p j := by
    intro j
    by_cases hja : j = D.a
    · subst hja
      rw [ite_eq_left rfl]
      refine le_of_eq_of_le (Finset.sum_congr rfl fun P hP => ?_) hV
      rw [hwa P hP, ← Real.rpow_mul P.vol_pos.le, one_div_mul_cancel hr0.ne', Real.rpow_one]
    · rw [ite_eq_right hja]
      simp only [hw]
      rw [Finset.sum_congr rfl fun P _ => TestFun.lpNorm_truncateₗ_rpow P (D.entries j) (hpj j),
        lpNorm_rpow_eq_integral (hpj j) (TestFun.memLp (D.entries j).2 _)]
      exact hM (D.entries j) (D.p.p j) (hpj j)
  -- assemble
  have hprodle : ∏ j, (∑ P ∈ S, w j P ^ D.p.p j) ^ (1 / D.p.p j) ≤
      ∏ j, (if j = D.a then V
        else M * lpNorm (D.entries j : (Fin d → ℝ) → ℝ) (D.p.p j) ^ D.p.p j) ^ (1 / D.p.p j) :=
    Finset.prod_le_prod₀ (fun j _ => Real.rpow_nonneg (Finset.sum_nonneg fun P _ =>
      Real.rpow_nonneg (hw0 j P) _) _)
      fun j _ => Real.rpow_le_rpow (Finset.sum_nonneg fun P _ => Real.rpow_nonneg (hw0 j P) _)
        (hsum j) (by have := hpj j; positivity)
  have hsum_erase : ∑ j ∈ Finset.univ.erase D.a, (D.p.p j)⁻¹ = 1 - 1 / D.r := by
    have := Finset.add_sum_erase Finset.univ (fun j => (D.p.p j)⁻¹) (Finset.mem_univ D.a)
    rw [D.p.sum_inv] at this
    rw [one_div]
    linarith
  have hprodeq : ∏ j, (if j = D.a then V
      else M * lpNorm (D.entries j : (Fin d → ℝ) → ℝ) (D.p.p j) ^ D.p.p j) ^ (1 / D.p.p j) =
      V ^ (1 / D.r) * M ^ (1 - 1 / D.r) * D.F * lpNorm (D.G : (Fin d → ℝ) → ℝ) D.q := by
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ D.a), ite_eq_left rfl]
    have hrest : ∏ j ∈ Finset.univ.erase D.a, (if j = D.a then V
        else M * lpNorm (D.entries j : (Fin d → ℝ) → ℝ) (D.p.p j) ^ D.p.p j) ^ (1 / D.p.p j) =
        ∏ j ∈ Finset.univ.erase D.a,
          M ^ (D.p.p j)⁻¹ * lpNorm (D.entries j : (Fin d → ℝ) → ℝ) (D.p.p j) := by
      refine Finset.prod_congr rfl fun j hj => ?_
      rw [ite_eq_right (Finset.mem_erase.mp hj).1,
        Real.mul_rpow hM0 (Real.rpow_nonneg (lpNorm_nonneg _ _) _), one_div,
        Real.rpow_rpow_inv (lpNorm_nonneg _ _) (hpj j).ne']
    have hb : lpNorm (D.entries D.b : (Fin d → ℝ) → ℝ) (D.p.p D.b) =
        lpNorm (D.G : (Fin d → ℝ) → ℝ) D.q := by simp [entries]
    have hrest2 : ∏ j ∈ (Finset.univ.erase D.a).erase D.b,
        lpNorm (D.entries j : (Fin d → ℝ) → ℝ) (D.p.p j) = D.F := by
      unfold F
      refine Finset.prod_congr rfl fun j hj => ?_
      rw [J, Finset.mem_erase, Finset.mem_erase] at hj
      have he : D.entries j = D.g j := by
        simp [entries, Function.update_of_ne hj.1, Function.update_of_ne hj.2.1]
      rw [he]
    rw [hrest, Finset.prod_mul_distrib,
      ← Real.rpow_sum_of_nonneg hM0 (fun j _ => inv_nonneg.mpr (hpj j).le), hsum_erase,
      ← Finset.mul_prod_erase (Finset.univ.erase D.a) _
        (Finset.mem_erase.mpr ⟨Ne.symm hab, Finset.mem_univ D.b⟩), hb, hrest2]
    ring
  calc ∑ P ∈ S, D.W P = ∑ P ∈ S, ∏ j, w j P := Finset.sum_congr rfl fun P hP => (hprod P hP).symm
    _ ≤ ∏ j, (∑ P ∈ S, w j P ^ D.p.p j) ^ (1 / D.p.p j) := hholder
    _ ≤ _ := hprodle.trans_eq hprodeq

/-- The overlap hypothesis for the pairwise disjoint collection `𝐏` (`M = 1`). -/
theorem overlap_Pst (f : TestFun d) (q : ℝ) (hq : 0 < q) :
    ∑ P ∈ D.Pst, ∫ x in P.toSet, |(f : (Fin d → ℝ) → ℝ) x| ^ q ≤
      1 * ∫ x, |(f : (Fin d → ℝ) → ℝ) x| ^ q := by
  rw [one_mul]
  exact D.sum_Pst_setIntegral_le f hq

/-- `∑_{P ∈ 𝐏} W(P) ≤ ((1-ε)|Q|)^{1/r} F ‖g‖_q`. [PROVED] -/
theorem sum_W_Pst_le : ∑ P ∈ D.Pst, D.W P ≤
    ((1 - D.ε) * D.Q.vol) ^ (1 / D.r) * D.F * lpNorm (D.G : (Fin d → ℝ) → ℝ) D.q := by
  have h := D.sum_W_le D.Pst (fun P hP => D.Pst_subset_Q hP) zero_le_one D.overlap_Pst
    D.sum_Pst_vol_le
  rwa [Real.one_rpow, mul_one] at h

/-- `|Λ_P(h, g)| ≤ A W(P)`: the estimate (2.1) for the data `σ'`, `𝐐_P`. [PROVED] -/
theorem abs_form2_hP_G_le {P : DyadicCube d} (hPQ : P.toSet ⊆ D.Q.toSet) :
    |D.form2 P (TestFun.ind P) (TestFun.truncateₗ P D.G)| ≤ D.A * D.W P := by
  have := D.estimateA P hPQ (TestFun.truncateₗ P D.G) (TestFun.truncateₗ_supportedOn P D.G)
  unfold form2
  refine this.trans (le_of_eq ?_)
  unfold W FP
  ring

/-- **The `A`-term of (2.18)** (p. 44): by the estimate (2.1) for the data `σ'`, `𝐐_P`, Hölder's
inequality over the stopping cubes and the claim (2.7),
`∑_{P ∈ 𝐏} |Λ_P(h, g)| ≤ A F ((1-ε)|Q|)^{1/r} ‖g‖_q`. This is the term carrying the
contraction factor `(1-ε)^{1/r}`. [PROVED] -/
theorem sum_form2_hP_G_le :
    ∑ P ∈ D.Pst, |D.form2 P (TestFun.ind P) (TestFun.truncateₗ P D.G)| ≤
      D.A * D.F * ((1 - D.ε) * D.Q.vol) ^ (1 / D.r) * lpNorm (D.G : (Fin d → ℝ) → ℝ) D.q := by
  calc ∑ P ∈ D.Pst, |D.form2 P (TestFun.ind P) (TestFun.truncateₗ P D.G)|
      ≤ ∑ P ∈ D.Pst, D.A * D.W P :=
        Finset.sum_le_sum fun P hP => D.abs_form2_hP_G_le (D.Pst_subset_Q hP)
    _ = D.A * ∑ P ∈ D.Pst, D.W P := by rw [Finset.mul_sum]
    _ ≤ D.A * (((1 - D.ε) * D.Q.vol) ^ (1 / D.r) * D.F * lpNorm (D.G : (Fin d → ℝ) → ℝ) D.q) :=
        mul_le_mul_of_nonneg_left D.sum_W_Pst_le D.hA0
    _ = _ := by ring

/-! #### The remaining terms of (2.13): (2.18), (2.19), (2.20) (p. 44–45) -/

theorem form2_smul_right (P : DyadicCube d) (ρ : TestFun d) (c : ℝ) (ρ' : TestFun d) :
    D.form2 P ρ (c • ρ') = c * D.form2 P ρ ρ' :=
  twoSlotForm_smul_right D.T D.a D.b D.g P ρ c ρ'

theorem form2_add_right (P : DyadicCube d) (ρ ρ₁ ρ₂ : TestFun d) :
    D.form2 P ρ (ρ₁ + ρ₂) = D.form2 P ρ ρ₁ + D.form2 P ρ ρ₂ :=
  twoSlotForm_add_right D.T D.a D.b D.g P ρ ρ₁ ρ₂

theorem form2_sub_right (P : DyadicCube d) (ρ ρ₁ ρ₂ : TestFun d) :
    D.form2 P ρ (ρ₁ - ρ₂) = D.form2 P ρ ρ₁ - D.form2 P ρ ρ₂ :=
  twoSlotForm_sub_right D.T D.a D.b D.g P ρ ρ₁ ρ₂

theorem form2_sum_right {ι : Type*} (P : DyadicCube d) (ρ : TestFun d) (s : Finset ι)
    (f : ι → TestFun d) : D.form2 P ρ (∑ i ∈ s, f i) = ∑ i ∈ s, D.form2 P ρ (f i) :=
  twoSlotForm_sum_right D.T D.a D.b D.g P ρ s f

theorem form2_sub_left (P : DyadicCube d) (ρ₁ ρ₂ ρ' : TestFun d) :
    D.form2 P (ρ₁ - ρ₂) ρ' = D.form2 P ρ₁ ρ' - D.form2 P ρ₂ ρ' :=
  twoSlotForm_sub_left D.T D.hab D.g P ρ₁ ρ₂ ρ'

theorem form2_truncateₗ_right (P : DyadicCube d) (ρ ρ' : TestFun d) :
    D.form2 P ρ (TestFun.truncateₗ P ρ') = D.form2 P ρ ρ' :=
  twoSlotForm_truncateₗ_right D.T D.a D.b D.g P ρ ρ'

theorem form2_truncateₗ_left (P : DyadicCube d) (ρ ρ' : TestFun d) :
    D.form2 P (TestFun.truncateₗ P ρ) ρ' = D.form2 P ρ ρ' :=
  twoSlotForm_truncateₗ_left D.T D.a D.b D.g P ρ ρ'

/-- `Λ_P(h, ρ') = Λ_P(𝟙_P, ρ')` for `P ⊆ Q`, since `h 𝟙_P = 𝟙_P`. [PROVED] -/
theorem form2_ind_left {P : DyadicCube d} (hPQ : P.toSet ⊆ D.Q.toSet) (ρ' : TestFun d) :
    D.form2 P (TestFun.ind D.Q) ρ' = D.form2 P (TestFun.ind P) ρ' := by
  rw [← D.form2_truncateₗ_left P (TestFun.ind D.Q) ρ', TestFun.truncateₗ_ind_of_subset hPQ]

/-- The smoothness step: `Λ_Q(ρ, ρ') = Λ_P(ρ, ρ')` for `ρ'` supported on `P ⊆ Q` with mean zero. -/
theorem form2_eq_of_subset {P R : DyadicCube d} (hPR : P.toSet ⊆ R.toSet) (ρ : TestFun d)
    {ρ' : TestFun d} (hρ' : SupportedOn ρ' P) (hρ0 : MeanZero (ρ' : (Fin d → ℝ) → ℝ)) :
    D.form2 R ρ ρ' = D.form2 P ρ ρ' :=
  (twoSlotForm_eq_of_subset D.T D.a D.b D.g hPR ρ hρ' hρ0).symm

/-- `Λ_P(ρ, u) = Λ_P(·, u)(ρ)`. -/
theorem form2_u (P : DyadicCube d) (ρ : TestFun d) :
    D.form2 P ρ D.u = slotForm D.T D.a D.g P ρ :=
  twoSlotForm_self D.T D.hab D.g P ρ

/-- `‖b_{σ,𝐐_P,k+1}‖_q ≤ (B|P|)^{1/q}` from (1.7). [PROVED] -/
theorem lpNorm_bP_le {P : DyadicCube d} (hPQ : P.toSet ⊆ D.Q.toSet) :
    lpNorm (D.bP P : (Fin d → ℝ) → ℝ) D.q ≤ (D.B * P.vol) ^ (1 / D.q) :=
  TestFun.lpNorm_le_rpow_of_integral_le (D.bP P) (by linarith [D.hq]) (D.bP_norm P hPQ)

/-- `‖b_{τ,𝐐_P,k}‖_r ≤ (B|P|)^{1/r}` from (1.7). [PROVED] -/
theorem lpNorm_vP_le {P : DyadicCube d} (hPQ : P.toSet ⊆ D.Q.toSet) :
    lpNorm (D.vP P : (Fin d → ℝ) → ℝ) D.r ≤ (D.B * P.vol) ^ (1 / D.r) :=
  TestFun.lpNorm_le_rpow_of_integral_le (D.vP P) (by linarith [D.hr]) (D.vP_norm P hPQ)

/-- `‖u 𝟙_P‖_q ≤ (2^d B ε^{-1} |P|)^{1/q}` on good cubes, from (2.9). [PROVED] -/
theorem lpNorm_truncateₗ_u_le {P : DyadicCube d} (hP : D.Good P) :
    lpNorm (TestFun.truncateₗ P D.u : (Fin d → ℝ) → ℝ) D.q ≤
      (2 ^ d * D.B / D.ε * P.vol) ^ (1 / D.q) := by
  have hq0 : 0 < D.q := by linarith [D.hq]
  refine TestFun.lpNorm_le_rpow_of_integral_le (TestFun.truncateₗ P D.u) hq0 ?_
  rw [← lpNorm_rpow_eq_integral hq0 (TestFun.memLp (TestFun.truncateₗ P D.u).2 _),
    TestFun.lpNorm_truncateₗ_rpow P D.u hq0]
  exact D.integral_u_rpow_le hP

/-- **The second term of (2.18)** (p. 44), for one cube: by the testing condition (1.9) for `σ`,
`𝐐_P`, `‖b_P‖_q ≤ (B|P|)^{1/q}` and `|[g]_P| |P|^{1/q} ≤ ‖g_P‖_q`,
`|[g]_P Λ_P(h, b_P)| ≤ B^{1+1/q} W(P)`. [PROVED] -/
theorem abs_avg_mul_form2_hP_bP_le {P : DyadicCube d} (hPQ : P.toSet ⊆ D.Q.toSet) :
    |avg P D.G * D.form2 P (TestFun.ind P) (D.bP P)| ≤ D.B ^ (1 + 1 / D.q) * D.W P := by
  have hq1 : 1 ≤ D.q := D.hq.le
  have hr0 : 0 < D.r := by linarith [D.hr]
  have hB0 : 0 ≤ D.B := by linarith [D.hB]
  have hV := P.vol_pos
  have hF0 := D.FP_nonneg P
  have ht := D.testing_bP P hPQ (TestFun.ind P) (fun x hx => Set.indicator_of_notMem hx _)
  rw [TestFun.lpNorm_ind P hr0] at ht
  have hb := D.lpNorm_bP_le hPQ
  have hg := abs_avg_mul_rpow_le P D.G hq1
  rw [abs_mul]
  calc |avg P D.G| * |D.form2 P (TestFun.ind P) (D.bP P)|
      ≤ |avg P D.G| * (D.B * D.FP P * (D.B * P.vol) ^ (1 / D.q) * P.vol ^ (1 / D.r)) := by
        refine mul_le_mul_of_nonneg_left (ht.trans ?_) (abs_nonneg _)
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb (mul_nonneg hB0 hF0))
          (Real.rpow_nonneg hV.le _)
    _ = D.B ^ (1 + 1 / D.q) * (D.FP P * P.vol ^ (1 / D.r)) * (|avg P D.G| * P.vol ^ (1 / D.q)) := by
        rw [Real.mul_rpow hB0 hV.le, Real.rpow_add' hB0 (by positivity), Real.rpow_one]
        ring
    _ ≤ D.B ^ (1 + 1 / D.q) * (D.FP P * P.vol ^ (1 / D.r)) *
          lpNorm (TestFun.truncateₗ P D.G : (Fin d → ℝ) → ℝ) D.q := by gcongr
    _ = D.B ^ (1 + 1 / D.q) * D.W P := by
        unfold W
        ring

/-- The constant of the first term of (2.20): `K₁ = 8 B^{1+1/r} (2^d B/ε)^{1/q}`. -/
noncomputable def K₁ : ℝ := 8 * D.B ^ (1 + 1 / D.r) * (2 ^ d * D.B / D.ε) ^ (1 / D.q)

/-- The constant of the second term of (2.20): `K₂ = 16 · 2^d B^{1+1/r+1/q} / ε`. -/
noncomputable def K₂ : ℝ := 16 * 2 ^ d * D.B ^ (1 + 1 / D.r + 1 / D.q) / D.ε

theorem K₁_nonneg : 0 ≤ D.K₁ := by
  have hB0 : 0 ≤ D.B := by linarith [D.hB]
  have hε := D.ε_pos
  unfold K₁
  positivity

theorem K₂_nonneg : 0 ≤ D.K₂ := by
  have hB0 : 0 ≤ D.B := by linarith [D.hB]
  have hε := D.ε_pos
  unfold K₂
  positivity

/-- **The first term of (2.20)** (p. 44), for one cube `P` not contained in a cube of `𝐏₄`: by the
testing condition (1.9) for `τ`, `𝐐_P`, `‖b_{τ,𝐐_P,k}‖_r ≤ (B|P|)^{1/r}`, (2.9) for `‖u_P‖_q`,
(2.11) for `|[g]_P/[u]_P| ≤ 8|[g]_P|` and Jensen's inequality,
`|c_P Λ_P(b_{τ,𝐐_P,k}, u)| ≤ K₁ W(P)`. [PROVED] -/
theorem abs_coef_mul_form2_vP_u_le {P : DyadicCube d} (hPt : P ∈ D.tree) (hgood : D.Good P)
    (hP4 : ∀ S ∈ D.P4, ¬ P.toSet ⊆ S.toSet) :
    |D.coef P * D.form2 P (D.vP P) D.u| ≤ D.K₁ * D.W P := by
  have hq1 : 1 ≤ D.q := D.hq.le
  have hq0 : 0 < D.q := by linarith
  have hr0 : 0 < D.r := by linarith [D.hr]
  have hB0 : 0 ≤ D.B := by linarith [D.hB]
  have hε := D.ε_pos
  have hV := P.vol_pos
  have hF0 := D.FP_nonneg P
  have hPQ : P.toSet ⊆ D.Q.toSet := hPt.1
  have ht := D.testing_vP P hPQ (TestFun.truncateₗ P D.u) (TestFun.truncateₗ_supportedOn P D.u)
  have hc := D.abs_coef_le (D.bound_2_11 D.hd hPt hP4)
  have hg := abs_avg_mul_rpow_le P D.G hq1
  have hv := D.lpNorm_vP_le hPQ
  have hu := D.lpNorm_truncateₗ_u_le hgood
  rw [← D.form2_truncateₗ_right, abs_mul]
  calc |D.coef P| * |D.form2 P (D.vP P) (TestFun.truncateₗ P D.u)|
      ≤ (8 * |avg P D.G|) *
          (D.B * D.FP P * (D.B * P.vol) ^ (1 / D.r) * (2 ^ d * D.B / D.ε * P.vol) ^ (1 / D.q)) := by
        refine mul_le_mul hc (ht.trans ?_) (abs_nonneg _) (by positivity)
        exact mul_le_mul (mul_le_mul_of_nonneg_left hv (mul_nonneg hB0 hF0)) hu
          (lpNorm_nonneg _ _) (mul_nonneg (mul_nonneg hB0 hF0)
            (Real.rpow_nonneg (mul_nonneg hB0 hV.le) _))
    _ = D.K₁ * (D.FP P * P.vol ^ (1 / D.r)) * (|avg P D.G| * P.vol ^ (1 / D.q)) := by
        unfold K₁
        rw [Real.mul_rpow hB0 hV.le, Real.mul_rpow (by positivity) hV.le,
          Real.rpow_add' hB0 (by positivity), Real.rpow_one]
        ring
    _ ≤ D.K₁ * (D.FP P * P.vol ^ (1 / D.r)) *
          lpNorm (TestFun.truncateₗ P D.G : (Fin d → ℝ) → ℝ) D.q := by
        have := D.K₁_nonneg
        gcongr
    _ = D.K₁ * D.W P := by
        unfold W
        ring

/-- The exponent bookkeeping for the second term of (2.20). [PROVED] -/
theorem rpow_algebra_2_20 {v V r q : ℝ} (hv : 0 < v) (hV : 0 < V) :
    v ^ (-(1 / q)) * V ^ (1 / q) * (v / V) ^ (1 - 1 / r) * v ^ (1 / r) =
      v ^ (1 - 1 / q) * V ^ (1 / r + 1 / q - 1) := by
  rw [Real.div_rpow hv.le hV.le, div_eq_mul_inv (v ^ (1 - 1 / r)) (V ^ (1 - 1 / r)),
    ← Real.rpow_neg hV.le, show (1 - 1 / q : ℝ) = -(1 / q) + (1 - 1 / r) + 1 / r by ring,
    show (1 / r + 1 / q - 1 : ℝ) = 1 / q + -(1 - 1 / r) by ring,
    Real.rpow_add hv, Real.rpow_add hv, Real.rpow_add hV]
  ring

/-- `|[g]_P| ≤ ‖g_P‖_q |P|^{-1/q}`. [PROVED] -/
theorem abs_avg_le_lpNorm_mul (P : DyadicCube d) :
    |avg P D.G| ≤ lpNorm (TestFun.truncateₗ P D.G : (Fin d → ℝ) → ℝ) D.q * P.vol ^ (-(1 / D.q)) :=
      by
  have hV := P.vol_pos
  have h := abs_avg_mul_rpow_le P D.G D.hq.le
  rw [Real.rpow_neg hV.le, ← div_eq_mul_inv, le_div_iff₀ (Real.rpow_pos_of_pos hV _)]
  exact h

/-- **The second term of (2.20)** (p. 45), for one good cube `P` not contained in a cube of `𝐏₄`:
by (2.10) applied to `h_P − b_{τ,𝐐_P,k}` (supported on `P`, mean zero), (1.7), (2.11) and Jensen,
`|c_P Λ_P(h_P − b_{τ,𝐐_P,k}, u)| ≤ K₂ F ‖g_P‖_q |P|^{1-1/q} |Q|^{1/r+1/q-1}`. [PROVED] -/
theorem abs_coef_mul_form2_hP_sub_vP_u_le {P : DyadicCube d} (hPt : P ∈ D.tree)
    (hgood : D.Good P) (hP4 : ∀ S ∈ D.P4, ¬ P.toSet ⊆ S.toSet) :
    |D.coef P * D.form2 P (TestFun.ind P - D.vP P) D.u| ≤
      D.K₂ * D.F * (lpNorm (TestFun.truncateₗ P D.G : (Fin d → ℝ) → ℝ) D.q *
        P.vol ^ (1 - 1 / D.q)) * D.Q.vol ^ (1 / D.r + 1 / D.q - 1) := by
  have hq1 : 1 ≤ D.q := D.hq.le
  have hq0 : 0 < D.q := by linarith
  have hr1 : 1 ≤ D.r := D.hr.le
  have hr0 : 0 < D.r := by linarith
  have hB1 := D.hB
  have hB0 : 0 ≤ D.B := by linarith
  have hε := D.ε_pos
  have hv := P.vol_pos
  have hV := D.Q.vol_pos
  have hF0 := D.Fpos'.le
  have hPQ : P.toSet ⊆ D.Q.toSet := hPt.1
  have hc := D.abs_coef_le (D.bound_2_11 D.hd hPt hP4)
  have hg := D.abs_avg_le_lpNorm_mul P
  -- The mean-zero difference is supported on P and has Lr norm at most
  -- twice B^(1/r) times the corresponding power of the cube's volume.
  set ρ : TestFun d := TestFun.ind P - D.vP P with hρ
  have hρs : SupportedOn (ρ : (Fin d → ℝ) → ℝ) P := fun x hx => by
    rw [hρ, Submodule.coe_sub, Pi.sub_apply, TestFun.coe_ind, Set.indicator_of_notMem hx,
      D.vP_supp P hPQ x hx, sub_zero]
  have hρ0 : MeanZero (ρ : (Fin d → ℝ) → ℝ) := by
    change TestFun.integralₗ ρ = 0
    rw [hρ, map_sub, TestFun.integralₗ_apply, TestFun.integralₗ_apply, TestFun.integral_ind,
      D.vP_mean P hPQ, sub_self]
  have hρn : lpNorm (ρ : (Fin d → ℝ) → ℝ) D.r ≤ 2 * D.B ^ (1 / D.r) * P.vol ^ (1 / D.r) := by
    have h1 : P.vol ^ (1 / D.r) ≤ (D.B * P.vol) ^ (1 / D.r) :=
      Real.rpow_le_rpow hv.le (le_mul_of_one_le_left hv.le hB1) (by positivity)
    calc lpNorm (ρ : (Fin d → ℝ) → ℝ) D.r
        ≤ lpNorm ((TestFun.ind P : TestFun d) : (Fin d → ℝ) → ℝ) D.r +
            lpNorm (D.vP P : (Fin d → ℝ) → ℝ) D.r := TestFun.lpNorm_sub_le _ _ hr1
      _ ≤ (D.B * P.vol) ^ (1 / D.r) + (D.B * P.vol) ^ (1 / D.r) := by
          rw [TestFun.lpNorm_ind P hr0]
          exact add_le_add h1 (D.lpNorm_vP_le hPQ)
      _ = 2 * D.B ^ (1 / D.r) * P.vol ^ (1 / D.r) := by
          rw [Real.mul_rpow hB0 hv.le]
          ring
  have hu := D.lpNorm_u_le
  have h10 := D.bound_2_10 D.hd hgood ρ hρs hρ0
  have hL0 : 0 ≤ lpNorm (TestFun.truncateₗ P D.G : (Fin d → ℝ) → ℝ) D.q := lpNorm_nonneg _ _
  have hρ0' : 0 ≤ lpNorm (ρ : (Fin d → ℝ) → ℝ) D.r := lpNorm_nonneg _ _
  have hu0 : 0 ≤ lpNorm (D.u : (Fin d → ℝ) → ℝ) D.q := lpNorm_nonneg _ _
  have hεi : 0 ≤ D.ε⁻¹ := inv_nonneg.mpr hε.le
  rw [D.form2_u, abs_mul]
  calc |D.coef P| * |slotForm D.T D.a D.g P ρ|
      ≤ (8 * (lpNorm (TestFun.truncateₗ P D.G : (Fin d → ℝ) → ℝ) D.q * P.vol ^ (-(1 / D.q)))) *
          (2 ^ d * (D.B * D.F * (D.B * D.Q.vol) ^ (1 / D.q) * D.ε⁻¹) *
            (P.vol / D.Q.vol) ^ (1 - 1 / D.r) * (2 * D.B ^ (1 / D.r) * P.vol ^ (1 / D.r))) := by
        refine mul_le_mul (hc.trans (by gcongr)) (h10.trans ?_) (abs_nonneg _) (by positivity)
        gcongr
    _ = D.K₂ * D.F * (lpNorm (TestFun.truncateₗ P D.G : (Fin d → ℝ) → ℝ) D.q *
          (P.vol ^ (-(1 / D.q)) * D.Q.vol ^ (1 / D.q) * (P.vol / D.Q.vol) ^ (1 - 1 / D.r) *
            P.vol ^ (1 / D.r))) := by
        unfold K₂
        rw [Real.mul_rpow hB0 hV.le, Real.rpow_add' hB0 (by positivity),
          Real.rpow_add' hB0 (by positivity), Real.rpow_one]
        ring
    _ = _ := by rw [rpow_algebra_2_20 hv hV]; ring

/-- **The estimate (2.20)** (p. 44–45) for one cube: adding and subtracting `b_{τ,𝐐_P,k}` in the
slot `k`, `|c_P Λ_P(h, u)| ≤ K₁ W(P) + K₂ F ‖g_P‖_q |P|^{1-1/q} |Q|^{1/r+1/q-1}`. [PROVED] -/
theorem abs_coef_mul_form2_hP_u_le {P : DyadicCube d} (hPt : P ∈ D.tree) (hgood : D.Good P)
    (hP4 : ∀ S ∈ D.P4, ¬ P.toSet ⊆ S.toSet) :
    |D.coef P * D.form2 P (TestFun.ind P) D.u| ≤
      D.K₁ * D.W P + D.K₂ * D.F * (lpNorm (TestFun.truncateₗ P D.G : (Fin d → ℝ) → ℝ) D.q *
        P.vol ^ (1 - 1 / D.q)) * D.Q.vol ^ (1 / D.r + 1 / D.q - 1) := by
  have hsplit : D.form2 P (TestFun.ind P) D.u =
      D.form2 P (D.vP P) D.u + D.form2 P (TestFun.ind P - D.vP P) D.u := by
    rw [D.form2_sub_left, add_sub_cancel]
  rw [hsplit, mul_add]
  exact (abs_add_le _ _).trans (add_le_add (D.abs_coef_mul_form2_vP_u_le hPt hgood hP4)
    (D.abs_coef_mul_form2_hP_sub_vP_u_le hPt hgood hP4))

/-- **Hölder's inequality with two exponents over a collection of cubes**:
`∑_{P ∈ S} ‖g_P‖_q |P|^{1-1/q} ≤ M ‖g‖_q |Q|^{1-1/q}` for a collection `S` of subcubes of `Q`
with overlap `M`. [PROVED] -/
theorem sum_lpNorm_mul_vol_rpow_le (S : Finset (DyadicCube d))
    (hS : ∀ P ∈ S, P.toSet ⊆ D.Q.toSet) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ f : TestFun d, ∀ q : ℝ, 0 < q →
      ∑ P ∈ S, ∫ x in P.toSet, |(f : (Fin d → ℝ) → ℝ) x| ^ q ≤
        M * ∫ x, |(f : (Fin d → ℝ) → ℝ) x| ^ q) :
    ∑ P ∈ S, lpNorm (TestFun.truncateₗ P D.G : (Fin d → ℝ) → ℝ) D.q * P.vol ^ (1 - 1 / D.q) ≤
      M * lpNorm (D.G : (Fin d → ℝ) → ℝ) D.q * D.Q.vol ^ (1 - 1 / D.q) := by
  have hq := D.hq
  have hq0 : 0 < D.q := by linarith
  have hV := D.Q.vol_pos
  have hc : D.q.HolderConjugate D.q.conjExponent := Real.HolderConjugate.conjExponent hq
  obtain ⟨-, hsum⟩ := Real.holderConjugate_iff.mp hc
  set q' := D.q.conjExponent with hq'
  have hq'inv : q'⁻¹ = 1 - 1 / D.q := by
    rw [one_div]
    linarith
  have h1q : 0 < 1 - 1 / D.q := sub_pos.mpr ((div_lt_one hq0).mpr hq)
  have hq'pos : 0 < q' := inv_pos.mp (hq'inv ▸ h1q)
  have hexp : (1 - 1 / D.q) * q' = 1 := by
    rw [← hq'inv]
    exact inv_mul_cancel₀ hq'pos.ne'
  have h := Real.inner_le_Lp_mul_Lq_of_nonneg S hc
    (f := fun P => lpNorm (TestFun.truncateₗ P D.G : (Fin d → ℝ) → ℝ) D.q)
    (g := fun P => P.vol ^ (1 - 1 / D.q)) (fun _ _ => lpNorm_nonneg _ _)
    (fun P _ => Real.rpow_nonneg P.vol_pos.le _)
  refine h.trans ?_
  have hA : ∑ P ∈ S, lpNorm (TestFun.truncateₗ P D.G : (Fin d → ℝ) → ℝ) D.q ^ D.q ≤
      M * lpNorm (D.G : (Fin d → ℝ) → ℝ) D.q ^ D.q := by
    rw [Finset.sum_congr rfl fun P _ => TestFun.lpNorm_truncateₗ_rpow P D.G hq0,
      lpNorm_rpow_eq_integral hq0 (TestFun.memLp D.G.2 _)]
    exact hM D.G D.q hq0
  have hB : ∑ P ∈ S, (P.vol ^ (1 - 1 / D.q)) ^ q' ≤ M * D.Q.vol := by
    rw [Finset.sum_congr rfl fun P _ => by
      rw [← Real.rpow_mul P.vol_pos.le, hexp, Real.rpow_one]]
    exact D.sum_vol_le_of_overlap S hS hM
  have hA' : (∑ P ∈ S, lpNorm (TestFun.truncateₗ P D.G : (Fin d → ℝ) → ℝ) D.q ^ D.q) ^ (1 / D.q)
      ≤ M ^ (1 / D.q) * lpNorm (D.G : (Fin d → ℝ) → ℝ) D.q := by
    refine (Real.rpow_le_rpow (Finset.sum_nonneg fun P _ => Real.rpow_nonneg (lpNorm_nonneg _ _) _)
      hA (by positivity)).trans (le_of_eq ?_)
    rw [Real.mul_rpow hM0 (Real.rpow_nonneg (lpNorm_nonneg _ _) _), one_div,
      Real.rpow_rpow_inv (lpNorm_nonneg _ _) hq0.ne']
  have hB' : (∑ P ∈ S, (P.vol ^ (1 - 1 / D.q)) ^ q') ^ (1 / q') ≤
      M ^ (1 - 1 / D.q) * D.Q.vol ^ (1 - 1 / D.q) := by
    refine (Real.rpow_le_rpow (Finset.sum_nonneg fun P _ => Real.rpow_nonneg
      (Real.rpow_nonneg P.vol_pos.le _) _) hB (one_div_nonneg.mpr hq'pos.le)).trans
      (le_of_eq ?_)
    rw [Real.mul_rpow hM0 hV.le, one_div, hq'inv]
  calc (∑ P ∈ S, lpNorm (TestFun.truncateₗ P D.G : (Fin d → ℝ) → ℝ) D.q ^ D.q) ^ (1 / D.q) *
        (∑ P ∈ S, (P.vol ^ (1 - 1 / D.q)) ^ q') ^ (1 / q')
      ≤ (M ^ (1 / D.q) * lpNorm (D.G : (Fin d → ℝ) → ℝ) D.q) *
          (M ^ (1 - 1 / D.q) * D.Q.vol ^ (1 - 1 / D.q)) :=
        mul_le_mul hA' hB' (Real.rpow_nonneg (Finset.sum_nonneg fun P _ => Real.rpow_nonneg
          (Real.rpow_nonneg P.vol_pos.le _) _) _)
          (mul_nonneg (Real.rpow_nonneg hM0 _) (lpNorm_nonneg _ _))
    _ = (M ^ (1 / D.q) * M ^ (1 - 1 / D.q)) * lpNorm (D.G : (Fin d → ℝ) → ℝ) D.q *
          D.Q.vol ^ (1 - 1 / D.q) := by ring
    _ = _ := by rw [← Real.rpow_add' hM0 (by norm_num), add_sub_cancel, Real.rpow_one]

/-- `|Q|^{1-1/q} |Q|^{1/r+1/q-1} = |Q|^{1/r}`. [PROVED] -/
theorem Q_vol_rpow_mul :
    D.Q.vol ^ (1 - 1 / D.q) * D.Q.vol ^ (1 / D.r + 1 / D.q - 1) = D.Q.vol ^ (1 / D.r) := by
  rw [← Real.rpow_add D.Q.vol_pos]
  congr 1
  ring

/-- `∑_{P ∈ S} W(P) ≤ M F ‖g‖_q |Q|^{1/r}` for a collection `S` of subcubes of `Q` with overlap
`M`. [PROVED] -/
theorem sum_W_le_of_overlap (S : Finset (DyadicCube d)) (hS : ∀ P ∈ S, P.toSet ⊆ D.Q.toSet)
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ f : TestFun d, ∀ q : ℝ, 0 < q →
      ∑ P ∈ S, ∫ x in P.toSet, |(f : (Fin d → ℝ) → ℝ) x| ^ q ≤
        M * ∫ x, |(f : (Fin d → ℝ) → ℝ) x| ^ q) :
    ∑ P ∈ S, D.W P ≤ M * D.F * lpNorm (D.G : (Fin d → ℝ) → ℝ) D.q * D.Q.vol ^ (1 / D.r) := by
  have hV := D.Q.vol_pos
  have hW := D.sum_W_le S hS hM0 hM (D.sum_vol_le_of_overlap S hS hM)
  refine hW.trans (le_of_eq ?_)
  rw [Real.mul_rpow hM0 hV.le, show M ^ (1 / D.r) * D.Q.vol ^ (1 / D.r) * M ^ (1 - 1 / D.r) =
    (M ^ (1 / D.r) * M ^ (1 - 1 / D.r)) * D.Q.vol ^ (1 / D.r) by ring,
    ← Real.rpow_add' hM0 (by norm_num), add_sub_cancel, Real.rpow_one]
  ring

/-- The sum of the right-hand sides of (2.20) over a collection `S` of subcubes of `Q` with
overlap `M ≥ 1`. [PROVED] -/
theorem sum_Kbound_le (S : Finset (DyadicCube d)) (hS : ∀ P ∈ S, P.toSet ⊆ D.Q.toSet)
    {M : ℝ} (hM1 : 1 ≤ M) (hM : ∀ f : TestFun d, ∀ q : ℝ, 0 < q →
      ∑ P ∈ S, ∫ x in P.toSet, |(f : (Fin d → ℝ) → ℝ) x| ^ q ≤
        M * ∫ x, |(f : (Fin d → ℝ) → ℝ) x| ^ q) :
    ∑ P ∈ S, (D.K₁ * D.W P + D.K₂ * D.F *
        (lpNorm (TestFun.truncateₗ P D.G : (Fin d → ℝ) → ℝ) D.q * P.vol ^ (1 - 1 / D.q)) *
        D.Q.vol ^ (1 / D.r + 1 / D.q - 1)) ≤
      M * (D.K₁ + D.K₂) * D.F * lpNorm (D.G : (Fin d → ℝ) → ℝ) D.q * D.Q.vol ^ (1 / D.r) := by
  have hM0 : 0 ≤ M := by linarith
  have hr0 : 0 < D.r := by linarith [D.hr]
  have hV := D.Q.vol_pos
  have hF0 := D.Fpos'.le
  have hK₁ := D.K₁_nonneg
  have hK₂ := D.K₂_nonneg
  have hW' := D.sum_W_le_of_overlap S hS hM0 hM
  have hH := D.sum_lpNorm_mul_vol_rpow_le S hS hM0 hM
  calc ∑ P ∈ S, (D.K₁ * D.W P + D.K₂ * D.F *
          (lpNorm (TestFun.truncateₗ P D.G : (Fin d → ℝ) → ℝ) D.q * P.vol ^ (1 - 1 / D.q)) *
          D.Q.vol ^ (1 / D.r + 1 / D.q - 1))
      = D.K₁ * ∑ P ∈ S, D.W P + D.K₂ * D.F * (∑ P ∈ S,
          lpNorm (TestFun.truncateₗ P D.G : (Fin d → ℝ) → ℝ) D.q * P.vol ^ (1 - 1 / D.q)) *
          D.Q.vol ^ (1 / D.r + 1 / D.q - 1) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
    _ ≤ D.K₁ * (M * D.F * lpNorm (D.G : (Fin d → ℝ) → ℝ) D.q * D.Q.vol ^ (1 / D.r)) +
          D.K₂ * D.F * (M * lpNorm (D.G : (Fin d → ℝ) → ℝ) D.q * D.Q.vol ^ (1 - 1 / D.q)) *
          D.Q.vol ^ (1 / D.r + 1 / D.q - 1) := by gcongr
    _ = _ := by
        rw [show D.K₂ * D.F * (M * lpNorm (D.G : (Fin d → ℝ) → ℝ) D.q * D.Q.vol ^ (1 - 1 / D.q)) *
          D.Q.vol ^ (1 / D.r + 1 / D.q - 1) = D.K₂ * D.F * M * lpNorm (D.G : (Fin d → ℝ) → ℝ) D.q *
          (D.Q.vol ^ (1 - 1 / D.q) * D.Q.vol ^ (1 / D.r + 1 / D.q - 1)) by ring, D.Q_vol_rpow_mul]
        ring

/-- **The sum of the estimates (2.20)** over a collection `S` of good subcubes of `Q` not contained
in cubes of `𝐏₄`, with overlap `M ≥ 1`:
`∑_{P ∈ S} |c_P Λ_P(h, u)| ≤ M (K₁ + K₂) F ‖g‖_q |Q|^{1/r}`. [PROVED] -/
theorem sum_abs_coef_mul_form2_hP_u_le (S : Finset (DyadicCube d))
    (hS : ∀ P ∈ S, P ∈ D.tree) (hgood : ∀ P ∈ S, D.Good P)
    (hP4 : ∀ P ∈ S, ∀ T ∈ D.P4, ¬ P.toSet ⊆ T.toSet) {M : ℝ} (hM1 : 1 ≤ M)
    (hM : ∀ f : TestFun d, ∀ q : ℝ, 0 < q →
      ∑ P ∈ S, ∫ x in P.toSet, |(f : (Fin d → ℝ) → ℝ) x| ^ q ≤
        M * ∫ x, |(f : (Fin d → ℝ) → ℝ) x| ^ q) :
    ∑ P ∈ S, |D.coef P * D.form2 P (TestFun.ind P) D.u| ≤
      M * (D.K₁ + D.K₂) * D.F * lpNorm (D.G : (Fin d → ℝ) → ℝ) D.q * D.Q.vol ^ (1 / D.r) := by
  have hS' : ∀ P ∈ S, P.toSet ⊆ D.Q.toSet := fun P hP => (hS P hP).1
  calc ∑ P ∈ S, |D.coef P * D.form2 P (TestFun.ind P) D.u|
      ≤ ∑ P ∈ S, (D.K₁ * D.W P + D.K₂ * D.F *
          (lpNorm (TestFun.truncateₗ P D.G : (Fin d → ℝ) → ℝ) D.q * P.vol ^ (1 - 1 / D.q)) *
          D.Q.vol ^ (1 / D.r + 1 / D.q - 1)) :=
        Finset.sum_le_sum fun P hP => D.abs_coef_mul_form2_hP_u_le (hS P hP) (hgood P hP) (hP4 P hP)
    _ ≤ _ := D.sum_Kbound_le S hS' hM1 hM

/-! #### The terms (2.21)–(2.22) with the parents `parents(𝐏)₄` (p. 45) -/

theorem card_children_le (R : DyadicCube d) : ((children R).card : ℝ) ≤ 2 ^ d := by
  have : (children R).card ≤ 2 ^ d := by
    rw [children]
    refine Finset.card_image_le.trans (le_of_eq ?_)
    simp [Finset.card_univ]
  exact_mod_cast this

/-- The product of the norms of the entries `f_j 𝟙_R` (`j ≠ k, k+1`), `x` in the slot `k` and `y`
in the slot `k+1`: `F_R ‖x‖_r ‖y‖_q`. [PROVED] -/
theorem prodNorm_entries (R : DyadicCube d) (x y : TestFun d) :
    prodNorm D.p (Function.update (Function.update (fun j => TestFun.truncateₗ R (D.g j)) D.a x)
      D.b y) = D.FP R * lpNorm (x : (Fin d → ℝ) → ℝ) D.r * lpNorm (y : (Fin d → ℝ) → ℝ) D.q := by
  have hab := D.hab
  unfold prodNorm
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ D.b),
    ← Finset.mul_prod_erase (Finset.univ.erase D.b) _
      (Finset.mem_erase.mpr ⟨hab, Finset.mem_univ D.a⟩)]
  have hb : Function.update (Function.update (fun j => TestFun.truncateₗ R (D.g j)) D.a x) D.b y
      D.b = y := by simp
  have ha : Function.update (Function.update (fun j => TestFun.truncateₗ R (D.g j)) D.a x) D.b y
      D.a = x := by
    rw [Function.update_of_ne hab, Function.update_self]
  have hJ : (Finset.univ.erase D.b).erase D.a = D.J := by rw [J, Finset.erase_right_comm]
  have hent : ∀ j ∈ D.J, Function.update (Function.update (fun j => TestFun.truncateₗ R (D.g j))
      D.a x) D.b y j = TestFun.truncateₗ R (D.g j) := by
    intro j hj
    rw [J, Finset.mem_erase, Finset.mem_erase] at hj
    rw [Function.update_of_ne hj.1, Function.update_of_ne hj.2.1]
  rw [hb, ha, hJ, Finset.prod_congr rfl fun j hj => by rw [hent j hj]]
  unfold FP
  ring

/-- **The expansion over the children** (p. 45): for a child `c = R.child ε` of `R` and `ρ'`
supported on `c`, `|Λ_R(h, ρ') − Λ_c(h, ρ')| ≤ n 2^d F_R |R|^{1/r} ‖ρ'‖_q`, by the decay condition
(1.1) applied to the terms of the expansion `f_j 𝟙_R = ∑_{P'} f_j 𝟙_{P'}`. [PROVED] -/
theorem abs_form2_parent_sub_child_le (R : DyadicCube d) (ε : Fin d → Bool) {ρ' : TestFun d}
    (hρ' : SupportedOn ρ' (R.child ε)) :
    |D.form2 R (TestFun.ind R) ρ' - D.form2 (R.child ε) (TestFun.ind (R.child ε)) ρ'| ≤
      n * 2 ^ d * (D.FP R * R.vol ^ (1 / D.r) * lpNorm (ρ' : (Fin d → ℝ) → ℝ) D.q) := by
  have hcR : (R.child ε).toSet ⊆ R.toSet := R.child_subset ε
  have hρR : SupportedOn ρ' R := fun x hx => hρ' x fun h => hx (hcR h)
  set e : Fin n → TestFun d := Function.update (Function.update
    (fun j => TestFun.truncateₗ R (D.g j)) D.a (TestFun.ind R)) D.b ρ' with he
  have h1 : D.form2 R (TestFun.ind R) ρ' = D.T.form e := by
    unfold form2 twoSlotForm
    rw [TestFun.truncateₗ_ind, TestFun.truncateₗ_of_supportedOn hρR]
  have h2 : D.form2 (R.child ε) (TestFun.ind (R.child ε)) ρ' =
      D.T.form (fun j => TestFun.truncateₗ (R.child ε) (e j)) := by
    unfold form2 twoSlotForm
    rw [he, TestFun.truncateₗ_comp_update, TestFun.truncateₗ_comp_update,
      TestFun.truncateₗ_ind_of_subset hcR, TestFun.truncateₗ_ind,
      show (fun j => TestFun.truncateₗ (R.child ε) (TestFun.truncateₗ R (D.g j))) =
        fun j => TestFun.truncateₗ (R.child ε) (D.g j) from
        funext fun j => TestFun.truncateₗ_truncateₗ_of_subset hcR _]
  have hsupp : ∀ j, SupportedOn (e j) R := by
    intro j
    by_cases hjb : j = D.b
    · rw [hjb, he, Function.update_self]
      exact hρR
    · rw [he, Function.update_of_ne hjb]
      by_cases hja : j = D.a
      · rw [hja, Function.update_self]
        exact TestFun.ind_supportedOn R
      · rw [Function.update_of_ne hja]
        exact TestFun.truncateₗ_supportedOn R (D.g j)
  have hb : SupportedOn (e D.b) (R.child ε) := by
    rw [he, Function.update_self]
    exact hρ'
  have h := D.T.abs_form_sub_truncate_child_le D.p R ε e D.b hsupp hb
  rw [h1, h2]
  refine h.trans (le_of_eq ?_)
  rw [he, D.prodNorm_entries, TestFun.lpNorm_ind R (by linarith [D.hr])]

/-- Regrouping a sum over the children of the parents `parents(𝐏)₄`: the children are exactly the
cubes
of `𝐏 ∩ 𝐏₄` and the siblings `𝐏₄'`. [PROVED] -/
theorem sum_Pbar4_children_ite {M : Type*} [AddCommMonoid M] (f g : DyadicCube d → M) :
    ∑ R ∈ D.Pbar4, ∑ c ∈ children R, (if c ∈ D.PstIn4 then f c else g c) =
      ∑ P ∈ D.PstIn4, f P + ∑ P ∈ D.Psib4, g P := by
  rw [← Finset.sum_biUnion (children_pairwiseDisjoint _), Finset.sum_ite,
    Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr D.PstIn4_subset_biUnion]
  rfl

theorem child_mem_Psib4 {R c : DyadicCube d} (hR : R ∈ D.Pbar4) (hc : c ∈ children R)
    (hnot : c ∉ D.PstIn4) : c ∈ D.Psib4 :=
  D.mem_Psib4.mpr ⟨⟨R, hR, hc⟩, hnot⟩

/-- The function `ξ^{parents(P)}` of (2.21): for a parent `R ∈ parents(𝐏)₄`,
`ξ^R = ∑_{children c ∈ 𝐏∩𝐏₄} [g]_c b_c + ∑_{children c ∈ 𝐏₄'} c_c u_c − c_R u_R`. -/
noncomputable def xi (R : DyadicCube d) : TestFun d :=
  ∑ c ∈ children R, (if c ∈ D.PstIn4 then avg c D.G • D.bP c
    else D.coef c • TestFun.truncateₗ c D.u) - D.coef R • TestFun.truncateₗ R D.u

/-- `∑_{parents(P) ∈ parents(𝐏)₄} ξ^{parents(P)}` is the sum of the three terms of (2.17).
[PROVED] -/
theorem sum_xi_eq : ∑ R ∈ D.Pbar4, D.xi R =
    ∑ P ∈ D.PstIn4, avg P D.G • D.bP P - ∑ P ∈ D.Pbar4, D.coef P • TestFun.truncateₗ P D.u
      + ∑ P ∈ D.Psib4, D.coef P • TestFun.truncateₗ P D.u := by
  simp only [xi, Finset.sum_sub_distrib]
  rw [D.sum_Pbar4_children_ite]
  abel

/-- `ξ^R` is supported on `R`. [PROVED] -/
theorem xi_supported {R : DyadicCube d} (hR : R ∈ D.Pbar4) :
    SupportedOn (D.xi R : (Fin d → ℝ) → ℝ) R := by
  intro x hx
  have h1 : ∀ c ∈ children R, ((if c ∈ D.PstIn4 then avg c D.G • D.bP c
      else D.coef c • TestFun.truncateₗ c D.u : TestFun d) : (Fin d → ℝ) → ℝ) x = 0 := by
    intro c hc
    obtain ⟨ε, rfl⟩ := mem_children.mp hc
    have hxc : x ∉ (R.child ε).toSet := fun h => hx (R.child_subset ε h)
    split_ifs with hc'
    · rw [Submodule.coe_smul, Pi.smul_apply,
        D.bP_supp _ ((R.child_subset ε).trans (D.Pbar4_subset_Q hR)) x hxc, smul_zero]
    · rw [Submodule.coe_smul, Pi.smul_apply, TestFun.truncateₗ_supportedOn _ _ x hxc, smul_zero]
  unfold xi
  rw [Submodule.coe_sub, Pi.sub_apply, Submodule.coe_sum, Finset.sum_apply,
    Finset.sum_eq_zero h1, Submodule.coe_smul, Pi.smul_apply,
    TestFun.truncateₗ_supportedOn R D.u x hx, smul_zero, sub_zero]

/-- `ξ^R` has mean zero (p. 45): `∑_{children} [g]_c |c| = [g]_R |R|`. [PROVED] -/
theorem xi_meanZero {R : DyadicCube d} (hR : R ∈ D.Pbar4) :
    MeanZero (D.xi R : (Fin d → ℝ) → ℝ) := by
  classical
  change TestFun.integralₗ (D.xi R) = 0
  have hc : ∀ c ∈ children R, TestFun.integralₗ (if c ∈ D.PstIn4 then avg c D.G • D.bP c
      else D.coef c • TestFun.truncateₗ c D.u) = avg c D.G * c.vol := by
    intro c hc
    split_ifs with h
    · rw [map_smul, smul_eq_mul, TestFun.integralₗ_apply,
        D.bP_mean c (D.Pst_subset_Q (Finset.mem_of_mem_filter c h))]
    · rw [map_smul, smul_eq_mul, TestFun.integralₗ_truncateₗ]
      have hsib := D.child_mem_Psib4 hR hc h
      exact D.coef_mul (D.avg_u_ne_zero (D.Psib4_mem_tree hsib) (D.Psib4_not_in_P4 hsib))
  unfold xi
  rw [map_sub, map_sum, map_smul, smul_eq_mul, TestFun.integralₗ_truncateₗ,
    Finset.sum_congr rfl hc, ← avg_mul_vol_children,
    D.coef_mul (D.avg_u_ne_zero (D.Pbar4_mem_tree hR) (D.Pbar4_not_in_P4 hR)), sub_self]

/-- `Λ_R(h, ξ^R)` expanded into the three kinds of terms of (2.22). [PROVED] -/
theorem form2_xi_eq (R : DyadicCube d) :
    D.form2 R (TestFun.ind R) (D.xi R) =
      ∑ c ∈ children R, (if c ∈ D.PstIn4 then avg c D.G * D.form2 R (TestFun.ind R) (D.bP c)
        else D.coef c * D.form2 R (TestFun.ind R) (TestFun.truncateₗ c D.u))
      - D.coef R * D.form2 R (TestFun.ind R) (TestFun.truncateₗ R D.u) := by
  unfold xi
  rw [D.form2_sub_right, D.form2_sum_right, D.form2_smul_right]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  split_ifs <;> rw [D.form2_smul_right]

/-- The constant of the decay terms of (2.22): `K₃ = n 2^d (B^{1/q} + 8 (2^d B/ε)^{1/q})`. -/
noncomputable def K₃ : ℝ := n * 2 ^ d * (D.B ^ (1 / D.q) + 8 * (2 ^ d * D.B / D.ε) ^ (1 / D.q))

theorem K₃_nonneg : 0 ≤ D.K₃ := by
  have hB0 : 0 ≤ D.B := by linarith [D.hB]
  have hε := D.ε_pos
  unfold K₃
  positivity

/-- **The terms of (2.22) for one child** `c` of a parent `R ∈ parents(𝐏)₄` (p. 45): by the
expansion over
the children and the decay condition, `Λ_R(h, ·)` differs from `Λ_c(h, ·)` by at most
`n 2^d F_R |R|^{1/r} ‖·‖_q`; the term `Λ_c(h, ·)` is estimated as for the cubes of `𝐏` and
`𝐏 ∖ 𝐏₄`, and the decay term by `K₃ W(R)` using `|[g]_c| ‖b_c‖_q ≤ B^{1/q} ‖g_R‖_q`,
`|c_c| ‖u_c‖_q ≤ 8 (2^d B/ε)^{1/q} ‖g_R‖_q`. [PROVED] -/
theorem child_term_le {R c : DyadicCube d} (hR : R ∈ D.Pbar4) (hc : c ∈ children R) :
    |if c ∈ D.PstIn4 then avg c D.G * D.form2 R (TestFun.ind R) (D.bP c)
      else D.coef c * D.form2 R (TestFun.ind R) (TestFun.truncateₗ c D.u)| ≤
      (if c ∈ D.PstIn4 then D.B ^ (1 + 1 / D.q) * D.W c
        else D.K₁ * D.W c + D.K₂ * D.F *
          (lpNorm (TestFun.truncateₗ c D.G : (Fin d → ℝ) → ℝ) D.q * c.vol ^ (1 - 1 / D.q)) *
          D.Q.vol ^ (1 / D.r + 1 / D.q - 1)) + D.K₃ * D.W R := by
  have hq1 : 1 ≤ D.q := D.hq.le
  have hq0 : 0 < D.q := by linarith
  have hr0 : 0 < D.r := by linarith [D.hr]
  have hB0 : 0 ≤ D.B := by linarith [D.hB]
  have hε := D.ε_pos
  have hRQ : R.toSet ⊆ D.Q.toSet := D.Pbar4_subset_Q hR
  obtain ⟨ε, rfl⟩ := mem_children.mp hc
  have hcR : (R.child ε).toSet ⊆ R.toSet := R.child_subset ε
  have hcQ : (R.child ε).toSet ⊆ D.Q.toSet := hcR.trans hRQ
  have hFR := D.FP_nonneg R
  have hVR := R.vol_pos
  have hvc := (R.child ε).vol_pos
  have hLR : 0 ≤ lpNorm (TestFun.truncateₗ R D.G : (Fin d → ℝ) → ℝ) D.q := lpNorm_nonneg _ _
  have hGc : |avg (R.child ε) D.G| * (R.child ε).vol ^ (1 / D.q) ≤
      lpNorm (TestFun.truncateₗ R D.G : (Fin d → ℝ) → ℝ) D.q :=
    (abs_avg_mul_rpow_le (R.child ε) D.G hq1).trans
      (TestFun.lpNorm_truncateₗ_mono hcR D.G hq0)
  have hX0 : 0 ≤ (n : ℝ) * 2 ^ d * (D.FP R * R.vol ^ (1 / D.r)) := by positivity
  have hWR : D.FP R * R.vol ^ (1 / D.r) * lpNorm (TestFun.truncateₗ R D.G : (Fin d → ℝ) → ℝ) D.q
      = D.W R := rfl
  have hBq : 0 ≤ D.B ^ (1 / D.q) := Real.rpow_nonneg hB0 _
  have hCq : 0 ≤ 8 * (2 ^ d * D.B / D.ε) ^ (1 / D.q) := by positivity
  split_ifs with h
  · -- `c ∈ 𝐏 ∩ 𝐏₄`
    have hd := D.abs_form2_parent_sub_child_le R ε (D.bP_supp _ hcQ)
    have h1 := D.abs_avg_mul_form2_hP_bP_le hcQ
    have hbn : |avg (R.child ε) D.G| * lpNorm (D.bP (R.child ε) : (Fin d → ℝ) → ℝ) D.q ≤
        D.B ^ (1 / D.q) * lpNorm (TestFun.truncateₗ R D.G : (Fin d → ℝ) → ℝ) D.q := by
      calc |avg (R.child ε) D.G| * lpNorm (D.bP (R.child ε) : (Fin d → ℝ) → ℝ) D.q
          ≤ |avg (R.child ε) D.G| * (D.B * (R.child ε).vol) ^ (1 / D.q) :=
            mul_le_mul_of_nonneg_left (D.lpNorm_bP_le hcQ) (abs_nonneg _)
        _ = D.B ^ (1 / D.q) * (|avg (R.child ε) D.G| * (R.child ε).vol ^ (1 / D.q)) := by
            rw [Real.mul_rpow hB0 hvc.le]
            ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hGc hBq
    have habs : |D.form2 R (TestFun.ind R) (D.bP (R.child ε))| ≤
        |D.form2 (R.child ε) (TestFun.ind (R.child ε)) (D.bP (R.child ε))| +
        |D.form2 R (TestFun.ind R) (D.bP (R.child ε)) -
          D.form2 (R.child ε) (TestFun.ind (R.child ε)) (D.bP (R.child ε))| := by
      have := abs_sub_abs_le_abs_sub (D.form2 R (TestFun.ind R) (D.bP (R.child ε)))
        (D.form2 (R.child ε) (TestFun.ind (R.child ε)) (D.bP (R.child ε)))
      linarith
    calc |avg (R.child ε) D.G * D.form2 R (TestFun.ind R) (D.bP (R.child ε))|
        = |avg (R.child ε) D.G| * |D.form2 R (TestFun.ind R) (D.bP (R.child ε))| := abs_mul _ _
      _ ≤ |avg (R.child ε) D.G| *
            (|D.form2 (R.child ε) (TestFun.ind (R.child ε)) (D.bP (R.child ε))| +
            |D.form2 R (TestFun.ind R) (D.bP (R.child ε)) -
              D.form2 (R.child ε) (TestFun.ind (R.child ε)) (D.bP (R.child ε))|) :=
          mul_le_mul_of_nonneg_left habs (abs_nonneg _)
      _ ≤ D.B ^ (1 + 1 / D.q) * D.W (R.child ε) +
            n * 2 ^ d * (D.FP R * R.vol ^ (1 / D.r)) *
              (D.B ^ (1 / D.q) * lpNorm (TestFun.truncateₗ R D.G : (Fin d → ℝ) → ℝ) D.q) := by
          rw [mul_add, ← abs_mul]
          refine add_le_add h1 ?_
          calc |avg (R.child ε) D.G| * |D.form2 R (TestFun.ind R) (D.bP (R.child ε)) -
                D.form2 (R.child ε) (TestFun.ind (R.child ε)) (D.bP (R.child ε))|
              ≤ |avg (R.child ε) D.G| * (n * 2 ^ d * (D.FP R * R.vol ^ (1 / D.r) *
                  lpNorm (D.bP (R.child ε) : (Fin d → ℝ) → ℝ) D.q)) :=
                mul_le_mul_of_nonneg_left hd (abs_nonneg _)
            _ = n * 2 ^ d * (D.FP R * R.vol ^ (1 / D.r)) *
                  (|avg (R.child ε) D.G| * lpNorm (D.bP (R.child ε) : (Fin d → ℝ) → ℝ) D.q) := by
                ring
            _ ≤ _ := mul_le_mul_of_nonneg_left hbn hX0
      _ = D.B ^ (1 + 1 / D.q) * D.W (R.child ε) + n * 2 ^ d * D.B ^ (1 / D.q) * D.W R := by
          rw [← hWR]
          ring
      _ ≤ D.B ^ (1 + 1 / D.q) * D.W (R.child ε) + D.K₃ * D.W R := by
          refine add_le_add le_rfl (mul_le_mul_of_nonneg_right ?_ (D.W_nonneg R))
          unfold K₃
          exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hCq) (by positivity)
  · -- `c ∈ 𝐏₄'`
    have hsib := D.child_mem_Psib4 hR hc h
    have hct : R.child ε ∈ D.tree := D.Psib4_mem_tree hsib
    have hgood : D.Good (R.child ε) := D.good_of_Psib4 hsib
    have hP4 := D.Psib4_not_in_P4 hsib
    have hd := D.abs_form2_parent_sub_child_le R ε (TestFun.truncateₗ_supportedOn (R.child ε) D.u)
    have h1 := D.abs_coef_mul_form2_hP_u_le hct hgood hP4
    rw [← D.form2_truncateₗ_right (R.child ε) (TestFun.ind (R.child ε)) D.u] at h1
    have hcn : |D.coef (R.child ε)| *
        lpNorm (TestFun.truncateₗ (R.child ε) D.u : (Fin d → ℝ) → ℝ) D.q ≤
        8 * (2 ^ d * D.B / D.ε) ^ (1 / D.q) *
          lpNorm (TestFun.truncateₗ R D.G : (Fin d → ℝ) → ℝ) D.q := by
      have hc8 := D.abs_coef_le (D.bound_2_11 D.hd hct hP4)
      have hu := D.lpNorm_truncateₗ_u_le hgood
      calc |D.coef (R.child ε)| *
            lpNorm (TestFun.truncateₗ (R.child ε) D.u : (Fin d → ℝ) → ℝ) D.q
          ≤ (8 * |avg (R.child ε) D.G|) * (2 ^ d * D.B / D.ε * (R.child ε).vol) ^ (1 / D.q) :=
            mul_le_mul hc8 hu (lpNorm_nonneg _ _) (by positivity)
        _ = 8 * (2 ^ d * D.B / D.ε) ^ (1 / D.q) *
              (|avg (R.child ε) D.G| * (R.child ε).vol ^ (1 / D.q)) := by
            rw [Real.mul_rpow (by positivity) hvc.le]
            ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hGc hCq
    have habs : |D.form2 R (TestFun.ind R) (TestFun.truncateₗ (R.child ε) D.u)| ≤
        |D.form2 (R.child ε) (TestFun.ind (R.child ε)) (TestFun.truncateₗ (R.child ε) D.u)| +
        |D.form2 R (TestFun.ind R) (TestFun.truncateₗ (R.child ε) D.u) -
          D.form2 (R.child ε) (TestFun.ind (R.child ε)) (TestFun.truncateₗ (R.child ε) D.u)| := by
      have := abs_sub_abs_le_abs_sub
        (D.form2 R (TestFun.ind R) (TestFun.truncateₗ (R.child ε) D.u))
        (D.form2 (R.child ε) (TestFun.ind (R.child ε)) (TestFun.truncateₗ (R.child ε) D.u))
      linarith
    calc |D.coef (R.child ε) * D.form2 R (TestFun.ind R) (TestFun.truncateₗ (R.child ε) D.u)|
        = |D.coef (R.child ε)| *
            |D.form2 R (TestFun.ind R) (TestFun.truncateₗ (R.child ε) D.u)| := abs_mul _ _
      _ ≤ |D.coef (R.child ε)| *
            (|D.form2 (R.child ε) (TestFun.ind (R.child ε)) (TestFun.truncateₗ (R.child ε) D.u)| +
            |D.form2 R (TestFun.ind R) (TestFun.truncateₗ (R.child ε) D.u) -
              D.form2 (R.child ε) (TestFun.ind (R.child ε))
                (TestFun.truncateₗ (R.child ε) D.u)|) :=
          mul_le_mul_of_nonneg_left habs (abs_nonneg _)
      _ ≤ (D.K₁ * D.W (R.child ε) + D.K₂ * D.F *
            (lpNorm (TestFun.truncateₗ (R.child ε) D.G : (Fin d → ℝ) → ℝ) D.q *
              (R.child ε).vol ^ (1 - 1 / D.q)) * D.Q.vol ^ (1 / D.r + 1 / D.q - 1)) +
            n * 2 ^ d * (D.FP R * R.vol ^ (1 / D.r)) *
              (8 * (2 ^ d * D.B / D.ε) ^ (1 / D.q) *
                lpNorm (TestFun.truncateₗ R D.G : (Fin d → ℝ) → ℝ) D.q) := by
          rw [mul_add, ← abs_mul]
          refine add_le_add h1 ?_
          calc |D.coef (R.child ε)| *
                |D.form2 R (TestFun.ind R) (TestFun.truncateₗ (R.child ε) D.u) -
                  D.form2 (R.child ε) (TestFun.ind (R.child ε))
                    (TestFun.truncateₗ (R.child ε) D.u)|
              ≤ |D.coef (R.child ε)| * (n * 2 ^ d * (D.FP R * R.vol ^ (1 / D.r) *
                  lpNorm (TestFun.truncateₗ (R.child ε) D.u : (Fin d → ℝ) → ℝ) D.q)) :=
                mul_le_mul_of_nonneg_left hd (abs_nonneg _)
            _ = n * 2 ^ d * (D.FP R * R.vol ^ (1 / D.r)) * (|D.coef (R.child ε)| *
                  lpNorm (TestFun.truncateₗ (R.child ε) D.u : (Fin d → ℝ) → ℝ) D.q) := by
                ring
            _ ≤ _ := mul_le_mul_of_nonneg_left hcn hX0
      _ = (D.K₁ * D.W (R.child ε) + D.K₂ * D.F *
            (lpNorm (TestFun.truncateₗ (R.child ε) D.G : (Fin d → ℝ) → ℝ) D.q *
              (R.child ε).vol ^ (1 - 1 / D.q)) * D.Q.vol ^ (1 / D.r + 1 / D.q - 1)) +
            n * 2 ^ d * (8 * (2 ^ d * D.B / D.ε) ^ (1 / D.q)) * D.W R := by
          rw [← hWR]
          ring
      _ ≤ _ := by
          refine add_le_add le_rfl (mul_le_mul_of_nonneg_right ?_ (D.W_nonneg R))
          unfold K₃
          exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hBq) (by positivity)

/-- **The bound for `Λ_R(h, ξ^R)`** (p. 45), for a parent `R ∈ parents(𝐏)₄`. [PROVED] -/
theorem abs_form2_xi_le {R : DyadicCube d} (hR : R ∈ D.Pbar4) :
    |D.form2 R (TestFun.ind R) (D.xi R)| ≤
      ∑ c ∈ children R, (if c ∈ D.PstIn4 then D.B ^ (1 + 1 / D.q) * D.W c
        else D.K₁ * D.W c + D.K₂ * D.F *
          (lpNorm (TestFun.truncateₗ c D.G : (Fin d → ℝ) → ℝ) D.q * c.vol ^ (1 - 1 / D.q)) *
          D.Q.vol ^ (1 / D.r + 1 / D.q - 1))
      + 2 ^ d * D.K₃ * D.W R + |D.coef R * D.form2 R (TestFun.ind R) D.u| := by
  rw [D.form2_xi_eq, ← D.form2_truncateₗ_right R (TestFun.ind R) D.u]
  refine (abs_sub _ _).trans ?_
  refine add_le_add ?_ le_rfl
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hK := D.K₃_nonneg
  have hW := D.W_nonneg R
  have hcard := card_children_le R
  calc ∑ c ∈ children R, |if c ∈ D.PstIn4 then avg c D.G * D.form2 R (TestFun.ind R) (D.bP c)
        else D.coef c * D.form2 R (TestFun.ind R) (TestFun.truncateₗ c D.u)|
      ≤ ∑ c ∈ children R, ((if c ∈ D.PstIn4 then D.B ^ (1 + 1 / D.q) * D.W c
          else D.K₁ * D.W c + D.K₂ * D.F *
            (lpNorm (TestFun.truncateₗ c D.G : (Fin d → ℝ) → ℝ) D.q * c.vol ^ (1 - 1 / D.q)) *
            D.Q.vol ^ (1 / D.r + 1 / D.q - 1)) + D.K₃ * D.W R) :=
        Finset.sum_le_sum fun c hc => D.child_term_le hR hc
    _ = ∑ c ∈ children R, (if c ∈ D.PstIn4 then D.B ^ (1 + 1 / D.q) * D.W c
          else D.K₁ * D.W c + D.K₂ * D.F *
            (lpNorm (TestFun.truncateₗ c D.G : (Fin d → ℝ) → ℝ) D.q * c.vol ^ (1 - 1 / D.q)) *
            D.Q.vol ^ (1 / D.r + 1 / D.q - 1)) + (children R).card * (D.K₃ * D.W R) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := by
        refine add_le_add le_rfl ?_
        rw [mul_assoc (2 ^ d : ℝ)]
        exact mul_le_mul_of_nonneg_right hcard (mul_nonneg hK hW)

/-- The overlap hypotheses for `parents(𝐏)₄` and `𝐏₄'`, with `M = 2^d/ε`. -/
theorem overlap_Pbar4 (f : TestFun d) (q : ℝ) (hq : 0 < q) :
    ∑ P ∈ D.Pbar4, ∫ x in P.toSet, |(f : (Fin d → ℝ) → ℝ) x| ^ q ≤
      2 ^ d / D.ε * ∫ x, |(f : (Fin d → ℝ) → ℝ) x| ^ q :=
  sum_setIntegral_le_of_overlap_real D.Pbar4 D.card_Pbar4_filter_le f hq

theorem overlap_Psib4 (f : TestFun d) (q : ℝ) (hq : 0 < q) :
    ∑ P ∈ D.Psib4, ∫ x in P.toSet, |(f : (Fin d → ℝ) → ℝ) x| ^ q ≤
      2 ^ d / D.ε * ∫ x, |(f : (Fin d → ℝ) → ℝ) x| ^ q :=
  sum_setIntegral_le_of_overlap_real D.Psib4 D.card_Psib4_filter_le f hq

theorem one_le_M : (1 : ℝ) ≤ 2 ^ d / D.ε := by
  have hε := D.ε_pos
  have hεle := D.ε_le
  rw [le_div_iff₀ hε, one_mul]
  have : (1 : ℝ) ≤ 2 ^ d := one_le_pow₀ (by norm_num)
  linarith

/-- `∑_{P ∈ 𝐏} W(P) ≤ F ‖g‖_q |Q|^{1/r}` (dropping the factor `(1-ε)^{1/r} ≤ 1`). [PROVED] -/
theorem sum_W_Pst_le' : ∑ P ∈ D.Pst, D.W P ≤
    D.F * lpNorm (D.G : (Fin d → ℝ) → ℝ) D.q * D.Q.vol ^ (1 / D.r) := by
  have hε := D.ε_pos
  have hεle := D.ε_le
  have hV := D.Q.vol_pos
  have h1 : ((1 - D.ε) * D.Q.vol) ^ (1 / D.r) ≤ D.Q.vol ^ (1 / D.r) :=
    Real.rpow_le_rpow (mul_nonneg (by linarith) hV.le)
      (mul_le_of_le_one_left hV.le (by linarith)) (by have := D.hr; positivity)
  refine D.sum_W_Pst_le.trans ?_
  have := D.Fpos'.le
  have := lpNorm_nonneg (D.G : (Fin d → ℝ) → ℝ) D.q
  calc ((1 - D.ε) * D.Q.vol) ^ (1 / D.r) * D.F * lpNorm (D.G : (Fin d → ℝ) → ℝ) D.q
      ≤ D.Q.vol ^ (1 / D.r) * D.F * lpNorm (D.G : (Fin d → ℝ) → ℝ) D.q := by gcongr
    _ = _ := by ring

/-- The sum of `W` over a subcollection of `𝐏`. [PROVED] -/
theorem sum_W_le_of_subset_Pst {S : Finset (DyadicCube d)} (hS : S ⊆ D.Pst) :
    ∑ P ∈ S, D.W P ≤ D.F * lpNorm (D.G : (Fin d → ℝ) → ℝ) D.q * D.Q.vol ^ (1 / D.r) :=
  (Finset.sum_le_sum_of_subset_of_nonneg hS fun P _ _ => D.W_nonneg P).trans D.sum_W_Pst_le'

/-- **The sum of (2.22) over the parents** (p. 45):
`∑_{parents(P) ∈ parents(𝐏)₄} |Λ_{parents(P)}(h, ξ^{parents(P)})| ≤ (B^{1+1/q} + 2 M (K₁+K₂) + 2^d
K₃ M) F ‖g‖_q |Q|^{1/r}`,
`M = 2^d/ε`, by the bounded overlap of `parents(𝐏)₄` and `𝐏₄'`. [PROVED] -/
theorem sum_abs_form2_xi_le :
    ∑ R ∈ D.Pbar4, |D.form2 R (TestFun.ind R) (D.xi R)| ≤
      (D.B ^ (1 + 1 / D.q) + 2 * (2 ^ d / D.ε) * (D.K₁ + D.K₂) + 2 ^ d * D.K₃ * (2 ^ d / D.ε)) *
        (D.F * lpNorm (D.G : (Fin d → ℝ) → ℝ) D.q * D.Q.vol ^ (1 / D.r)) := by
  classical
  have hM1 := D.one_le_M
  have hM0 : (0 : ℝ) ≤ 2 ^ d / D.ε := by linarith
  have hB0 : 0 ≤ D.B := by linarith [D.hB]
  have hK₃ := D.K₃_nonneg
  have hIn : ∑ P ∈ D.PstIn4, D.W P ≤
      D.F * lpNorm (D.G : (Fin d → ℝ) → ℝ) D.q * D.Q.vol ^ (1 / D.r) :=
    D.sum_W_le_of_subset_Pst (Finset.filter_subset _ _)
  have hSib := D.sum_Kbound_le D.Psib4 (fun P hP => D.Psib4_subset_Q hP) hM1 D.overlap_Psib4
  have hBar := D.sum_W_le_of_overlap D.Pbar4 (fun P hP => D.Pbar4_subset_Q hP) hM0 D.overlap_Pbar4
  have hCoef := D.sum_abs_coef_mul_form2_hP_u_le D.Pbar4 (fun P hP => D.Pbar4_mem_tree hP)
    (fun P hP => D.good_of_Pbar4 hP) (fun P hP => D.Pbar4_not_in_P4 hP) hM1 D.overlap_Pbar4
  calc ∑ R ∈ D.Pbar4, |D.form2 R (TestFun.ind R) (D.xi R)|
      ≤ ∑ R ∈ D.Pbar4, (∑ c ∈ children R, (if c ∈ D.PstIn4 then D.B ^ (1 + 1 / D.q) * D.W c
          else D.K₁ * D.W c + D.K₂ * D.F *
            (lpNorm (TestFun.truncateₗ c D.G : (Fin d → ℝ) → ℝ) D.q * c.vol ^ (1 - 1 / D.q)) *
            D.Q.vol ^ (1 / D.r + 1 / D.q - 1))
          + 2 ^ d * D.K₃ * D.W R + |D.coef R * D.form2 R (TestFun.ind R) D.u|) :=
        Finset.sum_le_sum fun R hR => D.abs_form2_xi_le hR
    _ = D.B ^ (1 + 1 / D.q) * ∑ P ∈ D.PstIn4, D.W P
        + ∑ P ∈ D.Psib4, (D.K₁ * D.W P + D.K₂ * D.F *
            (lpNorm (TestFun.truncateₗ P D.G : (Fin d → ℝ) → ℝ) D.q * P.vol ^ (1 - 1 / D.q)) *
            D.Q.vol ^ (1 / D.r + 1 / D.q - 1))
        + 2 ^ d * D.K₃ * ∑ R ∈ D.Pbar4, D.W R
        + ∑ R ∈ D.Pbar4, |D.coef R * D.form2 R (TestFun.ind R) D.u| := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
          D.sum_Pbar4_children_ite (fun c => D.B ^ (1 + 1 / D.q) * D.W c)
            (fun c => D.K₁ * D.W c + D.K₂ * D.F *
              (lpNorm (TestFun.truncateₗ c D.G : (Fin d → ℝ) → ℝ) D.q * c.vol ^ (1 - 1 / D.q)) *
              D.Q.vol ^ (1 / D.r + 1 / D.q - 1)),
          Finset.mul_sum, Finset.mul_sum]
    _ ≤ D.B ^ (1 + 1 / D.q) * (D.F * lpNorm (D.G : (Fin d → ℝ) → ℝ) D.q * D.Q.vol ^ (1 / D.r))
        + (2 ^ d / D.ε) * (D.K₁ + D.K₂) * D.F * lpNorm (D.G : (Fin d → ℝ) → ℝ) D.q *
            D.Q.vol ^ (1 / D.r)
        + 2 ^ d * D.K₃ * ((2 ^ d / D.ε) * D.F * lpNorm (D.G : (Fin d → ℝ) → ℝ) D.q *
            D.Q.vol ^ (1 / D.r))
        + (2 ^ d / D.ε) * (D.K₁ + D.K₂) * D.F * lpNorm (D.G : (Fin d → ℝ) → ℝ) D.q *
            D.Q.vol ^ (1 / D.r) := by gcongr
    _ = _ := by ring

/-- **The identity (2.18)** (p. 44): by the smoothness condition, since `g_P − [g]_P b_P` is
supported on `P` with mean zero,
`Λ_Q(h, ∑_{P ∈ 𝐏} (g_P − [g]_P b_P)) = ∑_{P ∈ 𝐏} Λ_P(h, g) − ∑_{P ∈ 𝐏} [g]_P Λ_P(h, b_P)`.
[PROVED] -/
theorem form2_hQ_sum_Pst_eq :
    D.form2 D.Q (TestFun.ind D.Q)
        (∑ P ∈ D.Pst, (TestFun.truncateₗ P D.G - avg P D.G • D.bP P)) =
      ∑ P ∈ D.Pst, D.form2 P (TestFun.ind P) (TestFun.truncateₗ P D.G) -
        ∑ P ∈ D.Pst, avg P D.G * D.form2 P (TestFun.ind P) (D.bP P) := by
  rw [D.form2_sum_right, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun P hP => ?_
  have hPQ := D.Pst_subset_Q hP
  have hsupp : SupportedOn ((TestFun.truncateₗ P D.G - avg P D.G • D.bP P : TestFun d) :
      (Fin d → ℝ) → ℝ) P := fun x hx => by
    rw [Submodule.coe_sub, Pi.sub_apply, Submodule.coe_smul, Pi.smul_apply,
      TestFun.truncateₗ_supportedOn P D.G x hx, D.bP_supp P hPQ x hx, smul_zero, sub_zero]
  have hmean : MeanZero ((TestFun.truncateₗ P D.G - avg P D.G • D.bP P : TestFun d) :
      (Fin d → ℝ) → ℝ) := by
    change TestFun.integralₗ (TestFun.truncateₗ P D.G - avg P D.G • D.bP P) = 0
    rw [map_sub, map_smul, smul_eq_mul, TestFun.integralₗ_truncateₗ, TestFun.integralₗ_apply,
      D.bP_mean P hPQ, sub_self]
  rw [D.form2_eq_of_subset hPQ _ hsupp hmean, D.form2_ind_left hPQ, D.form2_sub_right,
    D.form2_smul_right]

/-- **The identity (2.19)** (p. 44): for `P ∈ 𝐏 ∖ 𝐏₄`, `[g]_P b_P − c_P u_P` is supported on `P`
with mean zero, so
`Λ_Q(h, ∑_{P ∈ 𝐏∖𝐏₄} ([g]_P b_P − c_P u_P)) = ∑ [g]_P Λ_P(h, b_P) − ∑ c_P Λ_P(h, u)`. [PROVED] -/
theorem form2_hQ_sum_PstOut4_eq :
    D.form2 D.Q (TestFun.ind D.Q)
        (∑ P ∈ D.PstOut4, (avg P D.G • D.bP P - D.coef P • TestFun.truncateₗ P D.u)) =
      ∑ P ∈ D.PstOut4, avg P D.G * D.form2 P (TestFun.ind P) (D.bP P) -
        ∑ P ∈ D.PstOut4, D.coef P * D.form2 P (TestFun.ind P) D.u := by
  classical
  rw [D.form2_sum_right, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun P hP => ?_
  have hPs := (D.mem_PstOut4.mp hP).1
  have hPQ : P.toSet ⊆ D.Q.toSet := D.Pst_subset_Q (Finset.mem_of_mem_filter P hP)
  have hsupp : SupportedOn ((avg P D.G • D.bP P - D.coef P • TestFun.truncateₗ P D.u : TestFun d) :
      (Fin d → ℝ) → ℝ) P := fun x hx => by
    rw [Submodule.coe_sub, Pi.sub_apply, Submodule.coe_smul, Pi.smul_apply, Submodule.coe_smul,
      Pi.smul_apply, TestFun.truncateₗ_supportedOn P D.u x hx, D.bP_supp P hPQ x hx, smul_zero,
      smul_zero, sub_zero]
  have hmean : MeanZero ((avg P D.G • D.bP P - D.coef P • TestFun.truncateₗ P D.u : TestFun d) :
      (Fin d → ℝ) → ℝ) := by
    change TestFun.integralₗ (avg P D.G • D.bP P - D.coef P • TestFun.truncateₗ P D.u) = 0
    rw [map_sub, map_smul, map_smul, smul_eq_mul, smul_eq_mul, TestFun.integralₗ_truncateₗ,
      TestFun.integralₗ_apply, D.bP_mean P hPQ,
      D.coef_mul (D.avg_u_ne_zero (D.stoppingCubes_subset_tree' hPs) (D.PstOut4_not_in_P4 hP)),
      sub_self]
  rw [D.form2_eq_of_subset hPQ _ hsupp hmean, D.form2_ind_left hPQ, D.form2_sub_right,
    D.form2_smul_right, D.form2_smul_right, D.form2_truncateₗ_right]

/-- **The identity (2.21)–(2.22)** (p. 45): the three sums of (2.17) regrouped over the parents,
`Λ_Q(h, ∑_{𝐏∩𝐏₄} [g]_P b_P − ∑_{parents(𝐏)₄} c_P u_P + ∑_{𝐏₄'} c_P u_P) = ∑_{parents(P) ∈
parents(𝐏)₄} Λ_{parents(P)}(h, ξ^{parents(P)})`,
by the smoothness condition since `ξ^{parents(P)}` is supported on `parents(P)` with mean zero.
[PROVED] -/
theorem form2_hQ_Pbar4_eq :
    D.form2 D.Q (TestFun.ind D.Q)
        (∑ P ∈ D.PstIn4, avg P D.G • D.bP P - ∑ P ∈ D.Pbar4, D.coef P • TestFun.truncateₗ P D.u
          + ∑ P ∈ D.Psib4, D.coef P • TestFun.truncateₗ P D.u) =
      ∑ R ∈ D.Pbar4, D.form2 R (TestFun.ind R) (D.xi R) := by
  rw [← D.sum_xi_eq, D.form2_sum_right]
  refine Finset.sum_congr rfl fun R hR => ?_
  have hRQ := D.Pbar4_subset_Q hR
  rw [D.form2_eq_of_subset hRQ _ (D.xi_supported hR) (D.xi_meanZero hR), D.form2_ind_left hRQ]

/-- The constant `C` of (2.13):
`C = 4 B^{1+1/q} + (K₁ + K₂)(1 + 2 M) + 2^d K₃ M` with `M = 2^d/ε`; it depends only on `B`,
`n`, `d` and the exponents. -/
noncomputable def C₁₃ : ℝ :=
  4 * D.B ^ (1 + 1 / D.q) + (D.K₁ + D.K₂) * (1 + 2 * (2 ^ d / D.ε)) +
    2 ^ d * D.K₃ * (2 ^ d / D.ε)

/-- **The estimate (2.13)** (p. 43–45):
`|Λ_Q(h, g − 𝔤)| ≤ (A (1-ε)^{1/r} + C) F ‖g‖_q ‖h‖_r`, `‖h‖_r = |Q|^{1/r}`, assembled from the
expansion (2.15)–(2.17): the term `[g]_Q u`, the identity (2.18) with the `A`-term and the testing
term, the identity (2.19) with the two terms of (2.20), and the regrouped sum (2.21)–(2.22) over
the parents `parents(𝐏)₄`. [PROVED] -/
theorem estimate_2_13 :
    |D.form2 D.Q (TestFun.ind D.Q) (D.G - D.pruned)| ≤
      (D.A * (1 - D.ε) ^ (1 / D.r) + D.C₁₃) * D.F * lpNorm (D.G : (Fin d → ℝ) → ℝ) D.q *
        D.Q.vol ^ (1 / D.r) := by
  classical
  have hεle := D.ε_le
  have hV := D.Q.vol_pos
  have hB0 : 0 ≤ D.B := by linarith [D.hB]
  -- the four groups of terms
  have hsplit : D.G - D.pruned =
      avg D.Q D.G • D.u
      + ∑ P ∈ D.Pst, (TestFun.truncateₗ P D.G - avg P D.G • D.bP P)
      + ∑ P ∈ D.PstOut4, (avg P D.G • D.bP P - D.coef P • TestFun.truncateₗ P D.u)
      + (∑ P ∈ D.PstIn4, avg P D.G • D.bP P
        - ∑ P ∈ D.Pbar4, D.coef P • TestFun.truncateₗ P D.u
        + ∑ P ∈ D.Psib4, D.coef P • TestFun.truncateₗ P D.u) := by
    rw [D.sub_pruned_eq]
    abel
  rw [hsplit, D.form2_add_right, D.form2_add_right, D.form2_add_right]
  -- term (2.15), first part
  have hT1 := D.form2_hQ_avg_u_le
  -- term (2.18)
  have hT2 : |D.form2 D.Q (TestFun.ind D.Q)
      (∑ P ∈ D.Pst, (TestFun.truncateₗ P D.G - avg P D.G • D.bP P))| ≤
      D.A * D.F * ((1 - D.ε) * D.Q.vol) ^ (1 / D.r) * lpNorm (D.G : (Fin d → ℝ) → ℝ) D.q +
        D.B ^ (1 + 1 / D.q) *
          (D.F * lpNorm (D.G : (Fin d → ℝ) → ℝ) D.q * D.Q.vol ^ (1 / D.r)) := by
    rw [D.form2_hQ_sum_Pst_eq]
    refine (abs_sub _ _).trans (add_le_add ?_ ?_)
    · exact (Finset.abs_sum_le_sum_abs _ _).trans D.sum_form2_hP_G_le
    · refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ P ∈ D.Pst, |avg P D.G * D.form2 P (TestFun.ind P) (D.bP P)|
          ≤ ∑ P ∈ D.Pst, D.B ^ (1 + 1 / D.q) * D.W P :=
            Finset.sum_le_sum fun P hP => D.abs_avg_mul_form2_hP_bP_le (D.Pst_subset_Q hP)
        _ = D.B ^ (1 + 1 / D.q) * ∑ P ∈ D.Pst, D.W P := by rw [Finset.mul_sum]
        _ ≤ _ := mul_le_mul_of_nonneg_left D.sum_W_Pst_le' (Real.rpow_nonneg hB0 _)
  -- term (2.19)–(2.20)
  have hT3 : |D.form2 D.Q (TestFun.ind D.Q)
      (∑ P ∈ D.PstOut4, (avg P D.G • D.bP P - D.coef P • TestFun.truncateₗ P D.u))| ≤
      D.B ^ (1 + 1 / D.q) *
          (D.F * lpNorm (D.G : (Fin d → ℝ) → ℝ) D.q * D.Q.vol ^ (1 / D.r)) +
        1 * (D.K₁ + D.K₂) * D.F * lpNorm (D.G : (Fin d → ℝ) → ℝ) D.q * D.Q.vol ^ (1 / D.r) := by
    rw [D.form2_hQ_sum_PstOut4_eq]
    refine (abs_sub _ _).trans (add_le_add ?_ ?_)
    · refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ P ∈ D.PstOut4, |avg P D.G * D.form2 P (TestFun.ind P) (D.bP P)|
          ≤ ∑ P ∈ D.PstOut4, D.B ^ (1 + 1 / D.q) * D.W P :=
            Finset.sum_le_sum fun P hP => D.abs_avg_mul_form2_hP_bP_le
              (D.Pst_subset_Q (Finset.mem_of_mem_filter P hP))
        _ = D.B ^ (1 + 1 / D.q) * ∑ P ∈ D.PstOut4, D.W P := by rw [Finset.mul_sum]
        _ ≤ _ := mul_le_mul_of_nonneg_left
            (D.sum_W_le_of_subset_Pst (Finset.filter_subset _ _)) (Real.rpow_nonneg hB0 _)
    · refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      refine D.sum_abs_coef_mul_form2_hP_u_le D.PstOut4
        (fun P hP => D.stoppingCubes_subset_tree' (D.mem_PstOut4.mp hP).1)
        (fun P hP => D.good_of_mem_stoppingCubes (D.mem_PstOut4.mp hP).1)
        (fun P hP => D.PstOut4_not_in_P4 hP) le_rfl fun f q hq => ?_
      rw [one_mul]
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        fun P _ _ => integral_nonneg fun x => by positivity) ?_
      exact D.sum_Pst_setIntegral_le f hq
  -- term (2.21)–(2.22)
  have hT4 : |D.form2 D.Q (TestFun.ind D.Q)
      (∑ P ∈ D.PstIn4, avg P D.G • D.bP P - ∑ P ∈ D.Pbar4, D.coef P • TestFun.truncateₗ P D.u
        + ∑ P ∈ D.Psib4, D.coef P • TestFun.truncateₗ P D.u)| ≤
      (D.B ^ (1 + 1 / D.q) + 2 * (2 ^ d / D.ε) * (D.K₁ + D.K₂) + 2 ^ d * D.K₃ * (2 ^ d / D.ε)) *
        (D.F * lpNorm (D.G : (Fin d → ℝ) → ℝ) D.q * D.Q.vol ^ (1 / D.r)) := by
    rw [D.form2_hQ_Pbar4_eq]
    exact (Finset.abs_sum_le_sum_abs _ _).trans D.sum_abs_form2_xi_le
  -- the contraction factor
  have hmul : ((1 - D.ε) * D.Q.vol) ^ (1 / D.r) = (1 - D.ε) ^ (1 / D.r) * D.Q.vol ^ (1 / D.r) :=
    Real.mul_rpow (by linarith) hV.le
  rw [hmul] at hT2
  have habs := abs_add_le (D.form2 D.Q (TestFun.ind D.Q) (avg D.Q D.G • D.u)
    + D.form2 D.Q (TestFun.ind D.Q) (∑ P ∈ D.Pst, (TestFun.truncateₗ P D.G - avg P D.G • D.bP P))
    + D.form2 D.Q (TestFun.ind D.Q)
      (∑ P ∈ D.PstOut4, (avg P D.G • D.bP P - D.coef P • TestFun.truncateₗ P D.u)))
    (D.form2 D.Q (TestFun.ind D.Q)
      (∑ P ∈ D.PstIn4, avg P D.G • D.bP P - ∑ P ∈ D.Pbar4, D.coef P • TestFun.truncateₗ P D.u
        + ∑ P ∈ D.Psib4, D.coef P • TestFun.truncateₗ P D.u))
  have habs2 := abs_add_le (D.form2 D.Q (TestFun.ind D.Q) (avg D.Q D.G • D.u)
    + D.form2 D.Q (TestFun.ind D.Q) (∑ P ∈ D.Pst, (TestFun.truncateₗ P D.G - avg P D.G • D.bP P)))
    (D.form2 D.Q (TestFun.ind D.Q)
      (∑ P ∈ D.PstOut4, (avg P D.G • D.bP P - D.coef P • TestFun.truncateₗ P D.u)))
  have habs3 := abs_add_le (D.form2 D.Q (TestFun.ind D.Q) (avg D.Q D.G • D.u))
    (D.form2 D.Q (TestFun.ind D.Q) (∑ P ∈ D.Pst, (TestFun.truncateₗ P D.G - avg P D.G • D.bP P)))
  refine (habs.trans (add_le_add
    (habs2.trans (add_le_add habs3 le_rfl)) le_rfl)).trans ?_
  convert add_le_add (add_le_add (add_le_add hT1 hT2) hT3) hT4 using 1
  unfold C₁₃
  ring

/-! ### §2.4 The second stopping time and the pruning of `h` (paper, p. 45–47)

Fix a cube `R ⊆ Q` of the tree which is not contained in a stopping cube of the first stopping
time and with `F_R = ∏_{j ≠ k,k+1} ‖f_j 𝟙_R‖_{p_j} > 0` (if `F_R = 0` the form `Λ_R` vanishes
identically). The second stopping time (2.24)–(2.30) is the first stopping time with the roles
of the slots `k`, `k+1` exchanged: the data is `R` in place of `Q`, the entries `f_j 𝟙_R`, the
testing function `v = b_{τ,𝐐_R,k}` in the slot `k`, the function `h_R = 𝟙_R` to be pruned, the
auxiliary Chebyshev functions `𝔤_R` (2.25) and `u_R` (2.27), and the extra `𝐏₃`-type condition
(2.29) for `u_R` with the constant of (2.10). All of §2.2–2.3 then applies to this data: the
measure bound (2.31), the upper bounds (2.32)–(2.37), and the pruned function `𝔥` of (2.38) is
the pruned function of the mirrored data. -/

/-! #### Local bounds on good cubes of the first stopping time (p. 47 and (2.45), (2.46))

For a good cube `S` of the first stopping time we bound `‖𝔤 𝟙_S‖_q`, `|[𝔤]_S|`, `F_S` and
`‖(𝔤 − [𝔤]_S [u]_S^{-1} u) 𝟙_S‖_q` in terms of `(|S|/|Q|)^{1/q}` or `(|S|/|Q|)^{1/p_j}`. The bound
(2.8) for `g` itself ("including the case `f_{k+1} = g`", p. 44) requires `g` to be one of the
functions of the Chebyshev condition `𝐏₁`; this is the hypothesis `GAux`. -/

/-- A cube in no first stopping cube lies in no cube of `𝐏₄`. [PROVED] -/
theorem not_in_P4_of_notInStopping {R : DyadicCube d} (hRs : D.NotInStopping R) :
    ∀ S ∈ D.P4, ¬ R.toSet ⊆ S.toSet := by
  intro S hS hsub
  obtain ⟨S', hS', hsub'⟩ := exists_maximal_superset D.hd D.union_subset_tree (D.P4_subset hS)
  exact hRs S' hS' (hsub.trans hsub')

/-- `g` is among the auxiliary functions of `𝐏₁` (with the exponent `q`). -/
def GAux : Prop := ∃ i : Fin D.m, D.aux i = D.G ∧ D.auxExp i = D.q

/-- The constant of (2.8): `C_G = 2^d (n+m)/ε`. -/
noncomputable def CG : ℝ := 2 ^ d * (n + D.m) / D.ε

theorem CG_pos : 0 < D.CG := by
  have := D.ε_pos
  have := D.one_le_n_add_m
  unfold CG
  positivity

theorem one_le_CG : 1 ≤ D.CG := by
  have hε := D.ε_pos
  have hε8 := D.ε_le
  have h1 := D.one_le_n_add_m
  have h2 : (1 : ℝ) ≤ 2 ^ d := one_le_pow₀ (by norm_num)
  unfold CG
  rw [le_div_iff₀ hε, one_mul]
  nlinarith

/-- **The bound (2.8) for `g`**, real form: `∫_P |g|^q ≤ C_G (|P|/|Q|) ‖g‖_q^q` on good cubes. It
holds when `g` is among the auxiliary functions of `𝐏₁` (`GBound_of_GAux`) and when `g = 𝟙_Q`
(`GBound_of_ind`; this is the case of the mirrored data of §2.4, where `h_R = 𝟙_R` is pruned). All
estimates of §2.5 are proved under this hypothesis. -/
def GBound : Prop := ∀ P : DyadicCube d, D.Good P →
  ∫ x in P.toSet, |(D.G : (Fin d → ℝ) → ℝ) x| ^ D.q ≤
    D.CG * (P.vol / D.Q.vol) * lpNorm (D.G : (Fin d → ℝ) → ℝ) D.q ^ D.q

theorem integral_G_rpow_le (hG : D.GBound) {P : DyadicCube d} (hP : D.Good P) :
    ∫ x in P.toSet, |(D.G : (Fin d → ℝ) → ℝ) x| ^ D.q ≤
      D.CG * (P.vol / D.Q.vol) * lpNorm (D.G : (Fin d → ℝ) → ℝ) D.q ^ D.q := hG P hP

/-- (2.8) for `g = 𝟙_Q`: `∫_P |𝟙_Q|^q = |P| ≤ C_G (|P|/|Q|) |Q|` since `C_G ≥ 1`. [PROVED] -/
theorem GBound_of_ind (h : D.G = TestFun.ind D.Q) : D.GBound := by
  intro P hP
  have hq0 : 0 < D.q := by linarith [D.hq]
  have hV := D.Q.vol_pos
  have hP0 := P.vol_pos
  have hPQ : P.toSet ⊆ D.Q.toSet := hP.1.1
  have h1 : ∫ x in P.toSet, |(D.G : (Fin d → ℝ) → ℝ) x| ^ D.q = P.vol := by
    have e : ∫ x in P.toSet, |(D.G : (Fin d → ℝ) → ℝ) x| ^ D.q = ∫ x in P.toSet, (1 : ℝ) :=
      setIntegral_congr_fun P.measurableSet_toSet fun x hx => by
        show |(D.G : (Fin d → ℝ) → ℝ) x| ^ D.q = 1
        rw [h, TestFun.coe_ind, Set.indicator_of_mem (hPQ hx), Pi.one_apply, abs_one,
          Real.one_rpow]
    rw [e, setIntegral_const, measureReal_def, P.volume_toSet, ENNReal.toReal_ofReal hP0.le,
      smul_eq_mul, mul_one]
  have h2 : lpNorm (D.G : (Fin d → ℝ) → ℝ) D.q ^ D.q = D.Q.vol := by
    rw [h, TestFun.lpNorm_ind D.Q hq0, ← Real.rpow_mul hV.le, one_div, inv_mul_cancel₀ hq0.ne',
      Real.rpow_one]
  rw [h1, h2]
  have := D.one_le_CG
  calc P.vol = 1 * (P.vol / D.Q.vol) * D.Q.vol := by field_simp
    _ ≤ D.CG * (P.vol / D.Q.vol) * D.Q.vol := by gcongr

/-- (2.8) for `g` when `g` is among the auxiliary functions of `𝐏₁`. [PROVED] -/
theorem GBound_of_GAux (hG : D.GAux) : D.GBound := by
  intro P hP
  have hq0 : 0 < D.q := by linarith [D.hq]
  obtain ⟨i, hi, he⟩ := hG
  have h := D.bound_2_8_aux D.hd hP i
  rw [hi, he] at h
  have := TestFun.setIntegral_rpow_le_of_avg_le D.G hq0 P D.Q D.CG_pos.le h
  have hQ : ∫ x in D.Q.toSet, |(D.G : (Fin d → ℝ) → ℝ) x| ^ D.q =
      lpNorm (D.G : (Fin d → ℝ) → ℝ) D.q ^ D.q := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun x hx => by rw [D.Gsupp x hx, abs_zero, Real.zero_rpow hq0.ne']),
      ← lpNorm_rpow_eq_integral hq0 (TestFun.memLp D.G.2 _)]
  rwa [hQ] at this

/-- `‖g 𝟙_P‖_q ≤ (C_G |P|/|Q|)^{1/q} ‖g‖_q` on good cubes. [PROVED] -/
theorem lpNorm_truncateₗ_G_le (hG : D.GBound) {P : DyadicCube d} (hP : D.Good P) :
    lpNorm (TestFun.truncateₗ P D.G : (Fin d → ℝ) → ℝ) D.q ≤
      D.CG ^ (1 / D.q) * (P.vol / D.Q.vol) ^ (1 / D.q) * lpNorm (D.G : (Fin d → ℝ) → ℝ) D.q := by
  have hq0 : 0 < D.q := by linarith [D.hq]
  have hV := D.Q.vol_pos
  have hP0 := P.vol_pos
  have hCG := D.CG_pos
  have h := TestFun.lpNorm_le_rpow_of_integral_le (TestFun.truncateₗ P D.G) hq0
    (C := D.CG * (P.vol / D.Q.vol) * lpNorm (D.G : (Fin d → ℝ) → ℝ) D.q ^ D.q) (by
      rw [← lpNorm_rpow_eq_integral hq0 (TestFun.memLp (TestFun.truncateₗ P D.G).2 _),
        TestFun.lpNorm_truncateₗ_rpow P D.G hq0]
      exact D.integral_G_rpow_le hG hP)
  refine h.trans (le_of_eq ?_)
  rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg (lpNorm_nonneg _ _) _),
    Real.mul_rpow D.CG_pos.le (by positivity), one_div,
    Real.rpow_rpow_inv (lpNorm_nonneg _ _) hq0.ne']

/-- `|[g]_P| ≤ C_G^{1/q} |Q|^{-1/q} ‖g‖_q` on good cubes ((2.45), (2.46)). [PROVED] -/
theorem abs_avg_G_le (hG : D.GBound) {P : DyadicCube d} (hP : D.Good P) :
    |avg P D.G| ≤ D.CG ^ (1 / D.q) * D.Q.vol ^ (-(1 / D.q)) * lpNorm (D.G : (Fin d → ℝ) → ℝ) D.q :=
      by
  have hq0 : 0 < D.q := by linarith [D.hq]
  have hV := D.Q.vol_pos
  have hP0 := P.vol_pos
  have h1 := abs_avg_mul_rpow_le P D.G D.hq.le
  have h2 := D.lpNorm_truncateₗ_G_le hG hP
  have hdiv : (P.vol / D.Q.vol) ^ (1 / D.q) = P.vol ^ (1 / D.q) * D.Q.vol ^ (-(1 / D.q)) := by
    rw [Real.div_rpow hP0.le hV.le, Real.rpow_neg hV.le, div_eq_mul_inv]
  rw [hdiv] at h2
  have hpos : 0 < P.vol ^ (1 / D.q) := Real.rpow_pos_of_pos hP0 _
  have h3 : |avg P D.G| * P.vol ^ (1 / D.q) ≤
      (D.CG ^ (1 / D.q) * D.Q.vol ^ (-(1 / D.q)) * lpNorm (D.G : (Fin d → ℝ) → ℝ) D.q) *
        P.vol ^ (1 / D.q) := by
    refine (h1.trans h2).trans (le_of_eq ?_)
    ring
  exact le_of_mul_le_mul_right h3 hpos

/-- `|x / [u]_P| ≤ 8 |x|` when `|[u]_P| > 1/8`. [PROVED] -/
theorem abs_div_avg_u_le {P : DyadicCube d} (h : 1 / 8 < |avg P D.u|) (x : ℝ) :
    |x / avg P D.u| ≤ 8 * |x| := by
  rw [abs_div, div_le_iff₀ (by linarith)]
  have := mul_le_mul_of_nonneg_left h.le (by positivity : (0 : ℝ) ≤ 8 * |x|)
  linarith

/-- A good cube `S` is not strictly contained in a stopping cube: if `S ⊆ P ∈ 𝐏` then `P ⊆ S`.
[PROVED] -/
theorem subset_of_good_of_subset {S P : DyadicCube d} (hS : D.Good S) (hP : P ∈ D.stoppingCubes)
    (h : S.toSet ⊆ P.toSet) : P.toSet ⊆ S.toSet := by
  by_contra hne
  have hSP : S ≠ P := fun e => hne (e ▸ subset_rfl)
  obtain ⟨ε, hε⟩ := DyadicCube.exists_child_of_ssubset D.hd h hSP
  exact hS.2 P hP ε hε

open Classical in
/-- The cubes of a subcollection of `𝐏` strictly containing a good cube `S`: none. [PROVED] -/
theorem filter_ssup_eq_empty {S : DyadicCube d} (hS : D.Good S) {s : Finset (DyadicCube d)}
    (hs : ∀ P ∈ s, P ∈ D.stoppingCubes) :
    (s.filter fun P => ¬ P.toSet ⊆ S.toSet ∧ S.toSet ⊆ P.toSet) = ∅ :=
  Finset.filter_eq_empty_iff.mpr fun P hP h => h.1 (D.subset_of_good_of_subset hS (hs P hP) h.2)

open Classical in
/-- The cubes of a collection with overlap `M` strictly containing `S` number at most `M`.
[PROVED] -/
theorem card_filter_ssup_le (S : DyadicCube d) {s : Finset (DyadicCube d)} {M : ℕ}
    (hM : ∀ x, (s.filter fun P => x ∈ P.toSet).card ≤ M) :
    (s.filter fun P => ¬ P.toSet ⊆ S.toSet ∧ S.toSet ⊆ P.toSet).card ≤ M := by
  refine (Finset.card_le_card ?_).trans (hM (fun i => (2 : ℝ) ^ S.m * S.l i))
  intro P hP
  rw [Finset.mem_filter] at hP ⊢
  exact ⟨hP.1, hP.2.2 S.corner_mem⟩

/-- `|∑_{P ∈ s} [g]_P/[u]_P| ≤ 8 #s C_G^{1/q} |Q|^{-1/q} ‖g‖_q` for good cubes with `|[u]_P| > 1/8`.
[PROVED] -/
theorem abs_sum_coef_le (hG : D.GBound) (s : Finset (DyadicCube d)) (hgood : ∀ P ∈ s, D.Good P)
    (hu : ∀ P ∈ s, 1 / 8 < |avg P D.u|) :
    |∑ P ∈ s, D.coef P| ≤
      s.card * (8 * (D.CG ^ (1 / D.q) * D.Q.vol ^ (-(1 / D.q)) *
        lpNorm (D.G : (Fin d → ℝ) → ℝ) D.q)) := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [← nsmul_eq_mul]
  refine Finset.sum_le_card_nsmul _ _ _ fun P hP => ?_
  exact (D.abs_coef_le (hu P hP)).trans
    (mul_le_mul_of_nonneg_left (D.abs_avg_G_le hG (hgood P hP)) (by norm_num))

/-- `‖∑_{P ∈ s} g 𝟙_P‖_q ≤ ‖g 𝟙_S‖_q` for a pairwise disjoint collection of subcubes of `S`.
[PROVED] -/
theorem lpNorm_sum_truncateₗ_le_of_subset (s : Finset (DyadicCube d))
    (hdisj : (↑s : Set (DyadicCube d)).PairwiseDisjoint DyadicCube.toSet) (f : TestFun d)
    {S : DyadicCube d} (hS : ∀ P ∈ s, P.toSet ⊆ S.toSet) {q : ℝ} (hq : 1 ≤ q) :
    lpNorm ((∑ P ∈ s, TestFun.truncateₗ P f : TestFun d) : (Fin d → ℝ) → ℝ) q ≤
      lpNorm (TestFun.truncateₗ S f : (Fin d → ℝ) → ℝ) q := by
  rw [Finset.sum_congr rfl fun P hP => (TestFun.truncateₗ_truncateₗ_of_subset (hS P hP) f).symm]
  exact lpNorm_sum_truncateₗ_le s hdisj _ hq

/-- The constant of the local norm bound for `𝔤`:
`C_loc = C_G^{1/q} (3 + 8 (2^d B/ε)^{1/q} (1 + 4 ⌊2^d/ε⌋)) + (2^d B/ε)^{1/q}`. -/
noncomputable def locConst : ℝ :=
  D.CG ^ (1 / D.q) * (3 + 8 * (2 ^ d * D.B / D.ε) ^ (1 / D.q) * (2 + 4 * ⌊(2 : ℝ) ^ d / D.ε⌋₊)) +
    (2 ^ d * D.B / D.ε) ^ (1 / D.q)

theorem locConst_nonneg : 0 ≤ D.locConst := by
  have := D.CG_pos
  have := D.ε_pos
  have : 0 ≤ D.B := by linarith [D.hB]
  unfold locConst
  positivity

/-- **The local norm bound for `𝔤`** (p. 47): on a good cube `S` of the first stopping time,
`‖𝔤 𝟙_S‖_q ≤ C_loc (|S|/|Q|)^{1/q} ‖g‖_q`. The terms of (2.12) are truncated to `S`: the stopping
cubes inside `S` are handled by disjointness and bounded overlap as in the norm bound for `𝔤`
(with `g 𝟙_S` in place of `g`), the stopping cubes never strictly contain the good cube `S`, and
the parents and siblings strictly containing `S` (at most `⌊2^d/ε⌋` of each) contribute
multiples of `u 𝟙_S` with coefficients bounded by (2.8) for `g` on the (good) parents and
siblings and by (2.11). [PROVED] -/
theorem lpNorm_truncateₗ_pruned_le (hG : D.GBound) {S : DyadicCube d} (hS : D.Good S) :
    lpNorm (TestFun.truncateₗ S D.pruned : (Fin d → ℝ) → ℝ) D.q ≤
      D.locConst * (S.vol / D.Q.vol) ^ (1 / D.q) * lpNorm (D.G : (Fin d → ℝ) → ℝ) D.q := by
  classical
  have hq := D.hq
  have hq0 : 0 < D.q := by linarith
  have hq1 : 1 ≤ D.q := hq.le
  have hε := D.ε_pos
  have hB0 : 0 ≤ D.B := by linarith [D.hB]
  have hV := D.Q.vol_pos
  have hS0 := S.vol_pos
  have hCG := D.CG_pos
  set N := lpNorm (D.G : (Fin d → ℝ) → ℝ) D.q with hN
  have hN0 : 0 ≤ N := lpNorm_nonneg _ _
  set ρ : ℝ := (S.vol / D.Q.vol) ^ (1 / D.q) with hρ
  have hρ0 : 0 ≤ ρ := Real.rpow_nonneg (by positivity) _
  set M := ⌊(2 : ℝ) ^ d / D.ε⌋₊ with hM
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  set C₉ : ℝ := 2 ^ d * D.B / D.ε with hC₉
  have hC₉0 : 0 ≤ C₉ := by positivity
  set cG : ℝ := D.CG ^ (1 / D.q) with hcG
  have hcG0 : 0 ≤ cG := Real.rpow_nonneg hCG.le _
  -- the local norms of `g` and `u` on `S`
  have hGS : lpNorm (TestFun.truncateₗ S D.G : (Fin d → ℝ) → ℝ) D.q ≤ cG * ρ * N :=
    D.lpNorm_truncateₗ_G_le hG hS
  have huS : lpNorm (TestFun.truncateₗ S D.u : (Fin d → ℝ) → ℝ) D.q ≤
      C₉ ^ (1 / D.q) * S.vol ^ (1 / D.q) := by
    have := D.lpNorm_truncateₗ_u_le hS
    rwa [Real.mul_rpow hC₉0 hS0.le] at this
  have hρeq : S.vol ^ (1 / D.q) * D.Q.vol ^ (-(1 / D.q)) = ρ := by
    rw [hρ, Real.div_rpow hS0.le hV.le, Real.rpow_neg hV.le, ← div_eq_mul_inv]
  -- the coefficient of `u 𝟙_S` coming from `t` cubes strictly containing `S`
  have hcoefS : ∀ (s : Finset (DyadicCube d)) (t : ℕ), (∀ P ∈ s, D.Good P) →
      (∀ P ∈ s, 1 / 8 < |avg P D.u|) →
      (s.filter fun P => ¬ P.toSet ⊆ S.toSet ∧ S.toSet ⊆ P.toSet).card ≤ t →
      lpNorm (((∑ P ∈ s with ¬ P.toSet ⊆ S.toSet ∧ S.toSet ⊆ P.toSet, D.coef P) •
        TestFun.truncateₗ S D.u : TestFun d) : (Fin d → ℝ) → ℝ) D.q ≤
        8 * C₉ ^ (1 / D.q) * cG * t * ρ * N := by
    intro s t hgood hu hcard
    rw [TestFun.lpNorm_smul]
    have h1 := D.abs_sum_coef_le hG (s.filter fun P => ¬ P.toSet ⊆ S.toSet ∧ S.toSet ⊆ P.toSet)
      (fun P hP => hgood P (Finset.mem_of_mem_filter P hP))
      (fun P hP => hu P (Finset.mem_of_mem_filter P hP))
    have hcard' : ((s.filter fun P => ¬ P.toSet ⊆ S.toSet ∧ S.toSet ⊆ P.toSet).card : ℝ) ≤ t := by
      exact_mod_cast hcard
    calc |∑ P ∈ s with ¬ P.toSet ⊆ S.toSet ∧ S.toSet ⊆ P.toSet, D.coef P| *
          lpNorm (TestFun.truncateₗ S D.u : (Fin d → ℝ) → ℝ) D.q
        ≤ (t * (8 * (cG * D.Q.vol ^ (-(1 / D.q)) * N))) * (C₉ ^ (1 / D.q) * S.vol ^ (1 / D.q)) := by
          refine mul_le_mul (h1.trans ?_) huS (lpNorm_nonneg _ _) (by positivity)
          exact mul_le_mul_of_nonneg_right hcard' (by positivity)
      _ = 8 * C₉ ^ (1 / D.q) * cG * t * (S.vol ^ (1 / D.q) * D.Q.vol ^ (-(1 / D.q))) * N := by ring
      _ = _ := by rw [hρeq]
  -- overlap bounds
  have hM4 : ∀ x, (D.Pbar4.filter fun R => x ∈ R.toSet).card ≤ M := fun x =>
    Nat.le_floor (D.card_Pbar4_filter_le x)
  have hM4' : ∀ x, (D.Psib4.filter fun R => x ∈ R.toSet).card ≤ M := fun x =>
    Nat.le_floor (D.card_Psib4_filter_le x)
  have hdisjOut : (↑D.PstOut4 : Set (DyadicCube d)).PairwiseDisjoint DyadicCube.toSet :=
    fun P hP R hR hne => maximal_pairwiseDisjoint _ (D.mem_PstOut4.mp hP).1
      (D.mem_PstOut4.mp hR).1 hne
  have hdisjIn : (↑D.PstIn4 : Set (DyadicCube d)).PairwiseDisjoint DyadicCube.toSet :=
    fun P hP R hR hne => maximal_pairwiseDisjoint _ (D.mem_PstIn4.mp hP).1
      (D.mem_PstIn4.mp hR).1 hne
  have hM1 : ∀ x, (D.PstOut4.filter fun P => x ∈ P.toSet).card ≤ 1 := fun x =>
    Finset.card_le_one.mpr fun P hP R hR => by
      rw [Finset.mem_filter] at hP hR
      by_contra hne
      exact Set.disjoint_left.mp (hdisjOut hP.1 hR.1 hne) hP.2 hR.2
  -- the terms of `𝔤 𝟙_S`
  have hexp : TestFun.truncateₗ S D.pruned =
      TestFun.truncateₗ S D.G - avg D.Q D.G • TestFun.truncateₗ S D.u
      - TestFun.truncateₗ S (∑ P ∈ D.PstOut4, TestFun.truncateₗ P D.G)
      + TestFun.truncateₗ S (∑ P ∈ D.PstOut4, D.coef P • TestFun.truncateₗ P D.u)
      - TestFun.truncateₗ S (∑ P ∈ D.PstIn4, TestFun.truncateₗ P D.G)
      + TestFun.truncateₗ S (∑ P ∈ D.Pbar4, D.coef P • TestFun.truncateₗ P D.u)
      - TestFun.truncateₗ S (∑ P ∈ D.Psib4, D.coef P • TestFun.truncateₗ P D.u) := by
    unfold pruned
    simp only [map_sub, map_add, map_smul]
  -- a `g`-sum over stopping cubes, truncated to `S`
  have hGsum : ∀ s : Finset (DyadicCube d), (∀ P ∈ s, P ∈ D.stoppingCubes) →
      (↑s : Set (DyadicCube d)).PairwiseDisjoint DyadicCube.toSet →
      lpNorm (TestFun.truncateₗ S (∑ P ∈ s, TestFun.truncateₗ P D.G) : (Fin d → ℝ) → ℝ) D.q ≤
        cG * ρ * N := by
    intro s hs hdisj
    have e : (∑ P ∈ s, TestFun.truncateₗ P D.G) =
        ∑ P ∈ s, (1 : ℝ) • TestFun.truncateₗ P D.G := by simp
    rw [e, TestFun.truncateₗ_sum_smul_truncateₗ, D.filter_ssup_eq_empty hS hs, Finset.sum_empty,
      zero_smul, add_zero]
    simp only [one_smul]
    refine (lpNorm_sum_truncateₗ_le_of_subset _ (hdisj.subset (Finset.filter_subset _ _)) D.G
      (fun P hP => (Finset.mem_filter.mp hP).2) hq1).trans hGS
  -- a coefficient sum, truncated to `S`
  have hcsum : ∀ (s : Finset (DyadicCube d)) (t : ℕ),
      (∀ x, (s.filter fun P => x ∈ P.toSet).card ≤ t) → (∀ P ∈ s, D.Good P) →
      (∀ P ∈ s, 1 / 8 < |avg P D.u|) →
      lpNorm (TestFun.truncateₗ S (∑ P ∈ s, D.coef P • TestFun.truncateₗ P D.u) :
        (Fin d → ℝ) → ℝ) D.q ≤ 8 * C₉ ^ (1 / D.q) * cG * t * ρ * N +
          8 * C₉ ^ (1 / D.q) * cG * t * ρ * N := by
    intro s t ht hgood hu
    rw [TestFun.truncateₗ_sum_smul_truncateₗ]
    refine (TestFun.lpNorm_add_le _ _ hq1).trans (add_le_add ?_ ?_)
    · have h := D.lpNorm_sum_coef_le (s.filter fun P => P.toSet ⊆ S.toSet) (M := t)
        (fun x => (Finset.card_le_card (Finset.filter_subset_filter _ (Finset.filter_subset _
          _))).trans
          (ht x))
        (fun P hP => hgood P (Finset.mem_of_mem_filter P hP))
        (fun P hP => hu P (Finset.mem_of_mem_filter P hP)) (S := S)
        (fun P hP => (Finset.mem_filter.mp hP).2)
      refine h.trans ?_
      calc 8 * C₉ ^ (1 / D.q) * t * lpNorm (TestFun.truncateₗ S D.G : (Fin d → ℝ) → ℝ) D.q
          ≤ 8 * C₉ ^ (1 / D.q) * t * (cG * ρ * N) := by gcongr
        _ = _ := by ring
    · exact hcoefS s t hgood hu (card_filter_ssup_le S ht)
  -- the seven terms
  have h0 := hGS
  have h1 : lpNorm ((avg D.Q D.G • TestFun.truncateₗ S D.u : TestFun d) : (Fin d → ℝ) → ℝ) D.q ≤
      C₉ ^ (1 / D.q) * ρ * N := by
    rw [TestFun.lpNorm_smul]
    have hG := abs_avg_le D.Q D.G hq1
    calc |avg D.Q D.G| * lpNorm (TestFun.truncateₗ S D.u : (Fin d → ℝ) → ℝ) D.q
        ≤ (D.Q.vol ^ (-(1 / D.q)) * N) * (C₉ ^ (1 / D.q) * S.vol ^ (1 / D.q)) :=
          mul_le_mul hG huS (lpNorm_nonneg _ _) (by positivity)
      _ = C₉ ^ (1 / D.q) * (S.vol ^ (1 / D.q) * D.Q.vol ^ (-(1 / D.q))) * N := by ring
      _ = _ := by rw [hρeq]
  have h2 := hGsum D.PstOut4 (fun P hP => (D.mem_PstOut4.mp hP).1) hdisjOut
  have h4 := hGsum D.PstIn4 (fun P hP => (D.mem_PstIn4.mp hP).1) hdisjIn
  have h3 := hcsum D.PstOut4 1 hM1 (fun P hP => D.good_of_mem_stoppingCubes (D.mem_PstOut4.mp hP).1)
    (fun P hP => D.bound_2_11 D.hd (D.stoppingCubes_subset_tree' (D.mem_PstOut4.mp hP).1)
      (D.PstOut4_not_in_P4 hP))
  have h5 := hcsum D.Pbar4 M hM4 (fun P hP => D.good_of_Pbar4 hP)
    (fun P hP => D.bound_2_11 D.hd (D.Pbar4_mem_tree hP) (D.Pbar4_not_in_P4 hP))
  have h6 := hcsum D.Psib4 M hM4' (fun P hP => D.good_of_Psib4 hP)
    (fun P hP => D.bound_2_11 D.hd (D.Psib4_mem_tree hP) (D.Psib4_not_in_P4 hP))
  -- the triangle inequality
  set T₀ := TestFun.truncateₗ S D.G
  set T₁ : TestFun d := avg D.Q D.G • TestFun.truncateₗ S D.u
  set T₂ := TestFun.truncateₗ S (∑ P ∈ D.PstOut4, TestFun.truncateₗ P D.G)
  set T₃ := TestFun.truncateₗ S (∑ P ∈ D.PstOut4, D.coef P • TestFun.truncateₗ P D.u)
  set T₄ := TestFun.truncateₗ S (∑ P ∈ D.PstIn4, TestFun.truncateₗ P D.G)
  set T₅ := TestFun.truncateₗ S (∑ P ∈ D.Pbar4, D.coef P • TestFun.truncateₗ P D.u)
  set T₆ := TestFun.truncateₗ S (∑ P ∈ D.Psib4, D.coef P • TestFun.truncateₗ P D.u)
  have t1 := TestFun.lpNorm_sub_le (T₀ - T₁ - T₂ + T₃ - T₄ + T₅) T₆ hq1
  have t2 := TestFun.lpNorm_add_le (T₀ - T₁ - T₂ + T₃ - T₄) T₅ hq1
  have t3 := TestFun.lpNorm_sub_le (T₀ - T₁ - T₂ + T₃) T₄ hq1
  have t4 := TestFun.lpNorm_add_le (T₀ - T₁ - T₂) T₃ hq1
  have t5 := TestFun.lpNorm_sub_le (T₀ - T₁) T₂ hq1
  have t6 := TestFun.lpNorm_sub_le T₀ T₁ hq1
  rw [hexp]
  have hcast : ((1 : ℕ) : ℝ) = 1 := Nat.cast_one
  rw [hcast] at h3
  calc lpNorm ((T₀ - T₁ - T₂ + T₃ - T₄ + T₅ - T₆ : TestFun d) : (Fin d → ℝ) → ℝ) D.q
      ≤ lpNorm (T₀ : (Fin d → ℝ) → ℝ) D.q + lpNorm (T₁ : (Fin d → ℝ) → ℝ) D.q +
          lpNorm (T₂ : (Fin d → ℝ) → ℝ) D.q + lpNorm (T₃ : (Fin d → ℝ) → ℝ) D.q +
          lpNorm (T₄ : (Fin d → ℝ) → ℝ) D.q + lpNorm (T₅ : (Fin d → ℝ) → ℝ) D.q +
          lpNorm (T₆ : (Fin d → ℝ) → ℝ) D.q := by linarith
    _ ≤ cG * ρ * N + C₉ ^ (1 / D.q) * ρ * N + cG * ρ * N +
          (8 * C₉ ^ (1 / D.q) * cG * 1 * ρ * N + 8 * C₉ ^ (1 / D.q) * cG * 1 * ρ * N) +
          cG * ρ * N +
          (8 * C₉ ^ (1 / D.q) * cG * M * ρ * N + 8 * C₉ ^ (1 / D.q) * cG * M * ρ * N) +
          (8 * C₉ ^ (1 / D.q) * cG * M * ρ * N + 8 * C₉ ^ (1 / D.q) * cG * M * ρ * N) :=
        add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add h0 h1) h2) h3)
          h4) h5) h6
    _ = D.locConst * ρ * N := by
        unfold locConst
        simp only [hC₉, hcG, hM]
        ring

/-- The function `ψ_S = 𝔤 − [𝔤]_S [u]_S^{-1} u` of (2.23), (2.47). -/
noncomputable def psi (S : DyadicCube d) : TestFun d :=
  D.pruned - (avg S D.pruned / avg S D.u) • D.u

/-- The constant of the local bound for `ψ_S`: `C_ψ = C_loc (1 + 8 (2^d B/ε)^{1/q})`. -/
noncomputable def psiConst : ℝ := D.locConst * (1 + 8 * (2 ^ d * D.B / D.ε) ^ (1 / D.q))

theorem psiConst_nonneg : 0 ≤ D.psiConst := by
  have := D.locConst_nonneg
  have := D.ε_pos
  have : 0 ≤ D.B := by linarith [D.hB]
  unfold psiConst
  positivity

/-- **The local bound for `ψ_S`** (p. 49): for a cube `S` of the tree not contained in a first
stopping cube, `‖ψ_S 𝟙_S‖_q ≤ C_ψ (|S|/|Q|)^{1/q} ‖g‖_q`. [PROVED] -/
theorem lpNorm_truncateₗ_psi_le (hG : D.GBound) {S : DyadicCube d} (hS : S ∈ D.tree)
    (hSs : D.NotInStopping S) :
    lpNorm (TestFun.truncateₗ S (D.psi S) : (Fin d → ℝ) → ℝ) D.q ≤
      D.psiConst * (S.vol / D.Q.vol) ^ (1 / D.q) * lpNorm (D.G : (Fin d → ℝ) → ℝ) D.q := by
  have hq := D.hq
  have hq0 : 0 < D.q := by linarith
  have hq1 : 1 ≤ D.q := hq.le
  have hε := D.ε_pos
  have hB0 : 0 ≤ D.B := by linarith [D.hB]
  have hV := D.Q.vol_pos
  have hS0 := S.vol_pos
  have hgood : D.Good S := D.good_of_notInStopping hS hSs
  have hu8 : 1 / 8 < |avg S D.u| := D.bound_2_11 D.hd hS (D.not_in_P4_of_notInStopping hSs)
  set N := lpNorm (D.G : (Fin d → ℝ) → ℝ) D.q with hN
  have hN0 : 0 ≤ N := lpNorm_nonneg _ _
  set ρ : ℝ := (S.vol / D.Q.vol) ^ (1 / D.q) with hρ
  have hρ0 : 0 ≤ ρ := Real.rpow_nonneg (by positivity) _
  set C₉ : ℝ := 2 ^ d * D.B / D.ε with hC₉
  have hC₉0 : 0 ≤ C₉ := by positivity
  have hloc := D.lpNorm_truncateₗ_pruned_le hG hgood
  have hL0 := D.locConst_nonneg
  have huS : lpNorm (TestFun.truncateₗ S D.u : (Fin d → ℝ) → ℝ) D.q ≤
      C₉ ^ (1 / D.q) * S.vol ^ (1 / D.q) := by
    have := D.lpNorm_truncateₗ_u_le hgood
    rwa [Real.mul_rpow hC₉0 hS0.le] at this
  -- `|[𝔤]_S| |S|^{1/q} ≤ ‖𝔤 𝟙_S‖_q`
  have havg := abs_avg_mul_rpow_le S D.pruned hq1
  have hcoef : |avg S D.pruned / avg S D.u| * lpNorm (TestFun.truncateₗ S D.u : (Fin d → ℝ) → ℝ) D.q
      ≤ 8 * C₉ ^ (1 / D.q) * (D.locConst * ρ * N) := by
    calc |avg S D.pruned / avg S D.u| * lpNorm (TestFun.truncateₗ S D.u : (Fin d → ℝ) → ℝ) D.q
        ≤ (8 * |avg S D.pruned|) * (C₉ ^ (1 / D.q) * S.vol ^ (1 / D.q)) :=
          mul_le_mul (D.abs_div_avg_u_le hu8 _) huS (lpNorm_nonneg _ _) (by positivity)
      _ = 8 * C₉ ^ (1 / D.q) * (|avg S D.pruned| * S.vol ^ (1 / D.q)) := by ring
      _ ≤ 8 * C₉ ^ (1 / D.q) * (D.locConst * ρ * N) :=
          mul_le_mul_of_nonneg_left (havg.trans hloc) (by positivity)
  unfold psi
  rw [map_sub, map_smul]
  refine (TestFun.lpNorm_sub_le _ _ hq1).trans ?_
  rw [TestFun.lpNorm_smul]
  calc lpNorm (TestFun.truncateₗ S D.pruned : (Fin d → ℝ) → ℝ) D.q +
        |avg S D.pruned / avg S D.u| * lpNorm (TestFun.truncateₗ S D.u : (Fin d → ℝ) → ℝ) D.q
      ≤ D.locConst * ρ * N + 8 * C₉ ^ (1 / D.q) * (D.locConst * ρ * N) := add_le_add hloc hcoef
    _ = D.psiConst * ρ * N := by
        unfold psiConst
        ring

/-- `∑_{j ≠ k,k+1} 1/p_j = 1 − 1/r − 1/q`. [PROVED] -/
theorem sum_J_inv : ∑ j ∈ D.J, 1 / D.p.p j = 1 - 1 / D.r - 1 / D.q := by
  have hab := D.hab
  have h := D.p.sum_inv
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ D.a),
    ← Finset.add_sum_erase (Finset.univ.erase D.a) _
      (Finset.mem_erase.mpr ⟨Ne.symm hab, Finset.mem_univ D.b⟩)] at h
  simp only [one_div]
  change ∑ j ∈ (Finset.univ.erase D.a).erase D.b, (D.p.p j)⁻¹ = 1 - (D.p.p D.a)⁻¹ - (D.p.p D.b)⁻¹
  linarith

/-- **The local bound for `F_P`** (from (2.8)): on a good cube `P`,
`F_P ≤ (C_G |P|/|Q|)^{1-1/r-1/q} F`. [PROVED] -/
theorem FP_le (hP : D.Good P) :
    D.FP P ≤ (D.CG * (P.vol / D.Q.vol)) ^ (1 - 1 / D.r - 1 / D.q) * D.F := by
  have hV := D.Q.vol_pos
  have hP0 := P.vol_pos
  have hC : 0 ≤ D.CG * (P.vol / D.Q.vol) := by have := D.CG_pos; positivity
  have hpj : ∀ j, 0 < D.p.p j := fun j => by linarith [D.p.one_lt j]
  have hterm : ∀ j ∈ D.J, lpNorm (TestFun.truncateₗ P (D.g j) : (Fin d → ℝ) → ℝ) (D.p.p j) ≤
      (D.CG * (P.vol / D.Q.vol)) ^ (1 / D.p.p j) * lpNorm (D.g j : (Fin d → ℝ) → ℝ) (D.p.p j) := by
    intro j hj
    have h := TestFun.setIntegral_rpow_le_of_avg_le (D.g j) (hpj j) P D.Q D.CG_pos.le
      (D.bound_2_8 D.hd hP hj)
    have hQ : ∫ x in D.Q.toSet, |(D.g j : (Fin d → ℝ) → ℝ) x| ^ D.p.p j =
        lpNorm (D.g j : (Fin d → ℝ) → ℝ) (D.p.p j) ^ D.p.p j := by
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun x hx => by rw [D.supp j x hx, abs_zero, Real.zero_rpow (hpj j).ne']),
        ← lpNorm_rpow_eq_integral (hpj j) (TestFun.memLp (D.g j).2 _)]
    rw [hQ] at h
    have h2 := TestFun.lpNorm_le_rpow_of_integral_le (TestFun.truncateₗ P (D.g j)) (hpj j)
      (C := D.CG * (P.vol / D.Q.vol) * lpNorm (D.g j : (Fin d → ℝ) → ℝ) (D.p.p j) ^ D.p.p j) (by
        rw [← lpNorm_rpow_eq_integral (hpj j) (TestFun.memLp (TestFun.truncateₗ P (D.g j)).2 _),
          TestFun.lpNorm_truncateₗ_rpow P (D.g j) (hpj j)]
        exact h)
    refine h2.trans (le_of_eq ?_)
    rw [Real.mul_rpow hC (Real.rpow_nonneg (lpNorm_nonneg _ _) _), one_div,
      Real.rpow_rpow_inv (lpNorm_nonneg _ _) (hpj j).ne']
  unfold FP F
  calc ∏ j ∈ D.J, lpNorm (TestFun.truncateₗ P (D.g j) : (Fin d → ℝ) → ℝ) (D.p.p j)
      ≤ ∏ j ∈ D.J, (D.CG * (P.vol / D.Q.vol)) ^ (1 / D.p.p j) *
          lpNorm (D.g j : (Fin d → ℝ) → ℝ) (D.p.p j) :=
        Finset.prod_le_prod₀ (fun _ _ => lpNorm_nonneg _ _) hterm
    _ = _ := by
        rw [Finset.prod_mul_distrib, ← Real.rpow_sum_of_nonneg hC
          (fun j _ => one_div_nonneg.mpr (hpj j).le), D.sum_J_inv]

/-- The entries of the second stopping time: `f_j 𝟙_R` for `j ≠ k`, and `v = b_{τ,𝐐_R,k}` in the
slot `k`. -/
noncomputable def g2 (R : DyadicCube d) : Fin n → TestFun d :=
  Function.update (fun j => TestFun.truncateₗ R (D.g j)) D.a (D.vP R)

theorem g2_a (R : DyadicCube d) : D.g2 R D.a = D.vP R := by
  simp [g2]

theorem g2_of_ne (R : DyadicCube d) {j : Fin n} (hj : j ≠ D.a) :
    D.g2 R j = TestFun.truncateₗ R (D.g j) := by
  simp [g2, Function.update_of_ne hj]

/-- Truncating the mirrored entries to `S ⊆ R`. [PROVED] -/
theorem truncateₗ_g2 {R S : DyadicCube d} (hSR : S.toSet ⊆ R.toSet) :
    (fun j => TestFun.truncateₗ S (D.g2 R j)) =
      Function.update (fun j => TestFun.truncateₗ S (D.g j)) D.a (TestFun.truncateₗ S (D.vP R)) :=
        by
  funext j
  by_cases hj : j = D.a
  · rw [hj, D.g2_a, Function.update_self]
  · rw [D.g2_of_ne R hj, Function.update_of_ne hj, TestFun.truncateₗ_truncateₗ_of_subset hSR]

/-- `F'_S = F_S`: the product of the norms of the mirrored entries truncated to `S ⊆ R`. -/
theorem prod_g2 {R S : DyadicCube d} (hSR : S.toSet ⊆ R.toSet) :
    ∏ j ∈ (Finset.univ.erase D.b).erase D.a,
      lpNorm (TestFun.truncateₗ S (D.g2 R j) : (Fin d → ℝ) → ℝ) (D.p.p j) = D.FP S := by
  rw [Finset.erase_right_comm]
  unfold FP
  refine Finset.prod_congr rfl fun j hj => ?_
  rw [J, Finset.mem_erase, Finset.mem_erase] at hj
  rw [D.g2_of_ne R hj.2.1, TestFun.truncateₗ_truncateₗ_of_subset hSR]

theorem prod_g2' (R : DyadicCube d) :
    ∏ j ∈ (Finset.univ.erase D.b).erase D.a, lpNorm (D.g2 R j : (Fin d → ℝ) → ℝ) (D.p.p j) =
      D.FP R := by
  rw [Finset.erase_right_comm]
  unfold FP
  refine Finset.prod_congr rfl fun j hj => ?_
  rw [J, Finset.mem_erase, Finset.mem_erase] at hj
  rw [D.g2_of_ne R hj.2.1]

/-- **The mirror identity**: the two-slot form of the mirrored data is the two-slot form of the
original data with the slots exchanged, `Λ'_S(x, y) = Λ_S(y, x)` for `S ⊆ R`. [PROVED] -/
theorem twoSlotForm_g2 {R S : DyadicCube d} (hSR : S.toSet ⊆ R.toSet) (x y : TestFun d) :
    twoSlotForm D.T D.b D.a (D.g2 R) S x y = twoSlotForm D.T D.a D.b D.g S y x := by
  unfold twoSlotForm
  rw [D.truncateₗ_g2 hSR, Function.update_comm D.hab.symm, Function.update_idem]

theorem g2_supp {R : DyadicCube d} (hR : R ∈ D.tree) (j : Fin n) : SupportedOn (D.g2 R j) R := by
  by_cases hj : j = D.a
  · rw [hj, D.g2_a]
    exact D.vP_supp R hR.1
  · rw [D.g2_of_ne R hj]
    exact TestFun.truncateₗ_supportedOn R (D.g j)

/-- The second-stopping-time tree `𝒟_{N'}(R)` with `N' = N − (m(Q) − m(R))` lies in `𝒟_N(Q)`. -/
theorem second_N_spec {R : DyadicCube d} (hR : R ∈ D.tree) :
    R.m - ((R.m - (D.Q.m - D.N)).toNat : ℤ) = D.Q.m - D.N := by
  have := hR.2
  rw [Int.toNat_of_nonneg (by omega)]
  ring

/-- The constant `K_R` of the extra `𝐏₃`-type condition (2.29): the constant of (2.10) at `R`. -/
noncomputable def KR (R : DyadicCube d) : ℝ :=
  2 ^ d * (D.B * D.F * lpNorm (D.u : (Fin d → ℝ) → ℝ) D.q * D.ε⁻¹) *
    (R.vol / D.Q.vol) ^ (1 - 1 / D.r)

theorem KR_pos (R : DyadicCube d) : 0 < D.KR R := by
  have hB : 0 < D.B := by linarith [D.hB]
  have hF := D.Fpos'
  have hu := D.lpNorm_u_pos
  have hε := D.ε_pos
  have hV := D.Q.vol_pos
  have hR := R.vol_pos
  unfold KR
  positivity

/-- **The data of the second stopping time** (§2.4) for a cube `R` of the tree, not contained in a
first stopping cube, with `F_R > 0`. -/
noncomputable def second (R : DyadicCube d) (hR : R ∈ D.tree) (hRs : D.NotInStopping R)
    (hFR : 0 < D.FP R) : StoppingData d n where
  T := D.T
  p := D.p
  B := D.B
  Q := R
  hd := D.hd
  N := (R.m - (D.Q.m - D.N)).toNat
  a := D.b
  b := D.a
  hab := D.hab.symm
  g := D.g2 R
  G := TestFun.ind R
  hB := D.hB
  supp := D.g2_supp hR
  Gsupp := TestFun.ind_supportedOn R
  Gpos := by
    rw [TestFun.lpNorm_ind R (by linarith [D.hr])]
    exact Real.rpow_pos_of_pos R.vol_pos _
  mean := by
    rw [D.g2_a]
    exact D.vP_mean R hR.1
  norm := by
    rw [D.g2_a]
    exact D.vP_norm R hR.1
  Fpos := by
    rw [D.prod_g2']
    exact hFR
  testing := by
    intro ρ hρ
    rw [← twoSlotForm_self D.T D.hab.symm, D.twoSlotForm_g2 (subset_refl _), D.g2_a, D.prod_g2']
    exact D.testing_vP R hR.1 ρ hρ
  bP := D.vP
  vP := D.bP
  A := D.T.A₀ D.p
  hA0 := D.T.A₀_nonneg D.p
  bP_supp := fun S hS => D.vP_supp S (hS.trans hR.1)
  bP_mean := fun S hS => D.vP_mean S (hS.trans hR.1)
  bP_norm := fun S hS => D.vP_norm S (hS.trans hR.1)
  vP_supp := fun S hS => D.bP_supp S (hS.trans hR.1)
  vP_mean := fun S hS => D.bP_mean S (hS.trans hR.1)
  vP_norm := fun S hS => D.bP_norm S (hS.trans hR.1)
  testing_bP := by
    intro S hS ρ hρ
    rw [D.twoSlotForm_g2 hS, D.prod_g2 hS]
    exact D.testing_vP S (hS.trans hR.1) ρ hρ
  testing_vP := by
    intro S hS ρ hρ
    rw [D.twoSlotForm_g2 hS, D.prod_g2 hS]
    exact D.testing_bP S (hS.trans hR.1) ρ hρ
  estimateA := by
    intro S hS ρ _
    have h := abs_twoSlotForm_le_of_bound D.T D.p D.hab.symm (D.g2 R) S (TestFun.ind S) ρ
      (D.T.abs_form_le_A₀ D.p)
    rw [TestFun.truncateₗ_ind, TestFun.lpNorm_ind S (by linarith [D.hq])] at h
    refine h.trans ?_
    have := D.T.A₀_nonneg D.p
    have := S.vol_pos
    have hprod : 0 ≤ ∏ j ∈ (Finset.univ.erase D.b).erase D.a,
        lpNorm (TestFun.truncateₗ S (D.g2 R j) : (Fin d → ℝ) → ℝ) (D.p.p j) :=
      Finset.prod_nonneg fun _ _ => lpNorm_nonneg _ _
    gcongr
    exact TestFun.lpNorm_truncateₗ_le S ρ (by linarith [D.hr])
  m := 2
  aux := fun i => if i = 0 then TestFun.truncateₗ R D.pruned else TestFun.truncateₗ R D.u
  auxExp := fun _ => D.q
  aux_pos := fun _ => by linarith [D.hq]
  aux_supp := by
    intro i
    split_ifs <;> exact TestFun.truncateₗ_supportedOn R _
  w := TestFun.truncateₗ R D.u
  K := D.KR R
  hK := D.KR_pos R
  w_test := by
    intro ρ hρ hρ0
    rw [D.twoSlotForm_g2 (subset_refl _), twoSlotForm_truncateₗ_right, twoSlotForm_self D.T D.hab]
    exact D.bound_2_10 D.hd (D.good_of_notInStopping hR hRs) ρ hρ hρ0
  g_const := by
    intro j T hT hTm
    have hTm' : T.m = D.Q.m - D.N := hTm.trans (D.second_N_spec hR)
    by_cases hj : j = D.a
    · subst hj
      rw [D.g2_a]
      exact D.vP_const R hR.1 hR.2 T (hT.trans hR.1) hTm'
    · rw [D.g2_of_ne R hj]
      exact constOn_truncateₗ (Or.inl hT) (D.g_const j T (hT.trans hR.1) hTm')
  G_const := fun T hT _ => constOn_ind (Or.inl hT)
  bP_const := fun P hP hPm T hT hTm =>
    D.vP_const P (hP.trans hR.1) (by rw [D.second_N_spec hR] at hPm; exact hPm) T (hT.trans hR.1)
      (hTm.trans (D.second_N_spec hR))
  vP_const := fun P hP hPm T hT hTm =>
    D.bP_const P (hP.trans hR.1) (by rw [D.second_N_spec hR] at hPm; exact hPm) T (hT.trans hR.1)
      (hTm.trans (D.second_N_spec hR))

/-- The tree of the second stopping time is contained in the tree of the first. [PROVED] -/
theorem second_tree_subset {R : DyadicCube d} (hR : R ∈ D.tree) (hRs : D.NotInStopping R)
    (hFR : 0 < D.FP R) : (D.second R hR hRs hFR).tree ⊆ D.tree := by
  intro S hS
  obtain ⟨hSR, hm⟩ := hS
  refine ⟨hSR.trans hR.1, ?_⟩
  have h2 := D.second_N_spec hR
  simp only [second] at hm
  omega

/-- **The claim (2.31)**: `∑_{S ∈ 𝐒} |S| ≤ (1 − ε)|R|` for the stopping cubes `𝐒` of the second
stopping time. [PROVED] -/
theorem volume_second_stoppingCubes_le {R : DyadicCube d} (hR : R ∈ D.tree)
    (hRs : D.NotInStopping R) (hFR : 0 < D.FP R) :
    volume (⋃ S ∈ (D.second R hR hRs hFR).stoppingCubes, S.toSet) ≤
      ENNReal.ofReal ((1 - (D.second R hR hRs hFR).ε) * R.vol) :=
  (D.second R hR hRs hFR).volume_stoppingCubes_le

/-- The parameter `ε` of the second stopping time is the parameter `ε` of the first. [PROVED] -/
theorem second_ε {R : DyadicCube d} (hR : R ∈ D.tree) (hRs : D.NotInStopping R)
    (hFR : 0 < D.FP R) : (D.second R hR hRs hFR).ε = D.ε := rfl

section SecondBounds

variable {R : DyadicCube d} (hR : R ∈ D.tree) (hRs : D.NotInStopping R) (hFR : 0 < D.FP R)

theorem second_u : (D.second R hR hRs hFR).u = D.vP R := D.g2_a R

theorem second_g_of_ne {j : Fin n} (hj : j ≠ D.a) :
    (D.second R hR hRs hFR).g j = TestFun.truncateₗ R (D.g j) := D.g2_of_ne R hj

theorem second_F : (D.second R hR hRs hFR).F = D.FP R := D.prod_g2' R

theorem second_aux (i : Fin 2) :
    (D.second R hR hRs hFR).aux i =
      if (i : ℕ) = 0 then TestFun.truncateₗ R D.pruned else TestFun.truncateₗ R D.u := by
  change (if i = 0 then TestFun.truncateₗ R D.pruned else TestFun.truncateₗ R D.u) = _
  simp only [Fin.ext_iff, Fin.val_zero]

/-- **(2.30), the lower bound**: `|[v]_S| > 1/8` for `S` in the tree of `R` not contained in a
cube of `𝐒₄`. [PROVED] -/
theorem second_bound_2_30 {S : DyadicCube d} (hS : S ∈ (D.second R hR hRs hFR).tree)
    (hS4 : ∀ T ∈ (D.second R hR hRs hFR).P4, ¬ S.toSet ⊆ T.toSet) :
    1 / 8 < |avg S (D.vP R)| := by
  have h := (D.second R hR hRs hFR).bound_2_11 D.hd hS hS4
  rwa [second_u] at h

/-- **(2.32), first inequality**: for a good cube `S` of the second stopping time and `j ≠ k, k+1`,
`|S|^{-1} ‖f_j 𝟙_S‖_{p_j}^{p_j} ≤ 2^d (n+2) ε^{-1} |R|^{-1} ‖f_j 𝟙_R‖_{p_j}^{p_j}`. [PROVED] -/
theorem second_bound_2_32 {S : DyadicCube d} (hS : (D.second R hR hRs hFR).Good S) {j : Fin n}
    (hj : j ∈ D.J) :
    (volume S.toSet)⁻¹ *
        ∫⁻ x in S.toSet, ‖(TestFun.truncateₗ R (D.g j) : (Fin d → ℝ) → ℝ) x‖ₑ ^ D.p.p j ≤
      ENNReal.ofReal (2 ^ d * (n + 2) / D.ε) * ((volume R.toSet)⁻¹ *
        ∫⁻ x in R.toSet, ‖(TestFun.truncateₗ R (D.g j) : (Fin d → ℝ) → ℝ) x‖ₑ ^ D.p.p j) := by
  have hj' : j ∈ (D.second R hR hRs hFR).J := by
    change j ∈ (Finset.univ.erase D.b).erase D.a
    rw [Finset.erase_right_comm]
    exact hj
  have hja : j ≠ D.a := by
    rw [J, Finset.mem_erase, Finset.mem_erase] at hj
    exact hj.2.1
  have h := (D.second R hR hRs hFR).bound_2_8 D.hd hS hj'
  rwa [D.second_g_of_ne hR hRs hFR hja] at h

/-- **(2.33), first inequality**: `|S|^{-1} ‖𝔤_S‖_q^q ≤ 2^d (n+2) ε^{-1} |R|^{-1} ‖𝔤_R‖_q^q` on good
cubes of the second stopping time. [PROVED] -/
theorem second_bound_2_33 {S : DyadicCube d} (hS : (D.second R hR hRs hFR).Good S) :
    (volume S.toSet)⁻¹ *
        ∫⁻ x in S.toSet, ‖(TestFun.truncateₗ R D.pruned : (Fin d → ℝ) → ℝ) x‖ₑ ^ D.q ≤
      ENNReal.ofReal (2 ^ d * (n + 2) / D.ε) * ((volume R.toSet)⁻¹ *
        ∫⁻ x in R.toSet, ‖(TestFun.truncateₗ R D.pruned : (Fin d → ℝ) → ℝ) x‖ₑ ^ D.q) := by
  have h := (D.second R hR hRs hFR).bound_2_8_aux D.hd hS ((0 : Fin 2))
  rwa [D.second_aux hR hRs hFR (0 : Fin 2), ite_eq_left (show ((0 : Fin 2) : ℕ) = 0 from rfl)]
    at h

/-- **(2.34)**: `|S|^{-1} ‖v_S‖_r^r ≤ 2^d ε^{-1} |R|^{-1} ‖v‖_r^r` on good cubes of the second
stopping time. [PROVED] -/
theorem second_bound_2_34 {S : DyadicCube d} (hS : (D.second R hR hRs hFR).Good S) :
    (volume S.toSet)⁻¹ * ∫⁻ x in S.toSet, ‖(D.vP R : (Fin d → ℝ) → ℝ) x‖ₑ ^ D.r ≤
      ENNReal.ofReal (2 ^ d / D.ε) *
        ((volume R.toSet)⁻¹ * ∫⁻ x in R.toSet, ‖(D.vP R : (Fin d → ℝ) → ℝ) x‖ₑ ^ D.r) := by
  have h := (D.second R hR hRs hFR).bound_2_9 D.hd hS
  rwa [second_u] at h

/-- **(2.35), first inequality**: `|S|^{-1} ‖u_S‖_q^q ≤ 2^d (n+2) ε^{-1} |R|^{-1} ‖u_R‖_q^q` on good
cubes of the second stopping time. [PROVED] -/
theorem second_bound_2_35 {S : DyadicCube d} (hS : (D.second R hR hRs hFR).Good S) :
    (volume S.toSet)⁻¹ *
        ∫⁻ x in S.toSet, ‖(TestFun.truncateₗ R D.u : (Fin d → ℝ) → ℝ) x‖ₑ ^ D.q ≤
      ENNReal.ofReal (2 ^ d * (n + 2) / D.ε) * ((volume R.toSet)⁻¹ *
        ∫⁻ x in R.toSet, ‖(TestFun.truncateₗ R D.u : (Fin d → ℝ) → ℝ) x‖ₑ ^ D.q) := by
  have h := (D.second R hR hRs hFR).bound_2_8_aux D.hd hS ((1 : Fin 2))
  rwa [D.second_aux hR hRs hFR (1 : Fin 2),
    ite_eq_right (show ((1 : Fin 2) : ℕ) ≠ 0 from Nat.one_ne_zero)] at h

/-- **(2.36)**: for a good cube `S` of the second stopping time and a mean-zero `ϱ` supported on
`S`, `|Λ_S(v, ϱ)| ≤ 2^d B F_R ‖v‖_r ε^{-1} (|S|/|R|)^{1-1/q} ‖ϱ‖_q`. [PROVED] -/
theorem second_bound_2_36 {S : DyadicCube d} (hS : (D.second R hR hRs hFR).Good S)
    (ρ : TestFun d) (hρ : SupportedOn ρ S) (hρ0 : MeanZero (ρ : (Fin d → ℝ) → ℝ)) :
    |twoSlotForm D.T D.a D.b D.g S (D.vP R) ρ| ≤
      2 ^ d * (D.B * D.FP R * lpNorm (D.vP R : (Fin d → ℝ) → ℝ) D.r * D.ε⁻¹) *
        (S.vol / R.vol) ^ (1 - 1 / D.q) * lpNorm (ρ : (Fin d → ℝ) → ℝ) D.q := by
  have h : |slotForm D.T D.b (D.g2 R) S ρ| ≤
      2 ^ d * (D.B * (D.second R hR hRs hFR).F * lpNorm (D.g2 R D.a : (Fin d → ℝ) → ℝ) D.r *
        D.ε⁻¹) * (S.vol / R.vol) ^ (1 - 1 / D.q) * lpNorm (ρ : (Fin d → ℝ) → ℝ) D.q :=
    (D.second R hR hRs hFR).bound_2_10 D.hd hS ρ hρ hρ0
  rw [second_F, ← twoSlotForm_self D.T D.hab.symm, D.twoSlotForm_g2 (R := R) hS.1.1, D.g2_a] at h
  exact h

/-- **(2.37)**: for a good cube `S` of the second stopping time and a mean-zero `ϱ` supported on
`S`, `|Λ_S(ϱ, u)| ≤ 2^d K_R ε^{-1} (|S|/|R|)^{1-1/r} ‖ϱ‖_r`, where `K_R` is the constant of
(2.10) at `R`. [PROVED] -/
theorem second_bound_2_37 {S : DyadicCube d} (hS : (D.second R hR hRs hFR).Good S)
    (ρ : TestFun d) (hρ : SupportedOn ρ S) (hρ0 : MeanZero (ρ : (Fin d → ℝ) → ℝ)) :
    |slotForm D.T D.a D.g S ρ| ≤
      2 ^ d * (D.KR R * D.ε⁻¹) * (S.vol / R.vol) ^ (1 - 1 / D.r) *
        lpNorm (ρ : (Fin d → ℝ) → ℝ) D.r := by
  have h : |twoSlotForm D.T D.b D.a (D.g2 R) S (TestFun.truncateₗ R D.u) ρ| ≤
      2 ^ d * (D.KR R * D.ε⁻¹) * (S.vol / R.vol) ^ (1 - 1 / D.r) *
        lpNorm (ρ : (Fin d → ℝ) → ℝ) D.r :=
    (D.second R hR hRs hFR).bound_2_10_w D.hd hS ρ hρ hρ0
  rw [D.twoSlotForm_g2 (R := R) hS.1.1,
    show twoSlotForm D.T D.a D.b D.g S ρ (TestFun.truncateₗ R D.u) =
    twoSlotForm D.T D.a D.b D.g S ρ D.u by
      unfold twoSlotForm
      rw [TestFun.truncateₗ_truncateₗ_of_subset (R := R) hS.1.1], twoSlotForm_self D.T D.hab] at h
  exact h

end SecondBounds

/-- **The pruned function `𝔥`** of (2.38): the pruned function of the mirrored data,
`𝔥 = h_R − [h]_R v − ∑_{S ∈ 𝐒∖𝐒₄} h_S + ∑_{S ∈ 𝐒∖𝐒₄} ([h]_S/[v]_S) v_S − ∑_{S ∈ 𝐒∩𝐒₄} h_S
     + ∑_{S ∈ parents(𝐒)₄} ([h]_S/[v]_S) v_S − ∑_{S ∈ 𝐒₄'} ([h]_S/[v]_S) v_S`, `h = 𝟙_R`. -/
noncomputable def prunedH {R : DyadicCube d} (hR : R ∈ D.tree) (hRs : D.NotInStopping R)
    (hFR : 0 < D.FP R) : TestFun d := (D.second R hR hRs hFR).pruned

/-- `𝔥` is supported on `R` (p. 47). [PROVED] -/
theorem prunedH_supported {R : DyadicCube d} (hR : R ∈ D.tree) (hRs : D.NotInStopping R)
    (hFR : 0 < D.FP R) : SupportedOn (D.prunedH hR hRs hFR : (Fin d → ℝ) → ℝ) R :=
  (D.second R hR hRs hFR).pruned_supported

/-- `[𝔥]_R = 0` (p. 47). [PROVED] -/
theorem prunedH_meanZero {R : DyadicCube d} (hR : R ∈ D.tree) (hRs : D.NotInStopping R)
    (hFR : 0 < D.FP R) : MeanZero (D.prunedH hR hRs hFR : (Fin d → ℝ) → ℝ) :=
  (D.second R hR hRs hFR).pruned_meanZero

/-- The function `𝔤̂ = (𝔤 − [𝔤]_R [u]_R^{-1} u) 𝟙_R` of p. 46. -/
noncomputable def ghat (R : DyadicCube d) : TestFun d :=
  TestFun.truncateₗ R (D.pruned - (avg R D.pruned / avg R D.u) • D.u)

theorem ghat_supported (R : DyadicCube d) : SupportedOn (D.ghat R : (Fin d → ℝ) → ℝ) R :=
  TestFun.truncateₗ_supportedOn R _

/-- `𝔤̂` has mean zero on `R` when `[u]_R ≠ 0`, in particular when `R` lies in no first stopping
cube. [PROVED] -/
theorem ghat_meanZero {R : DyadicCube d} (hR : R ∈ D.tree) (hRs : D.NotInStopping R) :
    MeanZero (D.ghat R : (Fin d → ℝ) → ℝ) := by
  have hu : avg R D.u ≠ 0 := D.avg_u_ne_zero hR (D.not_in_P4_of_notInStopping hRs)
  change TestFun.integralₗ (D.ghat R) = 0
  unfold ghat
  rw [TestFun.integralₗ_truncateₗ, avg_mul_vol, Submodule.coe_sub, Submodule.coe_smul]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [integral_sub (TestFun.integrable D.pruned.2).integrableOn
    ((TestFun.integrable D.u.2).integrableOn.const_mul _), integral_const_mul, ← avg_mul_vol,
    ← avg_mul_vol]
  have : avg R D.pruned / avg R D.u * (avg R D.u * R.vol) = avg R D.pruned * R.vol := by
    rw [div_mul_eq_mul_div, mul_comm (avg R D.u) R.vol, ← mul_assoc, mul_div_assoc, div_self hu,
      mul_one]
  rw [this, sub_self]

/-! ### §2.5 The best constant `A'` of (2.23) and the estimate (2.39) (p. 45–51)

The unit of the estimates (2.23), (2.39), (2.40) is `E_R = F |R||Q|^{-1} ‖g‖_q ‖h‖_r` with
`‖h‖_r = |Q|^{1/r}` (`h = 𝟙_Q` is the function of (2.2)), i.e. `E_R = F ‖g‖_q |R| |Q|^{1/r-1}`. The
constant `A'` is the best constant in `|Λ_R(h, 𝔤 − [𝔤]_R[u]_R^{-1}u)| ≤ A' E_R` over the cubes `R`
of the tree which lie in no first stopping cube (for the other cubes the function
`𝔤 − [𝔤]_R[u]_R^{-1}u` vanishes on `R`, p. 46); it is finite since the tree is finite. -/

/-- `E_R = F ‖g‖_q |R| |Q|^{1/r-1}`. -/
noncomputable def E (R : DyadicCube d) : ℝ :=
  D.F * lpNorm (D.G : (Fin d → ℝ) → ℝ) D.q * R.vol * D.Q.vol ^ (1 / D.r - 1)

theorem E_pos (R : DyadicCube d) : 0 < D.E R := by
  have hF := D.Fpos'
  have hG : 0 < lpNorm (D.G : (Fin d → ℝ) → ℝ) D.q := D.Gpos
  have hR := R.vol_pos
  have hV := D.Q.vol_pos
  unfold E
  positivity

/-- The tree `𝒟_N(Q)` as a finite set. -/
noncomputable def treeFinset : Finset (DyadicCube d) := D.tree_finite.toFinset

theorem mem_treeFinset {R : DyadicCube d} : R ∈ D.treeFinset ↔ R ∈ D.tree :=
  Set.Finite.mem_toFinset _

open Classical in
/-- The admissible cubes of (2.23): the cubes of the tree in no first stopping cube. -/
noncomputable def adm : Finset (DyadicCube d) := D.treeFinset.filter fun R => D.NotInStopping R

/-- The ratio `|Λ_R(h, ψ_R)| / E_R` of (2.23). -/
noncomputable def ratio (R : DyadicCube d) : ℝ :=
  |D.form2 R (TestFun.ind R) (D.psi R)| / D.E R

/-- **The best constant `A'` of (2.23)**: the maximum of the ratios over the admissible cubes
(and `0`). -/
noncomputable def A' : ℝ :=
  (insert 0 (D.adm.image D.ratio)).sup' (Finset.insert_nonempty _ _) id

theorem A'_nonneg : 0 ≤ D.A' :=
  Finset.le_sup' (f := id) (Finset.mem_insert_self (0 : ℝ) _)

/-- **(2.23)**: for a cube `R` of the tree in no first stopping cube,
`|Λ_R(h, 𝔤 − [𝔤]_R[u]_R^{-1}u)| ≤ A' E_R`. [PROVED] -/
theorem estimate_2_23 {R : DyadicCube d} (hR : R ∈ D.tree) (hRs : D.NotInStopping R) :
    |D.form2 R (TestFun.ind R) (D.psi R)| ≤ D.A' * D.E R := by
  classical
  have hE := D.E_pos R
  have hmem : D.ratio R ∈ insert 0 (D.adm.image D.ratio) :=
    Finset.mem_insert_of_mem (Finset.mem_image_of_mem _
      (Finset.mem_filter.mpr ⟨D.mem_treeFinset.mpr hR, hRs⟩))
  have h : D.ratio R ≤ D.A' := Finset.le_sup' (f := id) hmem
  unfold ratio at h
  rwa [div_le_iff₀ hE] at h

/-- `A'` is the least constant in (2.23): `A' ≤ c` whenever `c ≥ 0` and (2.23) holds with `c`.
[PROVED] -/
theorem A'_le {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ R ∈ D.tree, D.NotInStopping R →
      |D.form2 R (TestFun.ind R) (D.psi R)| ≤ c * D.E R) : D.A' ≤ c := by
  classical
  refine Finset.sup'_le _ _ fun x hx => ?_
  rw [Finset.mem_insert, Finset.mem_image] at hx
  rcases hx with rfl | ⟨R, hR, rfl⟩
  · exact hc
  · have hR' := Finset.mem_filter.mp hR
    change D.ratio R ≤ c
    unfold ratio
    rw [div_le_iff₀ (D.E_pos R)]
    exact h R (D.mem_treeFinset.mp hR'.1) hR'.2

/-- `∫_S 𝟙_R = |S|` for `S ⊆ R`. [PROVED] -/
theorem TestFun.setIntegral_ind_of_subset {S R : DyadicCube d} (h : S.toSet ⊆ R.toSet) :
    ∫ x in S.toSet, ((TestFun.ind R : TestFun d) : (Fin d → ℝ) → ℝ) x = S.vol := by
  rw [TestFun.coe_ind, setIntegral_congr_fun S.measurableSet_toSet
    (f := fun x => R.toSet.indicator (1 : (Fin d → ℝ) → ℝ) x) (g := fun _ => (1 : ℝ))
    (fun x hx => by simp [Set.indicator_of_mem (h hx)]), setIntegral_const, measureReal_def,
    S.volume_toSet, ENNReal.toReal_ofReal S.vol_pos.le, smul_eq_mul, mul_one]

/-- `[h]_S = 1` for `S ⊆ R`, `h = 𝟙_R`. [PROVED] -/
theorem avg_ind_of_subset {S R : DyadicCube d} (h : S.toSet ⊆ R.toSet) :
    avg S (TestFun.ind R) = 1 := by
  rw [avg, TestFun.setIntegral_ind_of_subset h, div_self S.vol_pos.ne']

section Expansion241

variable {R : DyadicCube d} (hR : R ∈ D.tree) (hRs : D.NotInStopping R) (hFR : 0 < D.FP R)

/-- The coefficients `[h]_S/[v]_S = 1/[v]_S` of the second pruning. [PROVED] -/
theorem second_coef {S : DyadicCube d} (hS : S.toSet ⊆ R.toSet) :
    (D.second R hR hRs hFR).coef S = 1 / avg S (D.vP R) := by
  change avg S (TestFun.ind R) / avg S ((D.second R hR hRs hFR).u) = _
  rw [second_u, avg_ind_of_subset hS]

open Classical in
/-- **The expansion (2.41)–(2.43)** of `h_R − 𝔥`, with `v = b_{τ,𝐐_R,k}`, `b_S = b_{τ,𝐐_S,k}`,
`[h]_S = 1` and `[h]_S/[v]_S = 1/[v]_S`:
`h_R − 𝔥 = v + ∑_{S ∈ 𝐒} (h_S − b_S) + ∑_{S ∈ 𝐒∖𝐒₄} (b_S − [v]_S^{-1} v_S) + ∑_{S ∈ 𝐒∩𝐒₄} b_S
          − ∑_{S ∈ parents(𝐒)₄} [v]_S^{-1} v_S + ∑_{S ∈ 𝐒₄'} [v]_S^{-1} v_S`. [PROVED] -/
theorem sub_prunedH_eq :
    TestFun.ind R - D.prunedH hR hRs hFR =
      D.vP R
      + ∑ S ∈ (D.second R hR hRs hFR).Pst, (TestFun.ind S - D.vP S)
      + ∑ S ∈ (D.second R hR hRs hFR).PstOut4,
          (D.vP S - (1 / avg S (D.vP R)) • TestFun.truncateₗ S (D.vP R))
      + ∑ S ∈ (D.second R hR hRs hFR).PstIn4, D.vP S
      - ∑ S ∈ (D.second R hR hRs hFR).Pbar4, (1 / avg S (D.vP R)) • TestFun.truncateₗ S (D.vP R)
      + ∑ S ∈ (D.second R hR hRs hFR).Psib4, (1 / avg S (D.vP R)) • TestFun.truncateₗ S (D.vP R) :=
        by
  set D' := D.second R hR hRs hFR with hD'
  have h := D'.sub_pruned_eq
  have hu : D'.u = D.vP R := second_u _ _ _ _
  have hG : D'.G = TestFun.ind R := rfl
  have hbP : D'.bP = D.vP := rfl
  have hQ : D'.Q = R := rfl
  rw [hu, hG, hQ, avg_ind_of_subset (subset_refl _), one_smul] at h
  have e1 : ∑ P ∈ D'.Pst, (TestFun.truncateₗ P (TestFun.ind R) - avg P (TestFun.ind R) • D'.bP P)
      = ∑ S ∈ D'.Pst, (TestFun.ind S - D.vP S) :=
    Finset.sum_congr rfl fun S hS => by
      have hSR : S.toSet ⊆ R.toSet := D'.Pst_subset_Q hS
      rw [hbP, TestFun.truncateₗ_ind_of_subset hSR, avg_ind_of_subset hSR, one_smul]
  have e2 : ∑ P ∈ D'.PstOut4,
      (avg P (TestFun.ind R) • D'.bP P - D'.coef P • TestFun.truncateₗ P (D.vP R)) =
      ∑ S ∈ D'.PstOut4, (D.vP S - (1 / avg S (D.vP R)) • TestFun.truncateₗ S (D.vP R)) :=
    Finset.sum_congr rfl fun S hS => by
      have hSR : S.toSet ⊆ R.toSet := D'.Pst_subset_Q (Finset.mem_of_mem_filter S hS)
      rw [hbP, avg_ind_of_subset hSR, one_smul, D.second_coef hR hRs hFR hSR]
  have e3 : ∑ P ∈ D'.PstIn4, avg P (TestFun.ind R) • D'.bP P = ∑ S ∈ D'.PstIn4, D.vP S :=
    Finset.sum_congr rfl fun S hS => by
      have hSR : S.toSet ⊆ R.toSet := D'.Pst_subset_Q (Finset.mem_of_mem_filter S hS)
      rw [hbP, avg_ind_of_subset hSR, one_smul]
  have e4 : ∑ P ∈ D'.Pbar4, D'.coef P • TestFun.truncateₗ P (D.vP R) =
      ∑ S ∈ D'.Pbar4, (1 / avg S (D.vP R)) • TestFun.truncateₗ S (D.vP R) :=
    Finset.sum_congr rfl fun S hS => by
      rw [D.second_coef hR hRs hFR (D'.Pbar4_subset_Q hS)]
  have e5 : ∑ P ∈ D'.Psib4, D'.coef P • TestFun.truncateₗ P (D.vP R) =
      ∑ S ∈ D'.Psib4, (1 / avg S (D.vP R)) • TestFun.truncateₗ S (D.vP R) :=
    Finset.sum_congr rfl fun S hS => by
      rw [D.second_coef hR hRs hFR (D'.Psib4_subset_Q hS)]
  change TestFun.ind R - D'.pruned = _
  rw [h, e1, e2, e3, e4, e5]

/-- The constant of the first term of (2.41): `C_α = B^{1+1/r} C_G^{1-1/r-1/q} C_ψ`. -/
noncomputable def Cα : ℝ := D.B ^ (1 + 1 / D.r) * D.CG ^ (1 - 1 / D.r - 1 / D.q) * D.psiConst

include hR hRs in
/-- **The first term of (2.41)** (p. 48): by the testing condition (1.9) for `τ`, `𝐐_R`, the bound
`F_R ≤ (C_G |R|/|Q|)^{1-1/r-1/q} F` from (2.8), the local bound `‖𝔤̂‖_q ≤ C_ψ (|R|/|Q|)^{1/q} ‖g‖_q`
and `‖v‖_r ≤ (B|R|)^{1/r}`, `|Λ_R([h]_R v, 𝔤̂)| ≤ C_α E_R`. [PROVED] -/
theorem abs_form2_v_ghat_le (hG : D.GBound) :
    |twoSlotForm D.T D.a D.b D.g R (D.vP R) (D.ghat R)| ≤ D.Cα * D.E R := by
  have hr0 : 0 < D.r := by linarith [D.hr]
  have hq0 : 0 < D.q := by linarith [D.hq]
  have hB0 : 0 ≤ D.B := by linarith [D.hB]
  have hV := D.Q.vol_pos
  have hRv := R.vol_pos
  have hCG := D.CG_pos
  have hF0 := D.Fpos'.le
  have hN0 : 0 ≤ lpNorm (D.G : (Fin d → ℝ) → ℝ) D.q := lpNorm_nonneg _ _
  have hψ0 := D.psiConst_nonneg
  have hgood : D.Good R := D.good_of_notInStopping hR hRs
  have ht := D.testing_vP R hR.1 (D.ghat R) (D.ghat_supported R)
  have hFP := D.FP_le hgood
  have hv := D.lpNorm_vP_le hR.1
  have hψ : lpNorm (D.ghat R : (Fin d → ℝ) → ℝ) D.q ≤
      D.psiConst * (R.vol / D.Q.vol) ^ (1 / D.q) * lpNorm (D.G : (Fin d → ℝ) → ℝ) D.q :=
    D.lpNorm_truncateₗ_psi_le hG hR hRs
  set x : ℝ := R.vol / D.Q.vol with hx
  have hx0 : 0 < x := by positivity
  have hFP0 := D.FP_nonneg R
  have hv0 : 0 ≤ lpNorm (D.vP R : (Fin d → ℝ) → ℝ) D.r := lpNorm_nonneg _ _
  have hg0 : 0 ≤ lpNorm (D.ghat R : (Fin d → ℝ) → ℝ) D.q := lpNorm_nonneg _ _
  -- the exponent bookkeeping: `x^{1-1/r-1/q} x^{1/q} |R|^{1/r} = |R| |Q|^{1/r-1}`
  have hexp : x ^ (1 - 1 / D.r - 1 / D.q) * x ^ (1 / D.q) * R.vol ^ (1 / D.r) =
      R.vol * D.Q.vol ^ (1 / D.r - 1) := by
    rw [← Real.rpow_add hx0, show 1 - 1 / D.r - 1 / D.q + 1 / D.q = 1 - 1 / D.r by ring, hx,
      Real.div_rpow hRv.le hV.le, div_eq_mul_inv, ← Real.rpow_neg hV.le, mul_right_comm,
      ← Real.rpow_add hRv, sub_add_cancel, Real.rpow_one, neg_sub]
  calc |twoSlotForm D.T D.a D.b D.g R (D.vP R) (D.ghat R)|
      ≤ D.B * D.FP R * lpNorm (D.vP R : (Fin d → ℝ) → ℝ) D.r *
          lpNorm (D.ghat R : (Fin d → ℝ) → ℝ) D.q := ht
    _ ≤ D.B * ((D.CG * x) ^ (1 - 1 / D.r - 1 / D.q) * D.F) * (D.B * R.vol) ^ (1 / D.r) *
          (D.psiConst * x ^ (1 / D.q) * lpNorm (D.G : (Fin d → ℝ) → ℝ) D.q) := by gcongr
    _ = D.Cα * (D.F * lpNorm (D.G : (Fin d → ℝ) → ℝ) D.q *
          (x ^ (1 - 1 / D.r - 1 / D.q) * x ^ (1 / D.q) * R.vol ^ (1 / D.r))) := by
        unfold Cα
        rw [Real.mul_rpow hCG.le hx0.le, Real.mul_rpow hB0 hRv.le, Real.rpow_add' hB0 (by
          positivity),
          Real.rpow_one]
        ring
    _ = D.Cα * D.E R := by
        rw [hexp]
        unfold E
        ring

end Expansion241

/-! #### The sum (2.44) over the second stopping cubes: the part `∑''` (p. 48–49)

`Λ_R(∑_{S ∈ 𝐒} (h_S − b_S), 𝔤̂) = ∑_{S ∈ 𝐒} Λ_S(h_S − b_S, 𝔤̂)` by the smoothness condition. The sum
splits into `∑'` over the cubes contained in a first stopping cube and `∑''` over the others. For
the latter, `𝔤̂ = ψ_S + (c_S − c_R) u` on `S` with `c_S = [𝔤]_S/[u]_S`, which gives the three
terms (2.47)–(2.49): the `A'`-term `∑'' |Λ_S(h, ψ_S)| ≤ (1−ε) A' E_R` by (2.23) and (2.31), the
testing term `∑'' |Λ_S(b_S, ψ_S)|` by (1.9) for `τ`, `𝐐_S` and the local bounds, and the term
`∑'' |c_S − c_R| |Λ_S(h_S − b_S, u)|` by (2.10) and the bounds on `|[𝔤]_S|`, `|[𝔤]_R|`. -/

/-- Smoothness in the slot `k`: `Λ_Q(ρ, ρ') = Λ_P(ρ, ρ')` for `ρ` supported on `P ⊆ Q` with mean
zero. [PROVED] -/
theorem twoSlotForm_eq_of_subset_left (T : PerfectCZForm d n) {a b : Fin n} (hab : a ≠ b)
    (g : Fin n → TestFun d) {P Q : DyadicCube d} (hPQ : P.toSet ⊆ Q.toSet) {ρ : TestFun d}
    (hρ : SupportedOn ρ P) (hρ0 : MeanZero (ρ : (Fin d → ℝ) → ℝ)) (ρ' : TestFun d) :
    twoSlotForm T a b g P ρ ρ' = twoSlotForm T a b g Q ρ ρ' := by
  rw [twoSlotForm_eq_slotForm T hab, twoSlotForm_eq_slotForm T hab]
  exact slotForm_eq_of_subset T a _ hPQ hρ hρ0

theorem twoSlotForm_sum_left {ι : Type*} (T : PerfectCZForm d n) {a b : Fin n} (hab : a ≠ b)
    (g : Fin n → TestFun d) (P : DyadicCube d) (s : Finset ι) (f : ι → TestFun d)
    (ρ' : TestFun d) :
    twoSlotForm T a b g P (∑ i ∈ s, f i) ρ' = ∑ i ∈ s, twoSlotForm T a b g P (f i) ρ' := by
  simp only [twoSlotForm_eq_slotForm T hab, map_sum]

theorem twoSlotForm_smul_left (T : PerfectCZForm d n) {a b : Fin n} (hab : a ≠ b)
    (g : Fin n → TestFun d) (P : DyadicCube d) (c : ℝ) (ρ ρ' : TestFun d) :
    twoSlotForm T a b g P (c • ρ) ρ' = c * twoSlotForm T a b g P ρ ρ' := by
  simp only [twoSlotForm_eq_slotForm T hab, map_smul, smul_eq_mul]

/-- The coefficient `c_S = [𝔤]_S / [u]_S`. -/
noncomputable def cS (S : DyadicCube d) : ℝ := avg S D.pruned / avg S D.u

theorem psi_eq (S : DyadicCube d) : D.psi S = D.pruned - D.cS S • D.u := rfl

theorem ghat_eq (R : DyadicCube d) : D.ghat R = TestFun.truncateₗ R (D.psi R) := rfl

/-- `|[𝔤]_S| ≤ C_loc |Q|^{-1/q} ‖g‖_q` on good cubes ((2.45), (2.46) for `𝔤`). [PROVED] -/
theorem abs_avg_pruned_le (hG : D.GBound) {S : DyadicCube d} (hS : D.Good S) :
    |avg S D.pruned| ≤ D.locConst * D.Q.vol ^ (-(1 / D.q)) * lpNorm (D.G : (Fin d → ℝ) → ℝ) D.q :=
      by
  have hq0 : 0 < D.q := by linarith [D.hq]
  have hV := D.Q.vol_pos
  have hS0 := S.vol_pos
  have h1 := abs_avg_mul_rpow_le S D.pruned D.hq.le
  have h2 := D.lpNorm_truncateₗ_pruned_le hG hS
  have hdiv : (S.vol / D.Q.vol) ^ (1 / D.q) = S.vol ^ (1 / D.q) * D.Q.vol ^ (-(1 / D.q)) := by
    rw [Real.div_rpow hS0.le hV.le, Real.rpow_neg hV.le, div_eq_mul_inv]
  rw [hdiv] at h2
  have hpos : 0 < S.vol ^ (1 / D.q) := Real.rpow_pos_of_pos hS0 _
  have h3 : |avg S D.pruned| * S.vol ^ (1 / D.q) ≤
      (D.locConst * D.Q.vol ^ (-(1 / D.q)) * lpNorm (D.G : (Fin d → ℝ) → ℝ) D.q) *
        S.vol ^ (1 / D.q) := by
    refine (h1.trans h2).trans (le_of_eq ?_)
    ring
  exact le_of_mul_le_mul_right h3 hpos

/-- `|c_S| ≤ 8 C_loc |Q|^{-1/q} ‖g‖_q` for `S` in no first stopping cube. [PROVED] -/
theorem abs_cS_le (hG : D.GBound) {S : DyadicCube d} (hS : S ∈ D.tree) (hSs : D.NotInStopping S) :
    |D.cS S| ≤ 8 * (D.locConst * D.Q.vol ^ (-(1 / D.q)) * lpNorm (D.G : (Fin d → ℝ) → ℝ) D.q) :=
  (D.abs_div_avg_u_le (D.bound_2_11 D.hd hS (D.not_in_P4_of_notInStopping hSs)) _).trans
    (mul_le_mul_of_nonneg_left (D.abs_avg_pruned_le hG (D.good_of_notInStopping hS hSs))
      (by norm_num))

/-- `h_S − b_S` is supported on `S` and has mean zero. [PROVED] -/
theorem ind_sub_vP_supported {S : DyadicCube d} (hS : S.toSet ⊆ D.Q.toSet) :
    SupportedOn ((TestFun.ind S - D.vP S : TestFun d) : (Fin d → ℝ) → ℝ) S := fun x hx => by
  rw [Submodule.coe_sub, Pi.sub_apply, TestFun.coe_ind, Set.indicator_of_notMem hx,
    D.vP_supp S hS x hx, sub_zero]

theorem ind_sub_vP_meanZero {S : DyadicCube d} (hS : S.toSet ⊆ D.Q.toSet) :
    MeanZero ((TestFun.ind S - D.vP S : TestFun d) : (Fin d → ℝ) → ℝ) := by
  change TestFun.integralₗ (TestFun.ind S - D.vP S) = 0
  rw [map_sub, TestFun.integralₗ_apply, TestFun.integralₗ_apply, TestFun.integral_ind,
    D.vP_mean S hS, sub_self]

/-- `‖h_S − b_S‖_r ≤ 2 B^{1/r} |S|^{1/r}`. [PROVED] -/
theorem lpNorm_ind_sub_vP_le {S : DyadicCube d} (hS : S.toSet ⊆ D.Q.toSet) :
    lpNorm ((TestFun.ind S - D.vP S : TestFun d) : (Fin d → ℝ) → ℝ) D.r ≤
      2 * D.B ^ (1 / D.r) * S.vol ^ (1 / D.r) := by
  have hr1 : 1 ≤ D.r := D.hr.le
  have hr0 : 0 < D.r := by linarith
  have hB1 := D.hB
  have hB0 : 0 ≤ D.B := by linarith
  have hv := S.vol_pos
  have h1 : S.vol ^ (1 / D.r) ≤ (D.B * S.vol) ^ (1 / D.r) :=
    Real.rpow_le_rpow hv.le (le_mul_of_one_le_left hv.le hB1) (by positivity)
  calc lpNorm ((TestFun.ind S - D.vP S : TestFun d) : (Fin d → ℝ) → ℝ) D.r
      ≤ lpNorm ((TestFun.ind S : TestFun d) : (Fin d → ℝ) → ℝ) D.r +
          lpNorm (D.vP S : (Fin d → ℝ) → ℝ) D.r := TestFun.lpNorm_sub_le _ _ hr1
    _ ≤ (D.B * S.vol) ^ (1 / D.r) + (D.B * S.vol) ^ (1 / D.r) := by
        rw [TestFun.lpNorm_ind S hr0]
        exact add_le_add h1 (D.lpNorm_vP_le hS)
    _ = 2 * D.B ^ (1 / D.r) * S.vol ^ (1 / D.r) := by
        rw [Real.mul_rpow hB0 hv.le]
        ring

/-- `∑_{S ∈ 𝐒} E_S ≤ (1 − ε) E_R` by (2.31). [PROVED] -/
theorem sum_E_second_le {R : DyadicCube d} (hR : R ∈ D.tree) (hRs : D.NotInStopping R)
    (hFR : 0 < D.FP R) :
    ∑ S ∈ (D.second R hR hRs hFR).Pst, D.E S ≤ (1 - D.ε) * D.E R := by
  have h := (D.second R hR hRs hFR).sum_Pst_vol_le
  have hε : (D.second R hR hRs hFR).ε = D.ε := rfl
  have hQ : (D.second R hR hRs hFR).Q = R := rfl
  rw [hε, hQ] at h
  have hF := D.Fpos'.le
  have hN : 0 ≤ lpNorm (D.G : (Fin d → ℝ) → ℝ) D.q := lpNorm_nonneg _ _
  have hV : 0 ≤ D.Q.vol ^ (1 / D.r - 1) := Real.rpow_nonneg D.Q.vol_pos.le _
  unfold E
  calc ∑ S ∈ (D.second R hR hRs hFR).Pst,
        D.F * lpNorm (D.G : (Fin d → ℝ) → ℝ) D.q * S.vol * D.Q.vol ^ (1 / D.r - 1)
      = (D.F * lpNorm (D.G : (Fin d → ℝ) → ℝ) D.q * D.Q.vol ^ (1 / D.r - 1)) *
          ∑ S ∈ (D.second R hR hRs hFR).Pst, S.vol := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun S _ => by ring
    _ ≤ (D.F * lpNorm (D.G : (Fin d → ℝ) → ℝ) D.q * D.Q.vol ^ (1 / D.r - 1)) *
          ((1 - D.ε) * R.vol) := mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by ring

section Sum244

variable {R : DyadicCube d} (hR : R ∈ D.tree) (hRs : D.NotInStopping R) (hFR : 0 < D.FP R)

open Classical in
/-- `∑''`: the cubes of `𝐒` not contained in a first stopping cube. -/
noncomputable def Sout : Finset (DyadicCube d) :=
  (D.second R hR hRs hFR).Pst.filter fun S => D.NotInStopping S

open Classical in
/-- `∑'`: the cubes of `𝐒` contained in a first stopping cube. -/
noncomputable def Sin : Finset (DyadicCube d) :=
  (D.second R hR hRs hFR).Pst.filter fun S => ¬ D.NotInStopping S

theorem sum_Pst_eq_Sout_add_Sin (f : DyadicCube d → ℝ) :
    ∑ S ∈ (D.second R hR hRs hFR).Pst, f S =
      ∑ S ∈ D.Sout hR hRs hFR, f S + ∑ S ∈ D.Sin hR hRs hFR, f S := by
  unfold Sout Sin
  rw [Finset.sum_filter_add_sum_filter_not]

open Classical in
theorem Sout_mem_tree {S : DyadicCube d} (hS : S ∈ D.Sout hR hRs hFR) : S ∈ D.tree :=
  D.second_tree_subset hR hRs hFR
    ((D.second R hR hRs hFR).stoppingCubes_subset_tree'
      ((D.second R hR hRs hFR).mem_Pst.mp (Finset.mem_of_mem_filter S hS)))

open Classical in
theorem Sout_notInStopping {S : DyadicCube d} (hS : S ∈ D.Sout hR hRs hFR) :
    D.NotInStopping S := (Finset.mem_filter.mp hS).2

open Classical in
theorem Sout_subset_R {S : DyadicCube d} (hS : S ∈ D.Sout hR hRs hFR) : S.toSet ⊆ R.toSet :=
  (D.second R hR hRs hFR).Pst_subset_Q (Finset.mem_of_mem_filter S hS)

/-- **(2.44)**: `Λ_R(∑_{S ∈ 𝐒} (h_S − b_S), 𝔤̂) = ∑_{S ∈ 𝐒} Λ_S(h_S − b_S, 𝔤̂)`. [PROVED] -/
theorem form2_sum_ind_sub_vP_eq :
    twoSlotForm D.T D.a D.b D.g R (∑ S ∈ (D.second R hR hRs hFR).Pst, (TestFun.ind S - D.vP S))
        (D.ghat R) =
      ∑ S ∈ (D.second R hR hRs hFR).Pst,
        twoSlotForm D.T D.a D.b D.g S (TestFun.ind S - D.vP S) (D.ghat R) := by
  rw [twoSlotForm_sum_left D.T D.hab]
  refine Finset.sum_congr rfl fun S hS => ?_
  have hSR : S.toSet ⊆ R.toSet := (D.second R hR hRs hFR).Pst_subset_Q hS
  exact (twoSlotForm_eq_of_subset_left D.T D.hab D.g hSR (D.ind_sub_vP_supported (hSR.trans hR.1))
    (D.ind_sub_vP_meanZero (hSR.trans hR.1)) _).symm

/-- On `S ⊆ R`, `𝔤̂ = ψ_S + (c_S − c_R) u` (p. 49). [PROVED] -/
theorem truncateₗ_ghat_eq {S : DyadicCube d} (hSR : S.toSet ⊆ R.toSet) :
    TestFun.truncateₗ S (D.ghat R) =
      TestFun.truncateₗ S (D.psi S) + (D.cS S - D.cS R) • TestFun.truncateₗ S D.u := by
  rw [ghat_eq, TestFun.truncateₗ_truncateₗ_of_subset hSR, psi_eq, psi_eq, map_sub, map_sub,
    map_smul, map_smul]
  module

/-- **(2.47)–(2.49)**: for `S ∈ ∑''`,
`Λ_S(h_S − b_S, 𝔤̂) = Λ_S(h_S, ψ_S) − Λ_S(b_S, ψ_S) + (c_S − c_R) Λ_S(h_S − b_S, u)`. [PROVED] -/
theorem form2_ind_sub_vP_ghat_eq {S : DyadicCube d} (hSR : S.toSet ⊆ R.toSet) :
    twoSlotForm D.T D.a D.b D.g S (TestFun.ind S - D.vP S) (D.ghat R) =
      D.form2 S (TestFun.ind S) (D.psi S) - D.form2 S (D.vP S) (D.psi S) +
        (D.cS S - D.cS R) * slotForm D.T D.a D.g S (TestFun.ind S - D.vP S) := by
  rw [← twoSlotForm_truncateₗ_right, D.truncateₗ_ghat_eq hSR, twoSlotForm_add_right,
    twoSlotForm_truncateₗ_right, twoSlotForm_smul_right, twoSlotForm_truncateₗ_right,
    twoSlotForm_sub_left D.T D.hab, twoSlotForm_self D.T D.hab]
  rfl

/-- The constant of (2.49): `C₄₉ = 32 · 2^d C_loc B^{1+1/q+1/r} / ε`. -/
noncomputable def C₄₉ : ℝ := 32 * 2 ^ d * D.locConst * D.B ^ (1 + 1 / D.q + 1 / D.r) / D.ε

theorem C₄₉_nonneg : 0 ≤ D.C₄₉ := by
  have := D.locConst_nonneg
  have := D.ε_pos
  have : 0 ≤ D.B := by linarith [D.hB]
  unfold C₄₉
  positivity

include hR hRs in
/-- **(2.49)** for one cube: `|c_S − c_R| |Λ_S(h_S − b_S, u)| ≤ C₄₉ E_S` for `S ⊆ R` in no first
stopping cube, by (2.10), `‖h_S − b_S‖_r ≤ 2B^{1/r}|S|^{1/r}`, (1.7) for `u` and the bounds on
`|c_S|`, `|c_R|`. [PROVED] -/
theorem abs_term_2_49_le (hG : D.GBound) {S : DyadicCube d} (hS : S ∈ D.tree)
    (hSs : D.NotInStopping S) :
    |(D.cS S - D.cS R) * slotForm D.T D.a D.g S (TestFun.ind S - D.vP S)| ≤ D.C₄₉ * D.E S := by
  have hr0 : 0 < D.r := by linarith [D.hr]
  have hq0 : 0 < D.q := by linarith [D.hq]
  have hB0 : 0 ≤ D.B := by linarith [D.hB]
  have hε := D.ε_pos
  have hV := D.Q.vol_pos
  have hSv := S.vol_pos
  have hF0 := D.Fpos'.le
  have hL0 := D.locConst_nonneg
  have hN0 : 0 ≤ lpNorm (D.G : (Fin d → ℝ) → ℝ) D.q := lpNorm_nonneg _ _
  have hu0 : 0 ≤ lpNorm (D.u : (Fin d → ℝ) → ℝ) D.q := lpNorm_nonneg _ _
  have hgood : D.Good S := D.good_of_notInStopping hS hSs
  set K := D.locConst * D.Q.vol ^ (-(1 / D.q)) * lpNorm (D.G : (Fin d → ℝ) → ℝ) D.q with hK
  have hK0 : 0 ≤ K := by positivity
  have hc : |D.cS S - D.cS R| ≤ 16 * K := by
    calc |D.cS S - D.cS R| ≤ |D.cS S| + |D.cS R| := abs_sub _ _
      _ ≤ 8 * K + 8 * K := add_le_add (D.abs_cS_le hG hS hSs) (D.abs_cS_le hG hR hRs)
      _ = 16 * K := by ring
  have h10 := D.bound_2_10 D.hd hgood (TestFun.ind S - D.vP S) (D.ind_sub_vP_supported hS.1)
    (D.ind_sub_vP_meanZero hS.1)
  have hρ := D.lpNorm_ind_sub_vP_le hS.1
  have hu := D.lpNorm_u_le
  have hρ0 : 0 ≤ lpNorm ((TestFun.ind S - D.vP S : TestFun d) : (Fin d → ℝ) → ℝ) D.r :=
    lpNorm_nonneg _ _
  have hX0 : 0 ≤ (S.vol / D.Q.vol) ^ (1 - 1 / D.r) := Real.rpow_nonneg (by positivity) _
  have hexp : D.Q.vol ^ (-(1 / D.q)) * D.Q.vol ^ (1 / D.q) * (S.vol / D.Q.vol) ^ (1 - 1 / D.r) *
      S.vol ^ (1 / D.r) = S.vol * D.Q.vol ^ (1 / D.r - 1) := by
    rw [← Real.rpow_add hV, neg_add_cancel, Real.rpow_zero, one_mul, Real.div_rpow hSv.le hV.le,
      div_eq_mul_inv, ← Real.rpow_neg hV.le, mul_right_comm, ← Real.rpow_add hSv, sub_add_cancel,
      Real.rpow_one, neg_sub]
  rw [abs_mul]
  calc |D.cS S - D.cS R| * |slotForm D.T D.a D.g S (TestFun.ind S - D.vP S)|
      ≤ (16 * K) * (2 ^ d * (D.B * D.F * lpNorm (D.u : (Fin d → ℝ) → ℝ) D.q * D.ε⁻¹) *
          (S.vol / D.Q.vol) ^ (1 - 1 / D.r) *
          lpNorm ((TestFun.ind S - D.vP S : TestFun d) : (Fin d → ℝ) → ℝ) D.r) :=
        mul_le_mul hc h10 (abs_nonneg _) (by positivity)
    _ ≤ (16 * K) * (2 ^ d * (D.B * D.F * (D.B * D.Q.vol) ^ (1 / D.q) * D.ε⁻¹) *
          (S.vol / D.Q.vol) ^ (1 - 1 / D.r) * (2 * D.B ^ (1 / D.r) * S.vol ^ (1 / D.r))) := by
        gcongr
    _ = D.C₄₉ * (D.F * lpNorm (D.G : (Fin d → ℝ) → ℝ) D.q *
          (D.Q.vol ^ (-(1 / D.q)) * D.Q.vol ^ (1 / D.q) * (S.vol / D.Q.vol) ^ (1 - 1 / D.r) *
            S.vol ^ (1 / D.r))) := by
        unfold C₄₉
        rw [hK, Real.mul_rpow hB0 hV.le, Real.rpow_add' hB0 (by positivity),
          Real.rpow_add' hB0 (by positivity), Real.rpow_one]
        ring
    _ = D.C₄₉ * D.E S := by
        rw [hexp]
        unfold E
        ring

/-- **The part `∑''` of (2.44)** (p. 49): with the constants of (2.47)–(2.49),
`|∑''_{S} Λ_S(h_S − b_S, 𝔤̂)| ≤ ((1−ε) A' + C_α + C₄₉) E_R`. [PROVED] -/
theorem abs_sum_Sout_le (hG : D.GBound) :
    |∑ S ∈ D.Sout hR hRs hFR, twoSlotForm D.T D.a D.b D.g S (TestFun.ind S - D.vP S) (D.ghat R)| ≤
      ((1 - D.ε) * D.A' + D.Cα + D.C₄₉) * D.E R := by
  classical
  have hA := D.A'_nonneg
  have hE0 : ∀ S, 0 ≤ D.E S := fun S => (D.E_pos S).le
  have hsumE : ∑ S ∈ D.Sout hR hRs hFR, D.E S ≤ (1 - D.ε) * D.E R :=
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun S _ _ => hE0 S).trans
      (D.sum_E_second_le hR hRs hFR)
  have hsumE' : ∑ S ∈ D.Sout hR hRs hFR, D.E S ≤ D.E R :=
    hsumE.trans (mul_le_of_le_one_left (hE0 R) (by linarith [D.ε_pos]))
  have hCα0 : 0 ≤ D.Cα := by
    have := D.psiConst_nonneg
    have := D.CG_pos
    have : 0 ≤ D.B := by linarith [D.hB]
    unfold Cα
    positivity
  have hC₄₉ := D.C₄₉_nonneg
  -- the three terms
  have h1 : ∑ S ∈ D.Sout hR hRs hFR, |D.form2 S (TestFun.ind S) (D.psi S)| ≤
      (1 - D.ε) * D.A' * D.E R := by
    calc ∑ S ∈ D.Sout hR hRs hFR, |D.form2 S (TestFun.ind S) (D.psi S)|
        ≤ ∑ S ∈ D.Sout hR hRs hFR, D.A' * D.E S := Finset.sum_le_sum fun S hS =>
          D.estimate_2_23 (D.Sout_mem_tree hR hRs hFR hS) (D.Sout_notInStopping hR hRs hFR hS)
      _ = D.A' * ∑ S ∈ D.Sout hR hRs hFR, D.E S := by rw [Finset.mul_sum]
      _ ≤ D.A' * ((1 - D.ε) * D.E R) := mul_le_mul_of_nonneg_left hsumE hA
      _ = _ := by ring
  have h2 : ∑ S ∈ D.Sout hR hRs hFR, |D.form2 S (D.vP S) (D.psi S)| ≤ D.Cα * D.E R := by
    calc ∑ S ∈ D.Sout hR hRs hFR, |D.form2 S (D.vP S) (D.psi S)|
        ≤ ∑ S ∈ D.Sout hR hRs hFR, D.Cα * D.E S := Finset.sum_le_sum fun S hS => by
          have := D.abs_form2_v_ghat_le (D.Sout_mem_tree hR hRs hFR hS)
            (D.Sout_notInStopping hR hRs hFR hS) hG
          rwa [ghat_eq, ← form2, D.form2_truncateₗ_right] at this
      _ = D.Cα * ∑ S ∈ D.Sout hR hRs hFR, D.E S := by rw [Finset.mul_sum]
      _ ≤ D.Cα * D.E R := mul_le_mul_of_nonneg_left hsumE' hCα0
  have h3 : ∑ S ∈ D.Sout hR hRs hFR,
      |(D.cS S - D.cS R) * slotForm D.T D.a D.g S (TestFun.ind S - D.vP S)| ≤ D.C₄₉ * D.E R := by
    calc ∑ S ∈ D.Sout hR hRs hFR,
          |(D.cS S - D.cS R) * slotForm D.T D.a D.g S (TestFun.ind S - D.vP S)|
        ≤ ∑ S ∈ D.Sout hR hRs hFR, D.C₄₉ * D.E S := Finset.sum_le_sum fun S hS =>
          D.abs_term_2_49_le hR hRs hG (D.Sout_mem_tree hR hRs hFR hS)
            (D.Sout_notInStopping hR hRs hFR hS)
      _ = D.C₄₉ * ∑ S ∈ D.Sout hR hRs hFR, D.E S := by rw [Finset.mul_sum]
      _ ≤ D.C₄₉ * D.E R := mul_le_mul_of_nonneg_left hsumE' hC₄₉
  calc |∑ S ∈ D.Sout hR hRs hFR, twoSlotForm D.T D.a D.b D.g S (TestFun.ind S - D.vP S) (D.ghat R)|
      = |∑ S ∈ D.Sout hR hRs hFR, (D.form2 S (TestFun.ind S) (D.psi S) -
          D.form2 S (D.vP S) (D.psi S) +
          (D.cS S - D.cS R) * slotForm D.T D.a D.g S (TestFun.ind S - D.vP S))| := by
        rw [Finset.sum_congr rfl fun S hS =>
          D.form2_ind_sub_vP_ghat_eq (D.Sout_subset_R hR hRs hFR hS)]
    _ ≤ ∑ S ∈ D.Sout hR hRs hFR, (|D.form2 S (TestFun.ind S) (D.psi S)| +
          |D.form2 S (D.vP S) (D.psi S)| +
          |(D.cS S - D.cS R) * slotForm D.T D.a D.g S (TestFun.ind S - D.vP S)|) := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun S _ => ?_)
        exact (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    _ = ∑ S ∈ D.Sout hR hRs hFR, |D.form2 S (TestFun.ind S) (D.psi S)| +
          ∑ S ∈ D.Sout hR hRs hFR, |D.form2 S (D.vP S) (D.psi S)| +
          ∑ S ∈ D.Sout hR hRs hFR,
            |(D.cS S - D.cS R) * slotForm D.T D.a D.g S (TestFun.ind S - D.vP S)| := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ ≤ (1 - D.ε) * D.A' * D.E R + D.Cα * D.E R + D.C₄₉ * D.E R := add_le_add (add_le_add h1 h2) h3
    _ = _ := by ring

end Sum244

end StoppingData

end StoppingCollections

end MirekThiele
