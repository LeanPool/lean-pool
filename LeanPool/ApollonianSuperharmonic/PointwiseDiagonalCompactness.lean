/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Sequences
public import LeanPool.ApollonianSuperharmonic.IntegerLaplacianCastBridge
public import LeanPool.ApollonianSuperharmonic.LocalExponentialEstimate
public import LeanPool.ApollonianSuperharmonic.QuadraticAffineLaplacian
public import LeanPool.ApollonianSuperharmonic.RealLaplacianLinearity
public import Mathlib.Algebra.Order.Ring.Star

-- [TABLET NODE: PointwiseDiagonalCompactness]

/-!
# PointwiseDiagonalCompactness

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace DiagonalCompactnessProof

private theorem hw0 :
    (by
      classical
      exact
        ∀ (B : ℕ → Matrix (Fin (2 : ℕ)) (Fin (2 : ℕ)) ℝ), ∀ (b : ℕ → Fin (2 : ℕ) → ℝ), ∀ (u : ℕ →
            IntegerLatticeFunction), (∀ (k : ℕ), u k (0 : GaussianInt) = (0 : ℤ)) → (
        let w : Nat → GaussianInt → Real := fun k x =>
          (u k x : Real) - LatticeQuadraticForm (B k) x -
            dotProduct (b k) ![(x.re : Real), (x.im : Real)]
        ∀ k, w k 0 = 0) ) := by
  classical
  intro B b u hu0 w k
  simp [w, hu0 k, LatticeQuadraticForm, dotProduct]

private theorem hwpos :
    (by
      classical
      exact
        ∀ (B : ℕ → Matrix (Fin (2 : ℕ)) (Fin (2 : ℕ)) ℝ), ∀ (b : ℕ → Fin (2 : ℕ) → ℝ), ∀ (u : ℕ →
            IntegerLatticeFunction), (∀ (k : ℕ), ∀ (x : GaussianInt), LatticeQuadraticForm (B k)
            x + b k ⬝ᵥ ![(↑x.re : ℝ), (↑x.im : ℝ)] ≤ (↑(u k x) : ℝ)) → (
        let w : Nat → GaussianInt → Real := fun k x =>
          (u k x : Real) - LatticeQuadraticForm (B k) x -
            dotProduct (b k) ![(x.re : Real), (x.im : Real)]
        ∀ k, ∀ x, 0 ≤ w k x) ) := by
  classical
  intro B b u hulower w k x
  dsimp [w]
  linarith [hulower k x]

private theorem hwl :
    (by
      classical
      exact
        ∀ (B : ℕ → Matrix (Fin (2 : ℕ)) (Fin (2 : ℕ)) ℝ), ∀ (b : ℕ → Fin (2 : ℕ) → ℝ), ∀ (u : ℕ →
            IntegerLatticeFunction), ∀ (M : ℝ), (∀ (k : ℕ), (B k).IsSymm) → ((∀ (k : ℕ), ∀ (x :
            GaussianInt), FourNeighborLaplacian (u k) x ≤ (1 : ℤ)) → ((∀ (k : ℕ), (1 : ℝ) - (B
            k).trace ≤ M) → (
        let w : Nat → GaussianInt → Real := fun k x =>
          (u k x : Real) - LatticeQuadraticForm (B k) x -
            dotProduct (b k) ![(x.re : Real), (x.im : Real)]
        ∀ k, ∀ x, RealFourNeighborLaplacian (w k) x ≤ M))) ) := by
  classical
  intro B b u M hBsymm hulap htrace w k x
  dsimp [w]
  have hshape : (fun y => (u k y : Real) - LatticeQuadraticForm (B k) y -
      dotProduct (b k) ![(y.re : Real), (y.im : Real)]) =
      (fun y => (u k y : Real) - (LatticeQuadraticForm (B k) y +
        dotProduct (b k) ![(y.re : Real), (y.im : Real)])) := by
    funext y
    ring
  rw [hshape]
  have hlin := RealLaplacianLinearity
    (fun y => (u k y : Real))
    (fun y => LatticeQuadraticForm (B k) y +
      dotProduct (b k) ![(y.re : Real), (y.im : Real)]) 1 (-1) x
  have hwexpr : (fun y => (u k y : Real) - (LatticeQuadraticForm (B k) y +
      dotProduct (b k) ![(y.re : Real), (y.im : Real)])) =
      (fun y => 1 * (u k y : Real) + (-1) *
        (LatticeQuadraticForm (B k) y +
          dotProduct (b k) ![(y.re : Real), (y.im : Real)])) := by
    funext y
    simp
    ring
  rw [hwexpr]
  rw [hlin]
  have hq := QuadraticAffineLaplacian (B k) (hBsymm k) (b k) 0 x
  simp only [one_mul, neg_one_mul, add_zero] at hq ⊢
  have hc : RealFourNeighborLaplacian (fun y => (u k y : Real)) x ≤ 1 := by
    rw [IntegerLaplacianCastBridge]
    exact_mod_cast hulap k x
  rw [hq]
  have ht := htrace k
  linarith

private theorem hwb :
    (by
      classical
      exact
        ∀ (B : ℕ → Matrix (Fin (2 : ℕ)) (Fin (2 : ℕ)) ℝ), ∀ (b : ℕ → Fin (2 : ℕ) → ℝ), ∀ (u : ℕ →
            IntegerLatticeFunction), ∀ (M : ℝ),
        let w : Nat → GaussianInt → Real := fun k x =>
          (u k x : Real) - LatticeQuadraticForm (B k) x -
            dotProduct (b k) ![(x.re : Real), (x.im : Real)]
        (∀ k, w k 0 = 0) → ((∀ k, ∀ x, 0 ≤ w k x) → ((∀ k, ∀ x, RealFourNeighborLaplacian (w k) x
            ≤ M) → (∀ k, ∀ x, w k x ≤ (4 : Real) ^ (x.re.natAbs + x.im.natAbs) * (0 : Real) + M *
            (((4 : Real) ^ (x.re.natAbs + x.im.natAbs) - 1) / 3)))) ) := by
  classical
  intro B b u M w hw0 hwpos hwl k x
  simpa [hw0 k] using LocalExponentialEstimate (w k) M (hwpos k) (hwl k) x

private theorem hentry :
    (by
      classical
      exact
        ∀ (A : Matrix (Fin (2 : ℕ)) (Fin (2 : ℕ)) ℝ), ∀ (B : ℕ → Matrix (Fin (2 : ℕ)) (Fin (2 :
            ℕ)) ℝ), (∀ (i : Fin (2 : ℕ)), ∀ (j : Fin (2 : ℕ)), Filter.Tendsto (fun (k : ℕ) => B k
            i j) Filter.atTop (nhds (A i j))) → (∀ i j : Fin 2, ∃ lo hi : Real, ∀ k, lo ≤ B k i j
            ∧ B k i j ≤ hi) ) := by
  classical
  intro A B hconv i j
  have hu : ∀ᶠ k in Filter.atTop, B k i j < A i j + 1 :=
    (hconv i j) (Iio_mem_nhds (by linarith))
  have hl : ∀ᶠ k in Filter.atTop, A i j - 1 < B k i j :=
    (hconv i j) (Ioi_mem_nhds (by linarith))
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp hu
  obtain ⟨L, hL⟩ := Filter.eventually_atTop.mp hl
  let N := max K L
  let values := (Finset.range (N + 1)).image (fun k => B k i j)
  have values_ne : values.Nonempty := by
    refine ⟨B 0 i j, ?_⟩
    exact Finset.mem_image.mpr ⟨0, by simp, rfl⟩
  let lo := min (A i j - 1) (values.min' values_ne)
  let hi := max (A i j + 1) (values.max' values_ne)
  refine ⟨lo, hi, ?_⟩
  intro k
  have hmem : ∀ {r : Real}, r ∈ values → lo ≤ r ∧ r ≤ hi := by
    intro r hr
    exact ⟨le_trans (min_le_right _ _) (Finset.min'_le values r hr),
      le_trans (Finset.le_max' values r hr) (le_max_of_le_right (le_refl _))⟩
  by_cases hk : k ≤ N
  · have hkr : k ∈ Finset.range (N + 1) := by simp [hk]
    have hr : B k i j ∈ values := Finset.mem_image.mpr ⟨k, hkr, rfl⟩
    exact hmem hr
  · have hkK : K ≤ k := le_trans (le_max_left _ _) (Nat.le_of_not_ge hk)
    have hkL : L ≤ k := le_trans (le_max_right _ _) (Nat.le_of_not_ge hk)
    constructor
    · exact le_trans (min_le_left _ _) (le_of_lt (hL k hkL))
    · exact le_trans (le_of_lt (hK k hkK)) (le_max_left _ _)

private theorem hub :
    (by
      classical
      exact
        ∀ (B : ℕ → Matrix (Fin (2 : ℕ)) (Fin (2 : ℕ)) ℝ), ∀ (b : ℕ → Fin (2 : ℕ) → ℝ), ∀ (u : ℕ →
            IntegerLatticeFunction), ∀ (M : ℝ), (∀ (k : ℕ), ∀ (i : Fin (2 : ℕ)), |b k i| ≤ (1 :
            ℝ)) → (
        let w : Nat → GaussianInt → Real := fun k x =>
          (u k x : Real) - LatticeQuadraticForm (B k) x -
            dotProduct (b k) ![(x.re : Real), (x.im : Real)]
        (∀ k, ∀ x, 0 ≤ w k x) → ((∀ k, ∀ x, w k x ≤ (4 : Real) ^ (x.re.natAbs + x.im.natAbs) * (0
            : Real) + M * (((4 : Real) ^ (x.re.natAbs + x.im.natAbs) - 1) / 3)) → ((∀ i j : Fin
            2, ∃ lo hi : Real, ∀ k, lo ≤ B k i j ∧ B k i j ≤ hi) → (∀ x, ∃ C : Real, ∀ k, |(u k x
            : Real)| ≤ C)))) ) := by
  classical
  intro B b u M hb w hwpos hwb hentry x
  rcases hentry 0 0 with ⟨l00, u00, hL00⟩
  rcases hentry 0 1 with ⟨l01, u01, hL01⟩
  rcases hentry 1 0 with ⟨l10, u10, hL10⟩
  rcases hentry 1 1 with ⟨l11, u11, hL11⟩
  refine ⟨M * (((4 : Real) ^ (x.re.natAbs + x.im.natAbs) - 1) / 3) +
    |(x.re : Real)| * (|l00| + |u00|) * |(x.re : Real)| / 2 +
    |(x.re : Real)| * (|l01| + |u01|) * |(x.im : Real)| / 2 +
    |(x.im : Real)| * (|l10| + |u10|) * |(x.re : Real)| / 2 +
    |(x.im : Real)| * (|l11| + |u11|) * |(x.im : Real)| / 2 +
    |(x.re : Real)| + |(x.im : Real)| + 10, ?_⟩
  intro k
  have hw := hwb k x
  have hp := hwpos k x
  have h00' := hL00 k
  have h01' := hL01 k
  have h10' := hL10 k
  have h11' := hL11 k
  have hb0 := hb k 0
  have hb1 := hb k 1
  dsimp [w] at hw
  dsimp [w] at hp
  simp only [LatticeQuadraticForm, one_div, dotProduct, Int.reduceNeg, GaussianInt.intCast_re,
      GaussianInt.intCast_im, Matrix.mulVec, Fin.sum_univ_two, Fin.isValue,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, mul_zero, zero_add,
      tsub_le_iff_right, ge_iff_le] at hw ⊢
  simp only [LatticeQuadraticForm, one_div, dotProduct, Int.reduceNeg, GaussianInt.intCast_re,
      GaussianInt.intCast_im, Matrix.mulVec, Fin.sum_univ_two, Fin.isValue,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, sub_nonneg] at hp
  have e00 : |B k 0 0| ≤ |l00| + |u00| := by
    rw [abs_le]
    constructor <;> nlinarith [h00'.1, h00'.2, neg_le_abs l00, neg_le_abs u00,
      le_abs_self l00, le_abs_self u00]
  have e01 : |B k 0 1| ≤ |l01| + |u01| := by
    rw [abs_le]
    constructor <;> nlinarith [h01'.1, h01'.2, neg_le_abs l01, neg_le_abs u01,
      le_abs_self l01, le_abs_self u01]
  have e10 : |B k 1 0| ≤ |l10| + |u10| := by
    rw [abs_le]
    constructor <;> nlinarith [h10'.1, h10'.2, neg_le_abs l10, neg_le_abs u10,
      le_abs_self l10, le_abs_self u10]
  have e11 : |B k 1 1| ≤ |l11| + |u11| := by
    rw [abs_le]
    constructor <;> nlinarith [h11'.1, h11'.2, neg_le_abs l11, neg_le_abs u11,
      le_abs_self l11, le_abs_self u11]
  have hxre : (GaussianInt.toComplex x).re = (x.re : Real) := by
    exact (GaussianInt.intCast_re x).symm
  have hxim : (GaussianInt.toComplex x).im = (x.im : Real) := by
    exact (GaussianInt.intCast_im x).symm
  have q00 : |(GaussianInt.toComplex x).re * (B k 0 0 * (GaussianInt.toComplex x).re)| ≤
      |(x.re : Real)| * (|l00| + |u00|) * |(x.re : Real)| := by
    rw [hxre]
    rw [abs_mul, abs_mul]
    calc
      |(x.re : Real)| * (|B k 0 0| * |(x.re : Real)|) ≤
          |(x.re : Real)| * ((|l00| + |u00|) * |(x.re : Real)|) := by
            gcongr
      _ = _ := by ring
  have q01 : |(GaussianInt.toComplex x).re * (B k 0 1 * (GaussianInt.toComplex x).im)| ≤
      |(x.re : Real)| * (|l01| + |u01|) * |(x.im : Real)| := by
    rw [hxre, hxim]
    rw [abs_mul, abs_mul]
    calc
      |(x.re : Real)| * (|B k 0 1| * |(x.im : Real)|) ≤
          |(x.re : Real)| * ((|l01| + |u01|) * |(x.im : Real)|) := by
            gcongr
      _ = _ := by ring
  have q10 : |(GaussianInt.toComplex x).im * (B k 1 0 * (GaussianInt.toComplex x).re)| ≤
      |(x.im : Real)| * (|l10| + |u10|) * |(x.re : Real)| := by
    rw [hxim, hxre]
    rw [abs_mul, abs_mul]
    calc
      |(x.im : Real)| * (|B k 1 0| * |(x.re : Real)|) ≤
          |(x.im : Real)| * ((|l10| + |u10|) * |(x.re : Real)|) := by
            gcongr
      _ = _ := by ring
  have q11 : |(GaussianInt.toComplex x).im * (B k 1 1 * (GaussianInt.toComplex x).im)| ≤
      |(x.im : Real)| * (|l11| + |u11|) * |(x.im : Real)| := by
    rw [hxim]
    rw [abs_mul, abs_mul]
    calc
      |(x.im : Real)| * (|B k 1 1| * |(x.im : Real)|) ≤
          |(x.im : Real)| * ((|l11| + |u11|) * |(x.im : Real)|) := by
            gcongr
      _ = _ := by ring
  have d0 : |b k 0 * (GaussianInt.toComplex x).re| ≤ |(x.re : Real)| := by
    rw [hxre]
    rw [abs_mul]
    calc
      |b k 0| * |(x.re : Real)| ≤ 1 * |(x.re : Real)| := by
        gcongr
      _ = _ := by ring
  have d1 : |b k 1 * (GaussianInt.toComplex x).im| ≤ |(x.im : Real)| := by
    rw [hxim]
    rw [abs_mul]
    calc
      |b k 1| * |(x.im : Real)| ≤ 1 * |(x.im : Real)| := by
        gcongr
      _ = _ := by ring
  rw [hxre, hxim] at hw ⊢
  simp only [hxre, hxim] at hp
  simp only [hxre, hxim] at q00 q01 q10 q11 d0 d1
  have hu : (u k x : Real) ≤ M * (((4 : Real) ^ (x.re.natAbs + x.im.natAbs) - 1) / 3) +
      |(x.re : Real)| * (|l00| + |u00|) * |(x.re : Real)| / 2 +
      |(x.re : Real)| * (|l01| + |u01|) * |(x.im : Real)| / 2 +
      |(x.im : Real)| * (|l10| + |u10|) * |(x.re : Real)| / 2 +
      |(x.im : Real)| * (|l11| + |u11|) * |(x.im : Real)| / 2 +
      |(x.re : Real)| + |(x.im : Real)| + 10 := by
    linarith [q00, q01, q10, q11, d0, d1,
    le_abs_self (b k 0 * (x.re : Real)),
    le_abs_self (b k 1 * (x.im : Real)),
    le_abs_self ((x.re : Real) * (B k 0 0 * (x.re : Real))),
    le_abs_self ((x.re : Real) * (B k 0 1 * (x.im : Real))),
    le_abs_self ((x.im : Real) * (B k 1 0 * (x.re : Real))),
    le_abs_self ((x.im : Real) * (B k 1 1 * (x.im : Real))),
    abs_nonneg l00, abs_nonneg u00, abs_nonneg l01, abs_nonneg u01,
    abs_nonneg l10, abs_nonneg u10, abs_nonneg l11, abs_nonneg u11,
    abs_nonneg (x.re : Real), abs_nonneg (x.im : Real)]
  have hl : -(M * (((4 : Real) ^ (x.re.natAbs + x.im.natAbs) - 1) / 3) +
      |(x.re : Real)| * (|l00| + |u00|) * |(x.re : Real)| / 2 +
      |(x.re : Real)| * (|l01| + |u01|) * |(x.im : Real)| / 2 +
      |(x.im : Real)| * (|l10| + |u10|) * |(x.re : Real)| / 2 +
      |(x.im : Real)| * (|l11| + |u11|) * |(x.im : Real)| / 2 +
      |(x.re : Real)| + |(x.im : Real)| + 10) ≤ (u k x : Real) := by
    linarith [q00, q01, q10, q11, d0, d1,
      neg_le_abs (b k 0 * (x.re : Real)),
      neg_le_abs (b k 1 * (x.im : Real)),
      neg_le_abs ((x.re : Real) * (B k 0 0 * (x.re : Real))),
      neg_le_abs ((x.re : Real) * (B k 0 1 * (x.im : Real))),
      neg_le_abs ((x.im : Real) * (B k 1 0 * (x.re : Real))),
      neg_le_abs ((x.im : Real) * (B k 1 1 * (x.im : Real))),
      abs_nonneg l00, abs_nonneg u00, abs_nonneg l01, abs_nonneg u01,
      abs_nonneg l10, abs_nonneg u10, abs_nonneg l11, abs_nonneg u11,
      abs_nonneg (x.re : Real), abs_nonneg (x.im : Real)]
  exact abs_le.2 ⟨hl, hu⟩

private theorem enumerate_surj :
    (by
      classical
      exact
        ∀ [this : Encodable GaussianInt],
        let enumerate : Nat → GaussianInt := fun n =>
          (Encodable.decode n).getD 0
        ∀ x : GaussianInt, ∃ n, enumerate n = x ) := by
  classical
  intro this enumerate x
  refine ⟨Encodable.encode x, ?_⟩
  simp [enumerate, Encodable.encodek]

private theorem refineFiber :
    (by
      classical
      exact
        ∀ (u : ℕ → IntegerLatticeFunction), (∀ x, ∃ C : Real, ∀ k, |(u k x : Real)| ≤ C) → (∀ x :
            GaussianInt, ∀ s : Set Nat, s.Infinite → ∃ t : Set Nat, t ⊆ s ∧ t.Infinite ∧ ∃ z :
            Int, ∀ k ∈ t, u k x = z) ) := by
  classical
  intro u hub x s hs
  obtain ⟨C, hC⟩ := hub x
  let bound : Set Int := {z | |(z : Real)| ≤ C}
  let N : Nat := ⌈C⌉₊
  let positive : Set Int := {z | 0 ≤ z ∧ z.natAbs ≤ N}
  let negative : Set Int := {z | z ≤ 0 ∧ z.natAbs ≤ N}
  have hposimage : (Int.natAbs '' positive) ⊆ Set.Iic N := by
    intro n hn
    rcases hn with ⟨z, hz, rfl⟩
    exact hz.2
  have hnegimage : (Int.natAbs '' negative) ⊆ Set.Iic N := by
    intro n hn
    rcases hn with ⟨z, hz, rfl⟩
    exact hz.2
  have hpos : positive.Finite :=
    (Set.finite_Iic N).subset hposimage |>.of_finite_image
      (fun z hz w hw h => by
        have hh := congrArg (fun n : Nat => (n : Int)) h
        simpa [Int.natAbs_of_nonneg hz.1, Int.natAbs_of_nonneg hw.1] using hh)
  have hneg : negative.Finite :=
    (Set.finite_Iic N).subset hnegimage |>.of_finite_image
      (fun z hz w hw h => by
        have hh := congrArg (fun n : Nat => (n : Int)) h
        have ha : (-z : Int) = (z.natAbs : Int) := by
          simpa using (Int.natAbs_of_nonneg (neg_nonneg.mpr hz.1)).symm
        have hb : (-w : Int) = (w.natAbs : Int) := by
          simpa using (Int.natAbs_of_nonneg (neg_nonneg.mpr hw.1)).symm
        rw [← ha, ← hb] at hh
        simpa using congrArg Neg.neg hh)
  have hfinite : bound.Finite := by
    apply hpos.union hneg |>.subset
    intro z hz
    change |(z : Real)| ≤ C at hz
    by_cases hz0 : 0 ≤ z
    · left
      exact ⟨hz0, by
        have hc : 0 ≤ C := by
          exact le_trans (abs_nonneg (u 0 x : Real)) (hC 0)
        have hn : C ≤ (N : Real) := by exact_mod_cast Nat.le_ceil C
        have hzN : (z.natAbs : Real) ≤ (N : Real) := by
          have he : (z.natAbs : Real) = (z : Real) := by
            exact congrArg (fun q : Int => (q : Real)) (Int.natAbs_of_nonneg hz0)
          rw [he]
          exact (abs_le.mp hz).2.trans hn
        exact_mod_cast hzN⟩
    · right
      have hz0' : z ≤ 0 := le_of_not_ge hz0
      exact ⟨hz0', by
        have hc : 0 ≤ C := by
          exact le_trans (abs_nonneg (u 0 x : Real)) (hC 0)
        have hn : C ≤ (N : Real) := by exact_mod_cast Nat.le_ceil C
        have hzN : ((-z).natAbs : Real) ≤ (N : Real) := by
          have he : ((-z).natAbs : Real) = (-z : Real) := by
            simpa using congrArg (fun q : Int => (q : Real))
              (Int.natAbs_of_nonneg (neg_nonneg.mpr hz0'))
          rw [he]
          linarith [abs_le.mp hz |>.1, hn]
        simpa only [Int.natAbs_neg] using (show (-z).natAbs ≤ N by exact_mod_cast hzN)⟩
  let : Fintype bound := hfinite.fintype
  let α := {k : Nat // k ∈ s}
  let : Infinite α := hs.to_subtype
  let mapValue : α → bound := fun k =>
    ⟨u k.1 x, by exact hC k.1⟩
  obtain ⟨y, hy⟩ := Finite.exists_infinite_fiber mapValue
  let p : Set α := mapValue ⁻¹' ({y} : Set bound)
  let t : Set Nat := (fun k : α => k.1) '' p
  refine ⟨t, ?_, ?_, ?_⟩
  · intro k hk
    obtain ⟨q, hq, rfl⟩ := hk
    exact q.2
  · have ht : p.Infinite := Set.infinite_coe_iff.mp hy
    exact Set.Infinite.image (fun a _ b _ h => Subtype.ext h) ht
  · refine ⟨y.1, ?_⟩
    intro k hk
    obtain ⟨q, hq, rfl⟩ := hk
    have he : mapValue q = y := hq
    exact congrArg Subtype.val he

private theorem seq_step :
    (by
      classical
      exact
        ∀ (u : ℕ → IntegerLatticeFunction), ∀ [this : Encodable GaussianInt],
        let enumerate : Nat → GaussianInt := fun n =>
          (Encodable.decode n).getD 0
        ∀ (refineFiber : ∀ x : GaussianInt, ∀ s : Set Nat, s.Infinite → ∃ t : Set Nat, t ⊆ s ∧
            t.Infinite ∧ ∃ z : Int, ∀ k ∈ t, u k x = z),
        let next (n : Nat) (s : Set Nat) (hs : s.Infinite) : Set Nat :=
          Classical.choose (refineFiber (enumerate n) s hs)
        ∀ (next_spec : ∀ (n : Nat), ∀ (s : Set Nat), ∀ (hs : s.Infinite), next n s hs ⊆ s ∧ (next
            n s hs).Infinite ∧ ∃ z, ∀ k ∈ next n s hs, u k (enumerate n) = z),
        let good : Type := {s : Set Nat // s.Infinite}
        let seq : Nat → good := Nat.rec ⟨Set.univ, Set.infinite_univ⟩
          (fun n q => ⟨next n q.1 q.2, (next_spec n q.1 q.2).2.1⟩)
        ∀ (n : Nat), seq (n + 1) = ⟨next n (seq n).1 (seq n).2, (next_spec n (seq n).1 (seq
            n).2).2.1⟩ ) := by
  classical
  intro u this enumerate refineFiber next next_spec good seq n
  rfl

private theorem seq_nested :
    (by
      classical
      exact
        ∀ (u : ℕ → IntegerLatticeFunction), ∀ [this : Encodable GaussianInt],
        let enumerate : Nat → GaussianInt := fun n =>
          (Encodable.decode n).getD 0
        ∀ (refineFiber : ∀ x : GaussianInt, ∀ s : Set Nat, s.Infinite → ∃ t : Set Nat, t ⊆ s ∧
            t.Infinite ∧ ∃ z : Int, ∀ k ∈ t, u k x = z),
        let next (n : Nat) (s : Set Nat) (hs : s.Infinite) : Set Nat :=
          Classical.choose (refineFiber (enumerate n) s hs)
        ∀ (next_spec : ∀ (n : Nat), ∀ (s : Set Nat), ∀ (hs : s.Infinite), next n s hs ⊆ s ∧ (next
            n s hs).Infinite ∧ ∃ z, ∀ k ∈ next n s hs, u k (enumerate n) = z),
        let good : Type := {s : Set Nat // s.Infinite}
        let seq : Nat → good := Nat.rec ⟨Set.univ, Set.infinite_univ⟩
          (fun n q => ⟨next n q.1 q.2, (next_spec n q.1 q.2).2.1⟩)
        ∀ (m : ℕ), ∀ (n : ℕ), m ≤ n → (seq n).1 ⊆ (seq m).1 ) := by
  classical
  intro u this enumerate refineFiber next next_spec good seq m n hmn
  induction n, hmn using Nat.le_induction with
  | base => exact Set.Subset.rfl
  | succ n hmn ih =>
    exact (next_spec n (seq n).1 (seq n).2).1.trans ih

private theorem phi_spec :
    (by
      classical
      exact
        ∀ (u : ℕ → IntegerLatticeFunction), ∀ [this : Encodable GaussianInt],
        let enumerate : Nat → GaussianInt := fun n =>
          (Encodable.decode n).getD 0
        ∀ (refineFiber : ∀ x : GaussianInt, ∀ s : Set Nat, s.Infinite → ∃ t : Set Nat, t ⊆ s ∧
            t.Infinite ∧ ∃ z : Int, ∀ k ∈ t, u k x = z),
        let next (n : Nat) (s : Set Nat) (hs : s.Infinite) : Set Nat :=
          Classical.choose (refineFiber (enumerate n) s hs)
        ∀ (next_spec : ∀ (n : Nat), ∀ (s : Set Nat), ∀ (hs : s.Infinite), next n s hs ⊆ s ∧ (next
            n s hs).Infinite ∧ ∃ z, ∀ k ∈ next n s hs, u k (enumerate n) = z),
        let good : Type := {s : Set Nat // s.Infinite}
        let seq : Nat → good := Nat.rec ⟨Set.univ, Set.infinite_univ⟩
          (fun n q => ⟨next n q.1 q.2, (next_spec n q.1 q.2).2.1⟩)
        let first : Nat := Classical.choose (Set.Infinite.exists_gt (seq 0).2 0)
        (first ∈ (seq 0).1 ∧ 0 < first) → (
        let phi : Nat → Nat := Nat.rec first
          (fun n p => Classical.choose (Set.Infinite.exists_gt (seq (n + 1)).2 p))
        ∀ (n : ℕ), phi n ∈ (seq n).1) ) := by
  classical
  intro u this enumerate refineFiber next next_spec good seq first first_spec phi n
  induction n with
  | zero => exact first_spec.1
  | succ n ih =>
    exact (Classical.choose_spec (Set.Infinite.exists_gt (seq (n + 1)).2 (phi n))).1

private theorem phi_mono :
    (by
      classical
      exact
        ∀ (u : ℕ → IntegerLatticeFunction), ∀ [this : Encodable GaussianInt],
        let enumerate : Nat → GaussianInt := fun n =>
          (Encodable.decode n).getD 0
        ∀ (refineFiber : ∀ x : GaussianInt, ∀ s : Set Nat, s.Infinite → ∃ t : Set Nat, t ⊆ s ∧
            t.Infinite ∧ ∃ z : Int, ∀ k ∈ t, u k x = z),
        let next (n : Nat) (s : Set Nat) (hs : s.Infinite) : Set Nat :=
          Classical.choose (refineFiber (enumerate n) s hs)
        ∀ (next_spec : ∀ (n : Nat), ∀ (s : Set Nat), ∀ (hs : s.Infinite), next n s hs ⊆ s ∧ (next
            n s hs).Infinite ∧ ∃ z, ∀ k ∈ next n s hs, u k (enumerate n) = z),
        let good : Type := {s : Set Nat // s.Infinite}
        let seq : Nat → good := Nat.rec ⟨Set.univ, Set.infinite_univ⟩
          (fun n q => ⟨next n q.1 q.2, (next_spec n q.1 q.2).2.1⟩)
        let first : Nat := Classical.choose (Set.Infinite.exists_gt (seq 0).2 0)
        let phi : Nat → Nat := Nat.rec first
          (fun n p => Classical.choose (Set.Infinite.exists_gt (seq (n + 1)).2 p))
        StrictMono phi ) := by
  classical
  intro u this enumerate refineFiber next next_spec good seq first phi
  apply strictMono_nat_of_lt_succ
  intro n
  exact (Classical.choose_spec (Set.Infinite.exists_gt (seq (n + 1)).2 (phi n))).2

private theorem boundedSubsequence :
    (by
      classical
      exact
        ∀ f : Nat → Real, (∀ n, -1 ≤ f n ∧ f n ≤ 1) → ∃ q : Nat → Nat, StrictMono q ∧ ∃ c : Real,
            Filter.Tendsto (fun n => f (q n)) Filter.atTop (nhds c) ) := by
  classical
  intro f hf
  obtain ⟨c, _, q, hq, hc⟩ :=
    (isCompact_Icc : IsCompact (Set.Icc (-1 : Real) 1)).tendsto_subseq hf
  exact ⟨q, hq, c, hc⟩

private theorem hpsi_ge :
    (by
      classical
      exact
        ∀ (q0 : ℕ → ℕ), ∀ (q1 : ℕ → ℕ),
        let psi : Nat → Nat := q0 ∘ q1
        (StrictMono psi) → (∀ n, n ≤ psi n) ) := by
  classical
  intro q0 q1 psi hpsi n
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih =>
      exact Nat.succ_le_of_lt (lt_of_le_of_lt ih (hpsi (Nat.lt_succ_self n)))

private theorem fiber_spec :
    (by
      classical
      exact
        ∀ (u : ℕ → IntegerLatticeFunction), ∀ [this : Encodable GaussianInt],
        let enumerate : Nat → GaussianInt := fun n =>
          (Encodable.decode n).getD 0
        ∀ (enumerate_surj : ∀ x : GaussianInt, ∃ n, enumerate n = x), ∀ (refineFiber : ∀ x :
            GaussianInt, ∀ s : Set Nat, s.Infinite → ∃ t : Set Nat, t ⊆ s ∧ t.Infinite ∧ ∃ z :
            Int, ∀ k ∈ t, u k x = z),
        let next (n : Nat) (s : Set Nat) (hs : s.Infinite) : Set Nat :=
          Classical.choose (refineFiber (enumerate n) s hs)
        ∀ (next_spec : ∀ (n : Nat), ∀ (s : Set Nat), ∀ (hs : s.Infinite), next n s hs ⊆ s ∧ (next
            n s hs).Infinite ∧ ∃ z, ∀ k ∈ next n s hs, u k (enumerate n) = z),
        let good : Type := {s : Set Nat // s.Infinite}
        let seq : Nat → good := Nat.rec ⟨Set.univ, Set.infinite_univ⟩
          (fun n q => ⟨next n q.1 q.2, (next_spec n q.1 q.2).2.1⟩)
        let index : GaussianInt → Nat := fun x => Classical.choose (enumerate_surj x)
        (∀ (x : GaussianInt), enumerate (index x) = x) → (∀ (x : GaussianInt), ∃ z : Int, ∀ k ∈
            next (index x) (seq (index x)).1 (seq (index x)).2, u k x = z) ) := by
  classical
  intro u this enumerate enumerate_surj refineFiber next next_spec good seq index index_spec x
  simpa [index, index_spec x] using
    (next_spec (index x) (seq (index x)).1 (seq (index x)).2).2.2

private theorem eventual_eq :
    (by
      classical
      exact
        ∀ (u : ℕ → IntegerLatticeFunction), ∀ [this : Encodable GaussianInt],
        let enumerate : Nat → GaussianInt := fun n =>
          (Encodable.decode n).getD 0
        ∀ (enumerate_surj : ∀ x : GaussianInt, ∃ n, enumerate n = x), ∀ (refineFiber : ∀ x :
            GaussianInt, ∀ s : Set Nat, s.Infinite → ∃ t : Set Nat, t ⊆ s ∧ t.Infinite ∧ ∃ z :
            Int, ∀ k ∈ t, u k x = z),
        let next (n : Nat) (s : Set Nat) (hs : s.Infinite) : Set Nat :=
          Classical.choose (refineFiber (enumerate n) s hs)
        ∀ (next_spec : ∀ (n : Nat), ∀ (s : Set Nat), ∀ (hs : s.Infinite), next n s hs ⊆ s ∧ (next
            n s hs).Infinite ∧ ∃ z, ∀ k ∈ next n s hs, u k (enumerate n) = z),
        let good : Type := {s : Set Nat // s.Infinite}
        let seq : Nat → good := Nat.rec ⟨Set.univ, Set.infinite_univ⟩
          (fun n q => ⟨next n q.1 q.2, (next_spec n q.1 q.2).2.1⟩)
        (∀ (n : Nat), seq (n + 1) = ⟨next n (seq n).1 (seq n).2, (next_spec n (seq n).1 (seq
            n).2).2.1⟩) → ((∀ (m : Nat), ∀ (n : Nat), (m ≤ n) → ((seq n).1 ⊆ (seq m).1)) → (
        let first : Nat := Classical.choose (Set.Infinite.exists_gt (seq 0).2 0)
        let phi : Nat → Nat := Nat.rec first
          (fun n p => Classical.choose (Set.Infinite.exists_gt (seq (n + 1)).2 p))
        (∀ (n : Nat), phi n ∈ (seq n).1) → (∀ (q0 : ℕ → ℕ), ∀ (q1 : ℕ → ℕ),
        let psi : Nat → Nat := q0 ∘ q1
        (∀ n, n ≤ psi n) → (
        let output : Nat → Nat := phi ∘ psi
        let index : GaussianInt → Nat := fun x => Classical.choose (enumerate_surj x)
        ∀ (fiber_spec : ∀ (x : GaussianInt), ∃ z : Int, ∀ k ∈ next (index x) (seq (index x)).1
            (seq (index x)).2, u k x = z),
        let v : IntegerLatticeFunction := fun x => Classical.choose (fiber_spec x)
        (∀ (x : GaussianInt), ∀ k ∈ next (index x) (seq (index x)).1 (seq (index x)).2, u k x = v
            x) → (∀ (x : GaussianInt), ∃ (K : ℕ), ∀ (k : ℕ), K ≤ k → u (output k) x = v x))))) )
            := by
  classical
  intro u this enumerate enumerate_surj refineFiber next next_spec good seq seq_step seq_nested
      first phi phi_spec q0 q1 psi hpsi_ge output index fiber_spec v v_spec x
  let n := index x
  refine ⟨n + 1, ?_⟩
  intro k hk
  have hm : n + 1 ≤ psi k := le_trans hk (hpsi_ge k)
  have hs : phi (psi k) ∈ (seq (n + 1)).1 :=
    (seq_nested (n + 1) (psi k) hm) (phi_spec (psi k))
  have hs' : phi (psi k) ∈ next n (seq n).1 (seq n).2 := by
    simpa [seq_step] using hs
  exact v_spec x (phi (psi k)) hs'

private theorem hlim :
    (by
      classical
      exact
        ∀ (A : Matrix (Fin (2 : ℕ)) (Fin (2 : ℕ)) ℝ), ∀ (B : ℕ → Matrix (Fin (2 : ℕ)) (Fin (2 :
            ℕ)) ℝ), ∀ (b : ℕ → Fin (2 : ℕ) → ℝ), ∀ (u : ℕ → IntegerLatticeFunction), ∀ [this :
            Encodable GaussianInt],
        let enumerate : Nat → GaussianInt := fun n =>
          (Encodable.decode n).getD 0
        ∀ (refineFiber : ∀ x : GaussianInt, ∀ s : Set Nat, s.Infinite → ∃ t : Set Nat, t ⊆ s ∧
            t.Infinite ∧ ∃ z : Int, ∀ k ∈ t, u k x = z),
        let next (n : Nat) (s : Set Nat) (hs : s.Infinite) : Set Nat :=
          Classical.choose (refineFiber (enumerate n) s hs)
        ∀ (next_spec : ∀ (n : Nat), ∀ (s : Set Nat), ∀ (hs : s.Infinite), next n s hs ⊆ s ∧ (next
            n s hs).Infinite ∧ ∃ z, ∀ k ∈ next n s hs, u k (enumerate n) = z),
        let good : Type := {s : Set Nat // s.Infinite}
        let seq : Nat → good := Nat.rec ⟨Set.univ, Set.infinite_univ⟩
          (fun n q => ⟨next n q.1 q.2, (next_spec n q.1 q.2).2.1⟩)
        let first : Nat := Classical.choose (Set.Infinite.exists_gt (seq 0).2 0)
        let phi : Nat → Nat := Nat.rec first
          (fun n p => Classical.choose (Set.Infinite.exists_gt (seq (n + 1)).2 p))
        ∀ (q0 : ℕ → ℕ), ∀ (c0 : ℝ), ∀ (q1 : ℕ → ℕ), ∀ (c1 : ℝ),
        let psi : Nat → Nat := q0 ∘ q1
        let bInf : Fin 2 → Real := ![c0, c1]
        let output : Nat → Nat := phi ∘ psi
        ∀ (x : GaussianInt), (Filter.Tendsto ((fun (k : ℕ) => B k (0 : Fin (2 : ℕ)) (0 : Fin (2 :
            ℕ))) ∘ output) Filter.atTop (nhds (A (0 : Fin (2 : ℕ)) (0 : Fin (2 : ℕ))))) →
            ((Filter.Tendsto ((fun (k : ℕ) => B k (0 : Fin (2 : ℕ)) (1 : Fin (2 : ℕ))) ∘ output)
            Filter.atTop (nhds (A (0 : Fin (2 : ℕ)) (1 : Fin (2 : ℕ))))) → ((Filter.Tendsto ((fun
            (k : ℕ) => B k (1 : Fin (2 : ℕ)) (0 : Fin (2 : ℕ))) ∘ output) Filter.atTop (nhds (A
            (1 : Fin (2 : ℕ)) (0 : Fin (2 : ℕ))))) → ((Filter.Tendsto ((fun (k : ℕ) => B k (1 :
            Fin (2 : ℕ)) (1 : Fin (2 : ℕ))) ∘ output) Filter.atTop (nhds (A (1 : Fin (2 : ℕ)) (1
            : Fin (2 : ℕ))))) → ((Filter.Tendsto ((fun (n : ℕ) => b (phi (q0 n)) (0 : Fin (2 :
            ℕ))) ∘ q1) Filter.atTop (nhds c0)) → ((Filter.Tendsto (fun (n : ℕ) => b (phi (q0 (q1
            n))) (1 : Fin (2 : ℕ))) Filter.atTop (nhds c1)) → (Filter.Tendsto (fun k =>
            LatticeQuadraticForm (B (output k)) x + dotProduct (b (output k)) ![(x.re : Real),
            (x.im : Real)]) Filter.atTop (nhds (LatticeQuadraticForm A x + dotProduct bInf
            ![(x.re : Real), (x.im : Real)])))))))) ) := by
  classical
  intro A B b u this enumerate refineFiber next next_spec good seq first phi q0 c0 q1 c1 psi bInf
      output x h00 h01 h10 h11 hb0 hb1
  have xr : Filter.Tendsto (fun _ : Nat => (x.re : Real)) Filter.atTop
      (nhds (x.re : Real)) := tendsto_const_nhds
  have xi : Filter.Tendsto (fun _ : Nat => (x.im : Real)) Filter.atTop
      (nhds (x.im : Real)) := tendsto_const_nhds
  have half : Filter.Tendsto (fun _ : Nat => (2 : Real)⁻¹) Filter.atTop
      (nhds ((2 : Real)⁻¹)) := tendsto_const_nhds
  have r0 := (h00.mul xr).add (h01.mul xi)
  have r1 := (h10.mul xr).add (h11.mul xi)
  have q0 := xr.mul r0
  have q1 := xi.mul r1
  have q := half.mul (q0.add q1)
  have d := (hb0.mul xr).add (hb1.mul xi)
  have all := q.add d
  convert all using 1 <;>
    simp [LatticeQuadraticForm, Matrix.mulVec, dotProduct, output, bInf,
      psi, Function.comp_def]

end DiagonalCompactnessProof

theorem PointwiseDiagonalCompactness :
    ∀ (A : Matrix (Fin 2) (Fin 2) Real), ∀ (B : Nat -> Matrix (Fin 2) (Fin 2) Real), ∀ (b : Nat
        -> Fin 2 -> Real), ∀ (u : Nat -> IntegerLatticeFunction), ∀ (M : Real), (0 <= M) →
        ((forall i j,
      Filter.Tendsto (fun k => B k i j) Filter.atTop (nhds (A i j))) → ((forall k, (B k).IsSymm)
          → ((forall k i, abs (b k i) <= 1) → ((forall k, u k 0 = 0) → ((forall k x,
          FourNeighborLaplacian (u k) x <= 1) → ((forall k x, LatticeQuadraticForm (B k) x +
      dotProduct (b k) ![(x.re : Real), (x.im : Real)] <= (u k x : Real)) → ((forall k, 1 -
          Matrix.trace (B k) <= M) → (exists phi : Nat -> Nat, StrictMono phi /\
      exists bInf : Fin 2 -> Real, exists v : IntegerLatticeFunction,
        (forall i, Filter.Tendsto (fun k => b (phi k) i)
          Filter.atTop (nhds (bInf i))) /\
        (forall x, exists K, forall k, K <= k -> u (phi k) x = v x) /\
        (forall x, FourNeighborLaplacian v x <= 1) /\
        (forall x, LatticeQuadraticForm A x +
          dotProduct bInf ![(x.re : Real), (x.im : Real)] <= (v x : Real)))))))))) := by
  intro A B b u M hM hconv hBsymm hb hu0 hulap hulower htrace
-- BODY
  classical
  let w : Nat → GaussianInt → Real := fun k x =>
    (u k x : Real) - LatticeQuadraticForm (B k) x -
      dotProduct (b k) ![(x.re : Real), (x.im : Real)]
  have hw0 : ∀ k, w k 0 = 0 := DiagonalCompactnessProof.hw0 B b u hu0
  have hwpos : ∀ k x, 0 ≤ w k x := DiagonalCompactnessProof.hwpos B b u hulower
  have hwl : ∀ k x, RealFourNeighborLaplacian (w k) x ≤ M := DiagonalCompactnessProof.hwl B b u M
      hBsymm hulap htrace
  have hwb : ∀ k x, w k x ≤
      (4 : Real) ^ (x.re.natAbs + x.im.natAbs) * (0 : Real) +
        M * (((4 : Real) ^ (x.re.natAbs + x.im.natAbs) - 1) / 3) := DiagonalCompactnessProof.hwb
            B b u M hw0 hwpos hwl
  have hentry : ∀ i j : Fin 2, ∃ lo hi : Real, ∀ k,
      lo ≤ B k i j ∧ B k i j ≤ hi := DiagonalCompactnessProof.hentry A B hconv
  have hub : ∀ x, ∃ C : Real, ∀ k, |(u k x : Real)| ≤ C := DiagonalCompactnessProof.hub B b u M
      hb hwpos hwb hentry
  let : Encodable GaussianInt := Encodable.ofEquiv (Int × Int)
    { toFun := fun z => (z.re, z.im)
      invFun := fun p => ⟨p.1, p.2⟩
      left_inv := by intro z; cases z; rfl
      right_inv := by intro p; cases p; rfl }
  let enumerate : Nat → GaussianInt := fun n =>
    (Encodable.decode n).getD 0
  have enumerate_surj : ∀ x : GaussianInt, ∃ n, enumerate n = x :=
      DiagonalCompactnessProof.enumerate_surj (this := this)
  have refineFiber : ∀ x : GaussianInt, ∀ s : Set Nat, s.Infinite →
      ∃ t : Set Nat, t ⊆ s ∧ t.Infinite ∧ ∃ z : Int, ∀ k ∈ t, u k x = z :=
          DiagonalCompactnessProof.refineFiber u hub
  let next (n : Nat) (s : Set Nat) (hs : s.Infinite) : Set Nat :=
    Classical.choose (refineFiber (enumerate n) s hs)
  have next_spec (n : Nat) (s : Set Nat) (hs : s.Infinite) :
      next n s hs ⊆ s ∧ (next n s hs).Infinite ∧
        ∃ z, ∀ k ∈ next n s hs, u k (enumerate n) = z :=
    Classical.choose_spec (refineFiber (enumerate n) s hs)
  let good : Type := {s : Set Nat // s.Infinite}
  let seq : Nat → good := Nat.rec ⟨Set.univ, Set.infinite_univ⟩
    (fun n q => ⟨next n q.1 q.2, (next_spec n q.1 q.2).2.1⟩)
  have seq_step (n : Nat) : seq (n + 1) =
      ⟨next n (seq n).1 (seq n).2, (next_spec n (seq n).1 (seq n).2).2.1⟩ :=
          DiagonalCompactnessProof.seq_step u (this := this) refineFiber next_spec n
  have seq_nested (m n : Nat) (hmn : m ≤ n) : (seq n).1 ⊆ (seq m).1 :=
      DiagonalCompactnessProof.seq_nested u (this := this) refineFiber next_spec m n hmn
  let first : Nat := Classical.choose (Set.Infinite.exists_gt (seq 0).2 0)
  have first_spec : first ∈ (seq 0).1 ∧ 0 < first :=
    Classical.choose_spec (Set.Infinite.exists_gt (seq 0).2 0)
  let phi : Nat → Nat := Nat.rec first
    (fun n p => Classical.choose (Set.Infinite.exists_gt (seq (n + 1)).2 p))
  have phi_spec (n : Nat) : phi n ∈ (seq n).1 := DiagonalCompactnessProof.phi_spec u (this :=
      this) refineFiber next_spec first_spec n
  have phi_mono : StrictMono phi := DiagonalCompactnessProof.phi_mono u (this := this)
      refineFiber next_spec
  have boundedSubsequence : ∀ f : Nat → Real, (∀ n, -1 ≤ f n ∧ f n ≤ 1) →
      ∃ q : Nat → Nat, StrictMono q ∧ ∃ c : Real,
        Filter.Tendsto (fun n => f (q n)) Filter.atTop (nhds c) :=
            DiagonalCompactnessProof.boundedSubsequence
  obtain ⟨q0, hq0, c0, hc0⟩ := boundedSubsequence (fun n => b (phi n) 0) (by
    intro n
    have h := hb (phi n) 0
    rw [abs_le] at h
    exact h)
  obtain ⟨q1, hq1, c1, hc1⟩ := boundedSubsequence (fun n => b (phi (q0 n)) 1) (by
    intro n
    have h := hb (phi (q0 n)) 1
    rw [abs_le] at h
    exact h)
  let psi : Nat → Nat := q0 ∘ q1
  have hpsi : StrictMono psi := hq0.comp hq1
  have hpsi_ge : ∀ n, n ≤ psi n := DiagonalCompactnessProof.hpsi_ge q0 q1 hpsi
  let bInf : Fin 2 → Real := ![c0, c1]
  let output : Nat → Nat := phi ∘ psi
  have output_mono : StrictMono output := phi_mono.comp hpsi
  let index : GaussianInt → Nat := fun x => Classical.choose (enumerate_surj x)
  have index_spec (x : GaussianInt) : enumerate (index x) = x :=
    Classical.choose_spec (enumerate_surj x)
  have fiber_spec (x : GaussianInt) : ∃ z : Int, ∀ k ∈ next (index x)
      (seq (index x)).1 (seq (index x)).2, u k x = z := DiagonalCompactnessProof.fiber_spec u
          (this := this) enumerate_surj refineFiber next_spec index_spec x
  let v : IntegerLatticeFunction := fun x => Classical.choose (fiber_spec x)
  have v_spec (x : GaussianInt) : ∀ k ∈ next (index x)
      (seq (index x)).1 (seq (index x)).2, u k x = v x :=
    Classical.choose_spec (fiber_spec x)
  have eventual_eq (x : GaussianInt) : ∃ K, ∀ k, K ≤ k → u (output k) x = v x :=
      DiagonalCompactnessProof.eventual_eq u (this := this) enumerate_surj refineFiber next_spec
      seq_step seq_nested phi_spec q0 q1 hpsi_ge fiber_spec v_spec x
  refine ⟨output, output_mono, bInf, v, ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · simpa [output, psi, bInf, Function.comp_def] using hc0.comp hq1.tendsto_atTop
    · simpa [output, psi, bInf, Function.comp_def] using hc1
  · exact eventual_eq
  · intro x
    obtain ⟨K0, h0⟩ := eventual_eq x
    obtain ⟨K1, h1⟩ := eventual_eq (x + 1)
    obtain ⟨K2, h2⟩ := eventual_eq (x - 1)
    obtain ⟨K3, h3⟩ := eventual_eq (x + ⟨0, 1⟩)
    obtain ⟨K4, h4⟩ := eventual_eq (x - ⟨0, 1⟩)
    let K := max (max (max K0 K1) (max K2 K3)) K4
    have hu := hulap (output K) x
    have e0 := h0 K (by dsimp [K]; omega)
    have e1 := h1 K (by dsimp [K]; omega)
    have e2 := h2 K (by dsimp [K]; omega)
    have e3 := h3 K (by dsimp [K]; omega)
    have e4 := h4 K (by dsimp [K]; omega)
    simp only [FourNeighborLaplacian, e1, e2, Int.reduceNeg, e3, e4, e0, tsub_le_iff_right,
        ge_iff_le] at hu ⊢
    exact hu
  · intro x
    have h00 := (hconv 0 0).comp output_mono.tendsto_atTop
    have h01 := (hconv 0 1).comp output_mono.tendsto_atTop
    have h10 := (hconv 1 0).comp output_mono.tendsto_atTop
    have h11 := (hconv 1 1).comp output_mono.tendsto_atTop
    have hb0 := hc0.comp hq1.tendsto_atTop
    have hb1 := hc1
    have hlim : Filter.Tendsto
       (fun k => LatticeQuadraticForm (B (output k)) x +
         dotProduct (b (output k)) ![(x.re : Real), (x.im : Real)])
       Filter.atTop (nhds (LatticeQuadraticForm A x +
         dotProduct bInf ![(x.re : Real), (x.im : Real)])) := DiagonalCompactnessProof.hlim A B b
             u (this := this) refineFiber next_spec q0 c0 q1 c1 x h00 h01 h10 h11 hb0 hb1
    apply le_of_tendsto hlim
    obtain ⟨K, hK⟩ := eventual_eq x
    filter_upwards [Filter.eventually_ge_atTop K] with k hk
    have he := hK k hk
    simpa [he] using hulower (output k) x

end ApollonianSuperharmonic

end
