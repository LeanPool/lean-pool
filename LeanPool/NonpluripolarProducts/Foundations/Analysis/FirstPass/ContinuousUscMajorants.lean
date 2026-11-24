/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import Mathlib.Topology.Algebra.MetricSpace.Lipschitz
public import Mathlib.Topology.Instances.EReal.Lemmas
public import Mathlib.Topology.Semicontinuity.Basic
public import Mathlib.Tactic

/-!
# Continuous majorants of extended-real upper semicontinuous functions

This file gives an explicit metric sup-convolution.  If `u` has no value `⊤`
on a set `K` and is bounded above there by the real number `C`, put

`uₙ(x) = sup_{y ∈ K} (max(u(y), C - n) - n * dist(x,y))`.

The maximum is taken in `EReal` before applying `toReal`; consequently a pole
is replaced by `C - n`, rather than by the accidental value `0`.  The functions
`uₙ` are Lipschitz, decrease in `n`, majorize `u` on `K`, and their pointwise
infimum on `K` is exactly `u`.  The last assertion uses only upper
semicontinuity and the metric neighbourhood basis.  Compactness is needed only
by the final wrapper, which obtains the uniform real upper bound.
-/

@[expose] public section

noncomputable section

open Set Filter Metric TopologicalSpace
open scoped Topology NNReal

namespace SGPT.Foundations.Analysis.FirstPass

variable {X : Type*} [PseudoMetricSpace X]

/-- A finite real truncation of an extended-real value, with a moving floor. -/
def uscFloor (C : ℝ) (n : ℕ) (a : EReal) : ℝ :=
  (max a (((C - (n : ℝ)) : ℝ) : EReal)).toReal

theorem coe_uscFloor {C : ℝ} {n : ℕ} {a : EReal} (ha : a ≠ ⊤) :
    ((uscFloor C n a : ℝ) : EReal) =
      max a (((C - (n : ℝ)) : ℝ) : EReal) := by
  apply EReal.coe_toReal
  · exact ne_of_lt <| max_lt (lt_top_iff_ne_top.mpr ha) (EReal.coe_lt_top _)
  · exact ne_of_gt <|
      (EReal.bot_lt_coe (C - (n : ℝ))).trans_le (le_max_right _ _)

theorem le_coe_uscFloor {C : ℝ} {n : ℕ} {a : EReal} (ha : a ≠ ⊤) :
    a ≤ (uscFloor C n a : EReal) := by
  rw [coe_uscFloor ha]
  exact le_max_left _ _

theorem uscFloor_le {C : ℝ} {n : ℕ} {a : EReal} (ha : a ≠ ⊤)
    (haC : a ≤ (C : EReal)) : uscFloor C n a ≤ C := by
  apply EReal.coe_le_coe_iff.mp
  rw [coe_uscFloor ha]
  exact max_le haC <| EReal.coe_le_coe_iff.mpr <| by
    exact sub_le_self C (Nat.cast_nonneg n)

theorem uscFloor_antitone {C : ℝ} {a : EReal} (ha : a ≠ ⊤) :
    Antitone (fun n : ℕ => uscFloor C n a) := by
  intro n m hnm
  apply EReal.coe_le_coe_iff.mp
  rw [coe_uscFloor ha, coe_uscFloor ha]
  apply max_le_max le_rfl
  exact EReal.coe_le_coe_iff.mpr <| sub_le_sub_left (Nat.cast_le.mpr hnm) C

/-- The explicit distance-penalized supremum over `K`. -/
def uscSupConvolution (K : Set X) (u : X → EReal) (C : ℝ) (n : ℕ) (x : X) : ℝ :=
  sSup (Set.range fun y : K =>
    uscFloor C n (u y) - (n : ℝ) * dist x y)

private theorem uscSupConvolution_range_bddAbove {K : Set X} {u : X → EReal}
    {C : ℝ} (htop : ∀ y ∈ K, u y ≠ ⊤) (hC : ∀ y ∈ K, u y ≤ (C : EReal))
    (n : ℕ) (x : X) :
    BddAbove (Set.range fun y : K =>
      uscFloor C n (u y) - (n : ℝ) * dist x y) := by
  refine ⟨C, ?_⟩
  rintro _ ⟨y, rfl⟩
  have hfloor := uscFloor_le (n := n) (htop y y.property) (hC y y.property)
  have hpenalty : 0 ≤ (n : ℝ) * dist x y :=
    mul_nonneg (Nat.cast_nonneg n) dist_nonneg
  linarith

private theorem uscSupConvolution_range_nonempty {K : Set X} {u : X → EReal}
    {C : ℝ} (hne : K.Nonempty) (n : ℕ) (x : X) :
    (Set.range fun y : K =>
      uscFloor C n (u y) - (n : ℝ) * dist x y).Nonempty := by
  obtain ⟨y, hy⟩ := hne
  exact ⟨uscFloor C n (u y) - (n : ℝ) * dist x y, ⟨⟨y, hy⟩, rfl⟩⟩

theorem uscSupConvolution_le {K : Set X} {u : X → EReal} {C : ℝ}
    (hne : K.Nonempty) (htop : ∀ y ∈ K, u y ≠ ⊤)
    (hC : ∀ y ∈ K, u y ≤ (C : EReal)) (n : ℕ) (x : X) :
    uscSupConvolution K u C n x ≤ C := by
  apply csSup_le (uscSupConvolution_range_nonempty hne n x)
  rintro _ ⟨y, rfl⟩
  have hfloor := uscFloor_le (n := n) (htop y y.property) (hC y y.property)
  have hpenalty : 0 ≤ (n : ℝ) * dist x y :=
    mul_nonneg (Nat.cast_nonneg n) dist_nonneg
  linarith

theorem uscSupConvolution_lipschitz {K : Set X} {u : X → EReal} {C : ℝ}
    (hne : K.Nonempty) (htop : ∀ y ∈ K, u y ≠ ⊤)
    (hC : ∀ y ∈ K, u y ≤ (C : EReal))
    (n : ℕ) :
    LipschitzWith (n : ℝ≥0) (uscSupConvolution K u C n) := by
  apply LipschitzWith.of_dist_le_mul
  intro x x'
  have hbdd (z : X) := uscSupConvolution_range_bddAbove htop hC n z
  have hforward : uscSupConvolution K u C n x ≤
      uscSupConvolution K u C n x' + (n : ℝ) * dist x x' := by
    apply csSup_le (uscSupConvolution_range_nonempty hne n x)
    rintro _ ⟨y, rfl⟩
    have hterm : uscFloor C n (u y) - (n : ℝ) * dist x' y ≤
        uscSupConvolution K u C n x' :=
      le_csSup (hbdd x') (Set.mem_range_self y)
    have htriangle : dist x' y ≤ dist x x' + dist x y := by
      simpa [dist_comm x' x] using dist_triangle x' x y
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    nlinarith
  have hbackward : uscSupConvolution K u C n x' ≤
      uscSupConvolution K u C n x + (n : ℝ) * dist x x' := by
    apply csSup_le (uscSupConvolution_range_nonempty hne n x')
    rintro _ ⟨y, rfl⟩
    have hterm : uscFloor C n (u y) - (n : ℝ) * dist x y ≤
        uscSupConvolution K u C n x :=
      le_csSup (hbdd x) (Set.mem_range_self y)
    have htriangle : dist x y ≤ dist x x' + dist x' y :=
      dist_triangle x x' y
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    nlinarith
  rw [Real.dist_eq]
  simp only [NNReal.coe_natCast]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem continuous_uscSupConvolution {K : Set X} {u : X → EReal} {C : ℝ}
    (hne : K.Nonempty) (htop : ∀ y ∈ K, u y ≠ ⊤)
    (hC : ∀ y ∈ K, u y ≤ (C : EReal))
    (n : ℕ) : Continuous (uscSupConvolution K u C n) :=
  (uscSupConvolution_lipschitz hne htop hC n).continuous

theorem le_coe_uscSupConvolution {K : Set X} {u : X → EReal} {C : ℝ}
    (_hne : K.Nonempty) (htop : ∀ y ∈ K, u y ≠ ⊤)
    (hC : ∀ y ∈ K, u y ≤ (C : EReal)) (n : ℕ) {x : X} (hx : x ∈ K) :
    u x ≤ (uscSupConvolution K u C n x : EReal) := by
  let y : K := ⟨x, hx⟩
  have hterm : uscFloor C n (u x) ≤ uscSupConvolution K u C n x := by
    have := le_csSup (uscSupConvolution_range_bddAbove htop hC n x)
      (Set.mem_range_self y)
    simpa [uscSupConvolution, y] using this
  exact (le_coe_uscFloor (htop x hx)).trans <|
    EReal.coe_le_coe_iff.mpr hterm

theorem uscSupConvolution_antitone {K : Set X} {u : X → EReal} {C : ℝ}
    (hne : K.Nonempty) (htop : ∀ y ∈ K, u y ≠ ⊤)
    (hC : ∀ y ∈ K, u y ≤ (C : EReal)) (x : X) :
    Antitone (fun n : ℕ => uscSupConvolution K u C n x) := by
  intro n m hnm
  apply csSup_le (uscSupConvolution_range_nonempty hne m x)
  rintro _ ⟨y, rfl⟩
  have hterm : uscFloor C n (u y) - (n : ℝ) * dist x y ≤
      uscSupConvolution K u C n x :=
    le_csSup (uscSupConvolution_range_bddAbove htop hC n x)
      (Set.mem_range_self y)
  have hfloor := (uscFloor_antitone (C := C) (htop y y.property)) hnm
  have hcast : (n : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr hnm
  have hdist : 0 ≤ dist x y := dist_nonneg
  change uscFloor C m (u y) - (m : ℝ) * dist x y ≤
    uscSupConvolution K u C n x
  nlinarith

private theorem exists_uscSupConvolution_le {K : Set X} {u : X → EReal} {C A : ℝ}
    (hne : K.Nonempty) (hu : UpperSemicontinuousOn u K)
    (htop : ∀ y ∈ K, u y ≠ ⊤) (hC : ∀ y ∈ K, u y ≤ (C : EReal))
    {x : X} (hx : x ∈ K) (huxA : u x < (A : EReal)) :
    ∃ n : ℕ, uscSupConvolution K u C n x ≤ A := by
  obtain ⟨δ, hδ, hnear⟩ := Metric.mem_nhdsWithin_iff.mp (hu x hx (A : EReal) huxA)
  obtain ⟨n, hn⟩ := exists_nat_gt (max (C - A) ((C - A) / δ))
  have hn₁ : C - (n : ℝ) < A := by
    have := (le_max_left (C - A) ((C - A) / δ)).trans_lt hn
    linarith
  have hn₂ : C - A < (n : ℝ) * δ := by
    apply (div_lt_iff₀ hδ).mp
    exact (le_max_right (C - A) ((C - A) / δ)).trans_lt hn
  refine ⟨n, ?_⟩
  apply csSup_le (uscSupConvolution_range_nonempty hne n x)
  rintro _ ⟨y, rfl⟩
  by_cases hy : dist x y < δ
  · have hyball : (y : X) ∈ ball x δ := by
      simpa [mem_ball, dist_comm] using hy
    have huyA : u y < (A : EReal) := hnear ⟨hyball, y.property⟩
    have hfloor : uscFloor C n (u y) < A := by
      rw [← EReal.coe_lt_coe_iff, coe_uscFloor (htop y y.property)]
      exact max_lt huyA (EReal.coe_lt_coe_iff.mpr hn₁)
    have hpenalty : 0 ≤ (n : ℝ) * dist x y :=
      mul_nonneg (Nat.cast_nonneg n) dist_nonneg
    linarith
  · have hfloor := uscFloor_le (n := n) (htop y y.property) (hC y y.property)
    have hfar : δ ≤ dist x y := le_of_not_gt hy
    have hnnonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hmul : (n : ℝ) * δ ≤ (n : ℝ) * dist x y :=
      mul_le_mul_of_nonneg_left hfar hnnonneg
    linarith

theorem iInf_coe_uscSupConvolution {K : Set X} {u : X → EReal} {C : ℝ}
    (hne : K.Nonempty) (hu : UpperSemicontinuousOn u K)
    (htop : ∀ y ∈ K, u y ≠ ⊤) (hC : ∀ y ∈ K, u y ≤ (C : EReal))
    {x : X} (hx : x ∈ K) :
    (⨅ n : ℕ, (uscSupConvolution K u C n x : EReal)) = u x := by
  apply le_antisymm
  · apply le_of_forall_gt
    intro b hub
    obtain ⟨A, huA, hAb⟩ := EReal.exists_between_coe_real hub
    obtain ⟨n, hn⟩ := exists_uscSupConvolution_le hne hu htop hC hx huA
    exact (iInf_le (fun k : ℕ => (uscSupConvolution K u C k x : EReal)) n).trans_lt <|
      (EReal.coe_le_coe_iff.mpr hn).trans_lt hAb
  · exact le_iInf fun n => le_coe_uscSupConvolution hne htop hC n hx

/-- A compact upper-semicontinuous `EReal` function without `⊤` admits a
decreasing sequence of continuous real-valued majorants.  Its pointwise
`EReal` infimum on the compact set is the original function, including at
points where the function is `⊥`. -/
theorem exists_continuous_antitone_majorants_on_compact {K : Set X}
    (hK : IsCompact K) (hne : K.Nonempty) {u : X → EReal}
    (hu : UpperSemicontinuousOn u K) (htop : ∀ x ∈ K, u x ≠ ⊤) :
    ∃ (C : ℝ) (g : ℕ → X → ℝ),
      (∀ n, Continuous (g n)) ∧
      (∀ n x, x ∈ K → u x ≤ (g n x : EReal)) ∧
      (∀ n x, g n x ≤ C) ∧
      (∀ x, Antitone fun n => g n x) ∧
      (∀ x, x ∈ K → (⨅ n : ℕ, (g n x : EReal)) = u x) := by
  obtain ⟨y, hy, hmax⟩ := hu.exists_isMaxOn hne hK
  obtain ⟨C, hyC, _⟩ := EReal.exists_rat_btwn_of_lt
    (lt_top_iff_ne_top.mpr (htop y hy))
  have hC : ∀ x ∈ K, u x ≤ (((C : ℝ) : ℝ) : EReal) :=
    fun x hx => (hmax hx).trans hyC.le
  refine ⟨(C : ℝ), uscSupConvolution K u (C : ℝ), ?_, ?_, ?_, ?_, ?_⟩
  · exact fun n => continuous_uscSupConvolution hne htop hC n
  · exact fun n x hx => le_coe_uscSupConvolution hne htop hC n hx
  · exact fun n x => uscSupConvolution_le hne htop hC n x
  · exact fun x => uscSupConvolution_antitone hne htop hC x
  · exact fun x hx => iInf_coe_uscSupConvolution hne hu htop hC hx

end SGPT.Foundations.Analysis.FirstPass
