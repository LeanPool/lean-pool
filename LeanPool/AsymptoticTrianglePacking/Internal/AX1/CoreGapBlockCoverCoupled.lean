/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

/-
# Nibble — the **coupled** block-allocation residual

`Nibble.AX1.BlockCoverResidualFine` (`Nibble.CoreGapBlockCover`) asks for the block family at
*every* regularity scale `ε₁` and *every* relative block size `α ≤ δ/2` at once.  That is more than
the reduction to AX1 ever uses, and more than a nibble construction can deliver: a weighted nibble
in the hypergraph of grid cells only produces a near-perfect matching when the grid is *large*, i.e.
when the number of clusters `≈ 1/ε₁` and the number of blocks per cluster `≈ δ/α` are both large in
terms of the accuracy `ε`.

This file states the residual in the coupled form the construction can actually meet, and redoes
the reduction to AX1 with the coupling threaded through:

* `Nibble.AX1.BlockCoverResidualCoupled` — for every accuracy `ε`, density threshold `δ ≤ ε`, block
  uniformity scale `ε₂` and scale floor `T₀`, there is a regularity window `ε₁ ≤ ε₁₀(ε, δ, ε₂, T₀)`
  inside which the residual chooses its own relative block size `α` (only asked to satisfy
  `ε₁/8 ≤ α`, `2α ≤ 1` and `(ε₁/8)/α ≤ ε₂`, the three inequalities the design needs) and then
  produces the family of block sub-triples.
* `Nibble.AX1.subTripleDesignLocalResidual_of_blockCoverCoupled`,
  `Nibble.AX1.ax1_of_blockCoverCoupled` — the reduction.  It is the reduction of
  `Nibble.AX1.subTripleDesignLocalResidual_of_blockCoverFine` with the two parameters the residual
  now fixes — the regularity scale `ε₁` and the relative block size `α` — read off from the
  residual instead of being chosen in advance; the only inequalities used about them are the ones
  the coupled residual guarantees.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.CoreGapBlockShape
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.GridLineDesign
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.CoreGapClusterCapacity
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.CoreGapGridLocalResidual
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.TripleEdgesThree
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.CoreGapBlockCover

/-! # CoreGapBlockCoverCoupled -/

@[expose] public section

open Finset SimpleGraph Hypergraph Nibble.YusterE

namespace Nibble.AX1

/-! ### The arithmetic of the construction

The block scale `τ` is large (`8 ≤ τ·δ`), the blocks have size between `¾τδ` and `⁵⁄₄τ`, and the
regularity scale `ε₁` is small compared with `δ`, `μ₂` and `η`.  The four lemmas below are the only
computations the reduction needs; they are stated in isolation to keep the context small. -/

/-- The blocks have size between `¾·τδ` and `⁵⁄₄·τ`. -/
private theorem block_size_bounds {τ δ s dens : ℝ} (hτ : 0 < τ) (_hδ : 0 < δ) (_hδ1 : δ ≤ 1)
    (hτδ : 8 ≤ τ * δ) (h1 : δ ≤ dens) (h2 : dens ≤ 1) (habs : |s - τ * dens| ≤ 1) :
    3 / 4 * (τ * δ) ≤ s ∧ s ≤ 5 / 4 * τ := by
  rw [abs_le] at habs
  have h3 : τ * δ ≤ τ * dens := mul_le_mul_of_nonneg_left h1 hτ.le
  have h4 : τ * dens ≤ τ := by nlinarith
  have h6 : τ * δ ≤ τ := by nlinarith
  exact ⟨by linarith [habs.1], by linarith [habs.2]⟩

/-- The area and the support of a sub-triple, in terms of the scale. -/
private theorem area_bounds {τ δ a b c : ℝ} (hτ : 0 < τ) (_hδ : 0 < δ) (hτδ : 8 ≤ τ * δ)
    (ha : 3 / 4 * (τ * δ) ≤ a) (ha' : a ≤ 5 / 4 * τ)
    (hb : 3 / 4 * (τ * δ) ≤ b) (hb' : b ≤ 5 / 4 * τ)
    (hc : 3 / 4 * (τ * δ) ≤ c) (hc' : c ≤ 5 / 4 * τ) :
    0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ a * b + a * c + b * c ≤ 5 * τ ^ 2 ∧
      0 ≤ a * b + a * c + b * c ∧ a + b + c ≤ 4 * τ ∧ 0 ≤ a + b + c := by
  have ha0 : 0 ≤ a := by nlinarith
  have hb0 : 0 ≤ b := by nlinarith
  have hc0 : 0 ≤ c := by nlinarith
  refine ⟨ha0, hb0, hc0, by nlinarith, by positivity, by linarith, by linarith⟩

/-- The `Elo` of a sub-triple is at least a quarter of `τ²δ³`. -/
private theorem elo_lower {τ δ ε₁ a b c dAB dAC dBC : ℝ} (hτ : 0 < τ) (hδ : 0 < δ) (_hδ1 : δ ≤ 1)
    (_hε₁0 : 0 < ε₁) (hε₁b : ε₁ ≤ δ / 2) (hx : δ - ε₁ / 8 ≤ dAB)
    (hAC0 : 0 ≤ dAC) (hBC0 : 0 ≤ dBC)
    (ha : 3 / 4 * (τ * δ) ≤ a) (hb : 3 / 4 * (τ * δ) ≤ b) (hc0 : 0 ≤ c) (ha0 : 0 ≤ a)
    (hb0 : 0 ≤ b) :
    1 / 4 * (τ ^ 2 * δ ^ 3) ≤ dAB * a * b + dAC * a * c + dBC * b * c := by
  have hAB : 15 / 16 * δ ≤ dAB := by linarith
  have hnn : (0:ℝ) ≤ 3 / 4 * (τ * δ) := by positivity
  have hab : 9 / 16 * (τ ^ 2 * δ ^ 2) ≤ a * b := by
    linarith only [mul_le_mul ha hb hnn ha0]
  have hmain : 1 / 4 * (τ ^ 2 * δ ^ 3) ≤ dAB * a * b := by
    have h1 : (15 / 16 * δ) * (9 / 16 * (τ ^ 2 * δ ^ 2)) ≤ dAB * (a * b) :=
      mul_le_mul hAB hab (by positivity) (le_trans (by positivity) hAB)
    have h2 : dAB * a * b = dAB * (a * b) := by ring
    have h3 : (15 / 16 * δ) * (9 / 16 * (τ ^ 2 * δ ^ 2)) = 135 / 256 * (τ ^ 2 * δ ^ 3) := by ring
    have h4 : (0:ℝ) ≤ τ ^ 2 * δ ^ 3 := by positivity
    rw [h2]
    rw [h3] at h1
    linarith
  have h2 : 0 ≤ dAC * a * c := by positivity
  have h3 : 0 ≤ dBC * b * c := by positivity
  linarith

/-- The product of three densities at least `δ` is at least `δ³`. -/
private theorem dens_prod_lower {δ x y z : ℝ} (hδ : 0 < δ) (hx : δ ≤ x) (hy : δ ≤ y) (hz : δ ≤ z) :
    δ ^ 3 ≤ x * y * z := by
  have h1 : δ * δ ≤ x * y := mul_le_mul hx hy hδ.le (by linarith)
  have h2 : (δ * δ) * δ ≤ (x * y) * z :=
    mul_le_mul h1 hz hδ.le (le_trans (by positivity : (0:ℝ) ≤ δ * δ) h1)
  linarith only [h2]

/-- The triangle-degree scale of a sub-triple is above the floor `d₀`. -/
private theorem d_lower {τ δ d₀ x y z : ℝ} (hτ : 0 < τ) (hδ : 0 < δ) (hx : δ ≤ x) (hy : δ ≤ y)
    (hz : δ ≤ z) (hd₀ : d₀ ≤ τ * δ ^ 3) : d₀ ≤ τ * (x * y * z) :=
  le_trans hd₀ (mul_le_mul_of_nonneg_left (dens_prod_lower hδ hx hy hz) hτ.le)

/-- The triangle-degree scale of a sub-triple is nonnegative. -/
private theorem d_nonneg {τ δ x y z : ℝ} (hτ : 0 < τ) (hδ : 0 < δ) (hx : δ ≤ x) (hy : δ ≤ y)
    (hz : δ ≤ z) : 0 ≤ τ * (x * y * z) := by
  have h := dens_prod_lower hδ hx hy hz
  have h0 : (0:ℝ) < δ ^ 3 := by positivity
  exact mul_nonneg hτ.le (by linarith)

/-- The pruning slack `t` is at most half of `(μ - μ₂)` times the triangle-degree scale. -/
private theorem slack_bound {μ μ₂ τ δ x y z : ℝ} (hτ : 0 < τ) (hδ : 0 < δ)
    (hx : δ ≤ x) (hy : δ ≤ y) (hz : δ ≤ z) (hμ₂ : 2 * μ₂ ≤ μ) (hμ₂'₀ : 0 < μ₂) :
    2 * ((μ - μ₂) * τ * δ ^ 3 / 2) ≤ (μ - μ₂) * (τ * (x * y * z)) := by
  have h : τ * δ ^ 3 ≤ τ * (x * y * z) :=
    mul_le_mul_of_nonneg_left (dens_prod_lower hδ hx hy hz) hτ.le
  have hd : (0:ℝ) ≤ μ - μ₂ := by linarith
  linarith only [mul_le_mul_of_nonneg_left h hd]

/-- The pruning slack `t = (μ - μ₂)τδ³/2` is positive. -/
private theorem t_pos {μ μ₂ τ δ : ℝ} (hτ : 0 < τ) (hδ3 : 0 < δ ^ 3) (hμ₂ : 0 < μ₂)
    (h : 2 * μ₂ ≤ μ) : 0 < (μ - μ₂) * τ * δ ^ 3 / 2 := by
  nlinarith [mul_pos hτ hδ3]

/-- The pruning slack `t = (μ - μ₂)τδ³/2` is at least `μ₂τδ³/2`. -/
private theorem t_lower {μ μ₂ τ δ : ℝ} (hτ : 0 < τ) (hδ3 : 0 < δ ^ 3) (h : 2 * μ₂ ≤ μ) :
    μ₂ * τ * δ ^ 3 / 2 ≤ (μ - μ₂) * τ * δ ^ 3 / 2 := by
  nlinarith [mul_pos hτ hδ3]

/-- One term of the covering estimate: replacing the cluster densities by the block densities and
subtracting the exceptional budget costs at most `17ε₁/24` times the area. -/
private theorem cover_step {ε₁ ε₂ dAB dAC dBC eAB eAC eBC a b c : ℝ}
    (h1 : |eAB - dAB| ≤ ε₁ / 8) (h2 : |eAC - dAC| ≤ ε₁ / 8) (h3 : |eBC - dBC| ≤ ε₁ / 8)
    (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (hc0 : 0 ≤ c) :
    (dAB * a * b + dAC * a * c + dBC * b * c) / 3
        - (ε₁ / 8 + 4 * ε₂) / 3 * (a * b + a * c + b * c)
      ≤ (eAB * a * b + eAC * a * c + eBC * b * c
          - 4 * ε₂ * (a * b + a * c + b * c)) / 3 := by
  have k1 : -(ε₁ / 8) ≤ eAB - dAB := by linarith only [(abs_le.mp h1).1]
  have k2 : -(ε₁ / 8) ≤ eAC - dAC := by linarith only [(abs_le.mp h2).1]
  have k3 : -(ε₁ / 8) ≤ eBC - dBC := by linarith only [(abs_le.mp h3).1]
  have hab : (0:ℝ) ≤ a * b := mul_nonneg ha0 hb0
  have hac : (0:ℝ) ≤ a * c := mul_nonneg ha0 hc0
  have hbc : (0:ℝ) ≤ b * c := mul_nonneg hb0 hc0
  have m1 : -(ε₁ / 8) * (a * b) ≤ (eAB - dAB) * (a * b) :=
    mul_le_mul_of_nonneg_right k1 hab
  have m2 : -(ε₁ / 8) * (a * c) ≤ (eAC - dAC) * (a * c) :=
    mul_le_mul_of_nonneg_right k2 hac
  have m3 : -(ε₁ / 8) * (b * c) ≤ (eBC - dBC) * (b * c) :=
    mul_le_mul_of_nonneg_right k3 hbc
  linarith only [m1, m2, m3]

/-- The accumulated covering loss is absorbed by half of the accuracy. -/
private theorem cover_tail {ε K N : ℝ} (h : K ≤ ε) (hN : 0 ≤ N) :
    K * (N / 2) ≤ ε / 2 * N := by
  have := mul_le_mul_of_nonneg_right h hN
  linarith only [this]

/-- The block uniformity scale `ε₂ = (ε₁/8)/α` at `α = δ/2`, bounded from a bound on `ε₁`. -/
private theorem eps2_bound {x δ B : ℝ} (hδ : 0 < δ) (h : x ≤ B * δ) : x / (4 * δ) ≤ B / 4 := by
  rw [div_le_iff₀ (by positivity)]
  nlinarith

/-- Multiplying a nonnegative quantity by `δ ≤ 1` only decreases it. -/
private theorem mul_delta_le {B δ : ℝ} (hB : 0 ≤ B) (hδ1 : δ ≤ 1) (_hδ0 : 0 ≤ δ) : B * δ ≤ B := by
  nlinarith

/-- The block scale is large: `2 ≤ τ·μ₂δ³` and `μ₂ ≤ 1` give `2 ≤ τδ³`. -/
private theorem tau_delta3_lower {τ δ μ₂ : ℝ} (hτ : 0 < τ) (hδ3 : 0 < δ ^ 3) (hμ₂1 : μ₂ ≤ 1)
    (h : 2 ≤ τ * (μ₂ * δ ^ 3)) : 2 ≤ τ * δ ^ 3 := by
  nlinarith [mul_le_mul_of_nonneg_left hμ₂1 (le_of_lt (mul_pos hτ hδ3))]

/-- The block scale is large: `2 ≤ τδ³` and `δ ≤ 1/2` give `8 ≤ τδ`. -/
private theorem tau_delta_lower {τ δ : ℝ} (hτ : 0 < τ) (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2)
    (h : 2 ≤ τ * δ ^ 3) : 8 ≤ τ * δ := by
  have hsq : δ ^ 2 ≤ 1 / 4 := by nlinarith
  have hnn : 0 ≤ τ * δ := mul_nonneg hτ.le hδ.le
  nlinarith only [h, hsq, hnn]

/-- The exceptional-edge clause of the design, as an inequality between real numbers. -/
private theorem exc_bound {ε₂ δ μ₂ η τ t S sup Elo : ℝ}
    (hτ : 0 < τ) (hδ : 0 < δ) (hμ₂0 : 0 < μ₂) (hη : 0 < η)
    (hε₂0 : 0 < ε₂) (hε₂c : ε₂ ≤ η * μ₂ * δ ^ 6 / 2560) (hε₂d : ε₂ ≤ δ ^ 3 / 160)
    (hS : S ≤ 5 * τ ^ 2) (hsup : sup ≤ 4 * τ) (hsup0 : 0 ≤ sup)
    (hElo : 1 / 4 * (τ ^ 2 * δ ^ 3) ≤ Elo) (ht : μ₂ * τ * δ ^ 3 / 2 ≤ t) (ht0 : 0 < t) :
    2 * (4 * ε₂ * S) / t * sup ≤ η * (Elo - 4 * ε₂ * S) := by
  rw [div_mul_eq_mul_div, div_le_iff₀ ht0]
  have hτ3 : (0:ℝ) < τ ^ 3 := by positivity
  have h1 : 2 * (4 * ε₂ * S) * sup ≤ 160 * ε₂ * τ ^ 3 := by
    have hSs : S * sup ≤ (5 * τ ^ 2) * (4 * τ) := mul_le_mul hS hsup hsup0 (by positivity)
    nlinarith [hSs]
  have hbr : 1 / 8 * (τ ^ 2 * δ ^ 3) ≤ Elo - 4 * ε₂ * S := by
    have hεS : 4 * ε₂ * S ≤ 4 * (δ ^ 3 / 160) * (5 * τ ^ 2) := by nlinarith
    nlinarith [hεS]
  have h2 : η * (1 / 8 * (τ ^ 2 * δ ^ 3)) * (μ₂ * τ * δ ^ 3 / 2)
      ≤ η * (Elo - 4 * ε₂ * S) * t := by
    have hle1 : η * (1 / 8 * (τ ^ 2 * δ ^ 3)) ≤ η * (Elo - 4 * ε₂ * S) :=
      mul_le_mul_of_nonneg_left hbr hη.le
    have hnn : (0:ℝ) ≤ η * (1 / 8 * (τ ^ 2 * δ ^ 3)) := by positivity
    have hnn2 : (0:ℝ) ≤ μ₂ * τ * δ ^ 3 / 2 := by positivity
    exact mul_le_mul hle1 ht hnn2 (le_trans hnn hle1)
  have h3 : 160 * ε₂ * τ ^ 3 ≤ η * (1 / 8 * (τ ^ 2 * δ ^ 3)) * (μ₂ * τ * δ ^ 3 / 2) := by
    have hkey : 160 * ε₂ ≤ η * μ₂ * δ ^ 6 / 16 := by linarith
    linarith only [mul_le_mul_of_nonneg_right hkey hτ3.le]
  linarith
/-- **The coupled block-allocation residual.**  Given the accuracy `ε`, a density threshold
`δ ≤ ε`, the block uniformity scale `ε₂` that the caller needs and a scale floor `T₀`, the residual
names a regularity window `ε₁₀ > 0`; for every regularity scale `ε₁ ≤ ε₁₀` it then names a relative
block size `α` with `ε₁/8 ≤ α`, `2α ≤ 1` and `(ε₁/8)/α ≤ ε₂` — the three inequalities the transfer
of regularity from the clusters to the blocks needs — and, for all large enough
`(ε₁/8)`-regular equipartitions, a family of block sub-triples at that `α` with pairwise disjoint
vertex-pair rectangles carrying the fractional optimum up to `ε|V|²`.

Compared with `Nibble.AX1.BlockCoverResidualFine` the two scales `ε₁` and `α` are no longer
universally quantified independently: the residual may demand that the regularity scale be fine
(hence the number of clusters large) and may pick the relative block size itself (hence the number
of blocks per cluster large).  Both are exactly what the reduction to AX1 leaves free, which is why
`Nibble.AX1.ax1_of_blockCoverCoupled` still goes through. -/
def BlockCoverResidualCoupled : Prop :=
  ∀ ε δ ε₂ T₀ : ℝ, 0 < ε → 0 < δ → δ ≤ 1 → δ ≤ ε → 0 < ε₂ → 0 < T₀ →
  ∃ ε₁₀ : ℝ, 0 < ε₁₀ ∧
    ∀ ε₁ : ℝ, 0 < ε₁ → ε₁ ≤ ε₁₀ → ε₁ ≤ 1 →
    ∃ α : ℝ, ε₁ / 8 ≤ α ∧ 2 * α ≤ 1 ∧ ε₁ / 8 / α ≤ ε₂ ∧
    ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
      (P : Finpartition (univ : Finset V)),
      n₀ ≤ Fintype.card V →
      P.IsEquipartition →
      4 / ε₁ ≤ (P.parts.card : ℝ) →
      (P.parts.card : ℝ) ≤ ((SzemerediRegularity.bound (ε₁ / 8) ⌈4 / ε₁⌉₊ : ℕ) : ℝ) →
      P.IsUniform G (ε₁ / 8) →
      ∃ (τ : ℝ) (k : ℕ) (U W X A B C : ℕ → Finset V),
        T₀ ≤ τ ∧
        (∀ i < k, IsGridSubTriple G P (ε₁ / 8) δ α τ (U i) (W i) (X i) (A i) (B i) (C i)) ∧
        (∀ i < k, ∀ j < k, i ≠ j →
          Disjoint (tripleRect (A i) (B i) (C i)) (tripleRect (A j) (B j) (C j))) ∧
        nu3star (G.regularityReduced P (ε₁ / 8) (ε₁ / 4))
          ≤ (∑ i ∈ Finset.range k,
              ((G.edgeDensity (U i) (W i) : ℝ) * (#(A i) : ℝ) * (#(B i) : ℝ)
                + (G.edgeDensity (U i) (X i) : ℝ) * (#(A i) : ℝ) * (#(C i) : ℝ)
                + (G.edgeDensity (W i) (X i) : ℝ) * (#(B i) : ℝ) * (#(C i) : ℝ))) / 3
            + ε * (Fintype.card V : ℝ) ^ 2

theorem subTripleDesignLocalResidual_of_blockCoverCoupled (h : BlockCoverResidualCoupled) :
    SubTripleDesignLocalResidual := by
  classical
  intro ε hε μ hμ η hη d₀ hd₀
  -- ### the parameters of the construction
  obtain ⟨μ₂, hμ₂0, hμ₂1, hμ₂μ, hμ₂half⟩ :
      ∃ m : ℝ, 0 < m ∧ m ≤ 1 ∧ m ≤ μ ∧ 2 * m ≤ μ := by
    refine ⟨min μ 1 / 2, ?_, ?_, ?_, ?_⟩
    · have : 0 < min μ 1 := lt_min hμ one_pos; linarith
    · have : min μ 1 ≤ 1 := min_le_right _ _; linarith
    · have : min μ 1 ≤ μ := min_le_left _ _; linarith
    · have : min μ 1 ≤ μ := min_le_left _ _; linarith
  obtain ⟨δ, hδ0, hδhalf, hδε, hδsq⟩ :
      ∃ d : ℝ, 0 < d ∧ d ≤ 1 / 2 ∧ d ≤ ε / 2 ∧ d / 2 ≤ (ε / 2) ^ 2 := by
    have h0 : 0 < min 1 ε := lt_min one_pos hε
    have h1 : min 1 ε ≤ 1 := min_le_left _ _
    have h2 : min 1 ε ≤ ε := min_le_right _ _
    refine ⟨min 1 ε * min 1 ε / 8, by positivity, by nlinarith, by nlinarith, by nlinarith⟩
  have hδ1 : δ ≤ 1 := by linarith
  have hδ3 : (0:ℝ) < δ ^ 3 := by positivity
  obtain ⟨T₀, hT₀0, hT₀1, hT₀2⟩ :
      ∃ T : ℝ, 0 < T ∧ 2 / (μ₂ * δ ^ 3) ≤ T ∧ d₀ / δ ^ 3 ≤ T := by
    refine ⟨2 / (μ₂ * δ ^ 3) + d₀ / δ ^ 3, by positivity, ?_, ?_⟩
    · have : (0:ℝ) ≤ d₀ / δ ^ 3 := by positivity
      linarith
    · have : (0:ℝ) < 2 / (μ₂ * δ ^ 3) := by positivity
      linarith
  -- ### the block uniformity scale the reduction needs
  obtain ⟨ε₂, hε₂0', hε₂1', hε₂A', hε₂C', hε₂D', hε₂E'⟩ :
      ∃ e : ℝ, 0 < e ∧ e ≤ 1 ∧ e ≤ μ₂ * δ ^ 3 / 96 ∧ e ≤ η * μ₂ * δ ^ 6 / 2560 ∧
        e ≤ δ ^ 3 / 160 ∧ e ≤ ε / 8 := by
    refine ⟨min 1 (min (μ₂ * δ ^ 3 / 96) (min (η * μ₂ * δ ^ 6 / 2560)
      (min (δ ^ 3 / 160) (ε / 8)))), ?_, min_le_left _ _, ?_, ?_, ?_, ?_⟩
    · exact lt_min one_pos (lt_min (by positivity)
        (lt_min (by positivity) (lt_min (by positivity) (by positivity))))
    · exact le_trans (min_le_right _ _) (min_le_left _ _)
    · exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
    · exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (min_le_left _ _)))
    · exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (min_le_right _ _)))
  -- ### the coupling: the residual names the regularity window it can serve
  obtain ⟨ε₁₀, hε₁₀0, hcoup⟩ := h (ε / 2) δ ε₂ T₀ (by linarith) hδ0 hδ1 hδε hε₂0' hT₀0
  obtain ⟨ε₁, hε₁0, hε₁1, hε₁b, hε₁ε, hε₁A, hε₁10⟩ :
      ∃ e : ℝ, 0 < e ∧ e ≤ 1 ∧ e ≤ δ / 2 ∧ e ≤ ε ∧ e ≤ μ₂ * δ ^ 3 / 12 ∧ e ≤ ε₁₀ := by
    refine ⟨min 1 (min (δ / 2) (min ε (min (μ₂ * δ ^ 3 / 12) ε₁₀))), ?_, min_le_left _ _,
      ?_, ?_, ?_, ?_⟩
    · exact lt_min one_pos (lt_min (by positivity)
        (lt_min hε (lt_min (by positivity) hε₁₀0)))
    · exact le_trans (min_le_right _ _) (min_le_left _ _)
    · exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
    · exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (min_le_left _ _)))
    · exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (min_le_right _ _)))
  refine ⟨ε₁, hε₁0, hε₁ε, hε₁1, ?_⟩
  -- ### the residual supplies the relative block size and the blocks
  obtain ⟨α, hαε, hα2, hε₂, n₀, hres⟩ := hcoup ε₁ hε₁0 hε₁10 hε₁1
  refine ⟨n₀, ?_⟩
  intro V _ _ G _ P hV hP hPl hPb hPu _hrich
  obtain ⟨τ, k, U, W, X, A, B, C, hτT, hgrid, hdisj, hcov⟩ := hres V G P hV hP hPl hPb hPu
  -- ### the scale `τ` is large
  have hτpos : 0 < τ := lt_of_lt_of_le hT₀0 hτT
  have hτ2 : 2 / (μ₂ * δ ^ 3) ≤ τ := le_trans hT₀1 hτT
  have hτ2' : 2 ≤ τ * (μ₂ * δ ^ 3) := by
    rw [div_le_iff₀ (by positivity)] at hτ2; linarith
  have hτδ3 : 2 ≤ τ * δ ^ 3 := tau_delta3_lower hτpos hδ3 hμ₂1 hτ2'
  have hτδ8 : 8 ≤ τ * δ := tau_delta_lower hτpos hδ0 hδhalf hτδ3
  have hτd₀ : d₀ ≤ τ * δ ^ 3 := by
    have hle : d₀ / δ ^ 3 ≤ τ := le_trans hT₀2 hτT
    rw [div_le_iff₀ hδ3] at hle; linarith
  -- ### the local clauses of the design
  have hα0 : 0 < α := lt_of_lt_of_le (by positivity) hαε
  -- the derived windows for the block uniformity scale `ε₂ = (ε₁/8)/α`
  have hε₂0 : (0:ℝ) < ε₁ / 8 / α := by positivity
  have hε₂1 : ε₁ / 8 / α ≤ 1 := le_trans hε₂ hε₂1'
  have hε₂A : ε₁ / 8 / α ≤ μ₂ * δ ^ 3 / 96 := le_trans hε₂ hε₂A'
  have hε₂C : ε₁ / 8 / α ≤ η * μ₂ * δ ^ 6 / 2560 := le_trans hε₂ hε₂C'
  have hε₂D : ε₁ / 8 / α ≤ δ ^ 3 / 160 := le_trans hε₂ hε₂D'
  have hε₂E : ε₁ / 8 / α ≤ ε / 8 := le_trans hε₂ hε₂E'
  have hδ3le : δ ^ 3 ≤ δ := by
    simpa using pow_le_pow_of_le_one hδ0.le hδ1 (by norm_num : 1 ≤ 3)
  have hμδpos : (0:ℝ) ≤ μ₂ * δ ^ 3 := by positivity
  have hErr : ε₁ / 8 + 2 * (ε₁ / 8 / α) ≤ μ₂ * δ ^ 3 / 12 := by
    have h1 : ε₁ / 8 ≤ μ₂ * δ ^ 3 / 96 := by linarith
    linarith
  have hdense : 2 * (ε₁ / 8 / α) + ε₁ / 8 ≤ δ := by
    have h1 : ε₁ / 8 ≤ δ / 16 := by linarith
    have h2 : δ ^ 3 / 80 ≤ δ / 80 := by linarith
    linarith
  have hde : ε₁ / 4 ≤ δ := by linarith
  have hshape := subTripleShape_of_gridSubTriples G P U W X A B C hε₁0 hαε (by linarith)
    hδ0 hδ1 hμ₂0 hμ₂1 hde hErr hdense hτ2 hgrid hdisj
  -- ### the numerical data of each sub-triple
  have hdata : ∀ i < k,
      (Disjoint (A i) (B i) ∧ Disjoint (A i) (C i) ∧ Disjoint (B i) (C i)) ∧
      (|((G.regularityReduced P (ε₁ / 8) (ε₁ / 4)).edgeDensity (A i) (B i) : ℝ)
          - (G.edgeDensity (U i) (W i) : ℝ)| ≤ ε₁ / 8 ∧
        |((G.regularityReduced P (ε₁ / 8) (ε₁ / 4)).edgeDensity (A i) (C i) : ℝ)
          - (G.edgeDensity (U i) (X i) : ℝ)| ≤ ε₁ / 8 ∧
        |((G.regularityReduced P (ε₁ / 8) (ε₁ / 4)).edgeDensity (B i) (C i) : ℝ)
          - (G.edgeDensity (W i) (X i) : ℝ)| ≤ ε₁ / 8) := by
    intro i hi
    obtain ⟨h1, -, h3⟩ := gridSubTriple_data G P hε₁0 hαε (by linarith) hde (hgrid i hi)
    exact ⟨h1, h3⟩
  have hsize : ∀ (s dens : ℝ), δ ≤ dens → dens ≤ 1 → |s - τ * dens| ≤ 1 →
      3 / 4 * (τ * δ) ≤ s ∧ s ≤ 5 / 4 * τ :=
    fun s dens h1 h2 habs => block_size_bounds hτpos hδ0 hδ1 hτδ8 h1 h2 habs
  have hblocks : ∀ i < k,
      (3 / 4 * (τ * δ) ≤ (#(A i) : ℝ) ∧ (#(A i) : ℝ) ≤ 5 / 4 * τ) ∧
      (3 / 4 * (τ * δ) ≤ (#(B i) : ℝ) ∧ (#(B i) : ℝ) ≤ 5 / 4 * τ) ∧
      (3 / 4 * (τ * δ) ≤ (#(C i) : ℝ) ∧ (#(C i) : ℝ) ≤ 5 / 4 * τ) := by
    intro i hi
    obtain ⟨-, -, -, -, -, -, -, hsA, hsB, hsC⟩ := hgrid i hi
    obtain ⟨⟨hx, hx1⟩, ⟨hy, hy1⟩, ⟨hz, hz1⟩⟩ := gridSubTriple_density_mem G P (hgrid i hi)
    exact ⟨hsize _ _ hz hz1 hsA, hsize _ _ hy hy1 hsB, hsize _ _ hx hx1 hsC⟩
  have hHdens : ∀ S T : Finset V,
      (0:ℝ) ≤ (((G.regularityReduced P (ε₁ / 8) (ε₁ / 4)).edgeDensity S T : ℚ) : ℝ) := by
    intro S T
    exact_mod_cast (G.regularityReduced P (ε₁ / 8) (ε₁ / 4)).edgeDensity_nonneg S T
  -- ### the objects of the design
  refine ⟨ε₁ / 8 / α, μ₂, (μ - μ₂) * τ * δ ^ 3 / 2, k, A, B, C,
    fun i => τ * ((G.edgeDensity (U i) (W i) : ℝ) * (G.edgeDensity (U i) (X i) : ℝ)
      * (G.edgeDensity (W i) (X i) : ℝ)),
    fun i => ((G.regularityReduced P (ε₁ / 8) (ε₁ / 4)).edgeDensity (A i) (B i) : ℝ)
      * (#(A i) : ℝ) * (#(B i) : ℝ)
      + ((G.regularityReduced P (ε₁ / 8) (ε₁ / 4)).edgeDensity (A i) (C i) : ℝ)
      * (#(A i) : ℝ) * (#(C i) : ℝ)
      + ((G.regularityReduced P (ε₁ / 8) (ε₁ / 4)).edgeDensity (B i) (C i) : ℝ)
      * (#(B i) : ℝ) * (#(C i) : ℝ),
    hshape, by positivity, by linarith, ?_, hη.le, hμ₂μ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `0 < t`
    exact t_pos hτpos hδ3 hμ₂0 hμ₂half
  · -- `d₀ ≤ d i`
    intro i hi
    obtain ⟨⟨hx, -⟩, ⟨hy, -⟩, ⟨hz, -⟩⟩ := gridSubTriple_density_mem G P (hgrid i hi)
    exact d_lower hτpos hδ0 hx hy hz hτd₀
  · -- `0 ≤ d i`
    intro i hi
    obtain ⟨⟨hx, -⟩, ⟨hy, -⟩, ⟨hz, -⟩⟩ := gridSubTriple_density_mem G P (hgrid i hi)
    exact d_nonneg hτpos hδ0 hx hy hz
  · -- the slack `2t ≤ (μ - μ₂) d i`
    intro i hi
    obtain ⟨⟨hx, -⟩, ⟨hy, -⟩, ⟨hz, -⟩⟩ := gridSubTriple_density_mem G P (hgrid i hi)
    exact slack_bound hτpos hδ0 hx hy hz hμ₂half hμ₂0
  · -- `Elo i` really is a lower bound for the number of edges
    intro i hi
    obtain ⟨⟨hd1, hd2, hd3⟩, -⟩ := hdata i hi
    exact three_edgeDensity_mul_le_tripleGraph_edges
      (G.regularityReduced P (ε₁ / 8) (ε₁ / 4)) (A i) (B i) (C i) hd1 hd2 hd3
  · -- the exceptional-edge clause
    intro i hi
    obtain ⟨-, habs1, -, -⟩ := hdata i hi
    obtain ⟨⟨-, -⟩, -, -⟩ := gridSubTriple_density_mem G P (hgrid i hi)
    obtain ⟨⟨haL, haU⟩, ⟨hbL, hbU⟩, ⟨hcL, hcU⟩⟩ := hblocks i hi
    obtain ⟨ha0, hb0, hc0, hSle, hS0, hsuple, hsup0⟩ :=
      area_bounds hτpos hδ0 hτδ8 haL haU hbL hbU hcL hcU
    have hdAB : δ - ε₁ / 8
        ≤ (((G.regularityReduced P (ε₁ / 8) (ε₁ / 4)).edgeDensity (A i) (B i) : ℝ)) := by
      have hlow := (abs_le.mp habs1).1
      have hUW := (gridSubTriple_density_mem G P (hgrid i hi)).1.1
      linarith
    have hElo := elo_lower (ε₁ := ε₁) hτpos hδ0 hδ1 hε₁0 hε₁b hdAB
      (hHdens (A i) (C i)) (hHdens (B i) (C i)) haL hbL hc0 ha0 hb0
    simp only [designBad, designSupport]
    exact exc_bound hτpos hδ0 hμ₂0 hη hε₂0 hε₂C hε₂D hSle hsuple hsup0 hElo
      (t_lower hτpos hδ3 hμ₂half) (t_pos hτpos hδ3 hμ₂0 hμ₂half)
  · -- the covering clause
    have hSsum : ∑ i ∈ Finset.range k,
        ((#(A i) : ℝ) * (#(B i) : ℝ) + (#(A i) : ℝ) * (#(C i) : ℝ)
          + (#(B i) : ℝ) * (#(C i) : ℝ))
        ≤ (Fintype.card V : ℝ) ^ 2 / 2 :=
      sum_area_le_of_rect_disjoint A B C (fun i hi => (hdata i hi).1.1)
        (fun i hi => (hdata i hi).1.2.1) (fun i hi => (hdata i hi).1.2.2) hdisj
    have hper : ∀ i ∈ Finset.range k,
        ((G.edgeDensity (U i) (W i) : ℝ) * (#(A i) : ℝ) * (#(B i) : ℝ)
            + (G.edgeDensity (U i) (X i) : ℝ) * (#(A i) : ℝ) * (#(C i) : ℝ)
            + (G.edgeDensity (W i) (X i) : ℝ) * (#(B i) : ℝ) * (#(C i) : ℝ)) / 3
          - (ε₁ / 8 + 4 * (ε₁ / 8 / α)) / 3 * ((#(A i) : ℝ) * (#(B i) : ℝ)
              + (#(A i) : ℝ) * (#(C i) : ℝ) + (#(B i) : ℝ) * (#(C i) : ℝ))
        ≤ (((G.regularityReduced P (ε₁ / 8) (ε₁ / 4)).edgeDensity (A i) (B i) : ℝ)
              * (#(A i) : ℝ) * (#(B i) : ℝ)
            + ((G.regularityReduced P (ε₁ / 8) (ε₁ / 4)).edgeDensity (A i) (C i) : ℝ)
              * (#(A i) : ℝ) * (#(C i) : ℝ)
            + ((G.regularityReduced P (ε₁ / 8) (ε₁ / 4)).edgeDensity (B i) (C i) : ℝ)
              * (#(B i) : ℝ) * (#(C i) : ℝ)
            - 4 * (ε₁ / 8 / α) * ((#(A i) : ℝ) * (#(B i) : ℝ) + (#(A i) : ℝ) * (#(C i) : ℝ)
                + (#(B i) : ℝ) * (#(C i) : ℝ))) / 3 := by
      intro i hmem
      have hi : i < k := Finset.mem_range.mp hmem
      obtain ⟨-, habs1, habs2, habs3⟩ := hdata i hi
      obtain ⟨⟨haL, haU⟩, ⟨hbL, hbU⟩, ⟨hcL, hcU⟩⟩ := hblocks i hi
      obtain ⟨ha0, hb0, hc0, -, -, -, -⟩ :=
        area_bounds hτpos hδ0 hτδ8 haL haU hbL hbU hcL hcU
      exact cover_step habs1 habs2 habs3 ha0 hb0 hc0
    have hsum := Finset.sum_le_sum hper
    rw [Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.mul_sum] at hsum
    have hcoef : (0:ℝ) ≤ (ε₁ / 8 + 4 * (ε₁ / 8 / α)) / 3 := by positivity
    have h2 := mul_le_mul_of_nonneg_left hSsum hcoef
    have hV2 : (0:ℝ) ≤ (Fintype.card V : ℝ) ^ 2 := by positivity
    have hK : (ε₁ / 8 + 4 * (ε₁ / 8 / α)) / 3 ≤ ε := by linarith
    have h3 : (ε₁ / 8 + 4 * (ε₁ / 8 / α)) / 3 * ((Fintype.card V : ℝ) ^ 2 / 2)
        ≤ ε / 2 * (Fintype.card V : ℝ) ^ 2 := cover_tail hK hV2
    simp only [designBad]
    linarith only [hcov, hsum, h2, h3]

/-- **AX1 from the coupled block-allocation residual.** -/
theorem ax1_of_blockCoverCoupled (h : BlockCoverResidualCoupled) : AX1Statement :=
  ax1_of_subTripleDesignLocal (subTripleDesignLocalResidual_of_blockCoverCoupled h)

/-! ### Axiom check -/

section AxCheck




end AxCheck

end Nibble.AX1
