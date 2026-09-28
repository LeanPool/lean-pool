/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

/-
# Nibble — the weighted (fractional) nibble for spread fractional matchings, without any
regularity or codegree hypothesis on the hypergraph

The former degree-upper-bound formulation of the fractional nibble was false: its codegree
hypothesis `codeg ≤ γ·D` was vacuous because `D` was only an *upper* bound for the degrees.
That interface has been removed. A valid statement must measure codegrees against the fractional
matching `w` itself. This file proves
that repaired statement in the regime where `w` is **spread** and **near-perfect**:

> `Nibble.fracNibble_spread_weightedCodegree` — for all `r ≥ 2` and `β > 0` there are
> `δ, γ, η > 0` such that every `r`-uniform hypergraph `H` (arbitrary degrees, arbitrary
> codegrees!) carrying a fractional matching `w` with
> * `w T ≤ δ` for every edge (spread),
> * `∑_{T ∋ v} w T ≤ 1` for every vertex and `≥ 1 - γ` outside an exceptional set of at most
>   `η|W|` vertices (near-perfect),
> * `∑_{T ⊇ {x,z}} w T ≤ γ` for every pair `x ≠ z` (small **weighted** codegree),
>
> has a matching of size at least `(1-β)∑w`.

Nothing is assumed about the degrees or the codegrees of `H`; the weighting plays the role of the
regular measure, which is exactly the content the weighted nibble is supposed to add to the regular
one.  The proof is deterministic: `Nibble.BeckFiala.exists_rounding_pairs` rounds the fractional
selection `y = D·w` to an integral subhypergraph `S ⊆ H` whose degrees *and* codegrees differ from
`D·(fractional degrees)` and `D·(weighted codegrees)` by at most `1 + r²`.  Since the fractional
degrees are `≈ 1` and the weighted codegrees are `≤ γ`, `S` is nearly `D`-regular with codegree
`≤ μD` — precisely the input of the proved regular nibble `Nibble.nibbleTheoremMostCeil_holds`.
Finally every fractional matching has `∑ w ≤ |W|/r` (`Nibble.fracMatching_sum_le`), so the
`(1-β)|W|/r` vertices the nibble covers give the required `(1-β)∑w` edges.

* `Nibble.fracNibble_spread_weightedCodegree` — the main theorem.
* `Nibble.fracNibble_spread_codegree` — the corollary for hypergraphs of (unweighted) codegree at
  most `C`, for an arbitrary `C`: a spread fractional matching has weighted codegree `≤ C·δ`.

Sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
public import LeanPool.AsymptoticTrianglePacking.Internal.WeightedBeckFialaPairs
public import LeanPool.AsymptoticTrianglePacking.Internal.WeightedFractional
public import LeanPool.AsymptoticTrianglePacking.Internal.NearRegularNibble

/-! # Weighted fractional-to-integral nibble bridge -/

@[expose] public section

open Finset Hypergraph LeanPool.AsymptoticTrianglePacking.Internal

namespace Nibble

/-- **The weighted nibble for spread, near-perfect fractional matchings.**  No regularity and no
codegree hypothesis is placed on the hypergraph: all the hypotheses are on the fractional matching
`w`. -/
theorem fracNibble_spread_weightedCodegree (r : ℕ) (hr : 2 ≤ r) (β : ℝ) (hβ : 0 < β) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ γ : ℝ, 0 < γ ∧ ∃ η : ℝ, 0 < η ∧
      ∀ {W : Type} [Fintype W] [DecidableEq W] (H : Finset (Finset W)) (w : Finset W → ℝ)
        (Exc : Finset W),
        IsUniform H r →
        (∀ T, 0 ≤ w T) →
        (∀ T ∈ H, w T ≤ δ) →
        (∀ v : W, ∑ T ∈ H.filter (fun T => v ∈ T), w T ≤ 1) →
        (∀ v : W, v ∉ Exc → 1 - γ ≤ ∑ T ∈ H.filter (fun T => v ∈ T), w T) →
        (Exc.card : ℝ) ≤ η * (Fintype.card W : ℝ) →
        (∀ x z : W, x ≠ z → ∑ T ∈ H.filter (fun T => x ∈ T ∧ z ∈ T), w T ≤ γ) →
        ∃ M : Finset (Finset W), IsMatching H M ∧
          (1 - β) * ((Fintype.card W : ℝ) / r) ≤ (M.card : ℝ) ∧
          (1 - β) * (∑ T ∈ H, w T) ≤ (M.card : ℝ) := by
  classical
  obtain ⟨μ, hμ, η, hη, d₀, hd₀, hmain⟩ := nibbleTheoremMostCeil_holds r hr β hβ
  set k : ℕ := 1 + r * r with hkdef
  have hkpos : (0 : ℝ) < (k : ℝ) := by
    have : 0 < k := by rw [hkdef]; omega
    exact_mod_cast this
  set D : ℕ := max ⌈d₀⌉₊ ⌈(4 * (k : ℝ)) / μ⌉₊ + 1 with hDdef
  have hDpos : 0 < D := Nat.succ_pos _
  have hDR : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hDpos
  have hd₀D : d₀ ≤ (D : ℝ) := by
    have h1 : (⌈d₀⌉₊ : ℝ) ≤ (D : ℝ) := by
      exact_mod_cast (by omega : ⌈d₀⌉₊ ≤ D)
    exact le_trans (Nat.le_ceil _) h1
  have hkD : 4 * (k : ℝ) ≤ μ * (D : ℝ) := by
    have h1 : ((4 * (k : ℝ)) / μ) ≤ (⌈(4 * (k : ℝ)) / μ⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈(4 * (k : ℝ)) / μ⌉₊ : ℝ) ≤ (D : ℝ) := by
      exact_mod_cast (by omega : ⌈(4 * (k : ℝ)) / μ⌉₊ ≤ D)
    have h3 : ((4 * (k : ℝ)) / μ) ≤ (D : ℝ) := le_trans h1 h2
    rw [div_le_iff₀ hμ] at h3
    linarith
  refine ⟨1 / (D : ℝ), by positivity, μ / 4, by positivity, η, hη, ?_⟩
  intro W _ _ H w Exc hunif hwnn hspread hvle hvge hExc hcod
  -- the Beck–Fiala rounding of `y = D·w`
  set y : Finset W → ℝ := fun T => (D : ℝ) * w T with hydef
  have hy0 : ∀ T ∈ H, 0 ≤ y T := fun T _ => mul_nonneg hDR.le (hwnn T)
  have hy1 : ∀ T ∈ H, y T ≤ 1 := by
    intro T hT
    have h := hspread T hT
    rw [hydef]
    calc (D : ℝ) * w T ≤ (D : ℝ) * (1 / (D : ℝ)) := mul_le_mul_of_nonneg_left h hDR.le
      _ = 1 := by field_simp
  obtain ⟨S, hSH, hdeg, hcodeg⟩ :=
    BeckFiala.exists_rounding_pairs r H (fun T hT => hunif T hT) y hy0 hy1
  have hkr : (1 : ℝ) + (r : ℝ) * r = (k : ℝ) := by rw [hkdef]; push_cast; ring
  have hfrac : ∀ v : W, ∑ T ∈ H.filter (fun T => v ∈ T), y T
      = (D : ℝ) * ∑ T ∈ H.filter (fun T => v ∈ T), w T := by
    intro v; rw [hydef, ← Finset.mul_sum]
  have hfrac2 : ∀ x z : W, ∑ T ∈ H.filter (fun T => x ∈ T ∧ z ∈ T), y T
      = (D : ℝ) * ∑ T ∈ H.filter (fun T => x ∈ T ∧ z ∈ T), w T := by
    intro x z; rw [hydef, ← Finset.mul_sum]
  -- the rounded hypergraph is nearly `D`-regular with small codegree
  have hSunif : IsUniform S r := fun T hT => hunif T (hSH hT)
  have hdegeq : ∀ v : W, ((S.filter (fun T => v ∈ T)).card : ℝ) = (degree S v : ℝ) := by
    intro v; simp [degree]
  have hcodeq : ∀ x z : W, ((S.filter (fun T => x ∈ T ∧ z ∈ T)).card : ℝ)
      = (codegree S x z : ℝ) := by
    intro x z; simp [codegree]
  have hceil : ∀ v : W, (degree S v : ℝ) ≤ (1 + μ) * (D : ℝ) := by
    intro v
    have h := (abs_le.mp (hdeg v)).2
    rw [hfrac v, hdegeq v, hkr] at h
    have h2 : (D : ℝ) * ∑ T ∈ H.filter (fun T => v ∈ T), w T ≤ (D : ℝ) * 1 :=
      mul_le_mul_of_nonneg_left (hvle v) hDR.le
    linarith
  have hlow : ∀ v : W, v ∉ Exc → (1 - μ) * (D : ℝ) ≤ (degree S v : ℝ) := by
    intro v hv
    have h := (abs_le.mp (hdeg v)).1
    rw [hfrac v, hdegeq v, hkr] at h
    have h2 : (D : ℝ) * (1 - μ / 4) ≤ (D : ℝ) * ∑ T ∈ H.filter (fun T => v ∈ T), w T :=
      mul_le_mul_of_nonneg_left (hvge v hv) hDR.le
    linarith
  have hScod : CodegreeBounded S (μ * (D : ℝ)) := by
    intro x z hxz
    have h := (abs_le.mp (hcodeg x z)).2
    rw [hfrac2 x z, hcodeq x z, hkr] at h
    have h2 : (D : ℝ) * ∑ T ∈ H.filter (fun T => x ∈ T ∧ z ∈ T), w T ≤ (D : ℝ) * (μ / 4) :=
      mul_le_mul_of_nonneg_left (hcod x z hxz) hDR.le
    linarith
  have hreg : NearlyRegularMost S (D : ℝ) μ η :=
    ⟨Exc, hExc, fun v hv => ⟨hlow v hv, hceil v⟩⟩
  obtain ⟨M, hM, hMcard⟩ := hmain S (D : ℝ) hDR hd₀D hSunif hreg hScod hceil
  refine ⟨M, ⟨Finset.Subset.trans hM.subset hSH, hM.disjoint⟩, hMcard, ?_⟩
  -- every fractional matching has total weight at most `|W|/r`
  have hrpos : (0 : ℝ) < r := by
    have : 0 < r := lt_of_lt_of_le (by norm_num) hr
    exact_mod_cast this
  have hsum : (∑ T ∈ H, w T) ≤ (Fintype.card W : ℝ) / r := by
    rw [le_div_iff₀ hrpos, mul_comm]
    exact Hypergraph.weightedSum_le_card H w hunif hvle
  rcases le_or_gt β 1 with h1 | h1
  · exact le_trans (mul_le_mul_of_nonneg_left hsum (by linarith)) hMcard
  · have hnn' : 0 ≤ ∑ T ∈ H, w T := Finset.sum_nonneg (fun T _ => hwnn T)
    have hle0 : (1 - β) * (∑ T ∈ H, w T) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) hnn'
    exact le_trans hle0 (Nat.cast_nonneg _)

/-- **The spread hypothesis is redundant.**  Every edge contains a pair `x ≠ z`, so its weight is at
most the weighted codegree of that pair. -/
theorem weight_le_weightedCodegree {W : Type} [DecidableEq W] {r : ℕ} (hr : 2 ≤ r)
    {H : Finset (Finset W)} {w : Finset W → ℝ} {γ : ℝ} (hunif : IsUniform H r)
    (hwnn : ∀ T, 0 ≤ w T)
    (hcod : ∀ x z : W, x ≠ z → ∑ T ∈ H.filter (fun T => x ∈ T ∧ z ∈ T), w T ≤ γ)
    {T : Finset W} (hT : T ∈ H) : w T ≤ γ := by
  classical
  have hcard : 1 < T.card := by
    rw [hunif T hT]; omega
  obtain ⟨x, hx, z, hz, hxz⟩ := Finset.one_lt_card.mp hcard
  have hmem : T ∈ H.filter (fun T => x ∈ T ∧ z ∈ T) := Finset.mem_filter.mpr ⟨hT, hx, hz⟩
  have hle : w T ≤ ∑ T' ∈ H.filter (fun T => x ∈ T ∧ z ∈ T), w T' :=
    Finset.single_le_sum (fun T' _ => hwnn T') hmem
  exact le_trans hle (hcod x z hxz)

/-- **The weighted nibble for near-perfect fractional matchings of small weighted codegree.**  The
spread hypothesis of `Nibble.fracNibble_spread_weightedCodegree` is dropped: it follows from the
weighted codegree bound.  Still no hypothesis whatsoever on the degrees or codegrees of `H`. -/
theorem fracNibble_weightedCodegree (r : ℕ) (hr : 2 ≤ r) (β : ℝ) (hβ : 0 < β) :
    ∃ γ : ℝ, 0 < γ ∧ ∃ η : ℝ, 0 < η ∧
      ∀ {W : Type} [Fintype W] [DecidableEq W] (H : Finset (Finset W)) (w : Finset W → ℝ)
        (Exc : Finset W),
        IsUniform H r →
        (∀ T, 0 ≤ w T) →
        (∀ v : W, ∑ T ∈ H.filter (fun T => v ∈ T), w T ≤ 1) →
        (∀ v : W, v ∉ Exc → 1 - γ ≤ ∑ T ∈ H.filter (fun T => v ∈ T), w T) →
        (Exc.card : ℝ) ≤ η * (Fintype.card W : ℝ) →
        (∀ x z : W, x ≠ z → ∑ T ∈ H.filter (fun T => x ∈ T ∧ z ∈ T), w T ≤ γ) →
        ∃ M : Finset (Finset W), IsMatching H M ∧
          (1 - β) * ((Fintype.card W : ℝ) / r) ≤ (M.card : ℝ) ∧
          (1 - β) * (∑ T ∈ H, w T) ≤ (M.card : ℝ) := by
  classical
  obtain ⟨δ, hδ, γ, hγ, η, hη, hmain⟩ := fracNibble_spread_weightedCodegree r hr β hβ
  refine ⟨min δ γ, lt_min hδ hγ, η, hη, ?_⟩
  intro W _ _ H w Exc hunif hwnn hvle hvge hExc hcod
  have hcod' : ∀ x z : W, x ≠ z → ∑ T ∈ H.filter (fun T => x ∈ T ∧ z ∈ T), w T ≤ γ :=
    fun x z hxz => le_trans (hcod x z hxz) (min_le_right _ _)
  have hcodδ : ∀ x z : W, x ≠ z → ∑ T ∈ H.filter (fun T => x ∈ T ∧ z ∈ T), w T ≤ δ :=
    fun x z hxz => le_trans (hcod x z hxz) (min_le_left _ _)
  refine hmain H w Exc hunif hwnn
    (fun T hT => weight_le_weightedCodegree hr hunif hwnn hcodδ hT) hvle
    (fun v hv => le_trans (by have := min_le_right δ γ; linarith) (hvge v hv)) hExc hcod'

/-- **The weighted nibble for spread fractional matchings on hypergraphs of bounded codegree.**  A
fractional matching with all weights at most `δ` on a hypergraph of codegree at most `C` has
weighted codegree at most `C·δ`, so `Nibble.fracNibble_spread_weightedCodegree` applies.  This
generalises `Nibble.exists_matching_of_spread` (the case `C = 1`) to an arbitrary codegree bound,
and adds the weighted form `(1-β)∑w ≤ |M|` of the conclusion to the covering form
`(1-β)|W|/r ≤ |M|`. -/
theorem fracNibble_spread_codegree (r : ℕ) (hr : 2 ≤ r) (β : ℝ) (hβ : 0 < β) (C : ℝ) (hC : 0 < C) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ γ : ℝ, 0 < γ ∧ ∃ η : ℝ, 0 < η ∧
      ∀ {W : Type} [Fintype W] [DecidableEq W] (H : Finset (Finset W)) (w : Finset W → ℝ)
        (Exc : Finset W),
        IsUniform H r →
        (∀ x z : W, x ≠ z → (codegree H x z : ℝ) ≤ C) →
        (∀ T, 0 ≤ w T) →
        (∀ T ∈ H, w T ≤ δ) →
        (∀ v : W, ∑ T ∈ H.filter (fun T => v ∈ T), w T ≤ 1) →
        (∀ v : W, v ∉ Exc → 1 - γ ≤ ∑ T ∈ H.filter (fun T => v ∈ T), w T) →
        (Exc.card : ℝ) ≤ η * (Fintype.card W : ℝ) →
        ∃ M : Finset (Finset W), IsMatching H M ∧
          (1 - β) * ((Fintype.card W : ℝ) / r) ≤ (M.card : ℝ) ∧
          (1 - β) * (∑ T ∈ H, w T) ≤ (M.card : ℝ) := by
  classical
  obtain ⟨δ, hδ, γ, hγ, η, hη, hmain⟩ := fracNibble_spread_weightedCodegree r hr β hβ
  refine ⟨min δ (γ / C), lt_min hδ (by positivity), γ, hγ, η, hη, ?_⟩
  intro W _ _ H w Exc hunif hCod hwnn hspread hvle hvge hExc
  refine hmain H w Exc hunif hwnn (fun T hT => le_trans (hspread T hT) (min_le_left _ _))
    hvle hvge hExc ?_
  intro x z hxz
  -- the weighted codegree is at most `C · δ ≤ γ`
  have hbound : ∀ T ∈ H.filter (fun T => x ∈ T ∧ z ∈ T), w T ≤ γ / C := by
    intro T hT
    exact le_trans (hspread T (Finset.mem_filter.mp hT).1) (min_le_right _ _)
  calc ∑ T ∈ H.filter (fun T => x ∈ T ∧ z ∈ T), w T
      ≤ ∑ _T ∈ H.filter (fun T => x ∈ T ∧ z ∈ T), (γ / C) := Finset.sum_le_sum hbound
    _ = ((H.filter (fun T => x ∈ T ∧ z ∈ T)).card : ℝ) * (γ / C) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = (codegree H x z : ℝ) * (γ / C) := by rw [codegree]
    _ ≤ C * (γ / C) := by
        exact mul_le_mul_of_nonneg_right (hCod x z hxz) (by positivity)
    _ = γ := by field_simp

end Nibble
