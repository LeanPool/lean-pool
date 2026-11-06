/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/

module

public import LeanPool.RareSubtreePatterns.Lukasiewicz.CyclicShift


/-!
# Excursions, the first-passage decomposition, and weighted cyclic-shift identities

Complements to `PoissonDeclumping.Lukasiewicz.CyclicShift`, at the level of weights.

* `Lukasiewicz.excursionSet n`: sequences in `ℤ_{≥ -1}^n` with first passage time `ζ = n`.
  `𝐱` is a bijection from trees with `n` vertices onto it (`PlaneTree.dfsEquiv`); in weights, the
  DFS sequence of `𝒯^n` has the law of `(X_1, …, X_n)` given `ζ(𝐗) = n` (first half of
  `eq:shifts`, source lines 726–727; `PlaneTree.tsum_weight_mul_dfsSeq`).
* `Lukasiewicz.levelSet n s`: sequences in `ℤ_{≥ -1}^n` with sum `s`, and
  `Lukasiewicz.walkMass μ n s = ∑_{𝐲 ∈ levelSet n s} ∏ μ_{y_i + 1}`, i.e. `Ψ_n(s) = P(S_n = s)`
  for the walk with step law `P(X = i) = μ_{i+1}`.
* The first-passage decomposition of a bridge: a bridge `𝐱 ∈ ℤ_{≥ -1}^n` with sum `-1` splits
  uniquely as `𝐱(T) 𝐲` with `|T| ≤ n` and `𝐲 ∈ ℤ_{≥ -1}^{n - |T|}` of sum `0`
  (`PlaneTree.appendEquiv`); this is the Markov property at `ζ` used in the proof of
  Corollary `cor:cyclicshift` (source lines 811–825).
* `PlaneTree.tsum_sum_weight_mul_fringe`: the weighted form of Corollary `cor:cyclicshift`,
  `∑_{|T| = n} P_μ(T) ∑_{i < n} G(T_{u_i}) = E[G(𝒯) Ψ_{n - |𝒯|}(0)]` (with the convention
  `Ψ_{n-m}(0) = 0` for `m > n`); dividing by `n P(|𝒯| = n) = Ψ_n(-1)` gives the corollary.
-/

@[expose] public section

open scoped ENNReal

namespace PoissonDeclumping

namespace Lukasiewicz

/-- The sequences in `ℤ_{≥ -1}^n` whose first passage time to `-1` is `n`. -/
def excursionSet (n : ℕ) : Set (List ℤ) :=
  {x | x.length = n ∧ (∀ a ∈ x, -1 ≤ a) ∧ zeta x = some n}

/-- The sequences in `ℤ_{≥ -1}^n` with sum `s`. -/
def levelSet (n : ℕ) (s : ℤ) : Set (List ℤ) := {x | x.length = n ∧ (∀ a ∈ x, -1 ≤ a) ∧ x.sum = s}

theorem bridgeSet_eq_levelSet (n : ℕ) : bridgeSet n = levelSet n (-1) := rfl

/-- The weight `P(X_1 = x_1, …, X_n = x_n) = ∏ μ_{x_i + 1}` of a sequence with entries `≥ -1`. -/
noncomputable def walkWeight (μ : PMF ℕ) (x : List ℤ) : ℝ≥0∞ :=
  (x.map fun a => μ (a + 1).toNat).prod

/-- `Ψ_n(s) = P(S_n = s)`: the total walk weight of `levelSet n s`. -/
noncomputable def walkMass (μ : PMF ℕ) (n : ℕ) (s : ℤ) : ℝ≥0∞ :=
  ∑' x : levelSet n s, walkWeight μ x.1

theorem walkWeight_append (μ : PMF ℕ) (x y : List ℤ) :
    walkWeight μ (x ++ y) = walkWeight μ x * walkWeight μ y := by
  simp [walkWeight]

theorem excursionSet_subset_bridgeSet (n : ℕ) : excursionSet n ⊆ bridgeSet n := by
  rintro x ⟨hl, hge, hz⟩
  refine ⟨hl, hge, ?_⟩
  obtain ⟨-, h2, h3, -⟩ := zeta_eq_some_iff.mp hz
  rwa [List.take_of_length_le (by omega)] at h3

/-- Every bridge sequence has a finite first passage time to `-1`, at most its length. -/
theorem exists_zeta_eq_of_mem_bridgeSet {n : ℕ} {x : List ℤ} (hx : x ∈ bridgeSet n) :
    ∃ m, zeta x = some m ∧ m ≤ n := by
  obtain ⟨hl, -, hs⟩ := hx
  cases hz : zeta x with
  | none =>
    have h1 : 1 ≤ x.length := by
      rcases x with _ | ⟨a, x⟩
      · simp at hs
      · simp
    have := zeta_eq_none_iff.mp hz x.length h1 le_rfl
    rw [List.take_length] at this
    exact absurd hs this
  | some m =>
    obtain ⟨-, h2, -, -⟩ := zeta_eq_some_iff.mp hz
    exact ⟨m, rfl, by omega⟩

end Lukasiewicz

namespace PlaneTree

open Lukasiewicz

theorem weight_eq_walkWeight (μ : PMF ℕ) (T : PlaneTree) :
    weight μ T = walkWeight μ T.dfsSeq :=
  weight_eq_prod_dfsSeq μ T

/-! ### The DFS sequence of a tree with `n` vertices -/

theorem dfsSeq_mem_excursionSet (T : PlaneTree) : T.dfsSeq ∈ excursionSet T.vertexCount :=
  ⟨length_dfsSeq T, fun _ ha => neg_one_le_of_mem_dfsSeq ha, zeta_dfsSeq T⟩

/-- The DFS coding of trees with `n` vertices. -/
def dfsMap (n : ℕ) : {T : PlaneTree // T.vertexCount = n} → excursionSet n :=
  fun T => ⟨T.1.dfsSeq, by have := dfsSeq_mem_excursionSet T.1; rwa [T.2] at this⟩

theorem dfsMap_bijective (n : ℕ) : Function.Bijective (dfsMap n) := by
  constructor
  · rintro ⟨T, hT⟩ ⟨U, hU⟩ h
    exact Subtype.ext (dfsSeq_injective (congrArg Subtype.val h))
  · rintro ⟨x, hl, hge, hz⟩
    obtain ⟨T, hT, hn⟩ := exists_dfsSeq_eq_take hge hz
    refine ⟨⟨T, hn⟩, Subtype.ext ?_⟩
    change T.dfsSeq = x
    rw [hT, List.take_of_length_le (by omega)]

/-- **Łukasiewicz bijection.** Trees with `n` vertices correspond to the sequences in
`ℤ_{≥ -1}^n` with first passage time `ζ = n`. -/
noncomputable def dfsEquiv (n : ℕ) : {T : PlaneTree // T.vertexCount = n} ≃ excursionSet n :=
  Equiv.ofBijective _ (dfsMap_bijective n)

/-- **DFS law of `𝒯^n`, weighted form.** Summing `P_μ(T) g(𝐱(T))` over trees with `n`
vertices gives the sum of `P(X_1 = x_1, …, X_n = x_n) g(𝐱)` over `{ζ = n}`. -/
theorem tsum_weight_mul_dfsSeq (μ : PMF ℕ) (n : ℕ) (g : List ℤ → ℝ≥0∞) :
    ∑' T : {T : PlaneTree // T.vertexCount = n}, weight μ T.1 * g T.1.dfsSeq =
      ∑' x : excursionSet n, walkWeight μ x.1 * g x.1 := by
  rw [← (dfsEquiv n).tsum_eq]
  refine tsum_congr fun T => ?_
  rw [weight_eq_walkWeight]
  rfl

/-! ### First-passage decomposition of bridges -/

/-- `(T, 𝐲) ↦ 𝐱(T) 𝐲`, from trees with at most `n` vertices and sequences in
`ℤ_{≥ -1}^{n - |T|}` with sum `0`, to bridges of length `n`. -/
def appendMap (n : ℕ) :
    (Σ T : {T : PlaneTree // T.vertexCount ≤ n}, levelSet (n - T.1.vertexCount) 0) →
      bridgeSet n :=
  fun p => ⟨p.1.1.dfsSeq ++ p.2.1, by
    obtain ⟨⟨T, hT⟩, ⟨y, hyl, hyge, hys⟩⟩ := p
    refine ⟨?_, ?_, ?_⟩
    · simp only [List.length_append, length_dfsSeq, hyl]
      omega
    · intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · exact neg_one_le_of_mem_dfsSeq ha
      · exact hyge a ha
    · simp only [List.sum_append, sum_dfsSeq, hys, add_zero]⟩

@[simp] theorem coe_appendMap (n : ℕ)
    (p : Σ T : {T : PlaneTree // T.vertexCount ≤ n}, levelSet (n - T.1.vertexCount) 0) :
    (appendMap n p : List ℤ) = p.1.1.dfsSeq ++ p.2.1 := rfl

theorem appendMap_bijective (n : ℕ) : Function.Bijective (appendMap n) := by
  constructor
  · rintro ⟨⟨T, hT⟩, ⟨y, hy⟩⟩ ⟨⟨U, hU⟩, ⟨z, hz⟩⟩ h
    obtain ⟨rfl, rfl⟩ := dfsSeq_append_inj (congrArg Subtype.val h)
    rfl
  · rintro ⟨x, hxl, hge, hs⟩
    obtain ⟨m, hz, hmn⟩ := exists_zeta_eq_of_mem_bridgeSet ⟨hxl, hge, hs⟩
    obtain ⟨T, hT, hTm⟩ := exists_dfsSeq_eq_take hge hz
    have hsum : (x.drop m).sum = 0 := by
      have h := List.take_append_drop m x
      rw [← hT] at h
      have := congrArg List.sum h
      rw [List.sum_append, sum_dfsSeq, hs] at this
      linarith
    refine ⟨⟨⟨T, by omega⟩, ⟨x.drop m, ?_, fun a ha => hge a (List.mem_of_mem_drop ha), hsum⟩⟩,
      Subtype.ext ?_⟩
    · simp [hxl, hTm]
    · change T.dfsSeq ++ x.drop m = x
      rw [hT, List.take_append_drop]

/-- **First-passage decomposition** (Markov property at `ζ`): bridges of length `n` correspond
to pairs `(T, 𝐲)` with `|T| ≤ n` and `𝐲 ∈ ℤ_{≥ -1}^{n - |T|}` of sum `0`, via `𝐱(T) 𝐲`. -/
noncomputable def appendEquiv (n : ℕ) :
    (Σ T : {T : PlaneTree // T.vertexCount ≤ n}, levelSet (n - T.1.vertexCount) 0) ≃
      bridgeSet n :=
  Equiv.ofBijective _ (appendMap_bijective n)

/-- **Markov property at `ζ`, weighted form.** For every `G`, the bridge sum of
`P(𝐗 = 𝐱) G(T(𝐱))` equals `E[G(𝒯) Ψ_{n - |𝒯|}(0)]` in weights, with `Ψ_{n-m}(0) = 0` for
`m > n`. -/
theorem tsum_bridge_mul_ofSeq (μ : PMF ℕ) (n : ℕ) (G : PlaneTree → ℝ≥0∞) :
    ∑' x : bridgeSet n, walkWeight μ x.1 * (ofSeq x.1).elim 0 G =
      ∑' T : PlaneTree, if T.vertexCount ≤ n then
        weight μ T * G T * walkMass μ (n - T.vertexCount) 0 else 0 := by
  rw [← (appendEquiv n).tsum_eq, ENNReal.tsum_sigma']
  have h1 : ∀ p : Σ T : {T : PlaneTree // T.vertexCount ≤ n},
      levelSet (n - T.1.vertexCount) 0,
      walkWeight μ (appendEquiv n p).1 * (ofSeq (appendEquiv n p).1).elim 0 G =
        weight μ p.1.1 * G p.1.1 * walkWeight μ p.2.1 := by
    rintro ⟨⟨T, hT⟩, ⟨y, hy⟩⟩
    change walkWeight μ (T.dfsSeq ++ y) * (ofSeq (T.dfsSeq ++ y)).elim 0 G = _
    rw [ofSeq_dfsSeq_append, walkWeight_append, ← weight_eq_walkWeight]
    simp only [Option.elim_some]
    exact mul_right_comm _ _ _
  simp_rw [h1, ENNReal.tsum_mul_left]
  refine (tsum_subtype {T : PlaneTree | T.vertexCount ≤ n}
    (fun T => weight μ T * G T * walkMass μ (n - T.vertexCount) 0)).trans ?_
  refine tsum_congr fun T => ?_
  simp [Set.indicator_apply]

/-- **Kemperman / Dwass identity** with `Ψ_n(-1)`: `n P(|𝒯| = n) = Ψ_n(-1)`. -/
theorem natCast_mul_tsum_weight_eq_walkMass (μ : PMF ℕ) (n : ℕ) :
    (n : ℝ≥0∞) * ∑' T : PlaneTree, (if T.vertexCount = n then weight μ T else 0) =
      walkMass μ n (-1) :=
  natCast_mul_tsum_weight_eq μ n

/-- **Weighted form of Corollary `cor:cyclicshift`.** For every `G`,
`∑_{|T| = n} P_μ(T) ∑_{i < n} G(T_{u_i}) = ∑_{|T| ≤ n} P_μ(T) G(T) Ψ_{n - |T|}(0)`. Dividing by
`n P(|𝒯| = n) = Ψ_n(-1)` (`natCast_mul_tsum_weight_eq_walkMass`) gives
`E[G(𝒯^n_{U_n})] = E[G(𝒯) Ψ_{n - |𝒯|}(0)] / Ψ_n(-1)`. -/
theorem tsum_sum_weight_mul_fringe (μ : PMF ℕ) (n : ℕ) (G : PlaneTree → ℝ≥0∞) :
    ∑' T : {T : PlaneTree // T.vertexCount = n}, ∑ i : Fin n,
        weight μ T.1 *
          G (T.1.fringeTrees[(i : ℕ)]'(lt_length_fringeTrees (lt_of_lt_of_eq i.2 T.2.symm))) =
      ∑' T : PlaneTree, if T.vertexCount ≤ n then
        weight μ T * G T * walkMass μ (n - T.vertexCount) 0 else 0 := by
  rw [← tsum_bridge_mul_ofSeq]
  refine Eq.trans ?_ (tsum_sum_weight_mul_rotate μ n (fun x => (ofSeq x).elim 0 G))
  refine tsum_congr fun T => Finset.sum_congr rfl fun i _ => ?_
  rw [ofSeq_rotate_dfsSeq T.1 i (lt_of_lt_of_eq i.2 T.2.symm)]
  rfl

end PlaneTree

end PoissonDeclumping
