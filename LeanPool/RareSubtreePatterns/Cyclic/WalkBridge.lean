/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/

module

public import LeanPool.RareSubtreePatterns.Setup.Walk
public import LeanPool.RareSubtreePatterns.Lukasiewicz.BridgeLaw

/-!
# The convolution walk law and the product law of the increments

Source lines 711–730 and 777–780. The statement-level object `PoissonDeclumping.walkLaw μ m`
(`Setup/Walk.lean`) is the law of `S_m = X_1 + ⋯ + X_m` defined as an `m`-fold convolution of
the step law on `ℤ`, and `walkProb μ m i = Ψ_m(i) = P(S_m = i)` (with `Ψ_m = 0` for `m < 0`).
The proofs about the Łukasiewicz coding work with the law `Lukasiewicz.walkVecLaw μ n` of the
vector `(X_1, …, X_n)` (a product measure on `Fin n → ℤ`). This file proves that the two agree:

* `walkLaw_eq_map_sum`: `walkLaw μ m` is the image of `walkVecLaw μ m` under
  `ω ↦ ω_1 + ⋯ + ω_m`;
* `walkProb_natCast`, `walkProb_eq_toReal_walkMass`: `Ψ_m(i) = P(S_m = i)` computed in the product
  model, and as the total weight `walkMass μ m i` of the paths of length `m` ending at `i`;
* `walkProb_neg_one`: the Kemperman (Dwass) identity `Ψ_n(-1) = n P(|𝒯| = n)`, and
  `walkProb_neg_one_pos_iff`: `Ψ_n(-1) > 0` exactly at the admissible sizes;
* `walkVecLaw_map_split`, `walkVecLaw_map_sum_castAdd`: the first `m` and the last `k`
  increments of `(X_1, …, X_{m+k})` are independent with the laws of `(X_1, …, X_m)` and
  `(X_1, …, X_k)`; in particular `S_m` computed from the first `m` coordinates has law
  `walkLaw μ m` (finite-dimensional marginals).

The paper's sequences are indexed from `1`; ours from `0`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PoissonDeclumping

open Lukasiewicz PlaneTree

/-- The step law of `Setup/Walk.lean` is the step law of the Łukasiewicz files. -/
theorem stepLaw_eq_toMeasure (μ : PMF ℕ) : stepLaw μ = (stepPMF μ).toMeasure := by
  rw [stepLaw, stepPMF, PMF.toMeasure_map _ μ (measurable_of_countable _)]

instance (μ : PMF ℕ) : IsProbabilityMeasure (stepLaw μ) := by
  rw [stepLaw_eq_toMeasure]
  infer_instance

/-- **Bridge between the two walk laws.** The `m`-fold convolution `walkLaw μ m` is the law of
`S_m = X_1 + ⋯ + X_m` when `(X_1, …, X_m)` has the product law `walkVecLaw μ m`. -/
theorem walkLaw_eq_map_sum (μ : PMF ℕ) (m : ℕ) :
    walkLaw μ m = (walkVecLaw μ m).map (fun ω => ∑ i, ω i) := by
  induction m with
  | zero =>
    simp only [Finset.univ_eq_empty, Finset.sum_empty]
    rw [Measure.map_const, measure_univ, one_smul]
    rfl
  | succ m ih =>
    rw [walkLaw, Measure.conv, ih, stepLaw_eq_toMeasure]
    set P := (stepPMF μ).toMeasure
    have hpres := measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => P) 0
    have hW : walkVecLaw μ (m + 1) =
        (P.prod (walkVecLaw μ m)).map (MeasurableEquiv.piFinSuccAbove (fun _ => ℤ) 0).symm := by
      rw [walkVecLaw, ← hpres.symm.map_eq]
      rfl
    have hprod : ((walkVecLaw μ m).map (fun ω => ∑ i, ω i)).prod P =
        ((walkVecLaw μ m).prod P).map (Prod.map (fun ω => ∑ i, ω i) id) := by
      rw [← Measure.map_prod_map _ _ (measurable_of_countable _) measurable_id, Measure.map_id]
    rw [hW, Measure.map_map (measurable_of_countable _) (measurable_of_countable _), hprod,
      Measure.map_map (measurable_of_countable _) (measurable_of_countable _),
      ← Measure.prod_swap, Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
    congr 1
    funext p
    simp only [Function.comp_apply, MeasurableEquiv.piFinSuccAbove_symm_apply, Prod.map,
      Prod.fst_swap, Prod.snd_swap, id]
    rw [Fin.sum_univ_succAbove _ 0]
    simp [Fin.insertNthEquiv, add_comm]

instance (μ : PMF ℕ) (m : ℕ) : IsProbabilityMeasure (walkLaw μ m) := by
  rw [walkLaw_eq_map_sum]
  infer_instance

theorem walkLaw_apply (μ : PMF ℕ) (m : ℕ) (s : Set ℤ) :
    walkLaw μ m s = walkVecLaw μ m {ω | ∑ i, ω i ∈ s} := by
  rw [walkLaw_eq_map_sum, Measure.map_apply (measurable_of_countable _)
    (Set.to_countable _).measurableSet]
  rfl

/-- `P(S_m = i)` in the convolution model equals `P(X_1 + ⋯ + X_m = i)` in the product model. -/
theorem walkLaw_singleton (μ : PMF ℕ) (m : ℕ) (i : ℤ) :
    walkLaw μ m {i} = walkVecLaw μ m {ω | ∑ j, ω j = i} :=
  walkLaw_apply μ m {i}

theorem levelSet_admissible (n : ℕ) (s : ℤ) :
    ∀ x ∈ levelSet n s, x.length = n ∧ ∀ a ∈ x, -1 ≤ a := fun _ hx => ⟨hx.1, hx.2.1⟩

theorem ofFn_mem_levelSet_iff {n : ℕ} (s : ℤ) (ω : Fin n → ℤ) :
    List.ofFn ω ∈ levelSet n s ↔ ω ∈ {ω : Fin n → ℤ | ∑ i, ω i = s} ∧ ∀ i, -1 ≤ ω i := by
  simp only [levelSet, Set.mem_ofPred_eq, List.length_ofFn, List.mem_ofFn, List.sum_ofFn,
    true_and, forall_exists_index, forall_apply_eq_imp_iff]
  exact and_comm

/-- `P(X_1 + ⋯ + X_n = s)` is the total weight `walkMass μ n s` of the paths with
increments `≥ -1` of length `n` ending at `s`. -/
theorem walkVecLaw_sum_eq (μ : PMF ℕ) (n : ℕ) (s : ℤ) :
    walkVecLaw μ n {ω | ∑ i, ω i = s} = walkMass μ n s :=
  walkVecLaw_eq_tsum μ (levelSet_admissible n s) (ofFn_mem_levelSet_iff s)

theorem walkLaw_singleton_eq_walkMass (μ : PMF ℕ) (m : ℕ) (s : ℤ) :
    walkLaw μ m {s} = walkMass μ m s := by
  rw [walkLaw_singleton, walkVecLaw_sum_eq]

/-! ### `Ψ_m(i)` -/

/-- `Ψ_m(i) = P(S_m = i)` for `m ≥ 0`, computed in the product model of `(X_1, …, X_m)`. -/
theorem walkProb_natCast (μ : PMF ℕ) (m : ℕ) (i : ℤ) :
    walkProb μ m i = (walkVecLaw μ m).real {ω | ∑ j, ω j = i} := by
  rw [walkProb, ite_eq_left (by positivity), Int.toNat_natCast, measureReal_def, measureReal_def,
    walkLaw_singleton]

theorem walkProb_natCast_eq_toReal (μ : PMF ℕ) (m : ℕ) (i : ℤ) :
    walkProb μ m i = (walkLaw μ m {i}).toReal := by
  rw [walkProb, ite_eq_left (by positivity), Int.toNat_natCast, measureReal_def]

theorem walkProb_eq_toReal_walkMass (μ : PMF ℕ) (m : ℕ) (i : ℤ) :
    walkProb μ m i = (walkMass μ m i).toReal := by
  rw [walkProb_natCast_eq_toReal, walkLaw_singleton_eq_walkMass]

/-- The paper's convention `Ψ_m(i) = 0` for `m < 0`. -/
theorem walkProb_of_neg (μ : PMF ℕ) {m : ℤ} (hm : m < 0) (i : ℤ) : walkProb μ m i = 0 := by
  rw [walkProb, ite_eq_right (by omega)]

theorem walkProb_nonneg (μ : PMF ℕ) (m i : ℤ) : 0 ≤ walkProb μ m i := by
  unfold walkProb
  split_ifs
  · exact measureReal_nonneg
  · exact le_rfl

theorem walkProb_le_one (μ : PMF ℕ) (m i : ℤ) : walkProb μ m i ≤ 1 := by
  unfold walkProb
  split_ifs
  · exact measureReal_le_one
  · exact zero_le_one

/-- `Ψ_{n-m}(i)` with `m, n ∈ ℕ`, in `ℝ≥0∞`: `P(S_{n-m} = i)` if `m ≤ n` and `0` otherwise. -/
theorem walkProb_natCast_sub (μ : PMF ℕ) (n m : ℕ) (i : ℤ) :
    walkProb μ ((n : ℤ) - m) i = (if m ≤ n then walkLaw μ (n - m) {i} else 0).toReal := by
  unfold walkProb
  split_ifs with h1 h2 h2
  · rw [measureReal_def]
    congr 3
    omega
  · omega
  · omega
  · rfl

/-- **Kemperman / Dwass identity** for `Ψ`: `Ψ_n(-1) = n P(|𝒯| = n)`. -/
theorem walkProb_neg_one (μ : PMF ℕ) (n : ℕ) :
    walkProb μ n (-1) = n * (bienayme μ).real {T | T.vertexCount = n} := by
  rw [walkProb_natCast, measureReal_def, walkVecLaw_sum_eq_neg_one, ENNReal.toReal_mul,
    ENNReal.toReal_natCast, measureReal_def]

/-- `Ψ_n(-1) = P(S_n = -1)` in `ℝ≥0∞`. -/
theorem walkLaw_neg_one (μ : PMF ℕ) (n : ℕ) :
    walkLaw μ n {-1} = n * bienayme μ {T | T.vertexCount = n} := by
  rw [walkLaw_singleton, walkVecLaw_sum_eq_neg_one]

/-- No tree has `0` vertices, so `0` is never admissible. -/
theorem not_admissible_zero (μ : PMF ℕ) : ¬Admissible μ 0 := by
  intro h
  have : {T : PlaneTree | T.vertexCount = 0} = ∅ := by
    ext T
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    have := one_le_vertexCount T
    omega
  rw [Admissible, this, measure_empty] at h
  exact lt_irrefl _ h

/-- `Ψ_n(-1) > 0` exactly at the admissible sizes `n` (`P(|𝒯| = n) > 0`). -/
theorem walkProb_neg_one_pos_iff (μ : PMF ℕ) (n : ℕ) :
    0 < walkProb μ n (-1) ↔ Admissible μ n := by
  rw [walkProb_neg_one]
  constructor
  · intro h
    by_contra hn
    have h0 : bienayme μ {T | T.vertexCount = n} = 0 := le_antisymm (not_lt.mp hn) zero_le
    rw [measureReal_def, h0, ENNReal.toReal_zero, mul_zero] at h
    exact lt_irrefl _ h
  · intro h
    have hn : n ≠ 0 := by
      rintro rfl
      exact not_admissible_zero μ h
    refine mul_pos (by exact_mod_cast Nat.pos_of_ne_zero hn) ?_
    exact ENNReal.toReal_pos h.ne' (measure_ne_top _ _)

/-! ### Finite-dimensional marginals of the increments -/

/-- **Independent blocks of increments.** Under the law of `(X_1, …, X_{m+k})`, the first `m`
increments and the last `k` increments are independent, with the laws of `(X_1, …, X_m)` and
`(X_1, …, X_k)`. -/
theorem walkVecLaw_map_split (μ : PMF ℕ) (m k : ℕ) :
    (walkVecLaw μ (m + k)).map
        (fun ω => ((fun i : Fin m => ω (Fin.castAdd k i)), (fun j : Fin k => ω (Fin.natAdd m j)))) =
      (walkVecLaw μ m).prod (walkVecLaw μ k) := by
  refine Measure.ext_of_singleton fun p => ?_
  obtain ⟨a, b⟩ := p
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
  have hpre : (fun ω : Fin (m + k) → ℤ =>
      ((fun i : Fin m => ω (Fin.castAdd k i)), (fun j : Fin k => ω (Fin.natAdd m j)))) ⁻¹'
        {(a, b)} = {Fin.append a b} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Prod.mk.injEq]
    constructor
    · rintro ⟨rfl, rfl⟩
      exact Fin.append_castAdd_natAdd.symm
    · rintro rfl
      exact ⟨funext fun i => Fin.append_left a b i, funext fun j => Fin.append_right a b j⟩
  rw [hpre, ← Set.singleton_prod_singleton, Measure.prod_prod, walkVecLaw_singleton,
    walkVecLaw_singleton, walkVecLaw_singleton, Fin.prod_univ_add]
  simp only [Fin.append_left, Fin.append_right]

/-- The law of `S_m = X_1 + ⋯ + X_m`, computed from the first `m` coordinates of
`(X_1, …, X_{m+k})`, is `walkLaw μ m`. -/
theorem walkVecLaw_map_sum_castAdd (μ : PMF ℕ) (m k : ℕ) :
    (walkVecLaw μ (m + k)).map (fun ω => ∑ i : Fin m, ω (Fin.castAdd k i)) = walkLaw μ m := by
  have h : (fun ω : Fin (m + k) → ℤ => ∑ i : Fin m, ω (Fin.castAdd k i)) =
      (fun a : Fin m → ℤ => ∑ i, a i) ∘ Prod.fst ∘ (fun ω => ((fun i : Fin m => ω (Fin.castAdd k
        i)),
        (fun j : Fin k => ω (Fin.natAdd m j)))) := rfl
  rw [h, ← Measure.map_map (measurable_of_countable _) (measurable_of_countable _),
    ← Measure.map_map measurable_fst (measurable_of_countable _), walkVecLaw_map_split,
    Measure.map_fst_prod, measure_univ, one_smul, walkLaw_eq_map_sum]

/-- The law of `S_m` computed from the first `m` coordinates of `(X_1, …, X_n)`, `m ≤ n`. -/
theorem walkVecLaw_map_sum_castLE (μ : PMF ℕ) {m n : ℕ} (h : m ≤ n) :
    (walkVecLaw μ n).map (fun ω => ∑ i : Fin m, ω (Fin.castLE h i)) = walkLaw μ m := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  exact walkVecLaw_map_sum_castAdd μ m k

/-- The joint law of `(S_m, S_{m+k} - S_m)` is `walkLaw μ m ⊗ walkLaw μ k`. -/
theorem walkVecLaw_map_sum_pair (μ : PMF ℕ) (m k : ℕ) :
    (walkVecLaw μ (m + k)).map
        (fun ω => (∑ i : Fin m, ω (Fin.castAdd k i), ∑ j : Fin k, ω (Fin.natAdd m j))) =
      (walkLaw μ m).prod (walkLaw μ k) := by
  have h : (fun ω : Fin (m + k) → ℤ =>
      (∑ i : Fin m, ω (Fin.castAdd k i), ∑ j : Fin k, ω (Fin.natAdd m j))) =
      Prod.map (fun a : Fin m → ℤ => ∑ i, a i) (fun b : Fin k → ℤ => ∑ j, b j) ∘
        (fun ω => ((fun i : Fin m => ω (Fin.castAdd k i)),
          (fun j : Fin k => ω (Fin.natAdd m j)))) := rfl
  rw [h, ← Measure.map_map (measurable_of_countable _) (measurable_of_countable _),
    walkVecLaw_map_split, ← Measure.map_prod_map _ _ (measurable_of_countable _)
      (measurable_of_countable _), ← walkLaw_eq_map_sum, ← walkLaw_eq_map_sum]

end PoissonDeclumping
