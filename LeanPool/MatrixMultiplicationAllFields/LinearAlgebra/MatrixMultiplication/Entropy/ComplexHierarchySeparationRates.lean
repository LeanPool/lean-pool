/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Entropy.ComplexTypeEntropy
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Separation.ComplexHierarchyTypeCounting
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Entropy.ComplexSeparationAsymptotics
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Separation.ComplexLabelHierarchySeparation

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-! Finite entropy, rate estimates and ordered asymptotic limits. -/

@[expose] public section

namespace MatrixMultiplicationAllFields



noncomputable section

namespace MatrixMultiplication.Foundation

open Filter
open scoped BigOperators Topology

namespace LabelHierarchySeparation

theorem poolAuxiliaryCost_pos (k : ℕ) : 0 < poolAuxiliaryCost k := by
  unfold poolAuxiliaryCost
  split_ifs
  · exact Nat.zero_lt_one
  · exact Separation.gridGroupOrder_pos k

theorem population_le_poolAuxiliaryCost (k : ℕ) : k ≤ poolAuxiliaryCost k := by
  unfold poolAuxiliaryCost
  split_ifs with hk
  · simp [hk]
  · exact Separation.population_le_gridGroupOrder k

theorem poolAuxiliaryCost_le_gridGroupOrder (k : ℕ) :
    poolAuxiliaryCost k ≤ Separation.gridGroupOrder k := by
  unfold poolAuxiliaryCost
  split_ifs with hk
  · simpa only [hk] using Separation.population_le_gridGroupOrder k
  · exact le_rfl

theorem tendsto_log_poolAuxiliaryCost_div_nat {K : ℕ → ℕ} {H : ℝ}
    (hK : ∀ n, 0 < K n) (hH : 0 ≤ H)
    (hpop : Tendsto (fun n => Real.log (K n : ℝ) / (n : ℝ)) atTop (𝓝 H)) :
    Tendsto (fun n => Real.log (poolAuxiliaryCost (K n) : ℝ) / (n : ℝ))
      atTop (𝓝 H) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hpop
    (Separation.tendsto_log_gridGroupOrder_div_nat hK hH hpop) ?_ ?_
  · intro n
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
    exact Real.log_le_log (Nat.cast_pos.mpr (hK n))
      (by exact_mod_cast population_le_poolAuxiliaryCost (K n))
  · intro n
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
    exact Real.log_le_log (Nat.cast_pos.mpr (poolAuxiliaryCost_pos (K n)))
      (by exact_mod_cast poolAuxiliaryCost_le_gridGroupOrder (K n))

end LabelHierarchySeparation

namespace HierarchySeparationRates

universe u v w

/-- Total population times the entropy of its normalized letter frequencies. -/
def populationEntropyRate {B : Type*} [Fintype B] (counts : B → ℕ) : ℝ :=
  (∑ b, counts b : ℕ) *
    finiteEntropy (fun b => (counts b : ℝ) / (∑ b, counts b : ℕ))

theorem tendsto_log_multinomial_mul_div_repetition {B : Type*} [Fintype B]
    (counts : B → ℕ) :
    Tendsto
      (fun t : ℕ =>
        Real.log (Nat.multinomial Finset.univ (fun b => t * counts b) : ℝ) / (t : ℝ))
      atTop (𝓝 (populationEntropyRate counts)) := by
  by_cases hD : 0 < ∑ b, counts b
  · have hD' : ((∑ b, counts b : ℕ) : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.ne_of_gt hD)
    have h := (tendsto_log_multinomial_mul counts hD).const_mul
      ((∑ b, counts b : ℕ) : ℝ)
    apply h.congr
    intro t
    by_cases ht : t = 0
    · simp [ht]
    have ht' : (t : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr ht
    change ((∑ b, counts b : ℕ) : ℝ) *
        (Real.log (Nat.multinomial Finset.univ (fun b => t * counts b) : ℝ) /
          ((t : ℝ) * (∑ b, counts b : ℕ))) = _
    field_simp [hD', ht']
  · have hz : (∑ b, counts b) = 0 := Nat.eq_zero_of_not_pos hD
    have hc (b : B) : counts b = 0 := by
      apply Nat.eq_zero_of_le_zero
      calc
        counts b ≤ ∑ c, counts c :=
          Finset.single_le_sum (fun c _ => Nat.zero_le _) (Finset.mem_univ b)
        _ = 0 := hz
    simp only [populationEntropyRate, hz, Nat.cast_zero, zero_mul]
    simp [Nat.multinomial, hc]

theorem populationEntropyRate_nonneg {B : Type*} [Fintype B] (counts : B → ℕ) :
    0 ≤ populationEntropyRate counts := by
  apply ge_of_tendsto' (tendsto_log_multinomial_mul_div_repetition counts)
  intro t
  apply div_nonneg _ (Nat.cast_nonneg t)
  apply Real.log_nonneg
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr
    (Nat.ne_of_gt (Nat.multinomial_pos Finset.univ (fun b => t * counts b)))

section FinitePools

variable {I : Type u} [Fintype I] {Alphabet : I → Type v}
  [∀ i, Fintype (Alphabet i)]

/-- The multinomial count for one pool after repeating all populations t times. -/
def poolTypeCount (counts : ∀ i, Alphabet i → ℕ) (i : I) (t : ℕ) : ℕ :=
  Nat.multinomial Finset.univ (fun b => t * counts i b)

/-- The sum of population entropy rates over all pools. -/
def poolEntropyTotal (counts : ∀ i, Alphabet i → ℕ) : ℝ :=
  ∑ i, populationEntropyRate (counts i)

/-- The product of exact word counts across the independent pools. -/
def pairingProduct (counts : ∀ i, Alphabet i → ℕ) (t : ℕ) : ℕ :=
  ∏ i, poolTypeCount counts i t

/-- The product of ambient grid group orders used to separate the pools. -/
def gridProduct (counts : ∀ i, Alphabet i → ℕ) (t : ℕ) : ℕ :=
  ∏ i, Separation.gridGroupOrder (poolTypeCount counts i t)

/-- The product of auxiliary tensor costs assigned to the pools. -/
def auxiliaryProduct (counts : ∀ i, Alphabet i → ℕ) (t : ℕ) : ℕ :=
  ∏ i, LabelHierarchySeparation.poolAuxiliaryCost (poolTypeCount counts i t)

omit [Fintype I] in
theorem poolTypeCount_pos (counts : ∀ i, Alphabet i → ℕ) (i : I) (t : ℕ) :
    0 < poolTypeCount counts i t := Nat.multinomial_pos _ _

theorem pairingProduct_le_auxiliaryProduct (counts : ∀ i, Alphabet i → ℕ) (t : ℕ) :
    pairingProduct counts t ≤ auxiliaryProduct counts t := by
  exact Finset.prod_le_prod (fun i _ =>
    LabelHierarchySeparation.population_le_poolAuxiliaryCost (poolTypeCount counts i t))

theorem auxiliaryProduct_le_gridProduct (counts : ∀ i, Alphabet i → ℕ) (t : ℕ) :
    auxiliaryProduct counts t ≤ gridProduct counts t := by
  exact Finset.prod_le_prod (fun i _ =>
    LabelHierarchySeparation.poolAuxiliaryCost_le_gridGroupOrder (poolTypeCount counts i t))

omit [Fintype I] in
theorem tendsto_log_poolTypeCount_div (counts : ∀ i, Alphabet i → ℕ) (i : I) :
    Tendsto (fun t : ℕ => Real.log (poolTypeCount counts i t : ℝ) / (t : ℝ))
      atTop (𝓝 (populationEntropyRate (counts i))) :=
  tendsto_log_multinomial_mul_div_repetition (counts i)

theorem tendsto_log_pairingProduct_div (counts : ∀ i, Alphabet i → ℕ) :
    Tendsto (fun t : ℕ => Real.log (pairingProduct counts t : ℝ) / (t : ℝ))
      atTop (𝓝 (poolEntropyTotal counts)) := by
  exact Separation.tendsto_log_nat_prod_div_nat Finset.univ
    (fun i _ t => poolTypeCount_pos counts i t)
    (fun i _ => tendsto_log_poolTypeCount_div counts i)

theorem tendsto_log_gridProduct_div (counts : ∀ i, Alphabet i → ℕ) :
    Tendsto (fun t : ℕ => Real.log (gridProduct counts t : ℝ) / (t : ℝ))
      atTop (𝓝 (poolEntropyTotal counts)) := by
  exact Separation.tendsto_log_gridGroupOrder_prod_div_nat Finset.univ
    (fun i _ t => poolTypeCount_pos counts i t)
    (fun i _ => populationEntropyRate_nonneg (counts i))
    (fun i _ => tendsto_log_poolTypeCount_div counts i)

theorem tendsto_log_auxiliaryProduct_div (counts : ∀ i, Alphabet i → ℕ) :
    Tendsto (fun t : ℕ => Real.log (auxiliaryProduct counts t : ℝ) / (t : ℝ))
      atTop (𝓝 (poolEntropyTotal counts)) := by
  exact Separation.tendsto_log_nat_prod_div_nat Finset.univ
    (fun i _ t => LabelHierarchySeparation.poolAuxiliaryCost_pos (poolTypeCount counts i t))
    (fun i _ => LabelHierarchySeparation.tendsto_log_poolAuxiliaryCost_div_nat
      (poolTypeCount_pos counts i) (populationEntropyRate_nonneg (counts i))
      (tendsto_log_poolTypeCount_div counts i))

end FinitePools

section SourceHierarchy

variable {A : Type u} [Fintype A] {Label : ℕ → Type v}
  [∀ n, Fintype (Label n)]

theorem pushforwardCounts_mul {B : Type*} (counts : A → ℕ) (label : A → B)
    (t : ℕ) (b : B) :
    pushforwardCounts (fun a => t * counts a) label b =
      t * pushforwardCounts counts label b := by
  classical
  unfold pushforwardCounts
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : label a = b <;> simp [h]

omit [∀ n, Fintype (Label n)] in
theorem sourcePrefixCounts_mul (counts : A → ℕ) (labels : ∀ n, A → Label n)
    (t n : ℕ) (r : LabelRecord Label n) :
    LabelHierarchyCounts.sourcePrefixCounts (fun a => t * counts a) labels n r =
      t * LabelHierarchyCounts.sourcePrefixCounts counts labels n r :=
  pushforwardCounts_mul counts (labelRecordOf labels n) t r

/-- A hierarchy stage together with a label prefix at that stage. -/
abbrev PrefixPool (Label : ℕ → Type v) (depth : ℕ) :=
  Σ n : Fin depth, LabelRecord Label n.val

/-- Letter populations in each prefix fiber of the source hierarchy. -/
def sourcePoolCounts (counts : A → ℕ) (labels : ∀ n, A → Label n) (depth : ℕ)
    (j : PrefixPool Label depth) (s : Label j.1.val) : ℕ :=
  LabelHierarchyCounts.sourcePrefixCounts counts labels (j.1.val + 1) (j.2, s)

theorem pairingProduct_source_eq (counts : A → ℕ) (labels : ∀ n, A → Label n)
    (depth : ℕ) (hinjective : Function.Injective (labelRecordOf labels depth)) (t : ℕ) :
    pairingProduct (sourcePoolCounts counts labels depth) t =
      Nat.multinomial Finset.univ (fun a => t * counts a) := by
  classical
  unfold pairingProduct
  rw [Fintype.prod_sigma]
  have hpool (n : Fin depth) :
      (∏ r : LabelRecord Label n.val,
        poolTypeCount (sourcePoolCounts counts labels depth) ⟨n, r⟩ t) =
      LabelHierarchyCounts.refinementCount
        (LabelHierarchyCounts.sourcePrefixCounts (fun a => t * counts a) labels) n.val := by
    apply Finset.prod_congr rfl
    intro r _
    change Nat.multinomial Finset.univ
        (fun s : Label n.val => t *
          LabelHierarchyCounts.sourcePrefixCounts counts labels (n.val + 1) (r, s)) =
      Nat.multinomial Finset.univ
        (fun s : Label n.val =>
          LabelHierarchyCounts.sourcePrefixCounts (fun a => t * counts a)
            labels (n.val + 1) (r, s))
    apply Nat.multinomial_congr
    intro s _
    exact (sourcePrefixCounts_mul counts labels t (n.val + 1) (r, s)).symm
  simp_rw [hpool]
  rw [Fin.prod_univ_eq_prod_range]
  exact LabelHierarchyCounts.source_refinementCount_product
    (fun a => t * counts a) labels depth hinjective

theorem pairingProduct_source_eq_exactWords_card [DecidableEq A]
    (counts : A → ℕ) (labels : ∀ n, A → Label n) (depth : ℕ)
    (hinjective : Function.Injective (labelRecordOf labels depth)) (t : ℕ) :
    pairingProduct (sourcePoolCounts counts labels depth) t =
      Fintype.card (ExactWords (fun a => t * counts a)) := by
  rw [pairingProduct_source_eq counts labels depth hinjective, exactWords_card]

theorem source_poolEntropyTotal_eq (counts : A → ℕ) (labels : ∀ n, A → Label n)
    (depth : ℕ) (hinjective : Function.Injective (labelRecordOf labels depth)) :
    poolEntropyTotal (sourcePoolCounts counts labels depth) = populationEntropyRate counts := by
  have hsource : Tendsto
      (fun t : ℕ => Real.log (pairingProduct (sourcePoolCounts counts labels depth) t : ℝ) /
        (t : ℝ)) atTop (𝓝 (populationEntropyRate counts)) := by
    simpa only [pairingProduct_source_eq counts labels depth hinjective] using
      tendsto_log_multinomial_mul_div_repetition counts
  exact tendsto_nhds_unique
    (tendsto_log_pairingProduct_div (sourcePoolCounts counts labels depth)) hsource

private theorem normalized_of_per_repetition (counts : A → ℕ)
    (hD : 0 < ∑ a, counts a) (K : ℕ → ℕ)
    (h : Tendsto (fun t : ℕ => Real.log (K t : ℝ) / (t : ℝ))
      atTop (𝓝 (populationEntropyRate counts))) :
    Tendsto (fun t : ℕ => Real.log (K t : ℝ) / ((t : ℝ) * (∑ a, counts a : ℕ)))
      atTop (𝓝 (finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)))) := by
  have hD' : ((∑ a, counts a : ℕ) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt hD)
  have hmain : populationEntropyRate counts / (∑ a, counts a : ℕ) =
      finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)) := by
    unfold populationEntropyRate
    exact mul_div_cancel_left₀ _ hD'
  simpa only [div_div, hmain] using h.div_const ((∑ a, counts a : ℕ) : ℝ)

theorem tendsto_log_source_pairingProduct (counts : A → ℕ)
    (hD : 0 < ∑ a, counts a) (labels : ∀ n, A → Label n) (depth : ℕ)
    (hinjective : Function.Injective (labelRecordOf labels depth)) :
    Tendsto
      (fun t : ℕ => Real.log (pairingProduct (sourcePoolCounts counts labels depth) t : ℝ) /
        ((t : ℝ) * (∑ a, counts a : ℕ)))
      atTop (𝓝 (finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)))) := by
  simpa only [pairingProduct_source_eq counts labels depth hinjective] using
    tendsto_log_multinomial_mul counts hD

theorem tendsto_log_source_gridProduct (counts : A → ℕ)
    (hD : 0 < ∑ a, counts a) (labels : ∀ n, A → Label n) (depth : ℕ)
    (hinjective : Function.Injective (labelRecordOf labels depth)) :
    Tendsto
      (fun t : ℕ => Real.log (gridProduct (sourcePoolCounts counts labels depth) t : ℝ) /
        ((t : ℝ) * (∑ a, counts a : ℕ)))
      atTop (𝓝 (finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)))) := by
  apply normalized_of_per_repetition counts hD
  simpa only [source_poolEntropyTotal_eq counts labels depth hinjective] using
    tendsto_log_gridProduct_div (sourcePoolCounts counts labels depth)

theorem tendsto_log_source_auxiliaryProduct (counts : A → ℕ)
    (hD : 0 < ∑ a, counts a) (labels : ∀ n, A → Label n) (depth : ℕ)
    (hinjective : Function.Injective (labelRecordOf labels depth)) :
    Tendsto
      (fun t : ℕ => Real.log (auxiliaryProduct (sourcePoolCounts counts labels depth) t : ℝ) /
        ((t : ℝ) * (∑ a, counts a : ℕ)))
      atTop (𝓝 (finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)))) := by
  apply normalized_of_per_repetition counts hD
  simpa only [source_poolEntropyTotal_eq counts labels depth hinjective] using
    tendsto_log_auxiliaryProduct_div (sourcePoolCounts counts labels depth)

theorem rationalLaw_exists_source_rates [DecidableEq A] (p : RationalLaw A)
    (labels : ∀ n, A → Label n) (depth : ℕ)
    (hinjective : Function.Injective (labelRecordOf labels depth)) :
    ∃ counts : A → ℕ, 0 < ∑ a, counts a ∧
      (∀ a, (counts a : ℝ) / (∑ a, counts a : ℕ) = p.toFiniteLaw.mass a) ∧
      Tendsto
        (fun t : ℕ => Real.log (Fintype.card (ExactWords (fun a => t * counts a)) : ℝ) /
          ((t : ℝ) * (∑ a, counts a : ℕ)))
        atTop (𝓝 (finiteEntropy p.toFiniteLaw.mass)) ∧
      Tendsto
        (fun t : ℕ => Real.log (pairingProduct (sourcePoolCounts counts labels depth) t : ℝ) /
          ((t : ℝ) * (∑ a, counts a : ℕ)))
        atTop (𝓝 (finiteEntropy p.toFiniteLaw.mass)) ∧
      Tendsto
        (fun t : ℕ => Real.log (gridProduct (sourcePoolCounts counts labels depth) t : ℝ) /
          ((t : ℝ) * (∑ a, counts a : ℕ)))
        atTop (𝓝 (finiteEntropy p.toFiniteLaw.mass)) ∧
      Tendsto
        (fun t : ℕ => Real.log (auxiliaryProduct (sourcePoolCounts counts labels depth) t : ℝ) /
          ((t : ℝ) * (∑ a, counts a : ℕ)))
        atTop (𝓝 (finiteEntropy p.toFiniteLaw.mass)) := by
  obtain ⟨counts, hD, hmass⟩ := p.exists_type_representation
  have hfun : (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)) =
      p.toFiniteLaw.mass := funext hmass
  refine ⟨counts, hD, hmass, ?_, ?_, ?_, ?_⟩
  · simpa only [hfun] using tendsto_log_exactWords_card_mul counts hD
  · simpa only [hfun] using tendsto_log_source_pairingProduct counts hD labels depth hinjective
  · simpa only [hfun] using tendsto_log_source_gridProduct counts hD labels depth hinjective
  · simpa only [hfun] using tendsto_log_source_auxiliaryProduct counts hD labels depth hinjective

end SourceHierarchy

end HierarchySeparationRates
end MatrixMultiplication.Foundation

end

end MatrixMultiplicationAllFields
