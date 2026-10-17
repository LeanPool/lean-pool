/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Separation.AuxiliarySeparation
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Entropy.ComplexHierarchyEntropy

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-! Finite entropy, rate estimates and ordered asymptotic limits. -/

@[expose] public section

namespace MatrixMultiplicationAllFields



noncomputable section

namespace MatrixMultiplication

open MatrixMultiplication.Foundation Filter
open scoped Topology BigOperators

inductive ReaderPair where
  | xy | xz | yz
  deriving DecidableEq

protected abbrev ReaderPair.enumList : List ReaderPair := [.xy, .xz, .yz]

protected theorem ReaderPair.enumList_getElem?_ctorIdx_eq (x : ReaderPair) :
    ReaderPair.enumList[ReaderPair.ctorIdx x]? = some x := by
  classical
  cases x <;> rfl

protected theorem ReaderPair.enumList_nodup : ReaderPair.enumList.Nodup := by
  classical
  apply List.Nodup.of_map ReaderPair.ctorIdx
  have h : List.map ReaderPair.ctorIdx ReaderPair.enumList = List.range 3 := rfl
  exact h ▸ List.nodup_range

open Classical in
instance : Fintype ReaderPair where
  elems := Finset.mk ReaderPair.enumList (Multiset.coe_nodup.mpr ReaderPair.enumList_nodup)
  complete := by
    intro x
    rw [Finset.mem_mk, Multiset.mem_coe, List.mem_iff_getElem?]
    exact ⟨ReaderPair.ctorIdx x, ReaderPair.enumList_getElem?_ctorIdx_eq x⟩

namespace ConditionalLabels

universe u v

section PairAccounting

variable {I : Type u} [Fintype I]

open Classical in
def pairingSize (population : I → ℕ) (reader : I → ReaderPair)
    (pair : ReaderPair) : ℕ :=
  ∏ i, if reader i = pair then population i else 1

open Classical in
def pairingRate (rate : I → ℝ) (reader : I → ReaderPair)
    (pair : ReaderPair) : ℝ :=
  ∑ i, if reader i = pair then rate i else 0

theorem pairingSize_pos (population : I → ℕ) (reader : I → ReaderPair)
    (pair : ReaderPair) (positive : ∀ i, 0 < population i) :
    0 < pairingSize population reader pair := by
  classical
  apply Finset.prod_pos
  intro i _
  split_ifs
  · exact positive i
  · exact Nat.zero_lt_one

theorem pairingRate_nonneg (rate : I → ℝ) (reader : I → ReaderPair)
    (pair : ReaderPair) (nonneg : ∀ i, 0 ≤ rate i) :
    0 ≤ pairingRate rate reader pair := by
  classical
  apply Finset.sum_nonneg
  intro i _
  split_ifs
  · exact nonneg i
  · exact le_rfl

theorem pairingSize_product (population : I → ℕ) (reader : I → ReaderPair) :
    pairingSize population reader .xy * pairingSize population reader .xz *
      pairingSize population reader .yz = ∏ i, population i := by
  classical
  simp only [pairingSize, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  cases reader i <;> simp

theorem pairingRate_sum (rate : I → ℝ) (reader : I → ReaderPair) :
    pairingRate rate reader .xy + pairingRate rate reader .xz +
      pairingRate rate reader .yz = ∑ i, rate i := by
  classical
  simp only [pairingRate, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  cases reader i <;> simp

theorem tendsto_log_pairingSize (population : I → ℕ → ℕ)
    (rate : I → ℝ) (reader : I → ReaderPair) (pair : ReaderPair)
    (positive : ∀ i n, 0 < population i n)
    (growth : ∀ i, Tendsto (fun n => Real.log (population i n : ℝ) / (n : ℝ))
      atTop (𝓝 (rate i))) :
    Tendsto (fun n => Real.log (pairingSize (fun i => population i n) reader pair : ℝ) /
      (n : ℝ)) atTop (𝓝 (pairingRate rate reader pair)) := by
  classical
  apply Separation.tendsto_log_nat_prod_div_nat Finset.univ
  · intro i _ n
    split_ifs
    · exact positive i n
    · exact Nat.zero_lt_one
  · intro i _
    by_cases h : reader i = pair
    · simpa only [h, ite_true] using growth i
    · simpa only [h, ite_false, Nat.cast_one, Real.log_one, zero_div] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

end PairAccounting

section SourceHierarchy

variable {A : Type u} [Fintype A] {Label : ℕ → Type v}
  [∀ n, Fintype (Label n)]

open StageHierarchyResources HierarchySeparationRates

open Classical in
def stagePairingSize (counts : A → ℕ) (labels : ∀ n, A → Label n)
    (depth : ℕ) (reader : Fin depth → ReaderPair) (pair : ReaderPair) (t : ℕ) : ℕ :=
  pairingSize (fun n : Fin depth => stageRefinementCount counts labels n.val t) reader pair

open Classical in
def stagePairingRate (counts : A → ℕ) (labels : ∀ n, A → Label n)
    (depth : ℕ) (reader : Fin depth → ReaderPair) (pair : ReaderPair) : ℝ :=
  pairingRate (fun n : Fin depth => stageEntropyRate counts labels n.val) reader pair

open Classical in
theorem stagePairingSize_product (counts : A → ℕ) (labels : ∀ n, A → Label n)
    (depth : ℕ) (reader : Fin depth → ReaderPair)
    (complete : Function.Injective (labelRecordOf labels depth)) (t : ℕ) :
    stagePairingSize counts labels depth reader .xy t *
      stagePairingSize counts labels depth reader .xz t *
      stagePairingSize counts labels depth reader .yz t =
      Fintype.card (ExactWords (fun a => t * counts a)) := by
  classical
  rw [stagePairingSize, stagePairingSize, stagePairingSize, pairingSize_product]
  exact stagePairingProduct_eq_exactWords_card counts labels depth complete t

theorem stagePairingRate_sum (counts : A → ℕ) (labels : ∀ n, A → Label n)
    (depth : ℕ) (reader : Fin depth → ReaderPair)
    (complete : Function.Injective (labelRecordOf labels depth)) :
    stagePairingRate counts labels depth reader .xy +
      stagePairingRate counts labels depth reader .xz +
      stagePairingRate counts labels depth reader .yz = populationEntropyRate counts := by
  classical
  rw [stagePairingRate, stagePairingRate, stagePairingRate, pairingRate_sum]
  exact sum_stageEntropyRate_eq_source counts labels depth complete

theorem tendsto_log_stagePairingSize (counts : A → ℕ) (labels : ∀ n, A → Label n)
    (depth : ℕ) (reader : Fin depth → ReaderPair) (pair : ReaderPair) :
    Tendsto (fun t => Real.log (stagePairingSize counts labels depth reader pair t : ℝ) /
      (t : ℝ)) atTop (𝓝 (stagePairingRate counts labels depth reader pair)) := by
  classical
  exact tendsto_log_pairingSize _ _ reader pair
    (fun n => stageRefinementCount_pos counts labels n.val)
    (fun n => tendsto_log_stageRefinementCount_div counts labels n.val)

theorem tendsto_log_stagePairingSize_normalized (counts : A → ℕ)
    (labels : ∀ n, A → Label n) (depth : ℕ)
    (reader : Fin depth → ReaderPair) (pair : ReaderPair) :
    Tendsto (fun t => Real.log (stagePairingSize counts labels depth reader pair t : ℝ) /
      ((t : ℝ) * (∑ a, counts a : ℕ))) atTop
      (𝓝 (stagePairingRate counts labels depth reader pair / (∑ a, counts a : ℕ))) := by
  classical
  simpa only [div_div] using
    (tendsto_log_stagePairingSize counts labels depth reader pair).div_const
      ((∑ a, counts a : ℕ) : ℝ)

open Classical in
theorem auxiliary_overhead_tendsto_zero (counts : A → ℕ) (hD : 0 < ∑ a, counts a)
    (labels : ∀ n, A → Label n) (depth : ℕ)
    (complete : Function.Injective (labelRecordOf labels depth)) :
    Tendsto (fun t =>
      (Real.log (stageAuxiliaryBudget counts labels depth t : ℝ) -
        Real.log (Fintype.card (ExactWords (fun a => t * counts a)) : ℝ)) /
        ((t : ℝ) * (∑ a, counts a : ℕ))) atTop (𝓝 0) := by
  classical
  have h := (tendsto_log_stageAuxiliaryBudget counts hD labels depth complete).sub
    (tendsto_log_exactWords_card_mul counts hD)
  simpa only [sub_self, sub_div] using h

open Classical in
theorem auxiliary_overhead_nonneg (counts : A → ℕ)
    (labels : ∀ n, A → Label n) (depth : ℕ)
    (complete : Function.Injective (labelRecordOf labels depth)) (t : ℕ) :
    0 ≤ Real.log (stageAuxiliaryBudget counts labels depth t : ℝ) -
      Real.log (Fintype.card (ExactWords (fun a => t * counts a)) : ℝ) := by
  classical
  apply sub_nonneg.mpr
  rw [← stagePairingProduct_eq_exactWords_card counts labels depth complete t]
  apply Real.log_le_log
  · apply Nat.cast_pos.mpr
    exact Finset.prod_pos (fun n _ => stageRefinementCount_pos counts labels n.val t)
  · exact_mod_cast stagePairingProduct_le_budget counts labels depth t

open Classical in
theorem charged_cost_tendsto (counts : A → ℕ) (hD : 0 < ∑ a, counts a)
    (labels : ∀ n, A → Label n) (depth : ℕ)
    (complete : Function.Injective (labelRecordOf labels depth)) (C : ℝ) :
    Tendsto (fun t => C +
      (Real.log (stageAuxiliaryBudget counts labels depth t : ℝ) -
        Real.log (Fintype.card (ExactWords (fun a => t * counts a)) : ℝ)) /
        ((t : ℝ) * (∑ a, counts a : ℕ))) atTop (𝓝 C) := by
  classical
  simpa only [add_zero] using
    (auxiliary_overhead_tendsto_zero counts hD labels depth complete).const_add C

open Classical in
theorem limit_le_source_cost (counts : A → ℕ) (hD : 0 < ∑ a, counts a)
    (labels : ∀ n, A → Label n) (depth : ℕ)
    (complete : Function.Injective (labelRecordOf labels depth))
    {value : ℕ → ℝ} {rate C : ℝ}
    (limit : Tendsto value atTop (𝓝 rate))
    (finite_bound : ∀ᶠ t in atTop, value t ≤ C +
      (Real.log (stageAuxiliaryBudget counts labels depth t : ℝ) -
        Real.log (Fintype.card (ExactWords (fun a => t * counts a)) : ℝ)) /
        ((t : ℝ) * (∑ a, counts a : ℕ))) : rate ≤ C :=
  le_of_tendsto_of_tendsto limit
    (charged_cost_tendsto counts hD labels depth complete C) finite_bound

open Classical in
def lawPairingRate (p : FiniteLaw A) (labels : ∀ n, A → Label n)
    (depth : ℕ) (reader : Fin depth → ReaderPair) (pair : ReaderPair) : ℝ :=
  pairingRate (fun n : Fin depth =>
    (FiniteLabelHierarchy.ofLawLabels p labels depth).refinementEntropy n.val) reader pair

theorem lawPairingRate_sum (p : FiniteLaw A) (labels : ∀ n, A → Label n)
    (depth : ℕ) (reader : Fin depth → ReaderPair)
    (complete : Function.Injective (labelRecordOf labels depth)) :
    lawPairingRate p labels depth reader .xy +
      lawPairingRate p labels depth reader .xz +
      lawPairingRate p labels depth reader .yz = finiteEntropy p.mass := by
  classical
  rw [lawPairingRate, lawPairingRate, lawPairingRate, pairingRate_sum,
    Fin.sum_univ_eq_sum_range]
  exact FiniteLabelHierarchy.ofLawLabels_refinementEntropy_sum p labels depth complete

theorem incident_rate_eq_prefix_entropy (p : FiniteLaw A)
    (labels : ∀ n, A → Label n) (depth cut : ℕ) (hcut : cut ≤ depth)
    (reader : Fin depth → ReaderPair)
    (incident_prefix : ∀ n : Fin depth,
      (reader n = .xy ∨ reader n = .xz) ↔ n.val < cut) :
    lawPairingRate p labels depth reader .xy +
      lawPairingRate p labels depth reader .xz =
      finiteEntropy (p.map (labelRecordOf labels cut)).mass := by
  classical
  let hierarchy := FiniteLabelHierarchy.ofLawLabels p labels depth
  have hterms : ∀ n : Fin depth,
      (if reader n = .xy then hierarchy.refinementEntropy n.val else 0) +
        (if reader n = .xz then hierarchy.refinementEntropy n.val else 0) =
        if n.val < cut then hierarchy.refinementEntropy n.val else 0 := by
    intro n
    cases hr : reader n with
    | xy =>
        have hn := (incident_prefix n).mp (Or.inl hr)
        simp [hn]
    | xz =>
        have hn := (incident_prefix n).mp (Or.inr hr)
        simp [hn]
    | yz =>
        have hn : ¬n.val < cut := by
          intro h
          rcases (incident_prefix n).mpr h with h | h <;> simp [hr] at h
        simp [hn]
  have hfilter : (Finset.range depth).filter (fun n => n < cut) = Finset.range cut := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  calc
    lawPairingRate p labels depth reader .xy +
        lawPairingRate p labels depth reader .xz =
        ∑ n : Fin depth, if n.val < cut then hierarchy.refinementEntropy n.val else 0 := by
      simp only [lawPairingRate, pairingRate, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun n _ => hterms n)
    _ = ∑ n ∈ Finset.range cut, hierarchy.refinementEntropy n := by
      rw [show (∑ n : Fin depth, if n.val < cut then hierarchy.refinementEntropy n.val else 0) =
        ∑ n ∈ Finset.range depth, if n < cut then hierarchy.refinementEntropy n else 0 from
          Fin.sum_univ_eq_sum_range
            (fun n => if n < cut then hierarchy.refinementEntropy n else 0) depth]
      rw [← Finset.sum_filter, hfilter]
    _ = finiteEntropy (hierarchy.prefixLaw cut hcut).mass :=
      (hierarchy.prefixLaw_entropy cut hcut).symm
    _ = finiteEntropy (p.map (labelRecordOf labels cut)).mass := by
      rw [FiniteLabelHierarchy.ofLawLabels_prefixLaw_mass]

theorem remaining_rate_eq_entropy_sub_prefix (p : FiniteLaw A)
    (labels : ∀ n, A → Label n) (depth cut : ℕ) (hcut : cut ≤ depth)
    (reader : Fin depth → ReaderPair)
    (incident_prefix : ∀ n : Fin depth,
      (reader n = .xy ∨ reader n = .xz) ↔ n.val < cut)
    (complete : Function.Injective (labelRecordOf labels depth)) :
    lawPairingRate p labels depth reader .yz = finiteEntropy p.mass -
      finiteEntropy (p.map (labelRecordOf labels cut)).mass := by
  classical
  have hsum := lawPairingRate_sum p labels depth reader complete
  have hprefix := incident_rate_eq_prefix_entropy p labels depth cut hcut reader incident_prefix
  linarith

end SourceHierarchy
end ConditionalLabels
end MatrixMultiplication

end

end MatrixMultiplicationAllFields
