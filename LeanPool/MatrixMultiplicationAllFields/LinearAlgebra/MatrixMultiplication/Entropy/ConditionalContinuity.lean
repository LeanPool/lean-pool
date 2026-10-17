/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Entropy.ConditionalLabels

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-! Finite entropy, rate estimates and ordered asymptotic limits. -/

@[expose] public section

namespace MatrixMultiplicationAllFields



noncomputable section

namespace MatrixMultiplication.ConditionalLabels

open MatrixMultiplication.Foundation Filter
open scoped BigOperators Topology Classical

universe u v w
variable {A : Type u} [Fintype A] {Label : ℕ → Type v}
  [∀ n, Fintype (Label n)]

theorem refinementEntropy_eq_prefix_difference (p : FiniteLaw A)
    (labels : ∀ n, A → Label n) (depth n : ℕ) (hn : n < depth) :
    (FiniteLabelHierarchy.ofLawLabels p labels depth).refinementEntropy n =
      finiteEntropy (p.map (labelRecordOf labels (n + 1))).mass -
        finiteEntropy (p.map (labelRecordOf labels n)).mass := by
  have h := (FiniteLabelHierarchy.ofLawLabels p labels depth).prefixLaw_entropy_succ
    n (Nat.succ_le_of_lt hn)
  rw [FiniteLabelHierarchy.ofLawLabels_prefixLaw_mass,
    FiniteLabelHierarchy.ofLawLabels_prefixLaw_mass] at h
  linarith

theorem tendsto_map_entropy {J : Type w} {filter : Filter J}
    {p : J → FiniteLaw A} {q : FiniteLaw A}
    (mass : ∀ a, Tendsto (fun j => (p j).mass a) filter (𝓝 (q.mass a)))
    {B : Type*} [Fintype B] (label : A → B) :
    Tendsto (fun j => finiteEntropy ((p j).map label).mass) filter
      (𝓝 (finiteEntropy (q.map label).mass)) := by
  apply FiniteLaw.entropy_tendsto
  intro b
  simp only [FiniteLaw.map_mass]
  apply tendsto_finsetSum
  intro a _
  by_cases h : label a = b
  · simpa only [h, ite_true] using mass a
  · simp only [h, ite_false]
    exact tendsto_const_nhds

theorem tendsto_lawPairingRate {J : Type w} {filter : Filter J}
    {p : J → FiniteLaw A} {q : FiniteLaw A}
    (mass : ∀ a, Tendsto (fun j => (p j).mass a) filter (𝓝 (q.mass a)))
    (labels : ∀ n, A → Label n) (depth : ℕ)
    (reader : Fin depth → ReaderPair) (pair : ReaderPair) :
    Tendsto (fun j => lawPairingRate (p j) labels depth reader pair) filter
      (𝓝 (lawPairingRate q labels depth reader pair)) := by
  unfold lawPairingRate pairingRate
  apply tendsto_finsetSum
  intro n _
  by_cases h : reader n = pair
  · simp only [h, ite_true,
      refinementEntropy_eq_prefix_difference _ labels depth n.val n.isLt]
    exact (tendsto_map_entropy mass (labelRecordOf labels (n.val + 1))).sub
      (tendsto_map_entropy mass (labelRecordOf labels n.val))
  · simp only [h, ite_false]
    exact tendsto_const_nhds

theorem exists_rational_law_sequence (p : FiniteLaw A) :
    ∃ q : ℕ → RationalLaw A,
      ∀ a, Tendsto (fun n => (q n).toFiniteLaw.mass a) atTop (𝓝 (p.mass a)) := by
  have hexists (n : ℕ) := p.exists_rational_approximation
    (1 / ((n : ℝ) + 1)) (by positivity)
  choose q _support close using hexists
  refine ⟨q, fun a => ?_⟩
  have hdifference : Tendsto
      (fun n => (q n).toFiniteLaw.mass a - p.mass a) atTop (𝓝 0) := by
    apply squeeze_zero_norm _ tendsto_one_div_add_atTop_nhds_zero_nat
    intro n
    simpa only [Real.norm_eq_abs, RationalLaw.toFiniteLaw_mass] using (close n a).le
  simpa only [sub_add_cancel, zero_add] using hdifference.add_const (p.mass a)

theorem exists_rational_with_strict_margins (p : FiniteLaw A)
    (labels : ∀ n, A → Label n) (depth : ℕ) (reader : Fin depth → ReaderPair)
    {k C target : ℝ}
    (positive : 0 < lawPairingRate p labels depth reader .xy +
      lawPairingRate p labels depth reader .xz)
    (aspect : k * (lawPairingRate p labels depth reader .xy +
      lawPairingRate p labels depth reader .xz) <
      2 * lawPairingRate p labels depth reader .yz)
    (cost : 2 * C < target * (lawPairingRate p labels depth reader .xy +
      lawPairingRate p labels depth reader .xz)) :
    ∃ q : RationalLaw A,
      0 < lawPairingRate q.toFiniteLaw labels depth reader .xy +
        lawPairingRate q.toFiniteLaw labels depth reader .xz ∧
      k * (lawPairingRate q.toFiniteLaw labels depth reader .xy +
        lawPairingRate q.toFiniteLaw labels depth reader .xz) <
        2 * lawPairingRate q.toFiniteLaw labels depth reader .yz ∧
      2 * C < target * (lawPairingRate q.toFiniteLaw labels depth reader .xy +
        lawPairingRate q.toFiniteLaw labels depth reader .xz) := by
  obtain ⟨q, hq⟩ := exists_rational_law_sequence p
  have hincident := (tendsto_lawPairingRate hq labels depth reader .xy).add
    (tendsto_lawPairingRate hq labels depth reader .xz)
  have hhidden := tendsto_lawPairingRate hq labels depth reader .yz
  have hpos := hincident.eventually_const_lt positive
  have haspect := (hincident.const_mul k).eventually_lt (hhidden.const_mul 2) aspect
  have hcost := (hincident.const_mul target).eventually_const_lt cost
  obtain ⟨n, hnpos, hnaspect, hncost⟩ := (hpos.and (haspect.and hcost)).exists
  exact ⟨q n, hnpos, hnaspect, hncost⟩

end MatrixMultiplication.ConditionalLabels

end

end MatrixMultiplicationAllFields
