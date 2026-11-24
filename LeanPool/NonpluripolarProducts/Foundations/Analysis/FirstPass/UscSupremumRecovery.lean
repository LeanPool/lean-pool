/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.Envelopes

/-!
# Recovering finite values of a regularized supremum

At a finite value of the upper-semicontinuous regularization of a pointwise
supremum, one can approach the base point while choosing one member of the
family whose value approaches the regularized value.  This is the selection
step in the Fatou proof for locally bounded PSH suprema.  It is purely
topological and order-theoretic; no plurisubharmonicity is assumed here.
-/

@[expose] public section

open Filter Metric Set
open scoped Topology

namespace SGPT.Foundations.Analysis.FirstPass

noncomputable section

variable {X : Type*} [PseudoMetricSpace X]

/-- A strict lower bound for the regularization is achieved by the original
function at some point of every prescribed neighborhood. -/
theorem exists_mem_lt_of_lt_uscRegularization {f : X → EReal} {x : X}
    {a : EReal} (ha : a < uscRegularization f x) {U : Set X} (hU : U ∈ 𝓝 x) :
    ∃ y ∈ U, a < f y := by
  have hsup : a < ⨆ y ∈ U, f y :=
    ha.trans_le (uscRegularization_le_localSup f hU)
  rw [lt_iSup_iff] at hsup
  obtain ⟨y, hy⟩ := hsup
  rw [lt_iSup_iff] at hy
  obtain ⟨hyU, hyf⟩ := hy
  exact ⟨y, hyU, hyf⟩

/-- For a pointwise supremum, the witnessing value can be chosen from one
actual member of the family. -/
theorem exists_mem_mem_lt_of_lt_uscRegularization_sSup
    {F : Set (X → EReal)} {x : X} {a : EReal}
    (ha : a < uscRegularization (sSup F) x) {U : Set X} (hU : U ∈ 𝓝 x) :
    ∃ y ∈ U, ∃ f ∈ F, a < f y := by
  obtain ⟨y, hyU, hy⟩ := exists_mem_lt_of_lt_uscRegularization ha hU
  simp only [sSup_apply, iSup_subtype, lt_iSup_iff] at hy
  obtain ⟨f, hfF, hfy⟩ := hy
  exact ⟨y, hyU, f, hfF, hfy⟩

/-- Quantitative recovery at a finite value: in an arbitrarily small ball one
can choose a family member whose value lies in the matching real window. -/
theorem exists_family_value_between_of_uscRegularization_sSup_eq_coe
    {F : Set (X → EReal)} {x : X} {a ε : ℝ}
    (hx : uscRegularization (sSup F) x = (a : EReal)) (hε : 0 < ε) :
    ∃ y ∈ ball x ε, ∃ f ∈ F,
      ((a - ε : ℝ) : EReal) < f y ∧ f y < ((a + ε : ℝ) : EReal) := by
  let g := uscRegularization (sSup F)
  have hax : ((a : ℝ) : EReal) = g x := hx.symm
  have hupper_at : g x < ((a + ε : ℝ) : EReal) := by
    rw [← hax, EReal.coe_lt_coe_iff]
    linarith
  have hupper_nhds : {y | g y < ((a + ε : ℝ) : EReal)} ∈ 𝓝 x :=
    (upperSemicontinuous_uscRegularization (sSup F)) x _ hupper_at
  have hball : ball x ε ∈ 𝓝 x := ball_mem_nhds x hε
  have hU : ball x ε ∩ {y | g y < ((a + ε : ℝ) : EReal)} ∈ 𝓝 x :=
    inter_mem hball hupper_nhds
  have hlower : ((a - ε : ℝ) : EReal) < g x := by
    rw [← hax, EReal.coe_lt_coe_iff]
    linarith
  obtain ⟨y, hyU, f, hfF, hfy⟩ :=
    exists_mem_mem_lt_of_lt_uscRegularization_sSup hlower hU
  refine ⟨y, hyU.1, f, hfF, hfy, ?_⟩
  exact (le_uscRegularization (sSup F) y |>.trans'
    (le_sSup hfF y)).trans_lt hyU.2

/-- Sequential form of finite-value recovery.  Both the moving centers and
the selected family values converge to the prescribed base data. -/
theorem exists_sequences_tendsto_uscRegularization_sSup_eq_coe
    {F : Set (X → EReal)} {x : X} {a : ℝ}
    (hx : uscRegularization (sSup F) x = (a : EReal)) :
    ∃ y : ℕ → X, ∃ f : ℕ → X → EReal,
      Tendsto y atTop (𝓝 x) ∧ (∀ n, f n ∈ F) ∧
        Tendsto (fun n => f n (y n)) atTop (𝓝 (a : EReal)) := by
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hεpos : ∀ n, 0 < ε n := by
    intro n
    dsimp [ε]
    positivity
  have hchoice : ∀ n, ∃ y ∈ ball x (ε n), ∃ f ∈ F,
      ((a - ε n : ℝ) : EReal) < f y ∧ f y < ((a + ε n : ℝ) : EReal) :=
    fun n => exists_family_value_between_of_uscRegularization_sSup_eq_coe
      hx (hεpos n)
  choose y hy f hfF hlower hupper using hchoice
  have hε : Tendsto ε atTop (𝓝 0) := by
    simpa only [ε] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  refine ⟨y, f, ?_, hfF, ?_⟩
  · apply Metric.tendsto_atTop.2
    intro δ hδ
    have hsmall : ∀ᶠ n : ℕ in atTop, ε n < δ :=
      hε.eventually (gt_mem_nhds hδ)
    obtain ⟨N, hN⟩ := eventually_atTop.1 hsmall
    exact ⟨N, fun n hn => (hy n).trans (hN n hn)⟩
  · have hlower_tendsto : Tendsto (fun n => ((a - ε n : ℝ) : EReal))
        atTop (𝓝 (a : EReal)) := by
      apply EReal.tendsto_coe.mpr
      simpa using tendsto_const_nhds.sub hε
    have hupper_tendsto : Tendsto (fun n => ((a + ε n : ℝ) : EReal))
        atTop (𝓝 (a : EReal)) := by
      apply EReal.tendsto_coe.mpr
      simpa using tendsto_const_nhds.add hε
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower_tendsto hupper_tendsto
      (Eventually.of_forall fun n => (hlower n).le)
      (Eventually.of_forall fun n => (hupper n).le)

/-- A finite value of the upper regularization is approached by values of the original function. -/
theorem exists_sequence_tendsto_uscRegularization_eq_coe
    {f : X → EReal} {x : X} {a : ℝ}
    (hx : uscRegularization f x = (a : EReal)) :
    ∃ y : ℕ → X, Tendsto y atTop (𝓝 x) ∧
      Tendsto (fun n => f (y n)) atTop (𝓝 (a : EReal)) := by
  have hs : uscRegularization (sSup ({f} : Set (X → EReal))) x = (a : EReal) := by
    simpa only [sSup_singleton] using hx
  obtain ⟨y, g, hy, hg, hlim⟩ := exists_sequences_tendsto_uscRegularization_sSup_eq_coe hs
  refine ⟨y, hy, hlim.congr fun n => ?_⟩
  rw [Set.mem_singleton_iff.mp (hg n)]

end

end SGPT.Foundations.Analysis.FirstPass
