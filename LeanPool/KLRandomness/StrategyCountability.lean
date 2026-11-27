/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.ComputableRational
public import LeanPool.KLRandomness.EffectiveNormalizationStrategy
public import LeanPool.KLRandomness.ScanMeasure
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Computability.PartrecCode
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Countably many total computable-real betting strategies

The construction may enumerate total strategies non-effectively.  Countability
does not supply a computable enumeration of the total programs.  We prove it
by choosing a computable rational approximation for each real capital function;
two capitals with the same approximation are equal.

The final almost-everywhere quantifier interchange uses this actual countable
strategy type, rather than assuming that a chosen program list covers it.
-/

@[expose] public section

namespace Klr

open MeasureTheory Filter
open scoped Topology

/-- Computable functions between any two primitively encodable types form a countable type. -/
theorem countable_computable_functions {α β : Type*} [Primcodable α] [Primcodable β] :
    Countable {f : α → β // Computable f} := by
  classical
  let code : {f : α → β // Computable f} → Nat.Partrec.Code :=
    fun f => (Nat.Partrec.Code.exists_code.mp f.property).choose
  apply Function.Injective.countable (f := code)
  intro f g h
  apply Subtype.ext
  funext a
  have hf := congrFun (Nat.Partrec.Code.exists_code.mp f.property).choose_spec
    (Encodable.encode a)
  have hg := congrFun (Nat.Partrec.Code.exists_code.mp g.property).choose_spec
    (Encodable.encode a)
  change (code f).eval (Encodable.encode a) = _ at hf
  change (code g).eval (Encodable.encode a) = _ at hg
  rw [← h] at hg
  simpa using hf.symm.trans hg

/-- A uniformly vanishing rational error bound determines the real capital uniquely. -/
theorem capital_eq_of_common_approximation {d e : List Bool → ℝ}
    (q : List Bool → ℕ → ℚ)
    (hd : ∀ v n, |(q v n : ℝ) - d v| ≤ (1 / 2 : ℝ) ^ n)
    (he : ∀ v n, |(q v n : ℝ) - e v| ≤ (1 / 2 : ℝ) ^ n) : d = e := by
  funext v
  have hle (n : ℕ) : |d v - e v| ≤ 2 * (1 / 2 : ℝ) ^ n := by
    calc
      |d v - e v| = |(d v - (q v n : ℝ)) + ((q v n : ℝ) - e v)| := by ring_nf
      _ ≤ |d v - (q v n : ℝ)| + |(q v n : ℝ) - e v| := abs_add_le _ _
      _ ≤ (1 / 2 : ℝ) ^ n + (1 / 2 : ℝ) ^ n :=
        add_le_add (by simpa only [abs_sub_comm] using hd v n) (he v n)
      _ = _ := by ring
  have hlim : Tendsto (fun n : ℕ => 2 * (1 / 2 : ℝ) ^ n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)).const_mul 2
  exact sub_eq_zero.mp (abs_eq_zero.mp
    (le_antisymm (ge_of_tendsto hlim (Eventually.of_forall hle)) (abs_nonneg _)))

theorem ScanRule.ext_query {π τ : ScanRule} (h : π.query = τ.query) : π = τ := by
  cases π
  cases τ
  cases h
  rfl

theorem CapitalProcess.ext_value {d e : CapitalProcess} (h : d.value = e.value) : d = e := by
  cases d
  cases e
  cases h
  rfl

/-- The total strategies are countable, including their uniformly computable real capital. -/
instance : Countable BettingStrategy := by
  classical
  have := countable_computable_functions (α := List Bool) (β := ℕ)
  have := countable_computable_functions (α := List Bool × ℕ) (β := ℚ)
  let data : BettingStrategy →
      {f : List Bool → ℕ // Computable f} ×
      {q : List Bool × ℕ → ℚ // Computable q} := fun s =>
    (⟨s.scan.query, s.scan.computable_query⟩,
      ⟨fun p => s.computable_capital.choose p.1 p.2,
        RationalComputability.computable_rat_of_numDen s.computable_capital.choose_spec.1⟩)
  apply Function.Injective.countable (f := data)
  intro s t h
  have hscan : s.scan = t.scan :=
    ScanRule.ext_query (congrArg (fun p => p.1.val) h)
  have hq : (fun p : List Bool × ℕ => s.computable_capital.choose p.1 p.2) =
      (fun p : List Bool × ℕ => t.computable_capital.choose p.1 p.2) :=
    congrArg (fun p => p.2.val) h
  have hvalue : s.capital.value = t.capital.value := by
    apply capital_eq_of_common_approximation s.computable_capital.choose
      s.computable_capital.choose_spec.2
    intro v n
    rw [show s.computable_capital.choose v n = t.computable_capital.choose v n from
      congrFun hq (v, n)]
    exact t.computable_capital.choose_spec.2 v n
  have hcapital : s.capital = t.capital := CapitalProcess.ext_value hvalue
  cases s
  cases t
  cases hscan
  cases hcapital
  rfl

/-- A separate null success set for each total strategy suffices simultaneously for all of them. -/
theorem ae_kolmogorovLovelandRandom_iff (μ : Measure Cantor) :
    (∀ᵐ X ∂μ, KolmogorovLovelandRandom X) ↔
      ∀ s : BettingStrategy, ∀ᵐ X ∂μ, ¬s.Succeeds X :=
  ae_all_iff

/-- It suffices to defeat all the normalized strategies almost surely. -/
theorem ae_kolmogorovLovelandRandom_of_normalized (μ : Measure Cantor)
    (h : ∀ s : BettingStrategy, ∀ᵐ X ∂μ, ¬s.normalize.Succeeds X) :
    ∀ᵐ X ∂μ, KolmogorovLovelandRandom X := by
  apply (ae_kolmogorovLovelandRandom_iff μ).mpr
  intro s
  filter_upwards [h s] with X hX
  exact fun hs => hX (s.normalize_preserves_success hs)

end Klr
