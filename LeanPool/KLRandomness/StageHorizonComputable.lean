/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.StageHorizon
public import LeanPool.KLRandomness.PoolAdviceComputable
public import Mathlib.Computability.PartrecCode

/-!
# The uniform horizon-search program

For any uniformly computable rational functions `u` and `v`, one fixed
partial-recursive program searches for the first horizon passing the two
stage inequalities. Its input is the finite construction parameter together
with the bounded integer advice. Neither limiting probability nor a modulus
of convergence is supplied to the program.

The finite parameter type may contain the trial rank and the selected sparse
candidate index. All constants and the programs computing `u` and `v` remain
fixed outside the input quantifier.
-/

@[expose] public section

namespace Klr.StageHorizon

open Filter RationalComputability
open scoped Topology

variable {α : Type*}

/-- The exact Boolean verifier. The second component of the input is the
integer advice; the search horizon is a separate argument. -/
def check (error : ℚ) (u v : α → ℕ → ℚ) (input : α × ℕ) (horizon : ℕ) : Bool :=
  decide (u input.1 horizon < 3 * error) &&
    decide (((input.2 : ℚ) - 1) * error < v input.1 horizon)

theorem check_eq_true (error : ℚ) (u v : α → ℕ → ℚ)
    (input : α × ℕ) (horizon : ℕ) :
    check error u v input horizon = true ↔
      Accepted error (u input.1) (v input.1) input.2 horizon := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq, Accepted]

/-- The verifier is uniformly computable in the construction parameter,
integer advice, and proposed horizon. -/
theorem computable_check [Primcodable α] (error : ℚ) {u v : α → ℕ → ℚ}
    (hu : Computable₂ u) (hv : Computable₂ v) :
    Computable₂ (check error u v) := by
  have ha : Computable (fun p : (α × ℕ) × ℕ => p.1.1) :=
    Computable.fst.comp Computable.fst
  have hb : Computable (fun p : (α × ℕ) × ℕ => (p.1.2 : ℚ)) :=
    primrec_rat_natCast.to_comp.comp (Computable.snd.comp Computable.fst)
  have hthreshold := primrec_rat_mul.to_comp.comp
    (primrec_rat_sub.to_comp.comp hb (Computable.const 1)) (Computable.const error)
  exact Primrec.and.to_comp.comp
    (PoolAdvice.computable_rat_lt.comp (hu.comp ha Computable.snd)
      (Computable.const (3 * error)))
    (PoolAdvice.computable_rat_lt.comp hthreshold (hv.comp ha Computable.snd))

/-- Search successively through the natural-number horizons and return the
first one passing the rational tests. -/
def search (error : ℚ) (u v : α → ℕ → ℚ) (input : α × ℕ) : Part ℕ :=
  Nat.rfind fun horizon => Part.some (check error u v input horizon)

theorem partrec_search [Primcodable α] (error : ℚ) {u v : α → ℕ → ℚ}
    (hu : Computable₂ u) (hv : Computable₂ v) :
    Partrec (search error u v) :=
  Partrec.rfind (computable_check error hu hv).partrec.to₂

/-- A returned horizon satisfies the two finite tests. -/
theorem search_spec {error : ℚ} {u v : α → ℕ → ℚ} {input : α × ℕ}
    {horizon : ℕ} (h : horizon ∈ search error u v input) :
    Accepted error (u input.1) (v input.1) input.2 horizon := by
  apply (check_eq_true error u v input horizon).mp
  exact (Part.mem_some_iff.mp (Nat.rfind_spec h)).symm

/-- The search returns the first accepted horizon, not an arbitrary witness. -/
theorem search_min {error : ℚ} {u v : α → ℕ → ℚ} {input : α × ℕ}
    {horizon : ℕ} (h : horizon ∈ search error u v input) :
    ∀ n < horizon, ¬ Accepted error (u input.1) (v input.1) input.2 n := by
  intro n hn hnaccept
  have hnfalse := Nat.rfind_min h hn
  have hntrue := (check_eq_true error u v input n).mpr hnaccept
  simp only [hntrue, Part.mem_some_iff, Bool.false_eq_true] at hnfalse

/-- Halting requires precisely a finite accepted horizon. The limiting
analytic argument is used to establish this existence separately. -/
theorem search_dom_iff (error : ℚ) (u v : α → ℕ → ℚ) (input : α × ℕ) :
    (search error u v input).Dom ↔
      ∃ horizon, Accepted error (u input.1) (v input.1) input.2 horizon := by
  constructor
  · intro hdom
    obtain ⟨horizon, hhorizon⟩ := Part.dom_iff_mem.mp hdom
    exact ⟨horizon, search_spec hhorizon⟩
  · rintro ⟨horizon, hhorizon⟩
    apply Nat.rfind_dom.mpr
    refine ⟨horizon, ?_, fun {_} _ => trivial⟩
    exact Part.mem_some_iff.mpr ((check_eq_true error u v input horizon).mpr hhorizon).symm

/-- Use the canonical primitive encoding for the complete program input. -/
def encodeInput [Primcodable α] (input : α × ℕ) : ℕ :=
  @Encodable.encode (α × ℕ) (inferInstance : Primcodable (α × ℕ)).toEncodable input

/-- There is one fixed program for every parameter and every advice value.
The output is the horizon itself, so it need not be included in the input. -/
theorem exists_search_program [Primcodable α] (error : ℚ) {u v : α → ℕ → ℚ}
    (hu : Computable₂ u) (hv : Computable₂ v) :
    ∃ code : Nat.Partrec.Code, ∀ input : α × ℕ,
      code.eval (encodeInput input) = search error u v input := by
  obtain ⟨code, hcode⟩ := Nat.Partrec.Code.exists_code.mp (partrec_search error hu hv)
  refine ⟨code, fun input => ?_⟩
  rw [hcode]
  simp only [encodeInput, Encodable.encodek, Part.coe_some, Part.bind_some]
  exact Part.map_id' (fun _ => rfl) _

/-- The bounded advice provided by the analytic limit argument makes the
actual search halt, and its output satisfies both the early-rank and tail
bounds. No limit is evaluated by the search. -/
theorem exists_bounded_advice_search {error : ℚ} (herror : 0 < error)
    {u v : α → ℕ → ℚ} (input : α) {uLimit vLimit : ℝ} {protectedCount : ℕ}
    (hu : Tendsto (fun n => (u input n : ℝ)) atTop (𝓝 uLimit))
    (hv : Tendsto (fun n => (v input n : ℝ)) atTop (𝓝 vLimit))
    (huLimit : uLimit ≤ 2 * (error : ℝ)) (hvLimit : 0 ≤ vLimit)
    (hbound : vLimit ≤ protectedCount) :
    ∃ advice, advice ≤ adviceBound error protectedCount ∧
      (search error u v (input, advice)).Dom ∧
      ∀ horizon, horizon ∈ search error u v (input, advice) →
        Accepted error (u input) (v input) advice horizon ∧
        vLimit - (v input horizon : ℝ) < 2 * (error : ℝ) := by
  obtain ⟨advice, hadvice, _, heventually, htail⟩ :=
    exists_bounded_advice herror hu hv huLimit hvLimit hbound
  refine ⟨advice, hadvice, (search_dom_iff error u v (input, advice)).mpr
    heventually.exists, ?_⟩
  intro horizon hhorizon
  exact ⟨search_spec hhorizon, htail horizon (search_spec hhorizon)⟩

/-- The fixed program realizes the analytic construction for every parameter
whose two rational sequences have the requisite limits. The program is
chosen before the parameter, the limits, and the bounded advice. -/
theorem exists_uniform_bounded_horizon_program [Primcodable α]
    {error : ℚ} (herror : 0 < error)
    {u v : α → ℕ → ℚ} (hu : Computable₂ u) (hv : Computable₂ v) :
    ∃ code : Nat.Partrec.Code,
      (∀ input : α × ℕ, code.eval (encodeInput input) = search error u v input) ∧
      ∀ (input : α) (uLimit vLimit : ℝ) (protectedCount : ℕ),
        Tendsto (fun n => (u input n : ℝ)) atTop (𝓝 uLimit) →
        Tendsto (fun n => (v input n : ℝ)) atTop (𝓝 vLimit) →
        uLimit ≤ 2 * (error : ℝ) → 0 ≤ vLimit → vLimit ≤ protectedCount →
        ∃ advice, advice ≤ adviceBound error protectedCount ∧
          ∃ horizon, horizon ∈ code.eval (encodeInput (input, advice)) ∧
            Accepted error (u input) (v input) advice horizon ∧
            vLimit - (v input horizon : ℝ) < 2 * (error : ℝ) := by
  obtain ⟨code, hcode⟩ := exists_search_program error hu hv
  refine ⟨code, hcode, ?_⟩
  intro input uLimit vLimit protectedCount huconv hvconv huLimit hvLimit hbound
  obtain ⟨advice, hadvice, hdom, hspec⟩ :=
    exists_bounded_advice_search herror input huconv hvconv huLimit hvLimit hbound
  obtain ⟨horizon, hhorizon⟩ := Part.dom_iff_mem.mp hdom
  exact ⟨advice, hadvice, horizon, by rwa [hcode], hspec horizon hhorizon⟩

end Klr.StageHorizon
