/-
Copyright (c) 2026 George Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Lee
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.MultiplicativeErgodic.Induction

/-!
# Existence of the Oseledets decomposition

The existence half of Theorem \ref{mainres} (stated in the Introduction, proved in Section 6) of
`proof_met.tex`: the semi-invertible Oseledets decomposition for a strongly measurable,
forward-integrable random linear dynamical system on a separable Banach space. The full
`mainres` (`ProofMet/Main.lean`) adds the uniqueness of the decomposition and the backward
characterisation of the fast spaces.
-/

@[expose] public section

namespace MultiplicativeErgodic

open MeasureTheory Filter TopologicalSpace

variable {Ω X : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [MeasurableSpace X]

/-- **Theorem \ref{mainres}, existence.** Indexing is from `0`: `lam i` is the paper's `λ_{i+1}`,
`E i` its
fast space `E_{i+1}`, and `Lval` the number `L` of distinct Lyapunov exponents.

* `lam i` is the `i`-th distinct exponent `Cocycle.lambda i` (for `i < L`), possibly `-∞` for the
  last one; `L ≥ 1`, and `λ_{i+2}` exists (`i + 2 ≤ L`) exactly when `m_{i+1} = mult i ≠ 0`.
* For each `i` with `i + 2 ≤ L`, `E i` is measurable and equivariant, of dimension `m_{i+1}`, and
  grows at the uniform rate `lam i`, both in operator norm restricted to `E i ω` and in
  slowest-vector growth.
* For each `l` with `l + 2 ≤ L`, `X = (⨁_{i ≤ l} E_i(ω)) ⊕ V_{l+1}(ω)` with `V_{l+1}` equivariant,
  `V_{l+1}(ω) = {x : λ_ω(x) ≤ lam (l+1)}`, and `P_{l+1}` the projection onto `V_{l+1}` along
  `⨁_{i ≤ l} E_i`, strongly measurable and tempered.
* The decomposition is nontrivial (`L ≥ 2`) exactly when `𝓛` is quasicompact.

**Statement corrected** (earlier corrections 1--3 below; 4--8 made while starting the proof).

1. It used to carry `[MeasurableSpace (Submodule ℝ X)]` as an *instance* hypothesis and assert
   `Measurable (E i)` against it. Instance binders are universally quantified, so that asserted
   measurability for **every** σ-algebra on `Submodule ℝ X`, the discrete one included — and
   against the discrete σ-algebra a family that is injective on a non-measurable set has a
   non-measurable preimage, so the statement was false. This is precisely the defect
   `exists_measurable_retract_false` was written to guard against. The subspaces now live in
   `GrassmannianFin X (mdim i + 1)`, which carries the project's canonical Borel structure
   (`instMeasurableSpaceGrassmannianFin`); writing the dimension as `mdim i + 1` is what makes
   the `NeZero` instance that structure needs available without a side hypothesis.
2. `Measurable (P i)` was *norm* measurability of an operator family. `𝓑(X)` is not separable,
   the paper says "strongly measurable", and the construction (a pointwise limit) gives only
   `ω ↦ P i ω x` measurable for each fixed `x`. Corrected accordingly — see
   `ProofMet/StrongMeasurability.lean`.
3. `Measurable (V i)` had the same problem as (1) and is dropped: the slow spaces are pinned as
   `LinearMap.range (P (l+1) ω)`, so their measurability is inherited from `P`.
4. **The statement was false for every quasicompact cocycle.** It asserted
   `V (l+1) ω = {x : λ_ω(x) ≤ lam l}` together with `IsCompl (⨆_{i≤l} E i ω) (V (l+1) ω)`, but
   `E l ω ≠ 0` grows at rate `lam l`, so lies in that set, contradicting the complement. The slow
   space after `E_0, …, E_l` is `{λ ≤ lam (l+1)}`; accordingly the decomposition at level `l` is
   asserted for `l + 2 ≤ L` (when `lam (l+1)` exists), not `l < L`.
5. `lam` and `Lval` were free: nothing tied them to the Lyapunov exponents, so `Lval = 2` would
   always have done. They are now pinned to `Cocycle.lambda` and `Cocycle.mult`, as are the
   dimensions `mdim i + 1 = m_{i+1}`.
6. Equivariance of `E i` and `V (l+1)`, and that `P (l+1)` kills `⨆_{i≤l} E i` and is idempotent
   (i.e. is the projection *along* the fast spaces), were stated in the paper but missing here.
7. The last exponent may be `-∞` (a finite-rank cocycle), so `lam` is `EReal`-valued and the
   rates use `logEReal`.
8. `[Nontrivial X]`: `E` is a total function into `𝒢_{mdim i + 1}X`, which is empty for `X = 0`. -/
theorem mainres_existence (R : Cocycle Ω X) [SeparableSpace X] [BorelSpace X] [CompleteSpace X]
    [Nontrivial X] :
    ∃ (Lval : ℕ∞) (lam : ℕ → EReal) (mdim : ℕ → ℕ)
      (E : ∀ i : ℕ, Ω → GrassmannianFin X (mdim i + 1))
      (V : ℕ → Ω → Submodule ℝ X) (P : ℕ → Ω → X →L[ℝ] X),
      -- the exponents and how many there are
      1 ≤ Lval ∧
      (∀ i : ℕ, (i : ℕ∞) < Lval → ∀ᵐ ω ∂(R.μ), R.lambda i ω = lam i) ∧
      (∀ i : ℕ, ((i + 2 : ℕ) : ℕ∞) ≤ Lval ↔ ∀ᵐ ω ∂(R.μ), R.mult i ω ≠ 0) ∧
      ((2 : ℕ∞) ≤ Lval ↔ R.IsQuasicompact) ∧
      -- measurability and temperedness
      (∀ i, Measurable (E i)) ∧
      (∀ i, ∀ x : X, Measurable fun ω => P i ω x) ∧
      (∀ i, R.IsTempered (P i)) ∧
      -- the fast spaces
      (∀ i : ℕ, ((i + 2 : ℕ) : ℕ∞) ≤ Lval → ∀ᵐ ω ∂(R.μ),
        R.mult i ω = mdim i + 1 ∧
        Submodule.map (R.L ω : X →ₗ[ℝ] X) ((E i ω).1 : Submodule ℝ X)
          = ((E i (R.σ ω)).1 : Submodule ℝ X) ∧
        Tendsto (fun n : ℕ => logEReal
            ‖(R.iterate n ω).comp (((E i ω).1 : Submodule ℝ X)).subtypeL‖ / (n : EReal))
          atTop (nhds (lam i)) ∧
        Tendsto (fun n : ℕ => logEReal
            (growth (R.iterate n ω) ((E i ω).1 : Submodule ℝ X)) / (n : EReal))
          atTop (nhds (lam i))) ∧
      -- the decompositions
      (∀ l : ℕ, ((l + 2 : ℕ) : ℕ∞) ≤ Lval → ∀ᵐ ω ∂(R.μ),
        IsCompl (⨆ i ∈ Finset.range (l + 1), ((E i ω).1 : Submodule ℝ X)) (V (l + 1) ω) ∧
        Submodule.map (R.L ω : X →ₗ[ℝ] X) (V (l + 1) ω) ≤ V (l + 1) (R.σ ω) ∧
        (P (l + 1) ω).comp (P (l + 1) ω) = P (l + 1) ω ∧
        V (l + 1) ω = LinearMap.range ((P (l + 1) ω : X →ₗ[ℝ] X)) ∧
        (∀ x ∈ ⨆ i ∈ Finset.range (l + 1), ((E i ω).1 : Submodule ℝ X), P (l + 1) ω x = 0) ∧
        (V (l + 1) ω : Set X) = {x : X | R.lambdaAt ω x ≤ lam (l + 1)}) := by
  classical
  choose lam hlam using R.exists_lambda_ae_eq
  -- a junk level, used where the decomposition has ended
  obtain ⟨x₀, hx₀⟩ := exists_ne (0 : X)
  let e₀ : GrassmannianFin X 1 :=
    ⟨Submodule.span ℝ {x₀}, inferInstance, finrank_span_singleton hx₀⟩
  let f₀ : GrassmannianFin X 0 := ⟨⊥, inferInstance, finrank_bot ℝ X⟩
  let v₀ : GrassmannianCofin X 0 :=
    ⟨⟨⊤, Submodule.closedComplemented_top⟩, inferInstance, Module.finrank_zero_of_subsingleton⟩
  let D₀ : LevelData Ω X := ⟨0, 0, fun _ => e₀, fun _ => f₀, fun _ => v₀, fun _ => 0⟩
  let base : LevelData Ω X :=
    if h : ∃ D : LevelData Ω X, R.IsLevel lam 0 D ∧
        ∀ᵐ ω ∂(R.μ), ((D.F ω).1 : Submodule ℝ X) = ((D.E ω).1 : Submodule ℝ X)
    then Classical.choose h else D₀
  let step : ℕ → LevelData Ω X → LevelData Ω X := fun l D =>
    if h : ∃ D' : LevelData Ω X, R.IsLevel lam (l + 1) D' ∧
        ∀ᵐ ω ∂(R.μ), ((D'.F ω).1 : Submodule ℝ X) = ((D.F ω).1 : Submodule ℝ X) ⊔
          ((D'.E ω).1 : Submodule ℝ X)
    then Classical.choose h else D₀
  let seq : ℕ → LevelData Ω X := fun l => Nat.rec (motive := fun _ => LevelData Ω X) base step l
  have hseq0 : seq 0 = base := rfl
  have hseqs : ∀ l, seq (l + 1) = step l (seq l) := fun l => rfl
  -- measurability and temperedness hold at every level, junk or not
  have hbasicD : ∀ D : LevelData Ω X, (∃ l, R.IsLevel lam l D) ∨ D = D₀ →
      Measurable D.E ∧ (∀ x, Measurable fun ω => D.Q ω x) ∧ R.IsTempered D.Q := by
    rintro D (⟨l, hl⟩ | rfl)
    · exact ⟨hl.E_meas, hl.Q_meas, hl.Q_temp⟩
    · refine ⟨measurable_const, fun x => measurable_const, ?_⟩
      change ∀ᵐ ω ∂(R.μ), _
      refine Eventually.of_forall fun ω => ?_
      change Tendsto (fun n : ℕ => Real.log ‖(0 : X →L[ℝ] X)‖ / n) atTop (nhds 0)
      simp only [norm_zero, Real.log_zero, zero_div]
      exact tendsto_const_nhds
  have hbasic : ∀ l, Measurable (seq l).E ∧ (∀ x, Measurable fun ω => (seq l).Q ω x) ∧
      R.IsTempered (seq l).Q := by
    intro l
    refine hbasicD _ ?_
    cases l with
    | zero =>
      rw [hseq0]
      simp only [base]
      split_ifs with h
      · exact Or.inl ⟨0, (Classical.choose_spec h).1⟩
      · exact Or.inr rfl
    | succ l =>
      rw [hseqs]
      simp only [step]
      split_ifs with h
      · exact Or.inl ⟨l + 1, (Classical.choose_spec h).1⟩
      · exact Or.inr rfl
  -- the multiplicities are nonzero up to a point, and no further
  have hmono : ∀ i j, j ≤ i → (∀ᵐ ω ∂(R.μ), R.mult i ω ≠ 0) → ∀ᵐ ω ∂(R.μ), R.mult j ω ≠ 0 := by
    intro i j hji hi
    induction i with
    | zero => rwa [Nat.le_zero.1 hji]
    | succ i ih =>
      rcases Nat.lt_or_eq_of_le hji with h | h
      · exact ih (Nat.lt_succ_iff.1 h) (hi.mono fun ω hω => R.mult_ne_zero_of_succ ω hω)
      · rwa [h]
  -- the levels exist as long as the multiplicities are nonzero
  have hgood : ∀ l, (∀ᵐ ω ∂(R.μ), R.mult l ω ≠ 0) → R.IsLevel lam l (seq l) ∧
      (l = 0 → ∀ᵐ ω ∂(R.μ), (((seq l).F ω).1 : Submodule ℝ X) = (((seq l).E ω).1 : Submodule ℝ X)) ∧
      (∀ l', l = l' + 1 → ∀ᵐ ω ∂(R.μ), (((seq l).F ω).1 : Submodule ℝ X) =
        (((seq l').F ω).1 : Submodule ℝ X) ⊔ (((seq l).E ω).1 : Submodule ℝ X)) := by
    intro l hl
    induction l with
    | zero =>
      have hex := R.exists_level_zero hlam ((R.isQuasicompact_iff_mult_zero).2 hl)
      have hb : seq 0 = Classical.choose hex := by rw [hseq0]; simp only [base, dite_eq_left hex]
      rw [hb]
      exact ⟨(Classical.choose_spec hex).1, fun _ => (Classical.choose_spec hex).2,
        fun l' h => absurd h (Nat.succ_ne_zero l').symm⟩
    | succ l ih =>
      have hprev := (ih (hmono (l + 1) l (Nat.le_succ l) hl)).1
      have hex := R.exists_level_succ hlam hprev hl
      have hb : seq (l + 1) = Classical.choose hex := by rw [hseqs]; simp only [step,
        dite_eq_left hex]
      rw [hb]
      refine ⟨(Classical.choose_spec hex).1, fun h => absurd h (Nat.succ_ne_zero l), ?_⟩
      intro l' hl'
      obtain rfl : l' = l := by omega
      exact (Classical.choose_spec hex).2
  have hsum : ∀ l, (∀ᵐ ω ∂(R.μ), R.mult l ω ≠ 0) → ∀ᵐ ω ∂(R.μ),
      (((seq l).F ω).1 : Submodule ℝ X) =
        ⨆ i ∈ Finset.range (l + 1), (((seq i).E ω).1 : Submodule ℝ X) := by
    intro l hl
    induction l with
    | zero =>
      filter_upwards [(hgood 0 hl).2.1 rfl] with ω h
      rw [h, Finset.range_one, Finset.iSup_singleton]
    | succ l ih =>
      filter_upwards [ih (hmono (l + 1) l (Nat.le_succ l) hl), (hgood (l + 1) hl).2.2 l rfl]
        with ω h1 h2
      rw [h2, h1]
      conv_rhs => rw [Finset.range_add_one, Finset.iSup_insert]
      exact sup_comm _ _
  -- the number of exponents
  let Lval : ℕ∞ :=
    if h : ∃ i, ¬ ∀ᵐ ω ∂(R.μ), R.mult i ω ≠ 0 then ((Nat.find h + 1 : ℕ) : ℕ∞) else ⊤
  have hLval : ∀ i : ℕ, ((i + 2 : ℕ) : ℕ∞) ≤ Lval ↔ ∀ᵐ ω ∂(R.μ), R.mult i ω ≠ 0 := by
    intro i
    by_cases h : ∃ i, ¬ ∀ᵐ ω ∂(R.μ), R.mult i ω ≠ 0
    · simp only [Lval, dite_eq_left h, Nat.cast_le]
      constructor
      · intro hi
        have hlt : i < Nat.find h := by omega
        exact not_not.1 (Nat.find_min h hlt)
      · intro hi
        by_contra hle
        exact Nat.find_spec h (hmono i _ (by omega) hi)
    · simp only [Lval, dite_eq_right h, le_top, true_iff]
      push Not at h
      exact h i
  refine ⟨Lval, lam, fun i => (seq i).d, fun i => (seq i).E,
    fun l ω => LinearMap.range ((seq (l - 1)).Q ω : X →ₗ[ℝ] X), fun l => (seq (l - 1)).Q,
    ?_, fun i _ => hlam i, hLval, ?_, fun i => (hbasic i).1, fun i x => (hbasic (i - 1)).2.1 x,
    fun i => (hbasic (i - 1)).2.2, ?_, ?_⟩
  · by_cases h : ∃ i, ¬ ∀ᵐ ω ∂(R.μ), R.mult i ω ≠ 0
    · simp only [Lval, dite_eq_left h]
      exact_mod_cast Nat.le_add_left 1 _
    · simp only [Lval, dite_eq_right h, le_top]
  · rw [R.isQuasicompact_iff_mult_zero, ← hLval 0]
    norm_num
  · intro i hi
    have hL := (hgood i ((hLval i).1 hi)).1
    filter_upwards [hL.E_dim, hL.E_equiv, hL.E_norm, hL.E_growth] with ω h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  · intro l hl
    have hm := (hLval l).1 hl
    have hL := (hgood l hm).1
    filter_upwards [hL.Q_idem, hL.Q_ker, hL.Q_equiv, hL.Q_range, hL.slow_char, hsum l hm]
      with ω hid hker heq hrange hchar hs
    change IsCompl _ (LinearMap.range ((seq l).Q ω : X →ₗ[ℝ] X)) ∧
      Submodule.map (R.L ω : X →ₗ[ℝ] X) (LinearMap.range ((seq l).Q ω : X →ₗ[ℝ] X)) ≤
        LinearMap.range ((seq l).Q (R.σ ω) : X →ₗ[ℝ] X) ∧
      ((seq l).Q ω).comp ((seq l).Q ω) = (seq l).Q ω ∧
      LinearMap.range ((seq l).Q ω : X →ₗ[ℝ] X) = LinearMap.range ((seq l).Q ω : X →ₗ[ℝ] X) ∧
      (∀ x ∈ ⨆ i ∈ Finset.range (l + 1), (((seq i).E ω).1 : Submodule ℝ X), (seq l).Q ω x = 0) ∧
      ((LinearMap.range ((seq l).Q ω : X →ₗ[ℝ] X) : Submodule ℝ X) : Set X) =
        {x : X | R.lambdaAt ω x ≤ lam (l + 1)}
    have hfix : ∀ z, (seq l).Q ω ((seq l).Q ω z) = (seq l).Q ω z := fun z =>
      congrArg (fun T : X →L[ℝ] X => T z) hid
    rw [← hs, ← hker]
    refine ⟨⟨?_, ?_⟩, ?_, hid, rfl, fun x hx => hx, by rw [hrange]; exact hchar⟩
    · rw [Submodule.disjoint_def]
      rintro x hxk ⟨z, rfl⟩
      simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hxk ⊢
      rwa [hfix] at hxk
    · rw [codisjoint_iff, eq_top_iff]
      rintro x -
      refine Submodule.mem_sup.2 ⟨x - (seq l).Q ω x, ?_, (seq l).Q ω x, ⟨x, rfl⟩,
        sub_add_cancel _ _⟩
      simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, map_sub, hfix, sub_self]
    · rintro _ ⟨_, ⟨z, rfl⟩, rfl⟩
      exact ⟨R.L ω z, by simpa using congrArg (fun T : X →L[ℝ] X => T z) heq⟩

end MultiplicativeErgodic
