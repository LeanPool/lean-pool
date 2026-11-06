/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/

module

public import LeanPool.RareSubtreePatterns.Patterns.CutGraft

/-!
# The cut-and-graft bound (Lemma `lem:cut_graft`)

Source lines 2512–2546 (statement) and 2557–2621 (proof); inventory L6.1, P18.

Let `𝓔` be an event on finite plane trees, `(𝓠_m)_{m ∈ I}` a finite family of events with
`𝐏(𝒯 ∈ 𝓠_m) > 0`, `𝓡 ⊆ 𝒜_ℓ` and `τ : 𝓡 → I` such that
(a) `A[S'] ∈ 𝓔` for every `A ∈ 𝓡` and `S' ∈ 𝓠_{τ(A)}`, and
(b) whenever `|T| ≥ ℓ+1`, `T ∈ 𝓔` and `T_{u_{ℓ+1}(T)} ∈ 𝓔`, one has `Cut_ℓ(T) ∈ 𝓡` and
`T_{u_{ℓ+1}(T)} ∈ 𝓠_{τ(Cut_ℓ(T))}`. Then
`𝐏(|𝒯| ≥ ℓ+1, 𝒯 ∈ 𝓔, 𝒯_{u_{ℓ+1}(𝒯)} ∈ 𝓔) ≤ 𝐏(𝒯 ∈ 𝓔) max_{m ∈ I} 𝐏(𝒯 ∈ 𝓔 | 𝒯 ∈ 𝓠_m)`.

* `PlaneTree.lem_cut_graft`: the statement in `ℝ≥0∞`, with conditional probabilities given by
  `ProbabilityTheory.cond` and the maximum `Finset.univ.sup'` over a **nonempty** finite index
  type `I` (the paper writes `max_{m ∈ I}` without stating `I ≠ ∅`; all its applications have
  `I = {0}` or `I = {0, …, k}`).
* `PlaneTree.lem_cut_graft_real`: the same inequality between real probabilities, whose
  left-hand side is the paper's `A_n(ℓ)` set (cf. `PoissonDeclumping.pairProb`).
* `PlaneTree.cut_graft_bound_aux`: the core weighted estimate, for an arbitrary index type and a
  total selector, with any constant `c` such that `𝐏(𝓔 ∩ 𝓠_m) ≤ c 𝐏(𝓠_m)`.

The proof is the paper's: by the cut-and-graft factorization `𝐏(𝒯 = A[S]) = w(A) 𝐏(𝒯 = S)`,
the left-hand side is at most `∑_{A ∈ 𝓡} w(A) 𝐏(𝓔 ∩ 𝓠_{τ(A)})`, while uniqueness of the
decomposition and (a) give `∑_{A ∈ 𝓡} w(A) 𝐏(𝓠_{τ(A)}) ≤ 𝐏(𝓔)`. (The paper groups the sum by
`m` through `W_m = ∑_{τ(A) = m} w(A)`; we sum over `A` directly.)

The inequality holds for every offspring law `μ`: criticality and `μ_1 ≠ 1` (which make
`bienayme μ` a probability measure) are not needed, so they are not assumed.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PoissonDeclumping.PlaneTree

open MarkedTree

/-- Core estimate of Lemma `lem:cut_graft` (total selector `τ`, arbitrary index type, and any
constant `c` with `𝐏(𝓔 ∩ 𝓠_m) ≤ c 𝐏(𝓠_m)` for all `m`). -/
theorem cut_graft_bound_aux (μ : PMF ℕ) (ℓ : ℕ) (E : Set PlaneTree) {I : Type*}
    (Q : I → Set PlaneTree) (R : Set MarkedTree) (hR : R ⊆ cutFamily ℓ) (τ : MarkedTree → I)
    (ha : ∀ A ∈ R, ∀ S ∈ Q (τ A), A.graft S ∈ E)
    (hb : ∀ T : PlaneTree, ℓ + 1 ≤ T.vertexCount → T ∈ E → fringeAt T ℓ ∈ E →
      cut ℓ T ∈ R ∧ fringeAt T ℓ ∈ Q (τ (cut ℓ T)))
    (c : ℝ≥0∞) (hc : ∀ m, bienayme μ (E ∩ Q m) ≤ c * bienayme μ (Q m)) :
    bienayme μ {T | ℓ + 1 ≤ T.vertexCount ∧ T ∈ E ∧ fringeAt T ℓ ∈ E} ≤ c * bienayme μ E := by
  calc bienayme μ {T | ℓ + 1 ≤ T.vertexCount ∧ T ∈ E ∧ fringeAt T ℓ ∈ E}
      ≤ bienayme μ {T | ℓ + 1 ≤ T.vertexCount ∧ cut ℓ T ∈ R ∧
          fringeAt T ℓ ∈ (fun A => E ∩ Q (τ A)) (cut ℓ T)} := by
        apply measure_mono
        rintro T ⟨h1, h2, h3⟩
        obtain ⟨h4, h5⟩ := hb T h1 h2 h3
        exact ⟨h1, h4, h3, h5⟩
    _ = ∑' A, R.indicator (fun A => A.weight μ * bienayme μ (E ∩ Q (τ A))) A :=
        bienayme_cut_mem μ ℓ R hR (fun A => E ∩ Q (τ A))
    _ ≤ ∑' A, R.indicator (fun A => c * (A.weight μ * bienayme μ (Q (τ A)))) A := by
        refine ENNReal.tsum_le_tsum fun A => Set.indicator_le_indicator ?_
        calc A.weight μ * bienayme μ (E ∩ Q (τ A))
            ≤ A.weight μ * (c * bienayme μ (Q (τ A))) := mul_le_mul_right (hc _) _
          _ = c * (A.weight μ * bienayme μ (Q (τ A))) := by ring
    _ = c * ∑' A, R.indicator (fun A => A.weight μ * bienayme μ (Q (τ A))) A := by
        rw [← ENNReal.tsum_mul_left]
        refine tsum_congr fun A => ?_
        by_cases hA : A ∈ R
        · simp only [Set.indicator_of_mem hA]
        · simp only [Set.indicator_of_notMem hA, mul_zero]
    _ = c * bienayme μ {T | ℓ + 1 ≤ T.vertexCount ∧ cut ℓ T ∈ R ∧
          fringeAt T ℓ ∈ (fun A => Q (τ A)) (cut ℓ T)} := by
        rw [bienayme_cut_mem μ ℓ R hR (fun A => Q (τ A))]
    _ ≤ c * bienayme μ E := by
        gcongr
        rintro T ⟨h1, h2, h3⟩
        have := ha _ h2 _ h3
        rwa [graft_cut h1] at this

/-- The event `{|T| ≥ ℓ+1, T ∈ 𝓔, T_{u_{ℓ+1}(T)} ∈ 𝓔}` written with `fringeTrees[ℓ]?`
(as in `PoissonDeclumping.pairProb`) or with `fringeAt`. -/
theorem setOf_pair_eq (ℓ : ℕ) (E : Set PlaneTree) :
    {T : PlaneTree | ℓ + 1 ≤ T.vertexCount ∧ T ∈ E ∧ ∃ U ∈ T.fringeTrees[ℓ]?, U ∈ E} =
      {T | ℓ + 1 ≤ T.vertexCount ∧ T ∈ E ∧ fringeAt T ℓ ∈ E} := by
  ext T
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h1, h2, U, hU, h3⟩
    rw [getElem?_fringeTrees_eq h1, Option.mem_def, Option.some.injEq] at hU
    exact ⟨h1, h2, hU ▸ h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, fringeAt T ℓ, by rw [getElem?_fringeTrees_eq h1]; rfl, h3⟩

/-- **Lemma `lem:cut_graft`** (cut-and-graft bound, source lines 2512–2546). Here `ℓ` is any
natural number (the paper fixes `ℓ ≥ 1`), `fringeAt T ℓ = T.fringeTrees[ℓ]` is
`T_{u_{ℓ+1}(T)}`, `𝒜_ℓ = cutFamily ℓ`, `A[S] = A.graft S`, and the index type `I` is finite and
nonempty. The bound holds for the Bienaymé measure of any offspring law. -/
theorem lem_cut_graft (μ : PMF ℕ) (ℓ : ℕ) (E : Set PlaneTree) {I : Type*} [Fintype I]
    [Nonempty I] (Q : I → Set PlaneTree) (hQ : ∀ m, 0 < bienayme μ (Q m)) (R : Set MarkedTree)
    (hR : R ⊆ cutFamily ℓ) (τ : R → I)
    (ha : ∀ A : R, ∀ S ∈ Q (τ A), A.1.graft S ∈ E)
    (hb : ∀ T : PlaneTree, ℓ + 1 ≤ T.vertexCount → T ∈ E → fringeAt T ℓ ∈ E →
      ∃ hA : cut ℓ T ∈ R, fringeAt T ℓ ∈ Q (τ ⟨cut ℓ T, hA⟩)) :
    bienayme μ {T | ℓ + 1 ≤ T.vertexCount ∧ T ∈ E ∧ ∃ U ∈ T.fringeTrees[ℓ]?, U ∈ E} ≤
      bienayme μ E * Finset.univ.sup' Finset.univ_nonempty
        fun m => ProbabilityTheory.cond (bienayme μ) (Q m) E := by
  classical
  set M := Finset.univ.sup' Finset.univ_nonempty
    fun m => ProbabilityTheory.cond (bienayme μ) (Q m) E
  let τ' : MarkedTree → I := fun A => if h : A ∈ R then τ ⟨A, h⟩ else Classical.arbitrary I
  have hτ' : ∀ (A : MarkedTree) (h : A ∈ R), τ' A = τ ⟨A, h⟩ := fun A h => dite_eq_left h
  rw [setOf_pair_eq, mul_comm]
  refine cut_graft_bound_aux μ ℓ E Q R hR τ' (fun A hA S hS => ?_) (fun T h1 h2 h3 => ?_) M
    (fun m => ?_)
  · rw [hτ' A hA] at hS
    exact ha ⟨A, hA⟩ S hS
  · obtain ⟨hA, hS⟩ := hb T h1 h2 h3
    exact ⟨hA, by rw [hτ' _ hA]; exact hS⟩
  · have hle : ProbabilityTheory.cond (bienayme μ) (Q m) E ≤ M :=
      Finset.le_sup' (fun m => ProbabilityTheory.cond (bienayme μ) (Q m) E) (Finset.mem_univ m)
    calc bienayme μ (E ∩ Q m)
        = bienayme μ (Q m) * ProbabilityTheory.cond (bienayme μ) (Q m) E := by
          rw [ProbabilityTheory.cond_apply MeasurableSet.of_discrete,
            ENNReal.mul_inv_cancel_left (hQ m).ne' (measure_ne_top _ _), Set.inter_comm]
      _ ≤ bienayme μ (Q m) * M := mul_le_mul_right hle _
      _ = M * bienayme μ (Q m) := mul_comm _ _

/-- **Lemma `lem:cut_graft`**, real-valued form: the left-hand side is the paper's
`A_n(ℓ)`-type probability `𝐏(|𝒯| ≥ ℓ+1, 𝒯 ∈ 𝓔, 𝒯_{u_{ℓ+1}(𝒯)} ∈ 𝓔)`. -/
theorem lem_cut_graft_real (μ : PMF ℕ) (ℓ : ℕ) (E : Set PlaneTree) {I : Type*} [Fintype I]
    [Nonempty I] (Q : I → Set PlaneTree) (hQ : ∀ m, 0 < bienayme μ (Q m)) (R : Set MarkedTree)
    (hR : R ⊆ cutFamily ℓ) (τ : R → I)
    (ha : ∀ A : R, ∀ S ∈ Q (τ A), A.1.graft S ∈ E)
    (hb : ∀ T : PlaneTree, ℓ + 1 ≤ T.vertexCount → T ∈ E → fringeAt T ℓ ∈ E →
      ∃ hA : cut ℓ T ∈ R, fringeAt T ℓ ∈ Q (τ ⟨cut ℓ T, hA⟩)) :
    (bienayme μ).real {T | ℓ + 1 ≤ T.vertexCount ∧ T ∈ E ∧ ∃ U ∈ T.fringeTrees[ℓ]?, U ∈ E} ≤
      (bienayme μ).real E * Finset.univ.sup' Finset.univ_nonempty
        fun m => (ProbabilityTheory.cond (bienayme μ) (Q m)).real E := by
  have h := lem_cut_graft μ ℓ E Q hQ R hR τ ha hb
  obtain ⟨m₀, -, hm₀⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (fun m => ProbabilityTheory.cond (bienayme μ) (Q m) E)
  rw [hm₀] at h
  calc (bienayme μ).real {T | ℓ + 1 ≤ T.vertexCount ∧ T ∈ E ∧ ∃ U ∈ T.fringeTrees[ℓ]?, U ∈ E}
      ≤ (bienayme μ E * ProbabilityTheory.cond (bienayme μ) (Q m₀) E).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)) h
    _ = (bienayme μ).real E * (ProbabilityTheory.cond (bienayme μ) (Q m₀)).real E :=
        ENNReal.toReal_mul
    _ ≤ _ := mul_le_mul_of_nonneg_left
        (Finset.le_sup' (fun m => (ProbabilityTheory.cond (bienayme μ) (Q m)).real E)
          (Finset.mem_univ m₀)) ENNReal.toReal_nonneg

end PoissonDeclumping.PlaneTree
