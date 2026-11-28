/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.MeasureSpaces.Besov.Nikolskii
public import LeanPool.FunctionSpaces.ApproximationSpaces.Nikolskii

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Embedding theorems for Besov spaces

Let `S` be a scheme of functions with the Nikolskii property of dimension `D ≥ 0` for a
finite measure `μ`, and write `α = D (1/p - 1/r)` for `1 ≤ p ≤ r ≤ ∞`.  Then:

* **the Besov embedding** (`MemBesov.exists_inclusion_eq_of_nikolskii`): for `s > α`,
  every `f ∈ B^s_{p,q}` lies in `L_r` and belongs to `B^{s - α}_{r,q}`; with a norm bound
  (`exists_inclusion_eq_of_nikolskii`);
* **into `L_∞`** (the case `r = ∞`, `α = D/p`), for `s > D/p`;
* **into bounded continuous functions** (`MemBesov.exists_boundedContinuous`): if moreover
  `μ` charges every nonempty open set, every `f ∈ B^s_{p,q}` with `s > D/p` has a bounded
  continuous representative.

All three are the abstract Nikolskii transfer theorem
(`ApproximationScheme.exists_preimage_of_nikolskii`) for `X = L_p`, `Y = L_r` and the
inclusion `L_r ↪ L_p`; the pulled-back scheme is again `S` in `L_r`
(`FunctionScheme.comap_toLp_of_le`).  For the last one, `f` in `L_∞` with positive smoothness
is a limit of approximants, which are continuous, and the continuous functions are closed in
`L_∞`.

The limiting case `s = α` is not covered: the transfer theorem needs the strict inequality.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal BoundedContinuousFunction

namespace FunctionScheme

variable {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
  {S : FunctionScheme Ω} {μ : Measure Ω} [IsFiniteMeasure μ] {D : ℝ} {p r : ℝ≥0∞}
  [Fact (1 ≤ p)] [Fact (1 ≤ r)] {s : ℝ} {q : ℝ≥0∞}

/-- **The Besov embedding**, with a norm bound: for `1 ≤ p ≤ r ≤ ∞`, `α = D(1/p - 1/r) < s`
and `1 ≤ q ≤ ∞`, there is `K < ∞` such that every `f ∈ B^s_{p,q}` is the inclusion of some
`g ∈ L_r` with `‖g‖_{B^{s-α}_{r,q}} ≤ K ‖f‖_{B^s_{p,q}}` (dyadic quasi-norms). -/
theorem exists_inclusion_eq_of_nikolskii (h : S.HasNikolskii μ D) (hD : 0 ≤ D) (hpr : p ≤ r)
    (hs : nikolskiiExponent D p r < s) (hq : 1 ≤ q) :
    ∃ K : ℝ≥0∞, K ≠ ∞ ∧ ∀ f : Lp ℂ p μ, S.MemBesov μ p s q f →
      ∃ g : Lp ℂ r μ, Lp.inclusionOfExponentLe (𝕜 := ℝ) μ hpr g = f ∧
        (S.toLp μ r).approxNormDyadic (s - nikolskiiExponent D p r) q g ≤
          K * (S.toLp μ p).approxNormDyadic s q f := by
  obtain ⟨C, hC, hN⟩ := h.liftBound hpr
  have hα := nikolskiiExponent_nonneg hD (Fact.out : 1 ≤ p) hpr
  refine ⟨ApproximationScheme.nikolskiiConst C (nikolskiiExponent D p r) s,
    ApproximationScheme.nikolskiiConst_ne_top C hs, fun f hf => ?_⟩
  obtain ⟨g, hg, hle⟩ := ApproximationScheme.exists_preimage_of_nikolskii
    (Lp.inclusionOfExponentLe_injective hpr) hN hC hα hs hq hf
  refine ⟨g, hg, ?_⟩
  rwa [comap_toLp_of_le hpr] at hle

/-- **The Besov embedding** `B^s_{p,q} ↪ B^{s - D(1/p - 1/r)}_{r,q}` for `p ≤ r` and
`s > D(1/p - 1/r)`: every `f ∈ B^s_{p,q}` is the inclusion of some `g ∈ L_r` lying in
`B^{s - D(1/p-1/r)}_{r,q}`. -/
theorem MemBesov.exists_inclusion_eq_of_nikolskii (h : S.HasNikolskii μ D) (hD : 0 ≤ D)
    (hpr : p ≤ r) (hs : nikolskiiExponent D p r < s) (hq : 1 ≤ q) {f : Lp ℂ p μ}
    (hf : S.MemBesov μ p s q f) :
    ∃ g : Lp ℂ r μ, Lp.inclusionOfExponentLe (𝕜 := ℝ) μ hpr g = f ∧
      S.MemBesov μ r (s - nikolskiiExponent D p r) q g := by
  obtain ⟨C, hC, hN⟩ := h.liftBound hpr
  have hα := nikolskiiExponent_nonneg hD (Fact.out : 1 ≤ p) hpr
  obtain ⟨g, hg, hmem⟩ := ApproximationScheme.MemApprox.exists_preimage_of_nikolskii
    (Lp.inclusionOfExponentLe_injective hpr) hN hC hα hs hq hf
  refine ⟨g, hg, ?_⟩
  rwa [comap_toLp_of_le hpr] at hmem

/-- **Embedding into `L_∞`**: for `s > D/p`, every `f ∈ B^s_{p,q}` is the inclusion of some
`g ∈ L_∞` lying in `B^{s - D/p}_{∞,q}`. -/
theorem MemBesov.exists_inclusion_eq_top (h : S.HasNikolskii μ D) (hD : 0 ≤ D)
    (hs : D * p.toReal⁻¹ < s) (hq : 1 ≤ q) {f : Lp ℂ p μ} (hf : S.MemBesov μ p s q f) :
    ∃ g : Lp ℂ ∞ μ, Lp.inclusionOfExponentLe (𝕜 := ℝ) μ le_top g = f ∧
      S.MemBesov μ ∞ (s - D * p.toReal⁻¹) q g := by
  have := hf.exists_inclusion_eq_of_nikolskii h hD (le_top : p ≤ ∞)
    (by rwa [nikolskiiExponent_top]) hq
  rwa [nikolskiiExponent_top] at this

/-- **Embedding into bounded continuous functions**: if `μ` charges every nonempty open set
and `s > D/p`, every `f ∈ B^s_{p,q}` has a bounded continuous representative. -/
theorem MemBesov.exists_boundedContinuous [μ.IsOpenPosMeasure] (h : S.HasNikolskii μ D)
    (hD : 0 ≤ D) (hs : D * p.toReal⁻¹ < s) (hq : 1 ≤ q) {f : Lp ℂ p μ}
    (hf : S.MemBesov μ p s q f) :
    ∃ a : Ω →ᵇ ℂ, Lp.inclusionOfExponentLe (𝕜 := ℝ) μ le_top
      (BoundedContinuousFunction.toLp (E := ℂ) ∞ μ ℝ a) = f := by
  obtain ⟨g, hg, hmem⟩ := hf.exists_inclusion_eq_top h hD hs hq
  have hcl : g ∈ closure (⋃ n, S.toLp μ ∞ n) :=
    ApproximationScheme.mem_closure_iUnion_of_memApprox hq (sub_pos.2 hs) hmem
  have hsub : (⋃ n, S.toLp μ ∞ n) ⊆
      Set.range (BoundedContinuousFunction.toLp (E := ℂ) ∞ μ ℝ : (Ω →ᵇ ℂ) → Lp ℂ ∞ μ) := by
    rintro _ ⟨_, ⟨n, rfl⟩, a, -, rfl⟩
    exact ⟨a, rfl⟩
  obtain ⟨a, ha⟩ := (BoundedContinuousFunction.isClosed_range_toLp_top (μ := μ) (𝕜 := ℝ)
    (E := ℂ)).closure_subset_iff.2 hsub hcl
  exact ⟨a, by rw [ha, hg]⟩

end FunctionScheme
