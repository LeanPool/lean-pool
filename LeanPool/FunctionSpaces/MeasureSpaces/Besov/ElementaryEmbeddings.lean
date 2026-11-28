/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.MeasureSpaces.Besov.Basic
public import LeanPool.FunctionSpaces.ApproximationSpaces.Transfer

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Elementary embeddings of Besov spaces

Three embeddings follow from the abstract theory without any property of the scheme:

* **in the smoothness and fine indices**: `B^s_{p,q} ⊆ B^t_{p,r}` for `0 ≤ t < s`, or `t = s`
  and `q ≤ r` (`FunctionScheme.MemBesov.mono`), from `ApproximationScheme.MemApprox.mono`;
* **in the integrability**: for `p ≤ r`, `B^s_{r,q} ⊆ B^s_{p,q}` through the inclusion
  `L_r ↪ L_p` (`FunctionScheme.MemBesov.inclusion`), with
  `‖f‖_{B^s_{p,q}} ≤ ‖ι‖ ‖f‖_{B^s_{r,q}}`, by functoriality: the inclusion maps approximants
  to approximants;
* **from the sup norm**: the uniform Besov space embeds into every `B^s_{p,q}`
  (`FunctionScheme.MemBesov.of_sup`), again by functoriality, along `toLp`.

The embeddings in the opposite direction, from `B^s_{p,q}` into `B^{s'}_{r,q}` with `r > p`,
cost smoothness and need a Nikolskii inequality for the scheme
(`FunctionSpaces.MeasureSpaces.Besov.Embeddings`).
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal BoundedContinuousFunction

namespace FunctionScheme

variable {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
  {S : FunctionScheme Ω} {μ : Measure Ω} [IsFiniteMeasure μ] {p r : ℝ≥0∞} [Fact (1 ≤ p)]
  [Fact (1 ≤ r)] {s t : ℝ} {q q' : ℝ≥0∞}

/-- **Embeddings in the smoothness and fine indices**: for `0 ≤ t` and `t < s`, or `t = s`
and `q ≤ q'`, `B^s_{p,q} ⊆ B^t_{p,q'}`. -/
theorem MemBesov.mono (hq : 1 ≤ q) (hq' : 1 ≤ q') (ht : 0 ≤ t)
    (h : t < s ∨ (t = s ∧ q ≤ q')) {f : Lp ℂ p μ} (hf : S.MemBesov μ p s q f) :
    S.MemBesov μ p t q' f :=
  ApproximationScheme.MemApprox.mono hq hq' ht h hf

/-- **Embedding in the integrability**, norm form: for `p ≤ r`,
`‖ι f‖_{B^s_{p,q}} ≤ ‖ι‖ ‖f‖_{B^s_{r,q}}` with `ι : L_r ↪ L_p`. -/
theorem besovNorm_inclusion_le (hpr : p ≤ r) (f : Lp ℂ r μ) :
    S.besovNorm μ p s q (Lp.inclusionOfExponentLe (𝕜 := ℝ) μ hpr f) ≤
      ‖Lp.inclusionOfExponentLe (E := ℂ) (𝕜 := ℝ) μ hpr‖ₑ * S.besovNorm μ r s q f :=
  ApproximationScheme.approxNorm_map_le _ (fun _ _ hg => inclusion_mem_toLp hpr hg) f

/-- **Embedding in the integrability**: for `p ≤ r`, `B^s_{r,q} ⊆ B^s_{p,q}` through the
inclusion `L_r ↪ L_p`. -/
theorem MemBesov.inclusion (hpr : p ≤ r) {f : Lp ℂ r μ} (hf : S.MemBesov μ r s q f) :
    S.MemBesov μ p s q (Lp.inclusionOfExponentLe (𝕜 := ℝ) μ hpr f) :=
  ApproximationScheme.MemApprox.map _ (fun _ _ hg => inclusion_mem_toLp hpr hg) hf

/-- **Embedding of the uniform Besov space**: a bounded continuous function in the
approximation space of `S` in the sup norm lies in every `B^s_{p,q}`. -/
theorem MemBesov.of_sup {a : Ω →ᵇ ℂ} (ha : S.MemApprox s q a) :
    S.MemBesov μ p s q (BoundedContinuousFunction.toLp (E := ℂ) p μ ℝ a) :=
  ApproximationScheme.MemApprox.map _ (fun _ _ hb => toLp_mem_toLp hb) ha

end FunctionScheme
