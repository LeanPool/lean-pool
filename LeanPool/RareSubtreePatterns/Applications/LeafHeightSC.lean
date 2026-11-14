/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/

module

public import LeanPool.RareSubtreePatterns.Applications.TreeSurgery
public import LeanPool.RareSubtreePatterns.Applications.TreeCriteria
public import LeanPool.RareSubtreePatterns.Patterns.CutGraftBound
public import LeanPool.RareSubtreePatterns.Bridge.CriterionS
public import LeanPool.RareSubtreePatterns.RootDeclumping.LeafHeightMark
public import LeanPool.RareSubtreePatterns.RootDeclumping.LeafHeightSkeleton

/-!
# Leaf-height marks: Assumptions (S) and (C) (Lemmas `lem:S_lh` and `lem:C_lh`)

Section 7.2 of the paper, source lines 3029–3236 (inventory L7.3 (i), L7.5, P23 (use), P25).
Marks: `G_k(T) = 1{λ_∅(T) ≥ k}` and `Ghat_k = 1{k_∅ ≥ κ + 1} 1{∃ child c, λ_∅(T_c) ≥ k}`
(`RootDeclumping.lhDeclumpedMark μ k`), with `κ = min{j ≥ 1 : μ_j > 0}` (`LeafHeight.kappa μ`),
`π_k = P(λ_∅(𝒯) ≥ k)` (`LeafHeight.piSeq μ k`), `π̂_k = P(Ghat_k(𝒯) = 1)` and
`c = 1 - κ μ_κ` (`LeafHeight.cConst μ`).

## Main statements

* `lem_S_lh` (**Lemma `lem:S_lh`(i)**): if `k_n = n^{o(1)}` (`κ = 1`), resp. `κ^{k_n} = n^{o(1)}`
  (`κ ≥ 2`), then `(G_k)` satisfies Assumption (S) along `(k_n)` with respect to
  `M_n = max 1 ⌊n^{1-η}⌋₊`, `η ∈ (0, 1 - 1/α)`: Lemma `lem:critM` applied to the
  decomposition `RootDeclumping.lhSkeleton` (P23, already proved) with
  `E_k[C_k + L_k] ≤ C k + 1` resp. `≤ C κ^k`. Part (ii) (`E[N_{k_n}(𝒯^n)] ∼ n π_{k_n}`) is
  Corollary `cor:SM`(ii) and is not included.
* `le_rootLeafHeight_replaceAt`: if `λ_∅(T) ≥ k`, re-grafting at a vertex `u` a tree `S` with
  `λ_∅(S) ≥ min(λ_∅(T_u), k)` keeps `λ_∅ ≥ k` (P25, condition (a) of the cut-and-graft lemma).
* `pair_lhDeclumped_le` (**P25**): one constant `C` with
  `P(|𝒯| ≥ ℓ+1, Ghat_k(𝒯) = 1, Ghat_k(𝒯_{u_{ℓ+1}}) = 1) ≤ C π_k π̂_k` for all `k` and `ℓ ≥ 1`.
* `lem_C_lh` (**Lemma `lem:C_lh`**): if `c > 0`, then `(Ghat_k)` satisfies Assumption (C) for every
  level sequence and every cutoff with `M_n = o(n)`.

## Departure in the proof of P25

The paper's selector is `τ(A) = 0` if a root child other than the one above `⋆` witnesses the
root event, and `τ(A) = (k - h(A))_+` otherwise (`h(A)` the depth of `⋆` below that child). We use
instead the *minimal admissible* selector `τ(A) = min{m ≤ k : λ_∅(S) ≥ m ⇒ A[S] ∈ {Ghat_k = 1}}`.
Condition (a) of Lemma `lem:cut_graft` then holds by definition, and condition (b) follows from
`le_rootLeafHeight_replaceAt`: on the double event `𝒯 = A[S]`, `m = min(λ_∅(S), k)` is admissible,
so `τ(A) ≤ λ_∅(S)`. The rest (Lemma `lem:lh_conditional_mark` and `π̂_k ≥ b π_k`) is as in the
paper. No case distinction on the witness, and no notion of depth of `⋆`, is needed.
-/

@[expose] public section

open MeasureTheory Filter Asymptotics ProbabilityTheory
open scoped Topology ENNReal

namespace PoissonDeclumping

namespace PlaneTree

/-- If `λ_∅(T) ≥ k` and the vertex `u` of DFS index `ℓ` is replaced by a tree `S` with
`λ_∅(S) ≥ min(λ_∅(T_u), k)`, then still `λ_∅ ≥ k`: the new leaves are at depth
`depth(u) + (depth in S) ≥ k`, since `λ_∅(T_u) ≥ k - depth(u)`. -/
theorem le_rootLeafHeight_replaceAt : ∀ (k : ℕ) {T : PlaneTree} {ℓ : ℕ} {S : PlaneTree},
    k ≤ rootLeafHeight T → ℓ < T.vertexCount →
    min (rootLeafHeight (fringeAt T ℓ)) k ≤ rootLeafHeight S →
    k ≤ rootLeafHeight (replaceAt T ℓ S)
  | 0, _, _, _, _, _, _ => Nat.zero_le _
  | k + 1, T, ℓ, S, hT, hℓ, hS => by
    rcases ℓ with _ | ℓ
    · rw [replaceAt_zero]
      rw [fringeAt_zero, min_eq_right hT] at hS
      exact hS
    obtain ⟨ts⟩ := T
    rw [vertexCount_node_eq] at hℓ
    obtain ⟨pre, t, post, q, rfl, hq, rfl⟩ := exists_append_of_lt_forestSize ts ℓ (by omega)
    rw [fringeAt_node_append pre post t hq] at hS
    rw [replaceAt_node_append pre post t hq]
    rw [succ_le_rootLeafHeight_iff] at hT ⊢
    simp only [children_node] at hT ⊢
    refine ⟨by simp, fun U hU => ?_⟩
    rcases List.mem_append.1 hU with hU | hU
    · exact hT.2 U (List.mem_append_left _ hU)
    rcases List.mem_cons.1 hU with rfl | hU
    · exact le_rootLeafHeight_replaceAt k (hT.2 t (by simp)) hq
        ((min_le_min_left _ (Nat.le_succ k)).trans hS)
    · exact hT.2 U (by simp [hU])

end PlaneTree

namespace Applications

open PlaneTree LeafHeight RootDeclumping

variable {μ : PMF ℕ}

/-! ### Lemma `lem:S_lh`(i) -/

/-- `E_0[C_0 + L_0] = 1` (no skeleton, one frontier vertex: the root). -/
theorem lintegral_lhSkeleton_zero_le (μ : PMF ℕ) :
    ∫⁻ ω, ((ω.2.1 + ω.2.2.length : ℕ) : ℝ≥0∞) ∂(lhSkeleton μ 0) ≤ 1 := by
  rw [lintegral_lhSkeleton]
  simp only [skelSize_zero, gen_zero, List.length_singleton, zero_add, Nat.cast_one,
    lintegral_one]
  exact cond_univ_le_one _ _

/-- The moment bound of the leaf-height skeleton for all levels (P23): one `C > 0` with
`E_k[C_k + L_k] ≤ C k + 1` if `κ = 1` and `≤ C κ^k` if `κ ≥ 2`, for every `k ≥ 0`. -/
theorem lhSkeleton_moment_le (hc : IsCritical μ) (h1 : μ 1 ≠ 1) :
    ∃ C : ℝ, 0 < C ∧
      (kappa μ = 1 → ∀ k : ℕ,
        ∫⁻ ω, ((ω.2.1 : ℝ≥0∞) + (ω.2.2.length : ℝ≥0∞)) ∂(lhSkeleton μ k) ≤
          ENNReal.ofReal (C * k + 1)) ∧
      (2 ≤ kappa μ → ∀ k : ℕ,
        ∫⁻ ω, ((ω.2.1 : ℝ≥0∞) + (ω.2.2.length : ℝ≥0∞)) ∂(lhSkeleton μ k) ≤
          ENNReal.ofReal (C * (kappa μ : ℝ) ^ k)) := by
  obtain ⟨C, hC, hC1, hC2⟩ := lintegral_lhSkeleton_le hc h1
  have hcast : ∀ k, ∫⁻ ω, ((ω.2.1 : ℝ≥0∞) + (ω.2.2.length : ℝ≥0∞)) ∂(lhSkeleton μ k) =
      ∫⁻ ω, ((ω.2.1 + ω.2.2.length : ℕ) : ℝ≥0∞) ∂(lhSkeleton μ k) := fun k => by
    simp only [Nat.cast_add]
  refine ⟨C, hC, fun hκ k => ?_, fun hκ k => ?_⟩
  · rw [hcast]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · refine (lintegral_lhSkeleton_zero_le μ).trans ?_
      simp
    · refine (hC1 hκ k hk).trans (ENNReal.ofReal_le_ofReal ?_)
      linarith
  · rw [hcast]
    exact hC2 hκ k

/-- **Lemma `lem:S_lh`(i)** (source lines 3053–3130): let `(k_n)` be such that `k_n = n^{o(1)}` if
`κ = 1`, and `κ^{k_n} = n^{o(1)}` if `κ ≥ 2` (used through the upper halves `≤ n^δ`, for every
`δ > 0`, eventually along admissible sizes). Then for every `η ∈ (0, 1 - 1/α)` the leaf-height
marks `G_k = 1{λ_∅ ≥ k}` satisfy Assumption (S) along `(k_n)` with respect to
`M_n = max 1 ⌊n^{1-η}⌋₊` (`= ⌊n^{1-η}⌋` for `n ≥ 1`). -/
theorem lem_S_lh {α : ℝ} {a : ℕ → ℝ} (hT : StableToolkit μ α a) {η : ℝ}
    (hη : 0 < η ∧ η < 1 - 1 / α) {k : ℕ → ℕ}
    (hk1 : kappa μ = 1 → ∀ δ : ℝ, 0 < δ → ∀ᶠ n in admissibleSizes μ, (k n : ℝ) ≤ (n : ℝ) ^ δ)
    (hk2 : 2 ≤ kappa μ → ∀ δ : ℝ, 0 < δ → ∀ᶠ n in admissibleSizes μ,
      (kappa μ : ℝ) ^ k n ≤ (n : ℝ) ^ δ) :
    StructuralMicroscopic μ a (fun j T => j ≤ rootLeafHeight T) k
      (fun n => max 1 ⌊(n : ℝ) ^ (1 - η)⌋₊) := by
  have hc := hT.critical
  have h1 := hT.nondegenerate
  obtain ⟨C, hC, hC1, hC2⟩ := lhSkeleton_moment_le hc h1
  refine Bridge.critM hT hη (lhSkeleton μ) (fun j _ => lhSkeleton_skeleton hc h1 j)
    fun δ hδ => ?_
  rcases (one_le_kappa hc h1).eq_or_lt with hκ | hκ
  · filter_upwards [eventually_mul_add_le_rpow inf_le_left (hk1 hκ.symm) hC.le 1 δ hδ]
      with n hn
    exact (hC1 hκ.symm (k n)).trans (ENNReal.ofReal_le_ofReal hn)
  · filter_upwards [eventually_mul_add_le_rpow inf_le_left (hk2 hκ) hC.le 0 δ hδ] with n hn
    refine (hC2 hκ (k n)).trans (ENNReal.ofReal_le_ofReal ?_)
    linarith

/-! ### Lemma `lem:C_lh` -/

/-- **P25** (source lines 3190–3234, before the final use of `c > 0`): there is one `C > 0` such
that for all `k` and all `ℓ ≥ 1`,
`P(|𝒯| ≥ ℓ+1, Ghat_k(𝒯) = 1, Ghat_k(𝒯_{u_{ℓ+1}(𝒯)}) = 1) ≤ C π_k π̂_k`. Lemma `lem:cut_graft` is
applied with `𝓔 = {Ghat_k = 1}`, `𝓠_m = {λ_∅ ≥ m}` (`0 ≤ m ≤ k`) and the minimal admissible
selector, then Lemma `lem:lh_conditional_mark`. -/
theorem pair_lhDeclumped_le (hc : IsCritical μ) (h1 : μ 1 ≠ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ k ℓ : ℕ, 1 ≤ ℓ →
      (bienayme μ).real {T | ℓ + 1 ≤ T.vertexCount ∧ lhDeclumpedMark μ k T ∧
          ∃ U ∈ T.fringeTrees[ℓ]?, lhDeclumpedMark μ k U} ≤
        C * piSeq μ k * (bienayme μ).real {T | lhDeclumpedMark μ k T} := by
  obtain ⟨C, hC, hL⟩ := lem_lh_conditional_mark hc h1
  refine ⟨C, hC, fun k ℓ hℓ => ?_⟩
  set E : Set PlaneTree := {T | lhDeclumpedMark μ k T} with hE
  set Q : Fin (k + 1) → Set PlaneTree := fun m => {S | (m : ℕ) ≤ rootLeafHeight S} with hQ
  -- admissible levels for a cut tree
  set adm : MarkedTree → Set ℕ :=
    fun A => {m | m ≤ k ∧ ∀ S, m ≤ rootLeafHeight S → A.graft S ∈ E} with hadm
  set R : Set MarkedTree := {A | A.pos = ℓ ∧ (adm A).Nonempty} with hR
  have hmem : ∀ A : R, sInf (adm A.1) ∈ adm A.1 := fun A => Nat.sInf_mem A.2.2
  let τ : R → Fin (k + 1) := fun A => ⟨sInf (adm A.1), Nat.lt_succ_of_le (hmem A).1⟩
  have hQpos : ∀ m, 0 < bienayme μ (Q m) := fun m => by
    simp only [hQ]
    rw [bienayme_le_rootLeafHeight hc h1]
    exact ENNReal.ofReal_pos.mpr (piSeq_pos hc h1 m)
  have h := lem_cut_graft_real μ ℓ E Q hQpos R (fun A hA => mem_cutFamily_iff.2 hA.1) τ
    (fun A S hS => (hmem A).2 S hS) (fun T h1T h2 h3 => by
      have hprop : min (rootLeafHeight (fringeAt T ℓ)) k ∈ adm (cut ℓ T) := by
        refine ⟨min_le_right _ _, fun S hS => ?_⟩
        rw [graft_cut_eq_replaceAt (by omega)]
        exact declumpedMark_replaceAt (B := lhDegrees μ) (G := fun T => k ≤ rootLeafHeight T)
          S h2 hℓ (by omega) fun t q ht hq heq =>
            le_rootLeafHeight_replaceAt k ht hq (by rw [heq]; exact hS)
      refine ⟨⟨cut_pos (by omega), _, hprop⟩, ?_⟩
      exact (Nat.sInf_le hprop).trans (min_le_left _ _))
  refine h.trans ?_
  rw [mul_comm (C * piSeq μ k)]
  refine mul_le_mul_of_nonneg_left (Finset.sup'_le _ _ fun m _ => ?_) measureReal_nonneg
  have hπm := piSeq_pos hc h1 m
  have hQm : (bienayme μ).real (Q m) = piSeq μ m := bienayme_real_le_rootLeafHeight hc h1 m
  have hinter : Q m ∩ E = {T | lhDeclumpedMark μ k T ∧ (m : ℕ) ≤ rootLeafHeight T} := by
    ext T
    simp only [hQ, hE, Set.mem_inter_iff, Set.mem_ofPred_eq]
    exact and_comm
  rw [measureReal_def, cond_apply MeasurableSet.of_discrete, ENNReal.toReal_mul,
    ENNReal.toReal_inv, ← measureReal_def, ← measureReal_def, hQm, hinter,
    inv_mul_le_iff₀ hπm]
  calc (bienayme μ).real {T | lhDeclumpedMark μ k T ∧ (m : ℕ) ≤ rootLeafHeight T}
      ≤ C * piSeq μ k * piSeq μ m := hL m k (Nat.lt_succ_iff.1 m.2)
    _ = piSeq μ m * (C * piSeq μ k) := by ring

/-- **Lemma `lem:C_lh`** (source lines 3183–3236): if `c = 1 - κ μ_κ > 0`, then for every level
sequence `(k_n)` and every cutoff sequence with `M_n = o(n)`, the declumped leaf-height marks
`Ghat_k` satisfy Assumption (C): `Â_n(ℓ) ≤ C' π̂_{k_n}²` uniformly in `ℓ ≥ 1` (with
`C' = C / b`, `b = P(k_∅ ≥ κ + 1) > 0`), hence `∑_{ℓ=1}^{M_n} Â_n(ℓ) ≤ C' M_n π̂_{k_n}² =
o(n π̂_{k_n}²)`. -/
theorem lem_C_lh (hc : IsCritical μ) (h1 : μ 1 ≠ 1) (hcpos : 0 < cConst μ) (k M : ℕ → ℕ)
    (hM : (fun n => (M n : ℝ)) =o[atTop] (fun n => (n : ℝ))) :
    NonClustering μ (fun j => lhDeclumpedMark μ j) k M := by
  obtain ⟨C, hC, hpair⟩ := pair_lhDeclumped_le hc h1
  have hb : 0 < bB μ (lhDegrees μ) := bB_lhDegrees_pos hc hcpos
  refine nonClustering_of_pairSum_le hM (K := 0) (C := C / bB μ (lhDegrees μ))
    (div_pos hC hb).le
    (fun ε hε => Eventually.of_forall fun n => by
      rw [zero_mul]
      exact mul_nonneg hε.le (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))) fun n => ?_
  set πh := markProb μ (fun j => lhDeclumpedMark μ j) k n with hπh
  have hπh0 : 0 ≤ πh := measureReal_nonneg
  have hbπ : bB μ (lhDegrees μ) * piSeq μ (k n) ≤ πh := bB_mul_le_lh_declumped hc h1 (k n)
  have hπk : piSeq μ (k n) ≤ πh / bB μ (lhDegrees μ) := by
    rw [le_div_iff₀ hb]
    linarith
  calc ∑ ℓ ∈ Finset.Icc 1 (M n), pairProb μ (fun j => lhDeclumpedMark μ j) k n ℓ
      ≤ ∑ ℓ ∈ Finset.Icc 1 (M n), C / bB μ (lhDegrees μ) * πh ^ 2 := by
        refine Finset.sum_le_sum fun ℓ hℓ => ?_
        calc pairProb μ (fun j => lhDeclumpedMark μ j) k n ℓ
            ≤ C * piSeq μ (k n) * πh := hpair (k n) ℓ (Finset.mem_Icc.1 hℓ).1
          _ ≤ C * (πh / bB μ (lhDegrees μ)) * πh := by gcongr
          _ = C / bB μ (lhDegrees μ) * πh ^ 2 := by ring
    _ = 0 * πh + C / bB μ (lhDegrees μ) * (M n : ℝ) * πh ^ 2 := by
        simp only [Finset.sum_const, Nat.card_Icc, add_tsub_cancel_right, nsmul_eq_mul]
        ring

/-- **Lemma `lem:C_lh`** for every cutoff sequence (`IsCutoff M`). -/
theorem lem_C_lh_of_isCutoff (hc : IsCritical μ) (h1 : μ 1 ≠ 1) (hcpos : 0 < cConst μ)
    (k : ℕ → ℕ) {M : ℕ → ℕ} (hM : IsCutoff M) :
    NonClustering μ (fun j => lhDeclumpedMark μ j) k M :=
  lem_C_lh hc h1 hcpos k M hM.isLittleO

end Applications

end PoissonDeclumping
